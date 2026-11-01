import Mathlib
import LSG.MEV.Blk4
import LSG.MEV.SliceIG

/-!
# The sliced ideal of `G̃` in the 4-block grading

Copy of `LSG.MEV.SliceIG` (standard monomials) with `blk4 a` in place of `blk`: the `x`-count
splits into `∏ᵢ (t D(blk4 a (x i)) + 1)` (leading and trailing blocks).

* **`hfun_slIGV_le4`**:
  `H(sl α I_G̃; t) ≤ ∏ᵢ (tD(xᵢ) + 1) · (2tD_yz + 1)^{d₁} ∏_k 3 (tD_k + 1)(2tD_k + 1)`.
* **`hdata_slIGV4`**: `hdim = d₀ + d₁ + 2m`,
  `deg ≤ (d₀ + d₁ + 2m)! ∏ᵢ D(xᵢ) (2 D_yz)^{d₁} ∏_k 6 D_k²`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun bdeg bdeg_add)
open LSG.ME (Blk bdeg_single_n sub_single_add)

namespace LSG.MEV

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} (a : ℕ)

variable (g₂ g₃ : Fin m → K)

/-- **Upper bound for the Hilbert function of the sliced `I_G̃`.** -/
theorem hfun_slIGV_le4 (h2 : (2 : K) ≠ 0) (α : Fin m → K) (D : Blk4 m → ℕ) (t : ℕ) :
    hfun (blk4 a) D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)) t ≤
      (∏ i : Fin d₀, (t * D (blk4 a (.x i : Var d₀ d₁ m)) + 1)) * (2 * (t * D .yz) + 1) ^ d₁ *
        ∏ k : Fin m, 3 * ((t * D (.e k) + 1) * (2 * (t * D (.e k)) + 1)) := by
  classical
  set F := FLE K (blk4 a) (t • D)
  set I := sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
  set SS := StrongSix.M2.S (blk4 a : Var d₀ d₁ m → Blk4 m) (t • D)
  have hSfin : SS.Finite := StrongSix.M2.S_finite _ _
  set Std : Finset (Var d₀ d₁ m →₀ ℕ) := hSfin.toFinset.filter IsStdV
  set M := Submodule.span K ((fun s => monomial s (1 : K)) '' (Std : Set _)) ⊔
    (I.restrictScalars K ⊓ F)
  have hmonoF : ∀ s ∈ SS, monomial s (1 : K) ∈ F := fun s hs =>
    (monomial_mem_restrictSupport (R := K)).mpr (Or.inl hs)
  have hIG : IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ I := le_sup_left
  have hbd : ∀ (s : Var d₀ d₁ m →₀ ℕ) (v : Var d₀ d₁ m) (n : ℕ) (b : Blk4 m),
      bdeg (blk4 a) (s + Finsupp.single v n) b =
        bdeg (blk4 a) s b + if blk4 a v = b then n else 0 := by
    intro s v n b; rw [bdeg_add, bdeg_single_n]
  have hwt : ∀ (s : Var d₀ d₁ m →₀ ℕ) (v : Var d₀ d₁ m) (n : ℕ),
      Finsupp.weight wmuV (s + Finsupp.single v n) = Finsupp.weight wmuV s + n * wmuV v := by
    intro s v n; rw [map_add, Finsupp.weight_single, smul_eq_mul]
  have step : ∀ s ∈ SS, ∀ Q, Q ∈ M → Q ∈ F → monomial s (1 : K) - Q ∈ I →
      monomial s (1 : K) ∈ M := by
    intro s hs Q hQM hQF hdiff
    have : monomial s (1 : K) = Q + (monomial s 1 - Q) := by ring
    rw [this]
    exact M.add_mem hQM (Submodule.mem_sup_right ⟨hdiff, F.sub_mem (hmonoF s hs) hQF⟩)
  have cover : ∀ n, ∀ s ∈ SS, Finsupp.weight wmuV s = n → monomial s (1 : K) ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hs hn
    have hIH : ∀ s' ∈ SS, Finsupp.weight wmuV s' < n → monomial s' (1 : K) ∈ M :=
      fun s' hs' hlt => ih _ hlt s' hs' rfl
    by_cases c1 : ∃ j, 1 ≤ s (.y j) ∧ 1 ≤ s (.z j)
    · obtain ⟨j, hy, hz⟩ := c1
      set s₁ := s - Finsupp.single (Var.y j) 1
      set s' := s₁ - Finsupp.single (Var.z j) 1
      have hs₁z : s₁ (.z j) = s (.z j) := by simp [s₁]
      have hs's : s = s' + Finsupp.single (.z j) 1 + Finsupp.single (.y j) 1 := by
        rw [sub_single_add s₁ _ _ (by omega), sub_single_add s _ _ hy]
      have hS' : s' ∈ SS := fun b => by
        have := hs b; rw [hs's, hbd, hbd] at this; omega
      have hW : Finsupp.weight wmuV s' < n := by
        rw [← hn, hs's, hwt, hwt]; simp [wmuV]
      refine step s hs _ (hIH s' hS' hW) (hmonoF s' hS') (hIG ?_)
      rw [hs's, monoV_add_single, monoV_add_single]
      have : monomial s' (1 : K) * X (.z j) ^ 1 * X (.y j) ^ 1 - monomial s' 1 =
          YZ K d₀ m j * monomial s' 1 := by simp only [YZ]; ring
      rw [this]
      exact Ideal.mul_mem_right _ _ (YZ_mem_IG g₂ g₃ j)
    push Not at c1
    by_cases c2 : ∃ k, 1 ≤ s (.e k 1)
    · obtain ⟨k, hk⟩ := c2
      set s' := s - Finsupp.single (Var.e k 1) 1
      have hs's : s = s' + Finsupp.single (.e k 1) 1 := (sub_single_add s _ _ hk).symm
      have hS' : s' ∈ SS := fun b => by
        have := hs b; rw [hs's, hbd] at this; omega
      have hS'' : s' + Finsupp.single (.e k 2) 1 ∈ SS := fun b => by
        have := hs b; rw [hs's, hbd] at this; rw [hbd]
        simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b <;> simp [hb] at this ⊢ <;> omega
      have hW : Finsupp.weight wmuV s' < n := by rw [← hn, hs's, hwt]; simp [wmuV]
      have hW' : Finsupp.weight wmuV (s' + Finsupp.single (.e k 2) 1) < n := by
        rw [← hn, hs's, hwt, hwt]; simp [wmuV]
      refine step s hs (monomial s' 1 - C (α k) * monomial (s' + Finsupp.single (.e k 2) 1) 1)
        (M.sub_mem (hIH s' hS' hW) (by
          rw [← smul_eq_C_mul]; exact M.smul_mem _ (hIH _ hS'' hW')))
        (F.sub_mem (hmonoF s' hS') (by rw [← smul_eq_C_mul]; exact F.smul_mem _ (hmonoF _ hS'')))
        ?_
      rw [hs's, monoV_add_single, monoV_add_single]
      have : monomial s' (1 : K) * X (.e k 1) ^ 1 -
          (monomial s' 1 - C (α k) * (monomial s' 1 * X (.e k 2) ^ 1)) =
          (lsl α k - 1) * monomial s' 1 := by simp only [lsl]; ring
      rw [this]
      exact Ideal.mul_mem_right _ _ (lsl_sub_one_mem_sl α _ k)
    push Not at c2
    by_cases c3 : ∃ k, 3 ≤ s (.e k 0)
    · obtain ⟨k, hk⟩ := c3
      set s' := s - Finsupp.single (Var.e k 0) 3
      have hs's : s = s' + Finsupp.single (.e k 0) 3 := (sub_single_add s _ _ hk).symm
      set a := s' + Finsupp.single (.e k 1) 2 + Finsupp.single (.e k 2) 1
      set b := s' + Finsupp.single (.e k 0) 1 + Finsupp.single (.e k 2) 2
      set c := s' + Finsupp.single (.e k 2) 3
      have hSa : a ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [a, hbd]; simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hSb : b ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [b, hbd]; simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hSc : c ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [c, hbd]; simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hWa : Finsupp.weight wmuV a < n := by
        rw [← hn, hs's]; simp only [a, hwt]; simp [wmuV]
      have hWb : Finsupp.weight wmuV b < n := by
        rw [← hn, hs's]; simp only [b, hwt]; simp [wmuV]
      have hWc : Finsupp.weight wmuV c < n := by
        rw [← hn, hs's]; simp only [c, hwt]; simp [wmuV]
      set Q := C (1 / 4 : K) * (monomial a 1 + C (g₂ k) * monomial b 1 + C (g₃ k) * monomial c 1)
      have hQM : Q ∈ M := by
        simp only [Q, ← smul_eq_C_mul]
        exact M.smul_mem _ (M.add_mem (M.add_mem (hIH a hSa hWa)
          (M.smul_mem _ (hIH b hSb hWb))) (M.smul_mem _ (hIH c hSc hWc)))
      have hQF : Q ∈ F := by
        simp only [Q, ← smul_eq_C_mul]
        exact F.smul_mem _ (F.add_mem (F.add_mem (hmonoF a hSa)
          (F.smul_mem _ (hmonoF b hSb))) (F.smul_mem _ (hmonoF c hSc)))
      refine step s hs Q hQM hQF (hIG ?_)
      have h4 : (C (1 / 4 : K) : MvPolynomial (Var d₀ d₁ m) K) * 4 = 1 := by
        have : (1 / 4 : K) * 4 = 1 := by
          have : (4 : K) ≠ 0 := by
            have : (4 : K) = 2 * 2 := by norm_num
            rw [this]; exact mul_ne_zero h2 h2
          field_simp
        rw [show (4 : MvPolynomial (Var d₀ d₁ m) K) = C 4 from (map_ofNat C 4).symm, ← map_mul,
          this, map_one]
      have e : monomial s (1 : K) - Q = -(C (1 / 4 : K) * (Fk g₂ g₃ d₀ d₁ k * monomial s' 1)) := by
        simp only [Q, a, b, c, hs's, monoV_add_single, Fk, LSG.Elliptic.F]
        linear_combination (-(monomial s' 1 * X (Var.e k 0) ^ 3)) * h4
      rw [e]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Fk_mem_IG g₂ g₃ k)))
    push Not at c3
    by_cases c4 : ∃ k, 1 ≤ s (.e k 2) ∧ 1 ≤ s (.e k 4)
    · obtain ⟨k, hW2, hT3⟩ := c4
      set s₁ := s - Finsupp.single (Var.e k 2) 1
      set s' := s₁ - Finsupp.single (Var.e k 4) 1
      have hs₁4 : s₁ (.e k 4) = s (.e k 4) := by simp [s₁]
      have hs's : s = s' + Finsupp.single (.e k 4) 1 + Finsupp.single (.e k 2) 1 := by
        rw [sub_single_add s₁ _ _ (by omega), sub_single_add s _ _ hW2]
      set a := s' + Finsupp.single (.e k 1) 1 + Finsupp.single (.e k 3) 1
      set b := s' + Finsupp.single (.e k 0) 2
      have hSa : a ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd, hbd] at this; simp only [a, hbd]
        simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hSb : b ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd, hbd] at this; simp only [b, hbd]
        simp only [blk4_e] at this ⊢
        by_cases hb : Blk4.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hWa : Finsupp.weight wmuV a < n := by
        rw [← hn, hs's]; simp only [a, hwt]; simp [wmuV]
      have hWb : Finsupp.weight wmuV b < n := by
        rw [← hn, hs's]; simp only [b, hwt]; simp [wmuV]
      set Q := monomial a (1 : K) - C 2 * monomial b 1
      have hQM : Q ∈ M := by
        simp only [Q, ← smul_eq_C_mul]
        exact M.sub_mem (hIH a hSa hWa) (M.smul_mem _ (hIH b hSb hWb))
      have hQF : Q ∈ F := by
        simp only [Q, ← smul_eq_C_mul]
        exact F.sub_mem (hmonoF a hSa) (F.smul_mem _ (hmonoF b hSb))
      refine step s hs Q hQM hQF (hIG ?_)
      have e : monomial s (1 : K) - Q = Gk K d₀ d₁ k * monomial s' 1 := by
        simp only [Q, a, b, hs's, monoV_add_single, Gk, LSG.Elliptic.Gfib, map_ofNat]
        ring
      rw [e]
      exact Ideal.mul_mem_right _ _ (Gk_mem_IG g₂ g₃ k)
    push Not at c4
    have hstd : IsStdV s := ⟨fun j => by
        by_contra h; push Not at h; have := c1 j (by omega); omega,
      fun k => by have := c2 k; omega, fun k => by have := c3 k; omega,
      fun k => by
        by_contra h; push Not at h; have := c4 k (by omega); omega⟩
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, by simp [Std, hs, hstd], rfl⟩)
  have hcover : F ≤ M := by
    intro P hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsS : s ∈ SS := by
      have h' : P ∈ FLE K (blk4 a) (t • D) := hP
      rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at h'
      exact h' hs
    have : monomial s (P.coeff s) = P.coeff s • monomial s (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact M.smul_mem _ (cover _ s hsS rfl)
  -- counting standard monomials
  set N1 := t * D .yz
  let Tup := ((i : Fin d₀) → Fin (t * D (blk4 a (.x i : Var d₀ d₁ m)) + 1)) ×
    (Fin d₁ → Fin (2 * N1 + 1)) ×
    ((k : Fin m) → Fin 3 × Fin (t * D (.e k) + 1) × Fin (2 * (t * D (.e k)) + 1))
  have hbnd : ∀ s ∈ SS, ∀ v, s v ≤ t * D (blk4 a v) := fun s hs v =>
    (StrongSix.M2.le_bdeg (blk4 a) s v).trans (by simpa using hs (blk4 a v))
  have hyz : ∀ s ∈ SS, ∀ j, s (.y j) + s (.z j) ≤ N1 := by
    intro s hs j
    have h := hs .yz
    simp only [Pi.smul_apply, smul_eq_mul] at h
    refine le_trans ?_ h
    unfold bdeg
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Var.y j)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ (Var.z j)⟩)]
    simp
  have hwt3 : ∀ s ∈ SS, ∀ k, s (.e k 2) + s (.e k 4) ≤ t * D (.e k) := by
    intro s hs k
    have h := hs (.e k)
    simp only [Pi.smul_apply, smul_eq_mul] at h
    refine le_trans ?_ h
    unfold bdeg
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Var.e k 2)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ (Var.e k 4)⟩)]
    simp
  let tup : Std → Tup := fun s =>
    (fun i => ⟨s.1 (.x i), Nat.lt_succ_of_le (by
        have := hbnd s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) (.x i)
        simpa using this)⟩,
      fun j => ⟨N1 + s.1 (.y j) - s.1 (.z j), by
        have := hyz s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) j; omega⟩,
      fun k => (⟨s.1 (.e k 0), by have := (Finset.mem_filter.mp s.2).2.2.2.1 k; omega⟩,
        ⟨s.1 (.e k 3), Nat.lt_succ_of_le (by
          have := hbnd s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) (.e k 3)
          simpa using this)⟩,
        ⟨t * D (.e k) + s.1 (.e k 2) - s.1 (.e k 4), by
          have := hwt3 s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) k; omega⟩))
  have htup : Function.Injective tup := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hsS := hSfin.mem_toFinset.mp (Finset.mem_filter.mp hs).1
    have hsS' := hSfin.mem_toFinset.mp (Finset.mem_filter.mp hs').1
    obtain ⟨hy, hV, -, hWT⟩ := (Finset.mem_filter.mp hs).2
    obtain ⟨hy', hV', -, hWT'⟩ := (Finset.mem_filter.mp hs').2
    have hx : ∀ i, s (.x i) = s' (.x i) := fun i =>
      congrArg Fin.val (congrFun (congrArg Prod.fst h) i)
    have hyz' : ∀ j, N1 + s (.y j) - s (.z j) = N1 + s' (.y j) - s' (.z j) := fun j =>
      congrArg Fin.val (congrFun (congrArg (fun p => p.2.1) h) j)
    have he0 : ∀ k, s (.e k 0) = s' (.e k 0) := fun k =>
      congrArg (fun p => (p.1 : ℕ)) (congrFun (congrArg (fun p => p.2.2) h) k)
    have he3 : ∀ k, s (.e k 3) = s' (.e k 3) := fun k =>
      congrArg (fun p => (p.2.1 : ℕ)) (congrFun (congrArg (fun p => p.2.2) h) k)
    have he24 : ∀ k, t * D (.e k) + s (.e k 2) - s (.e k 4) =
        t * D (.e k) + s' (.e k 2) - s' (.e k 4) := fun k =>
      congrArg (fun p => (p.2.2 : ℕ)) (congrFun (congrArg (fun p => p.2.2) h) k)
    apply Subtype.ext
    ext v
    change s v = s' v
    cases v with
    | x i => exact hx i
    | y j =>
      have := hyz' j
      have := hyz s hsS j; have := hyz s' hsS' j
      rcases hy j with h | h <;> rcases hy' j with h' | h' <;> omega
    | z j =>
      have := hyz' j
      have := hyz s hsS j; have := hyz s' hsS' j
      rcases hy j with h | h <;> rcases hy' j with h' | h' <;> omega
    | e k c =>
      have := he24 k
      have := hwt3 s hsS k; have := hwt3 s' hsS' k
      fin_cases c
      · exact he0 k
      · simp only [Fin.mk_one, Fin.isValue]; rw [hV k, hV' k]
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rcases hWT k with h | h <;> rcases hWT' k with h' | h' <;> omega
      · exact he3 k
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rcases hWT k with h | h <;> rcases hWT' k with h' | h' <;> omega
  have hcardStd : Std.card ≤ Fintype.card Tup := by
    have := Fintype.card_le_of_injective tup htup
    simpa using this
  set Sp := Submodule.span K ((fun s => monomial s (1 : K)) '' (Std : Set (Var d₀ d₁ m →₀ ℕ)))
  have : FiniteDimensional K Sp :=
    FiniteDimensional.span_of_finite K (Set.toFinite _)
  have : FiniteDimensional K ↥(I.restrictScalars K ⊓ F) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have h1 := Submodule.finrank_mono hcover
  have h2' := Submodule.finrank_add_le_finrank_add_finrank
    Sp (I.restrictScalars K ⊓ F)
  have h3 : finrank K Sp ≤ Std.card := by
    refine (finrank_span_le_card _).trans ?_
    exact Finset.card_image_le.trans_eq' (by rw [Set.toFinset_image, Finset.toFinset_coe])
  have hTup : Fintype.card Tup = (∏ i : Fin d₀, (t * D (blk4 a (.x i : Var d₀ d₁ m)) + 1)) *
      (2 * (t * D .yz) + 1) ^ d₁ *
      ∏ k : Fin m, 3 * ((t * D (.e k) + 1) * (2 * (t * D (.e k)) + 1)) := by
    simp [Tup, Fintype.card_prod, Fintype.card_pi, N1, mul_assoc]
  have e : hfun (blk4 a) D K I t = finrank K F - finrank K ↥(I.restrictScalars K ⊓ F) := rfl
  have h1' : finrank K F ≤ finrank K Sp + finrank K ↥(I.restrictScalars K ⊓ F) := h1.trans h2'
  have h4 := h3.trans hcardStd
  rw [e, ← hTup]
  omega

omit g₂ g₃ in
/-- The bounding polynomial. -/
noncomputable def polIGV4 (D : Blk4 m → ℕ) : Polynomial ℤ :=
  (∏ i : Fin d₀, (Polynomial.C (D (blk4 a (.x i : Var d₀ d₁ m)) : ℤ) * Polynomial.X + 1)) *
    (Polynomial.C (2 * D .yz : ℤ) * Polynomial.X + 1) ^ d₁ *
    ∏ k : Fin m, ((Polynomial.C (3 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 3) *
      (Polynomial.C (2 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 1))

omit g₂ g₃ in
theorem polIGV4_data {D : Blk4 m → ℕ} (hD : ∀ i, 1 ≤ D i) :
    (polIGV4 (d₀ := d₀) (d₁ := d₁) a D).natDegree = d₀ + d₁ + 2 * m ∧
      (polIGV4 (d₀ := d₀) (d₁ := d₁) a D).leadingCoeff =
        (∏ i : Fin d₀, (D (blk4 a (.x i : Var d₀ d₁ m)) : ℤ)) * (2 * D .yz : ℤ) ^ d₁ *
          ∏ k : Fin m, (6 * D (.e k) ^ 2 : ℤ) ∧
      polIGV4 (d₀ := d₀) (d₁ := d₁) a D ≠ 0 := by
  have lin : ∀ (a b : ℤ), a ≠ 0 → (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 ∧
      (Polynomial.C a * Polynomial.X + Polynomial.C b).leadingCoeff = a ∧
      Polynomial.C a * Polynomial.X + Polynomial.C b ≠ 0 := fun a b ha => by
    have h1 := Polynomial.natDegree_linear (b := b) ha
    refine ⟨h1, Polynomial.leadingCoeff_linear ha, fun h0 => ?_⟩
    rw [h0, Polynomial.natDegree_zero] at h1
    omega
  have hx : ∀ i : Fin d₀, _ := fun i => lin (D (blk4 a (.x i : Var d₀ d₁ m))) 1
    (by have := hD (blk4 a (.x i : Var d₀ d₁ m)); omega)
  have hyz := lin (2 * D .yz) 1 (by have := hD .yz; omega)
  have he3 : ∀ k : Fin m, _ := fun k => lin (3 * D (.e k)) 3 (by have := hD (.e k); omega)
  have he2 : ∀ k : Fin m, _ := fun k => lin (2 * D (.e k)) 1 (by have := hD (.e k); omega)
  simp only [map_one] at hx hyz
  have hx0 : ∀ i : Fin d₀, (Polynomial.C (D (blk4 a (.x i : Var d₀ d₁ m)) : ℤ) * Polynomial.X + 1)
      ≠ 0 := fun i => (hx i).2.2
  have hxp0 : ∏ i : Fin d₀, (Polynomial.C (D (blk4 a (.x i : Var d₀ d₁ m)) : ℤ) *
      Polynomial.X + 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hx0 i
  have hyz0 := hyz.2.2
  have hb0 : ∀ k : Fin m, (Polynomial.C (3 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 3) *
      (Polynomial.C (2 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 1) ≠ 0 := fun k =>
    mul_ne_zero (he3 k).2.2 (he2 k).2.2
  have hprod0 : ∏ k : Fin m, ((Polynomial.C (3 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 3) *
      (Polynomial.C (2 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hb0 k
  refine ⟨?_, ?_, ?_⟩
  · rw [polIGV4, Polynomial.natDegree_mul (mul_ne_zero hxp0 (pow_ne_zero _ hyz0)) hprod0,
      Polynomial.natDegree_mul hxp0 (pow_ne_zero _ hyz0),
      Polynomial.natDegree_prod _ _ fun i _ => hx0 i,
      Polynomial.natDegree_pow, hyz.1,
      Polynomial.natDegree_prod _ _ fun k _ => hb0 k]
    simp only [fun i => (hx i).1, fun k => Polynomial.natDegree_mul (he3 k).2.2 (he2 k).2.2,
      fun k => (he3 k).1, fun k => (he2 k).1]
    simp; ring
  · rw [polIGV4, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_prod, Polynomial.leadingCoeff_pow, hyz.2.1,
      Polynomial.leadingCoeff_prod]
    simp only [fun i => (hx i).2.1, Polynomial.leadingCoeff_mul, fun k => (he3 k).2.1,
      fun k => (he2 k).2.1]
    congr 1
    exact Finset.prod_congr rfl fun k _ => by ring
  · exact mul_ne_zero (mul_ne_zero hxp0 (pow_ne_zero _ hyz0)) hprod0

omit g₂ g₃ in
theorem polIGV4_eval (D : Blk4 m → ℕ) (t : ℕ) :
    (polIGV4 (d₀ := d₀) (d₁ := d₁) a D).eval (t : ℤ) =
      ((((∏ i : Fin d₀, (t * D (blk4 a (.x i : Var d₀ d₁ m)) + 1)) *
        (2 * (t * D .yz) + 1) ^ d₁ *
          ∏ k : Fin m, 3 * ((t * D (.e k) + 1) * (2 * (t * D (.e k)) + 1))) : ℕ) : ℤ) := by
  simp only [polIGV4, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_prod]
  push_cast
  congr 1
  · congr 1
    · exact Finset.prod_congr rfl fun i _ => by ring
    · ring
  · exact Finset.prod_congr rfl fun k _ => by ring

/-- **Dimension and degree of the sliced `I_G̃`, 4-block grading.** -/
theorem hdata_slIGV4 (h2 : (2 : K) ≠ 0) (α : Fin m → K) {D : Blk4 m → ℕ}
    (hD : ∀ i, 1 ≤ D i) :
    (StrongSix.M2.hdata (blk4 a) D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃))).1 =
        d₀ + d₁ + 2 * m ∧
      (StrongSix.M2.hdata (blk4 a) D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃))).2 ≤
        (((d₀ + d₁ + 2 * m).factorial * (∏ i : Fin d₀, D (blk4 a (.x i : Var d₀ d₁ m))) *
          (2 * D .yz) ^ d₁ * ∏ k : Fin m, 6 * D (.e k) ^ 2 : ℕ) : ℤ) := by
  classical
  set I := sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
  have hne : I ≠ ⊤ := slIGV_ne_top g₂ g₃ α
  have hspec := StrongSix.M2.hdata_spec (blk4 a) D K hne
  have h1 : ∀ i : Blk m, 1 ≤ (fun _ => 1 : Blk m → ℕ) i := fun _ => le_rfl
  have hdim : (StrongSix.M2.hdata (blk4 a) D K I).1 = d₀ + d₁ + 2 * m := by
    rw [hdim4_eq a hD h1 hne]
    exact (hdata_slIGV g₂ g₃ h2 α h1).1
  obtain ⟨hdeg, hlc, hP0⟩ := polIGV4_data (d₀ := d₀) (d₁ := d₁) a hD
  have hg := StrongSix.M2.hasData_poly hP0
  rw [hdeg, hlc] at hg
  have hcmp := hspec.compare hg (Filter.Eventually.of_forall fun t => by
      rw [polIGV4_eval]; exact_mod_cast hfun_slIGV_le4 a g₂ g₃ h2 α D t)
    (Filter.Eventually.of_forall fun _ => by positivity)
  rcases hcmp with hlt | ⟨heq, hle⟩
  · omega
  · refine ⟨heq, hle.trans (le_of_eq ?_)⟩
    push_cast; ring

end LSG.MEV
