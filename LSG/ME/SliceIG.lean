import Mathlib
import LSG.ME.Slice
import LSG.ME.Chain

/-!
# The sliced ideal of `G`: Hilbert function upper bound (STAGE2 §11, item S3′)

`sl α I_G = I_G + (ℓ_k − 1)_k`, `ℓ_k = V_k + α_k W_k`. Standard monomials: no `V_k`, `U_k`-exponent
`≤ 2`, `min(Y_j, Z_j)`-exponent `0`. Reductions (block degrees do not increase):
`Y_j Z_j → 1`, `V_k → 1 − α_k W_k`, `U_k³ → ¼ (V_k² W_k + g₂ U_k W_k² + g₃ W_k³)` (`F_k`), with the
measure `Σ (Y + Z + U + V)`-exponents.

* **`hfun_slIG_le`**:
  `H(sl α I_G; t) ≤ (tD_x + 1)^{d₀} (2 tD_yz + 1)^{d₁} ∏_k 3 (tD_k + 1)` (any field with `2 ≠ 0`).
* `lGs = lG ++ (ℓ_k − 1)_k`, `slIG_eq_ofList`: `sl α I_G = Ideal.ofList lGs`; `slIG_ne_top`.
* **`hdata_slIG`**: `hdim (sl α I_G) = d₀ + d₁ + m` and
  `deg (sl α I_G) ≤ (d₀+d₁+m)! D_x^{d₀} (2 D_yz)^{d₁} ∏_k 3 D_k`;
  **`height_slIG`**: `ht (Ideal.ofList lGs) = lGs.length` (a complete intersection, for `bezout`).
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun bdeg bdeg_add)

namespace LSG.ME

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ}

/-- Standard monomials. -/
def IsStd (s : Var d₀ d₁ m →₀ ℕ) : Prop :=
  (∀ j, s (.y j) = 0 ∨ s (.z j) = 0) ∧ (∀ k, s (.e k 1) = 0) ∧ ∀ k, s (.e k 0) ≤ 2

/-- The reduction measure weights. -/
def wmu : Var d₀ d₁ m → ℕ
  | .x _ => 0
  | .y _ => 1
  | .z _ => 1
  | .e _ c => if c = 2 then 0 else 1

theorem bdeg_single_n {σ ι : Type*} [Fintype σ] [DecidableEq ι] (β : σ → ι)
    (v : σ) (n : ℕ) (i : ι) : bdeg β (Finsupp.single v n) i = if β v = i then n else 0 := by
  classical
  simp only [bdeg, Finsupp.single_apply]
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem monomial_add_single' (s : Var d₀ d₁ m →₀ ℕ) (v : Var d₀ d₁ m) (n : ℕ) :
    (monomial (s + Finsupp.single v n) (1 : K)) = monomial s 1 * X v ^ n :=
  monomial_add_single

theorem sub_single_add {σ : Type*} (s : σ →₀ ℕ) (v : σ) (n : ℕ) (h : n ≤ s v) :
    s - Finsupp.single v n + Finsupp.single v n = s := by
  classical
  ext w
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs with hw
  · subst hw; omega
  · simp

variable (g₂ g₃ : Fin m → K)

/-- **Upper bound for the Hilbert function of the sliced `I_G`.** -/
theorem hfun_slIG_le (h2 : (2 : K) ≠ 0) (α : Fin m → K) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)) t ≤
      (t * D .x + 1) ^ d₀ * (2 * (t * D .yz) + 1) ^ d₁ * ∏ k : Fin m, 3 * (t * D (.e k) + 1) := by
  classical
  set F := FLE K blk (t • D)
  set I := sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
  set SS := StrongSix.M2.S (blk : Var d₀ d₁ m → Blk m) (t • D)
  have hSfin : SS.Finite := StrongSix.M2.S_finite _ _
  set Std : Finset (Var d₀ d₁ m →₀ ℕ) := hSfin.toFinset.filter IsStd
  set M := Submodule.span K ((fun s => monomial s (1 : K)) '' (Std : Set _)) ⊔
    (I.restrictScalars K ⊓ F)
  have hmonoF : ∀ s ∈ SS, monomial s (1 : K) ∈ F := fun s hs =>
    (monomial_mem_restrictSupport (R := K)).mpr (Or.inl hs)
  have hIG : IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ I := le_sup_left
  -- block degrees of sums with singles
  have hbd : ∀ (s : Var d₀ d₁ m →₀ ℕ) (v : Var d₀ d₁ m) (n : ℕ) (b : Blk m),
      bdeg blk (s + Finsupp.single v n) b = bdeg blk s b + if blk v = b then n else 0 := by
    intro s v n b; rw [bdeg_add, bdeg_single_n]
  have hwt : ∀ (s : Var d₀ d₁ m →₀ ℕ) (v : Var d₀ d₁ m) (n : ℕ),
      Finsupp.weight wmu (s + Finsupp.single v n) = Finsupp.weight wmu s + n * wmu v := by
    intro s v n; rw [map_add, Finsupp.weight_single, smul_eq_mul]
  -- the reduction step
  have step : ∀ s ∈ SS, ∀ Q, Q ∈ M → Q ∈ F → monomial s (1 : K) - Q ∈ I →
      monomial s (1 : K) ∈ M := by
    intro s hs Q hQM hQF hdiff
    have : monomial s (1 : K) = Q + (monomial s 1 - Q) := by ring
    rw [this]
    exact M.add_mem hQM (Submodule.mem_sup_right ⟨hdiff, F.sub_mem (hmonoF s hs) hQF⟩)
  have cover : ∀ n, ∀ s ∈ SS, Finsupp.weight wmu s = n → monomial s (1 : K) ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hs hn
    have hIH : ∀ s' ∈ SS, Finsupp.weight wmu s' < n → monomial s' (1 : K) ∈ M :=
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
      have hW : Finsupp.weight wmu s' < n := by
        rw [← hn, hs's, hwt, hwt]; simp [wmu]
      refine step s hs _ (hIH s' hS' hW) (hmonoF s' hS') (hIG ?_)
      rw [hs's, monomial_add_single', monomial_add_single']
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
        simp only [blk_e] at this ⊢
        by_cases hb : Blk.e k = b <;> simp [hb] at this ⊢ <;> omega
      have hW : Finsupp.weight wmu s' < n := by rw [← hn, hs's, hwt]; simp [wmu]
      have hW' : Finsupp.weight wmu (s' + Finsupp.single (.e k 2) 1) < n := by
        rw [← hn, hs's, hwt, hwt]; simp [wmu]
      refine step s hs (monomial s' 1 - C (α k) * monomial (s' + Finsupp.single (.e k 2) 1) 1)
        (M.sub_mem (hIH s' hS' hW) (by
          rw [← smul_eq_C_mul]; exact M.smul_mem _ (hIH _ hS'' hW')))
        (F.sub_mem (hmonoF s' hS') (by rw [← smul_eq_C_mul]; exact F.smul_mem _ (hmonoF _ hS'')))
        ?_
      rw [hs's, monomial_add_single', monomial_add_single']
      have : monomial s' (1 : K) * X (.e k 1) ^ 1 -
          (monomial s' 1 - C (α k) * (monomial s' 1 * X (.e k 2) ^ 1)) =
          (lsl α k - 1) * monomial s' 1 := by simp only [lsl]; ring
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
    push Not at c2
    by_cases c3 : ∃ k, 3 ≤ s (.e k 0)
    · obtain ⟨k, hk⟩ := c3
      set s' := s - Finsupp.single (Var.e k 0) 3
      have hs's : s = s' + Finsupp.single (.e k 0) 3 := (sub_single_add s _ _ hk).symm
      set a := s' + Finsupp.single (.e k 1) 2 + Finsupp.single (.e k 2) 1
      set b := s' + Finsupp.single (.e k 0) 1 + Finsupp.single (.e k 2) 2
      set c := s' + Finsupp.single (.e k 2) 3
      have hSa : a ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [a, hbd]; simp only [blk_e] at this ⊢
        by_cases hb : Blk.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hSb : b ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [b, hbd]; simp only [blk_e] at this ⊢
        by_cases hb : Blk.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hSc : c ∈ SS := fun b' => by
        have := hs b'; rw [hs's, hbd] at this; simp only [c, hbd]; simp only [blk_e] at this ⊢
        by_cases hb : Blk.e k = b' <;> simp [hb] at this ⊢ <;> omega
      have hWa : Finsupp.weight wmu a < n := by
        rw [← hn, hs's]; simp only [a, hwt]; simp [wmu]
      have hWb : Finsupp.weight wmu b < n := by
        rw [← hn, hs's]; simp only [b, hwt]; simp [wmu]
      have hWc : Finsupp.weight wmu c < n := by
        rw [← hn, hs's]; simp only [c, hwt]; simp [wmu]
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
        simp only [Q, a, b, c, hs's, monomial_add_single', Fk, LSG.Elliptic.F]
        linear_combination (-(monomial s' 1 * X (Var.e k 0) ^ 3)) * h4
      rw [e]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Fk_mem_IG g₂ g₃ k)))
    push Not at c3
    -- a standard monomial
    have hstd : IsStd s := ⟨fun j => by
        by_contra h; push Not at h; have := c1 j (by omega); omega,
      fun k => by have := c2 k; omega, fun k => by have := c3 k; omega⟩
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, by simp [Std, hs, hstd], rfl⟩)
  have hcover : F ≤ M := by
    intro P hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsS : s ∈ SS := by
      have h' : P ∈ FLE K blk (t • D) := hP
      rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at h'
      exact h' hs
    have : monomial s (P.coeff s) = P.coeff s • monomial s (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact M.smul_mem _ (cover _ s hsS rfl)
  -- counting standard monomials
  set N0 := t * D .x
  set N1 := t * D .yz
  let Tup := (Fin d₀ → Fin (N0 + 1)) × (Fin d₁ → Fin (2 * N1 + 1)) ×
    ((k : Fin m) → Fin 3 × Fin (t * D (.e k) + 1))
  have hbnd : ∀ s ∈ SS, ∀ v, s v ≤ t * D (blk v) := fun s hs v =>
    (StrongSix.M2.le_bdeg blk s v).trans (by simpa using hs (blk v))
  have hyz : ∀ s ∈ SS, ∀ j, s (.y j) + s (.z j) ≤ N1 := by
    intro s hs j
    have h := hs .yz
    simp only [Pi.smul_apply, smul_eq_mul] at h
    refine le_trans ?_ h
    unfold bdeg
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Var.y j)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ (Var.z j)⟩)]
    simp
  let tup : Std → Tup := fun s =>
    (fun i => ⟨s.1 (.x i), Nat.lt_succ_of_le (by
        have := hbnd s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) (.x i)
        simpa [N0] using this)⟩,
      fun j => ⟨N1 + s.1 (.y j) - s.1 (.z j), by
        have := hyz s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) j; omega⟩,
      fun k => (⟨s.1 (.e k 0), by have := (Finset.mem_filter.mp s.2).2.2.2 k; omega⟩,
        ⟨s.1 (.e k 2), Nat.lt_succ_of_le (by
          have := hbnd s.1 (hSfin.mem_toFinset.mp (Finset.mem_filter.mp s.2).1) (.e k 2)
          simpa using this)⟩))
  have htup : Function.Injective tup := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hsS := hSfin.mem_toFinset.mp (Finset.mem_filter.mp hs).1
    have hsS' := hSfin.mem_toFinset.mp (Finset.mem_filter.mp hs').1
    obtain ⟨hy, hV, -⟩ := (Finset.mem_filter.mp hs).2
    obtain ⟨hy', hV', -⟩ := (Finset.mem_filter.mp hs').2
    have hx : ∀ i, s (.x i) = s' (.x i) := fun i =>
      congrArg Fin.val (congrFun (congrArg Prod.fst h) i)
    have hyz' : ∀ j, N1 + s (.y j) - s (.z j) = N1 + s' (.y j) - s' (.z j) := fun j =>
      congrArg Fin.val (congrFun (congrArg (fun p => p.2.1) h) j)
    have he0 : ∀ k, s (.e k 0) = s' (.e k 0) := fun k =>
      congrArg (fun p => (p.1 : ℕ)) (congrFun (congrArg (fun p => p.2.2) h) k)
    have he2 : ∀ k, s (.e k 2) = s' (.e k 2) := fun k =>
      congrArg (fun p => (p.2 : ℕ)) (congrFun (congrArg (fun p => p.2.2) h) k)
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
      fin_cases c
      · exact he0 k
      · simp only [Fin.mk_one, Fin.isValue]; rw [hV k, hV' k]
      · exact he2 k
  have hcardStd : Std.card ≤ Fintype.card Tup := by
    have := Fintype.card_le_of_injective tup htup
    simpa using this
  -- finrank
  set Sp := Submodule.span K ((fun s => monomial s (1 : K)) '' (Std : Set (Var d₀ d₁ m →₀ ℕ)))
  have : FiniteDimensional K Sp :=
    FiniteDimensional.span_of_finite K (Set.toFinite _)
  have : FiniteDimensional K ↥(I.restrictScalars K ⊓ F) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have h1 := Submodule.finrank_mono hcover
  have h2' := Submodule.finrank_add_le_finrank_add_finrank
    Sp (I.restrictScalars K ⊓ F)
  have h3 : finrank K Sp ≤
      Std.card := by
    refine (finrank_span_le_card _).trans ?_
    exact Finset.card_image_le.trans_eq' (by rw [Set.toFinset_image, Finset.toFinset_coe])
  have hTup : Fintype.card Tup = (t * D .x + 1) ^ d₀ * (2 * (t * D .yz) + 1) ^ d₁ *
      ∏ k : Fin m, 3 * (t * D (.e k) + 1) := by
    simp [Tup, Fintype.card_prod, Fintype.card_pi, N0, N1, mul_assoc]
  have e : hfun blk D K I t = finrank K F - finrank K ↥(I.restrictScalars K ⊓ F) := rfl
  have h1' : finrank K F ≤ finrank K Sp + finrank K ↥(I.restrictScalars K ⊓ F) := h1.trans h2'
  have h4 := h3.trans hcardStd
  rw [e, ← hTup]
  omega

/-! ### Dimension, degree, height -/

/-- The generators of the sliced `I_G`. -/
noncomputable def lGs (α : Fin m → K) : List (MvPolynomial (Var d₀ d₁ m) K) :=
  lG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ++ List.ofFn fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1

theorem lGs_length (α : Fin m → K) : (lGs (d₀ := d₀) (d₁ := d₁) g₂ g₃ α).length = d₁ + 2 * m := by
  simp [lGs, lG_length]; ring

theorem slIG_eq_ofList (α : Fin m → K) :
    sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) = Ideal.ofList (lGs g₂ g₃ α) := by
  rw [lGs, Ideal.ofList_append, IG, sl]
  congr 1
  congr 1
  ext P
  simp [List.mem_ofFn]

theorem slIG_ne_top (h2 : (2 : K) ≠ 0) (α : Fin m → K) :
    sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) ≠ ⊤ := by
  classical
  intro htop
  have hle : sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) ≤
      vanishS α (Set.univ : Set (GPt K d₀ d₁ g₂ g₃)) :=
    (sup_le_sup_right (IG_le_vanish h2 _) _).trans (sl_vanish_le α _)
  have h1 : (1 : MvPolynomial (Var d₀ d₁ m) K) ∈ vanishS α (Set.univ : Set (GPt K d₀ d₁ g₂ g₃)) :=
    hle (htop ▸ Submodule.mem_top)
  have h0 : ∀ k, lval α (0 : GPt K d₀ d₁ g₂ g₃) k ≠ 0 := fun k => by
    simp [lval, LSG.Elliptic.rep, LSG.Elliptic.O]
  have := (StrongSix.M2.mem_vanish' _).mp h1 0 ⟨Set.mem_univ _, h0⟩
  simp at this

/-- The bounding polynomial `(D_x X + 1)^{d₀} (2 D_yz X + 1)^{d₁} ∏_k (3 D_k X + 3)`. -/
noncomputable def polIG (D : Blk m → ℕ) : Polynomial ℤ :=
  (Polynomial.C (D .x : ℤ) * Polynomial.X + 1) ^ d₀ *
    (Polynomial.C (2 * D .yz : ℤ) * Polynomial.X + 1) ^ d₁ *
    ∏ k : Fin m, (Polynomial.C (3 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 3)

theorem polIG_data {D : Blk m → ℕ} (hD : ∀ i, 1 ≤ D i) :
    (polIG (d₀ := d₀) (d₁ := d₁) D).natDegree = d₀ + d₁ + m ∧
      (polIG (d₀ := d₀) (d₁ := d₁) D).leadingCoeff =
        (D .x : ℤ) ^ d₀ * (2 * D .yz : ℤ) ^ d₁ * ∏ k : Fin m, (3 * D (.e k) : ℤ) ∧
      polIG (d₀ := d₀) (d₁ := d₁) D ≠ 0 := by
  have lin : ∀ (a b : ℤ), a ≠ 0 → (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 ∧
      (Polynomial.C a * Polynomial.X + Polynomial.C b).leadingCoeff = a ∧
      Polynomial.C a * Polynomial.X + Polynomial.C b ≠ 0 := fun a b ha => by
    have h1 := Polynomial.natDegree_linear (b := b) ha
    refine ⟨h1, Polynomial.leadingCoeff_linear ha, fun h0 => ?_⟩
    rw [h0, Polynomial.natDegree_zero] at h1
    omega
  have hx := lin (D .x) 1 (by have := hD .x; omega)
  have hyz := lin (2 * D .yz) 1 (by have := hD .yz; omega)
  have he : ∀ k : Fin m, _ := fun k => lin (3 * D (.e k)) 3 (by have := hD (.e k); omega)
  simp only [map_one] at hx hyz
  have hx0 := hx.2.2
  have hyz0 := hyz.2.2
  have hprod0 :
      ∏ k : Fin m, (Polynomial.C (3 * D (.e k) : ℤ) * Polynomial.X + Polynomial.C 3) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (he k).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [polIG, Polynomial.natDegree_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hyz0))
      hprod0, Polynomial.natDegree_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hyz0),
      Polynomial.natDegree_pow, Polynomial.natDegree_pow, hx.1, hyz.1,
      Polynomial.natDegree_prod _ _ fun k _ => (he k).2.2,
      Finset.sum_congr rfl fun k _ => (he k).1]
    simp
  · rw [polIG, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow, hx.2.1, hyz.2.1,
      Polynomial.leadingCoeff_prod, Finset.prod_congr rfl fun k _ => (he k).2.1]
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hyz0)) hprod0

theorem polIG_eval (D : Blk m → ℕ) (t : ℕ) :
    (polIG (d₀ := d₀) (d₁ := d₁) D).eval (t : ℤ) = (((t * D .x + 1) ^ d₀ *
      (2 * (t * D .yz) + 1) ^ d₁ * ∏ k : Fin m, 3 * (t * D (.e k) + 1) : ℕ) : ℤ) := by
  simp only [polIG, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_prod]
  push_cast
  congr 1
  · ring
  · exact Finset.prod_congr rfl fun k _ => by ring

/-- **Dimension and degree of the sliced `I_G`.** -/
theorem hdata_slIG (h2 : (2 : K) ≠ 0) (α : Fin m → K) {D : Blk m → ℕ}
    (hD : ∀ i, 1 ≤ D i) :
    (StrongSix.M2.hdata blk D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃))).1 = d₀ + d₁ + m ∧
      (StrongSix.M2.hdata blk D K (sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃))).2 ≤
        (((d₀ + d₁ + m).factorial * D .x ^ d₀ * (2 * D .yz) ^ d₁ * ∏ k : Fin m, 3 * D (.e k) :
          ℕ) : ℤ) := by
  classical
  set I := sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
  have hne : I ≠ ⊤ := slIG_ne_top g₂ g₃ h2 α
  have hspec := StrongSix.M2.hdata_spec blk D K hne
  -- lower bound on the dimension (Krull)
  have hlow : d₀ + d₁ + m ≤ (StrongSix.M2.hdata blk D K I).1 := by
    have hb := StrongSix.M2.hdim_add_height_eq blk D hD hne
    have hI : I = Ideal.span ((lGs (d₀ := d₀) (d₁ := d₁) g₂ g₃ α).toFinset : Set _) := by
      change sl α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) = _
      rw [slIG_eq_ofList, Ideal.ofList]; congr 1; ext P; simp
    have hht : I.height ≤ (d₁ + 2 * m : ℕ) := by
      have := Ideal.height_span_le_card_of_span_ne_top (hI ▸ hne)
      rw [← hI] at this
      refine this.trans ?_
      have := List.toFinset_card_le (lGs (d₀ := d₀) (d₁ := d₁) g₂ g₃ α)
      rw [lGs_length] at this
      exact_mod_cast this
    rw [card_Var] at hb
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hne)
    rw [← hn] at hb hht
    have h1 : (StrongSix.M2.hdata blk D K I).1 + n = d₀ + 2 * d₁ + 3 * m := by exact_mod_cast hb
    have h2' : n ≤ d₁ + 2 * m := by exact_mod_cast hht
    omega
  obtain ⟨hdeg, hlc, hP0⟩ := polIG_data (d₀ := d₀) (d₁ := d₁) hD
  have hg := StrongSix.M2.hasData_poly hP0
  rw [hdeg, hlc] at hg
  have hcmp := hspec.compare hg (Filter.Eventually.of_forall fun t => by
      rw [polIG_eval]; exact_mod_cast hfun_slIG_le g₂ g₃ h2 α D t)
    (Filter.Eventually.of_forall fun _ => by positivity)
  rcases hcmp with hlt | ⟨heq, hle⟩
  · omega
  · refine ⟨heq, hle.trans (le_of_eq ?_)⟩
    push_cast; ring

/-- **The sliced `I_G` is a complete intersection.** -/
theorem height_slIG (h2 : (2 : K) ≠ 0) (α : Fin m → K) :
    (Ideal.ofList (lGs (d₀ := d₀) (d₁ := d₁) g₂ g₃ α)).height =
      (lGs (d₀ := d₀) (d₁ := d₁) g₂ g₃ α).length := by
  have hD : ∀ i : Blk m, 1 ≤ (fun _ => 1 : Blk m → ℕ) i := fun _ => le_rfl
  have hne := slIG_ne_top g₂ g₃ (d₀ := d₀) (d₁ := d₁) h2 α
  rw [slIG_eq_ofList] at hne
  have hb := StrongSix.M2.hdim_add_height_eq blk _ hD hne
  have hdim := (hdata_slIG (d₀ := d₀) (d₁ := d₁) g₂ g₃ h2 α hD).1
  rw [slIG_eq_ofList] at hdim
  rw [hdim, card_Var] at hb
  rw [lGs_length]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hne)
  rw [← hn] at hb ⊢
  have : d₀ + d₁ + m + n = d₀ + 2 * d₁ + 3 * m := by exact_mod_cast hb
  norm_cast
  omega

end LSG.ME
