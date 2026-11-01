import Mathlib
import LSG.ME.OrderTransl
import LSG.ME.WustAlg
import LSG.ME.WustCoset

/-!
# Wüstholz transversals: transport to cosets and gluing (STAGE2 §5–§6, S2.7)

Setting: `K` algebraically closed of characteristic `0`, `V` an irreducible Zariski-closed set
containing `0` (in the application `V = H⁰`). **Identity data** (constructed over `ℂ` in
`LSG.ME.WustId`): `w₁..w_ℓ`, homogeneous `T₁..T_ℓ ∈ I(V)` of a common multidegree `d`, and
`N ∉ I(V)` with `D̂_{wᵢ} Tⱼ − δᵢⱼ N ∈ I(V)` for the homogenised `V`-chart derivations
`D̂_w = Dh (fun _ => V) w`.

**Why one chart is not enough.** On a coset `σ + V` whose `k`-th coordinate is constantly a
`2`-torsion point `≠ 0`, the form `V_k` vanishes identically and `D̂_w` acts on `I(σ + V)` like a
multiple of the Euler field (`eval_Dhat_eq_zero_of_V`), so `D̂_{wᵢ} Qⱼ ≡ δᵢⱼ M` with
`M ∉ I(σ + V)` is impossible. We therefore use on each coset the canonical chart `chartAt σ`
(whose product form is nonzero at `σ`) and glue the derivations with separators:
`Dᵢ = Σ_{a ∈ R} B_a • Dh (chartAt a) wᵢ`.

* `homSub`, `IsHomE.mul/prod/det/adjugate`: multihomogeneity bookkeeping.
* `Dh_add_apply`, `Dh_smul_apply`: `Dh ch w` is linear in `w`.
* `transl_mem_vanish_gtransl`: `τ_{−σ}` maps `I(V)` into `I(σ + V)`.
* `exists_transl_notMem`: for `N ∉ I(V)` some law choice gives `τ_{−σ} N ∉ I(σ + V)`.
* **`transport`**: identity data ↦ data on `σ + V` for the chart `chartAt σ`
  (via the translation identity `tr_id`): `T′ = τ(V₁⋯V_m · T)`, `N′ = Lc_{chartAt σ} · τ N`.
* **`transversals_of_identity`**: for a finite set `R` of pairwise non-nested translates
  (`E = ⋃_{a ∈ R} (a + V)`): glued derivations `Dᵢ`, `Qⱼ ∈ I(E)`, `M` with
  `Dᵢ Qⱼ − δᵢⱼ M ∈ I(E)` and `M` a non-zero-divisor modulo `I(E)`.
-/

universe u

open MvPolynomial LSG.Elliptic

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Multihomogeneity bookkeeping -/

section Hom

variable (K) in
/-- The multihomogeneous polynomials of multidegree `d`. -/
noncomputable def homSub (d : Fin m → ℕ) : Submodule K (MvPolynomial (Var d₀ d₁ m) K) :=
  ⨅ k, weightedHomogeneousSubmodule K (wk k) (d k)

theorem mem_homSub {d : Fin m → ℕ} {P : MvPolynomial (Var d₀ d₁ m) K} :
    P ∈ homSub K d ↔ IsHomE P d := by
  simp only [homSub, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule, IsHomE]

theorem IsHomE.mul' {P Q : MvPolynomial (Var d₀ d₁ m) K} {a b : Fin m → ℕ} (hP : IsHomE P a)
    (hQ : IsHomE Q b) : IsHomE (P * Q) (a + b) := fun k => (hP k).mul (hQ k)

theorem IsHomE.prod' {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Var d₀ d₁ m) K)
    (e : ι → Fin m → ℕ) (h : ∀ i ∈ s, IsHomE (f i) (e i)) :
    IsHomE (∏ i ∈ s, f i) (∑ i ∈ s, e i) := fun k => by
  have := IsWeightedHomogeneous.prod s f (fun i => e i k) (fun i hi => h i hi k)
  simpa [Finset.sum_apply] using this

theorem isHomE_one : IsHomE (1 : MvPolynomial (Var d₀ d₁ m) K) 0 := fun _ =>
  isWeightedHomogeneous_one K _

/-- Determinants of matrices with entries of multidegree `e`. -/
theorem isHomE_det {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Var d₀ d₁ m) K))
    {e : Fin m → ℕ} (h : ∀ i j, IsHomE (A i j) e) : IsHomE A.det (n • e) := by
  rw [← mem_homSub, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_homSub]
  have := IsHomE.prod' Finset.univ (fun i => A (σ i) i) (fun _ => e) (fun i _ => h _ _)
  simpa using this

/-- Adjugates of matrices with entries of multidegree `e`. -/
theorem isHomE_adjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Var d₀ d₁ m) K))
    {e : Fin m → ℕ} (h : ∀ i j, IsHomE (A i j) e) (i j : Fin n) :
    IsHomE (A.adjugate i j) ((n - 1) • e) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hs : IsHomE ((-1 : MvPolynomial (Var d₀ d₁ m) K) ^ (j + i : ℕ)) 0 := by
      rcases neg_one_pow_eq_or (MvPolynomial (Var d₀ d₁ m) K) (j + i : ℕ) with h1 | h1 <;>
        rw [h1]
      · exact isHomE_one
      · rw [← mem_homSub]; exact neg_mem (mem_homSub.mpr isHomE_one)
    have := hs.mul' (isHomE_det (A.submatrix j.succAbove i.succAbove) fun a b => h _ _)
    simpa using this

/-- `V₁^{e₁} ⋯ V_m^{e_m}`. -/
noncomputable def Vpow (e : Fin m → ℕ) : MvPolynomial (Var d₀ d₁ m) K := ∏ k, X (.e k 1) ^ e k

theorem isHomE_Vpow (e : Fin m → ℕ) : IsHomE (Vpow e : MvPolynomial (Var d₀ d₁ m) K) e := by
  unfold Vpow
  have := IsHomE.prod' Finset.univ (fun k => (X (.e k 1) : MvPolynomial (Var d₀ d₁ m) K) ^ e k)
    (fun k => e k • Pi.single k 1) (fun k _ j => by
      have hX : IsWeightedHomogeneous (wk j) (X (.e k 1) : MvPolynomial (Var d₀ d₁ m) K)
          ((Pi.single k 1 : Fin m → ℕ) j) := by
        have := isWeightedHomogeneous_X K (wk j) (Var.e k 1 : Var d₀ d₁ m)
        convert this using 1
        by_cases hkj : k = j
        · subst hkj; simp [wk]
        · simp [wk, Ne.symm hkj, hkj]
      simpa using hX.pow (e k))
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

end Hom

/-! ### Linearity of `Dh` in `w` -/

theorem Dh_add_apply (ch : Fin m → Fin 3) (w w' : LieE K d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) K) :
    Dh g₂ g₃ ch (w + w') P = Dh g₂ g₃ ch w P + Dh g₂ g₃ ch w' P := by
  have : Dh g₂ g₃ ch (w + w') = Dh g₂ g₃ ch w + Dh g₂ g₃ ch w' := by
    apply MvPolynomial.derivation_ext
    intro v
    simp only [Derivation.add_apply, Dh_X]
    cases v <;> simp [dvalh, dval, mult] <;> ring
  rw [this, Derivation.add_apply]

theorem Dh_smul_apply (ch : Fin m → Fin 3) (a : K) (w : LieE K d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) K) : Dh g₂ g₃ ch (a • w) P = a • Dh g₂ g₃ ch w P := by
  have : Dh g₂ g₃ ch (a • w) = a • Dh g₂ g₃ ch w := by
    apply MvPolynomial.derivation_ext
    intro v
    simp only [Derivation.smul_apply, Dh_X]
    cases v <;> simp [dvalh, dval, mult, MvPolynomial.smul_eq_C_mul] <;> ring
  rw [this, Derivation.smul_apply]

/-! ### Translation to cosets -/

section Transport

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

theorem transl_mem_vanish_gtransl [IsAlgClosed K] (σ : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ vanish V) :
    τ g₂ g₃ (-σ) c P ∈ vanish (gtransl σ V) := by
  refine mem_vanish.mpr fun h hh lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl h2 hΔ (-σ) h c lam
  rw [hν]
  refine eval_coordsZ_eq_zero (mem_vanish.mp hP _ ?_) ν
  rw [← sub_eq_add_neg]; exact mem_gtransl.mp hh

theorem exists_transl_notMem [IsAlgClosed K] (σ : GPt K d₀ d₁ g₂ g₃)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} {N : MvPolynomial (Var d₀ d₁ m) K} (hN : N ∉ vanish V) :
    ∃ c, τ g₂ g₃ (-σ) c N ∉ vanish (gtransl σ V) := by
  obtain ⟨h', hh', lam', hne⟩ : ∃ h' ∈ V, ∃ lam', eval (coords h' lam') N ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN (mem_vanish.mpr hcon)
  obtain ⟨c, hc⟩ := exists_good h2 hΔ (h' + σ) (-σ)
  obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc
  obtain ⟨lam, hlam⟩ := exists_sq_mul μ lam'
  refine ⟨c, fun hmem => hne ?_⟩
  have := mem_vanish.mp hmem (h' + σ) (mem_gtransl.mpr (by simpa using hh')) lam
  rwa [hμ, hlam, add_neg_cancel_right] at this

/-- **Transport of transversal data** from `V` (chart `V` in every block) to `σ + V`
(chart `chartAt σ`). -/
theorem transport [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (h0 : (0 : GPt K d₀ d₁ g₂ g₃) ∈ V) {ℓ : ℕ}
    (w : Fin ℓ → LieE K d₀ d₁ m) (T : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K)
    (N : MvPolynomial (Var d₀ d₁ m) K) {d : Fin m → ℕ} (hTh : ∀ j, IsHomE (T j) d)
    (hT : ∀ j, T j ∈ vanish V) (hN : N ∉ vanish V)
    (hTδ : ∀ i j, Dh g₂ g₃ (fun _ => 1) (w i) (T j) - (if i = j then N else 0) ∈ vanish V)
    (σ : GPt K d₀ d₁ g₂ g₃) :
    ∃ (T' : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K) (N' : MvPolynomial (Var d₀ d₁ m) K),
      (∀ j, T' j ∈ vanish (gtransl σ V)) ∧ N' ∉ vanish (gtransl σ V) ∧
      ∀ i j, Dh g₂ g₃ (chartAt σ) (w i) (T' j) - (if i = j then N' else 0) ∈
        vanish (gtransl σ V) := by
  obtain ⟨c, hc⟩ := exists_transl_notMem h2 hΔ σ hN
  set C := gtransl σ V
  set τ' := τ g₂ g₃ (-σ) c
  set L1 : MvPolynomial (Var d₀ d₁ m) K := Lc d₀ d₁ (fun _ => 1)
  set Lσ : MvPolynomial (Var d₀ d₁ m) K := Lc d₀ d₁ (chartAt σ)
  have hpC : (vanish C).IsPrime := vanish_gtransl_isPrime h2 hΔ hV hp σ
  have hσC : σ ∈ C := mem_gtransl.mpr (by simpa using h0)
  have hτ : ∀ {P}, P ∈ vanish V → τ' P ∈ vanish C := fun hP =>
    transl_mem_vanish_gtransl h2 hΔ σ c hP
  refine ⟨fun j => τ' L1 * τ' (T j), Lσ * τ' N, fun j => Ideal.mul_mem_left _ _ (hτ (hT j)),
    fun hmem => ?_, fun i j => ?_⟩
  · rcases hpC.mem_or_mem hmem with h | h
    · exact eval_Lc_chartAt_ne σ 1 (mem_vanish.mp h σ hσC 1)
    · exact hc h
  · have hid := IG_le_vanish h2 C (tr_id h2 (chartAt_ne_zero σ) (fun _ => (by decide : (1 : Fin 3) ≠ 0)) (-σ) c (w i)
      (hTh j))
    have h1 := Ideal.mul_mem_left _ Lσ (hτ (hTδ i j))
    have h3 : ∑ k, te g₂ g₃ (-σ) c (chartAt σ) (fun _ => 1) (w i) k * (d k • τ' (T j)) ∈
        vanish C :=
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (by
        rw [nsmul_eq_mul]; exact Ideal.mul_mem_left _ _ (hτ (hT j)))
    have h4 := Ideal.mul_mem_right (Dh g₂ g₃ (chartAt σ) (w i) (τ' L1)) _ (hτ (hT j))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ hid h1) h3) h4
    convert this using 1
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sub]
    split_ifs <;> (try simp only [map_zero, sub_zero]) <;> ring

/-- **Wüstholz transversals for a finite union of translates**, from identity data. -/
theorem transversals_of_identity [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (h0 : (0 : GPt K d₀ d₁ g₂ g₃) ∈ V) {ℓ : ℕ}
    (w : Fin ℓ → LieE K d₀ d₁ m) (T : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K)
    (N : MvPolynomial (Var d₀ d₁ m) K) {d : Fin m → ℕ} (hTh : ∀ j, IsHomE (T j) d)
    (hT : ∀ j, T j ∈ vanish V) (hN : N ∉ vanish V)
    (hTδ : ∀ i j, Dh g₂ g₃ (fun _ => 1) (w i) (T j) - (if i = j then N else 0) ∈ vanish V)
    (R : Finset (GPt K d₀ d₁ g₂ g₃))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ (B : GPt K d₀ d₁ g₂ g₃ → MvPolynomial (Var d₀ d₁ m) K)
      (Q : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K) (M : MvPolynomial (Var d₀ d₁ m) K),
      (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a V)) ∧
      (∀ i j, (∑ a ∈ R, B a • Dh g₂ g₃ (chartAt a) (w i)) (Q j) - (if i = j then M else 0) ∈
        vanish (⋃ a ∈ R, gtransl a V)) ∧
      ∀ x, M * x ∈ vanish (⋃ a ∈ R, gtransl a V) → x ∈ vanish (⋃ a ∈ R, gtransl a V) := by
  classical
  choose T' N' hT' hN' hTδ' using transport h2 hΔ hV hp h0 w T N hTh hT hN hTδ
  have hpC : ∀ a, (vanish (gtransl a V)).IsPrime := fun a => vanish_gtransl_isPrime h2 hΔ hV hp a
  -- separators
  have hsep : ∀ a b : GPt K d₀ d₁ g₂ g₃, ∃ f : MvPolynomial (Var d₀ d₁ m) K,
      a ∈ R → b ∈ R → a ≠ b → f ∈ vanish (gtransl b V) ∧ f ∉ vanish (gtransl a V) := by
    intro a b
    by_cases h : a ∈ R ∧ b ∈ R ∧ a ≠ b
    · obtain ⟨f, hf1, hf2⟩ := exists_sep_proj (isZClosed_gtransl h2 hΔ hV b)
        (hdist a h.1 b h.2.1 h.2.2)
      exact ⟨f, fun _ _ _ => ⟨hf1, hf2⟩⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose f hf using hsep
  let B : GPt K d₀ d₁ g₂ g₃ → MvPolynomial (Var d₀ d₁ m) K := fun a => ∏ b ∈ R.erase a, f a b
  have hB : ∀ a ∈ R, B a ∉ vanish (gtransl a V) := by
    intro a ha hmem
    obtain ⟨b, hb, hfb⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpC a)).mp hmem
    exact (hf a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).2 hfb
  have hBo : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → B a ∈ vanish (gtransl b V) := by
    intro a ha b hb hab
    have hbe : b ∈ R.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    rw [show B a = f a b * ∏ x ∈ (R.erase a).erase b, f a x from
      (Finset.mul_prod_erase _ _ hbe).symm]
    exact Ideal.mul_mem_right _ _ (hf a b ha hb hab).1
  have hg := glue (K := K) R (fun a => vanish (gtransl a V)) (fun a _ => hpC a)
    (fun a i => Dh g₂ g₃ (chartAt a) (w i)) T' N' B (fun a _ => hT' a) (fun a _ => hTδ' a)
    (fun a _ => hN' a) hB hBo
  refine ⟨B, fun j => ∑ a ∈ R, B a ^ 2 * T' a j, ∑ a ∈ R, B a ^ 3 * N' a, fun j => ?_,
    fun i j => ?_, fun x hx => ?_⟩
  · exact (mem_vanish_biUnion R _).mpr fun a ha => (hg a ha).1 j
  · exact (mem_vanish_biUnion R _).mpr fun a ha => (hg a ha).2.1 i j
  · refine (mem_vanish_biUnion R _).mpr fun a ha => ?_
    exact ((hpC a).mem_or_mem ((mem_vanish_biUnion R _).mp hx a ha)).resolve_left (hg a ha).2.2

end Transport

end LSG.ME
