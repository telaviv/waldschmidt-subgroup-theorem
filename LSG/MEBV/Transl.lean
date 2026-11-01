/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.ModelIG
import LSG.MEBV.PhOpTwo

/-!
# Translations on the multi-cone model of `G̃` (M2.5, β)

The `VBlock` analogue of `LSG.MEB.Transl`. For `g ∈ G̃` and a law choice `c : ∀ k, Fin (B k).nLV`,
**`τ g c = lawSub c (coords g 1)`**: `x ↦ x + x_g`, `y ↦ y_g y`, `z ↦ y_g⁻¹ z`, and in block `k`,
`(X, T)_k ↦ lawV_{c k}((X, T)_k, rep g_k)`. Block degrees are multiplied by `ld_k` (MEB: by `2`).

* `VBlock.ld_pos`: the law degree is positive (else the lift would be projectively constant, and `(0, 1)` a
  period).
* `VBlock.evalLawV_rep`: `lawV_i(rep p, rep q) = κ • rep (p + q)` (from `lawV_eq` and `lift_add_perV`).
* `transl_mem_FLE`, `isHomV_transl`: degrees.
* **`eval_transl`**: `eval (coords h λ) (τ g c P) = eval (coordsZ (h + g) ν) P` for some `ν` (any `c`);
  **`eval_transl_good`**: for a good `c`, `ν = λ^{ld} μ`; `exists_good`, `exists_pow_mul`.
* `transl_mem_IGsem`; `transl_mem_vanish_gtransl`: `τ_{−σ}` maps `I(V)` into `I(σ + V)`.
* `translI g J = IGexp ⊔ (τ g c P : P ∈ J, all c)`; **`zeros_translI`**: `zeros (translI g J) = zeros J − g`.
-/

open MvPolynomial

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Laws on representatives -/

/-- **The law degree is positive.** With `ld = 0` the laws are constant, so `lawV_eq` would make the lift
projectively constant and `(0, 1)` a period, against `η 0 = 0`. -/
theorem VBlock.ld_pos (b : VBlock) : 0 < b.ld := by
  by_contra h0
  have hld : b.ld = 0 := by omega
  have hconst : ∀ i X Y, evalLawV (b.lawV i) X Y = evalLawV (b.lawV i) 0 0 := fun i X Y => by
    have := evalLawV_smul b i 0 0 X Y
    simpa [hld] using this.symm
  obtain ⟨i, hi⟩ := b.lawV_complete' 0 0
  obtain ⟨κ₀, h0'⟩ := b.lawV_eq' i 0 0
  obtain ⟨κ₁, h1⟩ := b.lawV_eq' i (0, 1) 0
  rw [hconst] at h0' h1 hi
  rw [h0'] at hi
  have hκ₀ : κ₀ ≠ 0 := fun h => hi (by rw [h, zero_smul])
  have hκ₁ : κ₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, h0'] at h1
    exact hi h1
  have h1' : κ₁ • b.lift ((0 : Fin b.g → ℂ), (1 : ℂ)) = κ₀ • b.lift 0 := by
    have := h1.symm.trans h0'
    rwa [add_zero, add_zero] at this
  have hrel : ∃ c : ℂ, b.lift (0, 1) = c • b.lift 0 :=
    ⟨κ₁⁻¹ * κ₀, by rw [mul_smul, ← h1', smul_smul, inv_mul_cancel₀ hκ₁, one_smul]⟩
  have hp := b.lift_ker 0 (0, 1) hrel
  rw [sub_zero, VBlock.mem_perV] at hp
  have := hp.2
  rw [b.η_zero] at this
  exact one_ne_zero this

/-- **Laws on representatives**: `lawV_i(rep p, rep q) = κ • rep (p + q)`. -/
theorem VBlock.evalLawV_rep (b : VBlock) (i : Fin b.nLV) (p q : b.Pt) :
    ∃ κ : ℂ, evalLawV (b.lawV i) (b.rep p) (b.rep q) = κ • b.rep (p + q) := by
  obtain ⟨κ, hκ⟩ := b.lawV_eq' i (Quotient.out p) (Quotient.out q)
  have hper : Quotient.out (p + q) - (Quotient.out p + Quotient.out q) ∈ b.perV := by
    have h1 : (QuotientAddGroup.mk (Quotient.out p + Quotient.out q) : b.Pt) = p + q := by
      rw [QuotientAddGroup.mk_add]
      exact congrArg₂ (· + ·) (Quotient.out_eq p) (Quotient.out_eq q)
    have := b.mk_out_sub (Quotient.out p + Quotient.out q)
    rwa [h1] at this
  obtain ⟨c, hc, h⟩ := b.lift_add_perV hper (Quotient.out p + Quotient.out q)
  refine ⟨κ / c, ?_⟩
  rw [VBlock.rep, VBlock.rep, VBlock.rep, hκ]
  have e : Quotient.out p + Quotient.out q + (Quotient.out (p + q) -
      (Quotient.out p + Quotient.out q)) = Quotient.out (p + q) := by abel
  rw [e] at h
  rw [h, smul_smul, div_mul_cancel₀ _ hc]

/-! ### The translation -/

/-- **Translation by `g`** with law choice `c`. -/
noncomputable def τ (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) ℂ :=
  lawSub c (coords g 1)

theorem τ_def (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) : τ g c = lawSub c (coords g 1) := rfl

theorem transl_mem_FLE (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    τ g c P ∈ StrongSix.M2.FLE ℂ blk (dblB B D) :=
  lawSub_mem_FLE c _ hP

theorem isHomV_transl (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) :
    IsHomV (τ g c P) (ldMul B d) :=
  isHomV_lawSub c _ hP

/-- The block-`k` law value at `(λ_k rep h_k, rep g_k)`. -/
theorem lawPt_coords_e (c : ∀ k, Fin (B k).nLV) (h g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (k : Fin m) :
    (fun a => lawPt c (coords h lam) (coords g 1) (.e k a)) =
      ((lam k : ℂ) ^ (B k).ld) • evalLawV ((B k).lawV (c k)) ((B k).rep (h.2.2 k))
        ((B k).rep (g.2.2 k)) := by
  have e1 : (fun b => coords h lam (.e k b)) = (lam k : ℂ) • (B k).rep (h.2.2 k) := by
    funext b; simp [coords]
  have e2 : (fun b => coords g 1 (.e k b)) = (1 : ℂ) • (B k).rep (g.2.2 k) := by
    funext b; simp [coords]
  funext a
  simp only [lawPt]
  rw [e1, e2, evalLawV_smul]
  simp

/-- **Evaluation of a translate** (any law choice). -/
theorem eval_transl (g h : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) (lam : Fin m → ℂˣ) :
    ∃ ν : Fin m → ℂ, ∀ P, eval (coords h lam) (τ g c P) = eval (coordsZ (h + g) ν) P := by
  choose κ hκ using fun k => (B k).evalLawV_rep (c k) (h.2.2 k) (g.2.2 k)
  refine ⟨fun k => (lam k : ℂ) ^ (B k).ld * κ k, fun P => ?_⟩
  rw [τ, eval_lawSub]
  refine congrArg (fun f => eval f P) (funext fun v => ?_)
  cases v with
  | x i => simp [lawPt, coordsZ, coords, add_comm]
  | y j => simp [lawPt, coordsZ, coords, mul_comm]
  | z j => simp [lawPt, coordsZ, coords, mul_comm]
  | e k a =>
    have := congrFun (lawPt_coords_e c h g lam k) a
    simp only [Pi.smul_apply] at this
    rw [this, hκ k]
    simp [coordsZ, mul_assoc]

/-- The law choice `c` is **good** at `(h, g)`: every chosen law is nonzero there. -/
def Good (h g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) : Prop :=
  ∀ k, evalLawV ((B k).lawV (c k)) ((B k).rep (h.2.2 k)) ((B k).rep (g.2.2 k)) ≠ 0

theorem VBlock.exists_law_ne (b : VBlock) (p q : b.Pt) :
    ∃ i, evalLawV (b.lawV i) (b.rep p) (b.rep q) ≠ 0 :=
  b.lawV_complete' _ _

theorem exists_good (h g : GPt d₀ d₁ B) : ∃ c, Good h g c := by
  choose c hc using fun k => (B k).exists_law_ne (h.2.2 k) (g.2.2 k)
  exact ⟨c, hc⟩

/-- **Evaluation of a translate**, good law choice: `ν = λ^{ld} μ` with `μ` independent of `λ`. -/
theorem eval_transl_good {g h : GPt d₀ d₁ B} {c : ∀ k, Fin (B k).nLV} (hc : Good h g c) :
    ∃ μ : Fin m → ℂˣ, ∀ lam P, eval (coords h lam) (τ g c P) =
      eval (coords (h + g) fun k => lam k ^ (B k).ld * μ k) P := by
  choose κ hκ using fun k => (B k).evalLawV_rep (c k) (h.2.2 k) (g.2.2 k)
  have hκ0 : ∀ k, κ k ≠ 0 := fun k h0 => hc k (by rw [hκ k, h0, zero_smul])
  refine ⟨fun k => Units.mk0 (κ k) (hκ0 k), fun lam P => ?_⟩
  rw [τ, eval_lawSub]
  refine congrArg (fun f => eval f P) (funext fun v => ?_)
  cases v with
  | x i => simp [lawPt, coords, add_comm]
  | y j => simp [lawPt, coords, mul_comm]
  | z j => simp [lawPt, coords, mul_comm]
  | e k a =>
    have := congrFun (lawPt_coords_e c h g lam k) a
    simp only [Pi.smul_apply] at this
    rw [this, hκ k]
    simp [coords, mul_assoc]

/-- Every `ν ∈ (ℂˣ)^m` is `λ^{ld} μ` for some `λ`. -/
theorem exists_pow_mul (μ ν : Fin m → ℂˣ) :
    ∃ lam : Fin m → ℂˣ, (fun k => lam k ^ (B k).ld * μ k) = ν := by
  have : ∀ k, ∃ z : ℂˣ, z ^ (B k).ld * μ k = ν k := fun k => by
    have hld := (B k).ld_pos
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((ν k : ℂ) / μ k) hld
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hld.ne'] at hz
      exact div_ne_zero (ν k).ne_zero (μ k).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
    field_simp
  choose lam hlam using this
  exact ⟨lam, funext hlam⟩

/-! ### Ideals -/

/-- **`τ` preserves `IGsem`.** -/
theorem transl_mem_IGsem (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ IGsem d₀ d₁ B) : τ g c P ∈ IGsem d₀ d₁ B := by
  refine mem_vanish.mpr fun h _ lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl g h c lam
  rw [hν]
  exact mem_IGsem_iff_coordsZ.mp hP _ _

/-- `τ_{−σ}` maps `I(V)` into `I(σ + V)`. -/
theorem transl_mem_vanish_gtransl (σ : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV)
    {V : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ vanish V) :
    τ (-σ) c P ∈ vanish (gtransl σ V) := by
  refine mem_vanish.mpr fun h hh lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl (-σ) h c lam
  rw [hν]
  refine eval_coordsZ_eq_zero (fun lam' => mem_vanish.mp hP _ ?_ lam') ν
  have := mem_gtransl.mp hh
  rwa [sub_eq_add_neg] at this

variable (d₀ d₁ B) in
/-- The ideal translate `τ_g J = IGexp + (τ g c P : P ∈ J, all c)`; its zeros are `zeros J − g`. -/
noncomputable def translI (g : GPt d₀ d₁ B) (J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  IGexp d₀ d₁ B ⊔ Ideal.span {Q | ∃ P ∈ J, ∃ c, Q = τ g c P}

/-- **Zeros of an ideal translate.** -/
theorem zeros_translI (g : GPt d₀ d₁ B) (J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    zeros (translI d₀ d₁ B g J : Set _) = {h | h + g ∈ zeros (J : Set _)} := by
  ext h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh P hP lam'
    obtain ⟨c, hc⟩ := exists_good h g
    obtain ⟨μ, hμ⟩ := eval_transl_good hc
    obtain ⟨lam, hlam⟩ := exists_pow_mul μ lam'
    have := hh _ (Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, c, rfl⟩)) lam
    rw [hμ, hlam] at this
    exact this
  · intro hh
    rw [mem_zeros_iff_le_vanish]
    refine sup_le (IGexp_le_vanish _) (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, hP, c, rfl⟩
    refine mem_vanish.mpr fun h' hh' lam => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    obtain ⟨ν, hν⟩ := eval_transl g h' c lam
    rw [hν]
    exact eval_coordsZ_eq_zero (hh P hP) ν

end LSG.MEBV
