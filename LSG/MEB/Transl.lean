/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.ModelIG
import LSG.MEB.PhOpLaw

/-!
# Translations on the multi-cone model (A4.2, α)

For `g ∈ G` and a law choice `c : ∀ k, Fin (B k).nL`, **`τ g c = lawSub c (coords g 1)`** (β's substitution,
`LSG.MEB.PhOpLaw`, as agreed in STAGE_A4 §7.3): `x ↦ x + x_g`, `y ↦ y_g y`, `z ↦ y_g⁻¹ z`, and in block `k`,
`X_k ↦ law_{c k}(X_k, rep g_k)`.

Everything here is **semantic**: the only input on the laws is `law_hom` and `law_eq`/`law_complete` on the
image of `θ`; there is no polynomial identity.

* `evalLaw_smul_hom`: laws are bihomogeneous of bidegree `(2, 2)`.
* `evalLaw_rep`: `law_i(rep p, rep q) = κ • rep (p + q)` (from `law_eq` and `θ_per`).
* `transl_mem_FLE`, `isHomB_transl`: degrees (β's `lawSub_mem_FLE`, `isHomB_lawSub`).
* **`eval_transl`**: `eval (coords h λ) (τ g c P) = eval (coordsZ (h + g) ν) P` for some `ν` (any `c`);
  **`eval_transl_good`**: for a good `c` (`Good`), `ν = λ² μ` with `μ : Fin m → ℂˣ` independent of `λ`, `P`;
  `exists_good` (`law_complete`), `exists_sq_mul`.
* `transl_mem_IGsem`: `τ g c` preserves `IGsem`; `transl_mem_vanish_gtransl`: `τ_{−σ}` maps `I(V)` into
  `I(σ + V)`.
* `translI g J = IGexp ⊔ (τ g c P : P ∈ J, all c)`; **`zeros_translI`**: `zeros (translI g J) = zeros J − g`.
-/

open MvPolynomial

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Laws on representatives -/

theorem evalLaw_smul_hom {N : ℕ} {L : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℂ}
    (hL : ∀ k, (L k).IsWeightedHomogeneous (biW N) ((2, 2) : ℕ × ℕ)) (a b : ℂ) (X Y : Fin N → ℂ) :
    evalLaw L (a • X) (b • Y) = (a ^ 2 * b ^ 2) • evalLaw L X Y := by
  funext k
  have h1 : IsWeightedHomogeneous (AddMonoidHom.fst ℕ ℕ ∘ biW N) (L k) 2 :=
    isWH_map_weight (hL k) (AddMonoidHom.fst ℕ ℕ)
  have h2 : IsWeightedHomogeneous (AddMonoidHom.snd ℕ ℕ ∘ biW N) (L k) 2 :=
    isWH_map_weight (hL k) (AddMonoidHom.snd ℕ ℕ)
  have s1 := eval_scale (κ := Unit) (fun v _ => (AddMonoidHom.fst ℕ ℕ ∘ biW N) v) (fun _ => a)
    (Sum.elim X (b • Y)) (Q := L k) (d := fun _ => 2)
    (fun s hs => funext fun _ => by
      rw [← h1 hs, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
        Finset.sum_apply]; rfl)
  have s2 := eval_scale (κ := Unit) (fun v _ => (AddMonoidHom.snd ℕ ℕ ∘ biW N) v) (fun _ => b)
    (Sum.elim X Y) (Q := L k) (d := fun _ => 2)
    (fun s hs => funext fun _ => by
      rw [← h2 hs, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
        Finset.sum_apply]; rfl)
  simp only [Finset.univ_unique, Finset.prod_singleton] at s1 s2
  have e1 : (fun v => a ^ (AddMonoidHom.fst ℕ ℕ ∘ biW N) v * Sum.elim X (b • Y) v) =
      Sum.elim (a • X) (b • Y) := by
    funext v; cases v <;> simp [biW]
  have e2 : (fun v => b ^ (AddMonoidHom.snd ℕ ℕ ∘ biW N) v * Sum.elim X Y v) =
      Sum.elim X (b • Y) := by
    funext v; cases v <;> simp [biW]
  simp only [evalLaw, Pi.smul_apply, smul_eq_mul]
  rw [← e1, s1, ← e2, s2]
  ring

/-- **Laws on representatives**: `law_i(rep p, rep q) = κ • rep (p + q)`. -/
theorem AbBlock.evalLaw_rep (b : AbBlock) (i : Fin b.nL) (p q : b.Pt) :
    ∃ κ : ℂ, evalLaw (b.law i) (b.rep p) (b.rep q) = κ • b.rep (p + q) := by
  obtain ⟨κ, hκ⟩ := b.law_eq i (Quotient.out p) (Quotient.out q)
  have hper : Quotient.out (p + q) - (Quotient.out p + Quotient.out q) ∈ b.per := by
    have h1 : (QuotientAddGroup.mk (Quotient.out p + Quotient.out q) : b.Pt) = p + q := by
      rw [QuotientAddGroup.mk_add]
      exact congrArg₂ (· + ·) (Quotient.out_eq p) (Quotient.out_eq q)
    have := b.mk_out_sub (Quotient.out p + Quotient.out q)
    rwa [h1] at this
  obtain ⟨c, hc, h⟩ := b.θ_per _ hper (Quotient.out p + Quotient.out q)
  refine ⟨κ / c, ?_⟩
  rw [AbBlock.rep, AbBlock.rep, AbBlock.rep, hκ]
  have e : Quotient.out p + Quotient.out q + (Quotient.out (p + q) -
      (Quotient.out p + Quotient.out q)) = Quotient.out (p + q) := by abel
  rw [e] at h
  rw [h, smul_smul, div_mul_cancel₀ _ hc]

/-! ### The translation -/

/-- **Translation by `g`** with law choice `c`. -/
noncomputable def τ (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) ℂ :=
  lawSub c (coords g 1)

theorem τ_def (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL) : τ g c = lawSub c (coords g 1) := rfl

theorem transl_mem_FLE (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    τ g c P ∈ StrongSix.M2.FLE ℂ blk (dblB D) :=
  lawSub_mem_FLE c _ hP

theorem isHomB_transl (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) :
    IsHomB (τ g c P) (2 • d) :=
  isHomB_lawSub c _ hP

/-- The block-`k` law value at `(λ_k rep h_k, rep g_k)`. -/
theorem lawPt_coords_e (c : ∀ k, Fin (B k).nL) (h g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (k : Fin m) :
    (fun a => lawPt c (coords h lam) (coords g 1) (.e k a)) =
      ((lam k : ℂ) ^ 2) • evalLaw ((B k).law (c k)) ((B k).rep (h.2.2 k)) ((B k).rep (g.2.2 k)) := by
  have e1 : (fun b => coords h lam (.e k b)) = (lam k : ℂ) • (B k).rep (h.2.2 k) := by
    funext b; simp
  have e2 : (fun b => coords g 1 (.e k b)) = (1 : ℂ) • (B k).rep (g.2.2 k) := by
    funext b; simp
  funext a
  simp only [lawPt]
  rw [e1, e2, evalLaw_smul_hom ((B k).law_hom (c k))]
  simp

/-- **Evaluation of a translate** (any law choice). -/
theorem eval_transl (g h : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL) (lam : Fin m → ℂˣ) :
    ∃ ν : Fin m → ℂ, ∀ P, eval (coords h lam) (τ g c P) = eval (coordsZ (h + g) ν) P := by
  choose κ hκ using fun k => (B k).evalLaw_rep (c k) (h.2.2 k) (g.2.2 k)
  refine ⟨fun k => (lam k : ℂ) ^ 2 * κ k, fun P => ?_⟩
  rw [τ, eval_lawSub]
  refine congrArg (fun f => eval f P) (funext fun v => ?_)
  cases v with
  | x i => simp [lawPt, coordsZ, add_comm]
  | y j => simp [lawPt, coordsZ, mul_comm]
  | z j => simp [lawPt, coordsZ, mul_comm]
  | e k a =>
    have := congrFun (lawPt_coords_e c h g lam k) a
    simp only [Pi.smul_apply] at this
    rw [this, hκ k]
    simp [coordsZ, mul_assoc]

/-- The law choice `c` is **good** at `(h, g)`: every chosen law is nonzero there. -/
def Good (h g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL) : Prop :=
  ∀ k, evalLaw ((B k).law (c k)) ((B k).rep (h.2.2 k)) ((B k).rep (g.2.2 k)) ≠ 0

theorem AbBlock.exists_law_ne (b : AbBlock) (p q : b.Pt) :
    ∃ i, evalLaw (b.law i) (b.rep p) (b.rep q) ≠ 0 :=
  b.law_complete _ _

theorem exists_good (h g : GPt d₀ d₁ B) : ∃ c, Good h g c := by
  choose c hc using fun k => (B k).exists_law_ne (h.2.2 k) (g.2.2 k)
  exact ⟨c, hc⟩

/-- **Evaluation of a translate**, good law choice: `ν = λ² μ` with `μ` independent of `λ`. -/
theorem eval_transl_good {g h : GPt d₀ d₁ B} {c : ∀ k, Fin (B k).nL} (hc : Good h g c) :
    ∃ μ : Fin m → ℂˣ, ∀ lam P, eval (coords h lam) (τ g c P) =
      eval (coords (h + g) fun k => lam k ^ 2 * μ k) P := by
  choose κ hκ using fun k => (B k).evalLaw_rep (c k) (h.2.2 k) (g.2.2 k)
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

/-- Every `ν ∈ (ℂˣ)^m` is `λ² μ` for some `λ`. -/
theorem exists_sq_mul (μ ν : Fin m → ℂˣ) :
    ∃ lam : Fin m → ℂˣ, (fun k => lam k ^ 2 * μ k) = ν := by
  have : ∀ k, ∃ z : ℂˣ, z ^ 2 * μ k = ν k := fun k => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((ν k : ℂ) / μ k) (n := 2) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
      exact div_ne_zero (ν k).ne_zero (μ k).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
    field_simp
  choose lam hlam using this
  exact ⟨lam, funext hlam⟩

/-! ### Ideals -/

/-- **`τ` preserves `IGsem`.** -/
theorem transl_mem_IGsem (g : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ IGsem d₀ d₁ B) : τ g c P ∈ IGsem d₀ d₁ B := by
  refine mem_vanish.mpr fun h _ lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl g h c lam
  rw [hν]
  exact mem_IGsem_iff_coordsZ.mp hP _ _

/-- `τ_{−σ}` maps `I(V)` into `I(σ + V)`. -/
theorem transl_mem_vanish_gtransl (σ : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nL)
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
    obtain ⟨lam, hlam⟩ := exists_sq_mul μ lam'
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

end LSG.MEB
