/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupTZ
import LSG.MEB.SubgroupImm

/-!
# The lift is an immersion; tangent vectors of lifted curves (M2.5 β′; template `LSG.MEB.SubgroupImm`)

* **`VBlock.bD_inj`**: the block lift `(z, w) ↦ (θ(z), T(z, w))` is a projective immersion: a derivative
  `bD z w ζ ω ∈ ℂ · lift (z, w)` forces `(ζ, ω) = 0`. The base part is `AbBlock.fderiv_inj`; then `c = 0` and
  `∂_wT_t = θ_{fc t}` with `exists_fc_ne` kill `ω`. (No addition law is needed.)
* `dLZ u μ w σ`: the derivative of `r ↦ liftZ (u + r w) (μ + r σ)`; **`dLZl_injective`** for nonzero scalings.
* **`dLZ_mem_tangentSpace`**, **`dirD_eq_zero_of_tangent`** (Zariski tangent spaces, `LSG.ME.tangentSpace`).
-/

open MvPolynomial Filter Topology Set

namespace LSG.MEBV

/-! ### The block lift is a projective immersion -/

namespace VBlock

variable (b : VBlock)

/-- **The block lift is a projective immersion.** -/
theorem bD_inj {z : Fin b.g → ℂ} {w : ℂ} {ζ : Fin b.g → ℂ} {ω c : ℂ}
    (h : b.bD z w ζ ω = c • b.lift (z, w)) : ζ = 0 ∧ ω = 0 := by
  have hX : fderiv ℂ b.base.θ z ζ = c • b.base.θ z := funext fun l => by
    simpa [bD] using congrFun h (Sum.inl l)
  have hζ : ζ = 0 := b.base.fderiv_inj hX
  subst hζ
  have hc : c = 0 := by
    obtain ⟨l, hl⟩ : ∃ l, b.base.θ z l ≠ 0 := by
      by_contra hcon; push Not at hcon; exact b.base.θ_ne z (funext hcon)
    have := congrFun hX l
    simp only [map_zero, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hl
  subst hc
  obtain ⟨t, ht⟩ := b.exists_fc_ne z
  have := congrFun h (Sum.inr t)
  simp only [bD, map_zero, Pi.zero_apply, zero_mul, sub_zero, zero_add, zero_smul] at this
  exact ⟨rfl, (mul_eq_zero.mp this).resolve_right ht⟩

end VBlock

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The derivative of the lift -/

/-- The derivative of `r ↦ liftZ (u + r w) (μ + r σ)` at `0`. -/
noncomputable def dLZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) (w : Tan d₀ d₁ B) (σ : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * Complex.exp (u.2.1 j)
  | .z j => -w.2.1 j * Complex.exp (-u.2.1 j)
  | .e k a => σ k * (B k).lift (u.blkV k) a +
      μ k * (B k).bD (u.2.2.1 k) (u.2.2.2 k) (w.2.2.1 k) (w.2.2.2 k) a

theorem hasDerivAt_liftZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) (w : Tan d₀ d₁ B) (σ : Fin m → ℂ)
    (v : Var d₀ d₁ B) :
    HasDerivAt (fun r : ℂ => liftZ (u + r • w) (μ + r • σ) v) (dLZ u μ w σ v) 0 := by
  have hB := hasDerivAt_liftV u w v
  cases v with
  | x i => simpa [liftZ, liftV, liftV', dLZ] using hB
  | y j => simpa [liftZ, liftV, liftV', dLZ] using hB
  | z j => simpa [liftZ, liftV, liftV', dLZ] using hB
  | e k l =>
    have hμ : HasDerivAt (fun r : ℂ => μ k + r * σ k) (σ k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ k)).const_add (μ k)
    have := hμ.mul hB
    simp only [liftV, liftV', zero_smul, add_zero, zero_mul] at this
    convert this using 1
    · funext r; simp [liftZ]
    · simp only [dLZ, Tan.blkV]

/-- `dLZ u μ` as a linear map on `Tan × ℂ^m`. -/
noncomputable def dLZl (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    (Tan d₀ d₁ B × (Fin m → ℂ)) →ₗ[ℂ] (Var d₀ d₁ B → ℂ) where
  toFun p := dLZ u μ p.1 p.2
  map_add' p q := by
    funext v
    cases v with
    | x i => simp [dLZ]
    | y j => simp [dLZ]; ring
    | z j => simp [dLZ]; ring
    | e k a =>
      cases a <;> simp [dLZ, VBlock.bD, map_add] <;> ring
  map_smul' a p := by
    funext v
    cases v with
    | x i => simp [dLZ]
    | y j => simp [dLZ]; ring
    | z j => simp [dLZ]; ring
    | e k a =>
      cases a <;> simp [dLZ, VBlock.bD, map_smul] <;> ring

theorem dLZl_apply (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) (p : Tan d₀ d₁ B × (Fin m → ℂ)) :
    dLZl u μ p = dLZ u μ p.1 p.2 := rfl

/-- **`dLZ` is injective** for nonzero scalings. -/
theorem dLZl_injective {u : Tan d₀ d₁ B} {μ : Fin m → ℂ} (hμ : ∀ k, μ k ≠ 0) :
    Function.Injective (dLZl u μ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, σ⟩ h
  rw [dLZl_apply] at h
  have hx : w.1 = 0 := funext fun i => by simpa [dLZ] using congrFun h (.x i)
  have hy : w.2.1 = 0 := funext fun j => by
    have := congrFun h (.y j)
    simpa [dLZ, Complex.exp_ne_zero] using this
  have hb : ∀ k, w.2.2.1 k = 0 ∧ w.2.2.2 k = 0 := fun k => by
    refine (B k).bD_inj (z := u.2.2.1 k) (w := u.2.2.2 k) (c := -σ k / μ k) ?_
    funext a
    have := congrFun h (.e k a)
    simp only [dLZ, Pi.zero_apply, Tan.blkV] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hμ k]
    linear_combination this
  have hw : w = 0 := Prod.ext hx (Prod.ext hy (Prod.ext (funext fun k => (hb k).1)
    (funext fun k => (hb k).2)))
  have hσ : σ = 0 := funext fun k => by
    obtain ⟨a, ha⟩ : ∃ a, (B k).lift (u.blkV k) a ≠ 0 := by
      by_contra hc; push Not at hc; exact (B k).lift_ne_zero _ (funext hc)
    have := congrFun h (.e k a)
    simp only [dLZ, hw, Pi.zero_apply] at this
    have hbD : (B k).bD (u.2.2.1 k) (u.2.2.2 k) 0 0 a = 0 := by
      cases a <;> simp [VBlock.bD]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, hbD, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right ha
  simp [hw, hσ]

/-! ### Tangent vectors -/

theorem eval_liftZ_eq_zero_of_mem_vanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ vanish E) {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ E) (μ : Fin m → ℂ) :
    eval (liftZ u μ) P = 0 := by
  obtain ⟨lam₀, h0⟩ := coords_expG u
  rw [liftZ_eq_coordsZ h0]
  exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ hu lam) _

/-- **Lifted curves give tangent vectors.** -/
theorem dLZ_mem_tangentSpace {E : Set (GPt d₀ d₁ B)} {u w : Tan d₀ d₁ B} (μ σ : Fin m → ℂ)
    (hE : ∀ r : ℂ, expG d₀ d₁ B (u + r • w) ∈ E) :
    dLZ u μ w σ ∈ LSG.ME.tangentSpace (vanish E) (liftZ u μ) := by
  have := LSG.MEB.tangent_of_curve (p := vanish E) (x := fun r => liftZ (u + r • w) (μ + r • σ))
    (hasDerivAt_liftZ u μ w σ) fun r f hf => eval_liftZ_eq_zero_of_mem_vanish hf (hE r) _
  simpa using this

/-- **The first derivative along a tangent direction vanishes.** -/
theorem dirD_eq_zero_of_tangent {E : Set (GPt d₀ d₁ B)} {f : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hf : IsHomV f d) (hfv : f ∈ vanish E) {u w : Tan d₀ d₁ B} {μ : Fin m → ℂ} (hμ : ∀ k, μ k ≠ 0)
    (hv : dLZ u μ w 0 ∈ LSG.ME.tangentSpace (vanish E) (liftZ u μ)) : dirD f u w = 0 := by
  have hx : ∀ v, HasDerivAt (fun r : ℂ => liftZ (u + r • w) μ v) (dLZ u μ w 0 v) 0 := fun v => by
    simpa using hasDerivAt_liftZ u μ w 0 v
  have h1 := LSG.MEB.hasDerivAt_eval hx f
  have e : (fun r : ℂ => eval (liftZ (u + r • w) μ) f) =
      fun r => (∏ k, μ k ^ d k) * eval (liftV (u + r • w)) f := by
    funext r
    have := eval_liftZ_mul hf (u + r • w) 1 μ
    rwa [one_mul, liftZ_one] at this
  rw [e] at h1
  have h2 : HasDerivAt (fun r : ℂ => (∏ k, μ k ^ d k) * eval (liftV (u + r • w)) f)
      ((∏ k, μ k ^ d k) * dirD f u w) 0 := by
    refine HasDerivAt.const_mul _ ?_
    have hd : DifferentiableAt ℂ (fun r : ℂ => eval (liftV (u + r • w)) f) 0 :=
      (LSG.MEB.analyticAt_eval_of (f := fun v (r : ℂ) => liftV (u + r • w) v)
        (fun v => analyticAt_liftV_comp (by fun_prop) v) f).differentiableAt
    exact hd.hasDerivAt
  have h3 := h1.unique h2
  have h4 : ∑ v, eval (liftZ (u + (0 : ℂ) • w) μ) (pderiv v f) * dLZ u μ w 0 v = 0 := by
    have := hv f hfv
    simp only [zero_smul, add_zero]
    rw [← this]; exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [h4] at h3
  have hprod : (∏ k, μ k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hμ k)
  exact (mul_eq_zero.mp h3.symm).resolve_left hprod

end LSG.MEBV
