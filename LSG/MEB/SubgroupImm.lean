/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupTZ
import LSG.ME.SmoothPoint

/-!
# The lift is an immersion; tangent vectors of lifted curves (A4.3, β′)

* **`AbBlock.fderiv_inj`**: `θ` is a projective immersion at every point: `dθ_z(w) ∈ ℂ θ(z)` forces `w = 0`. At `0`
  this is `coords_locInv`; at `z` translate by `-z` with a law that is nonzero at `(θ z, θ (-z))`, and compare the
  derivative of `s ↦ law(θ(z + s w), θ(-z))` with that of `s ↦ law((1 + s c) θ z, θ(-z))` (degree `2` in the first
  argument).
* `dLZ u μ w σ`: the derivative of `r ↦ liftZ (u + r w) (μ + r σ)` (`hasDerivAt_liftZ`); `dLZl u μ` the linear map.
  **`dLZ_injective`** for nonzero scalings.
* **`dLZ_mem_tangentSpace`**: lifted curves in the cone of `E` give Zariski tangent vectors of `vanish E`
  (`LSG.ME.tangentSpace`).
* **`dirD_eq_zero_of_tangent`**: if `dLZ u μ w 0` is tangent to `vanish E` at `liftZ u μ`, then the first derivative
  along `w` of every multihomogeneous `f ∈ vanish E` vanishes at `u`.
-/

open MvPolynomial Filter Topology Set

namespace LSG.MEB

/-! ### `θ` is a projective immersion -/

namespace AbBlock

variable (b : AbBlock)

theorem hasDerivAt_θ_line (z w : Fin b.g → ℂ) :
    HasDerivAt (fun s : ℂ => b.θ (z + s • w)) (fderiv ℂ b.θ z w) 0 := by
  have hθ : HasFDerivAt b.θ (fderiv ℂ b.θ z) (z + (0 : ℂ) • w) := by
    simpa using (b.θ_analytic z).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun r : ℂ => z + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add z
  simpa [Function.comp_def] using hθ.comp_hasDerivAt (0 : ℂ) hl

theorem fderiv_inj_zero {w : Fin b.g → ℂ} {c : ℂ} (h : fderiv ℂ b.θ 0 w = c • b.θ 0) : w = 0 := by
  obtain ⟨f', hf'⟩ := b.coords_locInv
  have hγ := b.hasDerivAt_θ_line 0 w
  simp only [zero_add] at hγ
  have hl : HasDerivAt (fun s : ℂ => s • w) w 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have h1 : HasDerivAt (fun s : ℂ => fun j => b.θ (s • w) (b.is j) / b.θ (s • w) b.i₀) (f' w) 0 :=
    hf'.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  have h2 : HasDerivAt (fun s : ℂ => fun j => b.θ (s • w) (b.is j) / b.θ (s • w) b.i₀) 0 0 := by
    refine hasDerivAt_pi.mpr fun j => ?_
    have ha := hasDerivAt_pi.mp hγ (b.is j)
    have hb := hasDerivAt_pi.mp hγ b.i₀
    have := ha.div hb (by simpa using b.θ_i₀)
    convert this using 1
    simp only [h, Pi.smul_apply, smul_eq_mul, zero_smul, Pi.zero_apply]
    ring
  have : (f' : (Fin b.g → ℂ) →L[ℂ] (Fin b.g → ℂ)) w = 0 := h1.unique h2
  exact f'.injective (by simpa using this)

/-- **`θ` is a projective immersion** at every point. -/
theorem fderiv_inj {z w : Fin b.g → ℂ} {c : ℂ} (h : fderiv ℂ b.θ z w = c • b.θ z) : w = 0 := by
  obtain ⟨i, hi⟩ := b.law_complete z (-z)
  obtain ⟨a, ha⟩ : ∃ a, b.θ 0 a ≠ 0 := by
    by_contra hc; push Not at hc; exact b.θ_ne 0 (funext hc)
  -- `F s = law(θ(z + s w), θ(-z))`
  set F : ℂ → Fin b.N → ℂ := fun s => evalLaw (b.law i) (b.θ (z + s • w)) (b.θ (-z))
  set F0 := evalLaw (b.law i) (b.θ z) (b.θ (-z))
  set x0 : Fin b.N ⊕ Fin b.N → ℂ := Sum.elim (b.θ z) (b.θ (-z))
  set x' : Fin b.N ⊕ Fin b.N → ℂ := Sum.elim (c • b.θ z) 0
  set D : Fin b.N → ℂ := fun l => ∑ v, eval x0 (pderiv v (b.law i l)) * x' v
  have hF : HasDerivAt F D 0 := by
    refine hasDerivAt_pi.mpr fun l => ?_
    have hx : ∀ v, HasDerivAt (fun r : ℂ => Sum.elim (b.θ (z + r • w)) (b.θ (-z)) v) (x' v) 0 := by
      rintro (l' | l')
      · simpa [x', h] using hasDerivAt_pi.mp (b.hasDerivAt_θ_line z w) l'
      · simpa [x'] using hasDerivAt_const (0 : ℂ) (b.θ (-z) l')
    have := hasDerivAt_eval hx (b.law i l)
    simp only [zero_smul, add_zero] at this
    exact this
  -- `G s = law((1 + s c) θ z, θ(-z)) = (1 + s c)² F0`
  have hG : HasDerivAt (fun s : ℂ => evalLaw (b.law i) ((1 + s * c) • b.θ z) (b.θ (-z))) D 0 := by
    refine hasDerivAt_pi.mpr fun l => ?_
    have hx : ∀ v, HasDerivAt (fun r : ℂ => Sum.elim ((1 + r * c) • b.θ z) (b.θ (-z)) v) (x' v) 0 := by
      rintro (l' | l')
      · simpa [x'] using (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add 1).mul_const (b.θ z l')
      · simpa [x'] using hasDerivAt_const (0 : ℂ) (b.θ (-z) l')
    have := hasDerivAt_eval hx (b.law i l)
    simp only [zero_mul, add_zero, one_smul] at this
    exact this
  have hG' : HasDerivAt (fun s : ℂ => evalLaw (b.law i) ((1 + s * c) • b.θ z) (b.θ (-z))) ((2 * c) • F0) 0 := by
    have e : (fun s : ℂ => evalLaw (b.law i) ((1 + s * c) • b.θ z) (b.θ (-z))) =
        fun s => (1 + s * c) ^ 2 • F0 := by
      funext s
      have := evalLaw_smul b i (1 + s * c) 1 (b.θ z) (b.θ (-z))
      simpa using this
    rw [e]
    have h1 : HasDerivAt (fun s : ℂ => (1 + s * c) ^ 2) (2 * c) 0 := by
      have h0 : HasDerivAt (fun s : ℂ => 1 + s * c) c 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c).const_add 1
      convert h0.mul h0 using 1
      · funext s; simp only [Pi.mul_apply]; ring
      · simp; ring
    exact h1.smul_const F0
  have hDeq : D = (2 * c) • F0 := hG.unique hG'
  -- `F s = κ s • θ (s w)` near `0`
  set κf : ℂ → ℂ := fun s => F s a / b.θ (s • w) a
  have hθa : ∀ᶠ s in 𝓝 (0 : ℂ), b.θ (s • w) a ≠ 0 := by
    have hc : ContinuousAt (fun s : ℂ => b.θ (s • w) a) 0 :=
      (continuous_apply a).continuousAt.comp ((b.continuous_θ.comp (by fun_prop)).continuousAt)
    exact hc.eventually_ne (by simpa using ha)
  have hFeq : F =ᶠ[𝓝 0] fun s => κf s • b.θ (s • w) := by
    filter_upwards [hθa] with s hs
    obtain ⟨κ, hκ⟩ := b.law_eq i (z + s • w) (-z)
    have e : z + s • w + -z = s • w := by abel
    rw [e] at hκ
    have hκa : κ = F s a / b.θ (s • w) a := by
      rw [eq_div_iff hs]; simp only [F, hκ, Pi.smul_apply, smul_eq_mul]
    simp only [κf, ← hκa, F, hκ]
  have hγ0 := b.hasDerivAt_θ_line 0 w
  simp only [zero_add] at hγ0
  have hFa : HasDerivAt (fun s => F s a) (D a) 0 := hasDerivAt_pi.mp hF a
  have hκd : HasDerivAt κf ((D a * b.θ 0 a - F 0 a * fderiv ℂ b.θ 0 w a) / b.θ 0 a ^ 2) 0 := by
    have := hFa.div (hasDerivAt_pi.mp hγ0 a) (by simpa using ha)
    simp only [zero_smul] at this
    exact this
  set k' := (D a * b.θ 0 a - F 0 a * fderiv ℂ b.θ 0 w a) / b.θ 0 a ^ 2
  have hprod : HasDerivAt (fun s => κf s • b.θ (s • w)) (κf 0 • fderiv ℂ b.θ 0 w + k' • b.θ 0) 0 := by
    have := hκd.smul hγ0
    simp only [zero_smul] at this
    exact this
  have hF' := hprod.congr_of_eventuallyEq hFeq
  have hDeq2 : D = κf 0 • fderiv ℂ b.θ 0 w + k' • b.θ 0 := hF.unique hF'
  have hF0 : F0 = κf 0 • b.θ 0 := by
    have := hFeq.eq_of_nhds
    simpa [F, F0] using this
  have hκ0 : κf 0 ≠ 0 := by
    intro h0; apply hi; rw [hF0, h0, zero_smul]
  apply b.fderiv_inj_zero (c := (2 * c - k' / κf 0))
  have e := hDeq2.symm.trans hDeq
  rw [hF0, smul_smul] at e
  have e2 : κf 0 • fderiv ℂ b.θ 0 w = (2 * c * κf 0 - k') • b.θ 0 := by
    rw [sub_smul, ← e]; abel
  calc fderiv ℂ b.θ 0 w = (κf 0)⁻¹ • (κf 0 • fderiv ℂ b.θ 0 w) := by rw [smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    _ = (2 * c - k' / κf 0) • b.θ 0 := by
      rw [e2, smul_smul]; congr 1; field_simp

end AbBlock

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### The derivative of the lift -/

/-- The derivative of `r ↦ liftZ (u + r w) (μ + r σ)` at `0`. -/
noncomputable def dLZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) (w : Tan d₀ d₁ B) (σ : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * Complex.exp (u.2.1 j)
  | .z j => -w.2.1 j * Complex.exp (-u.2.1 j)
  | .e k l => σ k * (B k).θ (u.2.2 k) l + μ k * fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) l

theorem hasDerivAt_liftZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) (w : Tan d₀ d₁ B) (σ : Fin m → ℂ)
    (v : Var d₀ d₁ B) :
    HasDerivAt (fun r : ℂ => liftZ (u + r • w) (μ + r • σ) v) (dLZ u μ w σ v) 0 := by
  have hB := hasDerivAt_liftB u w v
  cases v with
  | x i => simpa [liftZ, liftB, liftB', dLZ] using hB
  | y j => simpa [liftZ, liftB, liftB', dLZ] using hB
  | z j => simpa [liftZ, liftB, liftB', dLZ] using hB
  | e k l =>
    have hμ : HasDerivAt (fun r : ℂ => μ k + r * σ k) (σ k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ k)).const_add (μ k)
    have := hμ.mul hB
    simp only [liftB, liftB', zero_smul, add_zero, zero_mul] at this
    convert this using 1
    · funext r; simp [liftZ]
    · simp only [dLZ]

/-- `dLZ u μ` as a linear map on `Tan × ℂ^m`. -/
noncomputable def dLZl (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    (Tan d₀ d₁ B × (Fin m → ℂ)) →ₗ[ℂ] (Var d₀ d₁ B → ℂ) where
  toFun p := dLZ u μ p.1 p.2
  map_add' p q := by
    funext v
    cases v <;> simp [dLZ, map_add] <;> ring
  map_smul' a p := by
    funext v
    cases v <;> simp [dLZ, map_smul] <;> ring

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
  have hz : ∀ k, w.2.2 k = 0 := fun k => by
    refine (B k).fderiv_inj (z := u.2.2 k) (c := -σ k / μ k) ?_
    funext l
    have := congrFun h (.e k l)
    simp only [dLZ, Pi.zero_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hμ k]
    linear_combination this
  have hw : w = 0 := Prod.ext hx (Prod.ext hy (funext hz))
  have hσ : σ = 0 := funext fun k => by
    obtain ⟨l, hl⟩ : ∃ l, (B k).θ (u.2.2 k) l ≠ 0 := by
      by_contra hc; push Not at hc; exact (B k).θ_ne _ (funext hc)
    have := congrFun h (.e k l)
    simp only [dLZ, hw, Prod.snd_zero, Pi.zero_apply, map_zero, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hl
  simp [hw, hσ]

/-! ### Tangent vectors -/

theorem eval_liftZ_eq_zero_of_mem_vanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ vanish E) {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ E) (μ : Fin m → ℂ) :
    eval (liftZ u μ) P = 0 := by
  obtain ⟨lam₀, h0⟩ := coords_expG u
  rw [liftZ_eq_coordsZ h0]
  exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ hu lam) _

theorem tangent_of_curve {σ' : Type*} [Fintype σ'] {p : Ideal (MvPolynomial σ' ℂ)} {x : ℂ → σ' → ℂ}
    {x' : σ' → ℂ} (hx : ∀ v, HasDerivAt (fun r => x r v) (x' v) 0) (hz : ∀ r, ∀ f ∈ p, eval (x r) f = 0) :
    x' ∈ LSG.ME.tangentSpace p (x 0) := by
  intro f hf
  have h1 := hasDerivAt_eval hx f
  have h2 : HasDerivAt (fun r => eval (x r) f) 0 0 := by
    have e : (fun r => eval (x r) f) = fun _ => 0 := funext fun r => hz r f hf
    rw [e]; exact hasDerivAt_const _ _
  calc _ = ∑ v, eval (x 0) (pderiv v f) * x' v := Finset.sum_congr rfl fun v _ => mul_comm _ _
    _ = 0 := (h2.unique h1).symm

/-- **Lifted curves give tangent vectors**: if `exp(u + r w) ∈ E` for all `r`, then `dLZ u μ w σ` is tangent to
`vanish E` at `liftZ u μ`. -/
theorem dLZ_mem_tangentSpace {E : Set (GPt d₀ d₁ B)} {u w : Tan d₀ d₁ B} (μ σ : Fin m → ℂ)
    (hE : ∀ r : ℂ, expG d₀ d₁ B (u + r • w) ∈ E) :
    dLZ u μ w σ ∈ LSG.ME.tangentSpace (vanish E) (liftZ u μ) := by
  have := tangent_of_curve (p := vanish E) (x := fun r => liftZ (u + r • w) (μ + r • σ))
    (hasDerivAt_liftZ u μ w σ) fun r f hf => eval_liftZ_eq_zero_of_mem_vanish hf (hE r) _
  simpa using this

theorem tangentSpace_anti {σ' : Type*} [Fintype σ'] {p q : Ideal (MvPolynomial σ' ℂ)} (h : p ≤ q)
    (a : σ' → ℂ) : LSG.ME.tangentSpace q a ≤ LSG.ME.tangentSpace p a :=
  fun _ hv f hf => hv f (h hf)

/-- **The first derivative along a tangent direction vanishes.** -/
theorem dirD_eq_zero_of_tangent {E : Set (GPt d₀ d₁ B)} {f : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hf : IsHomB f d) (hfv : f ∈ vanish E) {u w : Tan d₀ d₁ B} {μ : Fin m → ℂ} (hμ : ∀ k, μ k ≠ 0)
    (hv : dLZ u μ w 0 ∈ LSG.ME.tangentSpace (vanish E) (liftZ u μ)) : dirD f u w = 0 := by
  have hx : ∀ v, HasDerivAt (fun r : ℂ => liftZ (u + r • w) μ v) (dLZ u μ w 0 v) 0 := fun v => by
    simpa using hasDerivAt_liftZ u μ w 0 v
  have h1 := hasDerivAt_eval hx f
  have e : (fun r : ℂ => eval (liftZ (u + r • w) μ) f) =
      fun r => (∏ k, μ k ^ d k) * eval (liftB (u + r • w)) f := by
    funext r
    have := eval_liftZ_mul hf (u + r • w) 1 μ
    rwa [one_mul, liftZ_one] at this
  rw [e] at h1
  have h2 : HasDerivAt (fun r : ℂ => (∏ k, μ k ^ d k) * eval (liftB (u + r • w)) f)
      ((∏ k, μ k ^ d k) * dirD f u w) 0 := by
    refine HasDerivAt.const_mul _ ?_
    have hd : DifferentiableAt ℂ (fun r : ℂ => eval (liftB (u + r • w)) f) 0 :=
      (analyticAt_eval_of (f := fun v (r : ℂ) => liftB (u + r • w) v)
        (fun v => analyticAt_liftB_comp (by fun_prop) v) f).differentiableAt
    exact hd.hasDerivAt
  have h3 := h1.unique h2
  have h4 : ∑ v, eval (liftZ (u + (0 : ℂ) • w) μ) (pderiv v f) * dLZ u μ w 0 v = 0 := by
    have := hv f hfv
    simp only [zero_smul, add_zero]
    rw [← this]; exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [h4] at h3
  have hprod : (∏ k, μ k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hμ k)
  exact (mul_eq_zero.mp h3.symm).resolve_left hprod

end LSG.MEB
