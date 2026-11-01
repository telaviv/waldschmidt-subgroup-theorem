/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Stmt
import LSG.MEB.Ord
import LSG.MEB.PhOpLaw

/-!
# Scaled lifts on the multi-cone model of `G̃` (M2.5, β; shared foundation)

The analogue for vector-extension blocks of the scaled-lift part of `LSG.MEB.Model`/`LSG.MEB.ModelIG`. It sits
under both β's analytic layer (`Ord`, `PhOp*`) and α's `ModelIG` (M2.md, "α/β interface (MEBV)" (1)).

* `wV`, `wE`, `wk_eq_wE`, **`isHomV_iff_wV`**: the multigrading by blocks (block `k` = its `X`- and
  `T`-coordinates).
* `coords_mul`, `eval_coords_eq_zero_iff`; `coordsZ` (zero scalars allowed), **`eval_coordsZ_eq_zero`** (density).
* **`liftZ u μ`** `= (u₀, e^{u₁}, e^{−u₁}, μ_k · lift_k(z_k, w_k))`, `liftZ_one : liftZ u 1 = liftV u`;
  `LZ = Tan × ℂ^m`; **`analyticAt_eval_liftZ`**; `liftZ_eq_coordsZ`; **`mem_IGsem_iff_liftZ`**.
* `VBlock.analyticAt_Φ_apply`, **`VBlock.analyticAt_lift_apply`**: the block lift is entire in `(z, w)`.

Generic lemmas are taken from `LSG.MEB` (read-only): `eval_scale`, `analyticAt_eval_of`,
`AbBlock.analyticAt_θ_apply`.
-/

open MvPolynomial

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The multigrading by blocks -/

/-- The multigrading by blocks. -/
def wV : Var d₀ d₁ B → Fin m → ℕ
  | .e k _ => Pi.single k 1
  | _ => 0

/-- The grading by the `k`-th block. -/
def wE (k : Fin m) : Var d₀ d₁ B → ℕ := fun v => wV v k

theorem wk_eq_wE (k : Fin m) : (wk k : Var d₀ d₁ B → ℕ) = wE k := by
  funext v
  cases v <;> simp [wk, wE, wV, Pi.single_apply, eq_comm]

theorem weight_wE (k : Fin m) (s : Var d₀ d₁ B →₀ ℕ) :
    Finsupp.weight (wE k) s = Finsupp.weight wV s k := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wE]

theorem isHomV_iff_wV {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {n : Fin m → ℕ} :
    IsHomV Q n ↔ IsWeightedHomogeneous wV Q n := by
  constructor
  · intro h s hs
    funext k
    rw [← weight_wE, ← wk_eq_wE]; exact h k hs
  · intro h k s hs; rw [wk_eq_wE, weight_wE, h hs]

/-- Rescaling the cone coordinates. -/
theorem coords_mul (g : GPt d₀ d₁ B) (μ lam : Fin m → ℂˣ) :
    coords g (fun k => μ k * lam k) =
      fun v => (∏ k, ((μ k : ℂˣ) : ℂ) ^ wV v k) * coords g lam v := by
  funext v
  cases v with
  | x i => simp [coords, wV]
  | y j => simp [coords, wV]
  | z j => simp [coords, wV]
  | e k c =>
    simp only [coords, wV, Units.val_mul, Pi.single_apply, pow_ite, pow_one,
      pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- Multihomogeneous polynomials vanish at all or none of the cone representatives of `g`. -/
theorem eval_coords_eq_zero_iff {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wV Q d) (g : GPt d₀ d₁ B) (lam lam' : Fin m → ℂˣ) :
    eval (coords g lam) Q = 0 ↔ eval (coords g lam') Q = 0 := by
  have e : lam' = fun k => (lam' k * (lam k)⁻¹) * lam k := by
    funext k; rw [inv_mul_cancel_right]
  rw [e, coords_mul, LSG.MEB.eval_scale wV _ _ hQ, mul_eq_zero, or_iff_right]
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Units.ne_zero _))

/-! ### Zero scalars -/

/-- The cone coordinates of `g` with scalars `ν : Fin m → ℂ` (which may vanish). -/
noncomputable def coordsZ (g : GPt d₀ d₁ B) (ν : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => g.1 i
  | .y j => (g.ym j : ℂ)
  | .z j => (((g.ym j)⁻¹ : ℂˣ) : ℂ)
  | .e k c => ν k * (B k).rep (g.2.2 k) c

theorem coords_eq_coordsZ (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) :
    coords g lam = coordsZ g fun k => (lam k : ℂ) := by
  funext v; cases v <;> rfl

/-- **Density.** A polynomial vanishing at `coords g λ` for all `λ` vanishes at `coordsZ g ν` for all `ν`. -/
theorem eval_coordsZ_eq_zero {g : GPt d₀ d₁ B} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : ∀ lam, eval (coords g lam) P = 0) (ν : Fin m → ℂ) : eval (coordsZ g ν) P = 0 := by
  classical
  let φ : Var d₀ d₁ B → Polynomial ℂ := fun v => match v with
    | .x i => Polynomial.C (g.1 i)
    | .y j => Polynomial.C (g.ym j : ℂ)
    | .z j => Polynomial.C (((g.ym j)⁻¹ : ℂˣ) : ℂ)
    | .e k c => (if ν k = 0 then Polynomial.X else Polynomial.C (ν k)) *
        Polynomial.C ((B k).rep (g.2.2 k) c)
  set Q := MvPolynomial.aeval φ P
  have hev : ∀ t : ℂ, Q.eval t = eval (fun v => (φ v).eval t) P := by
    intro t
    rw [show Q = MvPolynomial.aeval φ P from rfl, MvPolynomial.aeval_def,
      MvPolynomial.polynomial_eval_eval₂]
    have : (Polynomial.evalRingHom t).comp (algebraMap ℂ (Polynomial ℂ)) = RingHom.id ℂ := by
      ext; simp
    rw [this]; rfl
  have hroot : ∀ t : ℂ, t ≠ 0 → Q.IsRoot t := by
    intro t ht
    rw [Polynomial.IsRoot, hev]
    let lam : Fin m → ℂˣ := fun k => if h : ν k = 0 then Units.mk0 t ht else Units.mk0 (ν k) h
    have : (fun v => (φ v).eval t) = coords g lam := by
      funext v
      cases v with
      | x i => simp [φ, coords]
      | y j => simp [φ, coords]
      | z j => simp [φ, coords]
      | e k c =>
        by_cases h : ν k = 0
        · simp only [φ, coords, lam, h, dite_true, ite_true, Units.val_mk0, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_C]
        · simp [φ, coords, lam, h]
    rw [this]; exact hP lam
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) (fun t ht => hroot t ht) ?_
    exact Set.Finite.infinite_compl (Set.finite_singleton 0)
  have := hev 0
  rw [hQ, Polynomial.eval_zero] at this
  rw [this]
  congr 2
  funext v
  cases v with
  | x i => simp [φ, coordsZ]
  | y j => simp [φ, coordsZ]
  | z j => simp [φ, coordsZ]
  | e k c => by_cases h : ν k = 0 <;> simp [φ, coordsZ, h]

/-! ### Analyticity of the block lift -/

/-- A coordinate of `Φ` is analytic. -/
theorem VBlock.analyticAt_Φ_apply (b : VBlock) (z : Fin b.g → ℂ) (t : Fin b.nT) :
    AnalyticAt ℂ (fun w => b.Φ w t) z :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin b.nT => ℂ) t).analyticAt _).comp (b.Φ_analytic z)

/-- **The block lift is entire** in `(z, w)`. -/
theorem VBlock.analyticAt_lift_apply (b : VBlock) (p : (Fin b.g → ℂ) × ℂ) (c : b.Idx) :
    AnalyticAt ℂ (fun q => b.lift q c) p := by
  cases c with
  | inl c => exact (b.base.analyticAt_θ_apply p.1 c).comp analyticAt_fst
  | inr t =>
    exact (((b.base.analyticAt_θ_apply p.1 (b.fc t)).comp analyticAt_fst).mul analyticAt_snd).sub
      ((b.analyticAt_Φ_apply p.1 t).comp analyticAt_fst)

theorem VBlock.continuous_lift (b : VBlock) : Continuous b.lift :=
  continuous_pi fun c => continuous_iff_continuousAt.mpr fun p => (b.analyticAt_lift_apply p c).continuousAt

/-! ### The analytic lift with scalars -/

/-- **The lift with scalars** `(u₀, e^{u₁}, e^{−u₁}, μ_k lift_k(z_k, w_k))`. -/
noncomputable def liftZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => u.1 i
  | .y j => Complex.exp (u.2.1 j)
  | .z j => Complex.exp (-u.2.1 j)
  | .e k c => μ k * (B k).lift (u.blkV k) c

theorem liftZ_one (u : Tan d₀ d₁ B) : liftZ u 1 = liftV u := by
  funext v; cases v <;> simp [liftZ, liftV]

variable (d₀ d₁ B) in
/-- The parameter space `Tan × ℂ^m` of `liftZ`. -/
abbrev LZ : Type := Tan d₀ d₁ B × (Fin m → ℂ)

/-- The coordinate projections of `LZ` as continuous linear maps. -/
noncomputable def LZx (i : Fin d₀) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℂ _ _).comp
    (ContinuousLinearMap.fst ℂ _ _))

noncomputable def LZy (j : Fin d₁) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)))

noncomputable def LZe (k : Fin m) : LZ d₀ d₁ B →L[ℂ] (Fin (B k).g → ℂ) :=
  (ContinuousLinearMap.proj (φ := fun k => Fin (B k).g → ℂ) k).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp ((ContinuousLinearMap.snd ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _))))

noncomputable def LZw (k : Fin m) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp ((ContinuousLinearMap.snd ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _))))

noncomputable def LZμ (k : Fin m) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℂ _ _)

/-- **The lift is analytic** in `(u, μ)`. -/
theorem liftZ_analyticAt (v : Var d₀ d₁ B) (p : LZ d₀ d₁ B) :
    AnalyticAt ℂ (fun q : LZ d₀ d₁ B => liftZ q.1 q.2 v) p := by
  cases v with
  | x i => exact (LZx i).analyticAt p
  | y j => exact analyticAt_cexp.comp ((LZy j).analyticAt p)
  | z j => exact analyticAt_cexp.comp ((LZy j).analyticAt p).neg
  | e k c =>
    exact ((LZμ k).analyticAt p).mul (((B k).analyticAt_lift_apply _ c).comp
      (((LZe k).analyticAt p).prod ((LZw k).analyticAt p)))

theorem analyticAt_eval_liftZ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (p : LZ d₀ d₁ B) :
    AnalyticAt ℂ (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) P) p :=
  LSG.MEB.analyticAt_eval_of (f := fun v (q : LZ d₀ d₁ B) => liftZ q.1 q.2 v)
    (fun v => liftZ_analyticAt v p) P

/-- `liftZ` in terms of `coordsZ`, given the scalings of `coords_expG`. -/
theorem liftZ_eq_coordsZ {u : Tan d₀ d₁ B} {lam₀ : Fin m → ℂˣ}
    (h : coords (expG d₀ d₁ B u) lam₀ = liftV u) (μ : Fin m → ℂ) :
    liftZ u μ = coordsZ (expG d₀ d₁ B u) fun k => μ k * lam₀ k := by
  funext v
  have hv := congrFun h v
  cases v with
  | x i => exact hv.symm
  | y j => exact hv.symm
  | z j => exact hv.symm
  | e k c =>
    simp only [coords, liftV] at hv
    simp only [liftZ, coordsZ, ← hv]
    ring

/-- **`IGsem` through the lift.** -/
theorem mem_IGsem_iff_liftZ {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ IGsem d₀ d₁ B ↔ ∀ u μ, eval (liftZ u μ) P = 0 := by
  constructor
  · intro hP u μ
    obtain ⟨lam₀, h⟩ := coords_expG u
    rw [liftZ_eq_coordsZ h]
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ (Set.mem_univ _) lam) _
  · intro h
    refine mem_vanish.mpr fun g _ lam => ?_
    obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) g
    obtain ⟨lam₀, h0⟩ := coords_expG u
    have : coords (expG d₀ d₁ B u) lam = liftZ u fun k => (lam k : ℂ) / lam₀ k := by
      rw [liftZ_eq_coordsZ h0, coords_eq_coordsZ]
      congr 1
      funext k
      field_simp
    rw [this]
    exact h _ _

end LSG.MEBV
