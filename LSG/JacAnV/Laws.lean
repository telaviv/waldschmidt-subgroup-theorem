/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Fibre

/-!
# M2.2 (§2.3): the fibre addition laws are the polarisation of the 81 laws

For the law `lawK k m` (bidegree `(2, 2)`) put `∂_X law(X, Y)[S] = D_X lawK(X, Y)(S)` and `∂_Y law(X, Y)[S']`
(`A1Facts.dXlaw`, `A1Facts.dYlaw`: Fréchet derivatives, i.e. the formal partials `Σ_a ∂_{X_a}law · S_a`), and

  `lawT k m X Y S S' = ½ (∂_X law(X, Y)[S] + ∂_Y law(X, Y)[S'])`   (`A1Facts.lawT`).

* `A1Facts.dXlaw_self`, `A1Facts.dYlaw_self`: Euler, `∂_X law(X, Y)[X] = 2 law(X, Y)`;
* **`ThetaData.lawT_eq`**: if `lawK k m (θu) (θv) = κ θ_k(u + v) θ_m(u − v)` (`laws_eq`), then
  `lawT k m (θu) (θv) (T(u, w)) (T(v, w')) = κ θ_m(u − v) · T_k(u + v, w + w')`
  (differentiate `laws_eq` along `∂₀` in `u` and in `v`, use `∂₀θ_a = 3 (θ_a (w + ℓ) − T_a)` and Euler);
* **`ThetaData.lawsV_correct`**, **`ThetaData.lawsV_complete`**: law `m` on `(θ, T)` is `(κ θ_m(u − v)) • (θ, T)(u + v,
  w + w')`, and some `m` has `κ θ_m(u − v) ≠ 0`. No new law data: the fibre laws are determined by the `A`-laws.
-/

noncomputable section

open Filter

namespace LSG.JacAn

open LSG.JacAnV

/-- `∂_X law(X, Y)[S]`. -/
def A1Facts.dXlaw (A : A1Facts) (k m : Fin 9) (X Y S : P9) : ℂ := fderiv ℂ (fun X => A.lawK k m X Y) X S

/-- `∂_Y law(X, Y)[S']`. -/
def A1Facts.dYlaw (A : A1Facts) (k m : Fin 9) (X Y S' : P9) : ℂ := fderiv ℂ (fun Y => A.lawK k m X Y) Y S'

/-- **The polarised fibre law** `½ (∂_X law · S + ∂_Y law · S')`. -/
def A1Facts.lawT (A : A1Facts) (k m : Fin 9) (X Y S S' : P9) : ℂ :=
  1 / 2 * (A.dXlaw k m X Y S + A.dYlaw k m X Y S')

namespace A1Facts

variable (A : A1Facts)

lemma lawK_diffX (k m : Fin 9) (X Y : P9) : DifferentiableAt ℂ (fun X => A.lawK k m X Y) X :=
  (AnalyticAt.comp (g := fun XY : P9 × P9 => A.lawK k m XY.1 XY.2) (f := fun X => (X, Y))
    (A.lawK_analytic k m _ (Set.mem_univ _)) (analyticAt_id.prod analyticAt_const)).differentiableAt

lemma lawK_diffY (k m : Fin 9) (X Y : P9) : DifferentiableAt ℂ (fun Y => A.lawK k m X Y) Y :=
  (AnalyticAt.comp (g := fun XY : P9 × P9 => A.lawK k m XY.1 XY.2) (f := fun Y => (X, Y))
    (A.lawK_analytic k m _ (Set.mem_univ _)) (analyticAt_const.prod analyticAt_id)).differentiableAt

/-- Euler in `X`. -/
lemma dXlaw_self (k m : Fin 9) (X Y : P9) : A.dXlaw k m X Y X = 2 * A.lawK k m X Y := by
  have hs : HasDerivAt (fun t : ℂ => t • X) X 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).smul_const X
  have hd : HasFDerivAt (fun X => A.lawK k m X Y) (fderiv ℂ (fun X => A.lawK k m X Y) X) ((1 : ℂ) • X) := by
    rw [one_smul]; exact (A.lawK_diffX k m X Y).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (1 : ℂ) hs
  have e : ((fun X => A.lawK k m X Y) ∘ fun t : ℂ => t • X) = fun t => t ^ 2 * A.lawK k m X Y :=
    funext fun t => A.lawK_smul_left k m t X Y
  rw [e] at h1
  have h2 : HasDerivAt (fun t : ℂ => t ^ 2 * A.lawK k m X Y) (2 * A.lawK k m X Y) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℂ)).mul_const (A.lawK k m X Y)
  exact h1.unique h2

/-- Euler in `Y`. -/
lemma dYlaw_self (k m : Fin 9) (X Y : P9) : A.dYlaw k m X Y Y = 2 * A.lawK k m X Y := by
  have hs : HasDerivAt (fun t : ℂ => t • Y) Y 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).smul_const Y
  have hd : HasFDerivAt (fun Y => A.lawK k m X Y) (fderiv ℂ (fun Y => A.lawK k m X Y) Y) ((1 : ℂ) • Y) := by
    rw [one_smul]; exact (A.lawK_diffY k m X Y).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (1 : ℂ) hs
  have e : ((fun Y => A.lawK k m X Y) ∘ fun t : ℂ => t • Y) = fun t => t ^ 2 * A.lawK k m X Y :=
    funext fun t => A.lawK_smul_right k m t X Y
  rw [e] at h1
  have h2 : HasDerivAt (fun t : ℂ => t ^ 2 * A.lawK k m X Y) (2 * A.lawK k m X Y) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℂ)).mul_const (A.lawK k m X Y)
  exact h1.unique h2

lemma dXlaw_comb (k m : Fin 9) (X Y S : P9) (a b : ℂ) :
    A.dXlaw k m X Y (a • X - b • S) = a * (2 * A.lawK k m X Y) - b * A.dXlaw k m X Y S := by
  rw [← A.dXlaw_self]; simp [dXlaw, map_sub, map_smul]

lemma dYlaw_comb (k m : Fin 9) (X Y S : P9) (a b : ℂ) :
    A.dYlaw k m X Y (a • Y - b • S) = a * (2 * A.lawK k m X Y) - b * A.dYlaw k m X Y S := by
  rw [← A.dYlaw_self]; simp [dYlaw, map_sub, map_smul]

end A1Facts

lemma pd_comp_sub_left {f : (Fin 2 → ℂ) → ℂ} {ω y : Fin 2 → ℂ} (hf : DifferentiableAt ℂ f (ω - y)) (j : Fin 2) :
    pd j (fun y => f (ω - y)) y = -pd j f (ω - y) := by
  have h := hf.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub ω)
  unfold pd
  change fderiv ℂ (f ∘ HSub.hSub ω) y _ = _
  rw [h.fderiv]
  simp

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- The fibre vector `(T_a(z, w))_a`. -/
def ThetaData.fibV (z : Fin 2 → ℂ) (w : ℂ) : P9 := fun a => D.fibT a z w

/-- `∂₀θ = 3 (w + ℓ) θ − 3 T`. -/
lemma ThetaData.fderiv_thetaN_eq (z : Fin 2 → ℂ) (w : ℂ) :
    fderiv ℂ D.thetaN z (Pi.single 0 1) = (3 * (w + D.ellK z)) • D.thetaN z - (3 : ℂ) • D.fibV z w := by
  funext a
  rw [← pd_cmp (D.analyticAt_thetaN z).differentiableAt]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ThetaData.fibV, ThetaData.fibT, cmpV]
  ring

lemma ThetaData.pd_law_u (k m : Fin 9) (u v : Fin 2 → ℂ) :
    pd 0 (fun u => A.lawK k m (D.thetaN u) (D.thetaN v)) u =
      A.dXlaw k m (D.thetaN u) (D.thetaN v) (fderiv ℂ D.thetaN u (Pi.single 0 1)) := by
  have h := (A.lawK_diffX k m (D.thetaN u) (D.thetaN v)).hasFDerivAt.comp u
    (D.analyticAt_thetaN u).differentiableAt.hasFDerivAt
  unfold pd
  change fderiv ℂ ((fun X => A.lawK k m X (D.thetaN v)) ∘ D.thetaN) u _ = _
  rw [h.fderiv]; rfl

lemma ThetaData.pd_law_v (k m : Fin 9) (u v : Fin 2 → ℂ) :
    pd 0 (fun v => A.lawK k m (D.thetaN u) (D.thetaN v)) v =
      A.dYlaw k m (D.thetaN u) (D.thetaN v) (fderiv ℂ D.thetaN v (Pi.single 0 1)) := by
  have h := (A.lawK_diffY k m (D.thetaN u) (D.thetaN v)).hasFDerivAt.comp v
    (D.analyticAt_thetaN v).differentiableAt.hasFDerivAt
  unfold pd
  change fderiv ℂ ((fun Y => A.lawK k m (D.thetaN u) Y) ∘ D.thetaN) v _ = _
  rw [h.fderiv]; rfl

/-- **The polarised laws compute the fibre addition.** -/
theorem ThetaData.lawT_eq {κ : ℂ} (hκ : ∀ (u v : Fin 2 → ℂ) (k m : Fin 9),
    A.lawK k m (D.thetaN u) (D.thetaN v) = κ * D.thetaN (u + v) k * D.thetaN (u - v) m)
    (k m : Fin 9) (u v : Fin 2 → ℂ) (w w' : ℂ) :
    A.lawT k m (D.thetaN u) (D.thetaN v) (D.fibV u w) (D.fibV v w') =
      κ * D.thetaN (u - v) m * D.fibT k (u + v) (w + w') := by
  have hc : ∀ c, Ent (cmpV D.thetaN c) := ent_cmp D.analyticAt_thetaN
  -- derivative along `u`
  have hu := pd_congr (z := u) (funext fun u => hκ u v k m) 0
  have eu : (fun u => κ * D.thetaN (u + v) k * D.thetaN (u - v) m) =
      fun u => κ * (cmpV D.thetaN k (u + v) * cmpV D.thetaN m (u + -v)) := by
    funext u; simp only [cmpV, sub_eq_add_neg]; ring
  rw [eu, pd_const_mul _ ((((hc k).comp_add v).mul ((hc m).comp_add (-v))) u).differentiableAt,
    pd_mul (((hc k).comp_add v) u).differentiableAt (((hc m).comp_add (-v)) u).differentiableAt,
    pd_comp_add, pd_comp_add, D.pd_law_u, D.fderiv_thetaN_eq u w, A.dXlaw_comb] at hu
  -- derivative along `v`
  have hv := pd_congr (z := v) (funext fun v => hκ u v k m) 0
  have ev : (fun v => κ * D.thetaN (u + v) k * D.thetaN (u - v) m) =
      fun v => κ * (cmpV D.thetaN k (v + u) * cmpV D.thetaN m (u - v)) := by
    funext v; simp only [cmpV, add_comm u v]
    ring
  have hmv : DifferentiableAt ℂ (fun v => cmpV D.thetaN m (u - v)) v :=
    (AnalyticAt.comp (g := cmpV D.thetaN m) (f := fun v => u - v) (hc m (u - v))
      (analyticAt_const.sub analyticAt_id)).differentiableAt
  rw [ev, pd_const_mul (f := fun v => cmpV D.thetaN k (v + u) * cmpV D.thetaN m (u - v)) _
      ((((hc k).comp_add u) v).differentiableAt.mul hmv),
    pd_mul (f := fun v => cmpV D.thetaN k (v + u)) (g := fun v => cmpV D.thetaN m (u - v))
      (((hc k).comp_add u) v).differentiableAt hmv, pd_comp_add (f := cmpV D.thetaN k),
    pd_comp_sub_left (f := cmpV D.thetaN m) ((hc m).diff _), D.pd_law_v, D.fderiv_thetaN_eq v w',
    A.dYlaw_comb] at hv
  -- `∂₀θ_k(u + v)` through `T_k(u + v, w + w')`
  have hk : pd 0 (cmpV D.thetaN k) (u + v) =
      3 * D.thetaN (u + v) k * (w + w' + D.ellK u + D.ellK v) - 3 * D.fibT k (u + v) (w + w') := by
    unfold ThetaData.fibT; rw [map_add]; ring
  have hL := hκ u v k m
  rw [add_comm v u, hk] at hv
  rw [hk, ← sub_eq_add_neg] at hu
  unfold A1Facts.lawT
  simp only [cmpV] at hu hv
  linear_combination (-1 / 6 : ℂ) * hu + (-1 / 6 : ℂ) * hv + (w + w' + D.ellK u + D.ellK v) * hL

/-- **Correctness of the extended laws on the image.** -/
theorem ThetaData.lawsV_correct : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (u v : Fin 2 → ℂ) (w w' : ℂ) (m : Fin 9),
    (fun k => A.lawK k m (D.thetaN u) (D.thetaN v)) = (κ * D.thetaN (u - v) m) • D.thetaN (u + v) ∧
    (fun k => A.lawT k m (D.thetaN u) (D.thetaN v) (D.fibV u w) (D.fibV v w')) =
      (κ * D.thetaN (u - v) m) • D.fibV (u + v) (w + w') := by
  obtain ⟨κ, hκ0, hκ⟩ := D.laws_eq
  refine ⟨κ, hκ0, fun u v w w' m => ⟨funext fun k => ?_, funext fun k => ?_⟩⟩
  · rw [hκ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rw [D.lawT_eq hκ]; simp only [Pi.smul_apply, smul_eq_mul, ThetaData.fibV]

/-- **Completeness**: at every point some law has a nonzero multiplier. -/
theorem ThetaData.lawsV_complete {κ : ℂ} (hκ0 : κ ≠ 0) (u v : Fin 2 → ℂ) :
    ∃ m : Fin 9, κ * D.thetaN (u - v) m ≠ 0 :=
  ⟨nzIdx (D.thetaN (u - v)), mul_ne_zero hκ0 (nzIdx_spec (D.thetaN_ne_zero _))⟩

end LSG.JacAn
