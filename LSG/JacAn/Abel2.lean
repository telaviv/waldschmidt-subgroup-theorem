/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Branch

/-!
# The genus-2 Abel map near a generic pair of points, and the local exponential

Let `B₁, B₂ : LocalBranch f 2` be local branches of `y² = f(x)` (ABVAR A0.1: `f = 4x⁵ + 1`). The local Abel map is

  `abel2 (x₁, x₂) = ∫_{x₁⁰}^{x₁} (dx/y, x dx/y) + ∫_{x₂⁰}^{x₂} (dx/y, x dx/y)`        (`B₁.I x₁ + B₂.I x₂`).

* `hasFDerivAt_abel2`, `abelJac_matrix`: its Jacobian has columns `(1/yᵢ, xᵢ/yᵢ)`;
* `abelJacEquiv`: it is invertible when `x₁ ≠ x₂` (explicit inverse; `det = (x₂ − x₁)/(y₁y₂)`);
* `abelInv`, `analyticAt_abelInv`: the analytic local inverse (`analyticAt_localInverse`);
* `mumford`, `mumford_dvd`: Mumford coordinates `a = x² − s₁x + s₂`, `b = b₁x + b₀` with `a ∣ f − b²`;
* `localExp = mumford ∘ abelInv`: **the local exponential** near `z₀ = abel2 (x₁, x₂)`, analytic at `z₀`
  (`analyticAt_localExp`), landing in the Mumford chart (`localExp_mem_chart`), with `localExp z₀ = mumford (x₁, x₂)`.
-/

noncomputable section

open Polynomial Metric Filter Topology

namespace LSG.JacAn

variable {f : ℂ[X]} (B₁ B₂ : LocalBranch f 2)

/-- The genus-2 local Abel map `(x₁, x₂) ↦ I₁(x₁) + I₂(x₂)`. -/
def abel2 (p : ℂ × ℂ) : Fin 2 → ℂ := B₁.I p.1 + B₂.I p.2

/-- The domain of `abel2`: the product of the two discs. -/
def dom2 : Set (ℂ × ℂ) := ball B₁.x₀ B₁.r ×ˢ ball B₂.x₀ B₂.r

lemma isOpen_dom2 : IsOpen (dom2 B₁ B₂) := isOpen_ball.prod isOpen_ball

/-- The Jacobian `(h₁, h₂) ↦ h₁ ω(x₁) + h₂ ω(x₂)`, `ω(x) = (1/y, x/y)`. -/
def abelJac (p : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (omegaVec 2 B₁.Y p.1) +
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight (omegaVec 2 B₂.Y p.2)

lemma abelJac_apply (p h : ℂ × ℂ) :
    abelJac B₁ B₂ p h = h.1 • omegaVec 2 B₁.Y p.1 + h.2 • omegaVec 2 B₂.Y p.2 := by
  simp [abelJac]

/-- **The Jacobian matrix** of the Abel map: columns `(1/y₁, x₁/y₁)` and `(1/y₂, x₂/y₂)`. -/
theorem abelJac_matrix (p : ℂ × ℂ) :
    abelJac B₁ B₂ p (1, 0) = ![1 / B₁.Y p.1, p.1 / B₁.Y p.1] ∧
      abelJac B₁ B₂ p (0, 1) = ![1 / B₂.Y p.2, p.2 / B₂.Y p.2] := by
  constructor <;> (funext k; fin_cases k <;> simp [abelJac_apply, omegaVec])

theorem hasFDerivAt_abel2 {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) :
    HasFDerivAt (abel2 B₁ B₂) (abelJac B₁ B₂ p) p := by
  have h1 := (B₁.I_deriv p.1 hp.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 := (B₂.I_deriv p.2 hp.2).hasFDerivAt.comp p hasFDerivAt_snd
  refine (h1.add h2).congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  simp [abelJac_apply]

theorem analyticAt_abel2 {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) : AnalyticAt ℂ (abel2 B₁ B₂) p :=
  ((B₁.I_an p.1 hp.1).comp analyticAt_fst).add ((B₂.I_an p.2 hp.2).comp analyticAt_snd)

/-- The explicit inverse of the Jacobian:
`z ↦ (y₁ (x₂ z₀ − z₁)/(x₂ − x₁), y₂ (z₁ − x₁ z₀)/(x₂ − x₁))`. -/
def abelJacInv (p : ℂ × ℂ) : (Fin 2 → ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((B₁.Y p.1 / (p.2 - p.1)) • (p.2 • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0 -
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1)).prod
    ((B₂.Y p.2 / (p.2 - p.1)) • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1 -
      p.1 • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0))

/-- The Jacobian is invertible when `x₁ ≠ x₂` and `y₁, y₂ ≠ 0`. -/
def abelJacEquiv (p : ℂ × ℂ) (hY₁ : B₁.Y p.1 ≠ 0) (hY₂ : B₂.Y p.2 ≠ 0) (hx : p.1 ≠ p.2) :
    (ℂ × ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (abelJac B₁ B₂ p) (abelJacInv B₁ B₂ p)
    (by
      have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
      intro h
      simp only [abelJacInv, abelJac_apply]
      ext <;> simp [omegaVec] <;> field_simp <;> ring)
    (by
      have hx' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
      intro z
      funext k
      fin_cases k <;> simp [abelJacInv, abelJac_apply, omegaVec] <;> field_simp <;> ring)

@[simp] lemma coe_abelJacEquiv (p : ℂ × ℂ) (hY₁ : B₁.Y p.1 ≠ 0) (hY₂ : B₂.Y p.2 ≠ 0)
    (hx : p.1 ≠ p.2) :
    ((abelJacEquiv B₁ B₂ p hY₁ hY₂ hx : (ℂ × ℂ) ≃L[ℂ] (Fin 2 → ℂ)) : (ℂ × ℂ) →L[ℂ] (Fin 2 → ℂ)) =
      abelJac B₁ B₂ p := rfl

/-- `det = (x₂ − x₁)/(y₁ y₂)`: the two Jacobian columns are independent iff `x₁ ≠ x₂`. -/
theorem abelJac_det (p : ℂ × ℂ) :
    (1 / B₁.Y p.1) * (p.2 / B₂.Y p.2) - (1 / B₂.Y p.2) * (p.1 / B₁.Y p.1) =
      (p.2 - p.1) / (B₁.Y p.1 * B₂.Y p.2) := by
  ring

theorem hasStrictFDerivAt_abel2 {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2) :
    HasStrictFDerivAt (abel2 B₁ B₂)
      ((abelJacEquiv B₁ B₂ p (B₁.Y_ne _ hp.1) (B₂.Y_ne _ hp.2) hx : (ℂ × ℂ) ≃L[ℂ] (Fin 2 → ℂ)) :
        (ℂ × ℂ) →L[ℂ] (Fin 2 → ℂ)) p :=
  hasStrictFDerivAt_of_analyticAt (analyticAt_abel2 B₁ B₂ hp) (hasFDerivAt_abel2 B₁ B₂ hp)

section LocalInverse

variable {B₁ B₂} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

/-- **The local exponential in the coordinates `(x₁, x₂)`**: the local inverse of the Abel map near
`abel2 p`. -/
def abelInv : (Fin 2 → ℂ) → ℂ × ℂ :=
  (hasStrictFDerivAt_abel2 B₁ B₂ hp hx).localInverse _ _ _

include hp hx in
theorem analyticAt_abelInv : AnalyticAt ℂ (abelInv hp hx) (abel2 B₁ B₂ p) :=
  analyticAt_localInverse (analyticAt_abel2 B₁ B₂ hp) _

include hp hx in
theorem abelInv_abel2_self : abelInv hp hx (abel2 B₁ B₂ p) = p :=
  HasStrictFDerivAt.localInverse_apply_image _

include hp hx in
theorem abel2_abelInv : ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p), abel2 B₁ B₂ (abelInv hp hx z) = z :=
  HasStrictFDerivAt.eventually_right_inverse _

include hp hx in
theorem abelInv_abel2 : ∀ᶠ q in 𝓝 p, abelInv hp hx (abel2 B₁ B₂ q) = q :=
  HasStrictFDerivAt.eventually_left_inverse _

include hp hx in
/-- Near `abel2 p`, the local inverse stays in the discs and off the diagonal. -/
theorem eventually_abelInv_good :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p),
      abelInv hp hx z ∈ dom2 B₁ B₂ ∧ (abelInv hp hx z).1 ≠ (abelInv hp hx z).2 := by
  have hU : IsOpen (dom2 B₁ B₂ ∩ {q : ℂ × ℂ | q.1 ≠ q.2}) :=
    (isOpen_dom2 B₁ B₂).inter (isOpen_ne_fun continuous_fst continuous_snd)
  have hc : ContinuousAt (abelInv hp hx) (abel2 B₁ B₂ p) :=
    HasStrictFDerivAt.localInverse_continuousAt _
  have hmem : dom2 B₁ B₂ ∩ {q : ℂ × ℂ | q.1 ≠ q.2} ∈ 𝓝 (abelInv hp hx (abel2 B₁ B₂ p)) := by
    rw [abelInv_abel2_self hp hx]; exact hU.mem_nhds ⟨hp, hx⟩
  exact hc.preimage_mem_nhds hmem

end LocalInverse

/-! ## Mumford coordinates -/

/-- Mumford coordinates `(s₁, s₂, b₁, b₀)` of the divisor `(x₁, Y₁ x₁) + (x₂, Y₂ x₂)`:
`a = x² − s₁x + s₂ = (x − x₁)(x − x₂)` and `b = b₁x + b₀` with `b(xᵢ) = yᵢ`. -/
def mumford (q : ℂ × ℂ) : Fin 4 → ℂ :=
  ![q.1 + q.2, q.1 * q.2, (B₁.Y q.1 - B₂.Y q.2) / (q.1 - q.2),
    (q.1 * B₂.Y q.2 - q.2 * B₁.Y q.1) / (q.1 - q.2)]

theorem analyticAt_mumford {q : ℂ × ℂ} (hq : q ∈ dom2 B₁ B₂) (hx : q.1 ≠ q.2) :
    AnalyticAt ℂ (mumford B₁ B₂) q := by
  have hd : (fun q : ℂ × ℂ => q.1 - q.2) q ≠ 0 := sub_ne_zero.mpr hx
  have hY₁ : AnalyticAt ℂ (fun q : ℂ × ℂ => B₁.Y q.1) q := (B₁.Y_an q.1 hq.1).comp analyticAt_fst
  have hY₂ : AnalyticAt ℂ (fun q : ℂ × ℂ => B₂.Y q.2) q := (B₂.Y_an q.2 hq.2).comp analyticAt_snd
  have hsub : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 - q.2) q := analyticAt_fst.sub analyticAt_snd
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact analyticAt_fst.add analyticAt_snd
  · exact analyticAt_fst.mul analyticAt_snd
  · exact (hY₁.sub hY₂).div hsub hd
  · exact ((analyticAt_fst.mul hY₂).sub (analyticAt_snd.mul hY₁)).div hsub hd

/-- Interpolation: `a = (X − x₁)(X − x₂)` divides `f − b²` when `b(xᵢ) = yᵢ`, `yᵢ² = f(xᵢ)`. -/
theorem mumford_dvd_aux {x₁ x₂ y₁ y₂ : ℂ} (hx : x₁ ≠ x₂) (h₁ : y₁ ^ 2 = f.eval x₁)
    (h₂ : y₂ ^ 2 = f.eval x₂) :
    (X ^ 2 - C (x₁ + x₂) * X + C (x₁ * x₂)) ∣
      f - (C ((y₁ - y₂) / (x₁ - x₂)) * X + C ((x₁ * y₂ - x₂ * y₁) / (x₁ - x₂))) ^ 2 := by
  have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  set P := f - (C ((y₁ - y₂) / (x₁ - x₂)) * X + C ((x₁ * y₂ - x₂ * y₁) / (x₁ - x₂))) ^ 2 with hP
  have hb₁ : (y₁ - y₂) / (x₁ - x₂) * x₁ + (x₁ * y₂ - x₂ * y₁) / (x₁ - x₂) = y₁ := by
    field_simp; ring
  have hb₂ : (y₁ - y₂) / (x₁ - x₂) * x₂ + (x₁ * y₂ - x₂ * y₁) / (x₁ - x₂) = y₂ := by
    field_simp; ring
  have e₁ : P.eval x₁ = 0 := by simp [hP, hb₁, h₁]
  have e₂ : P.eval x₂ = 0 := by simp [hP, hb₂, h₂]
  have ha : X ^ 2 - C (x₁ + x₂) * X + C (x₁ * x₂) = (X - C x₁) * (X - C x₂) := by
    simp only [map_add, map_mul]; ring
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr e₁
  have hQ₂ : Q.eval x₂ = 0 := by
    have := e₂
    rw [hQ, eval_mul, eval_sub, eval_X, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx.symm)
  obtain ⟨S, hS⟩ := dvd_iff_isRoot.mpr hQ₂
  rw [ha, hQ, hS, ← mul_assoc]
  exact dvd_mul_right _ _

/-- **The chart relation**: the Mumford coordinates of a generic pair satisfy `a ∣ f − b²`. -/
theorem mumford_dvd {q : ℂ × ℂ} (hq : q ∈ dom2 B₁ B₂) (hx : q.1 ≠ q.2) :
    (X ^ 2 - C (mumford B₁ B₂ q 0) * X + C (mumford B₁ B₂ q 1)) ∣
      f - (C (mumford B₁ B₂ q 2) * X + C (mumford B₁ B₂ q 3)) ^ 2 := by
  have := mumford_dvd_aux (f := f) hx (B₁.Y_sq q.1 hq.1) (B₂.Y_sq q.2 hq.2)
  simpa [mumford] using this

/-! ## The local exponential -/

section LocalExp

variable {B₁ B₂} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

/-- **The local exponential** `z ↦ (s₁, s₂, b₁, b₀)` near `z₀ = abel2 (x₁, x₂)`: Mumford coordinates of the
divisor `Σᵢ (xᵢ, yᵢ)` with Abel sum `z`. -/
def localExp : (Fin 2 → ℂ) → (Fin 4 → ℂ) := mumford B₁ B₂ ∘ abelInv hp hx

include hp hx in
theorem analyticAt_localExp : AnalyticAt ℂ (localExp hp hx) (abel2 B₁ B₂ p) :=
  (analyticAt_mumford B₁ B₂ ((abelInv_abel2_self hp hx).symm ▸ hp)
    ((abelInv_abel2_self hp hx).symm ▸ hx)).comp (analyticAt_abelInv hp hx)

include hp hx in
theorem localExp_abel2_self : localExp hp hx (abel2 B₁ B₂ p) = mumford B₁ B₂ p := by
  simp [localExp, abelInv_abel2_self hp hx]

include hp hx in
/-- `localExp` is analytic on a neighbourhood of `z₀`. -/
theorem eventually_analyticAt_localExp :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p), AnalyticAt ℂ (localExp hp hx) z :=
  (analyticAt_localExp hp hx).eventually_analyticAt

include hp hx in
/-- **`localExp` lands in the Mumford chart** `{(a, b) : a ∣ f − b²}` near `z₀`. -/
theorem localExp_mem_chart :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p),
      (X ^ 2 - C (localExp hp hx z 0) * X + C (localExp hp hx z 1)) ∣
        f - (C (localExp hp hx z 2) * X + C (localExp hp hx z 3)) ^ 2 := by
  filter_upwards [eventually_abelInv_good hp hx] with z hz
  exact mumford_dvd B₁ B₂ hz.1 hz.2

include hp hx in
/-- `localExp` inverts the Abel sum: `abel2 (abelInv z) = z` near `z₀`, and `localExp z` is the Mumford
representation of `abelInv z`. -/
theorem localExp_spec :
    ∀ᶠ z in 𝓝 (abel2 B₁ B₂ p),
      abel2 B₁ B₂ (abelInv hp hx z) = z ∧ localExp hp hx z = mumford B₁ B₂ (abelInv hp hx z) := by
  filter_upwards [abel2_abelInv hp hx] with z hz using ⟨hz, rfl⟩

end LocalExp

end LSG.JacAn
