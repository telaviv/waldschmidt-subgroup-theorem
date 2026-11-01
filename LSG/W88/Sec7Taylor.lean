/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.TaylorK
import LSG.ME.FormalExp
import LSG.ME.SubgroupLie

/-!
# Taylor series of analytic germs and formal flows (W88 §7, bridge part 1)

* `tps f = Σ_j tco_j(f) zʲ`, the Taylor series at `0` of `f : ℂ → ℂ`.
* For `f, g` analytic at `0`: `tps (f + g) = tps f + tps g`, `tps (f * g) = tps f * tps g`,
  `tps (const c) = C c`, `constantCoeff (tps f) = f 0`, `d/dz (tps f) = tps f′` (`derivative_tps`),
  and `tps (Q ∘ Γ) = Q (tps ∘ Γ)` for polynomials `Q` (`tps_eval`).
* **`tps_eq_fflow`**: an analytic curve `Γ` with `Γ′ = D_w(X)(Γ)` near `0` (charts `b`) has Taylor
  series the formal flow `fflow b w (Γ 0)` (uniqueness of formal ODE solutions, `eq_fflow`).
-/

open MvPolynomial LSG.Aux Filter Topology

noncomputable section

namespace LSG.W88

/-- The Taylor series at `0`. -/
def tps (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun j => tco j f

theorem coeff_tps (f : ℂ → ℂ) (j : ℕ) : PowerSeries.coeff j (tps f) = tco j f :=
  PowerSeries.coeff_mk _ _

theorem tps_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) : tps f = tps g := by
  ext j; rw [coeff_tps, coeff_tps, tco_congr h]

theorem tps_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tps (f + g) = tps f + tps g := by
  ext j; rw [map_add, coeff_tps, coeff_tps, coeff_tps, tco_add hf hg]

theorem tps_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tps (f * g) = tps f * tps g := by
  ext j
  rw [PowerSeries.coeff_mul, coeff_tps, tco_mul hf hg,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_tps]

theorem tps_const (c : ℂ) : tps (fun _ => c) = PowerSeries.C c := by
  ext j
  rw [coeff_tps, tco_const, PowerSeries.coeff_C]

theorem constantCoeff_tps (f : ℂ → ℂ) : PowerSeries.constantCoeff (tps f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tps]
  simp [tco]

theorem derivative_tps (f : ℂ → ℂ) : PowerSeries.derivative (R := ℂ) (tps f) = tps (deriv f) := by
  ext j
  rw [PowerSeries.coeff_derivative, coeff_tps, coeff_tps, tco_deriv]
  ring

/-- **Polynomial evaluation commutes with `tps`.** -/
theorem tps_eval {σ : Type*} (Γ : σ → ℂ → ℂ) (hΓ : ∀ v, AnalyticAt ℂ (Γ v) 0)
    (Q : MvPolynomial σ ℂ) :
    tps (fun s => eval (fun v => Γ v s) Q) = aeval (fun v => tps (Γ v)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [eval_C, aeval_C, tps_const]; rfl
  | add p q hp hq =>
    simp only [map_add]
    rw [← hp, ← hq, ← tps_add (LSG.ME.analyticAt_eval hΓ p) (LSG.ME.analyticAt_eval hΓ q)]
    rfl
  | mul_X p v hp =>
    simp only [map_mul, eval_X, aeval_X]
    rw [← hp, ← tps_mul (LSG.ME.analyticAt_eval hΓ p) (hΓ v)]
    rfl

/-- **Analytic flows have the formal flow as Taylor series.** -/
theorem tps_eq_fflow {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → ℂ} (b : Fin m → Fin 3)
    (w : LSG.ME.LieE ℂ d₀ d₁ m) (Γ : LSG.ME.Var d₀ d₁ m → ℂ → ℂ) (hΓ : ∀ v, AnalyticAt ℂ (Γ v) 0)
    (hder : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ v, HasDerivAt (Γ v)
      (eval (fun u => Γ u s) (LSG.ME.dval g₂ g₃ b w v)) s) :
    (fun v => tps (Γ v)) = LSG.ME.fflow g₂ g₃ b w (fun v => Γ v 0) := by
  have hflow : LSG.ME.IsFlow g₂ g₃ b w (fun v => tps (Γ v)) := by
    intro v
    rw [derivative_tps]
    have hev : deriv (Γ v) =ᶠ[𝓝 0] fun s => eval (fun u => Γ u s) (LSG.ME.dval g₂ g₃ b w v) :=
      hder.mono fun s h => (h v).deriv
    rw [tps_congr hev, tps_eval Γ hΓ]
  have := LSG.ME.eq_fflow hflow
  rw [this]
  congr 1
  funext v
  exact constantCoeff_tps _

end LSG.W88
