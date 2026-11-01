/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.A1Facts

/-!
# a4, step 1: the germ of the exponential at the origin, and the local doubling law

Fix the A1 interface `A : A1Facts`, local branches `B₁, B₂` of `y² = 4x⁵ + 1` and a generic base pair `p` with
`z₀ = abel2 p`. Let `Ψ = grantJ ∘ localExp` (a chart-0 flow solution near `z₀`, (N1)) and `P₀ = Ψ(z₀)`.

* `germ A hp hx w = normalize 4 (law0 (Ψ(z₀ + w)) (negP P₀))`: the germ of `exp` at `0`, in the chart `X₄ = 1`
  (STAGE_A2 §6). Under the nondegeneracy `law0 P₀ (negP P₀) ≠ 0` at `X₄` (`hP₀`):
  - **`germ_zero`**: `germ 0 = e₄` (the origin), by (P);
  - **`eventually_germ_flow`**: the germ is a chart-4 flow solution on `V(Q)` near `0`, by (E1) (output chart 4).
* **`germ_dup`** (the local doubling law): `normalize 4 (dup (germ v)) = germ (2v)` on a ball around `0`. Both sides
  are speed-2 chart-4 flow solutions (by (E2) and the chain rule) with the value `e₄` at `0`; (U) (`flow_unique`)
  concludes. This is the anchor of `exp(z) = dupᵏ(germ(z/2ᵏ))`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

variable (A : A1Facts) {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} (hp : p ∈ dom2 B₁ B₂) (hx : p.1 ≠ p.2)

/-- `Ψ = grantJ ∘ localExp`. -/
def psiJ (z : Fin 2 → ℂ) : P9 := grantJ (localExp hp hx z)

/-- The base point `P₀ = Ψ(z₀)`. -/
def baseP : P9 := psiJ hp hx (abel2 B₁ B₂ p)

/-- **The germ of the exponential at `0`** (chart `X₄ = 1`). -/
def germ (w : Fin 2 → ℂ) : P9 :=
  normalize 4 (A.law0 (psiJ hp hx (abel2 B₁ B₂ p + w)) (A.negP (baseP hp hx)))

include hp hx in
lemma eventually_psi_flow_onQ :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ),
      IsFlowSol flowW 1 0 (fun w => psiJ hp hx (abel2 B₁ B₂ p + w)) w ∧
        A.OnQ (psiJ hp hx (abel2 B₁ B₂ p + w)) := by
  have ht : Tendsto (fun w : Fin 2 → ℂ => abel2 B₁ B₂ p + w) (𝓝 0) (𝓝 (abel2 B₁ B₂ p)) := by
    have hc : Continuous (fun w : Fin 2 → ℂ => abel2 B₁ B₂ p + w) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  filter_upwards [ht.eventually (grant_localExp_flow hp hx), ht.eventually (eventually_chartR_localExp hp hx)]
    with w hw hr
  refine ⟨⟨hw.1, ?_⟩, A.grantJ_onQ _ hr.1 hr.2⟩
  have := hw.2.comp w ((hasFDerivAt_id w).const_add (abel2 B₁ B₂ p))
  simpa [psiJ] using this

include hp hx in
/-- `germ 0 = e₄`. -/
theorem germ_zero (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    germ A hp hx 0 = origin9 := by
  have hQ : A.OnQ (baseP hp hx) :=
    by simpa [baseP] using (eventually_psi_flow_onQ A hp hx).self_of_nhds.2
  have hg : germ A hp hx 0 = normalize 4 (A.law0 (baseP hp hx) (A.negP (baseP hp hx))) := by
    simp [germ, baseP]
  rw [hg]
  funext k
  simp only [normalize, Pi.smul_apply, smul_eq_mul, origin9]
  by_cases hk : k = 4
  · subst hk; simp [hP₀]
  · rw [A.law0_neg _ hQ k hk, Pi.single_eq_of_ne hk]; ring

include hp hx in
/-- **The germ is a chart-4 flow solution on the model near `0`.** -/
theorem eventually_germ_flow (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), IsFlowSol A.W4 1 4 (germ A hp hx) w ∧ A.OnQ (germ A hp hx w) := by
  set Y := A.negP (baseP hp hx)
  set V : (Fin 2 → ℂ) → P9 := fun w => psiJ hp hx (abel2 B₁ B₂ p + w)
  have hev := eventually_psi_flow_onQ A hp hx
  have hYQ : A.OnQ Y := A.negP_onQ _ (by simpa [baseP] using hev.self_of_nhds.2)
  have hVc : ContinuousAt V 0 := hev.self_of_nhds.1.2.continuousAt
  have hc : ContinuousAt (fun w => A.law0 (V w) Y 4) 0 :=
    ((continuous_apply 4).continuousAt.comp ((A.hasFDerivAt_law0 (V 0) Y).continuousAt)).comp hVc
  have hne : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), A.law0 (V w) Y 4 ≠ 0 :=
    hc.eventually_ne (by simpa [V, baseP] using hP₀)
  filter_upwards [hev, hne] with w hw hw4
  refine ⟨⟨normalize_self 4 hw4, A.law0_transport₄ hw.1 hw.2 hYQ hw4⟩, ?_⟩
  exact A.onQ_smul _ _ (A.law0_onQ _ _ hw.2 hYQ)

include hp hx in
/-- **The local doubling law**: `normalize 4 (dup (germ v)) = germ (2v)` near `0`. -/
theorem germ_dup (hP₀ : A.law0 (baseP hp hx) (A.negP (baseP hp hx)) 4 ≠ 0) :
    ∃ ε > 0, ∀ v ∈ ball (0 : Fin 2 → ℂ) ε, A.dup (germ A hp hx v) 4 ≠ 0 ∧
      normalize 4 (A.dup (germ A hp hx v)) = germ A hp hx ((2 : ℂ) • v) := by
  set F := germ A hp hx
  have hF := eventually_germ_flow A hp hx hP₀
  have hF0 : F 0 = origin9 := germ_zero A hp hx hP₀
  obtain ⟨c, hc0, hc⟩ := A.dup_origin
  -- `dup (F v)` has nonzero `X₄` near `0`
  have hFc : ContinuousAt F 0 := hF.self_of_nhds.1.2.continuousAt
  have hdc : ContinuousAt (fun v => A.dup (F v) 4) 0 :=
    ((continuous_apply 4).continuousAt.comp ((A.hasFDerivAt_dup (F 0)).continuousAt)).comp hFc
  have hd4 : ∀ᶠ v in 𝓝 (0 : Fin 2 → ℂ), A.dup (F v) 4 ≠ 0 := by
    refine hdc.eventually_ne ?_
    show A.dup (F 0) 4 ≠ 0
    rw [hF0, hc]; simp [origin9, hc0]
  -- the doubled germ
  have h2 : Tendsto (fun v : Fin 2 → ℂ => (2 : ℂ) • v) (𝓝 0) (𝓝 0) := by
    have := ((continuous_const_smul (2 : ℂ)).tendsto (0 : Fin 2 → ℂ)); simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((hF.and hd4).and (h2.eventually hF))
  refine ⟨ε, hε, fun v hv => ⟨(hball v hv).1.2, ?_⟩⟩
  revert v
  refine flow_unique A.W4 A.W4_contDiff 2 (fun v hv => ?_) (fun v hv => ?_) ?_
  · obtain ⟨⟨hFv, hd⟩, -⟩ := hball v hv
    exact A.dup_transport₄ hFv.1 hFv.2 hd
  · obtain ⟨-, hF2⟩ := hball v hv
    have := hF2.1.2.comp v ((hasFDerivAt_id v).const_smul (2 : ℂ))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      flowCLM_apply, Pi.smul_apply, smul_eq_mul]
    simp only [one_smul, smul_add, smul_smul, one_mul]
    rfl
  · show normalize 4 (A.dup (F 0)) = F ((2 : ℂ) • 0)
    rw [smul_zero, hF0, hc]
    funext k
    simp [normalize, origin9, hc0, smul_smul]

end LSG.JacAn
