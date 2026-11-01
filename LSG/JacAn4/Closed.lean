/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.PsiLiouville

/-!
# A4.1b (S0): the cone over `E(ℂ²)` is closed

`imgCone D = {0} ∪ {c • θ_N z}`. With the compact fundamental domain `fundDom` and `θ_N(z + ω) = facN ω z • θ_N z`,
every nonzero point of the cone normalises into the compact set `K = {u • θ_N f / ‖θ_N f‖ : |u| = 1, f ∈ fundDom}`.
* **`ThetaData.isClosed_imgCone`**;
* `ThetaData.mem_imgCone_of_tendsto`: a nonzero limit of cone points is a cone point.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- The cone over the image of `E`. -/
def ThetaData.imgCone : Set P9 := {X | X = 0 ∨ ∃ z : Fin 2 → ℂ, ∃ c : ℂ, X = c • D.thetaN z}

/-- The normalisation `X ↦ X / ‖X‖`. -/
def nrm (X : P9) : P9 := ((‖X‖ : ℂ)⁻¹) • X

/-- The compact set of normalised representatives over the fundamental domain. -/
def ThetaData.Kset : Set P9 :=
  (fun uf : ℂ × (Fin 2 → ℂ) => uf.1 • nrm (D.thetaN uf.2)) '' (sphere (0 : ℂ) 1 ×ˢ fundDom)

lemma ThetaData.isCompact_Kset : IsCompact D.Kset := by
  refine (isCompact_sphere (0 : ℂ) 1 |>.prod isCompact_fundDom).image_of_continuousOn ?_
  have hθ : Continuous D.thetaN := continuous_iff_continuousAt.mpr fun z => (D.analyticAt_thetaN z).continuousAt
  have hinv : Continuous fun z => ((‖D.thetaN z‖ : ℂ))⁻¹ :=
    Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_norm.comp hθ)) fun z => by
      exact_mod_cast (norm_ne_zero_iff.mpr (D.thetaN_ne_zero z))
  have hn : Continuous fun z => nrm (D.thetaN z) := by
    change Continuous fun z => ((‖D.thetaN z‖ : ℂ))⁻¹ • D.thetaN z
    exact hinv.smul hθ
  exact (continuous_fst.smul (hn.comp continuous_snd)).continuousOn

lemma norm_nrm {X : P9} (hX : X ≠ 0) : ‖nrm X‖ = 1 := by
  have h := norm_pos_iff.mpr hX
  rw [nrm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h, inv_mul_cancel₀ h.ne']

lemma nrm_smul {X : P9} (hX : X ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    nrm (c • X) = ((‖c‖ : ℂ)⁻¹ * c) • nrm X := by
  have hX' := norm_pos_iff.mpr hX
  have hc' := norm_pos_iff.mpr hc
  simp only [nrm, norm_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- Nonzero cone points normalise into `Kset`. -/
lemma ThetaData.nrm_mem_Kset {z : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0) : nrm (c • D.thetaN z) ∈ D.Kset := by
  obtain ⟨f, hf, ω, hω, rfl⟩ := exists_fund z
  have pω := isPer_of_mem_latt (G := G) hω
  rw [D.thetaN_add pω, smul_smul]
  have hfac : D.facN ω f ≠ 0 := by
    rw [ThetaData.facN]; exact mul_ne_zero (Complex.exp_ne_zero _) (D.fac_ne_zero pω f)
  have hcf : c * D.facN ω f ≠ 0 := mul_ne_zero hc hfac
  rw [nrm_smul (D.thetaN_ne_zero f) hcf]
  refine ⟨(_, f), ⟨?_, hf⟩, rfl⟩
  rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hcf)]

lemma ThetaData.mem_imgCone_of_nrm {X : P9} (hX : X ≠ 0) (h : nrm X ∈ D.Kset) : X ∈ D.imgCone := by
  obtain ⟨⟨u, f⟩, -, hu⟩ := h
  right
  refine ⟨f, (‖X‖ : ℂ) * u * (‖D.thetaN f‖ : ℂ)⁻¹, ?_⟩
  have hX' := norm_pos_iff.mpr hX
  have hX'' : (‖X‖ : ℂ) ≠ 0 := by exact_mod_cast hX'.ne'
  have hXeq : X = (‖X‖ : ℂ) • nrm X := by rw [nrm, smul_smul, mul_inv_cancel₀ hX'', one_smul]
  conv_lhs => rw [hXeq]
  rw [← hu]
  simp only [nrm, smul_smul]
  congr 1; ring

/-- **The cone over `E(ℂ²)` is closed.** -/
theorem ThetaData.isClosed_imgCone : IsClosed D.imgCone := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro X hX
  have hX0 : X ≠ 0 := fun h => hX (Or.inl h)
  have hnK : nrm X ∉ D.Kset := fun h => hX (D.mem_imgCone_of_nrm hX0 h)
  have hcont : ContinuousAt nrm X := by
    have hinv : ContinuousAt (fun Y : P9 => ((‖Y‖ : ℂ))⁻¹) X :=
      ContinuousAt.inv₀ (Complex.continuous_ofReal.comp continuous_norm).continuousAt (by
        exact_mod_cast (norm_ne_zero_iff.mpr hX0))
    change ContinuousAt (fun Y : P9 => ((‖Y‖ : ℂ))⁻¹ • Y) X
    exact hinv.smul continuousAt_id
  have h1 : ∀ᶠ Y in 𝓝 X, nrm Y ∈ D.Ksetᶜ :=
    hcont.preimage_mem_nhds (D.isCompact_Kset.isClosed.isOpen_compl.mem_nhds hnK)
  have h2 : ∀ᶠ Y in 𝓝 X, Y ≠ 0 := isClosed_singleton.isOpen_compl.mem_nhds hX0
  filter_upwards [h1, h2] with Y hY hY0
  rintro (h | ⟨z, c, rfl⟩)
  · exact hY0 h
  · have hc : c ≠ 0 := by rintro rfl; exact hY0 (zero_smul ℂ _)
    exact hY (D.nrm_mem_Kset hc)

/-- A nonzero limit of cone points is a cone point. -/
theorem ThetaData.mem_imgCone_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {Xs : ι → P9} {X : P9}
    (hX : Tendsto Xs l (𝓝 X)) (hmem : ∀ᶠ i in l, Xs i ∈ D.imgCone) : X ∈ D.imgCone :=
  D.isClosed_imgCone.mem_of_tendsto hX hmem

end LSG.JacAn
