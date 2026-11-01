/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.KLemma

/-!
# M2.2 (N1 for `θ_N`): Lemma K♮ for the normalised theta lift

* `ThetaData.thetaN_PF0`, `ThetaData.thetaN_PF4`: the chart-0 and chart-4 projective flows of `θ_N`;
* `ThetaData.facN_aff`: `facN ω z = a_ω · exp(L_ω z)` on `latt`;
* **`ThetaData.kHyp`**: `θ_N` satisfies `KHyp`;
(These extend the namespace `LSG.JacAn.ThetaData`, so that dot notation works.)
* **`ThetaData.lemmaK_N`**: `G_c(θ_N) = K_ij θ_{N,c}²` for `c ∈ {0, 4, 8}`; the constants `ThetaData.kK`.
-/

noncomputable section

open Filter

namespace LSG.JacAn

open LSG.JacAnV

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

lemma ThetaData.thetaN_PF0 (z : Fin 2 → ℂ) : PFAt flowW 1 0 D.thetaN z :=
  (D.theta_PF0 z).of_eventually_smul flowW_smul (D.analyticAt_theta z) (D.analyticAt_thetaN z)
    (nzIdx_spec (D.theta_ne_zero z)) (Eventually.of_forall fun _ => ⟨_, rfl⟩)

lemma ThetaData.thetaN_PF4 (z : Fin 2 → ℂ) : PFAt A.W4 1 4 D.thetaN z :=
  (D.theta_PF4 z).of_eventually_smul A.W4_smul (D.analyticAt_theta z) (D.analyticAt_thetaN z)
    (nzIdx_spec (D.theta_ne_zero z)) (Eventually.of_forall fun _ => ⟨_, rfl⟩)

lemma ThetaData.thetaN_cmp_ne {z : Fin 2 → ℂ} {k : Fin 9} (h : D.theta z k ≠ 0) : D.thetaN z k ≠ 0 := by
  simp only [ThetaData.thetaN, Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (Complex.exp_ne_zero _) h

/-- The normalised factor is affine-exponential on `latt`. -/
lemma ThetaData.facN_aff {ω : Fin 2 → ℂ} (hω : ω ∈ latt) (z : Fin 2 → ℂ) :
    D.facN ω z = Complex.exp (-D.lamN ω) * D.fac ω 0 * Complex.exp (D.Lf ω z) := by
  rw [ThetaData.facN, D.fac_affine (isPer_of_mem_latt hω)]; ring

/-- **`θ_N` satisfies the hypotheses of Lemma K♮.** -/
theorem ThetaData.kHyp : KHyp D.thetaN where
  an := D.analyticAt_thetaN
  pf := D.thetaN_PF0
  quad := fun z => A.onQ_quad _ (D.thetaN_onQ z)
  ne0 := by
    obtain ⟨w, hw⟩ := D.exists_theta0_ne
    exact ⟨w, D.thetaN_cmp_ne hw⟩
  cover := fun z => by
    rcases D.theta_chart_cover z with h | h | h
    · exact Or.inl (D.thetaN_cmp_ne h)
    · exact Or.inr (Or.inl (D.thetaN_cmp_ne h))
    · exact Or.inr (Or.inr (D.thetaN_cmp_ne h))
  per := fun ω hω => ⟨Complex.exp (-D.lamN ω) * D.fac ω 0, D.Lf ω, fun z => by
    rw [D.thetaN_add (isPer_of_mem_latt hω), D.facN_aff hω]⟩

/-- **Lemma K♮ for `θ_N`.** -/
theorem ThetaData.lemmaK_N : ∃ K : Fin 2 → Fin 2 → ℂ, ∀ c : Fin 9, (c = 0 ∨ c = 4 ∨ c = 8) →
    ∀ (i j : Fin 2) z, kG D.thetaN c i j z = K i j * D.thetaN z c ^ 2 :=
  D.kHyp.lemmaK

/-- The constants `K_ij` of Lemma K♮ (`∂_i∂_j log θ_{N,0} = −3℘_ij + K_ij`). -/
def ThetaData.kK : Fin 2 → Fin 2 → ℂ := Classical.choose D.lemmaK_N

theorem ThetaData.kK_spec {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (i j : Fin 2) (z : Fin 2 → ℂ) :
    kG D.thetaN c i j z = D.kK i j * D.thetaN z c ^ 2 :=
  Classical.choose_spec D.lemmaK_N c hc i j z

/-- **Lemma K♮, chart 0, explicit**: `θ₀ ∂_i∂_jθ₀ − ∂_iθ₀ ∂_jθ₀ + 3 θ_{m(i,j)} θ₀ = K_ij θ₀²`. -/
theorem ThetaData.lemmaK0 (i j : Fin 2) (z : Fin 2 → ℂ) :
    D.thetaN z 0 * pd i (pd j (cmpV D.thetaN 0)) z - pd i (cmpV D.thetaN 0) z * pd j (cmpV D.thetaN 0) z +
      3 * D.thetaN z (mIdx i j) * D.thetaN z 0 = D.kK i j * D.thetaN z 0 ^ 2 := by
  have h := D.kK_spec (c := 0) (Or.inl rfl) i j z
  simpa [kG, kQ] using h

end LSG.JacAn
