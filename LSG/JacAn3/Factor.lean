/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.Theta

/-!
# A3.2: the factor of automorphy of `θ` (STAGE_A3 §1.2)

For a period `c` of `E` (`IsPer G c`: `E (z + c) = E z` for all `z`; e.g. `c ∈ kerE G`):
* `ThetaData.fac c z`, with **`fac_spec`**: `θ (z + c) = fac c z • θ z`;
* `analyticAt_fac` (entire), `fac_ne_zero`, `norm_theta_add` (`‖θ(z + c)‖ = ‖fac c z‖ ‖θ z‖`);
* **`fac_add`** (cocycle): `fac (c + c') z = fac c (z + c') * fac c' z`;
* **`fac_two`** (doubling): `fac (2c) (2z) = exp (−p₂(z + c) + p₂(z)) * fac c z ^ 4`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx}

/-- `c` is a period of `E`. -/
def IsPer (G : GermRad A hp hx) (c : Fin 2 → ℂ) : Prop := ∀ z, expP G (z + c) = expP G z

lemma isPer_of_mem_kerE {c : Fin 2 → ℂ} (hc : c ∈ kerE G) : IsPer G c := expP_periodic_of_ker G hc

lemma IsPer.add {c c' : Fin 2 → ℂ} (hc : IsPer G c) (hc' : IsPer G c') : IsPer G (c + c') := fun z => by
  rw [← add_assoc, hc' (z + c), hc z]

lemma IsPer.two_smul {c : Fin 2 → ℂ} (hc : IsPer G c) : IsPer G ((2 : ℂ) • c) := by
  have : (2 : ℂ) • c = c + c := _root_.two_smul ℂ c
  rw [this]; exact hc.add hc

/-- An index where a nonzero vector is nonzero. -/
def nzIdx (X : P9) : Fin 9 := if h : ∃ k, X k ≠ 0 then Classical.choose h else 0

lemma nzIdx_spec {X : P9} (hX : X ≠ 0) : X (nzIdx X) ≠ 0 := by
  have h : ∃ k, X k ≠ 0 := by
    by_contra hcon; push Not at hcon; exact hX (funext hcon)
  rw [nzIdx, dite_eq_left h]; exact Classical.choose_spec h

variable (D : ThetaData G)

/-- The factor of automorphy. -/
def ThetaData.fac (c z : Fin 2 → ℂ) : ℂ :=
  D.theta (z + c) (nzIdx (D.theta z)) / D.theta z (nzIdx (D.theta z))

lemma ThetaData.exists_smul {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    ∃ a : ℂ, D.theta (z + c) = a • D.theta z := by
  have h := hc z
  rw [D.expP_eq_theta, D.expP_eq_theta, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

lemma ThetaData.fac_eq_of {c z : Fin 2 → ℂ} (hc : IsPer G c) {k : Fin 9} (hk : D.theta z k ≠ 0) :
    D.fac c z = D.theta (z + c) k / D.theta z k := by
  obtain ⟨a, ha⟩ := D.exists_smul hc z
  have hn := nzIdx_spec (D.theta_ne_zero z)
  unfold ThetaData.fac
  rw [ha]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc, div_self hn, mul_div_assoc, div_self hk]

/-- **`θ (z + c) = fac c z • θ z`.** -/
theorem ThetaData.fac_spec {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    D.theta (z + c) = D.fac c z • D.theta z := by
  obtain ⟨a, ha⟩ := D.exists_smul hc z
  have hn := nzIdx_spec (D.theta_ne_zero z)
  have : D.fac c z = a := by
    rw [D.fac_eq_of hc hn, ha]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [this, ha]

theorem ThetaData.fac_ne_zero {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) : D.fac c z ≠ 0 := by
  intro h0
  have := D.fac_spec hc z
  rw [h0, zero_smul] at this
  exact D.theta_ne_zero _ this

theorem ThetaData.norm_theta_add {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    ‖D.theta (z + c)‖ = ‖D.fac c z‖ * ‖D.theta z‖ := by
  rw [D.fac_spec hc z, norm_smul]

/-- **The factor is entire.** -/
theorem ThetaData.analyticAt_fac {c : Fin 2 → ℂ} (hc : IsPer G c) (z₀ : Fin 2 → ℂ) :
    AnalyticAt ℂ (D.fac c) z₀ := by
  set k := nzIdx (D.theta z₀)
  have hk := nzIdx_spec (D.theta_ne_zero z₀)
  have han : AnalyticAt ℂ (fun z => D.theta z k) z₀ := (analyticAt_pi_iff.mp (D.analyticAt_theta z₀)) k
  have han' : AnalyticAt ℂ (fun z => D.theta (z + c) k) z₀ :=
    (analyticAt_pi_iff.mp (AnalyticAt.comp (g := D.theta) (f := fun z => z + c) (D.analyticAt_theta (z₀ + c))
      (analyticAt_id.add analyticAt_const))) k
  have hev : ∀ᶠ z in 𝓝 z₀, D.theta z k ≠ 0 := han.continuousAt.eventually_ne hk
  refine (han'.div han hk).congr ?_
  filter_upwards [hev] with z hz using (D.fac_eq_of hc hz).symm

theorem ThetaData.differentiable_fac {c : Fin 2 → ℂ} (hc : IsPer G c) : Differentiable ℂ (D.fac c) :=
  fun z => (D.analyticAt_fac hc z).differentiableAt

lemma smul_cancel_of_ne {a b : ℂ} {X : P9} (hX : X ≠ 0) (h : a • X = b • X) : a = b := by
  have hn := nzIdx_spec hX
  have := congrFun h (nzIdx X)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hn this

/-- **Cocycle.** -/
theorem ThetaData.fac_add {c c' : Fin 2 → ℂ} (hc : IsPer G c) (hc' : IsPer G c') (z : Fin 2 → ℂ) :
    D.fac (c + c') z = D.fac c (z + c') * D.fac c' z := by
  have h1 := D.fac_spec (hc.add hc') z
  have h2 : D.theta (z + (c + c')) = (D.fac c (z + c') * D.fac c' z) • D.theta z := by
    rw [show z + (c + c') = (z + c') + c by abel, D.fac_spec hc, D.fac_spec hc', smul_smul]
  exact smul_cancel_of_ne (D.theta_ne_zero z) (h1.symm.trans h2)

/-- **Doubling.** -/
theorem ThetaData.fac_two {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    D.fac ((2 : ℂ) • c) ((2 : ℂ) • z) = Complex.exp (-D.p2 (z + c) + D.p2 z) * D.fac c z ^ 4 := by
  have hdz : A.dup (D.theta z) ≠ 0 := A.dup_ne_zero _ (D.theta_onQ z) (D.theta_ne_zero z)
  have h1 := D.fac_spec hc.two_smul ((2 : ℂ) • z)
  rw [← smul_add, D.theta_two_smul, D.theta_two_smul, D.fac_spec hc, A.dup_smul, smul_smul,
    smul_smul] at h1
  have h2 := smul_cancel_of_ne hdz h1
  have he : Complex.exp (-D.p2 (z + c)) = Complex.exp (-D.p2 (z + c) + D.p2 z) * Complex.exp (-D.p2 z) := by
    rw [← Complex.exp_add]; ring_nf
  rw [he] at h2
  have hne : Complex.exp (-D.p2 z) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hne
  linear_combination -h2

end LSG.JacAn
