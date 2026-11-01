/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.PolyGrowth

/-!
# A3.5 (part 1): the factor is affine and the resonance vanishes (STAGE_A3 §1.4)

For periods `c` (`IsPer G c`):
* `fac_quad`: `fac c z = fac c 0 · exp (L_c z + M_c(z, z))` (Lemma RP + two-sided growth);
* `homog_exp_one`: `exp (α + β + γ) ≡ 1` with `β`, `γ` homogeneous of degrees 1, 2 forces `β = γ = 0`;
* comparing the cocycle and the doubling relation degree by degree:
  **`Mb_diag_zero`** (`M_c(z, z) = 0`), **`Lf_add`** (`L_{c+c'} = L_c + L_{c'}`), **`pb_sym_zero`**
  (`p₂(z, c) + p₂(c, z) = 0`);
* **`p2_eq_zero`**: the resonant quadratic term vanishes (the periods span `ℂ²` over `ℝ`), hence
  **`theta_two_smul'`**: `θ(2z) = dup(θ z)`, and **`fac_affine`**: `fac c z = fac c 0 · exp (L_c z)`.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAn

open Beta

/-- **`exp` of a sum of homogeneous parts of degrees 0, 1, 2 is `1` only if the parts of degree 1, 2 vanish.** -/
lemma homog_exp_one {E : Type*} [AddCommGroup E] [Module ℂ E] {α : ℂ} {β γ : E → ℂ}
    (hβ : ∀ (t : ℂ) z, β (t • z) = t * β z) (hγ : ∀ (t : ℂ) z, γ (t • z) = t ^ 2 * γ z)
    (h : ∀ z, Complex.exp (α + β z + γ z) = 1) (z : E) : β z = 0 ∧ γ z = 0 := by
  have hc : ∀ t : ℂ, Complex.exp (α + β z * t + γ z * t ^ 2) = 1 := fun t => by
    have := h (t • z); rwa [hβ, hγ, mul_comm t, mul_comm (t ^ 2)] at this
  have hd : ∀ t : ℂ, β z + 2 * γ z * t = 0 := by
    intro t
    have h1 : HasDerivAt (fun t : ℂ => α + β z * t + γ z * t ^ 2) (β z + 2 * γ z * t) t := by
      have := (((hasDerivAt_id t).const_mul (β z)).const_add α).add ((hasDerivAt_pow 2 t).const_mul (γ z))
      exact this.congr_deriv (by simp; ring)
    have hder := h1.cexp
    have hfun : (fun t : ℂ => Complex.exp (α + β z * t + γ z * t ^ 2)) = fun _ => 1 := funext hc
    rw [hfun] at hder
    have := hder.unique (hasDerivAt_const t (1 : ℂ))
    rwa [hc t, one_mul] at this
  have h0 := hd 0
  have h1 := hd 1
  simp only [mul_zero, add_zero] at h0
  rw [h0, zero_add, mul_one] at h1
  exact ⟨h0, by simpa using h1⟩

lemma exp_sub_eq_one {a b : ℂ} (h : Complex.exp a = Complex.exp b) : Complex.exp (a - b) = 1 := by
  rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- The linear part `L_c = fac(c, 0)⁻¹ D fac(c, ·)(0)`. -/
def ThetaData.Lf (c : Fin 2 → ℂ) : (Fin 2 → ℂ) →L[ℂ] ℂ := (D.fac c 0)⁻¹ • fderiv ℂ (D.fac c) 0

/-- The quadratic part, as a function of two arguments. -/
def ThetaData.Mb (c x y : Fin 2 → ℂ) : ℂ :=
  (1 / 2) * ((D.fac c 0)⁻¹ * fderiv ℂ (fderiv ℂ (D.fac c)) 0 x y - D.Lf c x * D.Lf c y)

lemma ThetaData.Mb_add_left (c x x' y : Fin 2 → ℂ) : D.Mb c (x + x') y = D.Mb c x y + D.Mb c x' y := by
  simp only [ThetaData.Mb, map_add, ContinuousLinearMap.add_apply]; ring

lemma ThetaData.Mb_add_right (c x y y' : Fin 2 → ℂ) : D.Mb c x (y + y') = D.Mb c x y + D.Mb c x y' := by
  simp only [ThetaData.Mb, map_add]; ring

lemma ThetaData.Mb_smul_left (c x y : Fin 2 → ℂ) (t : ℂ) : D.Mb c (t • x) y = t * D.Mb c x y := by
  simp only [ThetaData.Mb, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

lemma ThetaData.Mb_smul_right (c x y : Fin 2 → ℂ) (t : ℂ) : D.Mb c x (t • y) = t * D.Mb c x y := by
  simp only [ThetaData.Mb, map_smul, smul_eq_mul]; ring

lemma ThetaData.Mb_zero (c y : Fin 2 → ℂ) : D.Mb c 0 y = 0 := by
  have := D.Mb_smul_left c 0 y 0; simpa using this

/-- **Lemma RP applied to the factor.** -/
theorem ThetaData.fac_quad {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    D.fac c z = D.fac c 0 * Complex.exp (D.Lf c z + D.Mb c z z) := by
  obtain ⟨K, hK, hb⟩ := D.fac_growth_dyadic hc
  have := quadExp_of_growth (D.analyticAt_fac hc) (D.fac_ne_zero hc) hK hb z
  rw [this]
  simp only [ThetaData.Lf, ThetaData.Mb, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring_nf

/-- The bilinear form of `p₂`. -/
def ThetaData.pb (x y : Fin 2 → ℂ) : ℂ := D.P 2 ![x, y]

lemma vec2_update0 (x y x' : Fin 2 → ℂ) : Function.update ![x, y] 0 x' = ![x', y] := by
  ext i : 1; fin_cases i <;> simp

lemma vec2_update1 (x y y' : Fin 2 → ℂ) : Function.update ![x, y] 1 y' = ![x, y'] := by
  ext i : 1; fin_cases i <;> simp

lemma ThetaData.pb_add_left (x x' y : Fin 2 → ℂ) : D.pb (x + x') y = D.pb x y + D.pb x' y := by
  have := (D.P 2).map_update_add ![x, y] 0 x x'
  simpa [vec2_update0, ThetaData.pb] using this

lemma ThetaData.pb_add_right (x y y' : Fin 2 → ℂ) : D.pb x (y + y') = D.pb x y + D.pb x y' := by
  have := (D.P 2).map_update_add ![x, y] 1 y y'
  simpa [vec2_update1, ThetaData.pb] using this

lemma ThetaData.pb_smul_left (x y : Fin 2 → ℂ) (t : ℂ) : D.pb (t • x) y = t * D.pb x y := by
  have := (D.P 2).map_update_smul ![x, y] 0 t x
  simpa [vec2_update0, ThetaData.pb] using this

lemma ThetaData.pb_smul_right (x y : Fin 2 → ℂ) (t : ℂ) : D.pb x (t • y) = t * D.pb x y := by
  have := (D.P 2).map_update_smul ![x, y] 1 t y
  simpa [vec2_update1, ThetaData.pb] using this

lemma ThetaData.p2_eq_pb (z : Fin 2 → ℂ) : D.p2 z = D.pb z z := by
  unfold ThetaData.p2 ThetaData.pb
  congr 1; ext i : 1; fin_cases i <;> rfl

lemma ThetaData.p2_add (z c : Fin 2 → ℂ) : D.p2 (z + c) = D.p2 z + D.pb z c + D.pb c z + D.p2 c := by
  simp only [D.p2_eq_pb, D.pb_add_left, D.pb_add_right]; ring

lemma ThetaData.fac_zero_zero {c : Fin 2 → ℂ} (hc : IsPer G c) : D.fac c 0 ≠ 0 := D.fac_ne_zero hc 0

/-- **Cocycle, degree by degree.** -/
theorem ThetaData.cocycle_parts {c c' : Fin 2 → ℂ} (hc : IsPer G c) (hc' : IsPer G c') (z : Fin 2 → ℂ) :
    D.Lf (c + c') z - D.Lf c z - D.Lf c' z - D.Mb c z c' - D.Mb c c' z = 0 ∧
      D.Mb (c + c') z z - D.Mb c z z - D.Mb c' z z = 0 := by
  refine homog_exp_one (α := 0)
    (β := fun z => D.Lf (c + c') z - D.Lf c z - D.Lf c' z - D.Mb c z c' - D.Mb c c' z)
    (γ := fun z => D.Mb (c + c') z z - D.Mb c z z - D.Mb c' z z) (fun t z => ?_) (fun t z => ?_)
    (fun z => ?_) z
  · simp only [map_smul, smul_eq_mul, D.Mb_smul_left, D.Mb_smul_right]; ring
  · simp only [D.Mb_smul_left, D.Mb_smul_right]; ring
  · have hcc := hc.add hc'
    have hEz := D.fac_add hc hc' z
    have hE0 := D.fac_add hc hc' 0
    rw [D.fac_quad hcc z, D.fac_quad hc (z + c'), D.fac_quad hc' z] at hEz
    rw [D.fac_quad hcc 0, D.fac_quad hc (0 + c'), D.fac_quad hc' 0] at hE0
    simp only [map_zero, D.Mb_zero, add_zero, zero_add, Complex.exp_zero, mul_one] at hE0
    have ha := D.fac_zero_zero hc
    have ha' := D.fac_zero_zero hc'
    rw [hE0] at hEz
    have key : Complex.exp (D.Lf c c' + D.Mb c c' c') * Complex.exp (D.Lf (c + c') z + D.Mb (c + c') z z) =
        Complex.exp (D.Lf c (z + c') + D.Mb c (z + c') (z + c')) * Complex.exp (D.Lf c' z + D.Mb c' z z) := by
      have h2 : D.fac c 0 * D.fac c' 0 ≠ 0 := mul_ne_zero ha ha'
      apply mul_left_cancel₀ h2
      linear_combination hEz
    rw [← Complex.exp_add, ← Complex.exp_add] at key
    have := exp_sub_eq_one key
    convert this using 2
    simp only [map_add, D.Mb_add_left, D.Mb_add_right]
    ring

/-- **Doubling, degree by degree.** -/
theorem ThetaData.doubling_parts {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    2 * D.Lf ((2 : ℂ) • c) z - 4 * D.Lf c z + D.pb z c + D.pb c z = 0 ∧
      4 * D.Mb ((2 : ℂ) • c) z z - 4 * D.Mb c z z = 0 := by
  refine homog_exp_one (α := 0)
    (β := fun z => 2 * D.Lf ((2 : ℂ) • c) z - 4 * D.Lf c z + D.pb z c + D.pb c z)
    (γ := fun z => 4 * D.Mb ((2 : ℂ) • c) z z - 4 * D.Mb c z z) (fun t z => ?_) (fun t z => ?_)
    (fun z => ?_) z
  · simp only [map_smul, smul_eq_mul, D.pb_smul_left, D.pb_smul_right]; ring
  · simp only [D.Mb_smul_left, D.Mb_smul_right]; ring
  · have h2c := hc.two_smul
    have hEz := D.fac_two hc z
    have hE0 := D.fac_two hc 0
    rw [smul_zero] at hE0
    rw [D.fac_quad h2c, D.fac_quad hc z] at hEz
    rw [D.fac_quad h2c 0, D.fac_quad hc 0] at hE0
    simp only [map_zero, D.Mb_zero, add_zero, zero_add, Complex.exp_zero, mul_one] at hE0
    have ha := D.fac_zero_zero hc
    rw [hE0] at hEz
    have hp2 : D.p2 0 = 0 := by rw [D.p2_eq_pb]; simpa using D.pb_smul_left 0 0 0
    rw [hp2, add_zero] at hEz
    have key : Complex.exp (-D.p2 c) * Complex.exp (D.Lf ((2 : ℂ) • c) ((2 : ℂ) • z) +
        D.Mb ((2 : ℂ) • c) ((2 : ℂ) • z) ((2 : ℂ) • z)) =
        Complex.exp (-D.p2 (z + c) + D.p2 z) * Complex.exp (D.Lf c z + D.Mb c z z) ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 4 ha)
      linear_combination hEz
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add] at key
    have := exp_sub_eq_one key
    convert this using 2
    simp only [map_smul, smul_eq_mul, D.Mb_smul_left, D.Mb_smul_right, D.p2_add]
    push_cast
    ring

lemma two_smul_eq_add (c : Fin 2 → ℂ) : (2 : ℂ) • c = c + c := two_smul ℂ c

/-- **The quadratic part of the factor vanishes.** -/
theorem ThetaData.Mb_diag_zero {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) : D.Mb c z z = 0 := by
  have h1 := (D.cocycle_parts hc hc z).2
  have h2 := (D.doubling_parts hc z).2
  rw [two_smul_eq_add] at h2
  linear_combination h2 / 4 - h1

theorem ThetaData.Mb_polar {c : Fin 2 → ℂ} (hc : IsPer G c) (x y : Fin 2 → ℂ) :
    D.Mb c x y + D.Mb c y x = 0 := by
  have h := D.Mb_diag_zero hc (x + y)
  rw [D.Mb_add_left, D.Mb_add_right, D.Mb_add_right, D.Mb_diag_zero hc x, D.Mb_diag_zero hc y] at h
  linear_combination h

/-- **`L` is additive on periods.** -/
theorem ThetaData.Lf_add {c c' : Fin 2 → ℂ} (hc : IsPer G c) (hc' : IsPer G c') :
    D.Lf (c + c') = D.Lf c + D.Lf c' := by
  ext z
  have h1 := (D.cocycle_parts hc hc' z).1
  have h2 := D.Mb_polar hc z c'
  simp only [ContinuousLinearMap.add_apply]
  linear_combination h1 + h2

theorem ThetaData.pb_sym_zero {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    D.pb z c + D.pb c z = 0 := by
  have h1 := (D.doubling_parts hc z).1
  have h2 := D.Lf_add hc hc
  rw [two_smul_eq_add, h2] at h1
  simp only [ContinuousLinearMap.add_apply] at h1
  linear_combination h1

/-- The real dimension of `ℂ²`. -/
lemma finrank_real_C2 : Module.finrank ℝ (Fin 2 → ℂ) = 4 := by
  rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]

/-- **The periods form an `ℝ`-basis of `ℂ²`.** -/
def latBasis : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_perVec (by rw [finrank_real_C2]; rfl)

lemma latBasis_apply (e : Fin 4) : latBasis e = perVec (e : ℕ) := by
  simp [latBasis]

/-- **The resonant quadratic term vanishes.** -/
theorem ThetaData.p2_eq_zero (z : Fin 2 → ℂ) : D.p2 z = 0 := by
  let f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun c => D.pb z c + D.pb c z
      map_add' := fun c c' => by
        change D.pb z (c + c') + D.pb (c + c') z = (D.pb z c + D.pb c z) + (D.pb z c' + D.pb c' z)
        rw [D.pb_add_left, D.pb_add_right]; ring
      map_smul' := fun t c => by
        change D.pb z (t • c) + D.pb (t • c) z = t • (D.pb z c + D.pb c z)
        rw [D.pb_smul_left, D.pb_smul_right, smul_eq_mul]; ring }
  have hf : f.restrictScalars ℝ = 0 := latBasis.ext fun e => by
    rw [latBasis_apply]
    exact D.pb_sym_zero (isPer_of_mem_kerE ((lattice_le_ker G).1 _)) z
  have := LinearMap.congr_fun hf z
  simp only [LinearMap.restrictScalars_apply, LinearMap.zero_apply] at this
  change D.pb z z + D.pb z z = 0 at this
  rw [D.p2_eq_pb]; linear_combination this / 2

/-- **The doubling equation without the resonant term.** -/
theorem ThetaData.theta_two_smul' (z : Fin 2 → ℂ) : D.theta ((2 : ℂ) • z) = A.dup (D.theta z) := by
  rw [D.theta_two_smul, D.p2_eq_zero, neg_zero, Complex.exp_zero, one_smul]

/-- **The factor is affine**: `fac c z = fac c 0 · exp (L_c z)`. -/
theorem ThetaData.fac_affine {c : Fin 2 → ℂ} (hc : IsPer G c) (z : Fin 2 → ℂ) :
    D.fac c z = D.fac c 0 * Complex.exp (D.Lf c z) := by
  rw [D.fac_quad hc z, D.Mb_diag_zero hc z, add_zero]

end LSG.JacAn
