/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.MonoGrowth
import LSG.AuxFun.Chart
import LSG.Elliptic.NaturalGroupFull

/-!
# Entire coordinates of `exp_{E^♮}` (Stage 5, phase 1)

The model `X = V(F, G) ⊂ ℙ⁴` of `E^♮` (`LSG/Elliptic/NaturalModel.lean`, `VECEXT_SPIKE.md`): over an
affine point `(x : y : 1 : t : y t − 2x²)`, over `O` `(0 : 1 : 0 : 0 : w')`; analytically
`exp(z, w) = expN L z w` with `t = w − ζ(z)` (and `w' = w − ζ(λ)` at `z = λ ∈ Λ`).

Multiplying by `σ³` gives **entire** coordinates (`ellN L z w`):
`(σ³℘, σ³℘', σ³, w σ³ − σ²σ', w σ³℘' + κ_σ)`, with
* `σ³ζ = σ²σ'` (`zetaS`), and
* `−σ³(℘'ζ + 2℘²) = σ'²σ'' + σσ'σ''' − 2σσ''²` (`kapS`).

Main results:
* `ellN_eq_off`: `ellN L z w = σ(z)³ • ptAff (℘ z) (℘' z) (w − ζ z)` off the lattice;
* **`ellN_add`** (quasi-periodicity under the periods `(λ, η(λ))` of `E^♮`):
  `ellN L (z + λ) (w + η λ) = sigmaMult λ z ³ • ellN L z w` — the multiplier of `ellW`;
* **`ellN_eq_smul_expN`**: `ellN L z w = c • expN L z w` with `c ≠ 0`, for **all** `z, w`
  (so `ellN` represents `exp_{E^♮}` everywhere; `ellN_ne_zero`);
* `ellN_add_fib`: fibre translation is `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`;
* `zetaS_add`: `σ²σ'(z + λ) = m³ (σ²σ'(z) + η(λ) σ³(z))`;
* **`exists_ellN_growth`**: `|ellN L z w k| ≤ (1 + |w|) e^{c (1+|z|)²}` (order 2 in `z`,
  polynomial of degree 1 in `w`).
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair
open LSG.Aux (ellW sigmaMult ellW_add differentiable_ellW ellW_eq_off growthLE_ellW ellV)

noncomputable section

namespace LSG.AuxV

variable (L : PeriodPair)

/-! ### The two entire correction terms -/

/-- `σ³ζ = σ²σ'` (entire). -/
def zetaS (z : ℂ) : ℂ := sigma L z ^ 2 * deriv (sigma L) z

/-- `−σ³(℘'ζ + 2℘²) = σ'²σ'' + σσ'σ''' − 2σσ''²` (entire). -/
def kapS (z : ℂ) : ℂ :=
  deriv (sigma L) z ^ 2 * deriv (deriv (sigma L)) z +
    sigma L z * deriv (sigma L) z * deriv (deriv (deriv (sigma L))) z -
    2 * sigma L z * deriv (deriv (sigma L)) z ^ 2

lemma differentiable_zetaS : Differentiable ℂ (zetaS L) :=
  ((differentiable_sigma L).pow 2).mul (differentiable_deriv_sigma L)

lemma differentiable_kapS : Differentiable ℂ (kapS L) := by
  have d0 := differentiable_sigma L
  have d1 := differentiable_deriv_sigma L
  have d2 := differentiable_deriv_deriv_sigma L
  have d3 := differentiable_deriv_deriv_deriv_sigma L
  unfold kapS
  exact (((d1.pow 2).mul d2).add ((d0.mul d1).mul d3)).sub (((d0.const_mul 2).mul (d2.pow 2)))

lemma zetaS_eq_off {z : ℂ} (hz : z ∉ L.lattice) : zetaS L z = sigma L z ^ 3 * zeta L z := by
  rw [zetaS, deriv_sigma L hz]; ring

lemma kapS_eq_off {z : ℂ} (hz : z ∉ L.lattice) :
    kapS L z = -(sigma L z ^ 3 * (℘'[L] z * zeta L z + 2 * ℘[L] z ^ 2)) := by
  have hs := sigma_ne_zero L hz
  have hζ : zeta L z = deriv (sigma L) z / sigma L z := by
    rw [deriv_sigma L hz, mul_div_cancel_right₀ _ hs]
  rw [hζ, weierstrassP_eq_sigma_cube L hz, derivWeierstrassP_eq_sigma_cube L hz, kapS]
  field_simp
  ring

/-- `σ''(0) = 0` (`σ` is odd). -/
lemma deriv_deriv_sigma_zero : deriv (deriv (sigma L)) 0 = 0 := by
  have h1 : ∀ z, deriv (sigma L) (-z) = deriv (sigma L) z := by
    intro z
    have hf : (fun x => sigma L (-x)) = fun x => -sigma L x := funext (sigma_neg L)
    have := congrArg (fun f => deriv f z) hf
    simp only [deriv_comp_neg] at this
    simpa using this
  have h2 : ∀ z, -deriv (deriv (sigma L)) (-z) = deriv (deriv (sigma L)) z := by
    intro z
    have hf : (fun x => deriv (sigma L) (-x)) = deriv (sigma L) := funext h1
    have := congrArg (fun f => deriv f z) hf
    simpa only [deriv_comp_neg] using this
  have := h2 0
  rw [neg_zero] at this
  linear_combination -this / 2

lemma kapS_zero : kapS L 0 = 0 := by
  have h0 : sigma L 0 = 0 := (sigma_eq_zero_iff L).mpr L.lattice.zero_mem
  simp [kapS, h0, deriv_deriv_sigma_zero L]

lemma zetaS_zero : zetaS L 0 = 0 := by
  have h0 : sigma L 0 = 0 := (sigma_eq_zero_iff L).mpr L.lattice.zero_mem
  simp [zetaS, h0]

/-! ### The coordinates -/

/-- **Entire coordinates `(U, V, W, T₁, T₃)` of `exp_{E^♮}(z, w)`**:
`(σ³℘, σ³℘', σ³, w σ³ − σ²σ', w σ³℘' + kapS)`. -/
def ellN (z w : ℂ) : Fin 5 → ℂ :=
  ![ellW L 1 z, ellW L 2 z, ellW L 0 z, w * ellW L 0 z - zetaS L z, w * ellW L 2 z + kapS L z]

@[simp] lemma ellN_zero (z w : ℂ) : ellN L z w 0 = ellW L 1 z := rfl
@[simp] lemma ellN_one (z w : ℂ) : ellN L z w 1 = ellW L 2 z := rfl
@[simp] lemma ellN_two (z w : ℂ) : ellN L z w 2 = ellW L 0 z := rfl
@[simp] lemma ellN_three (z w : ℂ) : ellN L z w 3 = w * ellW L 0 z - zetaS L z := rfl
@[simp] lemma ellN_four (z w : ℂ) : ellN L z w 4 = w * ellW L 2 z + kapS L z := rfl

/-- The base part of `ellN` is the cone vector `ellV = (σ³℘, σ³℘', σ³)` of `exp_E`. -/
lemma Pe_ellN (z w : ℂ) : Pe (ellN L z w) = ellV L z := by
  funext i; fin_cases i <;> rfl

lemma differentiable_ellN (k : Fin 5) :
    Differentiable ℂ (fun p : ℂ × ℂ => ellN L p.1 p.2 k) := by
  have e0 := (differentiable_ellW L 0).comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have e1 := (differentiable_ellW L 1).comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have e2 := (differentiable_ellW L 2).comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have zs := (differentiable_zetaS L).comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have ks := (differentiable_kapS L).comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have ws : Differentiable ℂ (fun p : ℂ × ℂ => p.2) := differentiable_snd
  fin_cases k
  · exact e1
  · exact e2
  · exact e0
  · exact (ws.mul e0).sub zs
  · exact (ws.mul e2).add ks

lemma differentiable_ellN_left (w : ℂ) (k : Fin 5) : Differentiable ℂ (fun z => ellN L z w k) :=
  (differentiable_ellN L k).comp ((differentiable_id).prodMk (differentiable_const w))

lemma continuous_ellN_left (w : ℂ) : Continuous (fun z => ellN L z w) :=
  continuous_pi fun k => (differentiable_ellN_left L w k).continuous

/-- Off the lattice, `ellN = σ³ • (℘, ℘', 1, t, ℘' t − 2℘²)`, `t = w − ζ(z)`. -/
theorem ellN_eq_off {z : ℂ} (hz : z ∉ L.lattice) (w : ℂ) :
    ellN L z w = sigma L z ^ 3 • ptAff (℘[L] z) (℘'[L] z) (w - zeta L z) := by
  obtain ⟨h1, h2⟩ := ellW_eq_off L hz
  have h0 : ellW L 0 z = sigma L z ^ 3 := rfl
  funext k
  fin_cases k
  · simp [ptAff, h1]
  · simp [ptAff, h2]
  · simp [ptAff, h0]
  · simp [ptAff, h0, zetaS_eq_off L hz]; ring
  · simp [ptAff, h2, kapS_eq_off L hz]; ring

/-- Fibre translation: `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`. -/
theorem ellN_add_fib (z w v : ℂ) :
    ellN L z (w + v) = ellN L z w + v • ![0, 0, 0, ellW L 0 z, ellW L 2 z] := by
  funext k
  fin_cases k <;> simp [ellN] <;> ring

/-- **Quasi-periodicity of the coordinates of `exp_{E^♮}`** under the periods `(λ, η(λ))`. -/
theorem ellN_add {lam : ℂ} (hlam : lam ∈ L.lattice) (z w : ℂ) :
    ellN L (z + lam) (w + eta L lam) = sigmaMult L lam z ^ 3 • ellN L z w := by
  have hcont : Continuous fun z => ellN L (z + lam) (w + eta L lam) :=
    (continuous_ellN_left L _).comp (continuous_id.add continuous_const)
  have hcont' : Continuous fun z => sigmaMult L lam z ^ 3 • ellN L z w := by
    unfold sigmaMult
    exact ((continuous_const.mul ((continuous_const.mul
      (continuous_id.add continuous_const)).cexp)).pow 3).smul (continuous_ellN_left L w)
  have hd : Dense ((L.lattice : Set ℂ)ᶜ) := (countable_lattice L).dense_compl ℂ
  refine congrFun (hcont.ext_on hd hcont' fun u hu => ?_) z
  have hu' : u ∉ L.lattice := hu
  have hul : u + lam ∉ L.lattice := add_notMem_lattice L hu' hlam
  simp only
  rw [ellN_eq_off L hul, ellN_eq_off L hu', sigma_add L hlam u, zeta_add L hlam u,
    L.weierstrassP_add_coe u ⟨lam, hlam⟩, L.derivWeierstrassP_add_coe u ⟨lam, hlam⟩, smul_smul,
    show w + eta L lam - (zeta L u + eta L lam) = w - zeta L u by ring, sigmaMult]
  congr 1
  ring

/-- Quasi-periodicity of `σ²σ' = σ³ζ`. -/
theorem zetaS_add {lam : ℂ} (hlam : lam ∈ L.lattice) (z : ℂ) :
    zetaS L (z + lam) = sigmaMult L lam z ^ 3 * (zetaS L z + eta L lam * ellW L 0 z) := by
  have h3 := congrFun (ellN_add L hlam z 0) 3
  have hW := ellW_add L hlam 0 z
  simp only [ellN_three, zero_add, Pi.smul_apply, smul_eq_mul, zero_mul, zero_sub] at h3
  rw [hW] at h3
  linear_combination -h3

lemma ellN_at_zero (w : ℂ) : ellN L 0 w = (-2 : ℂ) • ptO w := by
  have h0 : sigma L 0 = 0 := (sigma_eq_zero_iff L).mpr L.lattice.zero_mem
  have h1 : deriv (sigma L) 0 = 1 := deriv_sigma_zero L
  funext k
  fin_cases k <;>
    simp [ellN, ellW, ptO, h0, h1, zetaS_zero, kapS_zero]
  ring

lemma sigmaMult_ne_zero (lam z : ℂ) : sigmaMult L lam z ≠ 0 := by
  unfold sigmaMult
  refine mul_ne_zero (fun h0 => ?_) (Complex.exp_ne_zero _)
  have := LSG.Aux.norm_sigmaSign L lam
  rw [h0, norm_zero] at this
  norm_num at this

/-- **`ellN` represents `exp_{E^♮}` everywhere**: `ellN L z w = c • expN L z w`, `c ≠ 0`. -/
theorem ellN_eq_smul_expN (z w : ℂ) : ∃ c : ℂ, c ≠ 0 ∧ ellN L z w = c • expN L z w := by
  by_cases hz : z ∈ L.lattice
  · have h := ellN_add L hz 0 (w - eta L z)
    rw [zero_add, sub_add_cancel, ellN_at_zero, smul_smul] at h
    refine ⟨sigmaMult L z 0 ^ 3 * (-2), mul_ne_zero (pow_ne_zero _ (sigmaMult_ne_zero L z 0))
      (by norm_num), ?_⟩
    rw [h, expN_of_mem L hz, zeta_of_mem' L hz]
  · exact ⟨sigma L z ^ 3, pow_ne_zero _ (sigma_ne_zero L hz),
      by rw [ellN_eq_off L hz, expN_of_notMem L hz]⟩

lemma expN_ne_zero (z w : ℂ) : expN L z w ≠ 0 := by
  unfold expN
  split_ifs
  · intro h; simpa [ptO] using congrFun h 1
  · intro h; simpa [ptAff] using congrFun h 2

lemma ellN_ne_zero (z w : ℂ) : ellN L z w ≠ 0 := by
  obtain ⟨c, hc, h⟩ := ellN_eq_smul_expN L z w
  rw [h]; exact smul_ne_zero hc (expN_ne_zero L z w)

/-! ### Growth -/

lemma growthLE_zetaS : LSG.GrowthLE 2 (zetaS L) :=
  growthLE_mul (growthLE_pow (growthLE_sigma L) 2) (growthLE_deriv_sigma L)

lemma growthLE_kapS : LSG.GrowthLE 2 (kapS L) := by
  have g0 := growthLE_sigma L
  have g1 := growthLE_deriv_sigma L
  have g2 := growthLE_deriv_deriv_sigma L
  have g3 := growthLE_deriv_deriv_deriv_sigma L
  exact growthLE_sub (growthLE_add (growthLE_mul (growthLE_pow g1 2) g2)
    (growthLE_mul (growthLE_mul g0 g1) g3)) (growthLE_congr
      (growthLE_const_mul 2 (growthLE_mul g0 (growthLE_pow g2 2))) fun z => by ring)

/-- **Growth of the coordinates of `exp_{E^♮}`**: order two in `z`, linear in `w`. -/
theorem exists_ellN_growth :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ k z w, ‖ellN L z w k‖ ≤ (1 + ‖w‖) * Real.exp (c * (1 + ‖z‖) ^ 2) := by
  choose C hC0 hC using fun t => growthLE_exists_nonneg (growthLE_ellW L t)
  obtain ⟨Cz, hCz0, hCz⟩ := growthLE_exists_nonneg (growthLE_zetaS L)
  obtain ⟨Ck, hCk0, hCk⟩ := growthLE_exists_nonneg (growthLE_kapS L)
  have hCt : ∀ t, C t ≤ ∑ t, C t := fun t => single_le_sum (fun t _ => hC0 t) (mem_univ t)
  have hS0 : 0 ≤ ∑ t, C t := sum_nonneg fun t _ => hC0 t
  set c : ℝ := (∑ t, C t) + Cz + Ck + 1
  have hsq : ∀ z : ℂ, 1 ≤ (1 + ‖z‖) ^ 2 := fun z => one_le_one_add_norm_sq z
  have hmono : ∀ (a : ℝ) (z : ℂ), 0 ≤ a → a ≤ c - 1 →
      Real.exp (a * (1 + ‖z‖) ^ 2) ≤ Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) := fun a z ha hac =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hac (by positivity))
  have hc1 : 0 ≤ c - 1 := by simp only [c]; linarith
  have hE : ∀ z : ℂ, Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) * 2 ≤ Real.exp (c * (1 + ‖z‖) ^ 2) := by
    intro z
    have h2 : (2 : ℝ) ≤ Real.exp ((1 + ‖z‖) ^ 2) := by
      have := Real.add_one_le_exp ((1 + ‖z‖) ^ 2); linarith [hsq z]
    calc Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) * 2
        ≤ Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) * Real.exp ((1 + ‖z‖) ^ 2) := by gcongr
      _ = Real.exp (c * (1 + ‖z‖) ^ 2) := by rw [← Real.exp_add]; ring_nf
  refine ⟨c, by linarith, fun k z w => ?_⟩
  have hb : ∀ t : Fin 3, ‖ellW L t z‖ ≤ Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) := by
    intro t
    refine (hC t z).trans (hmono _ z (hC0 t) ?_)
    simp only [c]; linarith [hCt t]
  have hz : ‖zetaS L z‖ ≤ Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) :=
    (hCz z).trans (hmono _ z hCz0 (by simp only [c]; linarith))
  have hk : ‖kapS L z‖ ≤ Real.exp ((c - 1) * (1 + ‖z‖) ^ 2) :=
    (hCk z).trans (hmono _ z hCk0 (by simp only [c]; linarith))
  set E := Real.exp ((c - 1) * (1 + ‖z‖) ^ 2)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have key : ‖ellN L z w k‖ ≤ (1 + ‖w‖) * (E * 2) := by
    fin_cases k
    · change ‖ellW L 1 z‖ ≤ _; nlinarith [hb 1]
    · change ‖ellW L 2 z‖ ≤ _; nlinarith [hb 2]
    · change ‖ellW L 0 z‖ ≤ _; nlinarith [hb 0]
    · change ‖w * ellW L 0 z - zetaS L z‖ ≤ _
      calc ‖w * ellW L 0 z - zetaS L z‖ ≤ ‖w‖ * ‖ellW L 0 z‖ + ‖zetaS L z‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
        _ ≤ ‖w‖ * E + E := by gcongr; exact hb 0
        _ ≤ (1 + ‖w‖) * (E * 2) := by nlinarith
    · change ‖w * ellW L 2 z + kapS L z‖ ≤ _
      calc ‖w * ellW L 2 z + kapS L z‖ ≤ ‖w‖ * ‖ellW L 2 z‖ + ‖kapS L z‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ ‖w‖ * E + E := by gcongr; exact hb 2
        _ ≤ (1 + ‖w‖) * (E * 2) := by nlinarith
  exact key.trans (mul_le_mul_of_nonneg_left (hE z) (by positivity))

end LSG.AuxV
