/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.ZetaDef

/-!
# The Weierstrass `σ` function

For a period pair `L` we define the Weierstrass sigma function as the Weierstrass product
`σ(z) = z ∏'_{ω ≠ 0} E(z/ω)`, `E(u) = (1 - u) exp (u + u²/2)`.

In Lean the factor for `ω = 0` is `E(z/0) = E 0 = 1`, so we take the product over the whole
lattice.

## Main results
* `LSG.Weierstrass.differentiable_sigma`: `σ` is entire.
* `LSG.Weierstrass.sigma_eq_zero_iff`: `σ z = 0 ↔ z ∈ L.lattice`.
* `LSG.Weierstrass.sigma_neg`: `σ` is odd.
* `LSG.Weierstrass.hasDerivAt_sigma_zero`: `σ'(0) = 1`.
* `LSG.Weierstrass.logDeriv_sigma`: `σ'/σ = ζ` off the lattice.
* `LSG.Weierstrass.deriv_sigma`: `σ' = ζ σ` off the lattice.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

/-! ### The elementary factor -/

/-- Weierstrass' elementary factor of genus two, `E(u) = (1 - u) exp (u + u²/2)`. -/
def weierstrassFactor (u : ℂ) : ℂ := (1 - u) * exp (u + u ^ 2 / 2)

@[simp] lemma weierstrassFactor_zero : weierstrassFactor 0 = 1 := by
  simp [weierstrassFactor]

@[simp] lemma weierstrassFactor_one : weierstrassFactor 1 = 0 := by
  simp [weierstrassFactor]

lemma weierstrassFactor_eq_zero_iff {u : ℂ} : weierstrassFactor u = 0 ↔ u = 1 := by
  rw [weierstrassFactor, mul_eq_zero, sub_eq_zero, or_iff_left (exp_ne_zero _), eq_comm]

lemma differentiable_weierstrassFactor : Differentiable ℂ weierstrassFactor := by
  unfold weierstrassFactor; fun_prop

/-- `E'(u) = -u² exp (u + u²/2)`. -/
lemma hasDerivAt_weierstrassFactor (u : ℂ) :
    HasDerivAt weierstrassFactor (-u ^ 2 * exp (u + u ^ 2 / 2)) u := by
  have h1 : HasDerivAt (fun v : ℂ ↦ v + v ^ 2 / 2) (1 + u) u :=
    ((hasDerivAt_id' u).add ((hasDerivAt_pow 2 u).div_const 2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun v : ℂ ↦ (1 - v) * exp (v + v ^ 2 / 2))
      ((0 - 1) * exp (u + u ^ 2 / 2) + (1 - u) * (exp (u + u ^ 2 / 2) * (1 + u))) u :=
    ((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id' u)).mul h1.cexp
  exact h2.congr_deriv (by ring)

lemma logTaylor_three (z : ℂ) : logTaylor 3 z = z - z ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

/-- The key estimate `‖E(u) - 1‖ ≤ 2‖u‖³` for `‖u‖ ≤ 1/2`. -/
lemma norm_weierstrassFactor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖weierstrassFactor u - 1‖ ≤ 2 * ‖u‖ ^ 3 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; norm_num at hu
  set w := log (1 + -u) - logTaylor (2 + 1) (-u) with hw
  have hwb := norm_log_sub_logTaylor_le 2 hu1
  rw [← hw, norm_neg] at hwb
  have hw' : w = log (1 - u) + (u + u ^ 2 / 2) := by
    rw [hw, show (2 + 1 : ℕ) = 3 from rfl, logTaylor_three, ← sub_eq_add_neg]; ring
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hwle : ‖w‖ ≤ ‖u‖ ^ 3 := by
    calc ‖w‖ ≤ ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) := by exact_mod_cast hwb
      _ ≤ ‖u‖ ^ 3 * 2 / 3 := by
          norm_num
          gcongr
      _ ≤ ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]
  have hu3 : ‖u‖ ^ 3 ≤ 1 := by
    calc ‖u‖ ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
      _ ≤ 1 := by norm_num
  have hexp : weierstrassFactor u = exp w := by
    rw [hw', exp_add, exp_log hne, weierstrassFactor]
  rw [hexp]
  calc ‖exp w - 1‖ ≤ 2 * ‖w‖ := norm_exp_sub_one_le (hwle.trans hu3)
    _ ≤ 2 * ‖u‖ ^ 3 := by gcongr

/-! ### Lattice bookkeeping -/

variable (L : PeriodPair)

/-- All but finitely many lattice points have norm at least `R`. -/
lemma eventually_le_norm (R : ℝ) : ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rw [Filter.eventually_cofinite]
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  simp only [Set.mem_ofPred_eq, not_le] at hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hl.le

lemma summable_norm_rpow_neg_three :
    Summable (fun l : L.lattice ↦ ‖(l : ℂ)‖ ^ (-3 : ℝ)) :=
  ZLattice.summable_norm_rpow _ _ (by simp; norm_num)

/-- Bound on the factors of the product for `‖z‖ ≤ r` and `‖l‖ ≥ 2r`. -/
lemma norm_weierstrassFactor_div_sub_one_le {r : ℝ} (hr : 0 < r) {z l : ℂ} (hz : ‖z‖ ≤ r)
    (hl : 2 * r ≤ ‖l‖) : ‖weierstrassFactor (z / l) - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hzl : ‖z / l‖ ≤ r / ‖l‖ := by rw [norm_div]; gcongr
  have hrl : r / ‖l‖ ≤ 1 / 2 := by rw [div_le_iff₀ hl0]; linarith
  refine (norm_weierstrassFactor_sub_one_le (hzl.trans hrl)).trans ?_
  rw [Real.rpow_neg hl0.le, show ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 by norm_cast]
  calc 2 * ‖z / l‖ ^ 3 ≤ 2 * (r / ‖l‖) ^ 3 := by gcongr
    _ = 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by field_simp

lemma summable_norm_weierstrassFactor_div_sub_one (z : ℂ) :
    Summable (fun l : L.lattice ↦ ‖weierstrassFactor (z / l) - 1‖) := by
  set r := ‖z‖ + 1
  have hr : 0 < r := by positivity
  refine ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_le_norm L (2 * r)] with l hl
  rw [norm_norm]
  exact norm_weierstrassFactor_div_sub_one_le hr (by simp [r]) hl

/-! ### The product -/

/-- The product `∏'_{ω} E(z/ω)`, so that `σ(z) = z · sigmaProd L z`. -/
def sigmaProd (z : ℂ) : ℂ := ∏' l : L.lattice, weierstrassFactor (z / l)

/-- The Weierstrass sigma function `σ(z) = z ∏'_{ω ≠ 0} (1 - z/ω) exp (z/ω + z²/(2ω²))`. -/
def sigma (z : ℂ) : ℂ := z * sigmaProd L z

lemma hasProdLocallyUniformlyOn_sigmaProd :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
      (sigmaProd L) Set.univ := by
  have key : HasProdLocallyUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ 1 + (weierstrassFactor (z / l) - 1))
      (fun z ↦ ∏' l : L.lattice, (1 + (weierstrassFactor (z / l) - 1))) Set.univ := by
    refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK ↦ ?_
    obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_closedBall 0
    set r := max r₀ 1
    have hr : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)) ?_ fun l ↦ ?_
    · filter_upwards [eventually_le_norm L (2 * r)] with l hl x hx
      refine norm_weierstrassFactor_div_sub_one_le hr ?_ hl
      have := hr₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    · exact ((differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).sub_const
        _).continuous.continuousOn
  rw [show sigmaProd L = fun z ↦ ∏' l : L.lattice, weierstrassFactor (z / l) from rfl]
  simpa only [add_sub_cancel] using key

/-- The product is entire. -/
lemma differentiable_sigmaProd : Differentiable ℂ (sigmaProd L) := by
  have := (hasProdLocallyUniformlyOn_sigmaProd L).differentiableOn
    (.of_forall fun s ↦ ?_) isOpen_univ
  · exact fun x ↦ (this x (Set.mem_univ x)).differentiableAt (isOpen_univ.mem_nhds trivial)
  · simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)

/-- `σ` is entire. -/
lemma differentiable_sigma : Differentiable ℂ (sigma L) :=
  differentiable_id.mul (differentiable_sigmaProd L)

lemma weierstrassFactor_div_ne_zero {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    weierstrassFactor (z / l) ≠ 0 := by
  rw [Ne, weierstrassFactor_eq_zero_iff]
  intro h
  have hl : (l : ℂ) ≠ 0 := by rintro h'; rw [h', div_zero] at h; exact zero_ne_one h
  rw [div_eq_one_iff_eq hl] at h
  exact hz (h ▸ l.2)

lemma sigmaProd_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigmaProd L z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable
    (f := fun l : L.lattice ↦ weierstrassFactor (z / l) - 1)
    (fun l ↦ by simpa using weierstrassFactor_div_ne_zero L hz l)
    (summable_norm_weierstrassFactor_div_sub_one L z)
  simpa only [add_sub_cancel, sigmaProd] using this

lemma sigmaProd_coe (l : L.lattice) (hl : (l : ℂ) ≠ 0) : sigmaProd L l = 0 :=
  tprod_of_exists_eq_zero ⟨l, by simp [div_self hl]⟩

@[simp] lemma sigmaProd_zero : sigmaProd L 0 = 1 := by
  simp [sigmaProd]

/-- The zeros of `σ` are exactly the lattice points. -/
lemma sigma_eq_zero_iff {z : ℂ} : sigma L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := fun h0 ↦ hz (h0 ▸ L.lattice.zero_mem)
    exact mul_ne_zero hz0 (sigmaProd_ne_zero L hz) h
  · intro hz
    by_cases hz0 : z = 0
    · simp [sigma, hz0]
    · simp [sigma, sigmaProd_coe L ⟨z, hz⟩ hz0]

lemma sigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigma L z ≠ 0 :=
  fun h ↦ hz ((sigma_eq_zero_iff L).mp h)

@[simp] lemma sigma_zero : sigma L 0 = 0 := by simp [sigma]

lemma sigma_coe (l : L.lattice) : sigma L l = 0 := (sigma_eq_zero_iff L).mpr l.2

lemma sigmaProd_neg (z : ℂ) : sigmaProd L (-z) = sigmaProd L z := by
  unfold sigmaProd
  rw [← (Equiv.neg L.lattice).tprod_eq]
  congr 1 with l
  simp [neg_div, div_neg]

/-- `σ` is odd. -/
lemma sigma_neg (z : ℂ) : sigma L (-z) = -sigma L z := by
  simp [sigma, sigmaProd_neg]

/-- `σ'(0) = 1`. -/
lemma hasDerivAt_sigma_zero : HasDerivAt (sigma L) 1 0 := by
  have := (hasDerivAt_id' (0 : ℂ)).mul (differentiable_sigmaProd L 0).hasDerivAt
  convert this using 1
  · rfl
  · simp

lemma deriv_sigma_zero : deriv (sigma L) 0 = 1 := (hasDerivAt_sigma_zero L).deriv

/-! ### Logarithmic derivative -/

lemma hasDerivAt_weierstrassFactor_div (l x : ℂ) :
    HasDerivAt (fun z ↦ weierstrassFactor (z / l))
      (-(x / l) ^ 2 * exp (x / l + (x / l) ^ 2 / 2) * (1 / l)) x := by
  have h := (hasDerivAt_weierstrassFactor (x / l)).comp x ((hasDerivAt_id' x).div_const l)
  exact h

lemma logDeriv_weierstrassFactor_div (l x : ℂ) (hx : x ≠ l) :
    logDeriv (fun z ↦ weierstrassFactor (z / l)) x = if l = 0 then 0 else zetaSummand l x := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassFactor_div l x).deriv]
  split_ifs with hl
  · simp [hl]
  · rw [zetaSummand_eq l x hl hx, weierstrassFactor]
    have h1 : (1 : ℂ) - x / l ≠ 0 := by
      rw [sub_ne_zero, ne_eq, eq_div_iff hl, one_mul]; exact fun h ↦ hx h.symm
    have h2 : x - l ≠ 0 := sub_ne_zero.mpr hx
    have h3 : (1 : ℂ) - x / l = -(x - l) / l := by field_simp; ring
    rw [h3]
    field_simp

lemma summable_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    Summable fun l : L.lattice ↦ logDeriv (fun z ↦ weierstrassFactor (z / l)) x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  refine (summable_zetaSummand L x).congr_cofinite ?_
  filter_upwards [eventually_le_norm L 1] with l hl
  have : (l : ℂ) ≠ 0 := by rintro h; rw [h, norm_zero] at hl; norm_num at hl
  simp [this]

lemma tsum_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    ∑' l : L.lattice, logDeriv (fun z ↦ weierstrassFactor (z / l)) x = zeta L x - 1 / x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  have hs := summable_zetaSummand L x
  have e : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else zetaSummand l x) =
      zetaSummand l x - if l = 0 then 1 / x else 0 := by
    intro l
    by_cases hl : l = 0
    · simp [hl, zetaSummand]
    · have : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      simp [hl, this]
  simp_rw [e]
  rw [hs.tsum_sub (summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset (by
    intro l hl; by_contra h; simp_all))), tsum_ite_eq]
  rfl

lemma logDeriv_sigmaProd {x : ℂ} (hx : x ∉ L.lattice) :
    logDeriv (sigmaProd L) x = zeta L x - 1 / x := by
  have h := logDeriv_tprod_eq_tsum (isOpen_compl_coe_lattice L) hx
    (f := fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
    (weierstrassFactor_div_ne_zero L hx)
    (fun l ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)
    (summable_logDeriv_weierstrassFactor_div L hx)
    ((hasProdLocallyUniformlyOn_sigmaProd L).multipliableLocallyUniformlyOn.mono
      (Set.subset_univ _))
    (sigmaProd_ne_zero L hx)
  rw [← tsum_logDeriv_weierstrassFactor_div L hx, ← h]
  rfl

/-- `σ'/σ = ζ` off the lattice. -/
lemma logDeriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : logDeriv (sigma L) x = zeta L x := by
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ L.lattice.zero_mem)
  have := logDeriv_mul (f := id) (g := sigmaProd L) x hx0 (sigmaProd_ne_zero L hx)
    differentiableAt_id (differentiable_sigmaProd L x)
  rw [show sigma L = id * sigmaProd L from rfl, this, logDeriv_id, logDeriv_sigmaProd L hx]
  ring

/-- `σ' = ζ σ` off the lattice. -/
lemma deriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : deriv (sigma L) x = zeta L x * sigma L x := by
  have := logDeriv_sigma L hx
  rw [logDeriv_apply, div_eq_iff (sigma_ne_zero L hx)] at this
  exact this

end LSG.Weierstrass
