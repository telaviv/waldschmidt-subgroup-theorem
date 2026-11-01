/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Basic facts about `℘` for a `PeriodPair`

* `LSG.Weierstrass.hasDerivAt_derivWeierstrassP` : `℘'' = 6 ℘² - g₂ / 2` off the lattice.
* Half periods: `℘'(ω/2) = 0`, `4 e³ - g₂ e - g₃ = 0` for `e = ℘(ω/2)`, algebraicity of `e`,
  translates `ω/2 + kω`.
* `LSG.Weierstrass.exists_primitive` : every nonzero period is `m • ω₀` with `ω₀/2 ∉ Λ`.
* Algebraic independence of `(z, ℘ z)` and of `(℘ z, exp (2πi z / ω))` over any field
  `K → ℂ`.
-/

open Complex Filter Topology PeriodPair Real

namespace LSG.Weierstrass

variable (L : PeriodPair)

/-! ### Generalities on the lattice -/

lemma intCast_mul_mem {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) : (k : ℂ) * ω ∈ L.lattice := by
  simpa [zsmul_eq_mul] using L.lattice.smul_mem k hω

lemma natCast_mul_mem {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℕ) : (k : ℂ) * ω ∈ L.lattice := by
  simpa using (intCast_mul_mem L) hω k

lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0

lemma ω₂_ne_zero : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1

/-- Integer coordinates with respect to `ω₁, ω₂` are unique. -/
lemma int_coords_eq {a b c d : ℤ} (h : (a : ℂ) * L.ω₁ + b * L.ω₂ = c * L.ω₁ + d * L.ω₂) :
    a = c ∧ b = d := by
  have := LinearIndependent.pair_iff.mp L.indep ((a : ℝ) - c) ((b : ℝ) - d)
    (by simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have h1 := this.1; rw [sub_eq_zero] at h1; exact_mod_cast h1
  · have h2 := this.2; rw [sub_eq_zero] at h2; exact_mod_cast h2

lemma lattice_countable : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    intro x hx
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hx
    exact ⟨(m, n), h⟩
  exact (Set.countable_range _).mono this

lemma isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
  ((lattice_countable L).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

lemma isOpen_compl_lattice : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl

lemma add_mem_lattice_iff {z ω : ℂ} (hω : ω ∈ L.lattice) : z + ω ∈ L.lattice ↔ z ∈ L.lattice :=
  L.lattice.add_mem_iff_left hω

/-! ### `℘` is unbounded (near `0`) -/

/-- `℘` takes arbitrarily large values off the lattice. -/
lemma exists_norm_weierstrassP_gt (M : ℝ) : ∃ z, z ∉ L.lattice ∧ M < ‖℘[L] z‖ := by
  have hc : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  set B := ‖(L.weierstrassPExcept 0) 0‖ + 1
  have hB : 0 ≤ B := by positivity
  set A := |M| + B + 2
  have hA : 2 ≤ A := by have := abs_nonneg M; linarith
  set t : ℝ := min (min δ₁ δ₂ / 2) (1 / A)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < min δ₁ δ₂ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htA : t ≤ 1 / A := min_le_right _ _
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
  have ht1 : ‖(t : ℂ)‖ < δ₁ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_left _ _)
  have ht2 : ‖(t : ℂ)‖ < δ₂ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_right _ _)
  have hnot : (t : ℂ) ∉ L.lattice := by
    have := hball (show (t : ℂ) ∈ Metric.ball 0 δ₂ by
      rw [Metric.mem_ball, dist_zero_right]; exact ht2)
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at this
    intro hm
    have := this hm
    exact (ne_of_gt ht0) (by exact_mod_cast this)
  refine ⟨t, hnot, ?_⟩
  have hbd : ‖(L.weierstrassPExcept 0) t‖ ≤ B := by
    have := hb (x := (t : ℂ)) (by rw [dist_zero_right]; exact ht1)
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' (L.weierstrassPExcept 0 t) (L.weierstrassPExcept 0 0)
    simp only [B]
    linarith
  have hdecomp : ℘[L] t = (L.weierstrassPExcept 0) t + 1 / (t : ℂ) ^ 2 := by
    rw [← L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩]; simp
  have hinv : A ≤ 1 / t ^ 2 := by
    have h1 : A * t ≤ 1 := by rw [le_div_iff₀ (by linarith)] at htA; linarith
    have ht1' : t ≤ 1 := by
      have : 1 / A ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hnorm : ‖1 / (t : ℂ) ^ 2‖ = 1 / t ^ 2 := by
    simp [norm_pow, abs_of_pos ht0]
  rw [hdecomp]
  have := norm_sub_norm_le (1 / (t : ℂ) ^ 2) (-(L.weierstrassPExcept 0) t)
  rw [sub_neg_eq_add, norm_neg, hnorm, add_comm] at this
  have hM := le_abs_self M
  linarith

lemma infinite_image_weierstrassP : (℘[L] '' (L.lattice : Set ℂ)ᶜ).Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hfin.isBounded
  obtain ⟨z, hz, hM⟩ := (exists_norm_weierstrassP_gt L) R
  exact absurd (hR _ ⟨z, hz, rfl⟩) (not_le.mpr hM)

/-! ### `℘'' = 6 ℘² - g₂/2` -/

lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘[L] (℘'[L] z) z := by
  have := (L.differentiableOn_weierstrassP.differentiableAt
    ((isOpen_compl_lattice L).mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at this

lemma differentiableAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘'[L] z :=
  L.differentiableOn_derivWeierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)

/-- `℘'` does not vanish identically near any point off the lattice. -/
lemma derivWeierstrassP_not_eventually_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) :
    ¬ (℘'[L] =ᶠ[𝓝 z₀] 0) := by
  intro h
  have hEq := L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_compl_lattice L) hz₀ h
  have hconst : ∀ x ∈ (L.lattice : Set ℂ)ᶜ, ℘[L] x = ℘[L] z₀ := fun x hx =>
    (isOpen_compl_lattice L).is_const_of_deriv_eq_zero (isPreconnected_compl_lattice L)
      L.differentiableOn_weierstrassP (by intro y hy; simp [hEq hy]) hx hz₀
  obtain ⟨z, hz, hM⟩ := (exists_norm_weierstrassP_gt L) ‖℘[L] z₀‖
  rw [hconst z hz] at hM
  exact lt_irrefl _ hM

/-- **`℘'' = 6 ℘² - g₂ / 2`** off the lattice. -/
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  -- the product identity `℘' (℘'' - 6℘² + g₂/2) = 0` off the lattice
  have key : ∀ w, w ∉ L.lattice →
      ℘'[L] w * (deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2)) = 0 := by
    intro w hw
    have h1 : HasDerivAt (fun x => ℘'[L] x ^ 2) (↑2 * ℘'[L] w ^ (2 - 1) * deriv ℘'[L] w) w :=
      ((differentiableAt_derivWeierstrassP L) hw).hasDerivAt.pow 2
    have hP := (hasDerivAt_weierstrassP L) hw
    have h2 : HasDerivAt (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃)
        (4 * (↑3 * ℘[L] w ^ (3 - 1) * ℘'[L] w) - L.g₂ * ℘'[L] w) w :=
      (((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃
    have hev : (fun x => ℘'[L] x ^ 2) =ᶠ[𝓝 w] (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hw] with x hx
      exact L.derivWeierstrassP_sq x hx
    have := h1.unique (h2.congr_of_eventuallyEq hev)
    norm_num at this
    linear_combination this / 2
  set F : ℂ → ℂ := fun w => deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2) with hF
  have hFa : AnalyticAt ℂ F z := by
    have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub ((analyticAt_const.mul (h2.pow 2)).sub analyticAt_const)
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘'[L] w ≠ 0 :=
    (L.analyticOnNhd_derivWeierstrassP z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      ((derivWeierstrassP_not_eventually_zero L) hz)
  have hU : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice :=
    nhdsWithin_le_nhds ((isOpen_compl_lattice L).mem_nhds hz)
  have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = 0 := by
    refine (hne.and hU).mono ?_ |>.frequently
    rintro w ⟨h1, h2⟩
    exact (mul_eq_zero.mp (key w h2)).resolve_left h1
  have hFz : F z = 0 := (hFa.frequently_zero_iff_eventually_zero.mp hfreq).self_of_nhds
  have hd := ((differentiableAt_derivWeierstrassP L) hz).hasDerivAt
  rwa [sub_eq_zero.mp hFz] at hd

/-! ### Half periods -/

/-- `℘'(ω/2) = 0` for every period `ω` (if `ω/2 ∈ Λ` this is the junk value). -/
lemma derivWeierstrassP_half {ω : ℂ} (hω : ω ∈ L.lattice) : ℘'[L] (ω / 2) = 0 := by
  have h1 : ℘'[L] (ω / 2) = ℘'[L] (-(ω / 2)) := by
    rw [← L.derivWeierstrassP_sub_coe (ω / 2) ⟨ω, hω⟩]
    congr 1; ring
  rw [L.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2

/-- `e = ℘(ω/2)` is a root of `4X³ - g₂X - g₃`. -/
lemma weierstrassP_half_cubic {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) :
    4 * ℘[L] (ω / 2) ^ 3 - L.g₂ * ℘[L] (ω / 2) - L.g₃ = 0 := by
  have := L.derivWeierstrassP_sq (ω / 2) h2
  rw [(derivWeierstrassP_half L) hω] at this
  linear_combination -this

/-- If `g₂, g₃` are algebraic, so is `℘(ω/2)`. -/
lemma isAlgebraic_weierstrassP_half (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) : IsAlgebraic ℚ (℘[L] (ω / 2)) := by
  set F := IntermediateField.adjoin ℚ ({L.g₂, L.g₃} : Set ℂ)
  have : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hg₂.isIntegral
    · exact hg₃.isIntegral)
  have m₂ : L.g₂ ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have m₃ : L.g₃ ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hF : IsAlgebraic F (℘[L] (ω / 2)) := by
    refine ⟨4 * Polynomial.X ^ 3 - Polynomial.C ⟨L.g₂, m₂⟩ * Polynomial.X
      - Polynomial.C ⟨L.g₃, m₃⟩, ?_, ?_⟩
    · intro hp
      have := congrArg (Polynomial.coeff · 3) hp
      simp at this
    · simpa [map_ofNat] using (weierstrassP_half_cubic L) hω h2
  exact hF.restrictScalars (R := ℚ)

lemma half_add_mul_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) (k : ℤ) :
    ω / 2 + k * ω ∉ L.lattice := by
  rwa [(add_mem_lattice_iff L) ((intCast_mul_mem L) hω k)]

lemma weierstrassP_half_add_mul {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) :
    ℘[L] (ω / 2 + k * ω) = ℘[L] (ω / 2) :=
  L.weierstrassP_add_coe (ω / 2) ⟨_, (intCast_mul_mem L) hω k⟩

lemma derivWeierstrassP_half_add_mul {ω : ℂ} (hω : ω ∈ L.lattice) (k : ℤ) :
    ℘'[L] (ω / 2 + k * ω) = 0 := by
  rw [L.derivWeierstrassP_add_coe (ω / 2) ⟨_, intCast_mul_mem L hω k⟩,
    derivWeierstrassP_half L hω]

/-! ### Primitive periods -/

/-- Every nonzero period is a positive integer multiple of a period `ω₀` with `ω₀/2 ∉ Λ`. -/
theorem exists_primitive {ω : ℂ} (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) :
    ∃ (m : ℕ) (ω₀ : ℂ), 1 ≤ m ∧ ω₀ ∈ L.lattice ∧ ω = (m : ℂ) * ω₀ ∧ ω₀ / 2 ∉ L.lattice := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hω
  set g := Int.gcd a b with hg
  have hg0 : 0 < g := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h
    exact h0 (by simp [← hab])
  set a' := a / g
  set b' := b / g
  have ha : a = a' * g := (Int.ediv_mul_cancel (Int.gcd_dvd_left a b)).symm
  have hb : b = b' * g := (Int.ediv_mul_cancel (Int.gcd_dvd_right a b)).symm
  have hcop : Int.gcd a' b' = 1 := Int.gcd_div_gcd_div_gcd hg0
  refine ⟨g, a' * L.ω₁ + b' * L.ω₂, hg0, ?_, ?_, ?_⟩
  · exact add_mem (intCast_mul_mem L L.ω₁_mem_lattice a') (intCast_mul_mem L L.ω₂_mem_lattice b')
  · rw [← hab, ha, hb]; push_cast; ring
  · intro hmem
    obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp hmem
    have := int_coords_eq L (show ((2 * c : ℤ) : ℂ) * L.ω₁ + ((2 * d : ℤ) : ℂ) * L.ω₂ =
      (a' : ℂ) * L.ω₁ + (b' : ℂ) * L.ω₂ by push_cast; linear_combination 2 * hcd)
    have h2 : (2 : ℤ) ∣ (Int.gcd a' b' : ℤ) :=
      Int.dvd_coe_gcd ⟨c, this.1.symm⟩ ⟨d, this.2.symm⟩
    rw [hcop] at h2
    norm_num at h2

/-! ### Algebraic independence -/

section AlgIndep

variable {K : Type*} [Field K] [Algebra K ℂ]

lemma mvPoly_one_eq_zero (c : MvPolynomial (Fin 1) ℂ) {Y : Set ℂ} (hY : Y.Infinite)
    (h : ∀ y ∈ Y, MvPolynomial.eval ![y] c = 0) : c = 0 := by
  obtain ⟨t, ht, htc⟩ := hY.exists_subset_card_eq (c.degreeOf 0 + 1)
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c (fun _ => t) ?_ ?_
  · intro i
    fin_cases i
    simp [htc]
  · intro x hx
    have hx' : x = ![x 0] := by ext i; fin_cases i; rfl
    rw [hx']
    exact h _ (ht (hx 0))

/-- A polynomial in two variables vanishing on infinitely many horizontal lines' worth of
infinitely many points is zero: if for infinitely many `y` the polynomial `P(·, y)` has infinitely
many roots, then `P = 0`. -/
theorem mvPoly_eq_zero_of_infinite_fibres (P : MvPolynomial (Fin 2) K) {Y : Set ℂ}
    (hY : Y.Infinite) (hfib : ∀ y ∈ Y, {x : ℂ | MvPolynomial.aeval ![x, y] P = 0}.Infinite) :
    P = 0 := by
  set P' := MvPolynomial.map (algebraMap K ℂ) P
  have hP' : ∀ v : Fin 2 → ℂ, MvPolynomial.aeval v P = MvPolynomial.eval v P' := by
    intro v
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  suffices hP0 : P' = 0 by
    exact MvPolynomial.map_injective _ (algebraMap K ℂ).injective (hP0.trans (map_zero _).symm)
  set Q := MvPolynomial.finSuccEquiv ℂ 1 P'
  have hQy : ∀ y ∈ Y, Polynomial.map (MvPolynomial.eval ![y]) Q = 0 := by
    intro y hy
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (hfib y hy).mono ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hP'] at hx
    rw [Polynomial.IsRoot, ← MvPolynomial.eval_eq_eval_mv_eval']
    exact hx
  have hQ : Q = 0 := by
    refine Polynomial.ext fun j => ?_
    simp only [Polynomial.coeff_zero]
    refine mvPoly_one_eq_zero _ hY fun y hy => ?_
    have := congrArg (Polynomial.coeff · j) (hQy y hy)
    simpa [Polynomial.coeff_map] using this
  exact (MvPolynomial.finSuccEquiv ℂ 1).injective (hQ.trans (map_zero _).symm)

/-- Variant of `mvPoly_eq_zero_of_infinite_fibres` with the roles of the variables swapped. -/
theorem mvPoly_eq_zero_of_infinite_fibres' (P : MvPolynomial (Fin 2) K) {X : Set ℂ}
    (hX : X.Infinite) (hfib : ∀ x ∈ X, {y : ℂ | MvPolynomial.aeval ![x, y] P = 0}.Infinite) :
    P = 0 := by
  set σ := Equiv.swap (0 : Fin 2) 1
  have hsw : ∀ x y : ℂ, MvPolynomial.aeval ![y, x] (MvPolynomial.rename σ P) =
      MvPolynomial.aeval ![x, y] P := by
    intro x y
    rw [MvPolynomial.aeval_rename]
    congr 2
    funext i
    fin_cases i <;> rfl
  have : MvPolynomial.rename σ P = 0 :=
    mvPoly_eq_zero_of_infinite_fibres _ hX fun x hx => by simpa [hsw] using hfib x hx
  exact MvPolynomial.rename_injective σ σ.injective (by rw [this, map_zero])

/-- **`z` and `℘(z)` are algebraically independent** over any field `K → ℂ`. -/
theorem algIndep_id_weierstrassP (P : MvPolynomial (Fin 2) K)
    (hP : ∀ z, z ∉ L.lattice → MvPolynomial.aeval ![z, ℘[L] z] P = 0) : P = 0 := by
  refine mvPoly_eq_zero_of_infinite_fibres P (infinite_image_weierstrassP L) ?_
  rintro _ ⟨z₀, hz₀, rfl⟩
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => z₀ + k * L.ω₁) ?_ ?_
  · intro k l hkl
    have := (ω₁_ne_zero L)
    simp only [add_right_inj] at hkl
    exact_mod_cast mul_right_cancel₀ this hkl
  · intro k
    have hmem := (intCast_mul_mem L) L.ω₁_mem_lattice k
    have hz : z₀ + k * L.ω₁ ∉ L.lattice := by rwa [(add_mem_lattice_iff L) hmem]
    have := hP _ hz
    rwa [L.weierstrassP_add_coe z₀ ⟨_, hmem⟩] at this

/-- For `ω ≠ 0` there is a period `ω'` with `‖exp (2πi ω'/ω)‖ ≠ 1`. -/
lemma exists_norm_exp_ne_one {ω : ℂ} (h0 : ω ≠ 0) :
    ∃ ω' ∈ L.lattice, ‖cexp (2 * π * I / ω * ω')‖ ≠ 1 := by
  by_contra! H
  have him : ∀ ω' ∈ L.lattice, (ω' / ω).im = 0 := by
    intro ω' hω'
    have := H ω' hω'
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at this
    have he : 2 * π * I / ω * ω' = 2 * π * I * (ω' / ω) := by field_simp
    rw [he] at this
    generalize ω' / ω = u at this ⊢
    have hu : (2 * (π : ℂ) * I * u).re = -(2 * π) * u.im := by simp [Complex.mul_re]
    rw [hu] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by have := Real.pi_pos; linarith)
    · exact h
  have hre : ∀ ω' ∈ L.lattice, ω' = ((ω' / ω).re : ℂ) * ω := by
    intro ω' hω'
    have : ((ω' / ω).re : ℂ) = ω' / ω := Complex.ext (by simp) (by simp [him ω' hω'])
    rw [this]; field_simp
  obtain ⟨s, hs1⟩ : ∃ s : ℝ, L.ω₁ = s * ω := ⟨_, hre _ L.ω₁_mem_lattice⟩
  obtain ⟨t, ht2⟩ : ∃ t : ℝ, L.ω₂ = t * ω := ⟨_, hre _ L.ω₂_mem_lattice⟩
  have := LinearIndependent.pair_iff.mp L.indep t (-s)
    (by simp only [Complex.real_smul]; rw [hs1, ht2]; push_cast; ring)
  have hs : s = 0 := by simpa using this.2
  exact (ω₁_ne_zero L) (by rw [hs1, hs]; simp)

/-- **`℘(z)` and `exp (2πi z/ω)` are algebraically independent** over any field `K → ℂ`, for
a nonzero period `ω`. -/
theorem algIndep_weierstrassP_exp {ω : ℂ} (h0 : ω ≠ 0) (P : MvPolynomial (Fin 2) K)
    (hP : ∀ z, z ∉ L.lattice → MvPolynomial.aeval ![℘[L] z, cexp (2 * π * I / ω * z)] P = 0) :
    P = 0 := by
  obtain ⟨ω', hω', hc⟩ := (exists_norm_exp_ne_one L) h0
  set c := cexp (2 * π * I / ω * ω')
  refine mvPoly_eq_zero_of_infinite_fibres' P (infinite_image_weierstrassP L) ?_
  rintro _ ⟨z₀, hz₀, rfl⟩
  have hexp : ∀ k : ℕ,
      cexp (2 * π * I / ω * (z₀ + k * ω')) = cexp (2 * π * I / ω * z₀) * c ^ k := by
    intro k
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; ring
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => cexp (2 * π * I / ω * (z₀ + k * ω'))) ?_ ?_
  · intro k l hkl
    simp only [hexp] at hkl
    have h' := congrArg norm hkl
    simp only [norm_mul, norm_pow] at h'
    have hn : ‖cexp (2 * π * I / ω * z₀)‖ ≠ 0 := by simp [Complex.exp_ne_zero]
    have h'' := mul_left_cancel₀ hn h'
    exact pow_right_injective₀ (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hc h''
  · intro k
    have hmem := (natCast_mul_mem L) hω' k
    have hz : z₀ + k * ω' ∉ L.lattice := by rwa [(add_mem_lattice_iff L) hmem]
    have := hP _ hz
    rwa [L.weierstrassP_add_coe z₀ ⟨_, hmem⟩] at this

end AlgIndep

end LSG.Weierstrass
