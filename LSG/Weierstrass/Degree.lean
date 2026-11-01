/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.Residue
import LSG.Weierstrass.SigmaSign

/-!
# `℘` has degree two

For `z ∉ Λ` the elliptic function
`F(u) = (℘(u) - ℘(z)) σ(u)² / (σ(u - z) σ(u + z))`
has no poles except possibly a simple pole along `z + Λ` (when `2z ∈ Λ`, where `σ(u-z)σ(u+z)` has
a double zero but `℘ - ℘(z)` only a known simple one). By `eq_const_of_simple_pole` it is a
constant `C`, and `C ≠ 0` since `℘` is not constant. Hence

* `sigma_identity`: `(℘(u) - ℘(z)) σ(u)² = C σ(u - z) σ(u + z)` for `u ∉ Λ`, with `C ≠ 0`;
* `weierstrassP_eq_iff`: **`℘(w) = ℘(z) ↔ w ≡ ±z (mod Λ)`** for `z, w ∉ Λ`;
* `derivWeierstrassP_eq_zero_iff`: `℘'(z) = 0 ↔ 2z ∈ Λ` for `z ∉ Λ` (differentiate the identity
  at `u = z`: `℘'(z) σ(z)² = C σ(2z)`).
-/

open Module Filter Complex Set
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

/-! ### Small facts -/

lemma sigma_eq_mul_sigmaProd (u : ℂ) : sigma L u = u * sigmaProd L u := rfl

lemma continuous_sigma : Continuous (sigma L) := (differentiable_sigma L).continuous

lemma continuous_sigmaProd : Continuous (sigmaProd L) := (differentiable_sigmaProd L).continuous

lemma differentiableAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘[L] z :=
  L.differentiableOn_weierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)

lemma continuousAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘[L] z :=
  (differentiableAt_weierstrassP L hz).continuousAt

lemma continuousAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘'[L] z :=
  (differentiableAt_derivWeierstrassP L hz).continuousAt

lemma weierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : ℘[L] (u + ω) = ℘[L] u :=
  L.weierstrassP_add_coe u ⟨ω, hω⟩

lemma derivWeierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    ℘'[L] (u + ω) = ℘'[L] u :=
  L.derivWeierstrassP_add_coe u ⟨ω, hω⟩

/-- `℘(u) = ℘₀(u) + 1/u²`, `℘₀` the series without the `0`-term. -/
lemma weierstrassP_eq_except_zero (u : ℂ) : ℘[L] u = L.weierstrassPExcept 0 u + 1 / u ^ 2 := by
  have := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at this
  rw [← this]

/-- `℘'(u) = ℘'₀(u) - 2/u³`. -/
lemma derivWeierstrassP_eq_except_zero (u : ℂ) : ℘'[L] u = L.derivWeierstrassPExcept 0 u - 2 / u ^ 3 := by
  have := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero] at this
  rw [this]
  ring

lemma continuousAt_weierstrassPExcept_zero : ContinuousAt (L.weierstrassPExcept 0) 0 :=
  (L.analyticAt_weierstrassPExcept 0).continuousAt

lemma continuousAt_derivWeierstrassPExcept_zero : ContinuousAt (L.derivWeierstrassPExcept 0) 0 :=
  (L.analyticAt_derivWeierstrassPExcept 0).continuousAt

/-- `σ(u + ω) / σ(u)` is a nonvanishing multiplier. -/
lemma sigma_add' {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    sigma L (u + ω) = (sigmaSign L ω * exp (eta L ω * (u + ω / 2))) * sigma L u :=
  sigma_add L hω u

lemma sigmaSign_mul_exp_ne_zero (ω v : ℂ) : sigmaSign L ω * exp v ≠ 0 :=
  mul_ne_zero (sigmaSign_ne_zero L ω) (exp_ne_zero v)

lemma exp_mul_exp_eq {e a b c : ℂ} (h : a + b = 2 * c) :
    exp (e * a) * exp (e * b) = exp (e * c) * exp (e * c) := by
  rw [← exp_add, ← exp_add]
  congr 1
  linear_combination e * h

/-- `dslope` form of a difference quotient. -/
lemma dslope_eq_div {f : ℂ → ℂ} {a u : ℂ} (hu : u ≠ a) :
    dslope f a u = (f u - f a) / (u - a) := by
  rw [dslope_of_ne _ hu, slope_def_field]

/-! ### The function `F` -/

/-- `F(u) = (℘(u) - ℘(z)) σ(u)² / (σ(u - z) σ(u + z))`. -/
def degF (z u : ℂ) : ℂ :=
  (℘[L] u - ℘[L] z) * sigma L u ^ 2 / (sigma L (u - z) * sigma L (u + z))

lemma degF_add (z : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    degF L z (u + ω) = degF L z u := by
  unfold degF
  rw [weierstrassP_add_mem L u hω, sigma_add' L hω u, show u + ω - z = (u - z) + ω by ring,
    sigma_add' L hω (u - z), show u + ω + z = (u + z) + ω by ring, sigma_add' L hω (u + z)]
  set s := sigmaSign L ω
  set e := eta L ω
  have hE := exp_mul_exp_eq (e := e) (a := u - z + ω / 2) (b := u + z + ω / 2) (c := u + ω / 2)
    (by ring)
  have hK : s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sigmaSign_ne_zero L ω) (sigmaSign_ne_zero L ω))
      (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
  rw [show s * exp (e * (u - z + ω / 2)) * sigma L (u - z) *
      (s * exp (e * (u + z + ω / 2)) * sigma L (u + z)) =
      sigma L (u - z) * sigma L (u + z) *
        (s * s * (exp (e * (u - z + ω / 2)) * exp (e * (u + z + ω / 2)))) by ring, hE,
    show (℘[L] u - ℘[L] z) * (s * exp (e * (u + ω / 2)) * sigma L u) ^ 2 =
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 *
        (s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2)))) by ring,
    mul_div_mul_right _ _ hK]

lemma degF_neg (z u : ℂ) : degF L z (-u) = degF L z u := by
  unfold degF
  rw [weierstrassP_neg, sigma_neg, show -u - z = -(u + z) by ring, sigma_neg,
    show -u + z = -(u - z) by ring, sigma_neg]
  ring

/-- The singular set `Λ ∪ (z + Λ) ∪ (-z + Λ)`. -/
def degS (z : ℂ) : Set ℂ := {u | u ∈ L.lattice ∨ u - z ∈ L.lattice ∨ u + z ∈ L.lattice}

lemma discr_degS (z : ℂ) : Discr (degS L z) := by
  have h := ((discr_add L 0).union (discr_sub L z)).union (discr_add L z)
  convert h using 1
  ext u
  simp [degS, or_assoc]

lemma degS_add {z u ω : ℂ} (hu : u ∈ degS L z) (hω : ω ∈ L.lattice) : u + ω ∈ degS L z := by
  rcases hu with h | h | h
  · exact Or.inl (add_mem h hω)
  · right; left
    rw [show u + ω - z = (u - z) + ω by ring]; exact add_mem h hω
  · right; right
    rw [show u + ω + z = (u + z) + ω by ring]; exact add_mem h hω

lemma differentiableAt_degF {z x : ℂ} (hx : x ∉ degS L z) : DifferentiableAt ℂ (degF L z) x := by
  have h0 : x ∉ L.lattice := fun h => hx (Or.inl h)
  have h1 : x - z ∉ L.lattice := fun h => hx (Or.inr (Or.inl h))
  have h2 : x + z ∉ L.lattice := fun h => hx (Or.inr (Or.inr h))
  have hP := differentiableAt_weierstrassP L h0
  have hs := differentiable_sigma L
  unfold degF
  refine DifferentiableAt.div ?_ ?_ (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))
  · exact (hP.sub_const _).mul ((hs x).pow 2)
  · exact ((hs _).comp x (differentiableAt_id.sub_const z)).mul
      ((hs _).comp x (differentiableAt_id.add_const z))

/-- Near `0`: `F` is bounded. -/
lemma locBdd_degF_zero {z : ℂ} (hz : z ∉ L.lattice) : LocBdd (degF L z) 0 := by
  have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun u => (1 + u ^ 2 * L.weierstrassPExcept 0 u - u ^ 2 * ℘[L] z) * sigmaProd L u ^ 2 /
    (sigma L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact ((continuousAt_const.add ((continuousAt_id.pow 2).mul
        (continuousAt_weierstrassPExcept_zero L))).sub ((continuousAt_id.pow 2).mul
        continuousAt_const)).mul ((continuous_sigmaProd L).continuousAt.pow 2)
    · exact ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [zero_sub, zero_add]
      exact mul_ne_zero (sigma_ne_zero L hz') (sigma_ne_zero L hz)
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  simp only [g, degF, sigma_eq_mul_sigmaProd L u, weierstrassP_eq_except_zero L u]
  congr 1
  field_simp
  ring

/-- Near `z`, if `2z ∉ Λ`: `F` is bounded. -/
lemma locBdd_degF_self {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    LocBdd (degF L z) z := by
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, one_mul]
      exact sigma_ne_zero L (by rwa [← two_mul])
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  simp only [g, degF, dslope_eq_div hu, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp

/-- Near `z`, if `2z ∈ Λ`: `(u - z) F(u)` is bounded. -/
lemma locBdd_mul_degF_self_of_two_mul_mem {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∈ L.lattice) :
    LocBdd (fun u => (u - z) * degF L z u) z := by
  set s := sigmaSign L (2 * z)
  set e := eta L (2 * z)
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) ^ 2 * (s * exp (e * u)))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact (((continuous_sigmaProd L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).pow 2).mul (by fun_prop)
    · simp only [sub_self, sigmaProd_zero, one_pow, one_mul]
      exact sigmaSign_mul_exp_ne_zero L _ _
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  have hσ : sigma L (u + z) = s * exp (e * u) * sigma L (u - z) := by
    have := sigma_add L h2 (u - z)
    rw [show u - z + 2 * z = u + z by ring, show u - z + 2 * z / 2 = u by ring] at this
    exact this
  have hne := sigmaSign_mul_exp_ne_zero L (2 * z) (e * u)
  simp only [g, degF, dslope_eq_div hu, hσ, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp

/-- **The `σ`-identity.** For `z ∉ Λ` there is `C ≠ 0` with
`(℘(u) - ℘(z)) σ(u)² = C σ(u - z) σ(u + z)` for all `u ∉ Λ`. -/
theorem sigma_identity {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
  have hb : ∀ s ∈ degS L z, s - z ∉ L.lattice → LocBdd (degF L z) s := by
    intro s hs hsz
    rcases hs with h | h | h
    · have := (locBdd_degF_zero L hz).of_periodic (ω := s) (fun u => degF_add L z h u)
      rwa [zero_add] at this
    · exact absurd h hsz
    · have h2 : 2 * z ∉ L.lattice := by
        intro h2
        apply hsz
        have := sub_mem h h2
        rwa [show s + z - 2 * z = s - z by ring] at this
      have h1 := ((locBdd_degF_self L hz h2).of_even (degF_neg L z)).of_periodic (ω := s + z)
        (fun u => degF_add L z h u)
      rwa [show -z + (s + z) = s by ring] at h1
  have ha : LocBdd (fun u => (u - z) * degF L z u) z := by
    by_cases h2 : 2 * z ∈ L.lattice
    · exact locBdd_mul_degF_self_of_two_mul_mem L hz h2
    · exact (LocBdd.of_continuousAt (f := fun u => u - z) (by fun_prop)).mul
        (locBdd_degF_self L hz h2)
  obtain ⟨C, hC⟩ := eq_const_of_simple_pole L z (discr_degS L z)
    (fun u hu ω hω => degS_add L hu hω) (fun u _ ω hω => degF_add L z hω u)
    (fun x hx => differentiableAt_degF L hx) hb ha
  have key : ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
    intro u hu
    by_cases hS : u ∈ degS L z
    · rcases hS with h | h | h
      · exact absurd h hu
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L z h
          rwa [show z + (u - z) = u by ring] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L (-z) h
          rwa [show -z + (u + z) = u by ring, weierstrassP_neg] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
    · have h1 : u - z ∉ L.lattice := fun h => hS (Or.inr (Or.inl h))
      have h2 : u + z ∉ L.lattice := fun h => hS (Or.inr (Or.inr h))
      have := hC u hS
      unfold degF at this
      rw [div_eq_iff (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))] at this
      exact this
  refine ⟨C, fun hC0 => ?_, key⟩
  obtain ⟨u, hu, hM⟩ := exists_norm_weierstrassP_gt L ‖℘[L] z‖
  have := key u hu
  rw [hC0, zero_mul, mul_eq_zero] at this
  rcases this with h | h
  · rw [sub_eq_zero.mp h] at hM
    exact lt_irrefl _ hM
  · exact sigma_ne_zero L hu (pow_eq_zero_iff (by norm_num) |>.mp h)

/-- **Degree two.** For `z, w ∉ Λ`: `℘(w) = ℘(z) ↔ w ≡ z ∨ w ≡ -z (mod Λ)`. -/
theorem weierstrassP_eq_iff {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] w = ℘[L] z ↔ w - z ∈ L.lattice ∨ w + z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have := key w hw
    rw [h, sub_self, zero_mul, eq_comm, mul_eq_zero, mul_eq_zero] at this
    rcases this with h0 | h0 | h0
    · exact absurd h0 hC
    · exact Or.inl ((sigma_eq_zero_iff L).mp h0)
    · exact Or.inr ((sigma_eq_zero_iff L).mp h0)
  · rintro (h | h)
    · have := weierstrassP_add_mem L z h
      rwa [show z + (w - z) = w by ring] at this
    · have := weierstrassP_add_mem L (-z) h
      rwa [show -z + (w + z) = w by ring, weierstrassP_neg] at this

/-- The zeros of `℘'` off the lattice are exactly the half periods. -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have hs := differentiable_sigma L
    have hL : HasDerivAt (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2)
        (℘'[L] z * sigma L z ^ 2 + (℘[L] z - ℘[L] z) * (2 * sigma L z ^ 1 * deriv (sigma L) z))
        z := by
      have := ((hasDerivAt_weierstrassP L hz).sub_const (℘[L] z)).mul ((hs z).hasDerivAt.pow 2)
      convert this using 1
    have hR : HasDerivAt (fun u => C * (sigma L (u - z) * sigma L (u + z)))
        (C * (deriv (sigma L) (z - z) * 1 * sigma L (z + z) +
          sigma L (z - z) * (deriv (sigma L) (z + z) * 1))) z := by
      have h1 : HasDerivAt (fun u => sigma L (u - z)) (deriv (sigma L) (z - z) * 1) z :=
        (hs (z - z)).hasDerivAt.comp (h := fun u => u - z) z ((hasDerivAt_id' z).sub_const z)
      have h2 : HasDerivAt (fun u => sigma L (u + z)) (deriv (sigma L) (z + z) * 1) z :=
        (hs (z + z)).hasDerivAt.comp (h := fun u => u + z) z ((hasDerivAt_id' z).add_const z)
      exact (h1.mul h2).const_mul C
    have heq : (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2) =ᶠ[𝓝 z]
        fun u => C * (sigma L (u - z) * sigma L (u + z)) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hz] with u hu
      exact key u hu
    have := hL.unique (hR.congr_of_eventuallyEq heq)
    rw [h, sub_self, sub_self, deriv_sigma_zero, sigma_zero] at this
    simp only [zero_mul, add_zero, mul_one, one_mul] at this
    have h0 : sigma L (z + z) = 0 := by
      rcases mul_eq_zero.mp this.symm with h' | h'
      · exact absurd h' hC
      · exact h'
    rw [← two_mul] at h0
    exact (sigma_eq_zero_iff L).mp h0
  · intro h
    have := derivWeierstrassP_half L h
    rwa [mul_div_cancel_left₀ _ two_ne_zero] at this

end LSG.Weierstrass
