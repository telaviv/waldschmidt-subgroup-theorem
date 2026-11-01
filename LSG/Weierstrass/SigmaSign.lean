/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaQuasiPeriod

/-!
# Quasi-periodicity of `σ` for every period

For every `ω ∈ Λ`,
`σ(z + ω) = ε(ω) · exp (η(ω) (z + ω/2)) · σ(z)`, with `ε(ω) = 1` if `ω/2 ∈ Λ` and `ε(ω) = -1`
otherwise.

The case `ω/2 ∉ Λ` is `sigma_add_of_half_notMem`. If `ω/2 ∈ Λ`, apply the formula for `ω/2`
twice (the signs cancel); the recursion terminates by strong induction on `|m| + |n|`,
`ω = m ω₁ + n ω₂`. No use of Legendre's relation is needed.

As a consequence the zeros of `σ` are simple: `σ'(ω) = ε(ω) exp (η(ω) ω/2) ≠ 0` for `ω ∈ Λ`.
-/

open Module Filter Complex
open scoped Topology

noncomputable section

namespace LSG.Weierstrass

open PeriodPair

variable (L : PeriodPair)

open scoped Classical in
/-- The sign `ε(ω)` in the quasi-periodicity of `σ`: `1` if `ω/2 ∈ Λ`, `-1` otherwise. -/
def sigmaSign (ω : ℂ) : ℂ := if ω / 2 ∈ L.lattice then 1 else -1

lemma sigmaSign_sq (ω : ℂ) : sigmaSign L ω ^ 2 = 1 := by
  unfold sigmaSign; split_ifs <;> norm_num

lemma sigmaSign_ne_zero (ω : ℂ) : sigmaSign L ω ≠ 0 := by
  unfold sigmaSign; split_ifs <;> norm_num

lemma sigmaSign_of_half_notMem {ω : ℂ} (h : ω / 2 ∉ L.lattice) : sigmaSign L ω = -1 := by
  simp [sigmaSign, h]

lemma sigmaSign_of_half_mem {ω : ℂ} (h : ω / 2 ∈ L.lattice) : sigmaSign L ω = 1 := by
  simp [sigmaSign, h]

/-- The doubling step: the formula for `ω'` implies the formula for `2ω'`. -/
lemma sigma_add_two_mul {ω' : ℂ} (hω' : ω' ∈ L.lattice)
    (ih : ∀ z, sigma L (z + ω') = sigmaSign L ω' * exp (eta L ω' * (z + ω' / 2)) * sigma L z)
    (z : ℂ) :
    sigma L (z + 2 * ω') = sigmaSign L (2 * ω') * exp (eta L (2 * ω') * (z + 2 * ω' / 2)) *
      sigma L z := by
  have h2 : (2 * ω') / 2 ∈ L.lattice := by simpa using hω'
  rw [sigmaSign_of_half_mem L h2, two_mul ω', eta_add L hω' hω',
    show z + (ω' + ω') = (z + ω') + ω' by ring, ih, ih]
  have hs := sigmaSign_sq L ω'
  have e : exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) =
      exp ((eta L ω' + eta L ω') * (z + (ω' + ω') / 2)) := by
    rw [← exp_add]; ring_nf
  linear_combination (exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) *
    sigma L z) * hs + sigma L z * e

/-- **Quasi-periodicity of `σ`.** For every `ω ∈ Λ`,
`σ(z + ω) = ε(ω) · exp (η(ω) (z + ω/2)) · σ(z)`. -/
theorem sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    sigma L (z + ω) = sigmaSign L ω * exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.mp hω
  revert z
  induction h : m.natAbs + n.natAbs using Nat.strong_induction_on generalizing m n with
  | _ N ih =>
  intro z
  by_cases h2 : ((m : ℂ) * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice
  · obtain ⟨m', n', hmn⟩ := mem_lattice.mp h2
    -- coordinates of `ω/2` are half those of `ω`
    have hind := LinearIndependent.pair_iff.mp L.indep ((2 * m' - m : ℤ) : ℝ)
      ((2 * n' - n : ℤ) : ℝ) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination 2 * hmn)
    have hm : 2 * m' = m := by have := Int.cast_eq_zero.mp hind.1; omega
    have hn : 2 * n' = n := by have := Int.cast_eq_zero.mp hind.2; omega
    by_cases h0 : N = 0
    · have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hm0 hn0
      simp [sigmaSign]
    · have hlt : m'.natAbs + n'.natAbs < N := by omega
      have ih' := ih _ hlt m' n' (by rw [hmn]; exact h2) rfl
      have e : (m : ℂ) * L.ω₁ + n * L.ω₂ = 2 * ((m' : ℂ) * L.ω₁ + n' * L.ω₂) := by
        rw [← hm, ← hn]; push_cast; ring
      rw [e]
      exact sigma_add_two_mul L (by rw [hmn]; exact h2) ih' z
  · rw [sigmaSign_of_half_notMem L h2, sigma_add_of_half_notMem L hω h2 z]
    ring

/-- `σ'(ω) = ε(ω) exp (η(ω) ω/2)` for `ω ∈ Λ`. -/
lemma deriv_sigma_of_mem {ω : ℂ} (hω : ω ∈ L.lattice) :
    deriv (sigma L) ω = sigmaSign L ω * exp (eta L ω * (ω / 2)) := by
  have h1 : HasDerivAt (fun z ↦ sigma L (z + ω)) (deriv (sigma L) (0 + ω)) 0 :=
    (differentiable_sigma L (0 + ω)).hasDerivAt.comp_add_const 0 ω
  have hE : HasDerivAt (fun z ↦ exp (eta L ω * (z + ω / 2)))
      (exp (eta L ω * (0 + ω / 2)) * (eta L ω * 1)) 0 :=
    (((hasDerivAt_id' (0 : ℂ)).add_const (ω / 2)).const_mul (eta L ω)).cexp
  have h2 := ((hasDerivAt_const (0 : ℂ) (sigmaSign L ω)).mul hE).mul (hasDerivAt_sigma_zero L)
  have h3 : HasDerivAt (fun z ↦ sigma L (z + ω)) (((0 * exp (eta L ω * (0 + ω / 2)) +
      sigmaSign L ω * (exp (eta L ω * (0 + ω / 2)) * (eta L ω * 1))) * sigma L 0 +
      sigmaSign L ω * exp (eta L ω * (0 + ω / 2)) * 1)) 0 := by
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
    exact sigma_add L hω z
  have := h1.unique h3
  rw [zero_add] at this
  rw [this, sigma_zero, zero_add]
  ring

/-- The zeros of `σ` are simple. -/
lemma deriv_sigma_ne_zero_of_mem {ω : ℂ} (hω : ω ∈ L.lattice) : deriv (sigma L) ω ≠ 0 := by
  rw [deriv_sigma_of_mem L hω]
  exact mul_ne_zero (sigmaSign_ne_zero L ω) (exp_ne_zero _)

end LSG.Weierstrass
