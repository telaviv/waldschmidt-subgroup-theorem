/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Schneider
import LSG.SchneiderLang.Main
import LSG.Weierstrass.OrderTwo
import LSG.SchneiderWp

/-!
# Schneider's theorem on elliptic periods (unconditional)

For a lattice `Λ` whose Weierstrass invariants `g₂, g₃` are algebraic, every nonzero period `ω`
satisfies: `ω` is transcendental, and `ω / π` is transcendental (Schneider 1937).

The conditional versions are in `LSG/Schneider.lean`; here the two hypotheses are discharged by
the Schneider–Lang criterion `LSG.schneiderLang` and the order-two representation of `℘`, `℘'`
by the Weierstrass σ function, `LSG.Weierstrass.weierstrassOrderTwo`.
-/

open Complex

namespace LSG.Schneider

variable {L : PeriodPair}

/-- **Schneider.** A nonzero period of a lattice with algebraic `g₂, g₃` is transcendental. -/
theorem period_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {ω : ℂ}
    (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) : Transcendental ℚ ω :=
  period_transcendental_of LSG.schneiderLang (LSG.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃ hω h0

/-- **Schneider.** For a nonzero period `ω` of a lattice with algebraic `g₂, g₃`, `ω / π` is
transcendental. -/
theorem period_div_pi_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {ω : ℂ} (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) : Transcendental ℚ (ω / (Real.pi : ℂ)) :=
  period_div_pi_transcendental_of LSG.schneiderLang (LSG.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃
    hω h0

end LSG.Schneider

namespace LSG.Schneider

variable {L : PeriodPair}

/-- **Schneider.** If `g₂, g₃` are algebraic and `α ∉ Λ` is algebraic, then `℘(α)` is
transcendental. -/
theorem wp_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {α : ℂ}
    (hα : IsAlgebraic ℚ α) (hαΛ : α ∉ L.lattice) : Transcendental ℚ (L.weierstrassP α) :=
  wp_transcendental_of LSG.schneiderLang (LSG.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃ hα hαΛ

end LSG.Schneider
