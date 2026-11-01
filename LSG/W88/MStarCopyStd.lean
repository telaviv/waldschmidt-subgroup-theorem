/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopy
import LSG.W88.Statement

/-!
# Verbatim copy of `lean_mstar`'s standard model `gmStd` and its hypotheses `HypStd`, `HypStdCM`

Source: `lean_mstar/CM4E/Bridge/Std.lean` (namespace `CM4E.Bridge`, commits 5026ff8, 95ddbfa), read 2026-10-31.
The bodies of `algStd`, `gmStd`, `HypStd`, `HypStdCM`, `HypStdCMAt` are copied verbatim; only the namespace is
`LSG.W88.MStarCopy`, and names that are ambiguous there are written fully qualified
(`LSG.W88.AlgVec`, as in the source the overloaded `AlgVec` resolves to it), so that the terms are the
same constants. `GroupModel`/`HyperplaneKappa` are the verbatim copies of `MStarCopy.lean`.
Hence `LSG.W88.MStarCopy.HypStd` and `CM4E.Bridge.HypStd` unfold to the same proposition.
-/

open Module

namespace LSG.W88.MStarCopy

variable {d0 d1 m : ℕ}

/-- Algebraic vectors of `Tan d₀ d₁ m`. -/
def algStd (v : LSG.W88.Tan d0 d1 m) : Prop :=
  LSG.W88.AlgVec v.1 ∧ LSG.W88.AlgVec v.2.1 ∧ LSG.W88.AlgVec v.2.2

/-- **The standard model of `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`.** -/
noncomputable def gmStd (d0 d1 : ℕ) {m : ℕ} (Ls : Fin m → PeriodPair) :
    GroupModel (LSG.W88.Tan d0 d1 m) where
  d₁ := d1
  d₂ := m
  alg := algStd
  lam := LSG.W88.Lam Ls
  per := Submodule.span ℚ (LSG.W88.Per (d0 := d0) (d1 := d1) Ls : Set (LSG.W88.Tan d0 d1 m))
  sub := fun S => ∃ H : LSG.W88.SubgroupData (d0 := d0) (d1 := d1) Ls, S = H.tan

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`** (curves with algebraic invariants). -/
def HypStd : Prop :=
  ∀ (d0 d1 m : ℕ) (Ls : Fin m → PeriodPair), (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) →
    HyperplaneKappa (gmStd d0 d1 Ls)

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × E^r`, one curve `E` repeated**. -/
def HypStdCM (L : PeriodPair) : Prop :=
  ∀ (d0 d1 r : ℕ), IsAlgebraic ℚ L.g₂ → IsAlgebraic ℚ L.g₃ → HyperplaneKappa (gmStd d0 d1 (fun _ : Fin r => L))

/-- The case `d₀ = d` of `HypStdCM`. -/
def HypStdCMAt (L : PeriodPair) (d : ℕ) : Prop :=
  ∀ (d1 r : ℕ), IsAlgebraic ℚ L.g₂ → IsAlgebraic ℚ L.g₃ → HyperplaneKappa (gmStd d d1 (fun _ : Fin r => L))

end LSG.W88.MStarCopy
