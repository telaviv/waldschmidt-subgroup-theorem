/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7V2
import LSG.AuxFunV.PropGVT
import LSG.W88.V5dMXPcm

/-!
# Theorem MX′'s hypothesis `Thm11KappaMXP`, unconditionally (`STAGE6_MXP.md`)

* **`LSG.W88.prop21GVT`**: W83 Prop. 2.1 on `V` with `dim (V ∩ fibre) ≤ 1`
  (`LSG.AuxV.prop21GVT_of_le_one`);
* **`LSG.W88.theorem41Vec2 : Theorem41Vec2`**: W88 Theorem 4.1 for the class `𝒞` with `d₀ = 0`,
  `r ≤ 2`, `dim (V ∩ fibre) ≤ 1` (`theorem41Vec2_of`);
* **`LSG.W88.V5d.hyperplaneKappaVec2_uncond : HyperplaneKappaVec2`** (W88 §5d at `d₀ = 0`,
  `r ≤ 2`);
* **`LSG.W88.V5d.thm11KappaMXP_uncond : MStarCopy.Thm11KappaMXP`** (verbatim copy of
  `lean_mstar`'s `CM4E.Gen.Thm11KappaMXP`).
-/

namespace LSG.W88

/-- **W83 Prop. 2.1 on `V` with `dim (V ∩ fibre) ≤ 1`.** -/
theorem prop21GVT : Prop21GVT := fun _ _ _ _ Ls M V hV _ ω hωV hωP hω =>
  LSG.AuxV.prop21GVT_of_le_one Ls M V hV ω hωV hωP hω

/-- **W88 Theorem 4.1 for the class `𝒞` with `d₀ = 0`, `r ≤ 2`, `dim (V ∩ fibre) ≤ 1`.** -/
theorem theorem41Vec2 : Vec.Theorem41Vec2 := theorem41Vec2_of prop21GVT

end LSG.W88

namespace LSG.W88.V5d

/-- **W88 §5d for the class with `d₀ = 0`, `r ≤ 2`, unconditionally.** -/
theorem hyperplaneKappaVec2_uncond : Vec.HyperplaneKappaVec2 :=
  hyperplaneKappaVec2_of LSG.W88.theorem41Vec2

/-- **Theorem MX′'s hypothesis, unconditionally** (statement verbatim from `lean_mstar`). -/
theorem thm11KappaMXP_uncond : MStarCopy.Thm11KappaMXP :=
  thm11KappaMXP_of LSG.W88.theorem41Vec2

end LSG.W88.V5d
