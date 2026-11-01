/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.ABlock
import LSG.Jac.B56

/-!
# A4.6: the complete A-block instance

`aBlockD D` is `aBlockOf D` with A1's B5 certificates (`LSG.Jac.B56`: four local systems `lciS`/`lciF`, cover
exponent 7). **`aBlock := aBlockD stdPkg.D`** is a fixed instance. A5 constraints (`g = 2`, `N = 9`, `θ = D.thetaN`,
`per = kerE G`, `i₀ = 4`) hold by `rfl`.
-/

noncomputable section

open LSG.JacAn LSG.Jac

namespace LSG.JacBlock

/-- **The A-block** for any `θ`-datum over `a1Facts`. -/
def aBlockD {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
    {G : GermRad a1Facts hp hx} (D : ThetaData G) : LSG.MEB.AbBlock :=
  aBlockOf D 4 LSG.Jac.lciS LSG.Jac.lciF LSG.Jac.lciA_len LSG.Jac.lciA_F_le LSG.Jac.lciA_mem LSG.Jac.lciA_cover

/-- **The A-block** (fixed `θ`-datum `stdPkg.D`). -/
def aBlock : LSG.MEB.AbBlock := aBlockD stdPkg.D

section Checks

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

example : (aBlockD D).g = 2 := rfl
example : (aBlockD D).N = 9 := rfl
example : (aBlockD D).θ = D.thetaN := rfl
example : (aBlockD D).per = kerE G := rfl
example : (aBlockD D).i₀ = (4 : Fin 9) := rfl
example : aBlock.θ = stdPkg.D.thetaN := rfl
example : aBlock.per = kerE stdPkg.G := rfl

end Checks

end LSG.JacBlock
