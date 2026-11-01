/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.Surj
import LSG.JacBlockV.Laws
import LSG.JacBlockV.B56V

/-!
# M2.4b: the vector-extension block `aBlockV : LSG.MEBV.VBlock` (`A_σ̄^♮` over `LSG.JacBlock.aBlock`)

`aBlockVD D` is the `VBlock` over `aBlockD D` for any `θ`-datum `D` over `a1Facts`;
**`aBlockV := aBlockVD stdPkg.D`**, so `aBlockV.base = LSG.JacBlock.aBlock` by `rfl`. Field sources:

| field | value / proof |
|---|---|
| `nT`, `fc`, `fc_charts` | `3`, `fcV = ![0, 4, 8]` (`Model`) |
| `gensT`, `gensT_hom` | `gensTV = [P₀₄, P₀₈, P₄₈]` as `plkGen` (`Model`; equal to B6V's `P04V`… after renaming, `B56V`) |
| `Φ`, `Φ_analytic`, `liftT_model` | `ΦV D` (`fibT`), `ΦV_analytic`, `liftT_modelV` (from `T_plkV`) |
| `η`, `lift_per` | `D.etaB`, `lift_perV` (on all of `kerE`, via `ThetaData.fibT_add_isPer`, `Period`) |
| `surjV` | `surjVV` (`Surj`, M2.1.6) |
| `nLV`, `ld`, `lawV*` | `81`, `3`, `lawVV` defined by `pderiv` from `spMv (Data.law k m)` (`Laws`) |
| `WT`, `T_flow` | `WTV t j = ⅓ kQ (fc t) j 0`, `T_flowV` (`ThetaData.fibT_flow`) |
| `plk`, `T_plk` | `plkV t t' = −⅓ Wmv (fc t) 0 (fc t')` (`plkV_self : plk t t = 0`), `T_plkV` (all charts) |
| `t₀`, `fc_t₀` | `1`, `rfl` (`fcV 1 = 4 = aBlock.i₀`) |
| `hilb_l`, `hilb_deg`, `hilb` | `hilbLV` (`T₀, T₄, T₈, X₀ + X₄ + X₈`), `41`, `hilbVV` (from `LSG.Jac.hilbV`) |
| `lci_*` | 12 systems `(i, s)`, multiplier `S_iX_{fc s}` (`B56V`, `kappaV` + `lciA_mem`, cover `lciA_cover·hilbA`) |
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV

namespace LSG.JacBlockV

open LSG.JacBlock

/-- **The vector-extension block `A_σ̄^♮`** over `aBlockD D`. -/
def aBlockVD {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
    {G : GermRad a1Facts hp hx} (D : ThetaData G) : LSG.MEBV.VBlock where
  base := aBlockD D
  nT := 3
  fc := fcV
  fc_charts := fc_charts
  gensT := gensTV
  gensT_hom := gensTV_hom
  Φ := ΦV D
  Φ_analytic := ΦV_analytic D
  liftT_model := liftT_modelV D
  η := D.etaB
  lift_per := lift_perV D
  surjV := surjVV D
  nLV := 81
  ld := 3
  lawV := lawVV
  lawV_hom := lawVV_hom
  lawV_eq := lawVV_eq D
  lawV_complete := lawVV_complete D
  WT := WTV
  WT_hom := WTV_hom
  T_flow := fun t _ => T_flowV D t
  plk := plkV
  plk_hom := plkV_hom
  T_plk := T_plkV D
  t₀ := 1
  fc_t₀ := rfl
  hilb_l := hilbLV
  hilb_deg := 41
  hilb := hilbVV
  lci_s := 12
  lci_S := lciSV
  lci_F := lciFV
  lci_len := lciV_len
  lci_F_le := lciV_F_le
  lci_mem := lciV_mem
  lci_cover := lciV_cover

/-- **The vector-extension block `A_σ̄^♮`** (fixed `θ`-datum `stdPkg.D`). -/
def aBlockV : LSG.MEBV.VBlock := aBlockVD stdPkg.D

section Checks

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

example : (aBlockVD D).base = aBlockD D := rfl
example : aBlockV.base = aBlock := rfl
example : (aBlockVD D).nT = 3 := rfl
example : (aBlockVD D).fc = fcV := rfl
example : fcV = ![0, 4, 8] := rfl
example : (aBlockVD D).t₀ = (1 : Fin 3) := rfl
example : (aBlockVD D).nLV = 81 := rfl
example : (aBlockVD D).ld = 3 := rfl
example : (aBlockVD D).hilb_deg = 41 := rfl
example : (aBlockVD D).η = D.etaB := rfl
example : (aBlockVD D).base.per = kerE G := rfl
example (t : Fin 3) : (aBlockVD D).plk t t = 0 := plkV_self t
example (a : Fin 4) (i : Fin 9 ⊕ Fin 3) : (aBlockVD D).hilb_l a i = hilbL a (finSumFinEquiv i) := rfl

end Checks

end LSG.JacBlockV
