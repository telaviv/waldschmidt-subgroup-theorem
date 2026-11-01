/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.Exit
import LSG.JacBlock.Tan4
import LSG.JacBlock.Tan8
import LSG.JacBlock.Affine
import LSG.JacBlock.Anchor
import LSG.Jac.E1Final

/-!
# `SurjFacts`: the certificate batch of A4.1b, discharged (agent γ)

`surjFactsOf A …` builds `LSG.JacAn.SurjFacts A` for any `A : A1Facts` whose model, law 0, `[−1]` and chart-4/8
flows are A1's (`OnQ`, `lawPt 0`, `negP`, `W4n/4`, `W8n/4`). Every A1 instance has these fields definitionally, so
`surjFactsMk` instantiates it for `mkA1Facts` with arbitrary values of its five remaining hypotheses, and
**`surjFacts : SurjFacts a1Facts`** is the instance for A1's unconditional `a1Facts`.

Sources of the fields (all standard axioms, no `sorry`, no `native_decide`):
* `affine_chart`: `affine_chartG` (`Affine.lean`, ideal membership in `I_A + (X₀ − 1)` by `linear_combination`).
* `anchor`: `anchorG` (`Anchor.lean`, `2D₀ = (21α/2, −6α², 99α⁴/2, 53)`, `λ = 54872 α⁴`).
* `gensI`, `gensI_diff`, `gensI_iff`, `tanC4/8`, `tanC4/8_cont`, `gensI_tan4/8`: `Gens.lean`.
* `exit4`, `exit8`: `exit4G`, `exit8G` (`Exit.lean`).
-/

noncomputable section

namespace LSG.JacBlock

open LSG.JacAn LSG.Jac

/-- **`SurjFacts` for any `A1Facts` built on A1's polynomial maps.** -/
def surjFactsOf (A : A1Facts) (hOnQ : A.OnQ = OnQ) (hlaw0 : A.law0 = lawPt 0) (hneg : A.negP = negP)
    (hW4 : A.W4 = W4G) (hW8 : A.W8 = W8G) : SurjFacts A where
  affine_chart X hX hX0 := affine_chartG X (hOnQ ▸ hX) hX0
  anchor := by rw [hlaw0, hneg]; exact anchorG
  gensI := gensA
  gensI_diff := gensA_diff
  gensI_iff X := by rw [hOnQ]; exact onQ_iff_gens X
  tanC4 := tanC4
  tanC8 := tanC8
  tanC4_cont := tanC4_cont
  tanC8_cont := tanC8_cont
  gensI_tan4 j i X := by rw [hW4]; exact gens_tan4 j i X
  gensI_tan8 j i X := by rw [hW8]; exact gens_tan8 j i X
  exit4 X hX hX0 h4 := by rw [hW4]; exact exit4G X (hOnQ ▸ hX) hX0 h4
  exit8 X hX hX0 h8 := by rw [hW8]; exact exit8G X (hOnQ ▸ hX) hX0 h8

/-- The instance for A1's `mkA1Facts` (any values of its remaining hypotheses). -/
def surjFactsMk (E1_40 E1_44 E1_4 E2_4 dup_ne_zero) :
    SurjFacts (mkA1Facts E1_40 E1_44 E1_4 E2_4 dup_ne_zero) :=
  surjFactsOf _ rfl rfl rfl rfl rfl

/-- **`SurjFacts` for A1's unconditional `a1Facts`** (`LSG.Jac.E1Final`). -/
def surjFacts : SurjFacts a1Facts := surjFactsOf a1Facts rfl rfl rfl rfl rfl

end LSG.JacBlock
