/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarQbar
import LSG.JacBlock.PackagesW88

/-!
# `RatTangentsA` for the `AbBlock` family `fun _ => aBlock` (`IsRatSub (perAb …)` form)

**`ratTangents_aBlock`**: a tangent `t ⊂ ∏_k ℂ^{aBlock.g}` with `IsRatSub (perAb (fun _ => aBlock)) t` (the `t_rat` field
of `SubgroupDataB`; lattice `kerE`) is spanned by vectors with algebraic coordinates. From `ratTangentsA` through the
finite-index transfer `isRatSub_perAb_iff` (`latt ≤ kerE`, `kerE ⊆ ℚ·latt`) and `aBlock.g = 2` by `rfl`.
-/

namespace LSG.W88

open LSG.JacBlock LSG.AuxA

theorem ratTangents_aBlock {r : ℕ} {t : Submodule ℂ (∀ k : Fin r, Fin ((fun _ : Fin r => aBlock) k).g → ℂ)}
    (ht : LSG.MEB.IsRatSub (LSG.MEB.perAb (fun _ : Fin r => aBlock)) t) :
    t = Submodule.span ℂ {z | z ∈ t ∧ ∀ k j, IsAlgebraic ℚ (z k j)} := by
  have hΛle : ∀ k, latF (aBlockAnF r) k ≤ ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_le
  have hΛ : ∀ k, IsNsmulIn (latF (aBlockAnF r) k) ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_nsmul
  have h := (LSG.MEB.isRatSub_perAb_iff hΛle hΛ t).mpr ht
  exact ratTangentsA_isRatSub (r := r) (t := t) h

end LSG.W88
