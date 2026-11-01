/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dRat
import LSG.JacBlockV.PerTanFib3
import LSG.JacBlockV.Tay

/-!
# M2.7f: W88 §5d for the vector-extension class, and the `A^♮` block family

* **`hyperplaneKappaAbVarV_of`**: `HyperplaneKappaAbVarV An M` from Theorem 4.1 for the pivot subfamilies
  (`Thm41FamV`), `AlgMat M` and the block-family properties `PerTanFib B M`, `PerTanPiv B`, `RatTangentsV B`.
  Members with `t ≠ 0`: `trans41AV_ne` (frames + pivot); `t = 0`: `trans41AV_bot` (Roy); `W ∩ T_H` rational:
  `ratAV_inf_tan`; the chase: `hyperplaneKappaAbVarV_of_trans` (`coreAV`).
* **`thm41FamV_of`**: `Thm41FamV` from `theorem41AbVarVPer` (M2.6″, `AbVarVSec7.lean`) and `TayAllV`.
* **`hyperplaneKappaAbVarV_aBlockV`**: the specialisation to `B = fun _ : Fin m => aBlockV`, `An = aBlockVAn`,
  `M = bᵀ` (`r = 1`) for an adapted basis `b` (lean_mstar's `IsAdaptedBasisD (zetaN 5) φ(5) b`). Unconditional.
-/

open Module LSG.AuxAV

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEBV (VBlock)
open LSG.W88.Vec (AlgMat)

variable {m r : ℕ} {B : Fin m → VBlock}

/-- **W88 §5d for the vector-extension class** (toric-injective hyperplanes), from Theorem 4.1 for the pivot
subfamilies and the block-family properties. -/
theorem hyperplaneKappaAbVarV_of (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) (hMa : AlgMat M)
    (hF : PerTanFib B M) (hP : PerTanPiv B) (hRT : RatTangentsV B) (h41 : Thm41FamV An r) :
    HyperplaneKappaAbVarV An M :=
  hyperplaneKappaAbVarV_of_trans An hF
    (fun _ _ H' => by
      by_cases ht : H'.t = ⊥
      · exact trans41AV_bot An H' ht
      · exact trans41AV_ne An hF hP hMa h41 H' ht)
    (fun _ _ _ H hW => ratAV_inf_tan hRT hF hW H)

/-- **Theorem 4.1 for every subfamily**, from M2.6″'s `theorem41AbVarVPer`. -/
theorem thm41FamV_of (An : ∀ k, VBlockAn (B k)) (Tay : TayAllV B) (hr : r ≤ 1) : Thm41FamV An r :=
  fun _ e _ M' hM' hMa' =>
    theorem41AbVarVPer (fun i => An (e i)) (fun K _ _ ι k => Tay K ι (e k)) M' hM' hMa' hr

/-- **W88 §5d for the vector-extension class**, unconditional on Theorem 4.1. -/
theorem hyperplaneKappaAbVarV_uncond (An : ∀ k, VBlockAn (B k)) (Tay : TayAllV B)
    (M : Matrix (Fin r) (Fin m) ℂ) (hr : r ≤ 1) (hMa : AlgMat M) (hF : PerTanFib B M) (hP : PerTanPiv B)
    (hRT : RatTangentsV B) : HyperplaneKappaAbVarV An M :=
  hyperplaneKappaAbVarV_of An M hMa hF hP hRT (thm41FamV_of An Tay hr)

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × ((A_σ̄^♮)^m pushed out along bᵀ)`**, `A = Jac(y⁵ = x(1 − x))`, on
toric-injective hyperplanes, for an adapted basis `b`, with the `A^m`-components of the logarithms in the period
lattice (`LamAV`; the `G_a`, `G_m` and fibre components are arbitrary algebraic). `M = bᵀ` is algebraic and
`PerTanFib` holds (`perTanFib_aBlockV_of_adapted`), so this is a special case of W88 §5d. -/
theorem hyperplaneKappaAbVarV_aBlockV (b : Fin m → ℂ)
    (hb : MStarCopy.IsAdaptedBasisD (MStarCopy.zetaN 5) (Nat.totient 5) b) :
    HyperplaneKappaAbVarV (fun _ : Fin m => LSG.JacBlockV.aBlockVAn) (Matrix.of fun (_ : Fin 1) j => b j) :=
  hyperplaneKappaAbVarV_uncond _ (fun _ _ _ ι _ => LSG.JacBlockV.aBlockVTay ι) _ le_rfl
    (fun _ j => hb.alg j) (LSG.JacBlockV.perTanFib_aBlockV_of_adapted b hb)
    LSG.JacBlockV.perTanPiv_aBlockV LSG.JacBlockV.ratTangentsV_aBlockV

end LSG.W88
