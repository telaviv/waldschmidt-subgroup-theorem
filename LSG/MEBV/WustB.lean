/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SliceWust
import LSG.MEBV.WustHyp

/-!
# The sliced Wüstholz lemma from transversal data (M2.5, β; copy of `LSG.MEB.WustB`)

The `VBlock` copy of `LSG.MEB.WustB`. **One change**: `WustData` carries the Euler constant `cE` of its
order-defining derivations, `[Eul_k, Dw] = cE • Dw` (MEB: `cE = 1`; the chart derivations `Dmix` of
`LSG.MEBV.DerivOrd` have `cE = 2`, `WustAlgB.Eul_Dh`).

* `WustData d₀ d₁ B W E ℓ`: derivations `Dv i` (`i < ℓ`), `Q_j ∈ I(E)`, a multihomogeneous `M` with
  `Dv i Q_j − δ_ij M ∈ I(E)`; derivations `Dw` (indexed by `Ws`) defining `VOg Dw Ws I(E)`, the `Dv i` lowering the
  `VOg`-order by one, and the bridge `A ≤ homOrd W S₀ E ⇒ A ≤ VOg Dw Ws I(E) S₀`.
* **`wust_of_data`**, **`wust_field_of_data`**: such data on every finite union of distinct cosets give
  `WustPropV`'s conclusion.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

variable (d₀ d₁ B) in
/-- **Wüstholz transversal data** on `E` along `W`, with `ℓ` transversal directions. -/
structure WustData (W : Submodule ℂ (Tan d₀ d₁ B)) (E : Set (GPt d₀ d₁ B)) (ℓ : ℕ) where
  /-- the index type of the derivations defining the order ideal -/
  ι' : Type
  Dw : ι' → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)
  Ws : Set ι'
  /-- the (glued) transversal derivations -/
  Dv : Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)
  Q : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ
  M : MvPolynomial (Var d₀ d₁ B) ℂ
  μ : Fin m → ℕ
  hQ : ∀ j, Q j ∈ vanish E
  hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ vanish E
  hMh : IsWeightedHomogeneous wV M μ
  /-- the Euler constant: `[Eul_k, Dw] = cE • Dw` -/
  cE : ℕ
  hcomm : ∀ k i x, Eul k (Dw i x) = Dw i (Eul k x) + cE • Dw i x
  hDv : ∀ i (n : ℕ) x, x ∈ LSG.ME.VOg Dw Ws (vanish E) (n + 1) →
    Dv i x ∈ LSG.ME.VOg Dw Ws (vanish E) n
  bridge : ∀ (S0 : ℕ) (A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)),
    A ≤ homOrd W S0 E → A ≤ LSG.ME.VOg Dw Ws (vanish E) S0

/-- **The sliced Wüstholz lemma from transversal data**, for `E = ⋃_{a ∈ R} (a + V)`. -/
theorem wust_of_data {V : Set (GPt d₀ d₁ B)} (hp : (vanish V).IsPrime)
    (W : Submodule ℂ (Tan d₀ d₁ B)) (R : Finset (GPt d₀ d₁ B)) {ℓ : ℕ}
    (WD : WustData d₀ d₁ B W (⋃ a ∈ R, gtransl a V) ℓ)
    (hMn : ∀ a ∈ R, WD.M ∉ vanish (gtransl a V)) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    (α : Alpha B) (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V)) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) (S0 k : ℕ), ℓ * k ≤ S0 →
      A ≤ homOrd W S0 (⋃ a ∈ R, gtransl a V) → ∀ t,
      (k + 1) ^ ℓ * hfun blk D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a V))) t ≤
        hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  classical
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' blk hD WD.Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  have hpC : ∀ a ∈ R, (vanish (gtransl a V)).IsPrime := fun a _ => vanish_gtransl_isPrime hp a
  exact wustholz_sl_of_data α D WD.Dv (fun k x hx => Eul_mem_vanish k hx) WD.hQ WD.hδ
    (nzd_sl α R (fun a => gtransl a V) hpC hℓ WD.hMh hMn) hQdeg WD.hcomm WD.hDv hk
    (WD.bridge S0 A hA) t

/-- `SubgroupData.wust` from transversal data on every finite union of distinct cosets of `H⁰`. -/
theorem wust_field_of_data {O : ObstrDataGV d₀ d₁ B} (hp : (vanish O.grp).IsPrime)
    (hdata : ∀ (W : Submodule ℂ (Tan d₀ d₁ B)) (R : Finset (GPt d₀ d₁ B)),
      (∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ O.grp) → ∀ α : Alpha B,
      (∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
      ∃ WD : WustData d₀ d₁ B W (⋃ a ∈ R, gtransl a O.grp)
          (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)),
        ∀ a ∈ R, WD.M ∉ vanish (gtransl a O.grp)) :
    ∀ (W : Submodule ℂ (Tan d₀ d₁ B)) (R : Finset (GPt d₀ d₁ B)),
      (∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ O.grp) → ∀ D : Blk m → ℕ, (∀ i, 1 ≤ D i) →
      ∀ α : Alpha B, (∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
      ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) (S0 k : ℕ),
        (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * k ≤ S0 →
        A ≤ homOrd W S0 (⋃ a ∈ R, gtransl a O.grp) → ∀ t,
        (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) *
            hfun blk D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a O.grp))) t ≤
          hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  intro W R hdist D hD α hℓ
  obtain ⟨WD, hMn⟩ := hdata W R hdist α hℓ
  exact wust_of_data hp W R WD hMn D hD α hℓ

end LSG.MEBV
