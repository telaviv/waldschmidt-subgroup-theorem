/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarProp61
import LSG.W88.Sec7Aux

/-!
# A5.7a: W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`, the statement (`STAGE_A5.md` §6.1)

Generic over a family of abelian blocks `B : Fin m → AbBlock` with analytic packages `An` (`AbBlockAn`); write
`G = Σ_k g_k`, `Λ = latF An` (the periods W88 counts, `Λ_k ≤ per_k` of finite index).

* **`LamB An`**: logarithms of algebraic points with block parts in `Λ` (`LamA` for the `A`-block).
* `AlgTanB`, `RationalOverQbarB`: the `ℚ̄`-structure of `T_G`.
* **`SubgroupDataB d₀ d₁ B`**: `H₀ × T_U × B′`, `h₀` `ℚ̄`-rational, `t` rational for `perAb B` (equivalently for
  `perAbL Λ`, `isRatSub_perAb_iff`); `tan`, `δ₀ δ₁ δ₂ δ`, `Proper`.
* **`Theorem41B An`**: W88 Theorem 4.1 under (NR) and toric injectivity, the exact analogue of
  `Theorem41AbVarPer` (`2r ↦ G`, `PerA ↦ PerL d₀ d₁ B Λ`, `TorInjA ↦ TorInjB`).
* `TayAll B`: Taylor packages over every number field (A5.8 supplies them for the `A`-block).
-/

open Module LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock PerL perAb IsRatSub tanOf)

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

variable (d₀ d₁) in
/-- **The logarithms of algebraic points with block parts in `Λ`.** -/
def LamB (An : ∀ k, AbBlockAn (B k)) : AddSubgroup (MEB.Tan d₀ d₁ B) where
  carrier := {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧ ∀ k, p.2.2 k ∈ (An k).lat}
  add_mem' {p q} hp hq := by
    refine ⟨fun i => (hp.1 i).add (hq.1 i), fun i => ?_, fun k => (An k).lat.add_mem (hp.2.2 k) (hq.2.2 k)⟩
    change IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
    rw [Complex.exp_add]; exact (hp.2.1 i).mul (hq.2.1 i)
  zero_mem' := ⟨fun _ => isAlgebraic_zero, fun _ => by simpa using isAlgebraic_one,
    fun k => (An k).lat.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨fun i => (hp.1 i).neg, fun i => ?_, fun k => (An k).lat.neg_mem (hp.2.2 k)⟩
    change IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
    rw [Complex.exp_neg]; exact (hp.2.1 i).inv

/-- The `ℚ̄`-structure of `T_G`. -/
def AlgTanB (p : MEB.Tan d₀ d₁ B) : Prop :=
  AlgVec p.1 ∧ AlgVec p.2.1 ∧ ∀ k j, IsAlgebraic ℚ (p.2.2 k j)

/-- `ℚ̄`-rational subspaces of `T_G`. -/
def RationalOverQbarB (W : Submodule ℂ (MEB.Tan d₀ d₁ B)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgTanB w}

variable (d₀ d₁ B) in
/-- **Data of a connected algebraic subgroup** `G′ = H₀ × T_U × B′` of `G_a^{d₀} × G_m^{d₁} × ∏ B_k`. -/
structure SubgroupDataB where
  h0 : Submodule ℂ (Fin d₀ → ℂ)
  U : Submodule ℚ (Fin d₁ → ℚ)
  t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)
  h0_rat : RationalOverQbar h0
  t_rat : IsRatSub (perAb B) t

namespace SubgroupDataB

variable (H : SubgroupDataB d₀ d₁ B)

/-- The tangent space `T_{G′} = h₀ × U^⊥ × t`. -/
def tan : Submodule ℂ (MEB.Tan d₀ d₁ B) := tanOf H.h0 H.U H.t

/-- `δ₀ = codim h₀`. -/
def δ0 : ℕ := d₀ - finrank ℂ H.h0
/-- `δ₁ = dim U`. -/
def δ1 : ℕ := finrank ℚ H.U
/-- `δ₂ = codim t = G − dim t`. -/
def δ2 : ℕ := (∑ k, (B k).g) - finrank ℂ H.t
/-- `δ = codim G′`. -/
def δ : ℕ := H.δ0 + H.δ1 + H.δ2

/-- `G′ ≠ G`. -/
def Proper : Prop := H.δ ≠ 0

end SubgroupDataB

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`, under (NR) and toric injectivity** (the family `B` and its
packages fixed; `d₀, d₁` free). -/
def Theorem41B (An : ∀ k, AbBlockAn (B k)) : Prop :=
  ∀ (d₀ d₁ : ℕ) (V W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (Y : AddSubgroup (MEB.Tan d₀ d₁ B)),
    finrank ℂ V < d₀ + d₁ + ∑ k, (B k).g → W ≤ V → RationalOverQbarB W →
    Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamB d₀ d₁ An) → TorInjB V →
    -- (NR)
    d₁ + 2 * d₀ + rk (Y ⊓ PerL d₀ d₁ B (latF An)) ≤ 2 * finrank ℂ V →
    ∃ H : SubgroupDataB d₀ d₁ B, H.Proper ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
      (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerL d₀ d₁ B (latF An))) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
          ((d₀ + d₁ + ∑ k, (B k).g : ℕ) - finrank ℂ V : ℤ) ≤
        ((H.δ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
          ((d₁ + 2 * ∑ k, (B k).g : ℕ) - rk (Y ⊓ PerL d₀ d₁ B (latF An)) : ℤ))

variable (B) in
/-- **Taylor packages over every number field** (`AbBlockTay`; for the `A`-block from `ks_chart4F`). -/
def TayAll :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (k : Fin m), AbBlockTay (B k) ι

end LSG.W88
