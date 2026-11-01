/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVStmt

/-!
# M2.7: the block-family hypotheses of the §5d engine for the vector-extension class

The engine (`AbVarV5d*.lean`) derives `HyperplaneKappaAbVarV An M` from Theorem 4.1 for the pivot subfamilies
(`Thm41FamV`) and three properties of the block family `B` (for `B = fun _ => aBlockV`, `M = bᵀ`: CM structure of
`A = Jac(y⁵ = x(1 − x))`, `LSG/JacBlockV/PerTanFib*.lean`):

* `PerTanFib B M` (`AbVarVStmt.lean`): the push-out of `B^♮` contains the fibre for every nonzero rational `t`
  (anti-affineness, M2.md N6);
* **`PerTanPiv B`**: for a rational `t` and a pivot `e` (`z ↦ z ∘ e` bijective on `t`), the fibre `η(λ)` of a
  period `λ ∈ t` is an algebraic linear image of the pivot fibres `η(λ ∘ e)`. So `B^♮ ≅ ∏_{e} B_{e i}^♮` on tangent
  spaces, and the push-out of `B^♮` along `M` is the push-out of `∏ B_{e i}^♮` along `M A` (for the CM block: the
  graph of `t` over `e` is given by CM endomorphisms `α_{ki}`, and `A_{ki} = σ̄(α_{ki})` since `η ∘ [α] = σ̄(α) η`);
* **`RatTangentsV B`**: rational `t` are `ℚ̄`-rational (γ's `ratTangentsA` for the base).
-/

open Module LSG.AuxAV

noncomputable section

namespace LSG.W88


open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock perBase perTanId)
open LSG.W88.Vec (AlgMat)

variable {m r : ℕ}

/-- **The pivot property of the block family**: for `t` rational and `e` a pivot of `t` (`z ↦ z ∘ e` is injective and
onto on `t`), there is an algebraic `A` with `η(λ) = A η(λ ∘ e)` for every period `λ ∈ t`. -/
def PerTanPiv (B : Fin m → VBlock) : Prop :=
  ∀ t : Submodule ℂ (∀ k, Fin (B k).g → ℂ), IsRatSub (perBase B) t →
    ∀ (n : ℕ) (e : Fin n → Fin m), Function.Injective e →
      (∀ z ∈ t, (∀ i, z (e i) = 0) → z = 0) →
      (∀ w : ∀ i, Fin (B (e i)).g → ℂ, ∃ z ∈ t, ∀ i, z (e i) = w i) →
      ∃ A : Matrix (Fin m) (Fin n) ℂ, AlgMat A ∧
        ∀ z ∈ t, (∀ k, z k ∈ (B k).base.per) →
          etaB B z = A.mulVec (fun i => (B (e i)).η (z (e i)))

/-- **Rational base tangents are `ℚ̄`-rational.** -/
def RatTangentsV (B : Fin m → VBlock) : Prop :=
  ∀ t : Submodule ℂ (∀ k, Fin (B k).g → ℂ), IsRatSub (perBase B) t →
    t = Submodule.span ℂ {z | z ∈ t ∧ ∀ k j, IsAlgebraic ℚ (z k j)}

/-- **Theorem 4.1 for the subfamilies** `B ∘ e` (`e` injective) with every algebraic onto push-out matrix. -/
def Thm41FamV {B : Fin m → VBlock} (An : ∀ k, VBlockAn (B k)) (r : ℕ) : Prop :=
  ∀ (n : ℕ) (e : Fin n → Fin m), Function.Injective e → ∀ M' : Matrix (Fin r) (Fin n) ℂ,
    Function.Surjective M'.mulVec → AlgMat M' → Theorem41AbVarVPer (fun i => An (e i)) M'

end LSG.W88
