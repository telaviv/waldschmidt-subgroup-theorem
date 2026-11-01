/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Stmt

/-!
# The multiplicity estimate on `G̃` itself, with symmetries (M2.5 α; the shape of `LSG.MEV.multEstG`)

`MultEstV` (the frozen statement, `Stmt.lean`) is about the push-out `G = G̃_r / K_M`. The core proves it in two
steps (as MEV does): the multiplicity estimate on the product `G̃ = G_a^{d₀} × G_m^{d₁} × ∏_k B_k^♮` with a
subspace `Kv ⊆ Lie G̃` of symmetries of the order hypothesis (`MultEstGV`, proved in `Main.lean` from
`MEBVInputs`), and the push-out bookkeeping (`MainPush.lean`, `multEstV_of`).

* `ObstrDataGV d₀ d₁ B`: obstruction data on `G̃` (no push-out): `ObstrDataBV` without `ker_le`.
* `prA` (the projection to `ℂ^{d₀}`), `ex0 T = dim prA T`, `ex2 T = dim (T ∩ ker prA ∩ ker prB)`: W88's projection
  exponents on `G̃`.
* **`MultEstGV`**: the statement on `G̃`, with `Kv ⊆ O.tan` in the conclusion.
-/

open MvPolynomial Module LSG.W88

namespace LSG.MEBV

open LSG.MEB (Blk DfunB IsRatSub perAb)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- **Obstruction data on `G̃`**: a member `T_U × (B̃ + Γ)` of the subgroup family, `t` rational for the base
periods, `grp = zcl (exp T′)` a Zariski-closed subgroup with Lie algebra `T′ = tanOfV Γ U t`, and
`exp⁻¹(grp) ⊆ ℚ ⊗ (T′ + Ω(G̃))`. (`ObstrDataBV` without `ker_le`.) -/
structure ObstrDataGV (d₀ d₁ : ℕ) {m : ℕ} (B : Fin m → VBlock) where
  U : Submodule ℚ (Fin d₁ → ℚ)
  t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)
  t_rat : IsRatSub (perBase B) t
  gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))
  grp : Set (GPt d₀ d₁ B)
  grp_eq : grp = zcl (expG d₀ d₁ B '' (tanOfV d₀ d₁ B gam U t : Set (Tan d₀ d₁ B)))
  grp_sub : IsSubgroupG grp
  grp_closed : IsZClosed grp
  lie : ∀ v : Tan d₀ d₁ B, (∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ grp) ↔ v ∈ tanOfV d₀ d₁ B gam U t
  htil : ∀ u : Tan d₀ d₁ B, expG d₀ d₁ B u ∈ grp →
    ∃ N : ℕ, 0 < N ∧ N • u ∈ (tanOfV d₀ d₁ B gam U t).toAddSubgroup ⊔ PerG d₀ d₁ B

/-- The projection to the additive coordinates `ℂ^{d₀}`. -/
def prA : Tan d₀ d₁ B →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.fst ℂ _ _

@[simp] theorem prA_apply (u : Tan d₀ d₁ B) : (prA : Tan d₀ d₁ B →ₗ[ℂ] _) u = u.1 := rfl

/-- `t₀ = dim pr_{G_a}(T′)`. -/
noncomputable def ex0 (T : Submodule ℂ (Tan d₀ d₁ B)) : ℕ := finrank ℂ (T.map prA)

/-- `t₂ = dim (T′ ∩ ker pr_{G_a} ∩ ker pr_{G_m})`. -/
noncomputable def ex2 (T : Submodule ℂ (Tan d₀ d₁ B)) : ℕ :=
  finrank ℂ ↥(T ⊓ (LinearMap.ker (prA : Tan d₀ d₁ B →ₗ[ℂ] _) ⊓ LinearMap.ker prB))

namespace ObstrDataGV

variable (O : ObstrDataGV d₀ d₁ B)

/-- The tangent space `T′ = Γ + U^⊥ + perTanId t`. -/
def tan : Submodule ℂ (Tan d₀ d₁ B) := tanOfV d₀ d₁ B O.gam O.U O.t

theorem expG_mem {u : Tan d₀ d₁ B} (hu : u ∈ O.tan) : expG d₀ d₁ B u ∈ O.grp := by
  simpa using (O.lie u).mpr hu 1

end ObstrDataGV

/-- **The multiplicity estimate on `G̃ = G_a^{d₀} × G_m^{d₁} × B₁^♮ × ⋯ × B_m^♮`, with a subspace `Kv` of
symmetries** (MEV's `multEstG` shape). If the order hypothesis is invariant under translation by `exp Kv`, the
obstruction contains `Kv`. Exponents: `t₀ = ex0 T′`, `t₁ = d₁ − dim U`, `t₂ = ex2 T′`. -/
def MultEstGV : Prop :=
  ∀ (d₀ d₁ m : ℕ) (B : Fin m → VBlock), ∃ C : ℕ,
    ∀ (W : Submodule ℂ (Tan d₀ d₁ B)) (S : Finset (GPt d₀ d₁ B))
      (P : MvPolynomial (Var d₀ d₁ B) ℂ) (T D₀ D₁ D₂ : ℕ) (Kv : Submodule ℂ (Tan d₀ d₁ B)),
      (0 : GPt d₀ d₁ B) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ StrongSix.M2.FLE ℂ blk (DfunB D₀ D₁ D₂) → P ∉ IGsem d₀ d₁ B →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sigB S (dimG d₀ d₁ B), OrdGtV W P (dimG d₀ d₁ B * T) σ) →
      (∀ v ∈ Kv, ∀ (y : GPt d₀ d₁ B) (n : ℕ), OrdGtV W P n y → OrdGtV W P n (y + expG d₀ d₁ B v)) →
      ∃ O : ObstrDataGV d₀ d₁ B, O.tan ≠ ⊤ ∧ Kv ≤ O.tan ∧
        ∀ F : Finset (GPt d₀ d₁ B), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ ex0 O.tan *
              D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ ex2 O.tan ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, ((B k).g + 1))

end LSG.MEBV
