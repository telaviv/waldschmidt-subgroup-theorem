/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement

/-!
# Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B`, `B ⊂ E₁ × ⋯ × E_m` an abelian subvariety (statement)

`Thm41Sub` is W88 Theorem 4.1 under (NR) for the group `G = G_a^{k₀} × G_m^{k₁} × B`, where `B` is
an arbitrary abelian subvariety of `E₁ × ⋯ × E_m`, given by its tangent space `t ⊂ ℂ^m`
(`IsAbelianTangent Ls t`). Everything is written in the *ambient* coordinates
`Tan k₀ k₁ m = ℂ^{k₀} × ℂ^{k₁} × ℂ^m` of `G_a^{k₀} × G_m^{k₁} × E₁ × ⋯ × E_m`:

* `T_G = tanB t = ℂ^{k₀} × ℂ^{k₁} × t`, and `V ≤ tanB t`, `dim V < dim G = k₀ + k₁ + dim t`;
* `Λ(G) = Λ(ambient) ∩ T_G` and `Ω(G) = Ω(ambient) ∩ T_G` (automatic, since `Y ⊂ V ⊂ T_G`):
  `Lam Ls`, `Per Ls` are used unchanged;
* the connected algebraic subgroups of `G` are the `SubgroupData` `H` with `H.t ≤ t`;
  `δ₂ = dim t − dim H.t`, `d₂ = dim t` (so `d₁ + 2d₂ − κ = k₁ + 2 dim t − κ`).

For `t = ⊤` this is exactly `LSG.W88.Theorem41Abelian` (`thm41SubAt_top`, in `K5dSub.lean`).
-/

open Module

namespace LSG.W88

variable {m : ℕ}

/-- The tangent space `ℂ^{k₀} × ℂ^{k₁} × t` of `G_a^{k₀} × G_m^{k₁} × B`. -/
def tanB (k0 k1 : ℕ) (t : Submodule ℂ (Fin m → ℂ)) : Submodule ℂ (Tan k0 k1 m) :=
  (⊤ : Submodule ℂ (Fin k0 → ℂ)).prod ((⊤ : Submodule ℂ (Fin k1 → ℂ)).prod t)

/-- `δ = codim_G G'` for `G' = H₀ × T_U × B'` inside `G = G_a^{k₀} × G_m^{k₁} × B`
(`δ₂ = dim t − dim H.t`). -/
noncomputable def SubgroupData.δB {k0 k1 : ℕ} {Ls : Fin m → PeriodPair}
    (H : SubgroupData (d0 := k0) (d1 := k1) Ls) (t : Submodule ℂ (Fin m → ℂ)) : ℕ :=
  H.δ0 + H.δ1 + (finrank ℂ t - finrank ℂ H.t)

/-- **W88 Theorem 4.1 under (NR) for `G_a^{k₀} × G_m^{k₁} × B`** (`T_B = t`), for given `k₀, k₁, Ls, t`. -/
def Thm41SubAt (k0 k1 : ℕ) (Ls : Fin m → PeriodPair) (t : Submodule ℂ (Fin m → ℂ)) : Prop :=
  ∀ (V W : Submodule ℂ (Tan k0 k1 m)) (Y : AddSubgroup (Tan k0 k1 m)),
    V ≤ tanB k0 k1 t → finrank ℂ V < k0 + k1 + finrank ℂ t → W ≤ V → RationalOverQbarTan W →
    Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ Lam Ls) →
    -- (NR)
    k1 + 2 * k0 + rk (Y ⊓ Per Ls) ≤ 2 * finrank ℂ V →
    ∃ H : SubgroupData (d0 := k0) (d1 := k1) Ls, H.t ≤ t ∧ H.δB t ≠ 0 ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δB t ∧
      (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) + H.δ1 +
          2 * (finrank ℂ t - finrank ℂ H.t) : ℕ) : ℤ) *
          ((k0 + k1 + finrank ℂ t : ℕ) - finrank ℂ V : ℤ) ≤
        ((H.δB t : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
          ((k1 + 2 * finrank ℂ t : ℕ) - rk (Y ⊓ Per Ls) : ℤ))

/-- **`Thm41Sub`**: Theorem 4.1 under (NR) for every `G_a^{k₀} × G_m^{k₁} × B`, `B` an abelian
subvariety of a product of elliptic curves with algebraic invariants. -/
def Thm41Sub : Prop :=
  ∀ (k0 k1 m : ℕ) (Ls : Fin m → PeriodPair),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) →
    ∀ t : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls t → Thm41SubAt k0 k1 Ls t

end LSG.W88
