/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.StmtG
import LSG.MEB.MainAux

/-!
# Auxiliary lemmas for the assembly of `MultEstGV` (M2.5 α; template `LSG.MEB.MainAux`)

The generic lemmas (`deg_le_of_hfun'`, `lower_deg`, `lin3`, `pow_self_mono`, `finrank_torusLie`) are MEB's,
used by full name.

* `prB_mem_torusLie`, `torIncl_mem_tanOfV`; **`finrank_tanOfV`**: `dim T′ = ex0 T′ + (d₁ − dim U) + ex2 T′` for
  `T′ = tanOfV Γ U t` (W88's projection exponents add up).
* `ex0_le`, `finrank_Tan`.
* `CstV`, **`final_arith_V`**: the final arithmetic, with the degree multiplier `L` (MEB: `L = 4`) and the
  block dimension `sg = Σ_k (g_k + 1)`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata HasData)

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

theorem finrank_Tan : finrank ℂ (Tan d₀ d₁ B) = dimG d₀ d₁ B := by
  simp [Tan, dimG, Module.finrank_prod, Module.finrank_pi_fintype, Finset.sum_add_distrib]
  ring

/-- The toric component of a vector of `tanOfV Γ U t` lies in `U^⊥`. -/
theorem prB_mem_torusLie {gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))}
    {U : Submodule ℚ (Fin d₁ → ℚ)} {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {v : Tan d₀ d₁ B}
    (hv : v ∈ tanOfV d₀ d₁ B gam U t) : v.2.1 ∈ LSG.W88.torusLie U := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, -, rfl⟩ := Submodule.mem_map.mp hy₁
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy₂
  obtain ⟨p, -, rfl⟩ := Submodule.mem_map.mp hz
  simpa [vecIncl, torIncl, g2Incl] using hb

theorem torIncl_mem_tanOfV (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ)))
    {U : Submodule ℚ (Fin d₁ → ℚ)} (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) {b : Fin d₁ → ℂ}
    (hb : b ∈ LSG.W88.torusLie U) : torIncl (d₀ := d₀) (B := B) b ∈ tanOfV d₀ d₁ B gam U t :=
  Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hb))

/-- **The exponents add up**: `dim T′ = ex0 T′ + (d₁ − dim U) + ex2 T′`. -/
theorem finrank_tanOfV (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ)))
    (U : Submodule ℚ (Fin d₁ → ℚ)) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    finrank ℂ (tanOfV d₀ d₁ B gam U t) =
      ex0 (tanOfV d₀ d₁ B gam U t) + (d₁ - finrank ℚ U) + ex2 (tanOfV d₀ d₁ B gam U t) := by
  classical
  set T := tanOfV d₀ d₁ B gam U t
  set K := T ⊓ LinearMap.ker (prA : Tan d₀ d₁ B →ₗ[ℂ] _)
  -- `dim T = dim prA T + dim (T ∩ ker prA)`
  have h1 := LinearMap.finrank_range_add_finrank_ker ((prA : Tan d₀ d₁ B →ₗ[ℂ] _).domRestrict T)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have hK1 : finrank ℂ ↥((LinearMap.ker (prA : Tan d₀ d₁ B →ₗ[ℂ] _)).comap T.subtype) =
      finrank ℂ K := StrongSix.M2.finrank_comap_subtype (K := ℂ) T _
  -- `dim K = dim prB K + dim (K ∩ ker prB)`
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((prB : Tan d₀ d₁ B →ₗ[ℂ] _).domRestrict K)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h2
  have hK2 : finrank ℂ ↥((LinearMap.ker (prB : Tan d₀ d₁ B →ₗ[ℂ] _)).comap K.subtype) =
      ex2 T := by
    rw [StrongSix.M2.finrank_comap_subtype, ex2, inf_assoc]
  -- `prB K = U^⊥`
  have hB : K.map (prB : Tan d₀ d₁ B →ₗ[ℂ] _) = LSG.W88.torusLie U := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact prB_mem_torusLie hv.1
    · intro b hb
      refine ⟨torIncl b, ⟨torIncl_mem_tanOfV gam t hb, ?_⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rfl
  have h3 := LSG.MEB.finrank_torusLie U
  rw [hB] at h2
  rw [hK1] at h1
  rw [hK2] at h2
  change finrank ℂ T = finrank ℂ (T.map prA) + _ + _
  omega

theorem ex0_le (T : Submodule ℂ (Tan d₀ d₁ B)) : ex0 T ≤ d₀ := by
  have := Submodule.finrank_le (T.map (prA : Tan d₀ d₁ B →ₗ[ℂ] _))
  rwa [Module.finrank_fin_fun] at this

/-- The constant of `MultEstGV`: `n = dim G̃`, `cL` the coset lower-bound constant, `cG` the Hilbert constant
`cB` of the sliced explicit ideal, `L` the degree multiplier. -/
def CstV (n d₀ d₁ cL cG L : ℕ) : ℕ :=
  n ^ n * d₀ ^ d₀ * d₁ ^ d₁ * cL * 2 ^ n * n.factorial * cG * L ^ n

/-- **The final arithmetic** (MEB's `final_arith_B` with `4` replaced by `L`). -/
theorem final_arith_V {n d₀ d₁ sg ℓ e t₀ t₁ t₂ T nF nR k D₀ D₁ D₂ κ cL cG L : ℕ}
    {deg0 degA degIG : ℤ} (hL : 1 ≤ L) (hn : n = d₀ + d₁ + sg)
    (hℓ : ℓ ≤ n) (he : e ≤ n) (hκ : κ ≤ d₀ ^ d₀ * d₁ ^ d₁)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (h0 : 0 ≤ deg0)
    (A1 : ((nR * (L * D₀) ^ t₀ * (L * D₁) ^ t₁ * (L * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0))
    (A2 : (((k + 1) ^ ℓ : ℕ) : ℤ) * deg0 ≤ degA) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ ((n.factorial * cG * (L * D₀) ^ d₀ * (L * D₁) ^ d₁ * (L * D₂) ^ sg : ℕ) : ℤ)) :
    T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤
      CstV n d₀ d₁ cL cG L * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg := by
  set X := (L * D₀) ^ t₀ * (L * D₁) ^ t₁ * (L * D₂) ^ t₂
  set Lℓ := ℓ ^ ℓ
  set P := (k + 1) ^ ℓ
  have hDX : D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ X := by
    simp only [X]
    gcongr <;> exact Nat.le_mul_of_pos_left _ hL
  have hfac : 1 ≤ e.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)
  have s1 : T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ Lℓ * P * (nR * X * e.factorial) := by
    calc T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ = T ^ ℓ * nF * (D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂) := by
          ring
      _ ≤ (Lℓ * P) * nR * (X * e.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul hT hF) (hDX.trans (Nat.le_mul_of_pos_right _ hfac))
      _ = Lℓ * P * (nR * X * e.factorial) := by ring
  have s2 : ((Lℓ * P * (nR * X * e.factorial) : ℕ) : ℤ) ≤
      (Lℓ : ℤ) * κ * cL * 2 ^ e * degIG := by
    have hA1 : ((nR * X * e.factorial : ℕ) : ℤ) ≤ ((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0) := by
      simpa [X, mul_assoc] using A1
    calc ((Lℓ * P * (nR * X * e.factorial) : ℕ) : ℤ)
        = (Lℓ : ℤ) * P * ((nR * X * e.factorial : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (Lℓ : ℤ) * P * (((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0)) := by gcongr
      _ = (Lℓ : ℤ) * κ * cL * 2 ^ e * ((P : ℤ) * deg0) := by push_cast; ring
      _ ≤ (Lℓ : ℤ) * κ * cL * 2 ^ e * degA :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast A2) (by positivity)
      _ ≤ (Lℓ : ℤ) * κ * cL * 2 ^ e * degIG := by gcongr
  have s3 : (Lℓ : ℤ) * κ * cL * 2 ^ e * degIG ≤
      ((CstV n d₀ d₁ cL cG L * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg : ℕ) : ℤ) := by
    have hLℓ : Lℓ ≤ n ^ n := LSG.MEB.pow_self_mono hℓ
    have h2e : 2 ^ e ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) he
    calc (Lℓ : ℤ) * κ * cL * 2 ^ e * degIG
        ≤ (Lℓ : ℤ) * κ * cL * 2 ^ e * ((n.factorial * cG * (L * D₀) ^ d₀ * (L * D₁) ^ d₁ *
            (L * D₂) ^ sg : ℕ) : ℤ) := by gcongr
      _ = (((Lℓ * κ * cL * 2 ^ e) * (n.factorial * cG * (L * D₀) ^ d₀ * (L * D₁) ^ d₁ *
            (L * D₂) ^ sg) : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((CstV n d₀ d₁ cL cG L * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          rw [mul_pow, mul_pow, mul_pow, CstV]
          have h4 : L ^ n = L ^ d₀ * L ^ d₁ * L ^ sg := by rw [hn, pow_add, pow_add]
          calc Lℓ * κ * cL * 2 ^ e * (n.factorial * cG * (L ^ d₀ * D₀ ^ d₀) *
                (L ^ d₁ * D₁ ^ d₁) * (L ^ sg * D₂ ^ sg))
              = (Lℓ * κ * 2 ^ e) * (cL * n.factorial * cG * (L ^ d₀ * L ^ d₁ * L ^ sg) *
                  D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg) := by ring
            _ ≤ (n ^ n * (d₀ ^ d₀ * d₁ ^ d₁) * 2 ^ n) * (cL * n.factorial * cG *
                  (L ^ d₀ * L ^ d₁ * L ^ sg) * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg) := by gcongr
            _ = _ := by rw [← h4]; ring
  exact_mod_cast (show ((T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ : ℕ) : ℤ) ≤ _ from
    (Nat.cast_le.mpr s1).trans (s2.trans s3))

end LSG.MEBV
