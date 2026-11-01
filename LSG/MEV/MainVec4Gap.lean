import Mathlib
import LSG.MEV.MainVec4

/-!
# `MultEstVec` in the 4-block grading (STAGE5_MEV §10.3)

* **`multEstVec_blk4`**: `MultEstVec` for every `M` and all degrees, from `multEstG4` (with
  `Kv = K_M`, `TrailDeg` turning `P ∈ FLE blk (D₀, D₁, D₂)` into
  `P ∈ FLE (blk4 d₀) (D₀, D₂, D₁, D₂)`,
  `fle4_of_trail`). The exponents of `multEstG4` are exactly `O.t0` and `O.t2`.
* **`multEstVecGap`**: the remaining case `MultEstVecGap` of `MainVecLe.lean`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk Dfun)
open LSG.W88.Vec (vecIncl torIncl)
open StrongSix.M2 (FLE)

namespace LSG.MEV

noncomputable section

/-- **The multiplicity estimate for `G = G̃_r / K_M`, any `M`, all degrees** (4-block grading). -/
theorem multEstVec_blk4 : MultEstVec := by
  intro d₀ r d₁ m Ls M
  refine ⟨CstV4 d₀ r d₁ m, fun W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂
    hvan => ?_⟩
  classical
  set W' := W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap
  have hK : ∀ v ∈ kerK (d₀ := d₀) (d₁ := d₁) M, ∀ y n, OrdGt Ls W' P n y →
      OrdGt Ls W' P n (y + expGV Ls v) := by
    rintro _ ⟨u, rfl⟩ y n hy
    have hI : InvTr Ls (expGV Ls (vtr (d₁ := d₁) (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u)) u))
        P := fun g lam => hInv g lam u
    exact (ordGt_add_vtr hI W' n y).mpr hy
  have hPD4 := fle4_of_trail (r := r) hPD hTr
  obtain ⟨H, hH, hc, hKs, hprop, hineq⟩ := multEstG4 (d₀ := d₀) (r := r) Ls W' S P T D₀ D₁ D₂
    (kerK M) hS hPh hPD4 hPI hT hD₀ hD₁ hD₂ hvan hK
  set Tt := lieAlg Ls hH with hTt
  obtain ⟨S₀, hS₀, hU₀, -, -⟩ := exists_subgroupV hH hc
  let O : ObstrDataV d₀ r d₁ Ls M :=
    { S := S₀
      grp := H0 Ls hH
      grp_eq := by rw [hS₀]; rfl
      grp_sub := H0_isSubgroup hH
      grp_closed := isZClosed_H0 hH
      lie := fun v => by
        rw [hS₀, ← lieAlg_H0 hH hc, mem_lieAlg]
      ker_le := hS₀ ▸ hKs }
  have hOtan : O.tan = Tt := hS₀
  refine ⟨O, fun h => hprop (hOtan ▸ h), fun F hFS hFd => ?_⟩
  have h1 := hineq F hFS hFd
  have hℓ : finrank ℂ W' - finrank ℂ ↥(W' ⊓ lieAlgL Ls hH) =
      finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) := by
    rw [hOtan, LinearEquiv.finrank_map_eq, lieAlgL, finrank_inf_lieAlgL]
  have hex0 : ex0L (d₀ := d₀) (r := r) Tt = O.t0 := by
    rw [ObstrDataV.t0, hOtan]; rfl
  have hex2 : ex2L (d₀ := d₀) (r := r) Tt = O.t2 := by
    rw [ObstrDataV.t2, hOtan]; rfl
  have hex1 : ex1 Tt = d₁ - finrank ℚ O.S.U := by
    have h1' := lieAlg_comap_torIncl hH hc (isAbelianTangent_map_piZ hH hc)
    rw [← hTt, ← hU₀] at h1'
    have h2' : finrank ℂ (LSG.W88.torusLie S₀.U) + finrank ℚ S₀.U = d₁ :=
      LSG.ME.finrank_torusLie S₀.U
    have h3 : ex1 Tt = finrank ℂ (LSG.W88.torusLie S₀.U) := by
      rw [ex1, h1']
    rw [h3]
    change _ = d₁ - finrank ℚ S₀.U
    omega
  rw [hℓ, hex0, hex1, hex2] at h1
  exact h1

/-- **The remaining case of `MultEstVec`** (`M` not onto, `D₂ < D₀`). -/
theorem multEstVecGap : MultEstVecGap := by
  intro d₀ r d₁ m Ls M _hM
  obtain ⟨C, hC⟩ := multEstVec_blk4 d₀ r d₁ m Ls M
  exact ⟨C, fun W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂ _h20 hvan =>
    hC W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂ hvan⟩

end

end LSG.MEV
