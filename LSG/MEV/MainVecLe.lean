import Mathlib
import LSG.MEV.MainVecPush

/-!
# `MultEstVec` for any `M` when `D₀ ≤ D₂` (STAGE5_MEV §10)

For a member `S` of the family of `G̃_r` let `j = dim trail(T̃′ ∩ ker prLead ∩ ker prB)` (`trail` =
the `r` trailing additive coordinates). Then (`exists_jV`, from `T̃′ = U^⊥ ⊕ tanV`, `tanV ⊆ ker prB`)
`dim prA T̃′ = t0 + j` and `t2 = dim (T̃′ ∩ ker prA ∩ ker prB) + j`, `j ≤ r`. So the 3-block estimate
`multEstG` gives the `MultEstVec` inequality up to the factor `(D₀ / D₂)^{r − j}`, which is `≤ 1` when
`D₀ ≤ D₂` (**`multEstVec_of_le : MultEstVecLe`**, any `M`). For onto `M`, `j = r`
(`multEstVec_of_surj`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk Dfun)
open LSG.W88.Vec (vecIncl torIncl)
open StrongSix.M2 (FLE)

namespace LSG.MEV

noncomputable section

variable {d₀ r d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- The `r` trailing additive coordinates. -/
def trailMap : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin r → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (Fin.natAdd d₀ : Fin r → Fin (d₀ + r))).comp
    (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))

/-- **The trailing defect `j`.** -/
theorem exists_jV (S : SubgroupPreV (d₀ := d₀ + r) (d₁ := d₁) Ls (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ j ≤ r,
      finrank ℂ (S.tan.map (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))) =
        finrank ℂ (S.tan.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m))) + j ∧
      finrank ℂ ↥(S.tan ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
        LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m)))) = ex2 S.tan + j := by
  classical
  set T := S.tan
  set V₁ := T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m)))
  set T₃ := T ⊓ (LinearMap.ker (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) ⊓
      LinearMap.ker prB)
  set j := finrank ℂ (V₁.map (trailMap (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)))
  have hj : j ≤ r := by
    have := Submodule.finrank_le (V₁.map (trailMap (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)))
    rwa [Module.finrank_fin_fun] at this
  refine ⟨j, hj, ?_, ?_⟩
  · -- `dim prA T = dim prLead T + j`
    set f := LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r))
    set U := T.map (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
    set Y := V₁.map (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
    have hUY : U ⊓ LinearMap.ker f = Y := by
      apply le_antisymm
      · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker] at hy
        have hx' := hx
        rw [show T = S.tan from rfl, SubgroupPreV.tan_eq] at hx'
        obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
        have hzT : z ∈ T := by
          rw [show T = S.tan from rfl, SubgroupPreV.tan_eq]; exact Submodule.mem_sup_right hz
        have ht0 : (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) t = 0 :=
          S.tor_le_ker_prA ht
        have hpz : (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) (t + z) =
            (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) z := by
          rw [map_add, ht0, zero_add]
        refine ⟨z, ⟨hzT, ?_, S.tanV_le_ker_prB hz⟩, hpz.symm⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        rw [hpz] at hy
        exact hy
      · rintro _ ⟨x, ⟨hxT, hxL, -⟩, rfl⟩
        refine ⟨⟨x, hxT, rfl⟩, ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker] at hxL ⊢
        exact hxL
    -- `dim Y = j`
    have hYj : finrank ℂ Y = j := by
      set g := LinearMap.funLeft ℂ ℂ (Fin.natAdd d₀ : Fin r → Fin (d₀ + r))
      have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict Y)
      have hker : LinearMap.ker (g.domRestrict Y) = ⊥ := by
        rw [eq_bot_iff]
        rintro ⟨y, hy⟩ hy0
        rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hy0
        have hyU : y ∈ U ⊓ LinearMap.ker f := hUY ▸ hy
        have hyf := hyU.2
        rw [SetLike.mem_coe, LinearMap.mem_ker] at hyf
        rw [Submodule.mem_bot, Subtype.ext_iff, Submodule.coe_zero]
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · exact congrFun hyf i
        · exact congrFun hy0 i
      rw [hker, finrank_bot, add_zero, LinearMap.range_domRestrict] at h
      have e : Y.map g = V₁.map (trailMap (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) := by
        rw [← Submodule.map_comp]; rfl
      rw [e] at h
      exact h.symm
    have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
      Submodule.map_comap_subtype, hUY, hYj] at h
    have e : U.map f = T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) := by
      rw [← Submodule.map_comp]; rfl
    rw [e] at h
    omega
  · -- `t2 = ex2 + j`
    have hle : T₃ ≤ V₁ := by
      rintro x ⟨hxT, hxA, hxB⟩
      refine ⟨hxT, ?_, hxB⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hxA ⊢
      funext i
      rw [prLead_apply]
      exact congrFun hxA (Fin.castAdd r i)
    have hkerg : LinearMap.ker ((trailMap (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)).domRestrict V₁) =
        T₃.comap V₁.subtype := by
      ext ⟨x, hx⟩
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
        Submodule.subtype_apply]
      obtain ⟨hxT, hxL, hxB⟩ := hx
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hxL
      constructor
      · intro h0
        refine ⟨hxT, ?_, hxB⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · exact congrFun hxL i
        · exact congrFun h0 i
      · rintro ⟨-, hxA, -⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker] at hxA
        funext i
        exact congrFun hxA (Fin.natAdd d₀ i)
    have h := LinearMap.finrank_range_add_finrank_ker
      ((trailMap (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)).domRestrict V₁)
    rw [LinearMap.range_domRestrict, hkerg, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
    show finrank ℂ ↥V₁ = finrank ℂ ↥T₃ + j
    exact h.symm.trans (Nat.add_comm _ _)

/-- **`MultEstVec` for `D₀ ≤ D₂`** (any `M`): the same statement with the extra hypothesis
`D₀ ≤ D₂`. -/
def MultEstVecLe : Prop :=
  ∀ (d₀ r d₁ m : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ), ∃ C : ℕ,
    ∀ (W : Submodule ℂ (TanG (d₀ + r) d₁ m)) (S : Finset (GPtV (d₀ + r) d₁ Ls))
      (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPtV (d₀ + r) d₁ Ls) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → TrailDeg (d₀ := d₀) D₂ P → InvarK Ls M P →
      P ∉ IG (d₀ := d₀ + r) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ → D₀ ≤ D₂ →
      (∀ σ ∈ sig S (d₀ + r + d₁ + 2 * m),
        OrdGt Ls (W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap) P
          ((d₀ + r + d₁ + 2 * m) * T) σ) →
      ∃ O : ObstrDataV d₀ r d₁ Ls M, O.Proper ∧
        ∀ F : Finset (GPtV (d₀ + r) d₁ Ls), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
              D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ O.t2 ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r)

/-- **The multiplicity estimate for `G = G̃_r / K_M`, any `M`, when `D₀ ≤ D₂`.** -/
theorem multEstVec_of_le : MultEstVecLe := by
  intro d₀ r d₁ m Ls M
  refine ⟨CstV (d₀ + r) d₁ m, fun W S P T D₀ D₁ D₂ hS hPh hPD _hTr hInv hPI hT hD₀ hD₁ hD₂
    hD02 hvan => ?_⟩
  classical
  set W' := W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap
  have hK : ∀ v ∈ kerK (d₀ := d₀) (d₁ := d₁) M, ∀ y n, OrdGt Ls W' P n y →
      OrdGt Ls W' P n (y + expGV Ls v) := by
    rintro _ ⟨u, rfl⟩ y n hy
    have hI : InvTr Ls (expGV Ls (vtr (d₁ := d₁) (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u)) u))
        P := fun g lam => hInv g lam u
    exact (ordGt_add_vtr hI W' n y).mpr hy
  obtain ⟨H, hH, hc, hKs, hprop, hineq⟩ := multEstG (d₀ := d₀ + r) Ls W' S P T D₀ D₁ D₂
    (kerK M) hS hPh hPD hPI hT hD₀ hD₁ hD₂ hvan hK
  set Tt := lieAlg Ls hH with hTt
  obtain ⟨S₀, hS₀, hU₀, -, hgam₀⟩ := exists_subgroupV hH hc
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
  obtain ⟨j, hjr, hj0, hj2⟩ := exists_jV S₀
  have hℓ : finrank ℂ W' - finrank ℂ ↥(W' ⊓ lieAlgL Ls hH) =
      finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) := by
    rw [hOtan, LinearEquiv.finrank_map_eq, lieAlgL, finrank_inf_lieAlgL]
  have hex0 : ex0 Tt = O.t0 + j := by
    have hA := S₀.map_prA_tan
    rw [hS₀, hgam₀] at hA
    rw [ex0, ← hA]
    rw [hS₀] at hj0
    rw [hj0, ObstrDataV.t0, hOtan]
  have hex1 : ex1 Tt = d₁ - finrank ℚ O.S.U := by
    have h1' := lieAlg_comap_torIncl hH hc (isAbelianTangent_map_piZ hH hc)
    rw [← hTt, ← hU₀] at h1'
    have h2' : finrank ℂ (LSG.W88.torusLie S₀.U) + finrank ℚ S₀.U = d₁ :=
      LSG.ME.finrank_torusLie S₀.U
    have h3 : ex1 Tt = finrank ℂ (LSG.W88.torusLie S₀.U) := by
      rw [ex1, h1']
    rw [h3]
    show _ = d₁ - finrank ℚ S₀.U
    omega
  have hex2 : O.t2 = ex2 Tt + j := by
    rw [ObstrDataV.t2, hOtan]
    rw [hS₀] at hj2
    exact hj2
  rw [hℓ, hex0, hex1] at h1
  rw [hex2]
  set X := T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
    D₁ ^ (d₁ - finrank ℚ O.S.U) with hX
  have hD0j : 0 < D₀ ^ j := pow_pos (by omega) j
  have hrj : D₀ ^ (r - j) ≤ D₂ ^ (r - j) := Nat.pow_le_pow_left hD02 _
  refine Nat.le_of_mul_le_mul_right ?_ hD0j
  calc X * D₂ ^ (ex2 Tt + j) * D₀ ^ j
      = (T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ (O.t0 + j) *
          D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ ex2 Tt) * D₂ ^ j := by rw [hX]; ring
    _ ≤ (CstV (d₀ + r) d₁ m * D₀ ^ (d₀ + r) * D₁ ^ d₁ * D₂ ^ (2 * m)) * D₂ ^ j :=
        Nat.mul_le_mul_right _ h1
    _ = (CstV (d₀ + r) d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) * D₂ ^ j * D₀ ^ j) *
          D₀ ^ (r - j) := by
        rw [show d₀ + r = d₀ + j + (r - j) by omega]; ring
    _ ≤ (CstV (d₀ + r) d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) * D₂ ^ j * D₀ ^ j) *
          D₂ ^ (r - j) := Nat.mul_le_mul_left _ hrj
    _ = CstV (d₀ + r) d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) * D₀ ^ j := by
        rw [show 2 * m + r = 2 * m + j + (r - j) by omega]; ring

/-! ### The remaining case -/

/-- **The remaining case of `MultEstVec`**: `M` not onto and `D₂ < D₀`. (Needs a second additive
block in the slice/Hilbert/Wüstholz layers, STAGE5_MEV §10.1.) -/
def MultEstVecGap : Prop :=
  ∀ (d₀ r d₁ m : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    ¬ Function.Surjective M.mulVec → ∃ C : ℕ,
    ∀ (W : Submodule ℂ (TanG (d₀ + r) d₁ m)) (S : Finset (GPtV (d₀ + r) d₁ Ls))
      (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPtV (d₀ + r) d₁ Ls) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → TrailDeg (d₀ := d₀) D₂ P → InvarK Ls M P →
      P ∉ IG (d₀ := d₀ + r) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ → D₂ < D₀ →
      (∀ σ ∈ sig S (d₀ + r + d₁ + 2 * m),
        OrdGt Ls (W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap) P
          ((d₀ + r + d₁ + 2 * m) * T) σ) →
      ∃ O : ObstrDataV d₀ r d₁ Ls M, O.Proper ∧
        ∀ F : Finset (GPtV (d₀ + r) d₁ Ls), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
              D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ O.t2 ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r)

/-- **`MultEstVec` from the remaining case.** -/
theorem multEstVec_of_gap (hgap : MultEstVecGap) : MultEstVec := by
  intro d₀ r d₁ m Ls M
  by_cases hM : Function.Surjective M.mulVec
  · exact multEstVec_of_surj d₀ r d₁ m Ls M hM
  obtain ⟨C₁, hC₁⟩ := hgap d₀ r d₁ m Ls M hM
  obtain ⟨C₂, hC₂⟩ := multEstVec_of_le d₀ r d₁ m Ls M
  refine ⟨C₁ + C₂, fun W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂ hvan => ?_⟩
  have hmono : ∀ {C x : ℕ}, C ≤ C₁ + C₂ →
      C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) ≤ (C₁ + C₂) * D₀ ^ d₀ * D₁ ^ d₁ *
        D₂ ^ (2 * m + r) := fun h => by gcongr
  by_cases h02 : D₀ ≤ D₂
  · obtain ⟨O, hO, hF⟩ := hC₂ W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂ h02 hvan
    exact ⟨O, hO, fun F hFS hFd => (hF F hFS hFd).trans (hmono (x := 0) (by omega))⟩
  · obtain ⟨O, hO, hF⟩ := hC₁ W S P T D₀ D₁ D₂ hS hPh hPD hTr hInv hPI hT hD₀ hD₁ hD₂
      (by omega) hvan
    exact ⟨O, hO, fun F hFS hFd => (hF F hFS hFd).trans (hmono (x := 0) (by omega))⟩

end

end LSG.MEV
