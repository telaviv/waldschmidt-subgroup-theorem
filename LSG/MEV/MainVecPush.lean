import Mathlib
import LSG.MEV.MainVec
import LSG.MEV.MultEstStmtV

/-!
# `MultEstVec` for onto `M` (the push-out reduction, STAGE5_MEV §4, §10)

`G = G̃_r / K_M` (`MultEstStmtV.lean`). For `M` onto (`Function.Surjective M.mulVec`, e.g. `r = 0`):

* `K_M`-invariance of `P` (`InvarK`) makes the formal order invariant under `exp(K_M)`
  (`ordGt_add_vtr`), so `multEstG` with `Kv = K_M` gives an obstruction `H` with `K_M ⊆ lieAlg H`;
* the obstruction datum: `ObstrDataV` from `exists_subgroupV` (`grp = H⁰`);
* the exponents: with `K_M ⊆ T̃′` and `M` onto, `dim prA T̃′ = t0 + r` (`finrank_map_prA_eq`) and
  `t2 = dim (T̃′ ∩ ker prA ∩ ker prB) + r` (`finrank_t2_eq`), `t₁ = d₁ − dim U`
  (`lieAlg_comap_torIncl`), and `ℓ` is unchanged by `toLie` (`finrank_inf_lieAlgL`);
* **`multEstVec_of_surj : MultEstVecSurj`**: `MultEstVec` with the extra hypothesis
  `Function.Surjective M.mulVec`, constant `C = CstV (d₀ + r) d₁ m`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk Dfun)
open LSG.W88.Vec (vecIncl torIncl)
open StrongSix.M2 (FLE)

namespace LSG.MEV

noncomputable section

variable {d₀ r d₁ m : ℕ}

/-! ### Linear algebra of the exponents -/

theorem kvec_apply (M : Matrix (Fin r) (Fin m) ℂ) (u : Fin m → ℂ) :
    kvec (d₀ := d₀) (d₁ := d₁) M u = (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u), 0, 0, u) := rfl

theorem prA_kvec (M : Matrix (Fin r) (Fin m) ℂ) (u : Fin m → ℂ) :
    (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) (kvec M u) =
      Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u) := rfl

theorem finrank_ker_funLeft_castAdd :
    finrank ℂ ↥(LinearMap.ker (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r)))) =
      r := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r)))
  have hs : LinearMap.range (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r))) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _
      (Fin.castAdd_injective d₀ r))
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

/-- **`dim prA T̃′ = t0 + r`** for `K_M ⊆ T̃′`, `M` onto. -/
theorem finrank_map_prA_eq {M : Matrix (Fin r) (Fin m) ℂ} (hM : Function.Surjective M.mulVec)
    {T : Submodule ℂ (TanG (d₀ + r) d₁ m)} (hK : kerK (d₀ := d₀) (d₁ := d₁) M ≤ T) :
    finrank ℂ (T.map (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))) =
      finrank ℂ (T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m))) + r := by
  classical
  set f := LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r))
  set U := T.map (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
  have hker : LinearMap.ker f ≤ U := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨u, hu⟩ := hM (-(fun i => x (Fin.natAdd d₀ i)))
    refine ⟨kvec M u, hK ⟨u, rfl⟩, ?_⟩
    rw [prA_kvec, hu, neg_neg]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have := congrFun hx i
      simp only [f, LinearMap.funLeft_apply, Pi.zero_apply] at this
      simp [this]
    · simp
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hker).finrank_eq, finrank_ker_funLeft_castAdd] at h
  have e : U.map f = T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h
  omega

/-- **`t2 = dim (T̃′ ∩ ker prA ∩ ker prB) + r`** for `K_M ⊆ T̃′`, `M` onto. -/
theorem finrank_t2_eq {M : Matrix (Fin r) (Fin m) ℂ} (hM : Function.Surjective M.mulVec)
    {T : Submodule ℂ (TanG (d₀ + r) d₁ m)} (hK : kerK (d₀ := d₀) (d₁ := d₁) M ≤ T) :
    finrank ℂ ↥(T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m)))) =
      ex2 T + r := by
  classical
  set T₂ := T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m)))
  set T₃ := T ⊓ (LinearMap.ker (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) ⊓
      LinearMap.ker prB)
  set g := (LinearMap.funLeft ℂ ℂ (Fin.natAdd d₀ : Fin r → Fin (d₀ + r))).comp
    (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
  have hkvec : ∀ u, kvec (d₀ := d₀) (d₁ := d₁) M u ∈ T₂ := fun u => by
    refine ⟨hK ⟨u, rfl⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      simp [prLead, kvec_apply]
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      rfl
  have hle : T₃ ≤ T₂ := by
    rintro x ⟨hxT, hxA, hxB⟩
    refine ⟨hxT, ?_, hxB⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hxA ⊢
    funext i
    rw [prLead_apply]
    exact congrFun hxA (Fin.castAdd r i)
  have hrange : LinearMap.range (g.domRestrict T₂) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨u, hu⟩ := hM (-b)
    refine ⟨⟨kvec M u, hkvec u⟩, ?_⟩
    funext i
    show Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u) (Fin.natAdd d₀ i) = b i
    simp [hu]
  have hkerg : LinearMap.ker (g.domRestrict T₂) = T₃.comap T₂.subtype := by
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
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict T₂)
  rw [hrange, finrank_top, Module.finrank_fin_fun, hkerg,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
  show finrank ℂ ↥T₂ = finrank ℂ ↥T₃ + r
  exact h.symm.trans (Nat.add_comm _ _)

/-- `ℓ` in the two coordinate systems. -/
theorem finrank_inf_lieAlgL (W T : Submodule ℂ (TanG d₀ d₁ m)) :
    finrank ℂ ↥(W.map (toLie : TanG d₀ d₁ m ≃ₗ[ℂ] LieV ℂ d₀ d₁ m).toLinearMap ⊓ T.comap toTan) =
      finrank ℂ ↥(W ⊓ T) := by
  have e : W.map (toLie : TanG d₀ d₁ m ≃ₗ[ℂ] LieV ℂ d₀ d₁ m).toLinearMap ⊓ T.comap toTan =
      (W ⊓ T).map (toLie : TanG d₀ d₁ m ≃ₗ[ℂ] LieV ℂ d₀ d₁ m).toLinearMap := by
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_comap]
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv, Submodule.mem_inf]
    rfl
  rw [e, LinearEquiv.finrank_map_eq]

/-! ### The statement for onto `M` and its proof -/

/-- **`MultEstVec` for onto `M`** (the same statement with the extra hypothesis
`Function.Surjective M.mulVec`; it covers `r = 0`). -/
def MultEstVecSurj : Prop :=
  ∀ (d₀ r d₁ m : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    Function.Surjective M.mulVec → ∃ C : ℕ,
    ∀ (W : Submodule ℂ (TanG (d₀ + r) d₁ m)) (S : Finset (GPtV (d₀ + r) d₁ Ls))
      (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPtV (d₀ + r) d₁ Ls) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → TrailDeg (d₀ := d₀) D₂ P → InvarK Ls M P →
      P ∉ IG (d₀ := d₀ + r) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sig S (d₀ + r + d₁ + 2 * m),
        OrdGt Ls (W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap) P
          ((d₀ + r + d₁ + 2 * m) * T) σ) →
      ∃ O : ObstrDataV d₀ r d₁ Ls M, O.Proper ∧
        ∀ F : Finset (GPtV (d₀ + r) d₁ Ls), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
              D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ O.t2 ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r)

/-- **The multiplicity estimate for `G = G̃_r / K_M`, `M` onto.** -/
theorem multEstVec_of_surj : MultEstVecSurj := by
  intro d₀ r d₁ m Ls M hM
  refine ⟨CstV (d₀ + r) d₁ m, fun W S P T D₀ D₁ D₂ hS hPh hPD _hTr hInv hPI hT hD₀ hD₁ hD₂
    hvan => ?_⟩
  classical
  set W' := W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap
  -- the formal order is `K_M`-invariant
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
  -- the obstruction datum
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
  -- the exponents
  have hℓ : finrank ℂ W' - finrank ℂ ↥(W' ⊓ lieAlgL Ls hH) =
      finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) := by
    rw [hOtan, LinearEquiv.finrank_map_eq, lieAlgL, finrank_inf_lieAlgL]
  have hex0 : ex0 Tt = O.t0 + r := by
    have hA := S₀.map_prA_tan
    rw [hS₀, hgam₀] at hA
    rw [ex0, ← hA, finrank_map_prA_eq hM hKs, ObstrDataV.t0, hOtan]
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
  have hex2 : O.t2 = ex2 Tt + r := by
    rw [ObstrDataV.t2, hOtan]
    exact finrank_t2_eq hM hKs
  rw [hℓ, hex0, hex1] at h1
  rw [hex2]
  -- cancel `D₀^r`
  have hD0r : 0 < D₀ ^ r := pow_pos (by omega) r
  refine Nat.le_of_mul_le_mul_right ?_ hD0r
  calc T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
          D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ (ex2 Tt + r) * D₀ ^ r
      = (T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ (O.t0 + r) *
          D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ ex2 Tt) * D₂ ^ r := by ring
    _ ≤ (CstV (d₀ + r) d₁ m * D₀ ^ (d₀ + r) * D₁ ^ d₁ * D₂ ^ (2 * m)) * D₂ ^ r :=
        Nat.mul_le_mul_right _ h1
    _ = CstV (d₀ + r) d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) * D₀ ^ r := by ring

end

end LSG.MEV
