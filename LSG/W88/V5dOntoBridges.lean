/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOntoMain
import LSG.W88.V5dMXGcm
import LSG.W88.V5dMGnK
import LSG.W88.V5dNat

/-!
# The four lean_mstar vector-extension bridges, unconditionally

The bridges `thm11KappaMXG_of`, `thm11KappaMGn_of`, `thm11KappaMGnK_of`, `thm11KappaNat_of`
(`V5dMXGcm.lean`, `V5dMGn.lean`, `V5dMGnK.lean`, `V5dNat.lean`) use their hypothesis
`h : Theorem41VecLA` only through `hyperplaneKappaVec_of h`. Their proofs are repeated here verbatim
with `hyperplaneKappaVec_uncond` (`V5dOntoMain.lean`) in its place:

* **`thm11KappaMXG_uncond : MStarCopy.Thm11KappaMXG`**;
* **`thm11KappaMGn_uncond (L) : MStarCopy.Thm11KappaMGn L`**;
* **`thm11KappaMGnK_uncond (L) : MStarCopy.Thm11KappaMGnK L`**;
* **`thm11KappaNat_uncond : MStarCopy.Nat.Thm11KappaNat`**.
-/

namespace LSG.W88.V5d

section MX

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM
open LSG.W88.Vec LSG.W88.MStarCopy

/-- **`Thm11KappaMXG` from the CM inputs, unconditionally** (see the module docstring). -/
theorem thm11KappaMXG_of_cm_uncond
    (hLA : ∀ r, LiftAlg (mxLs r)) (hPT : ∀ r, PerTanRat (mxLs r))
    (hΛ : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      ∃ Λs : AddSubgroup (TanV 1 0 (mxN r + mxN r) 1), (∀ x ∈ Λs, x ∈ LamV (mxLs r) (mxM b)) ∧
        ∀ g ∈ lamGenX b, (mxIota r).symm g ∈ Λs)
    (hper : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      perXG b ≤ (OmV 1 0 (mxLs r) (mxM b)).map ((mxIota r).toLinearMap.restrictScalars ℚ))
    (hsub : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      ∀ H : SubgroupDataV (d0 := 1) (d1 := 0) (mxLs r) (mxM b), H.tan ≠ ⊥ →
        (gmXG b).sub (H.tan.map (mxIota r).toLinearMap)) :
    MStarCopy.Thm11KappaMXG := by
  intro hg₂ hg₃ hg₂' hg₃' r b hb
  obtain ⟨Λs, hΛs, hgen⟩ := hΛ r b hb
  have hLs : ∀ j, IsAlgebraic ℚ (mxLs r j).g₂ ∧ IsAlgebraic ℚ (mxLs r j).g₃ := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [mxLs, Fin.append_left]; exact ⟨hg₂, hg₃⟩
    · simp only [mxLs, Fin.append_right]; exact ⟨hg₂', hg₃'⟩
  have hM : AlgMat (mxM b) := by
    intro i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [mxM, Fin.append_left]; exact theta_alg hb.alg _
    · simp only [mxM, Fin.append_right]; exact theta_alg hb.alg _
  refine hyperplaneKappa_of_iso hyperplaneKappaVec_uncond hLs hM le_rfl (hLA r) (hPT r) (gmXG b)
    (mxIota r) ?_ Λs hΛs ?_ (hper r b hb) rfl ?_ (hsub r b hb)
  · -- (i) algebraic vectors
    intro v hv
    rw [mxIota_symm_apply]
    refine ⟨fun _ => hv.1, fun i => i.elim0, fun k => ?_, fun _ => hv.2.2.2⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · change IsAlgebraic ℚ (Fin.append (fun i => v.2.1 ((mxE r).symm i))
        (fun i => v.2.2.1 ((mxE r).symm i)) (Fin.castAdd (mxN r) i))
      rw [Fin.append_left]; exact hv.2.1 _
    · change IsAlgebraic ℚ (Fin.append (fun i => v.2.1 ((mxE r).symm i))
        (fun i => v.2.2.1 ((mxE r).symm i)) (Fin.natAdd (mxN r) i))
      rw [Fin.append_right]; exact hv.2.2.1 _
  · -- (ii) common denominators
    intro y hy
    have hcl : y ∈ Submodule.span ℚ ((AddSubgroup.closure (lamGenX b) : AddSubgroup (TXG r)) :
        Set (TXG r)) := by
      rw [K11.span_closure_eq]; exact hy
    obtain ⟨N, hN, hNy⟩ := K11.exists_nsmul_mem_of_mem_span _ hcl
    refine ⟨N, hN, ?_⟩
    rw [← map_nsmul]
    have hle : AddSubgroup.closure (lamGenX b) ≤
        Λs.comap (mxIota r).symm.toLinearMap.toAddMonoidHom :=
      (AddSubgroup.closure_le _).mpr fun g hg => hgen g hg
    exact hle hNy
  · -- (iv) `d₂ = 2n + 1 = m + r`
    change 2 * Fintype.card (Fin r × Fin 2) + 1 =
      Fintype.card (Fin r × Fin 2) + Fintype.card (Fin r × Fin 2) + 1
    omega

/-- **Theorem MX's hypothesis `Thm11KappaMXG` unconditionally**, with the five CM inputs of
`thm11KappaMXG_of_cm` discharged. -/
theorem thm11KappaMXG_uncond : MStarCopy.Thm11KappaMXG := by
  intro hg₂ hg₃ hg₂' hg₃'
  have hLs : ∀ r, ∀ j, IsAlgebraic ℚ (mxLs r j).g₂ ∧ IsAlgebraic ℚ (mxLs r j).g₃ := by
    intro r j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [mxLs, Fin.append_left]; exact ⟨hg₂, hg₃⟩
    · simp only [mxLs, Fin.append_right]; exact ⟨hg₂', hg₃'⟩
  exact thm11KappaMXG_of_cm_uncond (liftAlg_mx hg₂ hg₃ hg₂' hg₃') perTanRat_mx
    (fun r b hb => ⟨lamVSub (mxLs r) (mxM b) (hLs r) (mxM_alg b hb), fun _ hx => hx,
      lamGen_mem b hb⟩)
    (fun _ b _ => perXG_le b) (fun _ b hb H hH => sub_mx b hb H hH) hg₂ hg₃ hg₂' hg₃'

end MX

section MGn

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM
open LSG.W88.Vec LSG.W88.MStarCopy

/-- **Theorem MG♮'s hypothesis unconditionally**, for every CM lattice. -/
theorem thm11KappaMGn_uncond (L : CMLattice) : MStarCopy.Thm11KappaMGn L := by
  intro hκ hg₂ hg₃ r b hb
  have hd := CMLat.cmD L hκ
  have hLs : ∀ j, IsAlgebraic ℚ (mgLs L r j).g₂ ∧ IsAlgebraic ℚ (mgLs L r j).g₃ :=
    fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat (mgM b) := fun _ k => hb.alg k
  refine hyperplaneKappa_of_iso hyperplaneKappaVec_uncond hLs hM le_rfl (liftAlg_block hg₂ hg₃ hd)
    (perTanRat_block hd) (gmMGn L b) (mgIota L b hb) (mg_alg L b hb)
    (lamVSub (mgLs L r) (mgM b) hLs hM) (fun _ hx => hx)
    (lam_nsmul L b hb _ (lamGen_mem_MGn L b hb hκ)) (per_le L b hb hκ) rfl
    (finrank_Qn L b hb) ?_
  intro H _
  refine ⟨(K11.annQ H.U).map (torLQ r),
    H.gam.map (gG L b) ⊔ (perTan (mgLs L r) (mgM b) H.t).map (gA L b),
    ?_, by rw [iota_tan, torus_eq]⟩
  by_cases hΓ : H.gam = ⊥
  · by_cases ht : H.t = ⊥
    · left; rw [hΓ, ht, perTan_bot]; simp
    · right
      obtain ⟨c, hc, -, hmem⟩ := abel_ne L b hb hκ H ht
      exact ⟨_, Submodule.mem_sup_right hmem, hc⟩
  · right
    obtain ⟨s, hs, -, hmem⟩ := gam_ne L b H hΓ
    exact ⟨_, Submodule.mem_sup_left hmem, hs⟩

/-- **The `K`-form hypothesis of Theorem MG♮ unconditionally**, for every CM lattice. -/
theorem thm11KappaMGnK_uncond (L : CMLattice) : MStarCopy.Thm11KappaMGnK L := by
  intro hκ hg₂ hg₃ r b hb
  have hd := CMLat.cmD L hκ
  have hLs : ∀ j, IsAlgebraic ℚ (mgLs L r j).g₂ ∧ IsAlgebraic ℚ (mgLs L r j).g₃ :=
    fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat (mgM b) := fun _ k => hb.alg k
  have hgen : ∀ g ∈ lamMGnK L b, (mgIota L b hb).symm g ∈ lamVSub (mgLs L r) (mgM b) hLs hM := by
    rintro g ((⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨i, u, w, huw, rfl⟩)
    · exact tor_mem_lam L b hb hx (torL_symm_single1 j x)
    · exact tor_mem_lam L b hb hx (torL_symm_single2 j x)
    · exact qv_log_mem L b hb hκ hg₂ hg₃ i huw
  refine hyperplaneKappa_of_iso hyperplaneKappaVec_uncond hLs hM le_rfl (liftAlg_block hg₂ hg₃ hd)
    (perTanRat_block hd) (gmMGnK L b) (mgIota L b hb) (mg_alg L b hb)
    (lamVSub (mgLs L r) (mgM b) hLs hM) (fun _ hx => hx) (lam_nsmul L b hb _ hgen)
    (per_le L b hb hκ) rfl (finrank_Qn L b hb) ?_
  intro H hH
  right
  rw [iota_tan]
  have halg0 : algQn L b 0 := ⟨⟨0, fun _ => isAlgebraic_zero, rfl⟩, isAlgebraic_zero⟩
  have hfib : ∀ s : ℂ, s ≠ 0 → IsAlgebraic ℚ s →
      ((0 : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), s) ∈
        H.gam.map (gG L b) ⊔ (perTan (mgLs L r) (mgM b) H.t).map (gA L b) →
      ∃ x ∈ ((torusLie H.U).map (torL r).toLinearMap).prod
          (H.gam.map (gG L b) ⊔ (perTan (mgLs L r) (mgM b) H.t).map (gA L b)),
        algF (algQn L b) x ∧ PsiG (theta L.α b) 0 (LinearMap.snd ℂ _ ℂ) x ≠ 0 := by
    intro s hs hsa hmem
    refine ⟨(0, (0, s)), ⟨zero_mem _, hmem⟩, ⟨fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero,
      ⟨0, fun _ => isAlgebraic_zero, rfl⟩, hsa⟩, ?_⟩
    rw [psiG_apply]
    intro h0
    apply hs
    have := congrArg Prod.snd h0
    simpa using this
  by_cases hT : torusLie H.U = ⊥
  · by_cases hΓ : H.gam = ⊥
    · by_cases ht : H.t = ⊥
      · exfalso; apply hH
        rw [SubgroupDataV.tan, hT, hΓ, ht, perTan_bot]; simp
      · obtain ⟨c, hc, hca, hmem⟩ := abel_ne L b hb hκ H ht
        exact hfib c hc hca (Submodule.mem_sup_right hmem)
    · obtain ⟨s, hs, hsa, hmem⟩ := gam_ne L b H hΓ
      exact hfib s hs hsa (Submodule.mem_sup_left hmem)
  · obtain ⟨q, hq, hqT⟩ := torus_ne H.U hT
    refine ⟨(torL r (K11.castL _ q), 0), ⟨Submodule.mem_map_of_mem hqT, zero_mem _⟩, ?_, ?_⟩
    · have hr : ∀ i, IsAlgebraic ℚ (K11.castL _ q i) := fun i => isAlgebraic_algebraMap (q i)
      exact ⟨fun j => hr _, fun j => hr _, halg0⟩
    · rw [psiG_apply]
      intro h0
      rcases dot_ne L b hb hq with h1 | h1
      · exact h1 (by simpa using congrArg Prod.fst h0)
      · exact h1 (by simpa using congrArg Prod.snd h0)

end MGn

section Nat

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM
open LSG.W88.Vec LSG.W88.MStarCopy LSG.W88.MStarCopy.Nat

/-- **Theorem 1(a)'s hypothesis unconditionally.** -/
theorem thm11KappaNat_uncond : MStarCopy.Nat.Thm11KappaNat := by
  intro hg₂ hg₃
  have hLs : ∀ j, IsAlgebraic ℚ (nLs j).g₂ ∧ IsAlgebraic ℚ (nLs j).g₃ := fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat nM := by
    intro i k; fin_cases k
    · simpa [nM] using isAlgebraic_one
    · simpa [nM] using isAlgebraic_r2
  set Λs := lamVSub (d0 := 0) (d1 := 8) nLs nM hLs hM
  refine hyperplaneKappa_of_iso hyperplaneKappaVec_uncond hLs hM le_rfl
    (liftAlg_block hg₂ hg₃ cmLem) (perTanRat_block cmLem) gmQ natIota ?_ Λs (fun _ hx => hx) ?_ ?_
    rfl rfl ?_
  · -- algebraic vectors
    intro v hv
    rw [natIota_symm_apply]
    have hr := isAlgebraic_r2
    have h2 : IsAlgebraic ℚ (2 : ℂ) := mem_Qbar.mp (ofNat_mem Qbar 2)
    refine ⟨fun i => i.elim0, hv.1, fun k => ?_, fun _ => hv.2 2⟩
    fin_cases k
    · exact ((hv.2 0).add (hv.2 1)).mul h2.inv
    · exact ((hv.2 0).sub (hv.2 1)).mul (h2.mul hr).inv
  · -- logarithms
    rintro y ⟨hy1, ⟨⟨m, n⟩, hmn⟩⟩
    refine ⟨1, one_pos, ?_⟩
    rw [one_smul]
    have : y = (y.1, (0 : Fin 3 → ℂ)) + ((0 : Fin 8 → ℂ), perImg m n) := by
      simp only at hmn
      rw [hmn]; simp
    rw [this, map_add]
    exact Λs.add_mem (natTor_lam hy1) (perV_le_lamV (perImg_mem m n))
  · -- periods
    have key : ∀ x, natIota.symm x ∈ PerV (d0 := 0) (d1 := 8) nLs nM →
        x ∈ (OmV 0 8 nLs nM).map (natIota.toLinearMap.restrictScalars ℚ) := by
      intro x hx
      refine ⟨natIota.symm x, Submodule.subset_span hx, ?_⟩
      simp
    change Submodule.span ℚ _ ≤ _
    rw [Submodule.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨q, ⟨⟨m, n⟩, rfl⟩, rfl⟩) <;> apply key
    · exact natTor_per j
    · exact perImg_mem m n
  · -- subgroups
    intro H _
    refine ⟨K11.annQ H.U, H.gam.map gN ⊔ (perTan nLs nM H.t).map aN, ?_, iota_tanN H⟩
    have hfib : ∀ c : ℂ, c ≠ 0 → ![0, 0, c] ∈ H.gam.map gN ⊔ (perTan nLs nM H.t).map aN →
        Pi.single 2 1 ∈ H.gam.map gN ⊔ (perTan nLs nM H.t).map aN := by
      intro c hc hmem
      have : (Pi.single 2 1 : Fin 3 → ℂ) = c⁻¹ • ![0, 0, c] := by
        funext i; fin_cases i <;> simp [hc]
      rw [this]; exact Submodule.smul_mem _ _ hmem
    by_cases hΓ : H.gam = ⊥
    · by_cases ht : H.t = ⊥
      · left; rw [hΓ, ht, perTan_bot]; simp
      · right
        obtain ⟨c, hc, hmem⟩ := abel_neN H ht
        exact hfib c hc (Submodule.mem_sup_right hmem)
    · right
      obtain ⟨w, hwΓ, -, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hΓ
        rw [H.gam_rat, Submodule.span_eq_bot]
        exact fun w hw => hcon w hw.1 hw.2
      refine hfib (w.2 0) (fun h0 => hw0 (Prod.ext (funext fun i => i.elim0) (funext fun i => ?_)))
        (Submodule.mem_sup_left ⟨w, hwΓ, rfl⟩)
      rw [Subsingleton.elim i 0, h0]; rfl

end Nat

end LSG.W88.V5d
