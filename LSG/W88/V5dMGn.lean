/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMGnGen
import LSG.W88.V5dMXG

/-!
# Theorem MG♮'s hypothesis `Thm11KappaMGn L` from `Theorem41VecLA`

**`thm11KappaMGn_of (h : Theorem41VecLA) (L : CMLattice) : MStarCopy.Thm11KappaMGn L`**, for every
CM lattice (lean_mstar's `CMLattice`, copied; its premise `KappaOneZero L` gives the CM data,
`LSG.CM.Kappa`). Via `hyperplaneKappa_of_iso` for the class-`𝒞` group `G_m^{2n} × ((E^r)^♮ pushed
out along bᵀ)` and the isomorphism `mgIota` (`LSG.W88.V5dMGnIso`): logarithm and period generators
pull back exactly into `Λ(G)`, `Ω(G)`; a member `H` maps to `torSub (annQ U) × h`, and a nonzero `h`
has a vector with fibre coordinate `≠ 0` (`gam_ne`, `abel_ne`).
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

lemma perTan_bot {m r' : ℕ} (Ls : Fin m → PeriodPair) (M : Matrix (Fin r') (Fin m) ℂ) :
    perTan Ls M ⊥ = ⊥ := by
  rw [perTan, perTanId, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨⟨l, e⟩, ⟨hl, -, he⟩, rfl⟩
  simp only [Submodule.mem_bot] at hl he
  subst hl; subst he
  have : etaV Ls 0 = 0 := funext fun j => eta_zero _
  simp [this]

variable {r : ℕ} (L : CMLattice) (b : Fin r → ℂ) (hb : IsAdaptedFieldBasis L.α b)

include hb in
/-- `ι⁻¹` of the generators of `gmMGn`'s logarithms lie in `Λ(G)`. -/
lemma lamGen_mem_MGn (hκ : KappaOneZero L) (g : TF (Fin r × Fin 2) (Qn L b))
    (hg : g ∈ lamGen (ι := Fin r × Fin 2) (perQn L b)) :
    (mgIota L b hb).symm g ∈ LamV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  rcases hg with (⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨q, hq, rfl⟩
  · exact tor_mem_lam L b hb hx (torL_symm_single1 j x)
  · exact tor_mem_lam L b hb hx (torL_symm_single2 j x)
  · exact perV_le_lamV (perQn_mem L b hb hκ hq)

include hb in
/-- The period generators pull back into `span_ℚ Ω(G)`. -/
lemma per_le (hκ : KappaOneZero L) :
    Submodule.span ℚ (perGen (ι := Fin r × Fin 2) (perQn L b)) ≤
      (OmV 0 (2 * nI r) (mgLs L r) (mgM b)).map
        ((mgIota L b hb).toLinearMap.restrictScalars ℚ) := by
  have key : ∀ x, (mgIota L b hb).symm x ∈ PerV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) →
      x ∈ (OmV 0 (2 * nI r) (mgLs L r) (mgM b)).map
        ((mgIota L b hb).toLinearMap.restrictScalars ℚ) := by
    intro x hx
    refine ⟨(mgIota L b hb).symm x, Submodule.subset_span hx, ?_⟩
    simp
  rw [Submodule.span_le]
  rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩) <;> apply key
  · exact tor_mem_per L b hb (torL_symm_single1 j _)
  · exact tor_mem_per L b hb (torL_symm_single2 j _)
  · exact perQn_mem L b hb hκ hq

include hb in
/-- Common denominators: `span_ℚ` of generators in a subgroup `Λs`. -/
lemma lam_nsmul {S : Set (TF (Fin r × Fin 2) (Qn L b))}
    (Λs : AddSubgroup (TanV 0 (2 * nI r) r 1)) (hgen : ∀ g ∈ S, (mgIota L b hb).symm g ∈ Λs) :
    ∀ y ∈ (Submodule.span ℚ S : Set (TF (Fin r × Fin 2) (Qn L b))),
      ∃ N : ℕ, 0 < N ∧ N • (mgIota L b hb).symm y ∈ Λs := by
  intro y hy
  have hcl : y ∈ Submodule.span ℚ ((AddSubgroup.closure S : AddSubgroup _) :
      Set (TF (Fin r × Fin 2) (Qn L b))) := by
    rw [K11.span_closure_eq]; exact hy
  obtain ⟨N, hN, hNy⟩ := K11.exists_nsmul_mem_of_mem_span _ hcl
  refine ⟨N, hN, ?_⟩
  rw [← map_nsmul]
  have hle : AddSubgroup.closure S ≤ Λs.comap (mgIota L b hb).symm.toLinearMap.toAddMonoidHom :=
    (AddSubgroup.closure_le _).mpr fun g hg => hgen g hg
  exact hle hNy

/-- **Theorem MG♮'s hypothesis from `Theorem41VecLA`**, for every CM lattice. -/
theorem thm11KappaMGn_of (h : Theorem41VecLA) (L : CMLattice) : MStarCopy.Thm11KappaMGn L := by
  intro hκ hg₂ hg₃ r b hb
  have hd := CMLat.cmD L hκ
  have hLs : ∀ j, IsAlgebraic ℚ (mgLs L r j).g₂ ∧ IsAlgebraic ℚ (mgLs L r j).g₃ :=
    fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat (mgM b) := fun _ k => hb.alg k
  refine hyperplaneKappa_of_iso (hyperplaneKappaVec_of h) hLs hM le_rfl (liftAlg_block hg₂ hg₃ hd)
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

end LSG.W88.V5d
