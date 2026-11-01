/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMGn

/-!
# The `K`-form of Theorem MG♮: `Thm11KappaMGnK L` from `Theorem41VecLA`

**`thm11KappaMGnK_of (h : Theorem41VecLA) (L : CMLattice) : MStarCopy.Thm11KappaMGnK L`**. Same
group and isomorphism `mgIota` as for `gmMGn`. New: the logarithm generators `([u e_i], θ_i w)`,
`(u, w) ∈ Λ(E^♮)` (`LogNat` with `etaL`), pull back to `(0, 0, γ_i u e_{i.1}, θ_i w)` with `γ_i ∈
{1, ᾱ}`, which lies in `Λ(G)` because `ᾱ = α⁻¹` is a multiplier (`ζ(ᾱu) − α ζ(u) ∈ ℚ̄`); and the
uniform subgroup condition of `gmF2` (an algebraic `x ∈ ι(T_H)` with `Ψ''(x) ≠ 0`: a rational toric
vector, `dot_ne`, or `(0, s)`, `s ≠ 0`).
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

variable {r : ℕ} (L : CMLattice) (b : Fin r → ℂ) (hb : IsAdaptedFieldBasis L.α b)

/-- `ᾱ = α⁻¹` is a multiplier. -/
lemma conj_mem_multRing (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) : starRingEnd ℂ L.α ∈ multRing hg₂ hg₃ := by
  have hd := CMLat.cmD L hκ
  have hu : IsLatUnit L.pp L.α⁻¹ :=
    ⟨inv_ne_zero hd.unit.ne, hd.unit.inv_mul_mem, fun x hx => by
      rw [inv_inv]; exact hd.unit.mul_mem x hx⟩
  rw [hd.conj_eq]
  refine ⟨hd.alg.inv, fun u hu' => ⟨?_, ?_⟩⟩
  · rcases hu' with hu' | hu'
    · exact Or.inl (hu.mul_mem u hu')
    · right
      rw [weierstrassP_mul L.pp hu]
      exact ((hd.alg.inv.pow 2).inv).mul hu'
  · rw [zeta_mul L.pp hu, map_inv₀, hd.conj_eq, sub_self]
    exact isAlgebraic_zero

lemma gam_mem_multRing (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) (j : Fin r × Fin 2) :
    (if j.2 = 0 then 1 else starRingEnd ℂ L.α) ∈ multRing hg₂ hg₃ := by
  split_ifs
  · exact one_mem _
  · exact conj_mem_multRing L hκ hg₂ hg₃

lemma logNat_zeta (hκ : KappaOneZero L) {u w : ℂ} (h : LogNat L.pp (etaL L) u w) :
    AlgPtE L.pp u ∧ IsAlgebraic ℚ (w - zeta L.pp u) := by
  have hd := CMLat.cmD L hκ
  rcases h with ⟨m, n, rfl, hw⟩ | ⟨-, hp, -, hw⟩
  · have hl : (m : ℂ) * L.pp.ω₁ + n * L.pp.ω₂ ∈ L.pp.lattice :=
      PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
    refine ⟨Or.inl hl, ?_⟩
    have e : zeta L.pp ((m : ℂ) * L.pp.ω₁ + n * L.pp.ω₂) = etaL L m n := by
      rw [zeta_of_mem_lattice _ hl, hd.eta_eq_conj hl, CMLat.eta_one_eq L hκ, etaL, hd.hω]
      have hω := hd.ω₁_ne
      rw [show ((m : ℂ) * L.pp.ω₁ + n * (L.α * L.pp.ω₁)) / L.pp.ω₁ = m + n * L.α by field_simp]
      simp [map_add, map_mul]
    rwa [e]
  · exact ⟨Or.inr hp, hw⟩

include hb in
/-- **The new logarithm generators pull back into `Λ(G)`.** -/
lemma qv_log_mem (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (i : Fin r × Fin 2) {u w : ℂ} (h : LogNat L.pp (etaL L) u w) :
    (mgIota L b hb).symm (qv (((Submodule.Quotient.mk (Pi.single i u) :
      (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b i * w) : Qn L b)) ∈
      LamV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  obtain ⟨hu, hw⟩ := logNat_zeta L hκ h
  obtain ⟨hγu, hdef⟩ := (gam_mem_multRing L hκ hg₂ hg₃ i).2 u hu
  rw [mgIota_symm_apply]
  simp only [qv, qPi_mk, piB_single]
  refine ⟨fun k => k.elim0, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · change IsAlgebraic ℚ (Complex.exp (Sum.elim (0 : Fin r × Fin 2 → ℂ) 0 (tE r k)))
    rcases tE r k with _ | _ <;> simpa using isAlgebraic_one
  · by_cases hk : k = i.1
    · subst hk
      change (Pi.single i.1 _ : Fin r → ℂ) i.1 ∈ L.pp.lattice ∨
        IsAlgebraic ℚ (L.pp.weierstrassP ((Pi.single i.1 _ : Fin r → ℂ) i.1))
      rw [Pi.single_eq_same]; exact hγu
    · simp only [Pi.single_apply, hk, ite_false]; exact Or.inl (zero_mem _)
  · rw [Subsingleton.elim k 0, Pi.sub_apply, mgM_mulVec]
    simp only [zetaV]
    rw [sum_single_fin b (zeta L.pp) (zeta_zero _), theta_eq]
    set γ := (if i.2 = 0 then 1 else starRingEnd ℂ L.α)
    have : b i.1 * starRingEnd ℂ γ * w - b i.1 * zeta L.pp (γ * u) =
        b i.1 * (starRingEnd ℂ γ * (w - zeta L.pp u)) -
          b i.1 * (zeta L.pp (γ * u) - starRingEnd ℂ γ * zeta L.pp u) := by ring
    rw [this]
    exact ((hb.alg _).mul ((isAlgebraic_conj (gam_mem_multRing L hκ hg₂ hg₃ i).1).mul hw)).sub
      ((hb.alg _).mul hdef)

lemma psiG_apply (θ : Fin r × Fin 2 → ℂ) (lam : Qn L b →ₗ[ℂ] ℂ) (v : TF (Fin r × Fin 2) (Qn L b)) :
    PsiG θ 0 lam v = (dotL θ v.1.1, dotL θ v.1.2 + lam v.2) := by
  simp [PsiG]

/-- **The `K`-form hypothesis of Theorem MG♮ from `Theorem41VecLA`**, for every CM lattice. -/
theorem thm11KappaMGnK_of (h : Theorem41VecLA) (L : CMLattice) : MStarCopy.Thm11KappaMGnK L := by
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
  refine hyperplaneKappa_of_iso (hyperplaneKappaVec_of h) hLs hM le_rfl (liftAlg_block hg₂ hg₃ hd)
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

end LSG.W88.V5d
