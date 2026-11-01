/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOntoBridges
import LSG.W88.MStarCopySMGn

/-!
# Theorem SMG♮'s hypothesis `Thm11KappaSMGn L`, unconditionally

**`thm11KappaSMGn_uncond (L : CMLattice) : MStarCopy.Thm11KappaSMGn L`** (premised on
`KappaOneZero L`, like `Thm11KappaMGn`, `Thm11KappaMGnK`). The group `G_a × G_m^{2n} × Q''` of
lean_mstar's `gmSMGn` is the `gmMGnK` group with one extra `G_a` factor, i.e. the class-`𝒞` group
`G_a × G_m^{2n} × ((E^r)^♮ pushed out along bᵀ)` (`d₀ = 1`, curves `mgLs L r`, `M = mgM b`). Via
`hyperplaneKappa_of_iso` and `hyperplaneKappaVec_uncond` with
`smIota : TanV 1 (2n) r 1 ≃ T(G_a × G_m^{2n} × Q'')`, `(a, x, z, s) ↦ (x, (a, ([incl z], s)))`:

* generators: toric logarithms and periods of `Q''` pull back as for `gmMGn` (prepending `a = 0`,
  `ext0`); the new generators `(a, (0, f))`, `a, f ∈ ℚ̄`, pull back to `(a, 0, 0, f) ∈ Λ(G)`;
* the subgroup condition of `gmF2` (an algebraic `x ∈ ι(T_H)` with
  `Ψ''(x) = (θᵀx₁ + a, θᵀx₂ + f) ≠ 0`): a rational toric vector (`dot_ne`), a nonzero algebraic
  `(a, s) ∈ Γ` (now `μ = a` is used), or the vector `(0, c)`, `c ≠ 0`, of the abelian part
  (`abel_ne`, applied to the `d₀ = 0` datum with the same `t`).
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

/-! ### Prepending a zero `G_a` coordinate -/

/-- `(x₁, x₂, x₃) ↦ (0, x₁, x₂, x₃)`. -/
def ext0 {d1 m r' : ℕ} (x : TanV 0 d1 m r') : TanV 1 d1 m r' := (0, x.2)

lemma ext0_per {d1 m r' : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r') (Fin m) ℂ}
    {x : TanV 0 d1 m r'} (hx : x ∈ PerV Ls M) : ext0 x ∈ PerV (d0 := 1) Ls M :=
  ⟨rfl, hx.2.1, hx.2.2.1, hx.2.2.2⟩

lemma ext0_lam {d1 m r' : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r') (Fin m) ℂ}
    {x : TanV 0 d1 m r'} (hx : x ∈ LamV Ls M) : ext0 x ∈ LamV (d0 := 1) Ls M :=
  ⟨fun _ => isAlgebraic_zero, hx.2.1, hx.2.2.1, hx.2.2.2⟩

variable {r : ℕ} (L : CMLattice) (b : Fin r → ℂ) (hb : IsAdaptedFieldBasis L.α b)

/-! ### The isomorphism -/

/-- **`ι : TanV 1 (2n) r 1 ≃ T(G_a × G_m^{2n} × Q'')`**,
`(a, x, z, s) ↦ (x, (a, ([incl z], s)))`. -/
noncomputable def smIota : TanV 1 (2 * nI r) r 1 ≃ₗ[ℂ] TF (Fin r × Fin 2) (QSn L b) where
  toFun v := (torL r v.2.1, (v.1 0, (Submodule.Quotient.mk (inclB v.2.2.1), v.2.2.2 0)))
  invFun w := (fun _ => w.2.1, (torL r).symm w.1, qPi L b hb w.2.2.1, fun _ => w.2.2.2)
  map_add' v w := by
    refine Prod.ext (map_add _ _ _) (Prod.ext rfl (Prod.ext ?_ rfl))
    simp only [Prod.snd_add, Prod.fst_add, map_add, Submodule.Quotient.mk_add]
  map_smul' c v := by
    refine Prod.ext (map_smul _ _ _) (Prod.ext rfl (Prod.ext ?_ rfl))
    change Submodule.Quotient.mk (inclB (c • v.2.2.1)) = c • Submodule.Quotient.mk (inclB v.2.2.1)
    rw [map_smul, Submodule.Quotient.mk_smul]
  left_inv v := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i; fin_cases i; rfl
    · exact (torL r).symm_apply_apply _
    · change qPi L b hb (Submodule.Quotient.mk _) = _
      rw [qPi_mk, piB_inclB]
    · funext i; fin_cases i; rfl
  right_inv w := by
    refine Prod.ext ((torL r).apply_symm_apply _) (Prod.ext rfl (Prod.ext ?_ rfl))
    exact mk_inclB_qPi L b hb _

lemma smIota_symm_apply (w : TF (Fin r × Fin 2) (QSn L b)) :
    (smIota L b hb).symm w =
      (fun _ => w.2.1, (torL r).symm w.1, qPi L b hb w.2.2.1, fun _ => w.2.2.2) :=
  rfl

lemma smIota_apply (v : TanV 1 (2 * nI r) r 1) :
    smIota L b hb v =
      (torL r v.2.1, (v.1 0, (Submodule.Quotient.mk (inclB v.2.2.1), v.2.2.2 0))) := rfl

lemma sm_symm_qv0 (q : Qn L b) :
    (smIota L b hb).symm (qv (((0 : ℂ), q) : QSn L b)) = ext0 ((mgIota L b hb).symm (qv q)) :=
  Prod.ext (funext fun _ => rfl) rfl

lemma sm_symm_tor (p : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) :
    (smIota L b hb).symm ((p, 0) : TF (Fin r × Fin 2) (QSn L b)) =
      ext0 ((mgIota L b hb).symm ((p, 0) : TF (Fin r × Fin 2) (Qn L b))) :=
  Prod.ext (funext fun _ => rfl) rfl

include hb in
/-- `ι⁻¹` preserves algebraic vectors. -/
lemma sm_alg (v : TF (Fin r × Fin 2) (QSn L b)) (hv : algF (algQSn L b) v) :
    AlgVecV ((smIota L b hb).symm v) := by
  obtain ⟨-, h1, h2, h3⟩ := mg_alg L b hb (v.1, v.2.2) ⟨hv.1, hv.2.1, hv.2.2.2⟩
  exact ⟨fun _ => hv.2.2.1, h1, h2, h3⟩

/-! ### Generators -/

/-- The new generators `(a, (0, f))` pull back to `(a, 0, 0, f) ∈ Λ(G)`. -/
lemma ga_mem_lam {a f : ℂ} (ha : IsAlgebraic ℚ a) (hf : IsAlgebraic ℚ f) :
    (smIota L b hb).symm (qv ((a, (0, f)) : QSn L b)) ∈
      LamV (d0 := 1) (d1 := 2 * nI r) (mgLs L r) (mgM b) := by
  rw [smIota_symm_apply]
  refine ⟨fun _ => ha, fun i => ?_, fun k => Or.inl ?_, fun _ => ?_⟩
  · change IsAlgebraic ℚ (Complex.exp ((torL r).symm 0 i))
    rw [map_zero, Pi.zero_apply, Complex.exp_zero]; exact isAlgebraic_one
  · change qPi L b hb 0 k ∈ _
    rw [map_zero]; exact zero_mem _
  · change IsAlgebraic ℚ (f - (mgM b).mulVec (zetaV (mgLs L r) (qPi L b hb 0)) _)
    have : zetaV (mgLs L r) (0 : Fin r → ℂ) = 0 := funext fun _ => zeta_zero _
    rw [map_zero, this, Matrix.mulVec_zero, Pi.zero_apply, sub_zero]; exact hf

include hb in
/-- Common denominators for `smIota`. -/
lemma smLam_nsmul {S : Set (TF (Fin r × Fin 2) (QSn L b))}
    (Λs : AddSubgroup (TanV 1 (2 * nI r) r 1)) (hgen : ∀ g ∈ S, (smIota L b hb).symm g ∈ Λs) :
    ∀ y ∈ (Submodule.span ℚ S : Set (TF (Fin r × Fin 2) (QSn L b))),
      ∃ N : ℕ, 0 < N ∧ N • (smIota L b hb).symm y ∈ Λs := by
  intro y hy
  have hcl : y ∈ Submodule.span ℚ ((AddSubgroup.closure S : AddSubgroup _) :
      Set (TF (Fin r × Fin 2) (QSn L b))) := by
    rw [K11.span_closure_eq]; exact hy
  obtain ⟨N, hN, hNy⟩ := K11.exists_nsmul_mem_of_mem_span _ hcl
  refine ⟨N, hN, ?_⟩
  rw [← map_nsmul]
  have hle : AddSubgroup.closure S ≤ Λs.comap (smIota L b hb).symm.toLinearMap.toAddMonoidHom :=
    (AddSubgroup.closure_le _).mpr fun g hg => hgen g hg
  exact hle hNy

include hb in
/-- The period generators pull back into `span_ℚ Ω(G)`. -/
lemma smPer_le (hκ : KappaOneZero L) :
    Submodule.span ℚ (perSSn L b) ≤
      (OmV 1 (2 * nI r) (mgLs L r) (mgM b)).map
        ((smIota L b hb).toLinearMap.restrictScalars ℚ) := by
  have key : ∀ x, (smIota L b hb).symm x ∈ PerV (d0 := 1) (d1 := 2 * nI r) (mgLs L r) (mgM b) →
      x ∈ (OmV 1 (2 * nI r) (mgLs L r) (mgM b)).map
        ((smIota L b hb).toLinearMap.restrictScalars ℚ) := by
    intro x hx
    refine ⟨(smIota L b hb).symm x, Submodule.subset_span hx, ?_⟩
    simp
  rw [Submodule.span_le]
  rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩) <;> apply key
  · exact (sm_symm_tor L b hb _).symm ▸ ext0_per (tor_mem_per L b hb (torL_symm_single1 j _))
  · exact (sm_symm_tor L b hb _).symm ▸ ext0_per (tor_mem_per L b hb (torL_symm_single2 j _))
  · exact (sm_symm_qv0 L b hb q).symm ▸ ext0_per (perQn_mem L b hb hκ hq)

/-! ### Subgroup tangent spaces -/

lemma psiGS_apply (v : TF (Fin r × Fin 2) (QSn L b)) :
    PsiG (theta L.α b) (muSn L b) (lamSn L b) v =
      (dotL (theta L.α b) v.1.1 + v.2.1, dotL (theta L.α b) v.1.2 + v.2.2.2) := rfl

lemma sm_vecIncl (w : (Fin 1 → ℂ) × (Fin 1 → ℂ)) :
    smIota L b hb (vecIncl (d1 := 2 * nI r) (m := r) w) = (0, (w.1 0, (0, w.2 0))) := by
  rw [smIota_apply]
  refine Prod.ext (map_zero _) (Prod.ext rfl (Prod.ext ?_ rfl))
  change Submodule.Quotient.mk (inclB (0 : Fin r → ℂ)) = 0
  rw [map_zero]; rfl

lemma sm_torIncl (y : Fin (2 * nI r) → ℂ) :
    smIota L b hb (torIncl (d0 := 1) (m := r) (r := 1) y) = (torL r y, 0) := by
  rw [smIota_apply]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  change Submodule.Quotient.mk (inclB (0 : Fin r → ℂ)) = 0
  rw [map_zero]; rfl

lemma sm_g2Incl (p : (Fin r → ℂ) × (Fin 1 → ℂ)) :
    smIota L b hb (g2Incl (d0 := 1) (d1 := 2 * nI r) p) = (0, (0, gA L b p)) := by
  rw [smIota_apply]
  exact Prod.ext (map_zero _) rfl

lemma ratPair_bot {a c : ℕ} : RatPair (⊥ : Submodule ℂ ((Fin a → ℂ) × (Fin c → ℂ))) :=
  (Submodule.span_eq_bot.mpr fun _ hw => (Submodule.mem_bot ℂ).mp hw.1).symm

/-! ### The theorem -/

/-- **Theorem SMG♮'s hypothesis unconditionally**, for every CM lattice
(premise `KappaOneZero L`). -/
theorem thm11KappaSMGn_uncond (L : CMLattice) : MStarCopy.Thm11KappaSMGn L := by
  intro hκ hg₂ hg₃ r b hb
  have hd := CMLat.cmD L hκ
  have hLs : ∀ j, IsAlgebraic ℚ (mgLs L r j).g₂ ∧ IsAlgebraic ℚ (mgLs L r j).g₃ :=
    fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat (mgM b) := fun _ k => hb.alg k
  have hgen : ∀ g ∈ lamSSn L b,
      (smIota L b hb).symm g ∈ lamVSub (d0 := 1) (d1 := 2 * nI r) (mgLs L r) (mgM b) hLs hM := by
    rintro g (((⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨a, f, ha, hf, rfl⟩) | ⟨q, hq, rfl⟩)
    · exact (sm_symm_tor L b hb _).symm ▸
        ext0_lam (tor_mem_lam L b hb hx (torL_symm_single1 j x))
    · exact (sm_symm_tor L b hb _).symm ▸
        ext0_lam (tor_mem_lam L b hb hx (torL_symm_single2 j x))
    · exact ga_mem_lam L b hb ha hf
    · exact (sm_symm_qv0 L b hb q).symm ▸ ext0_lam (perV_le_lamV (perQn_mem L b hb hκ hq))
  refine hyperplaneKappa_of_iso hyperplaneKappaVec_uncond hLs hM le_rfl (liftAlg_block hg₂ hg₃ hd)
    (perTanRat_block hd) (gmSMGn L b) (smIota L b hb) (sm_alg L b hb)
    (lamVSub (mgLs L r) (mgM b) hLs hM) (fun _ hx => hx) (smLam_nsmul L b hb _ hgen)
    (smPer_le L b hb hκ) rfl (finrank_Qn L b hb) ?_
  intro H hH
  right
  have halg0 : algQn L b 0 := ⟨⟨0, fun _ => isAlgebraic_zero, rfl⟩, isAlgebraic_zero⟩
  -- a vector of `T_H` whose image is algebraic with `Ψ'' ≠ 0`
  have hvec : ∀ v ∈ H.tan, algF (algQSn L b) (smIota L b hb v) →
      PsiG (theta L.α b) (muSn L b) (lamSn L b) (smIota L b hb v) ≠ 0 →
      ∃ x ∈ H.tan.map (smIota L b hb).toLinearMap, algF (algQSn L b) x ∧
        PsiG (theta L.α b) (muSn L b) (lamSn L b) x ≠ 0 :=
    fun v hv h1 h2 => ⟨_, Submodule.mem_map_of_mem hv, h1, h2⟩
  by_cases hT : torusLie H.U = ⊥
  · by_cases hΓ : H.gam = ⊥
    · by_cases ht : H.t = ⊥
      · exfalso; apply hH
        rw [SubgroupDataV.tan, hT, hΓ, ht, perTan_bot]; simp
      · -- the abelian part, via the `d₀ = 0` datum with the same `t`
        let H0 : SubgroupDataV (d0 := 0) (d1 := 2 * nI r) (mgLs L r) (mgM b) :=
          ⟨H.U, H.t, ⊥, ratPair_bot, H.t_ab⟩
        obtain ⟨c, hc, hca, p, hp, hpc⟩ := abel_ne L b hb hκ H0 ht
        refine hvec (g2Incl p) (Submodule.mem_sup_right (Submodule.mem_map_of_mem hp)) ?_ ?_
        · rw [sm_g2Incl, hpc]
          exact ⟨fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero, isAlgebraic_zero,
            ⟨0, fun _ => isAlgebraic_zero, rfl⟩, hca⟩
        · rw [sm_g2Incl, hpc, psiGS_apply]
          intro h0
          apply hc
          simpa using congrArg Prod.snd h0
    · -- the vector part: `Ψ'' = (a, s)`
      obtain ⟨w, hwΓ, hwa, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hΓ
        rw [H.gam_rat, Submodule.span_eq_bot]
        exact fun w hw => hcon w hw.1 hw.2
      refine hvec (vecIncl w)
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_map_of_mem hwΓ))) ?_ ?_
      · rw [sm_vecIncl]
        exact ⟨fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero, hwa.1 0,
          ⟨0, fun _ => isAlgebraic_zero, rfl⟩, hwa.2 0⟩
      · rw [sm_vecIncl, psiGS_apply]
        intro h0
        apply hw0
        have e1 : w.1 0 = 0 := by simpa using congrArg Prod.fst h0
        have e2 : w.2 0 = 0 := by simpa using congrArg Prod.snd h0
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · rw [Subsingleton.elim i 0, e1]; rfl
        · rw [Subsingleton.elim i 0, e2]; rfl
  · -- the toric part
    obtain ⟨q, hq, hqT⟩ := torus_ne H.U hT
    refine hvec (torIncl (K11.castL _ q))
      (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hqT))) ?_ ?_
    · rw [sm_torIncl]
      have hr : ∀ i, IsAlgebraic ℚ (K11.castL _ q i) := fun i => isAlgebraic_algebraMap (q i)
      exact ⟨fun j => hr _, fun j => hr _, isAlgebraic_zero, halg0⟩
    · rw [sm_torIncl, psiGS_apply]
      intro h0
      rcases dot_ne L b hb hq with h1 | h1
      · exact h1 (by simpa using congrArg Prod.fst h0)
      · exact h1 (by simpa using congrArg Prod.snd h0)

end LSG.W88.V5d
