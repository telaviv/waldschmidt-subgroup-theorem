/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarMStarN

/-!
# M2.8: lean_mstar's `Thm11KappaAnK` (with `LAn = ∅`) at `y⁵ = x(1 − x)`

**`thm11KappaAnK5 : MStarCopy.Thm11KappaAnK 5 2 (·+1) perA5 perB5 ∅`**, unconditionally, by `hkOn_transport` along
`iotaN5` (`AbVarMStarN.lean`). The model `gmAnK … ∅` (frame `gmF2`) has the same `d₁, d₂, alg, per` as `gmAn`; its
logarithms `lamAnK … ∅` are the toric logarithms and `twistAn b j e (perA5, perB5) = genN5 b j e` (the period
generators). Its subgroup family asks for an **algebraic** `x ∈ S` with `PsiG θ 0 snd x ≠ 0`. For `S = ι(T_H) ≠ 0`:
* `t ≠ 0`: `FibOK` puts the fibre vector `(0, 0, 0, 1)` in `T_H`; `ι` of it is `(0, (0, 5/3))` (`subK_fib`);
* `t = 0`, `Γ ≠ 0`: `Γ` is `ℚ̄`-rational, so it has an algebraic vector `(·, s)` with `s ≠ 0` (`d₀ = 0`), and
  `ι(0, 0, 0, s) = (0, (0, (5/3) s₀))` (`subK_fib`);
* `t = 0`, `Γ = 0`: the torus part `torusLie U` is nonzero, so it contains a nonzero rational vector `l`, and
  `PsiG ((l₁, l₂), 0) = (θᵀl₁, θᵀl₂) ≠ 0` by `ℚ`-independence of `θ` (`subK_tor`, M1's argument).
-/

open Complex Module LSG.AuxAV

noncomputable section

namespace LSG.W88

open LSG.JacAn LSG.JacAn.Beta
open LSG.W88.Vec (AlgPair)

variable {r : ℕ}

/-- A vector of `S` with zero toric and abelian parts and algebraic nonzero fibre gives `gmAnK`'s witness. -/
lemma subK_fib (b : Fin r → ℂ) (S : Submodule ℂ (TanN5 r)) {p : TanN5 r} (hp : p ∈ S) (ht : p.2.1 = 0)
    (hz : p.2.2.1 = 0) (ha : IsAlgebraic ℚ (p.2.2.2 0)) (h0 : p.2.2.2 0 ≠ 0) :
    ∃ x ∈ S.map (iotaN5 r).toLinearMap, MStarCopy.algF (MStarCopy.algAn 2) x ∧
      MStarCopy.PsiG (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) 0 (LinearMap.snd ℂ _ ℂ) x ≠ 0 := by
  have hx : iotaN5 r p = ((0 : (ιA r → ℂ) × (ιA r → ℂ)), ((0 : Fin 2 × Fin r → ℂ), 5 / 3 * p.2.2.2 0)) := by
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · change torA r p.2.1 = 0
      rw [ht, map_zero]
    · change abA r p.2.2.1 = 0
      rw [hz]
      exact map_zero (abA r)
  refine ⟨iotaN5 r p, ⟨p, hp, rfl⟩, ?_, ?_⟩
  · rw [hx]
    exact ⟨fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero, fun _ => isAlgebraic_zero,
      isAlgebraic_five_thirds.mul ha⟩
  · rw [hx]
    intro h
    have e2 : (MStarCopy.PsiG (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) 0 (LinearMap.snd ℂ _ ℂ)
        (((0 : (ιA r → ℂ) × (ιA r → ℂ)), ((0 : Fin 2 × Fin r → ℂ), 5 / 3 * p.2.2.2 0)) : TFN5 r)).2 =
        5 / 3 * p.2.2.2 0 := by
      simp [MStarCopy.PsiG]
    exact mul_ne_zero (by norm_num) h0 (e2.symm.trans (congrArg Prod.snd h))

/-- A nonzero torus part gives `gmAnK`'s witness (M1's argument). -/
lemma subK_tor (b : Fin r → ℂ) (hb : MStarCopy.IsAdaptedBasisD (MStarCopy.zetaN 5) (Nat.totient 5) b)
    (S : Submodule ℂ (TanN5 r)) (U : Submodule ℚ (Fin (d1A r) → ℚ)) (hU : torusLie U ≠ ⊥)
    (hS : ∀ w ∈ torusLie U, torInclA (B := BN5 r) (d₀ := 0) (r := 1) w ∈ S) :
    ∃ x ∈ S.map (iotaN5 r).toLinearMap, MStarCopy.algF (MStarCopy.algAn 2) x ∧
      MStarCopy.PsiG (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) 0 (LinearMap.snd ℂ _ ℂ) x ≠ 0 := by
  have hθ : LinearIndependent ℚ (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) := hb.indep
  have hann : K11.annQ U ≠ ⊥ := by
    intro h0
    apply hU
    rw [show torusLie U = K11.annC U from rfl, K11.annC_eq_cspan, h0, K11.cspan_eq, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨q, hq, rfl⟩
    rw [(Submodule.mem_bot ℚ).mp hq]; simp
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann
  set lc : Fin (d1A r) → ℂ := fun k => ((l k : ℚ) : ℂ)
  have hlc : lc ∈ torusLie U := by
    rw [show torusLie U = K11.annC U from rfl, K11.annC_eq_cspan]
    exact K11.castL_mem_cspan hl
  refine ⟨iotaN5 r (torInclA lc), ⟨_, hS lc hlc, rfl⟩, ?_, ?_⟩
  · rw [iotaN5_torIncl]
    refine ⟨fun i => ?_, fun i => ?_, fun _ => isAlgebraic_zero, isAlgebraic_zero⟩
    · exact isAlgebraic_algebraMap (l _ : ℚ)
    · exact isAlgebraic_algebraMap (l _ : ℚ)
  · rw [iotaN5_torIncl]
    intro h0
    set θ := MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b
    have e1 : (MStarCopy.PsiG θ 0 (LinearMap.snd ℂ _ ℂ) ((torA r lc, 0) : TFN5 r)).1 =
        ∑ i, l ((tEA r).symm (Sum.inl i)) • θ i := by
      simp [MStarCopy.PsiG, MStarCopy.dotL, torA, lc, Rat.smul_def, mul_comm]
    have e2 : (MStarCopy.PsiG θ 0 (LinearMap.snd ℂ _ ℂ) ((torA r lc, 0) : TFN5 r)).2 =
        ∑ i, l ((tEA r).symm (Sum.inr i)) • θ i := by
      simp [MStarCopy.PsiG, MStarCopy.dotL, torA, lc, Rat.smul_def, mul_comm]
    have hz1 : ∀ i, l ((tEA r).symm (Sum.inl i)) = 0 :=
      Fintype.linearIndependent_iff.mp hθ _ (by rw [← e1, h0]; rfl)
    have hz2 : ∀ i, l ((tEA r).symm (Sum.inr i)) = 0 :=
      Fintype.linearIndependent_iff.mp hθ _ (by rw [← e2, h0]; rfl)
    apply hl0
    funext k
    rcases hk : tEA r k with i | i
    · have := hz1 i; rwa [← hk, Equiv.symm_apply_apply] at this
    · have := hz2 i; rwa [← hk, Equiv.symm_apply_apply] at this

/-- **lean_mstar's `Thm11KappaAnK` (`LAn = ∅`) for `A^♮`, `A = Jac(y⁵ = x(1 − x))`**, unconditionally. -/
theorem thm11KappaAnK5 :
    MStarCopy.Thm11KappaAnK 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 MStarCopy.perB5 ∅ := by
  intro r b hb
  set G := MStarCopy.gmAnK 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b ∅ with hG
  refine hkOn_transport (gmLsgAV 0 (d1A r) (AnN5 r) (MN5 b)) (TorInjAV (MN5 b))
    (hyperplaneKappaAbVarV_aBlockV b hb 0 (d1A r)) G (MStarCopy.TorInj G) (iotaN5 r) (fun v hv => algN5 v hv)
    (LamAV 0 (d1A r) (AnN5 r) (MN5 b)) rfl ?_ (fun v hv => perN5_symm b hv) rfl d2N5 ?_
    (fun V hV => torInjAV_of b V hV)
  · -- logarithms
    intro y hy
    have key : Submodule.span ℚ (MStarCopy.lamAnK 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b ∅) ≤
        (Submodule.span ℚ ((LamAV 0 (d1A r) (AnN5 r) (MN5 b) : AddSubgroup (TanN5 r)) : Set (TanN5 r))).comap
          ((iotaN5 r).symm.toLinearMap.restrictScalars ℚ) := by
      rw [Submodule.span_le]
      intro v hv
      refine Submodule.subset_span ?_
      change (iotaN5 r).symm v ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b)
      rcases hv with (⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨j, e, vw, hvw, rfl⟩
      · exact symm_tor1_lam b j x hx
      · exact symm_tor2_lam b j x hx
      · have hvw' : vw = (MStarCopy.perA5, MStarCopy.perB5) := by simpa using hvw
        subst hvw'
        change (iotaN5 r).symm (MStarCopy.qv (genN5 b j e)) ∈ _
        rw [symm_qv_genN5]
        exact pvN5_lam b j e
    exact key hy
  · -- subgroups: an algebraic vector with `PsiG ≠ 0`
    rintro S ⟨H, rfl, hF⟩ hS0
    right
    by_cases ht : H.t = ⊥
    · by_cases hgam : H.gam = ⊥
      · have hU : torusLie H.U ≠ ⊥ := by
          intro hU
          apply hS0
          rw [SubgroupDataAV.tan, hgam, hU, ht, perTanA_bot']
          simp
        exact subK_tor b hb H.tan H.U hU
          (fun w hw => Submodule.mem_sup_left (Submodule.mem_sup_right ⟨w, hw, rfl⟩))
      · obtain ⟨w, ⟨hwg, hwa⟩, hw0⟩ : ∃ w ∈ {w | w ∈ H.gam ∧ AlgPair w}, w ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hgam
          rw [H.gam_rat, eq_bot_iff, Submodule.span_le]
          intro w hw
          exact (Submodule.mem_bot ℂ).mpr (hcon w hw)
        have hw2 : w.2 0 ≠ 0 := by
          intro h
          apply hw0
          refine Prod.ext (Subsingleton.elim _ _) (funext fun i => ?_)
          rw [Subsingleton.elim i 0, h]
          rfl
        exact subK_fib b H.tan (p := vecInclA w)
          (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨w, hwg, rfl⟩)) rfl rfl (hwa.2 0) hw2
    · exact subK_fib b H.tan (p := (0, 0, 0, fun _ => 1)) (hF ht ⟨fun _ => 1, rfl⟩) rfl rfl isAlgebraic_one
        one_ne_zero

end LSG.W88
