/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarQbar

/-!
# A6: lean_mstar's `Thm11KappaAK` (with `LA = ∅`) for `Jac(y⁵ = x(1 − x))`

**`thm11KappaAK5_of`**: `HyperplaneKappaAbVar → MStarCopy.Thm11KappaAK 5 2 (fun s => s + 1) perA5 0 ∅`.

The model `gmAK … ∅` (frame `gmF2`) has the same `d₁, d₂, alg, per` as `gmA`; its logarithms `lamAK … ∅` are the toric
logarithms and `twistA j e perA5 = genA j e` (the period generators). Its subgroup family asks for an **algebraic**
`x ∈ S` with `PsiG θ 0 λ x ≠ 0`. For `S = ι(H.tan) ≠ ⊥`:
* `t ≠ 0`: `exists_alg_lam_ne` (abelian subvarieties are defined over `ℚ̄`, `AbVarQbar.lean`) gives an algebraic
  `z ∈ t` with `λ(abA z) = 5 Σ_j b_j z_j(0) ≠ 0`;
* `t = 0`: the torus part `torusLie U = cspan (annQ U)` is nonzero, so it contains a nonzero rational vector `l`, and
  `PsiG ((l₁, l₂), 0) = (θᵀl₁, θᵀl₂) ≠ 0` by `ℚ`-independence of `θ = thetaD ζ 4 b`.
-/

open Complex Module

namespace LSG.W88

open LSG.JacAn LSG.JacAn.Beta

variable {r : ℕ}

/-- **lean_mstar's `Thm11KappaAK` (`LA = ∅`) for `Jac(y⁵ = x(1 − x))`** from lean_lsg's `§5d` statement. -/
theorem thm11KappaAK5_of (h : HyperplaneKappaAbVar) :
    MStarCopy.Thm11KappaAK 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0 ∅ := by
  intro r b hb
  set G := MStarCopy.gmAK 5 2 (fun s : Fin 2 => (s : ℕ) + 1) MStarCopy.perA5 0 b ∅ with hG
  set f : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ) →ₗ[ℚ] TanA 0 (d1A r) r :=
    (iotaA r).symm.toLinearMap.restrictScalars ℚ with hf
  set g : TanA 0 (d1A r) r →ₗ[ℚ] MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ) :=
    (iotaA r).toLinearMap.restrictScalars ℚ with hg
  refine hkOn_transport (gmLsgA 0 (d1A r) r) TorInjA (h 0 (d1A r) r) G _ (iotaA r) ?_ LamA rfl ?_ ?_ rfl ?_ ?_ ?_
  · -- algebraic vectors
    rintro v ⟨h1, h2, h3⟩
    refine ⟨fun i => i.elim0, fun k => ?_, fun j s => ?_⟩
    · change IsAlgebraic ℚ (Sum.elim v.1.1 v.1.2 (tEA r k))
      rcases tEA r k with i | i
      · exact h1 i
      · exact h2 i
    · exact (isAlgebraic_cA_inv s).mul (h3 _)
  · -- logarithms
    intro y hy
    have key : Submodule.span ℚ (MStarCopy.lamAK 5 2 (fun s : Fin 2 => (s : ℕ) + 1) MStarCopy.perA5 ∅) ≤
        (Submodule.span ℚ ((LamA : AddSubgroup (TanA 0 (d1A r) r)) : Set (TanA 0 (d1A r) r))).comap f := by
      rw [Submodule.span_le]
      intro v hv
      refine Submodule.subset_span ?_
      change (iotaA r).symm v ∈ LamA
      rcases hv with (⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨j, e, w, hw, rfl⟩
      · obtain ⟨hk, hA⟩ := symm_toric_mem (MStarCopy.tor1 j x) rfl (fun t => IsAlgebraic ℚ (Complex.exp t))
          (fun i => by
            by_cases hi : i = j
            · subst hi; simpa [MStarCopy.tor1] using hx
            · simpa [MStarCopy.tor1, Pi.single_apply, hi] using isAlgebraic_one)
          (fun i => by simpa [MStarCopy.tor1] using isAlgebraic_one)
        exact ⟨fun i => i.elim0, hk, fun j' => by rw [hA]; exact latt.zero_mem⟩
      · obtain ⟨hk, hA⟩ := symm_toric_mem (MStarCopy.tor2 j x) rfl (fun t => IsAlgebraic ℚ (Complex.exp t))
          (fun i => by simpa [MStarCopy.tor2] using isAlgebraic_one)
          (fun i => by
            by_cases hi : i = j
            · subst hi; simpa [MStarCopy.tor2] using hx
            · simpa [MStarCopy.tor2, Pi.single_apply, hi] using isAlgebraic_one)
        exact ⟨fun i => i.elim0, hk, fun j' => by rw [hA]; exact latt.zero_mem⟩
      · have hw' : w = MStarCopy.perA5 := by simpa using hw
        subst hw'
        change (iotaA r).symm (MStarCopy.qv (genA j e)) ∈ LamA
        rw [symm_qv_genA]
        exact ⟨fun i => i.elim0, fun _ => by simpa using isAlgebraic_one, single_perVec_mem j e⟩
    exact key hy
  · -- periods
    intro v hv
    have key : Submodule.span ℚ (MStarCopy.perGen (ι := ιA r) (MStarCopy.perAgen 5 2
        (fun s : Fin 2 => (s : ℕ) + 1) MStarCopy.perA5)) ≤
        (Submodule.span ℚ ((PerA : AddSubgroup (TanA 0 (d1A r) r)) : Set (TanA 0 (d1A r) r))).comap f := by
      rw [Submodule.span_le]
      intro w hw
      refine Submodule.subset_span ?_
      change (iotaA r).symm w ∈ PerA
      rcases hw with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, ⟨⟨j, e⟩, rfl⟩, rfl⟩
      · obtain ⟨hk, hA⟩ := symm_toric_mem (MStarCopy.tor1 j (2 * Real.pi * I)) rfl
          (fun t => ∃ k : ℤ, t = 2 * Real.pi * I * k)
          (fun i => by
            by_cases hi : i = j
            · subst hi; exact ⟨1, by simp [MStarCopy.tor1]⟩
            · exact ⟨0, by simp [MStarCopy.tor1, Pi.single_apply, hi]⟩)
          (fun i => ⟨0, by simp [MStarCopy.tor1]⟩)
        exact ⟨Subsingleton.elim _ _, hk, fun j' => by rw [hA]; exact latt.zero_mem⟩
      · obtain ⟨hk, hA⟩ := symm_toric_mem (MStarCopy.tor2 j (2 * Real.pi * I)) rfl
          (fun t => ∃ k : ℤ, t = 2 * Real.pi * I * k)
          (fun i => ⟨0, by simp [MStarCopy.tor2]⟩)
          (fun i => by
            by_cases hi : i = j
            · subst hi; exact ⟨1, by simp [MStarCopy.tor2]⟩
            · exact ⟨0, by simp [MStarCopy.tor2, Pi.single_apply, hi]⟩)
        exact ⟨Subsingleton.elim _ _, hk, fun j' => by rw [hA]; exact latt.zero_mem⟩
      · change (iotaA r).symm (MStarCopy.qv (genA j e)) ∈ PerA
        rw [symm_qv_genA]
        exact ⟨rfl, fun _ => ⟨0, by simp⟩, single_perVec_mem j e⟩
    exact key hv
  · -- d₂
    change Module.finrank ℂ (Fin 2 × Fin r → ℂ) = 2 * r
    simp [Module.finrank_fintype_fun_eq_card]
  · -- subgroups: an algebraic vector with `PsiG ≠ 0`
    rintro S ⟨H, rfl⟩ hS0
    right
    have hθ : LinearIndependent ℚ (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) := hb.indep
    by_cases ht : H.t = ⊥
    · -- the torus part is nonzero
      have hU : torusLie H.U ≠ ⊥ := by
        intro hU
        apply hS0
        have h0 : H.h0 = ⊥ := Subsingleton.elim _ _
        rw [SubgroupDataA.tan, h0, hU, ht, Submodule.prod_bot, Submodule.prod_bot]
      have hann : K11.annQ H.U ≠ ⊥ := by
        intro h0
        apply hU
        rw [show torusLie H.U = K11.annC H.U from rfl, K11.annC_eq_cspan, h0, K11.cspan_eq, eq_bot_iff,
          Submodule.span_le]
        rintro _ ⟨q, hq, rfl⟩
        rw [(Submodule.mem_bot ℚ).mp hq]; simp
      obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann
      set lc : Fin (d1A r) → ℂ := fun k => ((l k : ℚ) : ℂ)
      have hlc : lc ∈ torusLie H.U := by
        rw [show torusLie H.U = K11.annC H.U from rfl, K11.annC_eq_cspan]
        exact K11.castL_mem_cspan hl
      refine ⟨iotaA r (0, lc, 0), ⟨(0, lc, 0), ⟨Submodule.zero_mem _, hlc, Submodule.zero_mem _⟩, rfl⟩, ?_, ?_⟩
      · refine ⟨fun i => ?_, fun i => ?_, fun p => ?_⟩
        · exact (isAlgebraic_algebraMap (l _ : ℚ))
        · exact (isAlgebraic_algebraMap (l _ : ℚ))
        · simp [iotaA_apply, abA, isAlgebraic_zero]
      · intro h0
        set θ := MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b
        have e1 : (MStarCopy.PsiG θ 0 (MStarCopy.dotL (MStarCopy.thetaA 2 0 b)) (iotaA r (0, lc, 0))).1 =
            ∑ i, l ((tEA r).symm (Sum.inl i)) • θ i := by
          simp [MStarCopy.PsiG, iotaA_apply, MStarCopy.dotL, torA, lc, Rat.smul_def, mul_comm]
        have e2 : (MStarCopy.PsiG θ 0 (MStarCopy.dotL (MStarCopy.thetaA 2 0 b)) (iotaA r (0, lc, 0))).2 =
            ∑ i, l ((tEA r).symm (Sum.inr i)) • θ i := by
          simp [MStarCopy.PsiG, iotaA_apply, MStarCopy.dotL, torA, lc, Rat.smul_def, mul_comm, abA]
        have hz1 : ∀ i, l ((tEA r).symm (Sum.inl i)) = 0 :=
          Fintype.linearIndependent_iff.mp hθ _ (by rw [← e1, h0]; rfl)
        have hz2 : ∀ i, l ((tEA r).symm (Sum.inr i)) = 0 :=
          Fintype.linearIndependent_iff.mp hθ _ (by rw [← e2, h0]; rfl)
        apply hl0
        funext k
        rcases hk : tEA r k with i | i
        · have := hz1 i; rwa [← hk, Equiv.symm_apply_apply] at this
        · have := hz2 i; rwa [← hk, Equiv.symm_apply_apply] at this
    · -- the abelian part is nonzero
      obtain ⟨z, hz, hzalg, hzne⟩ := exists_alg_lam_ne H.t_ab ht (indep_of_adapted b hb)
      refine ⟨iotaA r (0, 0, z), ⟨(0, 0, z), ⟨Submodule.zero_mem _, Submodule.zero_mem _, hz⟩, rfl⟩, ?_, ?_⟩
      · refine ⟨fun i => ?_, fun i => ?_, fun p => ?_⟩
        · simp [iotaA_apply, torA, isAlgebraic_zero]
        · simp [iotaA_apply, torA, isAlgebraic_zero]
        · exact (isAlgebraic_cA _).mul (hzalg _ _)
      · intro h0
        have e2 : (MStarCopy.PsiG (MStarCopy.thetaD (MStarCopy.zetaN 5) (Nat.totient 5) b) 0
            (MStarCopy.dotL (MStarCopy.thetaA 2 0 b)) (iotaA r (0, 0, z))).2 =
            MStarCopy.dotL (MStarCopy.thetaA 2 0 b) (abA r z) := by
          simp [MStarCopy.PsiG, iotaA_apply, map_zero]
        have h2 := congrArg Prod.snd h0
        rw [e2, dotL_thetaA_abA] at h2
        exact mul_ne_zero (by norm_num) hzne h2
  · -- toric injectivity
    intro V hV v hvV hvper htor
    have hmem : ∀ p ∈ (PerA : AddSubgroup (TanA 0 (d1A r) r)), iotaA r p ∈ G.per := by
      rintro p ⟨-, hp1, hp2⟩
      choose n hn using hp1
      choose m hm using fun j => latt_repr' (hp2 j)
      have hsplit : iotaA r p = (((torA r p.2.1).1, (torA r p.2.1).2), (0 : Fin 2 × Fin r → ℂ)) +
          MStarCopy.qv (abA r p.2.2) := by
        rw [iotaA_apply]; ext <;> simp [MStarCopy.qv]
      rw [hsplit, tor_decomp, qv_decomp p.2.2 m hm]
      refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_))
        (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun e _ =>
          Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inr ⟨_, genA_mem j e, rfl⟩)))
      · change MStarCopy.tor1 i (p.2.1 ((tEA r).symm (Sum.inl i))) ∈ _
        rw [hn, tor1_int]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
      · change MStarCopy.tor2 i (p.2.1 ((tEA r).symm (Sum.inr i))) ∈ _
        rw [hn, tor2_int]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
    have hper : iotaA r v ∈ G.per := by
      have : Submodule.span ℚ ((PerA : AddSubgroup (TanA 0 (d1A r) r)) : Set (TanA 0 (d1A r) r)) ≤
          G.per.comap g := by
        rw [Submodule.span_le]; intro p hp; exact hmem p hp
      exact this hvper
    have h0 := hV (iotaA r v) hvV hper (by rw [iotaA_apply, htor, map_zero])
    exact (iotaA r).injective (by rw [h0, map_zero])

end LSG.W88
