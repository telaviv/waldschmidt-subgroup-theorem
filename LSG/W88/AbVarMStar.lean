/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyAbVar
import LSG.W88.AbVarSub
import LSG.W88.K11Lin
import LSG.W88.K5dRoy

/-!
# A6: lean_mstar's `Thm11KappaA` for `Jac(y⁵ = x(1 − x))` from `HyperplaneKappaAbVar`

* **`hkOn_transport`** (generic): `HyperplaneKappaOnLsg G' good'` (lean_lsg's binder order) transfers to
  lean_mstar's `HyperplaneKappaOn G good` along a linear isomorphism `ι : Vs ≃ Vt` that preserves algebraic vectors,
  maps `G.lam` into `ι(span_ℚ L)` for a subgroup `L = G'.lam`, `G.per` into `ι(G'.per)`, has the same `d₁, d₂`,
  maps nonzero members of `G'.sub` into `G.sub`, and `good` into `good'` (pattern of `V5d.hyperplaneKappa_of_iso`,
  with `hyperplaneKappaOn_of_scale`'s common denominators).
* **`iotaA r`**: `TanA 0 (2·|ι|) r ≃ TF ι (Fin 2 × Fin r → ℂ)`, `ι = Fin r × Fin φ(5)`: the toric part reindexed, and
  `q (s, j) = 5(−1)^s z_j s` on the `A`-part (lean_mstar's periods are `ζ^{(s+1)e} perA5 s`, lean_lsg's
  `perVec e s = cJ s ζ^{(s+1)e}`, and `perA5 s = 5(−1)^s cJ s`: **`perA5_scale`**).
* **`thm11KappaA5_of`**: `HyperplaneKappaAbVar → MStarCopy.Thm11KappaA 5 2 (fun s => s + 1) perA5 0`.
-/

open Complex Module

namespace LSG.W88

open LSG.JacAn LSG.JacAn.Beta

/-! ### Generic transport -/

/-- **Transport of the `§5d` hypothesis along a linear isomorphism.** -/
theorem hkOn_transport {Vs Vt : Type*} [AddCommGroup Vs] [Module ℂ Vs] [Module ℚ Vs] [IsScalarTower ℚ ℂ Vs]
    [FiniteDimensional ℂ Vs] [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt] [IsScalarTower ℚ ℂ Vt]
    (G' : MStarCopy.GroupModel Vs) (good' : Submodule ℂ Vs → Prop) (h : HyperplaneKappaOnLsg G' good')
    (G : MStarCopy.GroupModel Vt) (good : Submodule ℂ Vt → Prop) (ι : Vs ≃ₗ[ℂ] Vt)
    (halg : ∀ v, G.alg v → G'.alg (ι.symm v))
    (L : AddSubgroup Vs) (hL : G'.lam = (L : Set Vs))
    (hlam : ∀ y ∈ G.lam, ι.symm y ∈ Submodule.span ℚ (L : Set Vs))
    (hper : ∀ v ∈ G.per, ι.symm v ∈ G'.per)
    (hd1 : G.d₁ = G'.d₁) (hd2 : G.d₂ = G'.d₂)
    (hsub : ∀ S, G'.sub S → S ≠ ⊥ → G.sub (S.map ι.toLinearMap))
    (hgood : ∀ V, good V → good' (V.comap ι.toLinearMap)) :
    MStarCopy.HyperplaneKappaOn G good := by
  classical
  intro V W m y hg hV hWV hWrat hy hineq
  set f : Vt →ₗ[ℚ] Vs := ι.symm.toLinearMap.restrictScalars ℚ with hf
  have hfinj : Function.Injective f := ι.symm.injective
  have hfin : finrank ℂ Vs = finrank ℂ Vt := ι.finrank_eq
  have : FiniteDimensional ℂ Vt := LinearEquiv.finiteDimensional ι
  set V' := V.comap ι.toLinearMap with hV'
  set W' := W.comap ι.toLinearMap with hW'
  have hfV' : finrank ℂ V' = finrank ℂ V := by
    rw [hV', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hfW' : finrank ℂ W' = finrank ℂ W := by
    rw [hW', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hW'rat : G'.Rational W' := by
    obtain ⟨S, hS, rfl⟩ := hWrat
    refine ⟨ι.symm '' S, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩; exact halg s (hS s hs)
    · rw [hW', Submodule.comap_equiv_eq_map_symm, Submodule.map_span]; rfl
  obtain ⟨M, hM, hMy⟩ := exists_common_nsmul (S := (L : Set Vs)) (fun i => hlam _ (hy i).2)
  rw [AddSubgroup.closure_eq] at hMy
  set y' : Fin m → Vs := fun i => M • ι.symm (y i) with hy'
  have hy'V : ∀ i, y' i ∈ V' ∧ y' i ∈ G'.lam := fun i => by
    refine ⟨?_, by rw [hL]; exact hMy i⟩
    change ι (M • ι.symm (y i)) ∈ V
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    exact V.toAddSubgroup.nsmul_mem (hy i).1 M
  have hspan : Submodule.span ℚ (Set.range y') = (Submodule.span ℚ (Set.range y)).map f := by
    rw [hy', span_range_nsmul hM, Submodule.map_span, ← Set.range_comp]; rfl
  have hrk : finrank ℚ (Submodule.span ℚ (Set.range y')) = finrank ℚ (Submodule.span ℚ (Set.range y)) := by
    rw [hspan, K5d.finrank_map_inj hfinj]
  have hκ : finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per) ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ G'.per) := by
    rw [← K5d.finrank_map_inj hfinj (Submodule.span ℚ (Set.range y) ⊓ G.per)]
    have hfd : FiniteDimensional ℚ ↥(Submodule.span ℚ (Set.range y')) :=
      FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
    have : FiniteDimensional ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ G'.per) :=
      Submodule.finiteDimensional_of_le inf_le_left
    refine Submodule.finrank_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hspan ▸ ⟨u, hu.1, rfl⟩, hper u hu.2⟩
  have hdimW : finrank ℂ W ≤ finrank ℂ V := Submodule.finrank_mono hWV
  obtain ⟨S', hS', hS'0, hS'V⟩ := h V' W' m y' (by rw [hfV', hfin]; exact hV) (Submodule.comap_mono hWV)
    hW'rat (hgood V hg) hy'V (by
      rw [hrk, hfW', hfin, ← hd1, ← hd2]
      have h1 : (finrank ℂ Vt : ℤ) - 1 - finrank ℂ W ≥ 0 := by omega
      have h2 : (finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per) : ℤ) ≤
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ G'.per) := by exact_mod_cast hκ
      nlinarith)
  refine ⟨S'.map ι.toLinearMap, hsub S' hS' hS'0, ?_, ?_⟩
  · intro h0
    apply hS'0
    rw [← Submodule.map_bot ι.toLinearMap] at h0
    exact Submodule.map_injective_of_injective ι.injective h0
  · rintro _ ⟨x, hx, rfl⟩; exact hS'V hx

/-! ### Periods of `Jac(y⁵ = x(1 − x))`: the two normalisations -/

/-- The scaling `q (s, j) = cA s · z_j s`. -/
def cA (s : Fin 2) : ℂ := 5 * (-1) ^ (s : ℕ)

lemma cA_ne_zero (s : Fin 2) : cA s ≠ 0 := by
  unfold cA; exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))

lemma isAlgebraic_cA (s : Fin 2) : IsAlgebraic ℚ (cA s) := by
  fin_cases s
  · simpa [cA] using (isAlgebraic_int (R := ℚ) (A := ℂ) 5)
  · simpa [cA] using (isAlgebraic_int (R := ℚ) (A := ℂ) (-5))

lemma isAlgebraic_cA_inv (s : Fin 2) : IsAlgebraic ℚ (cA s)⁻¹ := (isAlgebraic_cA s).inv

/-- **`perA5 s = 5(−1)^s cJ s`**, hence lean_mstar's period `ζ^{(s+1)e} perA5 s` is `cA s · perVec e s`. -/
theorem perA5_scale (e : ℕ) (s : Fin 2) :
    MStarCopy.zetaN 5 ^ (((s : ℕ) + 1) * e) * MStarCopy.perA5 s = cA s * perVec e s := by
  have hz : MStarCopy.zetaN 5 = LSG.JacAn.Beta.zetaN 5 := rfl
  have hb : ∀ a b, MStarCopy.betaG a b = LSG.JacAn.Beta.betaG a b := fun _ _ => rfl
  rw [perVec_eq, MStarCopy.perA5, hz, hb, cJ]
  have hB := betaG_eq (s : ℕ)
  push_cast at hB ⊢
  rw [hB, pow_mul]
  unfold cA
  have h5 : ((-1 : ℂ) ^ (s : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-(LSG.JacAn.Beta.zetaN 5 ^ ((s : ℕ) + 1)) ^ e *
    (1 - LSG.JacAn.Beta.zetaN 5 ^ ((s : ℕ) + 1)) * betaIntegral (((s : ℂ) + 1) / 5) (((s : ℂ) + 1) / 5)) * h5

/-- `perVec e ∈ latt` for every `e` (`ζ⁵ = 1`, `1 + ζ + ⋯ + ζ⁴ = 0` coordinatewise). -/
theorem perVec_mem_latt (e : ℕ) : perVec e ∈ latt := by
  have hmem : ∀ e : Fin 4, perVec (e : ℕ) ∈ latt := fun e => AddSubgroup.subset_closure ⟨e, rfl⟩
  have hroot : ∀ j : Fin 2, IsPrimitiveRoot (LSG.JacAn.Beta.zetaN 5 ^ ((j : ℕ) + 1)) 5 := fun j =>
    (zetaN_prim 5 (by norm_num)).pow_of_coprime ((j : ℕ) + 1) (by fin_cases j <;> decide)
  have hper5 : ∀ e, perVec (e + 5) = perVec e := fun e => by
    funext j; rw [perVec_eq, perVec_eq, pow_add, (hroot j).pow_eq_one, mul_one]
  have h4 : perVec 4 = -(perVec 0 + perVec 1 + perVec 2 + perVec 3) := by
    funext j
    simp only [Pi.neg_apply, Pi.add_apply, perVec_eq]
    have hs := (hroot j).geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
    linear_combination cJ j * hs
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    by_cases he : e < 4
    · exact hmem ⟨e, he⟩
    · by_cases h4' : e = 4
      · subst h4'; rw [h4]
        exact neg_mem (add_mem (add_mem (add_mem (hmem 0) (hmem 1)) (hmem 2)) (hmem 3))
      · obtain ⟨k, rfl⟩ : ∃ k, e = k + 5 := ⟨e - 5, by omega⟩
        rw [hper5]; exact ih k (by omega)

/-- Lattice points are integer combinations of the four periods. -/
lemma latt_repr' {v : Fin 2 → ℂ} (hv : v ∈ latt) : ∃ n : Fin 4 → ℤ, v = ∑ e : Fin 4, n e • perVec (e : ℕ) := by
  unfold latt at hv
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.mp hv
  exact ⟨n, hn⟩

/-! ### The isomorphism -/

/-- The toric index set `ι = Fin r × Fin φ(5)`. -/
abbrev ιA (r : ℕ) := Fin r × Fin (Nat.totient 5)

/-- `d₁ = 2|ι|`. -/
abbrev d1A (r : ℕ) : ℕ := 2 * Fintype.card (ιA r)

/-- `Fin (2|ι|) ≃ ι ⊕ ι`. -/
noncomputable def tEA (r : ℕ) : Fin (d1A r) ≃ ιA r ⊕ ιA r :=
  (finCongr (two_mul _)).trans (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm))

/-- The toric part. -/
noncomputable def torA (r : ℕ) : (Fin (d1A r) → ℂ) →ₗ[ℂ] (ιA r → ℂ) × (ιA r → ℂ) where
  toFun x := (fun i => x ((tEA r).symm (Sum.inl i)), fun i => x ((tEA r).symm (Sum.inr i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `ℚ`-version of `torA`. -/
noncomputable def torAQ (r : ℕ) : (Fin (d1A r) → ℚ) →ₗ[ℚ] (ιA r → ℚ) × (ιA r → ℚ) where
  toFun x := (fun i => x ((tEA r).symm (Sum.inl i)), fun i => x ((tEA r).symm (Sum.inr i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `A`-part. -/
noncomputable def abA (r : ℕ) : (Fin r → Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 × Fin r → ℂ) where
  toFun z sj := cA sj.1 * z sj.2 sj.1
  map_add' _ _ := by funext sj; simp [mul_add]
  map_smul' _ _ := by funext sj; simp; ring

/-- **The isomorphism** `TanA 0 d₁ r ≃ TF ι (Fin 2 × Fin r → ℂ)`. -/
noncomputable def iotaA (r : ℕ) : TanA 0 (d1A r) r ≃ₗ[ℂ] MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ) where
  toFun p := (torA r p.2.1, abA r p.2.2)
  invFun v := (0, fun k => Sum.elim v.1.1 v.1.2 (tEA r k), fun j s => (cA s)⁻¹ * v.2 (s, j))
  map_add' p q := by simp [map_add]
  map_smul' c p := by simp [map_smul]
  left_inv p := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ ?_)
    · funext k
      change Sum.elim _ _ (tEA r k) = p.2.1 k
      rcases h : tEA r k with i | i
      · change p.2.1 ((tEA r).symm (Sum.inl i)) = p.2.1 k
        rw [← h, Equiv.symm_apply_apply]
      · change p.2.1 ((tEA r).symm (Sum.inr i)) = p.2.1 k
        rw [← h, Equiv.symm_apply_apply]
    · funext j s
      change (cA s)⁻¹ * (cA s * p.2.2 j s) = p.2.2 j s
      rw [← mul_assoc, inv_mul_cancel₀ (cA_ne_zero s), one_mul]
  right_inv v := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext i; simp [torA]
    · funext i; simp [torA]
    · funext sj
      change cA sj.1 * ((cA sj.1)⁻¹ * v.2 (sj.1, sj.2)) = v.2 sj
      rw [← mul_assoc, mul_inv_cancel₀ (cA_ne_zero _), one_mul]

lemma iotaA_symm_apply (r : ℕ) (v : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) :
    (iotaA r).symm v = (0, fun k => Sum.elim v.1.1 v.1.2 (tEA r k), fun j s => (cA s)⁻¹ * v.2 (s, j)) := rfl

lemma iotaA_apply (r : ℕ) (p : TanA 0 (d1A r) r) : iotaA r p = (torA r p.2.1, abA r p.2.2) := rfl

/-! ### Generators -/

section Gen

variable {r : ℕ}

/-- lean_mstar's period generator `[ζ^e]γ` in copy `j`. -/
noncomputable def genA (j : Fin r) (e : ℕ) : Fin 2 × Fin r → ℂ :=
  fun p => if p.2 = j then MStarCopy.zetaN 5 ^ (((p.1 : ℕ) + 1) * e) * MStarCopy.perA5 p.1 else 0

lemma genA_mem (j : Fin r) (e : ℕ) : genA j e ∈ MStarCopy.perAgen 5 2 (fun s : Fin 2 => (s : ℕ) + 1)
    MStarCopy.perA5 := ⟨(j, e), rfl⟩

lemma abA_single (j : Fin r) (e : ℕ) : abA r (Pi.single j (perVec e)) = genA j e := by
  funext p
  simp only [abA, LinearMap.coe_mk, AddHom.coe_mk, genA]
  by_cases hj : p.2 = j
  · subst hj; simp [perA5_scale]
  · simp [Pi.single_apply, hj]

lemma symm_tor (v : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) (k : Fin (d1A r)) :
    ((iotaA r).symm v).2.1 k = Sum.elim v.1.1 v.1.2 (tEA r k) := rfl

lemma symm_A (v : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) : ((iotaA r).symm v).2.2 =
    fun j s => (cA s)⁻¹ * v.2 (s, j) := rfl

lemma symm_qv_genA (j : Fin r) (e : ℕ) :
    (iotaA r).symm (MStarCopy.qv (genA j e)) = (0, 0, Pi.single j (perVec e)) := by
  rw [← abA_single]
  apply (iotaA r).injective
  rw [LinearEquiv.apply_symm_apply, iotaA_apply]
  simp [MStarCopy.qv, map_zero]

lemma single_perVec_mem (j : Fin r) (e : ℕ) : ∀ j', (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ) j' ∈ latt := by
  intro j'
  by_cases h : j' = j
  · subst h; simpa using perVec_mem_latt e
  · simp [Pi.single_apply, h, latt.zero_mem]

/-- `ι⁻¹` of a vector with zero `Q`-part and toric entries satisfying `P`. -/
lemma symm_toric_mem (v : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) (hv : v.2 = 0) (P : ℂ → Prop)
    (h1 : ∀ i, P (v.1.1 i)) (h2 : ∀ i, P (v.1.2 i)) :
    (∀ k, P (((iotaA r).symm v).2.1 k)) ∧ ((iotaA r).symm v).2.2 = 0 := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [symm_tor v]
    rcases tEA r k with i | i
    · exact h1 i
    · exact h2 i
  · rw [symm_A, hv]; funext j s; simp

end Gen

/-! ### The main theorem -/

section Main

variable {r : ℕ} (b : Fin r → ℂ)

/-- The torus part of a subgroup is `torSub` of the rational annihilator. -/
lemma torusA_eq (U : Submodule ℚ (Fin (d1A r) → ℚ)) :
    (torusLie U).map (torA r) = MStarCopy.torSub ((K11.annQ U).map (torAQ r)) := by
  have h1 : torusLie U = K11.annC U := rfl
  rw [h1, K11.annC_eq_cspan, K11.cspan_eq, Submodule.map_span, MStarCopy.torSub, Submodule.map_coe,
    Set.image_image, Set.image_image]
  rfl

lemma dotL_thetaA_abA (z : Fin r → Fin 2 → ℂ) :
    MStarCopy.dotL (MStarCopy.thetaA 2 0 b) (abA r z) = 5 * ∑ j, b j * z j 0 := by
  change ∑ p : Fin 2 × Fin r, MStarCopy.thetaA 2 0 b p * (cA p.1 * z p.2 p.1) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.mul_sum]
  simp [MStarCopy.thetaA, cA]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma indep_of_adapted (hb : MStarCopy.IsAdaptedBasisD (MStarCopy.zetaN 5) (Nat.totient 5) b) :
    LinearIndependent ℚ (fun p : Fin r × Fin 4 => zetaN 5 ^ (p.2 : ℕ) * b p.1) := by
  have h4 : 4 = Nat.totient 5 := by decide
  have := hb.indep.comp (Equiv.prodCongr (Equiv.refl _) (finCongr h4)) (Equiv.injective _)
  convert this using 1
  funext p
  simp only [Function.comp, MStarCopy.thetaD, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map,
    finCongr_apply, Fin.val_cast]
  rfl

lemma tor_decomp (f1 f2 : ιA r → ℂ) :
    (((f1, f2), (0 : Fin 2 × Fin r → ℂ)) : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) =
      ∑ i, MStarCopy.tor1 i (f1 i) + ∑ i, MStarCopy.tor2 i (f2 i) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i; simp [MStarCopy.tor1, MStarCopy.tor2, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext i; simp [MStarCopy.tor1, MStarCopy.tor2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
      Pi.single_apply]
  · simp [MStarCopy.tor1, MStarCopy.tor2, Prod.snd_sum]

lemma qv_decomp (z : Fin r → Fin 2 → ℂ) (n : Fin r → Fin 4 → ℤ)
    (hn : ∀ j, z j = ∑ e : Fin 4, n j e • perVec (e : ℕ)) :
    (MStarCopy.qv (abA r z) : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) =
      ∑ j, ∑ e : Fin 4, n j e • MStarCopy.qv (genA j e) := by
  have hz : z = ∑ j, ∑ e : Fin 4, n j e • (Pi.single j (perVec (e : ℕ)) : Fin r → Fin 2 → ℂ) := by
    funext j' s
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single j']
    · rw [hn j']; simp [Finset.sum_apply]
    · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
    · simp
  have hlin : ∀ w : Fin 2 × Fin r → ℂ, (MStarCopy.qv w : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) =
      (LinearMap.inr ℂ _ _) w := fun w => rfl
  simp only [hlin]
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_zsmul, map_zsmul, abA_single]

lemma tor1_int (i : ιA r) (n : ℤ) :
    (MStarCopy.tor1 i (2 * Real.pi * I * n) : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) =
      n • MStarCopy.tor1 i (2 * Real.pi * I) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext k; by_cases hk : k = i
    · subst hk; simp [MStarCopy.tor1]; ring
    · simp [MStarCopy.tor1, Pi.single_apply, hk]
  · simp [MStarCopy.tor1]
  · simp [MStarCopy.tor1]

lemma tor2_int (i : ιA r) (n : ℤ) :
    (MStarCopy.tor2 i (2 * Real.pi * I * n) : MStarCopy.TF (ιA r) (Fin 2 × Fin r → ℂ)) =
      n • MStarCopy.tor2 i (2 * Real.pi * I) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp [MStarCopy.tor2]
  · funext k; by_cases hk : k = i
    · subst hk; simp [MStarCopy.tor2]; ring
    · simp [MStarCopy.tor2, Pi.single_apply, hk]
  · simp [MStarCopy.tor2]

/-- **lean_mstar's `Thm11KappaA` for `Jac(y⁵ = x(1 − x))`** from lean_lsg's `§5d` statement. -/
theorem thm11KappaA5_of (h : HyperplaneKappaAbVar) :
    MStarCopy.Thm11KappaA 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0 := by
  intro r b hb
  set G := MStarCopy.gmA 5 2 (fun s : Fin 2 => (s : ℕ) + 1) MStarCopy.perA5 0 b with hG
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
    have key : Submodule.span ℚ (MStarCopy.lamGen (ι := ιA r) (MStarCopy.perAgen 5 2
        (fun s : Fin 2 => (s : ℕ) + 1) MStarCopy.perA5)) ≤
        (Submodule.span ℚ ((LamA : AddSubgroup (TanA 0 (d1A r) r)) : Set (TanA 0 (d1A r) r))).comap f := by
      rw [Submodule.span_le]
      intro v hv
      refine Submodule.subset_span ?_
      change (iotaA r).symm v ∈ LamA
      rcases hv with (⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨q, ⟨⟨j, e⟩, rfl⟩, rfl⟩
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
      · change (iotaA r).symm (MStarCopy.qv (genA j e)) ∈ LamA
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
  · -- subgroups
    rintro S ⟨H, rfl⟩ hS0
    refine ⟨(K11.annQ H.U).map (torAQ r), H.t.map (abA r), ?_, ?_⟩
    · by_cases ht : H.t = ⊥
      · left; rw [ht, Submodule.map_bot]
      · right
        obtain ⟨z, hz, hne⟩ := lam_ne_zero_of_abelian H.t_ab ht (indep_of_adapted b hb)
        refine ⟨abA r z, ⟨z, hz, rfl⟩, ?_⟩
        rw [dotL_thetaA_abA]
        exact mul_ne_zero (by norm_num) hne
    · ext ⟨x, q⟩
      rw [← torusA_eq]
      constructor
      · rintro ⟨p, hp, hpx⟩
        obtain ⟨-, hpU, hpt⟩ := hp
        change iotaA r p = (x, q) at hpx
        rw [iotaA_apply] at hpx
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpx
        exact ⟨⟨_, hpU, rfl⟩, ⟨_, hpt, rfl⟩⟩
      · rintro ⟨⟨u, hu, rfl⟩, ⟨z, hz, rfl⟩⟩
        exact ⟨(0, u, z), ⟨Submodule.zero_mem _, hu, hz⟩, rfl⟩
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

end Main

end LSG.W88
