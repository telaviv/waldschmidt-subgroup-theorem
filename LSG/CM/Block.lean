/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.CM.Mult
import LSG.CM.Coord

/-!
# `T(B^♮)` for an abelian subvariety `B` of a power `E^p` of one CM curve

`E` has CM data `(L, α)` (`CMData`: `Λ = ω₁ℤ[α]`, `ζ(αz) = ᾱζ(z)`). For an abelian tangent
`t ⊂ ℂ^p` (`IsAbelianTangent`):
* `fst_mem`, `snd_mem`: for every lattice point `λ ∈ t`, `(λ, 0)` and `(0, η(λ))` lie in
  `perTanId t` (from `(λ, η(λ))` and `(αλ, ᾱη(λ))`, `α ≠ ᾱ`). Since `λ = ω₁ a` and
  `η(λ) = η(ω₁) ā` with `a ∈ ℤ[α]^p`, this gives **`perTanRat_block`** (`T(B^♮)` is `ℚ̄`-rational);
* **`liftAlg_block`** (algebraic `g₂, g₃`): every algebraic point `z ∈ t` of `B` lifts to an
  algebraic point `(z, w)` of `B^♮`. With a chart `ι` of `t` and a basis `λ₁, …, λ_s` of lattice
  points, `A = (λ_l(ι k)/ω₁) ∈ ℤ[α]^{s×s}` is invertible and `Δ z_j = Σ_k β_{jk} z_{ι k}`
  (`Δ = det A`, `β = (adj A-combinations) ∈ ℤ[α]`); then `w_j = Δ̄⁻¹ Σ_k β̄_{jk} ζ(z_{ι k})` works
  by   the semilinearity of `ζ` modulo `ℚ̄` (`sum_mem`), and lies in the span of the `η(λ_l)`.
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.W88 LSG.W88.Vec

namespace LSG.CM

/-- On an abelian tangent, the lattice points span `t` over `ℂ`. -/
lemma span_lat_eq {m : ℕ} {Ls : Fin m → PeriodPair} {t : Submodule ℂ (Fin m → ℂ)}
    (hab : IsAbelianTangent Ls t) :
    Submodule.span ℂ {z | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice} = t := by
  apply le_antisymm
  · rw [Submodule.span_le]; exact fun z hz => hz.1
  · intro z hz
    have : z ∈ t.restrictScalars ℝ := hz
    rw [hab] at this
    exact Submodule.span_le_restrictScalars ℝ ℂ _ this

variable {p : ℕ} {L : PeriodPair} {α : ℂ}

lemma etaV_smul (hd : CMData L α) {l : Fin p → ℂ} (hl : ∀ j, l j ∈ L.lattice) :
    etaV (fun _ => L) (α • l) = α⁻¹ • etaV (fun _ => L) l := by
  funext j
  simp only [etaV, Pi.smul_apply, smul_eq_mul]
  exact eta_mul L hd.unit (hl j)

lemma etaV_eq (hd : CMData L α) {l : Fin p → ℂ} (hl : ∀ j, l j ∈ L.lattice) (j : Fin p) :
    etaV (fun _ => L) l j = starRingEnd ℂ (l j / L.ω₁) * eta L L.ω₁ :=
  hd.eta_eq_conj (hl j)

variable {t : Submodule ℂ (Fin p → ℂ)}

lemma gen_mem {l : Fin p → ℂ} (hlt : l ∈ t) (hl : ∀ j, l j ∈ L.lattice) :
    (l, etaV (fun _ => L) l) ∈ perTanId (fun _ => L) t :=
  Submodule.subset_span ⟨hlt, hl, rfl⟩

/-- `(λ, 0) ∈ T(B^♮)` for a lattice point `λ ∈ t`. -/
theorem fst_mem (hd : CMData L α) {l : Fin p → ℂ} (hlt : l ∈ t) (hl : ∀ j, l j ∈ L.lattice) :
    (l, 0) ∈ perTanId (fun _ => L) t := by
  have hl' : ∀ j, (α • l) j ∈ L.lattice := fun j => hd.unit.mul_mem _ (hl j)
  have h1 := gen_mem (t.smul_mem α hlt) hl'
  have h2 := gen_mem (L := L) hlt hl
  rw [etaV_smul hd hl] at h1
  have : (l, (0 : Fin p → ℂ)) = (α - α⁻¹)⁻¹ • ((α • l, α⁻¹ • etaV (fun _ => L) l) -
      α⁻¹ • (l, etaV (fun _ => L) l)) := by
    have hne := hd.ne_inv
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.fst_sub, smul_sub, smul_smul, ← sub_smul]
      rw [← mul_sub, inv_mul_cancel₀ hne, one_smul]
    · simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))

/-- `(0, η(λ)) ∈ T(B^♮)` for a lattice point `λ ∈ t`. -/
theorem snd_mem (hd : CMData L α) {l : Fin p → ℂ} (hlt : l ∈ t) (hl : ∀ j, l j ∈ L.lattice) :
    (0, etaV (fun _ => L) l) ∈ perTanId (fun _ => L) t := by
  have : ((0 : Fin p → ℂ), etaV (fun _ => L) l) = (l, etaV (fun _ => L) l) - (l, 0) := by simp
  rw [this]
  exact Submodule.sub_mem _ (gen_mem hlt hl) (fst_mem hd hlt hl)

/-- **`T(B^♮)` is `ℚ̄`-rational** for every abelian subvariety of `E^p`. -/
theorem perTanRat_block (hd : CMData L α) : PerTanRat (fun _ : Fin p => L) := by
  intro t _
  set P := perTanId (fun _ : Fin p => L) t
  have hω := hd.ω₁_ne
  have hη := hd.eta_one_ne
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro ⟨l, e⟩ ⟨hlt, hl, he⟩
    simp only at hlt hl he
    subst he
    have h1 : (L.ω₁⁻¹ • l, (0 : Fin p → ℂ)) ∈ P := by
      have := Submodule.smul_mem P L.ω₁⁻¹ (fst_mem hd hlt hl)
      simpa using this
    have h2 : ((0 : Fin p → ℂ), (eta L L.ω₁)⁻¹ • etaV (fun _ => L) l) ∈ P := by
      have := Submodule.smul_mem P (eta L L.ω₁)⁻¹ (snd_mem hd hlt hl)
      simpa using this
    have ha1 : AlgPair (L.ω₁⁻¹ • l, (0 : Fin p → ℂ)) := by
      refine ⟨fun j => ?_, fun j => isAlgebraic_zero⟩
      simpa [inv_mul_eq_div] using hd.isAlgebraic_div (hl j)
    have ha2 : AlgPair ((0 : Fin p → ℂ), (eta L L.ω₁)⁻¹ • etaV (fun _ => L) l) := by
      refine ⟨fun j => isAlgebraic_zero, fun j => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, etaV_eq hd hl j]
      rw [mul_comm, mul_assoc, mul_inv_cancel₀ hη, mul_one]
      exact isAlgebraic_conj (hd.isAlgebraic_div (hl j))
    have : (l, etaV (fun _ => L) l) = L.ω₁ • (L.ω₁⁻¹ • l, (0 : Fin p → ℂ)) +
        eta L L.ω₁ • ((0 : Fin p → ℂ), (eta L L.ω₁)⁻¹ • etaV (fun _ => L) l) := by
      refine Prod.ext ?_ ?_
      · simp [smul_smul, mul_inv_cancel₀ hω]
      · simp [smul_smul, mul_inv_cancel₀ hη]
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨h1, ha1⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨h2, ha2⟩))
  · rw [Submodule.span_le]; exact fun w hw => hw.1

/-! ### Lifting algebraic points -/

section Lift

variable (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
include hg₂ hg₃

/-- **Algebraic points of `B` lift to algebraic points of `B^♮`** (`E^p`, `E` with CM). -/
theorem liftAlg_block (hd : CMData L α) : LiftAlg (fun _ : Fin p => L) := by
  classical
  intro t hab z hz hgood
  set R := multRing hg₂ hg₃
  set P := perTanId (fun _ : Fin p => L) t
  have hω := hd.ω₁_ne
  have hη := hd.eta_one_ne
  obtain ⟨c⟩ := nonempty_chart t
  set s := finrank ℂ t
  set G : Set (Fin p → ℂ) := {l | l ∈ t ∧ ∀ j, l j ∈ L.lattice}
  have hGt : Submodule.span ℂ G = t := span_lat_eq hab
  obtain ⟨b, hbG, hspan, hli⟩ := exists_linearIndependent ℂ G
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = s := by
    have := finrank_span_set_eq_card hli
    rw [hspan, hGt, Set.toFinset_card] at this
    exact this.symm
  let e : Fin s ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  let lam : Fin s → Fin p → ℂ := fun k => (e k : Fin p → ℂ)
  have hlam : ∀ k, lam k ∈ G := fun k => hbG (e k).2
  have hlin : LinearIndependent ℂ lam := hli.comp e e.injective
  have hrange : Set.range lam = b := by
    ext v; constructor
    · rintro ⟨k, rfl⟩; exact (e k).2
    · intro hv; exact ⟨e.symm ⟨v, hv⟩, by simp [lam]⟩
  have hspan' : Submodule.span ℂ (Set.range lam) = t := by rw [hrange, hspan, hGt]
  -- the matrix `A`
  let A : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun k l => lam l (c.ι k) / L.ω₁
  have hAR : ∀ k l, A k l ∈ R := fun k l => div_mem hg₂ hg₃ hd ((hlam l).2 _)
  let A' : Matrix (Fin s) (Fin s) R := Matrix.of fun k l => ⟨A k l, hAR k l⟩
  have hA' : R.subtype.mapMatrix A' = A := by ext k l; rfl
  have hadj : ∀ l k, A.adjugate l k ∈ R := by
    intro l k
    rw [← hA', ← RingHom.map_adjugate]
    exact (A'.adjugate l k).2
  have hdetR : A.det ∈ R := by
    rw [← hA', ← RingHom.map_det]; exact (A'.det).2
  have hAv : ∀ v : Fin s → ℂ, ∀ k, (∑ l, v l • lam l) (c.ι k) = L.ω₁ * (A.mulVec v) k := by
    intro v k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, A,
      Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hy : (∑ l, v l • lam l) ∈ t :=
      Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hlam l).1
    have hpy : ((proj c.ι).comp t.subtype) ⟨∑ l, v l • lam l, hy⟩ = 0 := by
      funext k
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.funLeft_apply,
        Pi.zero_apply]
      rw [hAv v k, hv]; simp
    have : (⟨∑ l, v l • lam l, hy⟩ : t) = 0 := c.bij.1 (hpy.trans (map_zero _).symm)
    have hy0 : ∑ l, v l • lam l = 0 := congrArg Subtype.val this
    exact hv0 (funext fun l => Fintype.linearIndependent_iff.mp hlin v hy0 l)
  -- coordinates of `z`
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan'.symm ▸ hz :
    z ∈ Submodule.span ℂ (Set.range lam))
  set Δ := A.det
  let β : Fin p → Fin s → ℂ := fun j k => ∑ l, A.adjugate l k * (lam l j / L.ω₁)
  have hβR : ∀ j k, β j k ∈ R := fun j k =>
    Subring.sum_mem _ fun l _ => mul_mem (hadj l k) (div_mem hg₂ hg₃ hd ((hlam l).2 j))
  have hAγ : A.mulVec γ = fun k => z (c.ι k) / L.ω₁ := by
    funext k
    rw [← hγ, hAv γ k]; field_simp
  have hΔγ : ∀ l, Δ * γ l = ∑ k, A.adjugate l k * (z (c.ι k) / L.ω₁) := by
    intro l
    have h1 : A.adjugate.mulVec (A.mulVec γ) = Δ • γ := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 l
    rw [hAγ] at h2
    simpa [Matrix.mulVec, dotProduct] using h2.symm
  have hkey : ∀ j, ∑ k, β j k * z (c.ι k) = Δ * z j := by
    intro j
    have hzj : z j = ∑ l, γ l * lam l j := by
      rw [← hγ]; simp [Finset.sum_apply]
    calc ∑ k, β j k * z (c.ι k) = ∑ l, ∑ k, A.adjugate l k * (z (c.ι k) / L.ω₁) * lam l j := by
          simp only [β, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
          field_simp
      _ = ∑ l, Δ * γ l * lam l j := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hΔγ l, Finset.sum_mul]
      _ = Δ * z j := by
          rw [hzj, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
  -- the lift
  have hΔc : starRingEnd ℂ Δ ≠ 0 := by rwa [map_ne_zero]
  let w : Fin p → ℂ := fun j =>
    (starRingEnd ℂ Δ)⁻¹ * ∑ k, starRingEnd ℂ (β j k) * zeta L (z (c.ι k))
  refine ⟨w, ?_, fun j => ?_⟩
  · -- `(z, w) ∈ T(B^♮)`
    have hz0 : (z, (0 : Fin p → ℂ)) ∈ P := by
      have : (z, (0 : Fin p → ℂ)) = ∑ l, γ l • (lam l, (0 : Fin p → ℂ)) := by
        rw [← hγ]; ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (fst_mem hd (hlam l).1 (hlam l).2)
    let cf : Fin s → ℂ := fun l => (starRingEnd ℂ Δ)⁻¹ * (eta L L.ω₁)⁻¹ *
      ∑ k, zeta L (z (c.ι k)) * starRingEnd ℂ (A.adjugate l k)
    have hw : w = ∑ l, cf l • etaV (fun _ => L) (lam l) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, etaV_eq hd (hlam _).2 j, w, cf, β,
        map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      field_simp
    have h0w : ((0 : Fin p → ℂ), w) ∈ P := by
      have : ((0 : Fin p → ℂ), w) = ∑ l, cf l • ((0 : Fin p → ℂ), etaV (fun _ => L) (lam l)) := by
        rw [hw]; ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (snd_mem hd (hlam l).1 (hlam l).2)
    have : (z, w) = (z, (0 : Fin p → ℂ)) + ((0 : Fin p → ℂ), w) := by simp
    rw [this]; exact Submodule.add_mem _ hz0 h0w
  · -- `w − ζ(z)` is algebraic
    have hgood' : ∀ k ∈ (Finset.univ : Finset (Fin s)), AlgPtE L (z (c.ι k)) :=
      fun k _ => hgood (c.ι k)
    obtain ⟨-, h1⟩ := sum_mem hg₂ hg₃ Finset.univ (β j) (fun k => z (c.ι k))
      (fun k _ => hβR j k) hgood'
    obtain ⟨-, h2⟩ := hdetR.2 (z j) (hgood j)
    rw [hkey j] at h1
    have hX := h2.sub h1
    have : w j - zetaV (fun _ => L) z j = (starRingEnd ℂ Δ)⁻¹ *
        ((zeta L (Δ * z j) - starRingEnd ℂ Δ * zeta L (z j)) -
          (zeta L (Δ * z j) - ∑ k, starRingEnd ℂ (β j k) * zeta L (z (c.ι k)))) := by
      simp only [w, zetaV]
      field_simp
      ring
    rw [Pi.sub_apply, this]
    exact (isAlgebraic_conj hdetR.1).inv.mul hX

end Lift

end LSG.CM
