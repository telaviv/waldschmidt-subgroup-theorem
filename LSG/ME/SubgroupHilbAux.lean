import Mathlib
import StrongSix.M2.Veronese
import LSG.ME.Transl

/-!
# Auxiliary lemmas for the Hilbert lower bound (STAGE2 §5, item 6)

* `hfun_eq_finrank_quotient`: `hfun β D K J t = dim (FLE(tD) ⧸ (J ∩ FLE(tD)))`.
* **`exists_indep_lift`**: `hfun` many polynomials of `FLE(tD)` whose classes modulo `J` are
  linearly independent.
* `rename_mem_FLE`: renaming variables along a map of blocks preserves block-degree bounds.
* **`exists_coord_surj`**: a subspace `t ⊆ K^m` has `dim t` coordinates onto which it projects
  surjectively.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun S bdeg finrank_comap_subtype)

namespace LSG.ME

section HFun

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] {K : Type*}
  [Field K] (β : σ → ι) (D : ι → ℕ)

/-- The submodule `J ∩ FLE(tD)` of `FLE(tD)`. -/
noncomputable abbrev Nsub (J : Ideal (MvPolynomial σ K)) (t : ℕ) : Submodule K (FLE K β (t • D)) :=
  (J.restrictScalars K).comap (FLE K β (t • D)).subtype

theorem hfun_eq_finrank_quotient (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    hfun β D K J t = finrank K (FLE K β (t • D) ⧸ Nsub β D J t) := by
  have h1 := Submodule.finrank_quotient_add_finrank (Nsub β D J t)
  have h2 : finrank K (Nsub β D J t) = finrank K ↥(J.restrictScalars K ⊓ FLE K β (t • D)) := by
    rw [Nsub, finrank_comap_subtype, inf_comm]
  unfold hfun
  omega

/-- **Independent lifts.** -/
theorem exists_indep_lift (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    ∃ A : Fin (hfun β D K J t) → MvPolynomial σ K, (∀ i, A i ∈ FLE K β (t • D)) ∧
      ∀ c : Fin (hfun β D K J t) → K, ∑ i, c i • A i ∈ J → c = 0 := by
  classical
  set Q := FLE K β (t • D) ⧸ Nsub β D J t
  have hdim := hfun_eq_finrank_quotient β D J t
  let b := (Module.finBasis K Q).reindex (finCongr hdim.symm)
  choose A' hA' using fun i => Submodule.Quotient.mk_surjective (Nsub β D J t) (b i)
  refine ⟨fun i => (A' i : MvPolynomial σ K), fun i => (A' i).2, fun c hc => ?_⟩
  have h0 : ∑ i, c i • b i = 0 := by
    have hmem : (∑ i, c i • A' i : FLE K β (t • D)) ∈ Nsub β D J t := by
      show ((∑ i, c i • A' i : FLE K β (t • D)) : MvPolynomial σ K) ∈ J
      simpa using hc
    have := (Submodule.Quotient.mk_eq_zero (Nsub β D J t)).mpr hmem
    rw [← Submodule.mkQ_apply, map_sum] at this
    simpa [hA'] using this
  exact funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent c h0 i

end HFun

/-! ### Renaming -/

section Rename

variable {σ τ ι ι' : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
  [DecidableEq ι] [DecidableEq ι']
  [Fintype ι] {K : Type*} [Field K]

theorem rename_mem_FLE (e : σ → τ) {β : σ → ι} {β' : τ → ι'} (φ : ι → ι')
    (hφ : ∀ v, β' (e v) = φ (β v)) {D : ι → ℕ} {D' : ι' → ℕ}
    (hD : ∀ i', ∑ i, (if φ i = i' then D i else 0) ≤ D' i') {P : MvPolynomial σ K}
    (hP : P ∈ FLE K β D) : rename e P ∈ FLE K β' D' := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S β D := by
    rw [FLE, mem_restrictSupport_iff] at hP; exact hP hn
  have hmono : rename e (monomial n (P.coeff n)) =
      C (P.coeff n) * ∏ v, (X (e v) : MvPolynomial τ K) ^ n v := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_mul, map_prod, rename_C]
    simp [rename_X]
  rw [hmono]
  have hprod := StrongSix.M2.prod_mem_FLE' (K := K) (β := β') Finset.univ
    (fun v => (X (e v) : MvPolynomial τ K) ^ n v) (fun v => Pi.single (β' (e v)) (n v))
    fun v _ => by
      have := StrongSix.M2.pow_mem_FLE' (fle_X (K := K) (β := β') (e v)) (n v)
      refine StrongSix.M2.FLE_mono K β' (fun i => ?_) this
      simp [Pi.single_apply]
  have hle : (∑ v, (Pi.single (β' (e v)) (n v) : ι' → ℕ)) ≤ D' := by
    intro i'
    refine le_trans ?_ (hD i')
    simp only [Finset.sum_apply, Pi.single_apply, hφ]
    calc ∑ v, (if i' = φ (β v) then n v else 0)
        = ∑ i, ∑ v, (if φ i = i' then (if β v = i then n v else 0) else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_eq_single (β v) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
          simp [eq_comm]
      _ = ∑ i, (if φ i = i' then bdeg β n i else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp [bdeg]
      _ ≤ ∑ i, (if φ i = i' then D i else 0) :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> simp [hnS i]
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (StrongSix.M2.FLE_mono K β' hle hprod)

end Rename

/-! ### Coordinates on a subspace -/

/-- **Coordinates.** A subspace `t ⊆ K^m` projects onto `dim t` of the coordinates. -/
theorem exists_coord_surj {K : Type*} [Field K] {m : ℕ} (t : Submodule K (Fin m → K)) :
    ∃ ι : Fin (finrank K t) → Fin m, Function.Injective ι ∧
      ∀ y : Fin (finrank K t) → K, ∃ z ∈ t, ∀ l, z (ι l) = y l := by
  classical
  let f : Fin m → Module.Dual K t := fun j => (LinearMap.proj j).comp t.subtype
  have hspan : Submodule.span K (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    set v := (Module.evalEquiv K t).symm φ
    have hv : ∀ j, f j v = 0 := by
      intro j
      have : φ (f j) = 0 := hφ (Submodule.subset_span ⟨j, rfl⟩)
      rw [← (Module.evalEquiv K t).apply_symm_apply φ] at this
      simpa [v] using this
    have hv0 : v = 0 := by
      apply Subtype.ext
      funext j
      simpa [f] using hv j
    apply hφ0
    rw [← (Module.evalEquiv K t).apply_symm_apply φ]
    simp [show (Module.evalEquiv K t).symm φ = 0 from hv0]
  obtain ⟨κ, a, ha, hspan', hind⟩ := exists_linearIndependent' K f
  rw [hspan] at hspan'
  have hκfin : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = finrank K t := by
    have := finrank_span_eq_card hind
    rw [hspan', finrank_top, Subspace.dual_finrank_eq] at this
    exact this.symm
  let e := (Fintype.equivFin κ).trans (finCongr hcard)
  let ι : Fin (finrank K t) → Fin m := fun l => a (e.symm l)
  have hι : Function.Injective ι := fun l l' h => e.symm.injective (ha h)
  -- the projection is injective, hence surjective
  let p : t →ₗ[K] (Fin (finrank K t) → K) := LinearMap.pi fun l => f (ι l)
  have hpinj : Function.Injective p := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hb0 : ∀ x ∈ Set.range (f ∘ a), x z = 0 := by
      rintro _ ⟨k, rfl⟩
      have := congrFun hz (e k)
      simpa [p, ι] using this
    have hall : ∀ φ ∈ Submodule.span K (Set.range (f ∘ a)), φ z = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => exact hb0 x hx
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul c x _ hx => simp [hx]
    exact (forall_dual_apply_eq_zero_iff K z).mp fun φ => hall φ (hspan' ▸ Submodule.mem_top)
  have hpsurj : Function.Surjective p :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hpinj
  refine ⟨ι, hι, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hpsurj y
  exact ⟨z, z.2, fun l => by simpa [p, f] using congrFun hz l⟩

end LSG.ME
