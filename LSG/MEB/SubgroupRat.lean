/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupDim
import LSG.MEB.Rational
import LSG.ME.ProductRat
import LSG.Subgroups.TorusLattice

/-!
# Product decomposition, step 1: `π_A(lieAlg H)` is rational (A4.3, β′)

Port of ME's `ProductRat` to abstract blocks (transcendence-degree count, with `hdim_H0` in place of `trdeg_H0`).

* `piA`, `inAbL`, `rhoL`, `varL`: the projection to the abelian coordinates, its section, the linear coordinates.
* `span_perAb`; **`isRatSub_of_linPart`**: a complex subspace that is the linear part of a closed subgroup containing
  `perAb` is rational (`LSG.Subgroups.span_linPart_inter_lattice`).
* **`lieAlg_zcl_map_piA`**: for `P = π_A(lieAlg H)`, the Zariski closure `B'` of `exp(0 × 0 × P)` has Lie algebra
  exactly `0 × 0 × P`. (A transcendence basis of coordinates of `B'⁰` and the linear coordinates of `lieAlg H ∩ ker π_A`
  are algebraically independent modulo `I(H⁰)`, so `dim lieAlg B' + dim (lieAlg H ∩ ker π_A) ≤ dim lieAlg H`.)
* **`isRatSub_map_piA`**: `IsRatSub (perAb B) (π_A(lieAlg H))`.
-/

open MvPolynomial Module Set
open StrongSix.M2 (hdata)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Linear maps -/

/-- The projection `π_A : Tan → ∏ ℂ^{g_k}`. -/
def piA : Tan d₀ d₁ B →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) := (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)

@[simp] theorem piA_apply (u : Tan d₀ d₁ B) : piA u = u.2.2 := rfl

/-- `z ↦ (0, 0, z)`. -/
def inAbL : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] Tan d₀ d₁ B := (LinearMap.inr ℂ _ _).comp (LinearMap.inr ℂ _ _)

@[simp] theorem inAbL_apply (z : ∀ k, Fin (B k).g → ℂ) : (inAbL z : Tan d₀ d₁ B) = (0, 0, z) := rfl

theorem inAbL_injective : Function.Injective (inAbL : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] Tan d₀ d₁ B) :=
  fun _ _ h => congrArg (fun u : Tan d₀ d₁ B => u.2.2) h

/-- The linear coordinates `(x, y)` as one vector of `ℂ^{d₀ + d₁}`. -/
def rhoL : Tan d₀ d₁ B →ₗ[ℂ] (Fin (d₀ + d₁) → ℂ) where
  toFun u i := Sum.elim u.1 u.2.1 (finSumFinEquiv.symm i)
  map_add' u v := by
    funext i; simp only [Pi.add_apply]; cases (finSumFinEquiv.symm i) <;> rfl
  map_smul' c u := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply]; cases (finSumFinEquiv.symm i) <;> rfl

theorem rhoL_apply (u : Tan d₀ d₁ B) (i : Fin (d₀ + d₁)) :
    rhoL u i = Sum.elim u.1 u.2.1 (finSumFinEquiv.symm i) := rfl

/-- The linear variables `x i`, `y j`. -/
def varL : Fin d₀ ⊕ Fin d₁ → Var d₀ d₁ B := Sum.elim Var.x Var.y

/-! ### Rationality of linear parts -/

theorem span_perAb : Submodule.span ℝ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  rw [← Finset.univ_sum_single z]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : z k ∈ Submodule.span ℝ ((B k).per : Set (Fin (B k).g → ℂ)) := (B k).per_span ▸ Submodule.mem_top
  have hle : Submodule.map (LinearMap.single ℝ (fun k => Fin (B k).g → ℂ) k)
      (Submodule.span ℝ ((B k).per : Set (Fin (B k).g → ℂ))) ≤
      Submodule.span ℝ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨ω, hω, rfl⟩ k' -
    by_cases h : k' = k
    · subst h; simpa using hω
    · simp [Pi.single_apply, h, zero_mem]
  exact hle ⟨z k, hk, rfl⟩

/-- **Linear parts are rational**: a complex subspace that is the linear part of a closed subgroup containing
`perAb` is `perAb`-rational. -/
theorem isRatSub_of_linPart {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {S : AddSubgroup (∀ k, Fin (B k).g → ℂ)}
    (hS : IsClosed (S : Set (∀ k, Fin (B k).g → ℂ))) (hLS : (perAb B : Set (∀ k, Fin (B k).g → ℂ)) ⊆ S)
    (ht : ∀ z, z ∈ t ↔ ∀ s : ℝ, s • z ∈ S) : IsRatSub (perAb B) t := by
  let L : Submodule ℤ (∀ k, Fin (B k).g → ℂ) := (perAb B).toIntSubmodule
  haveI : DiscreteTopology L := discreteTopology_perAb
  have hspan : Submodule.span ℝ (L : Set (∀ k, Fin (B k).g → ℂ)) = ⊤ := span_perAb
  have h := LSG.Subgroups.span_linPart_inter_lattice L S hspan hS hLS
  have hlin : t.restrictScalars ℝ = LSG.Subgroups.linPart S := by
    ext z; exact ht z
  unfold IsRatSub
  rw [hlin, ← h]
  congr 1
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, SetLike.mem_coe]
  exact and_congr (by simp only [Submodule.restrictScalars_mem, LSG.Subgroups.mem_linPart]; exact (ht z).symm)
    Iff.rfl

/-! ### Step 1 -/

variable {H : Set (GPt d₀ d₁ B)}

/-- **The Zariski closure of `exp(0 × 0 × π_A(lieAlg H))` has Lie algebra `0 × 0 × π_A(lieAlg H)`.** -/
theorem lieAlg_zcl_map_piA (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (((lieAlg hH).map piA).map inAbL : Submodule ℂ (Tan d₀ d₁ B)) =
      lieAlg (zcl_isSubgroup (isSubgroupG_expG_image (((lieAlg hH).map piA).map inAbL))) := by
  classical
  set T := lieAlg hH with hTdef
  set P := T.map (piA (d₀ := d₀) (d₁ := d₁) (B := B)) with hPdef
  set PA := P.map (inAbL (d₀ := d₀) (d₁ := d₁) (B := B))
  set S : Set (GPt d₀ d₁ B) := expG d₀ d₁ B '' (PA : Set (Tan d₀ d₁ B))
  have hB : IsSubgroupG (zcl S) := zcl_isSubgroup (isSubgroupG_expG_image PA)
  have hBc : IsZClosed (zcl S) := isZClosed_zcl S
  have hPB : PA ≤ lieAlg hB := by
    intro v hv c
    rw [mem_Htil]
    exact subset_zcl S ⟨c • v, PA.smul_mem c hv, rfl⟩
  have hSB : vanish S ≤ vanish (H0 hB) := by
    rw [← vanish_zcl S]; exact vanish_antitone (H0_subset hB hBc)
  -- a transcendence basis of coordinates on `B⁰`
  haveI := vanish_H0_isPrime hB
  obtain ⟨ι, _, g, -, hb, hcard⟩ := LSG.ME.exists_coord_transcendenceBasis (vanish (H0 hB))
  have hindB : ∀ Q : MvPolynomial ι ℂ, rename g Q ∈ vanish (H0 hB) → Q = 0 := by
    intro Q hQ
    refine (algebraicIndependent_iff.mp hb.1) Q ?_
    rw [← aeval_rename]
    exact (LSG.ME.aeval_genPt_eq_zero_iff _).mpr hQ
  have hSpt : ∀ g' ∈ S, g'.1 = 0 ∧ ∀ j, g'.ym j = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨rfl, fun j => Units.ext (by simp [expG_apply, expGf, GPt.ym, expU])⟩
  have hgE : ∀ i, ∃ k c, g i = Var.e k c := by
    intro i
    rcases hgi : g i with j | j | j | ⟨k, c⟩
    · exfalso
      have hm : rename g (X i) ∈ vanish (H0 hB) := hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [rename_X, hgi, eval_X, coords_x]; exact congrFun (hSpt g' hg').1 j)
      have := congrArg (eval fun _ => (1 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ vanish (H0 hB) := hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, coords_y, (hSpt g' hg').2 j]
        simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ vanish (H0 hB) := hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, coords_z, (hSpt g' hg').2 j]
        simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exact ⟨k, c, rfl⟩
  -- `T_L = T ∩ ker π_A` and its coordinates
  set f := (piA (d₀ := d₀) (d₁ := d₁) (B := B)).comp T.subtype
  have hrange : LinearMap.range f = P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  set K0 := LinearMap.ker f
  set f0 := (rhoL (d₀ := d₀) (d₁ := d₁) (B := B)).comp (T.subtype.comp K0.subtype)
  have hf0 : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hA : ((w : T) : Tan d₀ d₁ B).2.2 = 0 := LinearMap.mem_ker.mp w.2
    have hx : ∀ i, ((w : T) : Tan d₀ d₁ B).1 i = 0 := fun i => by
      have := congrFun hw (finSumFinEquiv (Sum.inl i))
      simpa [f0, rhoL_apply] using this
    have hy : ∀ j, ((w : T) : Tan d₀ d₁ B).2.1 j = 0 := fun j => by
      have := congrFun hw (finSumFinEquiv (Sum.inr j))
      simpa [f0, rhoL_apply] using this
    have : ((w : T) : Tan d₀ d₁ B) = 0 := Prod.ext (funext hx) (Prod.ext (funext hy) hA)
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ιL, -, hsurjL⟩ := LSG.ME.exists_coord_surj (LinearMap.range f0)
  have hr : finrank ℂ (LinearMap.range f0) = finrank ℂ K0 := LinearMap.finrank_range_of_inj hf0
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  -- the combined family of coordinates
  set σL := fun l => finSumFinEquiv.symm (ιL l)
  set e := Sum.elim (fun l => varL (B := B) (σL l)) g
  set s : Fin (finrank ℂ (LinearMap.range f0)) → Set ℂ :=
    fun l => Sum.elim (fun _ => univ) (fun _ => {0}ᶜ) (σL l)
  have hX : ∀ Q : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0))) ℂ,
      (∀ x ∈ Set.pi univ s, eval x Q = 0) → Q = 0 := by
    intro Q hQ
    refine funext_set s (fun l => ?_) fun x hx => by rw [hQ x hx, map_zero]
    change (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ) (σL l) : Set ℂ).Infinite
    cases σL l
    · exact Set.infinite_univ
    · exact (Set.finite_singleton 0).infinite_compl
  set Y : Set (ι → ℂ) := {y | ∃ v ∈ PA, ∃ lam : Fin m → ℂˣ, y = coords (expG d₀ d₁ B v) lam ∘ g}
  have hY : ∀ Q : MvPolynomial ι ℂ, (∀ y ∈ Y, eval y Q = 0) → Q = 0 := by
    intro Q hQ
    refine hindB Q (hSB (mem_vanish.mpr fun g' hg' lam => ?_))
    obtain ⟨v, hv, rfl⟩ := hg'
    rw [eval_rename]
    exact hQ _ ⟨v, hv, lam, rfl⟩
  haveI := vanish_H0_isPrime hH
  have hind : ∀ R : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0)) ⊕ ι) ℂ,
      rename e R ∈ vanish (H0 hH) → R = 0 := by
    intro R hRm
    refine LSG.ME.eq_zero_of_eval_elim hX hY fun x hx y hy => ?_
    obtain ⟨v, hv, lam, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
    set y' : Fin (finrank ℂ (LinearMap.range f0)) → ℂ := fun l =>
      Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j) (σL l)
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hsurjL y'
    have hwA : ((w : T) : Tan d₀ d₁ B).2.2 = 0 := LinearMap.mem_ker.mp w.2
    have hpt : Sum.elim x (coords (expG d₀ d₁ B (inAbL (piA u))) lam ∘ g) =
        coords (expG d₀ d₁ B (u + ((w : T) : Tan d₀ d₁ B))) lam ∘ e := by
      funext t
      cases t with
      | inl l =>
        have hl : Sum.elim ((w : T) : Tan d₀ d₁ B).1 ((w : T) : Tan d₀ d₁ B).2.1 (σL l) =
            Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j) (σL l) :=
          hw l
        have hxl : x l ∈ s l := hx l (Set.mem_univ l)
        change x l = coords (expG d₀ d₁ B (u + ((w : T) : Tan d₀ d₁ B))) lam (varL (σL l))
        simp only [s] at hxl
        generalize σL l = q at hl hxl ⊢
        cases q with
        | inl i =>
          change ((w : T) : Tan d₀ d₁ B).1 i = x l - u.1 i at hl
          change x l = u.1 i + ((w : T) : Tan d₀ d₁ B).1 i
          rw [hl]; ring
        | inr j =>
          change ((w : T) : Tan d₀ d₁ B).2.1 j = Complex.log (x l) - u.2.1 j at hl
          change x l ≠ 0 at hxl
          change x l = Complex.exp (u.2.1 j + ((w : T) : Tan d₀ d₁ B).2.1 j)
          rw [hl, add_sub_cancel, Complex.exp_log hxl]
      | inr i =>
        obtain ⟨k, c, hkc⟩ := hgE i
        simp only [Sum.elim_inr, Function.comp_apply, e, hkc, coords_e]
        have : (u + ((w : T) : Tan d₀ d₁ B)).2.2 k = u.2.2 k := by simp [hwA]
        simp only [expG_apply, expGf, piA_apply, inAbL_apply]
        rw [this]
    rw [hpt, ← eval_rename]
    exact mem_vanish.mp hRm _ (expG_mem_H0 hH (T.add_mem hu (w : T).2)) lam
  -- the count
  have hcount := LSG.ME.card_le_trdeg_of_indep (vanish (H0 hH)) e hind
  rw [← LSG.ME.hdim_eq_trdeg blk (fun _ => 1) (fun _ => le_rfl), hdim_H0 hH hc _ fun _ => le_rfl,
    Fintype.card_sum, Fintype.card_fin] at hcount
  have hι : Fintype.card ι = finrank ℂ (lieAlg hB) + m := by
    have := congrArg Cardinal.toNat hcard
    rwa [Cardinal.toNat_natCast, ← LSG.ME.hdim_eq_trdeg blk (fun _ => 1) (fun _ => le_rfl),
      hdim_H0 hB hBc _ fun _ => le_rfl] at this
  have hPA : finrank ℂ PA = finrank ℂ P :=
    (Submodule.equivMapOfInjective _ inAbL_injective P).finrank_eq.symm
  have hle : finrank ℂ (lieAlg hB) ≤ finrank ℂ PA := by
    have hK : finrank ℂ (LinearMap.ker f) = finrank ℂ K0 := rfl
    have hTT : finrank ℂ T = finrank ℂ (lieAlg hH) := rfl
    omega
  exact Submodule.eq_of_le_of_finrank_le hPB hle

/-- **Step 1: `π_A(lieAlg H)` is `perAb`-rational.** -/
theorem isRatSub_map_piA (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsRatSub (perAb B) ((lieAlg hH).map (piA (d₀ := d₀) (d₁ := d₁))) := by
  set P := (lieAlg hH).map (piA (d₀ := d₀) (d₁ := d₁) (B := B))
  set PA := P.map (inAbL (d₀ := d₀) (d₁ := d₁) (B := B))
  have hB := zcl_isSubgroup (isSubgroupG_expG_image PA)
  have hBc : IsZClosed (zcl (expG d₀ d₁ B '' (PA : Set (Tan d₀ d₁ B)))) := isZClosed_zcl _
  have heq : PA = lieAlg hB := lieAlg_zcl_map_piA hH hc
  let SA : AddSubgroup (∀ k, Fin (B k).g → ℂ) := (Htil hB).comap inAbL.toAddMonoidHom
  refine isRatSub_of_linPart (S := SA) ?_ ?_ fun z => ?_
  · exact (isClosed_Htil hB hBc).preimage (by fun_prop : Continuous fun z : (∀ k, Fin (B k).g → ℂ) =>
      ((0, 0, z) : Tan d₀ d₁ B))
  · intro ω hω
    exact Per_le_Htil hB ⟨rfl, fun i => ⟨0, by simp⟩, fun k => hω k (Set.mem_univ k)⟩
  · have h1 : z ∈ P ↔ inAbL z ∈ PA :=
      ⟨fun h => ⟨z, h, rfl⟩, fun ⟨z', hz', h⟩ => inAbL_injective h ▸ hz'⟩
    rw [h1, heq, mem_lieAlg_iff_real hB hBc]
    refine forall_congr' fun s => ?_
    change _ ↔ inAbL (s • z) ∈ Htil hB
    rw [show inAbL (s • z) = ((s : ℂ) • inAbL z : Tan d₀ d₁ B) by
      rw [← map_smul]; congr 1]

end LSG.MEB
