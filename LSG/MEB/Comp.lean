/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SliceDim
import StrongSix.M2.Component

/-!
# Components, cosets and relevant radicals (A4.2, α; templates `ME.{WustCoset, MainAbChain, MainAbSlice,
MainAbAux}`)

* Generic (any block structure): `exists_compl_hfun`, **`hfun_inter_ge`** (two ideals and a non-zero-divisor).
* `vanish_union`, `mem_vanish_biUnion`, `exists_sep_proj`, `not_gtransl_subset`; `gtransl_eq_of_sub_mem`,
  **`exists_reps_G`**, `coords_nscal_univ`, `biUnion_gtransl_cover`.
* `relI L = I(Z(L))`, `le_relI`, `relI_mono`, `relI_le_vanish_zero`; **`exists_relevant_prime`**;
  **`component_rel`** (Roy §8.4.1).
* `point_of_lsl_notMem`, `mem_vanishP_biUnion`, `vanishP_biUnion_eq_inf`; **`hdim_vanishP_cosets_le`**,
  **`hfun_sum_cosets_P`** (S5).
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le FLE_mono mul_mem_FLE)

namespace LSG.MEB

section Generic

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  (β : σ → ι) (D : ι → ℕ)

/-- A complement of `J ∩ F_t` in `F_t`, of dimension `H(J; t)`. -/
theorem exists_compl_hfun (J : Ideal (MvPolynomial σ ℂ)) (t : ℕ) :
    ∃ E : Submodule ℂ (MvPolynomial σ ℂ), E ≤ FLE ℂ β (t • D) ∧
      finrank ℂ E = hfun β D ℂ J t ∧ ∀ x ∈ E, x ∈ J → x = 0 := by
  set F := FLE ℂ β (t • D)
  set p := J.restrictScalars ℂ ⊓ F
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  have : FiniteDimensional ℂ p := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional ℂ ↥(q ⊓ F) := Submodule.finiteDimensional_of_le inf_le_right
  have hpE : p ⊓ (q ⊓ F) = ⊥ := eq_bot_iff.mpr fun x hx =>
    hq.disjoint.le_bot ⟨hx.1, hx.2.1⟩
  have hpE' : p ⊔ (q ⊓ F) = F := by
    rw [← sup_inf_assoc_of_le q (inf_le_right : p ≤ F), hq.sup_eq_top, top_inf_eq]
  refine ⟨q ⊓ F, inf_le_right, ?_, fun x hx hxJ => ?_⟩
  · have := Submodule.finrank_sup_add_finrank_inf_eq p (q ⊓ F)
    rw [hpE, hpE', finrank_bot] at this
    change _ = finrank ℂ F - finrank ℂ p
    omega
  · exact (Submodule.mem_bot ℂ).mp (hpE ▸ ⟨⟨hxJ, hx.2⟩, hx⟩)

/-- **Two ideals and a non-zero-divisor.** -/
theorem hfun_inter_ge {J₁ J₂ : Ideal (MvPolynomial σ ℂ)} {B : MvPolynomial σ ℂ} {c : ℕ}
    (hB : B ∈ FLE ℂ β (c • D)) (hBJ : B ∈ J₁) (hB₂ : ∀ x, B * x ∈ J₂ → x ∈ J₂)
    {t₁ t₂ t : ℕ} (h₁ : t₁ ≤ t) (h₂ : t₂ + c ≤ t) :
    hfun β D ℂ J₁ t₁ + hfun β D ℂ J₂ t₂ ≤ hfun β D ℂ (J₁ ⊓ J₂) t := by
  classical
  obtain ⟨E₁, hE₁F, hE₁d, hE₁J⟩ := exists_compl_hfun β D J₁ t₁
  obtain ⟨E₂, hE₂F, hE₂d, hE₂J⟩ := exists_compl_hfun β D J₂ t₂
  set F := FLE ℂ β (t • D)
  have : FiniteDimensional ℂ E₁ := Submodule.finiteDimensional_of_le hE₁F
  have : FiniteDimensional ℂ E₂ := Submodule.finiteDimensional_of_le hE₂F
  let Ψ : (E₁ × E₂) →ₗ[ℂ] MvPolynomial σ ℂ :=
    E₁.subtype ∘ₗ LinearMap.fst ℂ E₁ E₂ + LinearMap.mulLeft ℂ B ∘ₗ E₂.subtype ∘ₗ
      LinearMap.snd ℂ E₁ E₂
  have hΨ : ∀ x, Ψ x = (x.1 : MvPolynomial σ ℂ) + B * x.2 := fun x => rfl
  have hzero : ∀ x, Ψ x ∈ J₁ ⊓ J₂ → x = 0 := by
    intro x hx
    rw [hΨ] at hx
    have h1 : (x.1 : MvPolynomial σ ℂ) = 0 := hE₁J _ x.1.2 (by
      have := J₁.sub_mem hx.1 (J₁.mul_mem_right (x.2 : MvPolynomial σ ℂ) hBJ)
      rwa [add_sub_cancel_right] at this)
    rw [h1, zero_add] at hx
    have h2 : (x.2 : MvPolynomial σ ℂ) = 0 := hE₂J _ x.2.2 (hB₂ _ hx.2)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot ℂ).mpr (hzero x (by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _))
  set U := LinearMap.range Ψ
  have hUF : U ≤ F := by
    rintro _ ⟨x, rfl⟩
    rw [hΨ]
    refine Submodule.add_mem _ (FLE_mono ℂ β (fun i => ?_) (hE₁F x.1.2)) ?_
    · simp only [Pi.smul_apply, smul_eq_mul]; exact Nat.mul_le_mul_right _ h₁
    · have := mul_mem_FLE ℂ hB (hE₂F x.2.2)
      rw [← add_smul] at this
      exact FLE_mono ℂ β (fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact Nat.mul_le_mul_right _ (by omega)) this
  set X := (J₁ ⊓ J₂).restrictScalars ℂ ⊓ F
  have : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUF
  have : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le inf_le_right
  have hUX : U ⊓ X = ⊥ := eq_bot_iff.mpr fun y ⟨⟨x, hx⟩, hyJ, _⟩ => by
    subst hx; rw [hzero x hyJ, map_zero]; exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U X
  rw [hUX, finrank_bot, add_zero] at hsum
  have hle : finrank ℂ ↥(U ⊔ X) ≤ finrank ℂ F := Submodule.finrank_mono (sup_le hUF inf_le_right)
  have hU : finrank ℂ U = hfun β D ℂ J₁ t₁ + hfun β D ℂ J₂ t₂ := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, hE₁d, hE₂d]
  have hX : hfun β D ℂ (J₁ ⊓ J₂) t = finrank ℂ F - finrank ℂ X := rfl
  rw [hX, ← hU]
  omega

end Generic

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

theorem vanish_union (E₁ E₂ : Set (GPt d₀ d₁ B)) :
    vanish (E₁ ∪ E₂) = vanish E₁ ⊓ vanish E₂ := by
  ext P
  simp only [Submodule.mem_inf, mem_vanish, Set.mem_union]
  exact ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun h g hg => hg.elim (h.1 g) (h.2 g)⟩

theorem mem_vanish_biUnion {ι : Type*} (s : Finset ι) (C : ι → Set (GPt d₀ d₁ B))
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} : P ∈ vanish (⋃ a ∈ s, C a) ↔ ∀ a ∈ s, P ∈ vanish (C a) := by
  simp only [mem_vanish, Set.mem_iUnion]
  exact ⟨fun h a ha g hg => h g ⟨a, ha, hg⟩, fun h g ⟨a, ha, hg⟩ => h a ha g hg⟩

/-- A polynomial vanishing on a Zariski-closed `C₂` but not on `C₁ ⊄ C₂`. -/
theorem exists_sep_proj {C₁ C₂ : Set (GPt d₀ d₁ B)} (hC₂ : IsZClosed C₂)
    (h : ¬ C₁ ⊆ C₂) : ∃ f ∈ vanish C₂, f ∉ vanish C₁ := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [← zeros_vanish hC₂]
  intro g hg P hP lam
  exact mem_vanish.mp (hcon P hP) g hg lam


/-- Distinct cosets of a subgroup are not nested. -/
theorem not_gtransl_subset {V : Set (GPt d₀ d₁ B)} (hVs : IsSubgroupG V)
    {a b : GPt d₀ d₁ B} (hab : a - b ∉ V) : ¬ gtransl a V ⊆ gtransl b V := by
  intro h
  have : a ∈ gtransl b V := h ⟨0, hVs.zero_mem, zero_add a⟩
  exact hab (mem_gtransl.mp this)

theorem gtransl_eq_of_sub_mem {H : Set (GPt d₀ d₁ B)} (hH : IsSubgroupG H)
    {a b : GPt d₀ d₁ B} (h : a - b ∈ H) : gtransl a H = gtransl b H := by
  ext x
  rw [mem_gtransl, mem_gtransl]
  constructor
  · intro hx
    have := hH.add_mem _ hx _ h
    rwa [show x - a + (a - b) = x - b by abel] at this
  · intro hx
    have := hH.add_mem _ hx _ (hH.neg_mem _ h)
    rwa [show x - b + -(a - b) = x - a by abel] at this

/-- **Distinct coset representatives.** -/
theorem exists_reps_G {H : Set (GPt d₀ d₁ B)} (hH : IsSubgroupG H)
    (T' : Finset (GPt d₀ d₁ B)) :
    ∃ Rs ⊆ T', (⋃ a ∈ Rs, gtransl a H) = (⋃ a ∈ T', gtransl a H) ∧
      ∀ a ∈ Rs, ∀ b ∈ Rs, a ≠ b → a - b ∉ H := by
  classical
  induction T' using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | insert t T' ht ih =>
    obtain ⟨Rs, hsub, hU, hd⟩ := ih
    by_cases hc : ∃ a ∈ Rs, t - a ∈ H
    · obtain ⟨a, ha, hat⟩ := hc
      refine ⟨Rs, hsub.trans (Finset.subset_insert _ _), ?_, hd⟩
      rw [Finset.set_biUnion_insert, ← hU, gtransl_eq_of_sub_mem hH hat]
      exact (Set.union_eq_right.mpr
        (Set.subset_iUnion₂ (s := fun a (_ : a ∈ Rs) => gtransl a H) a ha)).symm
    · push_neg at hc
      refine ⟨insert t Rs, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, hU]
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · exact absurd rfl hab
          · exact hc b hb'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · intro hmem
            apply hc a ha'
            have := hH.neg_mem _ hmem
            rwa [neg_sub] at this
          · exact hd a ha' b hb' hab

theorem coords_nscal_univ {α : Alpha B} {g : GPt d₀ d₁ B} (hg : ∀ k, lval α g k ≠ 0)
    (lam : Fin m → ℂˣ) : coords g (nscal Finset.univ α g lam) = nrm α g := by
  unfold nrm
  congr 1
  funext k
  apply Units.ext
  rw [nscal_mem (Finset.mem_univ k) (hg k)]
  simp [hg k]

open Classical in
/-- Translates of `GV` as unions of cosets of `H ⊆ GV`. -/
theorem biUnion_gtransl_cover {H GV : Set (GPt d₀ d₁ B)}
    (hGV : IsSubgroupG GV) (hHGV : H ⊆ GV) (Rc : Finset (GPt d₀ d₁ B))
    (hRc : ∀ c ∈ Rc, c ∈ GV) (hcov : GV ⊆ ⋃ c ∈ Rc, gtransl c H) (X : Finset (GPt d₀ d₁ B)) :
    (⋃ a ∈ X, gtransl a GV) = ⋃ b ∈ (X ×ˢ Rc).image (fun p => p.2 + p.1), gtransl b H := by
  classical
  ext x
  simp only [Set.mem_iUnion, mem_gtransl, Finset.mem_image, Finset.mem_product, exists_prop]
  constructor
  · rintro ⟨a, ha, hxa⟩
    have := hcov hxa
    simp only [Set.mem_iUnion, mem_gtransl, exists_prop] at this
    obtain ⟨c, hc, hxc⟩ := this
    refine ⟨c + a, ⟨(a, c), ⟨ha, hc⟩, rfl⟩, ?_⟩
    rwa [show x - (c + a) = x - a - c by abel]
  · rintro ⟨b, ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩, hx⟩
    refine ⟨a, ha, ?_⟩
    have := hGV.add_mem _ (hHGV hx) _ (hRc c hc)
    rwa [show x - (c + a) + c = x - a by abel] at this

variable (d₀ d₁ B) in
/-- The **relevant radical** `I(Z(L))`. -/
noncomputable def relI (L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  vanish (zeros (L : Set _) : Set (GPt d₀ d₁ B))

theorem le_relI (L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) : L ≤ relI d₀ d₁ B L :=
  fun P hP => mem_vanish.mpr fun _ hg lam => hg P hP lam

theorem relI_mono {L L' : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (h : L ≤ L') :
    relI d₀ d₁ B L ≤ relI d₀ d₁ B L' :=
  vanish_antitone fun _ hg P hP lam => hg P (h hP) lam

theorem relI_le_vanish_zero {L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)}
    (h : L ≤ vanish ({0} : Set (GPt d₀ d₁ B))) :
    relI d₀ d₁ B L ≤ vanish ({0} : Set (GPt d₀ d₁ B)) :=
  vanish_antitone (Set.singleton_subset_iff.mpr (mem_zeros_iff_le_vanish.mpr h))

/-- **A relevant prime over `relI L` of the same Hilbert dimension.** -/
theorem exists_relevant_prime (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (hne : relI d₀ d₁ B L ≠ ⊤) :
    ∃ p : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ), p.IsPrime ∧ relI d₀ d₁ B L ≤ p ∧
      (hdata blk D ℂ p).1 = (hdata blk D ℂ (relI d₀ d₁ B L)).1 ∧
      vanish (zeros (p : Set _) : Set (GPt d₀ d₁ B)) = p := by
  obtain ⟨p, hp, hJp, hdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  have := hp
  have hmin := StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD hJp hdim
  obtain ⟨ps, hps, hcov⟩ := exists_components (d₀ := d₀) (d₁ := d₁) (B := B)
    (H := zeros (L : Set (MvPolynomial (Var d₀ d₁ B) ℂ)))
  obtain ⟨p', hp'ps, hp'p⟩ := hcov p hp hJp
  obtain ⟨hp'pr, hJp', hp'v⟩ := hps p' hp'ps
  have he : p' = p := le_antisymm hp'p (hmin.2 ⟨hp'pr, hJp'⟩ hp'p)
  subst he
  exact ⟨p', hp, hJp, hdim, hp'v⟩

/-- **Roy's component step** (relevant form): if `V` is irreducible Zariski-closed with
`hdim I(V) = hdim (relI L)`, the translates `h + V ⊆ Z(L)` are finitely many, so
`{h | h + V ⊆ Z(L)}` is covered by finitely many cosets of `stabG V`. -/
theorem component_rel (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime)
    (hdim : (hdata blk D ℂ (vanish V)).1 = (hdata blk D ℂ (relI d₀ d₁ B L)).1) :
    ∃ R : Finset (GPt d₀ d₁ B),
      {h | gtransl h V ⊆ zeros (L : Set _)} ⊆ ⋃ a ∈ R, gtransl a (stabG V) := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top vanish_empty
  set Z := {h | gtransl h V ⊆ zeros (L : Set (MvPolynomial (Var d₀ d₁ B) ℂ))}
  let φ : GPt d₀ d₁ B → Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) := fun h =>
    vanish (gtransl h V)
  have hmin : ∀ h ∈ Z, φ h ∈ (relI d₀ d₁ B L).minimalPrimes := by
    intro h hh
    have := vanish_gtransl_isPrime hp h
    refine StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD (vanish_antitone hh) ?_
    rw [hdim_vanish_gtransl D hVne h, hdim]
  have hfinM : (relI d₀ d₁ B L).minimalPrimes.Finite :=
    (relI d₀ d₁ B L).finite_minimalPrimes_of_isNoetherianRing
  have hfin : (φ '' Z).Finite := hfinM.subset (by rintro _ ⟨h, hh, rfl⟩; exact hmin h hh)
  have hrep : ∀ q ∈ φ '' Z, ∃ a ∈ Z, φ a = q := fun q hq => hq
  choose! rep hrepZ hrepφ using hrep
  refine ⟨hfin.toFinset.image rep, fun h hh => ?_⟩
  have hq : φ h ∈ φ '' Z := ⟨h, hh, rfl⟩
  set a := rep (φ h)
  have haφ : φ a = φ h := hrepφ _ hq
  have hV' : gtransl a V = gtransl h V :=
    vanish_injOn (isZClosed_gtransl hV a) (isZClosed_gtransl hV h) haφ
  simp only [Set.mem_iUnion]
  refine ⟨a, Finset.mem_image.mpr ⟨φ h, (Set.Finite.mem_toFinset _).mpr hq, rfl⟩, ?_⟩
  rw [mem_gtransl]
  intro v hv
  have : v + h ∈ gtransl a V := hV' ▸ ⟨v, hv, rfl⟩
  obtain ⟨u, hu, hu'⟩ := this
  have e : h - a + v = u := by
    have := congrArg (· - a) hu'
    simp only [add_sub_cancel_right] at this
    rw [this]; abel
  rw [e]; exact hu

/-! ### Sliced unions of cosets -/

/-- A point with all `ℓ_k(rep) ≠ 0`. -/
theorem point_of_lsl_notMem {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E) :
    ∃ g ∈ E, ∀ k, lval α g k ≠ 0 := by
  classical
  have hprod := prod_lsl_notMem (s := Finset.univ) hp fun k _ => hℓ k
  by_contra hcon
  push_neg at hcon
  apply hprod
  refine mem_vanish.mpr fun g hg lam => ?_
  obtain ⟨k, hk⟩ := hcon g hg
  rw [map_prod, Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_coords_lsl, hk, mul_zero])]

theorem mem_vanishP_biUnion {s : Finset (Fin m)} {α : Alpha B} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPt d₀ d₁ B)) {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanishP s α (⋃ a ∈ R, C a) ↔ ∀ a ∈ R, P ∈ vanishP s α (C a) := by
  simp only [mem_vanishP, Set.mem_iUnion]
  constructor
  · intro h a ha g hg hs lam; exact h g ⟨a, ha, hg⟩ hs lam
  · rintro h g ⟨a, ha, hg⟩ hs lam; exact h a ha g hg hs lam

theorem vanishP_biUnion_eq_inf {s : Finset (Fin m)} {α : Alpha B} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPt d₀ d₁ B)) :
    vanishP s α (⋃ a ∈ R, C a) = R.inf fun a => vanishP s α (C a) := by
  ext P
  rw [mem_vanishP_biUnion]
  simp only [Finset.inf_eq_iInf, Submodule.mem_iInf]

/-- **Sliced unions of translates drop the dimension by `m`.** -/
theorem hdim_vanishP_cosets_le (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) {α : Alpha B}
    {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt d₀ d₁ B)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hne : vanishP Finset.univ α (⋃ a ∈ R, gtransl a V) ≠ ⊤) :
    (hdata blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V))).1 + m ≤
      (hdata blk D ℂ (vanish V)).1 := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top vanish_empty
  obtain ⟨q, hq, hJq, hqdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  rw [vanishP_biUnion_eq_inf] at hJq hqdim
  obtain ⟨a, ha, haq⟩ := (Ideal.IsPrime.inf_le' (hp := hq)).mp hJq
  have hpa := vanish_gtransl_isPrime hp a
  obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa (hα a ha)
  have hdrop := hdim_vanishP_add_le D hD hpa (hα a ha) hg₀ hs₀ Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, hdim_vanish_gtransl D hVne a] at hdrop
  have hle := hdata_le_of_le blk D ℂ haq hq.ne_top
  rw [vanishP_biUnion_eq_inf]
  rcases hle with h | ⟨h, -⟩ <;> omega

/-- **The sliced coset count** (S5). -/
theorem hfun_sum_cosets_P (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Alpha B)
    {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt d₀ d₁ B)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) t ≤
      hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (t + c) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih (fun x hx k => hα x (Finset.mem_insert_of_mem hx) k)
      fun x hx y hy hxy =>
        hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hα' := hα a (Finset.mem_insert_self a s)
    have hpa := vanish_gtransl_isPrime hp a
    obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa hα'
    have hPa := vanishP_isPrime (s := Finset.univ) hpa (fun k _ => hα' k) hg₀ (fun k _ => hs₀ k)
    -- multihomogeneous separators
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanishP Finset.univ α (gtransl a V) := by
      intro b hb
      have hns := hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
      obtain ⟨x, hxa, hxb⟩ := Set.not_subset.mp hns
      obtain ⟨Q, ⟨hQb, d, hd⟩, hQx⟩ := exists_homogVanish_ne (isZClosed_gtransl hV b) hxb
      refine ⟨Q, hQb, fun hQa => ?_⟩
      have := hom_mem_vanish_of_mem_vanishP hpa hα' hd hQa
      exact hQx 1 (mem_vanish.mp this x hxa 1)
    choose! f hfb hfa using hsep
    set B := ∏ b ∈ s, f b
    have hBs : B ∈ vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) := by
      rw [mem_vanishP_biUnion]
      intro b hb
      rw [show B = f b * ∏ x ∈ s.erase b, f x from (Finset.mul_prod_erase s f hb).symm]
      exact Ideal.mul_mem_right _ _ (vanish_le_vanishP _ α _ (hfb b hb))
    have hBa : B ∉ vanishP Finset.univ α (gtransl a V) := by
      intro h
      obtain ⟨b, hb, hfb'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPa)).mp h
      exact hfa b hb hfb'
    have hnzd : ∀ x, B * x ∈ vanishP Finset.univ α (gtransl a V) →
        x ∈ vanishP Finset.univ α (gtransl a V) := fun x hx =>
      (hPa.mem_or_mem hx).resolve_left hBa
    have hBdeg := StrongSix.M2.mem_FLE_totalDegree blk D ℂ hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : vanishP Finset.univ α (⋃ x ∈ insert a s, gtransl x V) =
        vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) ⊓ vanishP Finset.univ α (gtransl a V) := by
      ext P
      simp only [Submodule.mem_inf, mem_vanishP_biUnion, Finset.forall_mem_insert]
      exact and_comm
    have h1 := hfun_inter_ge blk D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, Finset.sum_insert ha]
    have := hc t
    omega

end LSG.MEB
