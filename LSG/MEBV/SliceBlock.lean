/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.ModelIG
import LSG.MEB.SliceBlock
import StrongSix.M2.LCIBlocks

/-!
# One vector-extension block: the certificates B5 and B6 on a slice (M2.5 α; template `LSG.MEB.SliceBlock`)

Block-local facts in `ℂ[X_c, T_t]` for a block `b`, from its certificate fields only:

* **B6 (Hilbert upper bound), with linear forms.** `y_a = lformV (hilb_l a)` (`ylin`, `g + 2` of them).
  `hilb_hom`: every homogeneous `M` of degree `d ≥ max(hilb_deg, 1)` is `Σ_a y_a c_a` modulo `I` with `c_a`
  homogeneous of degree `d − 1`. `Std e` (`y^β M'`, `|β| = e`, `deg M' = n₁ − 1`): **`hom_mem_span_Std`**;
  `card_Std_le : #(Std e) ≤ (e+1)^(g+1) · n₁^(N+nT)`; **`mem_span_Std_slice`** (every linear form `ℓ`).
* **B5 (local complete intersection), `X`-only slices.** `lform α = Σ_c α_c X_c`, `slB α = I + (ℓ − 1)`;
  **`locGen_slB`**: `LocGen (slB α) (N + nT − (g + 1))` (the cover from the `X`-only `lci_cover`).
  `g_lt_N : g + 1 < N + nT`.
-/

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LSG.MEBV

/-! ### Generic lemmas (the rest are imported from `LSG.MEB.SliceBlock`) -/

/-- Multiplying by a linear form shifts homogeneous components. -/
theorem homogeneousComponent_lin_mul {σ : Type*} {ℓ : MvPolynomial σ ℂ} (hℓ : ℓ.IsHomogeneous 1)
    (p : MvPolynomial σ ℂ) {d : ℕ} (hd : 1 ≤ d) :
    homogeneousComponent d (ℓ * p) = ℓ * homogeneousComponent (d - 1) p := by
  have hX : ℓ ∈ homogeneousSubmodule σ ℂ 1 := (mem_homogeneousSubmodule 1 _).mpr hℓ
  have := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := homogeneousSubmodule σ ℂ)
    (b := p) hX hd
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply]
  exact this

theorem degree_eq_sum_univ' {σ : Type*} [Fintype σ] (s : σ →₀ ℕ) : s.degree = ∑ c, s c := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa using hc

theorem lformV_isHomogeneous {ι : Type*} [Fintype ι] (α : ι → ℂ) : (lformV α).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ c).C_mul _

namespace VBlock

variable (b : VBlock)

theorem gens_hom' : ∀ Q ∈ {Q | Q ∈ b.gens}, ∃ d, Q.IsHomogeneous d :=
  fun Q hQ => (b.gens_hom Q hQ).imp fun _ h => h.2

/-- The `a`-th linear form of the Hilbert certificate. -/
noncomputable def ylin (a : Fin (b.g + 2)) : MvPolynomial b.Idx ℂ := lformV (b.hilb_l a)

theorem ylin_isHomogeneous (a : Fin (b.g + 2)) : (b.ylin a).IsHomogeneous 1 :=
  lformV_isHomogeneous _

theorem comp_mem_blockI {P : MvPolynomial b.Idx ℂ} (hP : P ∈ b.blockI) (i : ℕ) :
    homogeneousComponent i P ∈ b.blockI :=
  LSG.MEB.homogeneousComponent_mem_span b.gens_hom' hP i

/-- The ideal `(y_0, …, y_{g+1})` of the Hilbert certificate (linear forms). -/
noncomputable def Yideal : Ideal (MvPolynomial b.Idx ℂ) :=
  Ideal.span (Set.range fun a => b.ylin a)

/-- `n₁ = max(hilb_deg, 1)`. -/
def n₁ : ℕ := max b.hilb_deg 1

theorem one_le_n₁ : 1 ≤ b.n₁ := le_max_right _ _

/-- Monomials of degree `≥ hilb_deg` lie in `I + (y)`. -/
theorem monomial_mem_sup : ∀ d, b.hilb_deg ≤ d → ∀ s : b.Idx →₀ ℕ, s.degree = d →
    monomial s (1 : ℂ) ∈ b.blockI ⊔ b.Yideal := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact fun s hs => b.hilb (monomial s 1) (isHomogeneous_monomial _ hs)
  | succ d _ ih =>
    intro s hs
    have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
    obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp hs0
    have hv1 : 1 ≤ s v := Nat.one_le_iff_ne_zero.mpr hv
    set s' := s - Finsupp.single v 1
    have hss : s = s' + Finsupp.single v 1 := by
      ext w
      simp only [s', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hw
      · subst hw; omega
      · simp
    have hdeg : s'.degree = d := by
      have := congrArg Finsupp.degree hss
      rw [map_add, Finsupp.degree_single, hs] at this
      omega
    rw [hss, ← mul_one (1 : ℂ), ← monomial_mul]
    exact Ideal.mul_mem_right _ _ (ih s' hdeg)

/-- Homogeneous polynomials of degree `≥ hilb_deg` lie in `I + (y)`. -/
theorem hom_mem_sup {M : MvPolynomial b.Idx ℂ} {d : ℕ} (hM : M.IsHomogeneous d)
    (hd : b.hilb_deg ≤ d) : M ∈ b.blockI ⊔ b.Yideal := by
  rw [LSG.MEB.IsHomogeneous.eq_sum_monomial (P := M)]
  refine Ideal.sum_mem _ fun s hs => ?_
  rw [smul_eq_C_mul]
  refine Ideal.mul_mem_left _ _ (b.monomial_mem_sup d hd s ?_)
  have := hM (mem_support_iff.mp hs)
  rw [Finsupp.degree_eq_weight_one]
  exact this

/-- **The Hilbert certificate in homogeneous form**: `M ≡ Σ_a y_a c_a (mod I)` with `c_a` homogeneous of
degree `d − 1`. -/
theorem hilb_hom {M : MvPolynomial b.Idx ℂ} {d : ℕ} (hM : M.IsHomogeneous d) (hd : b.n₁ ≤ d) :
    ∃ c : Fin (b.g + 2) → MvPolynomial b.Idx ℂ, (∀ a, (c a).IsHomogeneous (d - 1)) ∧
      M - ∑ a, b.ylin a * c a ∈ b.blockI := by
  have hd0 : b.hilb_deg ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : 1 ≤ d := le_trans b.one_le_n₁ hd
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (b.hom_mem_sup hM hd0)
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hj
  refine ⟨fun a => homogeneousComponent (d - 1) (c' a),
    fun a => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hM' : M = homogeneousComponent d M := (homogeneousComponent_eq_self hM).symm
  have e : homogeneousComponent d M = homogeneousComponent d i +
      ∑ a, b.ylin a * homogeneousComponent (d - 1) (c' a) := by
    rw [← hij, ← hc', map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm, homogeneousComponent_lin_mul (b.ylin_isHomogeneous a) _ hd1]
  rw [hM', e, add_sub_cancel_right]
  exact b.comp_mem_blockI hi d

/-! ### The spanning sets `Std e` -/

/-- Exponents `β` of the `y`-monomials of degree `e`. -/
def Bset (e : ℕ) : Finset (Fin (b.g + 2) → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (e + 1)).filter fun β => ∑ a, β a = e

/-- Exponents of the monomials of degree `n₁ − 1`. -/
def Mset : Finset (b.Idx → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range b.n₁).filter fun s => ∑ c, s c = b.n₁ - 1

/-- `y^β`. -/
noncomputable def yb (β : Fin (b.g + 2) → ℕ) : MvPolynomial b.Idx ℂ :=
  ∏ a, b.ylin a ^ β a

/-- `X^s`. -/
noncomputable def Mmon (s : b.Idx → ℕ) : MvPolynomial b.Idx ℂ := ∏ c, X c ^ s c

/-- **The spanning set** `{y^β X^s : |β| = e, |s| = n₁ − 1}`. -/
noncomputable def Std (e : ℕ) : Finset (MvPolynomial b.Idx ℂ) :=
  (b.Bset e ×ˢ b.Mset).image fun p => b.yb p.1 * b.Mmon p.2

theorem yb_add_single (β : Fin (b.g + 2) → ℕ) (a : Fin (b.g + 2)) :
    b.yb (β + Pi.single a 1) = b.ylin a * b.yb β := by
  classical
  simp only [yb, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single a (fun a' _ ha' => by simp [Pi.single_apply, ha'])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp

/-- **Homogeneous polynomials of degree `e + n₁ − 1` lie in `span (Std e) + I`.** -/
theorem hom_mem_span_Std : ∀ (e : ℕ) (M : MvPolynomial b.Idx ℂ),
    M.IsHomogeneous (e + b.n₁ - 1) →
      M ∈ Submodule.span ℂ (b.Std e : Set _) ⊔ b.blockI.restrictScalars ℂ := by
  intro e
  induction e with
  | zero =>
    intro M hM
    rw [LSG.MEB.IsHomogeneous.eq_sum_monomial (P := M)]
    refine Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_)
    refine Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(0, fun c => s c), ?_, ?_⟩))
    · have hdeg : s.degree = b.n₁ - 1 := by
        have := hM (mem_support_iff.mp hs)
        rw [zero_add] at this
        rw [Finsupp.degree_eq_weight_one]
        exact this
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simp only [Bset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
          Pi.zero_apply, Finset.sum_const_zero, and_true]
        exact fun _ => Nat.zero_lt_succ _
      · simp only [Mset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun c => ?_, by rw [← degree_eq_sum_univ', hdeg]⟩
        have h1 : s c ≤ s.degree := by
          rw [degree_eq_sum_univ']
          exact Finset.single_le_sum (f := fun c => s c) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ c)
        have := b.one_le_n₁
        omega
    · simp only [yb, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul, Mmon]
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  | succ e ih =>
    intro M hM
    obtain ⟨c, hc, hMc⟩ := b.hilb_hom hM (by omega)
    have hM' : M = (M - ∑ a, b.ylin a * c a) + ∑ a, b.ylin a * c a := by ring
    rw [hM']
    refine Submodule.add_mem _ (Submodule.mem_sup_right hMc) (Submodule.sum_mem _ fun a _ => ?_)
    have hca := ih (c a) (by
      have := hc a
      rwa [show e + 1 + b.n₁ - 1 - 1 = e + b.n₁ - 1 by omega] at this)
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hca
    rw [← hpq, mul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (LSG.MEB.mul_mem_span_of ?_ hp))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ hq))
    intro x hx
    obtain ⟨⟨β, s⟩, hβs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨hβ, hs⟩ := Finset.mem_product.mp hβs
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(β + Pi.single a 1, s), ?_, ?_⟩)
    · refine Finset.mem_product.mpr ⟨?_, hs⟩
      simp only [Bset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hβ ⊢
      refine ⟨fun a' => ?_, ?_⟩
      · have := hβ.1 a'
        simp only [Pi.add_apply, Pi.single_apply]
        split_ifs <;> omega
      · simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, hβ.2, Finset.sum_pi_single']
        simp
    · simp only
      rw [b.yb_add_single, mul_assoc]

theorem card_Bset_le (e : ℕ) : (b.Bset e).card ≤ (e + 1) ^ (b.g + 1) := by
  classical
  have hinj : Set.InjOn (fun β : Fin (b.g + 2) → ℕ => fun i : Fin (b.g + 1) => β i.castSucc)
      (b.Bset e : Set _) := by
    intro β hβ β' hβ' h
    simp only [Bset, Finset.coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hβ hβ'
    have hc : ∀ i : Fin (b.g + 1), β i.castSucc = β' i.castSucc := fun i => congrFun h i
    have h1 := hβ.2
    have h2 := hβ'.2
    rw [Fin.sum_univ_castSucc] at h1 h2
    have hs : ∑ i : Fin (b.g + 1), β i.castSucc = ∑ i : Fin (b.g + 1), β' i.castSucc :=
      Finset.sum_congr rfl fun i _ => hc i
    funext a
    refine Fin.lastCases ?_ (fun i => hc i) a
    omega
  calc (b.Bset e).card
      ≤ (Fintype.piFinset fun _ : Fin (b.g + 1) => Finset.range (e + 1)).card := by
        refine Finset.card_le_card_of_injOn _ (fun β hβ => ?_) hinj
        simp only [Bset, Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hβ
        simp only [Finset.mem_coe, Fintype.mem_piFinset]
        exact fun i => hβ.1 _
    _ = (e + 1) ^ (b.g + 1) := by simp

theorem card_Mset_le : b.Mset.card ≤ b.n₁ ^ (b.N + b.nT) := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem card_Std_le (e : ℕ) : (b.Std e).card ≤ (e + 1) ^ (b.g + 1) * b.n₁ ^ (b.N + b.nT) := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  exact Nat.mul_le_mul (b.card_Bset_le e) b.card_Mset_le

/-! ### The slice of one block -/

/-- The linear form `ℓ = Σ_c α_c X_c` in the `X`-variables of the block. -/
noncomputable def lform (α : Fin b.N → ℂ) : MvPolynomial b.Idx ℂ := ∑ c, C (α c) * X (Sum.inl c)

theorem lform_isHomogeneous (α : Fin b.N → ℂ) : (b.lform α).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ _).C_mul _

/-- The slice `I + (ℓ − 1)` of the block. -/
noncomputable def slB (α : Fin b.N → ℂ) : Ideal (MvPolynomial b.Idx ℂ) :=
  b.blockI ⊔ Ideal.span {b.lform α - 1}

theorem pow_sub_one_mem (α : Fin b.N → ℂ) (k : ℕ) : b.lform α ^ k - 1 ∈ b.slB α := by
  refine Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ?_)
  simpa using sub_dvd_pow_sub_pow (b.lform α) 1 k

/-- **Slicing one block**: a polynomial of degree `≤ n` lies in `span (Std n) + I + (ℓ − 1)`. -/
theorem mem_span_Std_slice (α : Fin b.N → ℂ) {P : MvPolynomial b.Idx ℂ} {n : ℕ}
    (hP : P.totalDegree ≤ n) :
    P ∈ Submodule.span ℂ (b.Std n : Set _) ⊔ (b.slB α).restrictScalars ℂ := by
  rw [← sum_homogeneousComponent P]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  set k := n + b.n₁ - 1 - j
  set Pj := homogeneousComponent j P
  have hhom : (b.lform α ^ k * Pj).IsHomogeneous (n + b.n₁ - 1) := by
    have := ((b.lform_isHomogeneous α).pow k).mul (homogeneousComponent_isHomogeneous j P)
    rwa [show 1 * k + j = n + b.n₁ - 1 by have := b.one_le_n₁; omega] at this
  have h1 := b.hom_mem_span_Std n _ hhom
  have e : Pj = b.lform α ^ k * Pj - (b.lform α ^ k - 1) * Pj := by ring
  rw [e]
  refine Submodule.sub_mem _ ?_ (Submodule.mem_sup_right
    (Ideal.mul_mem_right _ _ (b.pow_sub_one_mem α k)))
  exact (sup_le_sup_left (Submodule.restrictScalars_mono ℂ (le_sup_left : b.blockI ≤ b.slB α))
    _) h1

/-! ### B5: local generation of the block slice -/

theorem eval_lift_blockI {P : MvPolynomial b.Idx ℂ} (hP : P ∈ b.blockI) (p : (Fin b.g → ℂ) × ℂ) :
    eval (b.lift p) P = 0 :=
  LSG.MEB.eval_eq_zero_of_span (fun Q hQ => b.lift_model p Q hQ) hP

/-- `g + 1 < N + nT`: the certificate `lci` has at least one local system. -/
theorem g_lt_N : b.g + 1 < b.N + b.nT := by
  by_cases hs : b.lci_s = 0
  · exfalso
    apply b.base.θ_ne 0
    funext v
    obtain ⟨e, he⟩ := b.lci_cover v
    have hrange : Set.range b.lci_S = ∅ := by
      rw [Set.range_eq_empty_iff]; rw [hs]; exact Fin.isEmpty'
    rw [hrange, Ideal.span_empty, sup_bot_eq] at he
    have := b.eval_lift_blockI he (0, 0)
    rw [map_pow, eval_X] at this
    exact eq_zero_of_pow_eq_zero this
  · have := b.lci_len ⟨0, Nat.pos_of_ne_zero hs⟩
    change b.base.g + 1 < b.base.N + b.nT
    omega

/-- **B5 for the block slice**: `I + (ℓ − 1)` (`ℓ` in the `X`-variables) is locally generated by
`N + nT − (g + 1)` elements. -/
theorem locGen_slB (α : Fin b.N → ℂ) :
    StrongSix.M2.LocGen (b.slB α) (b.N + b.nT - (b.g + 1)) := by
  classical
  refine StrongSix.M2.LocGen.of_cover b.lci_S (fun i => b.lci_F i ++ [b.lform α - 1])
    (fun i => ?_) (fun i x hx => ?_) (fun i => ?_) ?_
  · rw [Ideal.ofList_append]
    refine sup_le ((b.lci_F_le i).trans le_sup_left) ?_
    rw [Ideal.ofList, Ideal.span_le]
    intro y hy
    simp only [List.mem_singleton, Set.mem_setOf_eq] at hy
    exact Ideal.mem_sup_right (Ideal.subset_span hy)
  · obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    clear hx
    rw [mul_add, Ideal.ofList_append]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · induction hu using Submodule.span_induction with
      | mem y hy => exact b.lci_mem i y hy
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Ideal.add_mem _ hy hz
      | smul a y _ hy => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ a hy
    · obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      rw [mul_left_comm]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      simp
  · have := b.lci_len i
    simp only [List.length_append, List.length_singleton]
    change _ ≤ b.base.N + b.nT - (b.base.g + 1)
    omega
  · -- the cover: `ℓ` (an `X`-form) is nilpotent modulo `I + (S)`, and `ℓ ≡ 1` modulo `ℓ − 1`
    set J := b.blockI ⊔ Ideal.span (Set.range b.lci_S)
    have hX : ∀ c, (X (Sum.inl c) : MvPolynomial b.Idx ℂ) ∈ J.radical := fun c => by
      obtain ⟨e, he⟩ := b.lci_cover c
      exact ⟨e, he⟩
    have hℓ : b.lform α ∈ J.radical :=
      Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hX c)
    obtain ⟨K, hK⟩ := hℓ
    have hJ : J ≤ b.slB α ⊔ Ideal.span (Set.range b.lci_S) :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    have e : (1 : MvPolynomial b.Idx ℂ) = b.lform α ^ K - (b.lform α ^ K - 1) := by ring
    rw [SetLike.mem_coe, e]
    exact Ideal.sub_mem _ (hJ hK) (Ideal.mem_sup_left (b.pow_sub_one_mem α K))

end VBlock

end LSG.MEBV
