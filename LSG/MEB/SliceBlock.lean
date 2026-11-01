/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.ModelIG
import StrongSix.M2.LCIBlocks

/-!
# One abelian block: the certificates B5 and B6 on a slice (A4.2, α)

Block-local facts in `ℂ[X_c : c < N]` for an abelian block `b`, from its certificate fields only:

* **B6 (Hilbert upper bound).** `comp_mem_blockI`: the explicit ideal is homogeneous. `hilb_hom`: every
  homogeneous `M` of degree `d ≥ max(hilb_deg, 1)` is `Σ_a y_a c_a` modulo `I` with `c_a` homogeneous of degree
  `d − 1`. `Std e` (`y^β M'`, `|β| = e`, `deg M' = n₁ − 1`): **`hom_mem_span_Std`**: every homogeneous polynomial
  of degree `e + n₁ − 1` lies in `span (Std e) + I`; `card_Std_le : #(Std e) ≤ (e+1)^g · n₁^N`.
  **`mem_span_Std_slice`**: every polynomial of degree `≤ n` lies in `span (Std n) + I + (ℓ − 1)` for every linear
  form `ℓ` (homogenisation by powers of `ℓ`).
* **B5 (local complete intersection).** `slB ℓ = I + (ℓ − 1)`; **`locGen_slB`**: `LocGen (slB ℓ) (N − g)`
  (StrongSix's `LocGen.of_cover` with the local systems `F_i ++ [ℓ − 1]`; the cover from `lci_cover` by a radical
  argument). `g_lt_N : g < N`.
-/

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LSG.MEB

/-! ### Homogeneous ideals -/

/-- The homogeneous components of an element of an ideal spanned by homogeneous elements lie in it. -/
theorem homogeneousComponent_mem_span {σ : Type*} {s : Set (MvPolynomial σ ℂ)}
    (hs : ∀ Q ∈ s, ∃ d, Q.IsHomogeneous d) {P : MvPolynomial σ ℂ} (hP : P ∈ Ideal.span s)
    (i : ℕ) : homogeneousComponent i P ∈ Ideal.span s := by
  have hI : (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ ℂ) :=
    Ideal.homogeneous_span _ s fun x hx => by
      obtain ⟨d, hd⟩ := hs x hx
      exact ⟨d, (mem_homogeneousSubmodule d x).mpr hd⟩
  have := hI i hP
  rwa [← decomposition.decompose'_apply]

theorem homogeneousComponent_X_mul {σ : Type*} (v : σ) (p : MvPolynomial σ ℂ) {d : ℕ}
    (hd : 1 ≤ d) : homogeneousComponent d (X v * p) = X v * homogeneousComponent (d - 1) p := by
  have hX : (X v : MvPolynomial σ ℂ) ∈ homogeneousSubmodule σ ℂ 1 :=
    (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℂ v)
  have := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := homogeneousSubmodule σ ℂ)
    (b := p) hX hd
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply]
  exact this

/-- A homogeneous polynomial is the sum of its monomials. -/
theorem IsHomogeneous.eq_sum_monomial {σ : Type*} {P : MvPolynomial σ ℂ} :
    P = ∑ s ∈ P.support, P.coeff s • monomial s (1 : ℂ) := by
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem mul_mem_span_of {A : Type*} [CommRing A] [Algebra ℂ A] {S T : Set A} {x : A}
    (hx : ∀ s ∈ S, x * s ∈ T) {p : A} (hp : p ∈ Submodule.span ℂ S) :
    x * p ∈ Submodule.span ℂ T := by
  induction hp using Submodule.span_induction with
  | mem s hs => exact Submodule.subset_span (hx s hs)
  | zero => simp
  | add p q _ _ hp hq => rw [mul_add]; exact Submodule.add_mem _ hp hq
  | smul a p _ hp => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hp

theorem degree_eq_sum_univ {N : ℕ} (s : Fin N →₀ ℕ) : s.degree = ∑ c, s c := by
  rw [Finsupp.degree]
  exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa using hc

namespace AbBlock

variable (b : AbBlock)

theorem gens_hom' : ∀ Q ∈ {Q | Q ∈ b.gens}, ∃ d, Q.IsHomogeneous d :=
  fun Q hQ => (b.gens_hom Q hQ).imp fun _ h => h.2

theorem comp_mem_blockI {P : MvPolynomial (Fin b.N) ℂ} (hP : P ∈ b.blockI) (i : ℕ) :
    homogeneousComponent i P ∈ b.blockI :=
  homogeneousComponent_mem_span b.gens_hom' hP i

/-- The ideal `(y_0, …, y_g)` of the Hilbert certificate. -/
noncomputable def Yideal : Ideal (MvPolynomial (Fin b.N) ℂ) :=
  Ideal.span (Set.range fun a => (X (b.hilb_y a) : MvPolynomial (Fin b.N) ℂ))

/-- `n₁ = max(hilb_deg, 1)`. -/
def n₁ : ℕ := max b.hilb_deg 1

theorem one_le_n₁ : 1 ≤ b.n₁ := le_max_right _ _

/-- Monomials of degree `≥ hilb_deg` lie in `I + (y)`. -/
theorem monomial_mem_sup : ∀ d, b.hilb_deg ≤ d → ∀ s : Fin b.N →₀ ℕ, s.degree = d →
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
theorem hom_mem_sup {M : MvPolynomial (Fin b.N) ℂ} {d : ℕ} (hM : M.IsHomogeneous d)
    (hd : b.hilb_deg ≤ d) : M ∈ b.blockI ⊔ b.Yideal := by
  rw [IsHomogeneous.eq_sum_monomial (P := M)]
  refine Ideal.sum_mem _ fun s hs => ?_
  rw [smul_eq_C_mul]
  refine Ideal.mul_mem_left _ _ (b.monomial_mem_sup d hd s ?_)
  have := hM (mem_support_iff.mp hs)
  rw [Finsupp.degree_eq_weight_one]
  exact this

/-- **The Hilbert certificate in homogeneous form**: `M ≡ Σ_a y_a c_a (mod I)` with `c_a` homogeneous of
degree `d − 1`. -/
theorem hilb_hom {M : MvPolynomial (Fin b.N) ℂ} {d : ℕ} (hM : M.IsHomogeneous d) (hd : b.n₁ ≤ d) :
    ∃ c : Fin (b.g + 1) → MvPolynomial (Fin b.N) ℂ, (∀ a, (c a).IsHomogeneous (d - 1)) ∧
      M - ∑ a, X (b.hilb_y a) * c a ∈ b.blockI := by
  have hd0 : b.hilb_deg ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : 1 ≤ d := le_trans b.one_le_n₁ hd
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (b.hom_mem_sup hM hd0)
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hj
  refine ⟨fun a => homogeneousComponent (d - 1) (c' a),
    fun a => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hM' : M = homogeneousComponent d M := (homogeneousComponent_eq_self hM).symm
  have e : homogeneousComponent d M = homogeneousComponent d i +
      ∑ a, X (b.hilb_y a) * homogeneousComponent (d - 1) (c' a) := by
    rw [← hij, ← hc', map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm, homogeneousComponent_X_mul _ _ hd1]
  rw [hM', e, add_sub_cancel_right]
  exact b.comp_mem_blockI hi d

/-! ### The spanning sets `Std e` -/

/-- Exponents `β` of the `y`-monomials of degree `e`. -/
def Bset (e : ℕ) : Finset (Fin (b.g + 1) → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (e + 1)).filter fun β => ∑ a, β a = e

/-- Exponents of the monomials of degree `n₁ − 1`. -/
def Mset : Finset (Fin b.N → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range b.n₁).filter fun s => ∑ c, s c = b.n₁ - 1

/-- `y^β`. -/
noncomputable def yb (β : Fin (b.g + 1) → ℕ) : MvPolynomial (Fin b.N) ℂ :=
  ∏ a, X (b.hilb_y a) ^ β a

/-- `X^s`. -/
noncomputable def Mmon (s : Fin b.N → ℕ) : MvPolynomial (Fin b.N) ℂ := ∏ c, X c ^ s c

/-- **The spanning set** `{y^β X^s : |β| = e, |s| = n₁ − 1}`. -/
noncomputable def Std (e : ℕ) : Finset (MvPolynomial (Fin b.N) ℂ) :=
  (b.Bset e ×ˢ b.Mset).image fun p => b.yb p.1 * b.Mmon p.2

theorem yb_add_single (β : Fin (b.g + 1) → ℕ) (a : Fin (b.g + 1)) :
    b.yb (β + Pi.single a 1) = X (b.hilb_y a) * b.yb β := by
  classical
  simp only [yb, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single a (fun a' _ ha' => by simp [Pi.single_apply, ha'])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp

/-- **Homogeneous polynomials of degree `e + n₁ − 1` lie in `span (Std e) + I`.** -/
theorem hom_mem_span_Std : ∀ (e : ℕ) (M : MvPolynomial (Fin b.N) ℂ),
    M.IsHomogeneous (e + b.n₁ - 1) →
      M ∈ Submodule.span ℂ (b.Std e : Set _) ⊔ b.blockI.restrictScalars ℂ := by
  intro e
  induction e with
  | zero =>
    intro M hM
    rw [IsHomogeneous.eq_sum_monomial (P := M)]
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
        refine ⟨fun c => ?_, by rw [← degree_eq_sum_univ, hdeg]⟩
        have h1 : s c ≤ s.degree := by
          rw [degree_eq_sum_univ]
          exact Finset.single_le_sum (f := fun c => s c) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ c)
        have := b.one_le_n₁
        omega
    · simp only [yb, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul, Mmon]
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  | succ e ih =>
    intro M hM
    obtain ⟨c, hc, hMc⟩ := b.hilb_hom hM (by omega)
    have hM' : M = (M - ∑ a, X (b.hilb_y a) * c a) + ∑ a, X (b.hilb_y a) * c a := by ring
    rw [hM']
    refine Submodule.add_mem _ (Submodule.mem_sup_right hMc) (Submodule.sum_mem _ fun a _ => ?_)
    have hca := ih (c a) (by
      have := hc a
      rwa [show e + 1 + b.n₁ - 1 - 1 = e + b.n₁ - 1 by omega] at this)
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hca
    rw [← hpq, mul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (mul_mem_span_of ?_ hp))
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

theorem card_Bset_le (e : ℕ) : (b.Bset e).card ≤ (e + 1) ^ b.g := by
  classical
  have hinj : Set.InjOn (fun β : Fin (b.g + 1) → ℕ => fun i : Fin b.g => β i.castSucc)
      (b.Bset e : Set _) := by
    intro β hβ β' hβ' h
    simp only [Bset, Finset.coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hβ hβ'
    have hc : ∀ i : Fin b.g, β i.castSucc = β' i.castSucc := fun i => congrFun h i
    have h1 := hβ.2
    have h2 := hβ'.2
    rw [Fin.sum_univ_castSucc] at h1 h2
    have hs : ∑ i : Fin b.g, β i.castSucc = ∑ i : Fin b.g, β' i.castSucc :=
      Finset.sum_congr rfl fun i _ => hc i
    funext a
    refine Fin.lastCases ?_ (fun i => hc i) a
    omega
  calc (b.Bset e).card
      ≤ (Fintype.piFinset fun _ : Fin b.g => Finset.range (e + 1)).card := by
        refine Finset.card_le_card_of_injOn _ (fun β hβ => ?_) hinj
        simp only [Bset, Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hβ
        simp only [Finset.mem_coe, Fintype.mem_piFinset]
        exact fun i => hβ.1 _
    _ = (e + 1) ^ b.g := by simp

theorem card_Mset_le : b.Mset.card ≤ b.n₁ ^ b.N := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem card_Std_le (e : ℕ) : (b.Std e).card ≤ (e + 1) ^ b.g * b.n₁ ^ b.N := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  exact Nat.mul_le_mul (b.card_Bset_le e) b.card_Mset_le

/-! ### The slice of one block -/

/-- The linear form `ℓ = Σ_c α_c X_c` in the block variables. -/
noncomputable def lform (α : Fin b.N → ℂ) : MvPolynomial (Fin b.N) ℂ := ∑ c, C (α c) * X c

theorem lform_isHomogeneous (α : Fin b.N → ℂ) : (b.lform α).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ c).C_mul _

/-- The slice `I + (ℓ − 1)` of the block. -/
noncomputable def slB (α : Fin b.N → ℂ) : Ideal (MvPolynomial (Fin b.N) ℂ) :=
  b.blockI ⊔ Ideal.span {b.lform α - 1}

theorem pow_sub_one_mem (α : Fin b.N → ℂ) (k : ℕ) : b.lform α ^ k - 1 ∈ b.slB α := by
  refine Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ?_)
  simpa using sub_dvd_pow_sub_pow (b.lform α) 1 k

/-- **Slicing one block**: a polynomial of degree `≤ n` lies in `span (Std n) + I + (ℓ − 1)`. -/
theorem mem_span_Std_slice (α : Fin b.N → ℂ) {P : MvPolynomial (Fin b.N) ℂ} {n : ℕ}
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

theorem eval_θ_blockI {P : MvPolynomial (Fin b.N) ℂ} (hP : P ∈ b.blockI) (z : Fin b.g → ℂ) :
    eval (b.θ z) P = 0 :=
  eval_eq_zero_of_span (fun Q hQ => b.θ_model z Q hQ) hP

/-- `g < N`: the certificate `lci` has at least one local system. -/
theorem g_lt_N : b.g < b.N := by
  by_cases hs : b.lci_s = 0
  · exfalso
    apply b.θ_ne 0
    funext v
    obtain ⟨e, he⟩ := b.lci_cover v
    have hrange : Set.range b.lci_S = ∅ := by
      rw [Set.range_eq_empty_iff]; rw [hs]; exact Fin.isEmpty'
    rw [hrange, Ideal.span_empty, sup_bot_eq] at he
    have := b.eval_θ_blockI he 0
    rw [map_pow, eval_X] at this
    exact eq_zero_of_pow_eq_zero this
  · have := b.lci_len ⟨0, Nat.pos_of_ne_zero hs⟩
    omega

/-- **B5 for the block slice**: `I + (ℓ − 1)` is locally generated by `N − g` elements. -/
theorem locGen_slB (α : Fin b.N → ℂ) : StrongSix.M2.LocGen (b.slB α) (b.N - b.g) := by
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
    omega
  · -- the cover: `ℓ` is nilpotent modulo `I + (S)`, and `ℓ ≡ 1` modulo `ℓ − 1`
    set J := b.blockI ⊔ Ideal.span (Set.range b.lci_S)
    have hX : ∀ c, (X c : MvPolynomial (Fin b.N) ℂ) ∈ J.radical := fun c => by
      obtain ⟨e, he⟩ := b.lci_cover c
      exact ⟨e, he⟩
    have hℓ : b.lform α ∈ J.radical :=
      Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hX c)
    obtain ⟨K, hK⟩ := hℓ
    have hJ : J ≤ b.slB α ⊔ Ideal.span (Set.range b.lci_S) :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    have e : (1 : MvPolynomial (Fin b.N) ℂ) = b.lform α ^ K - (b.lform α ^ K - 1) := by ring
    rw [SetLike.mem_coe, e]
    exact Ideal.sub_mem _ (hJ hK) (Ideal.mem_sup_left (b.pow_sub_one_mem α K))

end AbBlock

end LSG.MEB
