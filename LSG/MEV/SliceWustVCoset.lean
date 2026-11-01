import Mathlib
import LSG.MEV.SliceWustV

/-!
# The sliced Wüstholz lemma for finite unions of cosets of `H⁰` in `G̃` (STAGE5_MEV §10)

For `E = ⋃_{a ∈ R} (a + H⁰)` (distinct cosets), `α` with `ℓ_k ∉ I(a + H⁰)` (`a ∈ R`, all `k`),
`W ⊆ Lie G̃` and `ℓ = dim W − dim (W ∩ lieAlg H)`:

  **`wustholz_cosets_slV`**: `(k+1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S₀ c₀)`

for every `A ≤ VOg DmixV (WmixV W) I(E) S₀` and `ℓ k ≤ S₀`.

Ingredients beyond `wustholz_cosetsV` (`WustTrans`): the multiplier must be **multihomogeneous**
(`nzd_slV`). The coset data of `exists_coset_data` are rebuilt with homogeneous duals:
* `compV_mem_vanish`: multigraded components of elements of `I(E)` lie in `I(E)`;
* `hzV` (homogenisation of a polynomial vanishing at `a` with powers of the chart forms of `a`,
  which are `1` at `coords a 1`): it keeps the first-order pairing at `a`;
* `isWH_det` (the determinant of a matrix of homogeneous entries of one degree);
* `exists_coset_data_hom`, then balancing of the degrees by powers `ℓ^c` (`lpowV`) and homogeneous
  separators (`exists_homogVanish_ne`), and `LSG.ME.glue`: **`exists_transversals_slV`**.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk VOg)
open StrongSix.M2 (DL DL_cons hfun FLE)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Multigraded components of vanishing ideals -/

theorem comp_iter_mem_vanish {E : Set (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ vanish E) (e : Fin m → ℕ) (s : Finset (Fin m)) :
    ∃ Q ∈ vanish E, ∀ t, Q.coeff t =
      if (∀ k ∈ s, Finsupp.weight (wEV k) t = e k) then P.coeff t else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P, hP, fun t => by simp⟩
  | insert k s hk ih =>
    obtain ⟨Q, hQ, hQc⟩ := ih
    refine ⟨weightedHomogeneousComponent (wEV k) (e k) Q, comp_mem_vanish hQ k (e k), fun t => ?_⟩
    rw [coeff_weightedHomogeneousComponent, hQc]
    by_cases h1 : Finsupp.weight (wEV k) t = e k
    · by_cases h2 : ∀ k' ∈ s, Finsupp.weight (wEV k') t = e k'
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left]
        intro k' hk'
        rcases Finset.mem_insert.mp hk' with rfl | hk'
        · exact h1
        · exact h2 k' hk'
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right]
        exact fun h => h2 fun k' hk' => h k' (Finset.mem_insert_of_mem hk')
    · rw [ite_eq_right h1, ite_eq_right]
      exact fun h => h1 (h k (Finset.mem_insert_self k s))

/-- **Multigraded components of elements of `I(E)` lie in `I(E)`.** -/
theorem compV_mem_vanish {E : Set (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ vanish E) (e : Fin m → ℕ) : weightedHomogeneousComponent wtV e P ∈ vanish E := by
  classical
  obtain ⟨Q, hQ, hQc⟩ := comp_iter_mem_vanish hP e Finset.univ
  convert hQ using 1
  ext t
  rw [coeff_weightedHomogeneousComponent, hQc]
  have : Finsupp.weight wtV t = e ↔ ∀ k ∈ Finset.univ, Finsupp.weight (wEV k) t = e k := by
    constructor
    · intro h k _; rw [weight_wEV, h]
    · intro h; funext k; rw [← weight_wEV]; exact h k (Finset.mem_univ k)
  simp only [this]

/-! ### Determinants -/

theorem isWH_det {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    {d : Fin m → ℕ} (hA : ∀ i j, IsWeightedHomogeneous wtV (A i j) d) :
    IsWeightedHomogeneous wtV A.det (ℓ • d) := by
  rw [← mem_weightedHomogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wtV) Finset.univ (fun i => A (σ i) i)
    (fun _ => d) (fun i _ => hA (σ i) i)
  simpa using this

/-! ### Homogenisation with the chart forms of a point -/

/-- `∏_k L_k^{c_k}`, `L_k` the chart form of `a` in block `k`. -/
def lchV (a : GPtV d₀ d₁ Ls) (c : Fin m → ℕ) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  ∏ k, (X (.e k (bi (chartsV a k))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ c k

theorem isWH_lchV (a : GPtV d₀ d₁ Ls) (c : Fin m → ℕ) :
    IsWeightedHomogeneous wtV (lchV (d₀ := d₀) (d₁ := d₁) a c) c := by
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wtV) Finset.univ
    (fun k => (X (.e k (bi (chartsV a k))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ c k)
    (fun k => c k • Pi.single k 1)
    (fun k _ => (isWeightedHomogeneous_X ℂ wtV (Var.e k (bi (chartsV a k)) :
      Var d₀ d₁ m)).pow (c k))
  unfold lchV
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem eval_lchV (a : GPtV d₀ d₁ Ls) (c : Fin m → ℕ) :
    eval (coords a 1) (lchV (d₀ := d₀) (d₁ := d₁) a c) = 1 := by
  have h : ∀ k, eval (coords a 1) (X (.e k (bi (chartsV a k))) :
      MvPolynomial (Var d₀ d₁ m) ℂ) = 1 := fun k => by
    have := eval_chartIdeal a (X_sub_one_mem (d₀ := d₀) (d₁ := d₁) (chartsV a) k)
    rwa [map_sub, map_one, sub_eq_zero] at this
  simp [lchV, map_prod, h]

/-- Multiplying by `L − 1` (`L(pt) = 1`) does not change the first-order pairing at `pt` of an
element vanishing at `pt`. -/
theorem eval_Dhc_mul_sub_one (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (y : Var d₀ d₁ m → ℂ)
    {L Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hL : eval y L = 1) (hQ : eval y Q = 0) :
    eval y (Dhc Ls ch w (L * Q)) = eval y (Dhc Ls ch w Q) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hL, hQ]
  ring

/-! ### Coset data with a homogeneous multiplier -/

section Trans

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **Transversal data at one coset with a multihomogeneous multiplier.** -/
theorem exists_coset_data_hom {ℓ : ℕ} (w : Fin ℓ → LieV ℂ d₀ d₁ m)
    (hw : ∀ c : Fin ℓ → ℂ, ∑ i, c i • w i ∈ lieAlgL Ls hH → c = 0) (a : GPtV d₀ d₁ Ls) :
    ∃ (T : Fin ℓ → MvPolynomial (Var d₀ d₁ m) ℂ) (N : MvPolynomial (Var d₀ d₁ m) ℂ)
      (ν : Fin m → ℕ),
      (∀ j, T j ∈ vanish (gtransl a (H0 Ls hH))) ∧ N ∉ vanish (gtransl a (H0 Ls hH)) ∧
      IsWeightedHomogeneous wtV N ν ∧
      ∀ i j, Dhc Ls (chartsV a) (w i) (T j) - (if i = j then N else 0) ∈
        vanish (gtransl a (H0 Ls hH)) := by
  classical
  set C := gtransl a (H0 Ls hH)
  have haC : a ∈ C := ⟨0, (H0_isSubgroup hH).zero_mem, zero_add a⟩
  set φ := pairV Ls (chartsV a) (coords a 1) (vanish C)
  obtain ⟨P, hP⟩ := exists_dual φ w fun c hc0 => hw c (mem_lieAlgL_of_ker hH hc a fun Q hQ => by
    have := LinearMap.congr_fun hc0 ⟨Q, hQ⟩
    rwa [pairV_apply] at this)
  -- homogenise the duals to one common degree
  choose s hs using fun j => sum_compV (P j : MvPolynomial (Var d₀ d₁ m) ℂ)
  set e₀ : Fin m → ℕ := ∑ j, ∑ e ∈ s j, e
  have hle : ∀ j, ∀ e ∈ s j, e ≤ e₀ := fun j e he =>
    (Finset.single_le_sum (f := fun e => e) (fun _ _ => zero_le) he).trans
      (Finset.single_le_sum (f := fun j => ∑ e ∈ s j, e) (fun _ _ => zero_le) (Finset.mem_univ j))
  set P' : Fin ℓ → MvPolynomial (Var d₀ d₁ m) ℂ := fun j =>
    ∑ e ∈ s j, lchV a (e₀ - e) * weightedHomogeneousComponent wtV e (P j : MvPolynomial _ ℂ)
  have hcomp : ∀ j e, weightedHomogeneousComponent wtV e (P j : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
      vanish C := fun j e => compV_mem_vanish (P j).2 e
  have hP'C : ∀ j, P' j ∈ vanish C := fun j =>
    Ideal.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (hcomp j e)
  have hP'h : ∀ j, IsWeightedHomogeneous wtV (P' j) e₀ := fun j => by
    refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWH_lchV (d₀ := d₀) (d₁ := d₁) a (e₀ - e)).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := wtV) e
        (P j : MvPolynomial (Var d₀ d₁ m) ℂ))
    rwa [tsub_add_cancel_of_le (hle j e he)] at this
  have hP'ev : ∀ i j, eval (coords a 1) (Dhc Ls (chartsV a) (w i) (P' j)) =
      eval (coords a 1) (Dhc Ls (chartsV a) (w i) (P j)) := by
    intro i j
    conv_rhs => rw [hs j]
    simp only [P', map_sum]
    refine Finset.sum_congr rfl fun e _ => eval_Dhc_mul_sub_one _ _ _ (eval_lchV a _)
      (mem_vanish.mp (hcomp j e) a haC 1)
  set A : Matrix (Fin ℓ) (Fin ℓ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    fun i j => Dhc Ls (chartsV a) (w i) (P' j)
  have hA0 : ∀ i j, eval (coords a 1) (A i j) = if i = j then 1 else 0 := by
    intro i j
    have h1 := eval_DL_Dhc_chartsV (Ls := Ls) a [w i] (P j : MvPolynomial (Var d₀ d₁ m) ℂ)
    simp only [DL_cons, StrongSix.M2.DL_nil] at h1
    rw [show A i j = Dhc Ls (chartsV a) (w i) (P' j) from rfl, hP'ev, h1, ← hP i j, pairV_apply]
  have hAh : ∀ i j, IsWeightedHomogeneous wtV (A i j) (fun k => e₀ k + 2) := fun i j =>
    isHomV_iff_wtV.mp (isHomV_Dhc (isHomV_iff_wtV.mpr (hP'h j)) _ _)
  refine ⟨fun j => ∑ k, P' k * A.adjugate k j, A.det, ℓ • fun k => e₀ k + 2,
    fun j => Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hP'C k), fun hmem => ?_,
    isWH_det A hAh, fun i j => ?_⟩
  · have h1 := mem_vanish.mp hmem a haC 1
    rw [RingHom.map_det] at h1
    have : (eval (coords a 1)).mapMatrix A = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hA0, Matrix.one_apply]
    rw [this, Matrix.det_one] at h1
    exact one_ne_zero h1
  · have hmul := congrFun (congrFun (Matrix.mul_adjugate A) i) j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hmul
    have e : Dhc Ls (chartsV a) (w i) (∑ k, P' k * A.adjugate k j) -
        (if i = j then A.det else 0) =
        ∑ k, P' k * Dhc Ls (chartsV a) (w i) (A.adjugate k j) := by
      rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      have : ∑ k, A.adjugate k j * Dhc Ls (chartsV a) (w i) (P' k) =
          if i = j then A.det else 0 := by
        calc ∑ k, A.adjugate k j * Dhc Ls (chartsV a) (w i) (P' k)
            = ∑ k, A i k * A.adjugate k j := Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = _ := hmul
          _ = _ := by split_ifs <;> simp
      rw [this]; ring
    rw [e]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hP'C k)

/-- **Wüstholz transversals with a multihomogeneous multiplier** for a finite union of distinct
cosets of `H⁰`, given `ℓ_k ∉ I(a + H⁰)`. -/
theorem exists_transversals_slV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH) (α : Fin m → ℂ)
    (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH))) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → LieV ℂ d₀ d₁ m)
      (B : GPtV d₀ d₁ Ls → MvPolynomial (Var d₀ d₁ m) ℂ)
      (Q : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (M : MvPolynomial (Var d₀ d₁ m) ℂ) (μ : Fin m → ℕ),
      (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) ∧
      (∀ i j, (∑ a ∈ R, B a • Dhc Ls (chartsV a) (w i)) (Q j) -
        (if i = j then M else 0) ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) ∧
      IsWeightedHomogeneous wtV M μ ∧ ∀ a ∈ R, M ∉ vanish (gtransl a (H0 Ls hH)) := by
  classical
  obtain ⟨w, hwW, hwind⟩ := exists_dirs hH hc W
  choose T N ν hT hN hNh hTδ using exists_coset_data_hom hH hc w hwind
  set V := H0 Ls hH
  have hV : IsZClosed V := isZClosed_H0 hH
  have hVp : (vanish V).IsPrime := vanish_H0_isPrime hH
  have hpC : ∀ a, (vanish (gtransl a V)).IsPrime := fun a => vanish_gtransl_isPrime hV hVp a
  -- balance the multipliers to one degree
  set νm : Fin m → ℕ := ∑ a ∈ R, ν a
  have hνle : ∀ a ∈ R, ν a ≤ νm := fun a ha =>
    Finset.single_le_sum (f := ν) (fun _ _ => zero_le) ha
  set T' : GPtV d₀ d₁ Ls → _ := fun a j => lpowV α (νm - ν a) * T a j
  set N' : GPtV d₀ d₁ Ls → MvPolynomial (Var d₀ d₁ m) ℂ := fun a => lpowV α (νm - ν a) * N a
  have hT' : ∀ a j, T' a j ∈ vanish (gtransl a V) := fun a j => Ideal.mul_mem_left _ _ (hT a j)
  have hN' : ∀ a ∈ R, N' a ∉ vanish (gtransl a V) := by
    intro a ha hmem
    rcases (hpC a).mem_or_mem hmem with h | h
    · exact lpowV_notMem (hpC a) α (hℓ a ha) _ h
    · exact hN a h
  have hN'h : ∀ a ∈ R, IsWeightedHomogeneous wtV (N' a) νm := by
    intro a ha
    have := (isWH_lpowV (d₀ := d₀) (d₁ := d₁) α (νm - ν a)).mul (hNh a)
    rwa [tsub_add_cancel_of_le (hνle a ha)] at this
  have hTδ' : ∀ a i j, Dhc Ls (chartsV a) (w i) (T' a j) - (if i = j then N' a else 0) ∈
      vanish (gtransl a V) := by
    intro a i j
    have e : Dhc Ls (chartsV a) (w i) (T' a j) - (if i = j then N' a else 0) =
        lpowV α (νm - ν a) * (Dhc Ls (chartsV a) (w i) (T a j) - (if i = j then N a else 0)) +
          T a j * Dhc Ls (chartsV a) (w i) (lpowV α (νm - ν a)) := by
      simp only [T', N', Derivation.leibniz, smul_eq_mul]
      split_ifs <;> ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hTδ a i j)) (Ideal.mul_mem_right _ _ (hT a j))
  -- homogeneous separators
  have hsep : ∀ a b : GPtV d₀ d₁ Ls, ∃ (ef : Fin m → ℕ) (f : MvPolynomial (Var d₀ d₁ m) ℂ),
      IsWeightedHomogeneous wtV f ef ∧
      (a ∈ R → b ∈ R → a ≠ b → f ∈ vanish (gtransl b V) ∧ f ∉ vanish (gtransl a V)) := by
    intro a b
    by_cases h : a ∈ R ∧ b ∈ R ∧ a ≠ b
    · have hab : a ∉ gtransl b V := fun hm => hdist a h.1 b h.2.1 h.2.2 (mem_gtransl.mp hm)
      obtain ⟨f, hf1, ⟨ef, hfe⟩, hf2⟩ := exists_homogVanish_ne (isZClosed_gtransl hV b) hab
      refine ⟨ef, f, hfe, fun _ _ _ => ⟨hf1, fun hm => hf2 1 ?_⟩⟩
      exact mem_vanish.mp hm a ⟨0, (H0_isSubgroup hH).zero_mem, zero_add a⟩ 1
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose ef f hfe hf using hsep
  set β : GPtV d₀ d₁ Ls → Fin m → ℕ := fun a => ∑ b ∈ R.erase a, ef a b
  set βm : Fin m → ℕ := ∑ a ∈ R, β a
  set B : GPtV d₀ d₁ Ls → MvPolynomial (Var d₀ d₁ m) ℂ :=
    fun a => lpowV α (βm - β a) * ∏ b ∈ R.erase a, f a b
  have hBh : ∀ a ∈ R, IsWeightedHomogeneous wtV (B a) βm := by
    intro a ha
    have hle : β a ≤ βm := Finset.single_le_sum (f := β) (fun _ _ => zero_le) ha
    have h1 := (isWH_lpowV (d₀ := d₀) (d₁ := d₁) α (βm - β a)).mul
      (IsWeightedHomogeneous.prod (R.erase a) (fun b => f a b) (fun b => ef a b)
        fun b _ => hfe a b)
    rwa [tsub_add_cancel_of_le hle] at h1
  have hB : ∀ a ∈ R, B a ∉ vanish (gtransl a V) := by
    intro a ha hmem
    rcases (hpC a).mem_or_mem hmem with h | h
    · exact lpowV_notMem (hpC a) α (hℓ a ha) _ h
    · obtain ⟨b, hb, hfb⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpC a)).mp h
      exact (hf a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).2 hfb
  have hBo : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → B a ∈ vanish (gtransl b V) := by
    intro a ha b hb hab
    have hbe : b ∈ R.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    refine Ideal.mul_mem_left _ _ ?_
    rw [show ∏ x ∈ R.erase a, f a x = f a b * ∏ x ∈ (R.erase a).erase b, f a x from
      (Finset.mul_prod_erase _ _ hbe).symm]
    exact Ideal.mul_mem_right _ _ (hf a b ha hb hab).1
  have hg := LSG.ME.glue (K := ℂ) R (fun a => vanish (gtransl a V)) (fun a _ => hpC a)
    (fun a i => Dhc Ls (chartsV a) (w i)) T' N' B (fun a _ => hT' a) (fun a _ => hTδ' a)
    hN' hB hBo
  refine ⟨w, B, fun j => ∑ a ∈ R, B a ^ 2 * T' a j, ∑ a ∈ R, B a ^ 3 * N' a,
    3 • βm + νm, hwW, fun j => ?_, fun i j => ?_, ?_, fun a ha => (hg a ha).2.2⟩
  · exact (mem_vanish_biUnionV R _).mpr fun a ha => (hg a ha).1 j
  · exact (mem_vanish_biUnionV R _).mpr fun a ha => (hg a ha).2.1 i j
  · exact IsWeightedHomogeneous.sum _ _ _ fun a ha =>
      ((hBh a ha).pow 3).mul (hN'h a ha)

/-! ### The sliced Wüstholz lemma for cosets -/

/-- **Sliced Wüstholz lemma for `E = ⋃_{a ∈ R} (a + H⁰)`** (vector extensions): for `α` with
`ℓ_k ∉ I(a + H⁰)` (`a ∈ R`, all `k`) there is `c₀` such that for every ideal `A` vanishing to order
`> S₀` modulo `I(E)` along `W` in all charts and `ℓ k ≤ S₀`:
`(k+1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_cosets_slV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    (α : Fin m → ℂ) (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH))) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) * k ≤ S0 →
      A ≤ VOg (DmixV Ls) (WmixV W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) S0 → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) *
          hfun blk D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH)))) t ≤
        hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  classical
  obtain ⟨w, B, Q, M, μ, hwW, hQ, hδ, hMh, hMn⟩ := exists_transversals_slV hH hc W R hdist α hℓ
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' blk hD Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  have hpC : ∀ a ∈ R, (vanish (gtransl a (H0 Ls hH))).IsPrime := fun a _ =>
    vanish_gtransl_isPrime (isZClosed_H0 hH) (vanish_H0_isPrime hH) a
  exact wustholz_sl_of_dataV α D (fun i => ∑ a ∈ R, B a • Dhc Ls (chartsV a) (w i))
    (fun k x hx => EulV_mem_vanish k hx) hQ hδ
    (nzd_slV α R (fun a => gtransl a (H0 Ls hH)) hpC hℓ hMh hMn) hQdeg
    (Dw := DmixV Ls) (Ws := WmixV W) (fun k p x => EulV_Dhc k p.1 p.2 x)
    (fun i n x hx => LSG.ME.glued_mem_VOg (Dv := DmixV Ls) R B (fun a => (chartsV a, w i))
      (fun a _ => hwW i) hx) hk hA t

end Trans

end

end LSG.MEV
