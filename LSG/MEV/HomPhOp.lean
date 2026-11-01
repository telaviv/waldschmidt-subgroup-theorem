import Mathlib
import LSG.MEV.AVO

/-!
# Philippon's operators and translations preserve block homogeneity (`IsHomV`)

The `E^♮` layer works with the block rescalings `sclV` and the predicate `IsHomV Q d`
(`Q` homogeneous of degree `d k` in every `E^♮` block `k`). The generators of Roy's ideal `A` are
`τ_v^c (phOp σ w c₁ c₂ κ P)` with `P` homogeneous, and `mem_VOg_mixV` needs them homogeneous:

* `isWH_aeval_mul`: substituting polynomials of weight `s · wt v` for the variables `v`
  multiplies weighted degrees by `s`;
* **`isHomV_transl`**: `IsHomV Q d → IsHomV (τ_v^c Q) (3 d)` (the laws have bidegree `(3, 3)`);
* `CW wt n F`: every coefficient of the power series `F` is weighted homogeneous of degree `n`;
  `CW_aeval`;
* `CW_nlaw`: the coefficients of a law with power-series second argument are homogeneous of
  degree `3` in its own block and `0` in the other blocks;
* **`isHomV_phOp`**: `IsHomV Q d → IsHomV (phOp g w c c' κ Q) (3 d)` for every `κ`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Substitutions -/

section Subst

variable {σ : Type*}

theorem isWH_zero_of_le {wt wt' : σ → ℕ} (hle : ∀ v, wt v ≤ wt' v) {f : MvPolynomial σ ℂ}
    (h : f.IsWeightedHomogeneous wt' 0) : f.IsWeightedHomogeneous wt 0 := by
  intro d hd
  have h0 := h hd
  have hle' : Finsupp.weight wt d ≤ Finsupp.weight wt' d := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
    exact Finset.sum_le_sum fun v _ => Nat.mul_le_mul_left _ (hle v)
  omega

/-- Substitution of weighted homogeneous polynomials of weight `s · wt v`. -/
theorem isWH_aeval_mul {wt : σ → ℕ} (s : ℕ) {f : σ → MvPolynomial σ ℂ}
    (hf : ∀ v, (f v).IsWeightedHomogeneous wt (s * wt v)) {Q : MvPolynomial σ ℂ} {n : ℕ}
    (hQ : Q.IsWeightedHomogeneous wt n) : (aeval f Q).IsWeightedHomogeneous wt (s * n) := by
  classical
  rw [Q.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hdn : Finsupp.weight wt d = n := hQ (mem_support_iff.mp hd)
  rw [aeval_monomial, Finsupp.prod]
  have hp := IsWeightedHomogeneous.prod (R := ℂ) (w := wt) d.support (fun v => f v ^ d v)
    (fun v => d v • (s * wt v)) fun v _ => (hf v).pow (d v)
  have := (isWeightedHomogeneous_C (R := ℂ) wt (Q.coeff d)).mul hp
  rw [algebraMap_eq]
  convert this using 1
  rw [← hdn, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum, zero_add]
  exact Finset.sum_congr rfl fun v _ => by simp only [smul_eq_mul]; ring

end Subst

/-- **Translations multiply block degrees by `3`.** -/
theorem isHomV_transl {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (v : GPtV d₀ d₁ Ls) (c : Fin m → LC) : IsHomV (τ Ls v c Q) (fun k => 3 * d k) := by
  intro k
  refine isWH_aeval_mul 3 (fun u => ?_) (hQ k)
  cases u with
  | x i =>
    simp only [translVar, wb, blk_x, reduceCtorEq, ite_false, mul_zero]
    exact (isWeightedHomogeneous_X ℂ _ _).add (isWeightedHomogeneous_C _ _)
  | y j =>
    simp only [translVar, wb, blk_y, reduceCtorEq, ite_false, mul_zero]
    exact LSG.ME.isWH_mul' (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_X ℂ _ _)
      (by simp [wb])
  | z j =>
    simp only [translVar, wb, blk_z, reduceCtorEq, ite_false, mul_zero]
    exact LSG.ME.isWH_mul' (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_X ℂ _ _)
      (by simp [wb])
  | e k' i =>
    simp only [translVar]
    by_cases hk : k' = k
    · subst hk
      simpa [wb] using lawPolyV_isWH (Ls := Ls) (d₀ := d₀) (d₁ := d₁) (c k') k' (repV (v.2.2 k')) i
    · have h0 := lawPolyV_isWH_wo (Ls := Ls) (d₀ := d₀) (d₁ := d₁) (c k') k' (repV (v.2.2 k')) i
      have : wb blk (Blk.e k) (.e k' i : Var d₀ d₁ m) = 0 := by simp [wb, hk]
      rw [this, mul_zero]
      refine isWH_zero_of_le (fun u => ?_) h0
      simp only [wb, wo]
      split_ifs with h1 h2 <;> simp_all

/-! ### Coefficientwise homogeneity of power series -/

section CW

variable {σ : Type*}

local notation "PSσ" => PowerSeries (MvPolynomial σ ℂ)

/-- Every coefficient of `F` is weighted homogeneous of degree `n`. -/
def CW (wt : σ → ℕ) (n : ℕ) (F : PSσ) : Prop :=
  ∀ i, (PowerSeries.coeff i F).IsWeightedHomogeneous wt n

theorem CW_add {wt : σ → ℕ} {n : ℕ} {F G : PSσ} (hF : CW wt n F) (hG : CW wt n G) :
    CW wt n (F + G) := fun i => by rw [map_add]; exact (hF i).add (hG i)

theorem CW_mul {wt : σ → ℕ} {n n' : ℕ} {F G : PSσ} (hF : CW wt n F) (hG : CW wt n' G) :
    CW wt (n + n') (F * G) := fun i => by
  rw [PowerSeries.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ fun p _ => (hF p.1).mul (hG p.2)

theorem CW_one {wt : σ → ℕ} : CW wt 0 (1 : PSσ) := fun i => by
  rw [PowerSeries.coeff_one]; split_ifs
  · exact isWeightedHomogeneous_one ℂ wt
  · exact isWeightedHomogeneous_zero ℂ wt 0

theorem CW_pow {wt : σ → ℕ} {n : ℕ} {F : PSσ} (hF : CW wt n F) (k : ℕ) : CW wt (k * n) (F ^ k) := by
  induction k with
  | zero => simpa using (CW_one (wt := wt))
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact CW_mul ih hF

theorem CW_prod {ι : Type*} (s : Finset ι) {wt : σ → ℕ} (f : ι → PSσ) (e : ι → ℕ)
    (h : ∀ i ∈ s, CW wt (e i) (f i)) : CW wt (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CW_one (wt := wt))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact CW_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CW_sum {ι : Type*} (s : Finset ι) {wt : σ → ℕ} {n : ℕ} (f : ι → PSσ)
    (h : ∀ i ∈ s, CW wt n (f i)) : CW wt n (∑ i ∈ s, f i) := fun j => by
  rw [map_sum]; exact IsWeightedHomogeneous.sum _ _ _ fun i hi => h i hi j

theorem CW_C {wt : σ → ℕ} {n : ℕ} {p : MvPolynomial σ ℂ} (hp : p.IsWeightedHomogeneous wt n) :
    CW wt n (PowerSeries.C p) := fun i => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact isWeightedHomogeneous_zero ℂ wt n

theorem CW_mapC {wt : σ → ℕ} (B : PowerSeries ℂ) :
    CW wt 0 (PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) B) := fun i => by
  rw [PowerSeries.coeff_map]; exact isWeightedHomogeneous_C wt _

theorem CW_algebraMap {wt : σ → ℕ} (a : ℂ) : CW wt 0 (algebraMap ℂ PSσ a) := by
  rw [PowerSeries.algebraMap_apply]; exact CW_C (isWeightedHomogeneous_C wt _)

/-- Substitution into power series. -/
theorem CW_aeval {wt : σ → ℕ} (s : ℕ) {f : σ → PSσ} (hf : ∀ v, CW wt (s * wt v) (f v))
    {Q : MvPolynomial σ ℂ} {n : ℕ} (hQ : Q.IsWeightedHomogeneous wt n) :
    CW wt (s * n) (aeval f Q) := by
  classical
  rw [Q.as_sum, map_sum]
  refine CW_sum _ _ fun d hd => ?_
  have hdn : Finsupp.weight wt d = n := hQ (mem_support_iff.mp hd)
  rw [aeval_monomial, Finsupp.prod]
  have hp := CW_prod d.support (fun v => f v ^ d v) (fun v => d v * (s * wt v))
    fun v _ => CW_pow (hf v) (d v)
  have := CW_mul (CW_algebraMap (wt := wt) (Q.coeff d)) hp
  convert this using 1
  rw [← hdn, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum, zero_add]
  exact Finset.sum_congr rfl fun v _ => by simp only [smul_eq_mul]; ring

end CW

/-! ### The laws -/

local notation "PS" => PowerSeries (MvPolynomial (Var d₀ d₁ m) ℂ)

/-- **Coefficientwise homogeneity of a law** with power-series second argument. -/
theorem CW_nlaw (c : LC) (k k' : Fin m) (a b : ℂ) (B : Fin 5 → PowerSeries ℂ) (i : Fin 5) :
    CW (wb blk (Blk.e k)) (3 * wb blk (Blk.e k) (.e k' i : Var d₀ d₁ m))
      (nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
        (fun i => PowerSeries.C (X (.e k' i))) (fun i => PowerSeries.map C (B i)) i) := by
  intro n
  set L := nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
      (fun i => PowerSeries.C (X (.e k' i))) (fun i => PowerSeries.map C (B i)) i
  have key : ∀ (w : Var d₀ d₁ m → ℕ) (u : MvPolynomial (Var d₀ d₁ m) ℂ),
      (∀ l, scw w (X (.e k' l) : MvPolynomial (Var d₀ d₁ m) ℂ) = u * X (.e k' l)) →
      scw w (PowerSeries.coeff n L) = u ^ 3 * PowerSeries.coeff n L := by
    intro w u hu
    have h1 : PowerSeries.map (scw w).toRingHom L =
        nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
          ((PowerSeries.C u) • fun i => PowerSeries.C (X (.e k' i)))
          (fun i => PowerSeries.map C (B i)) i := by
      rw [show L = NLaw (algebraMap ℂ PS a) (algebraMap ℂ PS b) c.1 c.2.1 c.2.2
        (fun i => PowerSeries.C (X (.e k' i))) (fun i => PowerSeries.map C (B i)) i from rfl,
        NLaw_map, map_alg_algebraMap, map_alg_algebraMap]
      congr 1
      · funext l; simp [PowerSeries.map_C, hu]
      · funext l; exact map_alg_mapC _ _
    rw [nlawc_smul_left] at h1
    have h2 := congrArg (PowerSeries.coeff n) h1
    rw [PowerSeries.coeff_map] at h2
    simp only [Pi.smul_apply, smul_eq_mul, ← map_pow,
      PowerSeries.coeff_C_mul] at h2
    exact h2
  apply isWH_of_scw
  rw [key (wb blk (Blk.e k)) (C (2 ^ wb blk (Blk.e k) (.e k' i : Var d₀ d₁ m)))
    (fun l => by simp [scw_X, wb]), ← map_pow, ← pow_mul, mul_comm (wb _ _ _) 3]

theorem CW_phSub (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (k : Fin m)
    (v : Var d₀ d₁ m) : CW (wb blk (Blk.e k)) (3 * wb blk (Blk.e k) v) (phSub Ls g w c c' v) := by
  cases v with
  | x i =>
    simp only [phSub, wb, blk_x, reduceCtorEq, ite_false, mul_zero]
    have hX : (X (.x i) : MvPolynomial (Var d₀ d₁ m) ℂ).IsWeightedHomogeneous
        (wb blk (Blk.e k)) 0 := by
      simpa [wb] using isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (.x i : Var d₀ d₁ m)
    exact CW_add (CW_C hX) (CW_mapC _)
  | y j =>
    simp only [phSub, wb, blk_y, reduceCtorEq, ite_false, mul_zero]
    have hX : (X (.y j) : MvPolynomial (Var d₀ d₁ m) ℂ).IsWeightedHomogeneous
        (wb blk (Blk.e k)) 0 := by
      simpa [wb] using isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (.y j : Var d₀ d₁ m)
    exact CW_mul (CW_C hX) (CW_mapC _)
  | z j =>
    simp only [phSub, wb, blk_z, reduceCtorEq, ite_false, mul_zero]
    have hX : (X (.z j) : MvPolynomial (Var d₀ d₁ m) ℂ).IsWeightedHomogeneous
        (wb blk (Blk.e k)) 0 := by
      simpa [wb] using isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (.z j : Var d₀ d₁ m)
    exact CW_mul (CW_C hX) (CW_mapC _)
  | e k' i =>
    simp only [phSub]
    exact CW_nlaw (c k') k k' _ _ _ i

/-- **Philippon's operators multiply block degrees by `3`**, for every order `κ`. -/
theorem isHomV_phOp (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d) :
    IsHomV (phOp Ls g w c c' κ Q) (fun k => 3 * d k) := fun k =>
  CW_aeval 3 (fun v => CW_phSub g w c c' k v) (hQ k) κ

end LSG.MEV
