/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.PerTanFib

/-!
# M2.7 for `B = fun _ => aBlockV`: `PerTanPiv`, part 1 (rational coordinates)

Coordinates in the period basis: `Φ1 x = Σ_e x_e perVec e` (`x ∈ ℚ⁴`, injective, `Φ1_eq_zero`), copywise `Φq`.
Multiplication by `ζ` in these coordinates is `Tq` (`perVec 4 = −Σ_{e<4} perVec e`): `Φ1 (Tq x) = [ζ](Φ1 x)`
(`Φ1_Tq`), and the `σ̄`-coordinate `Ψq x = Σ_e x_e ζ^{4e}` (the fibre period up to `cη`) satisfies
`Ψq (Tq x) = ζ⁴ Ψq x` (`Ψq_Tq`). **`Wsub t = {x ∈ ℚ^{4m} : Φq x ∈ t}`** is a `Tq`-stable `ℚ`-subspace
(`Wsub_Tm`, for an abelian tangent `t`), and it is "large": `2 dim_ℂ t ≤ dim_ℚ Wsub t` (`finrank_t_le`), since the
lattice points of `t` (which span `t` over `ℝ`) lie in `Φq (Wsub t)`.
-/

noncomputable section

open Module LSG.JacAn LSG.JacAn.Beta LSG.JacBlock

namespace LSG.JacBlockV

local notation "ζ" => LSG.JacAn.Beta.zetaN 5

variable {m : ℕ}

/-! ### Coordinates -/

/-- `x ↦ Σ_e x_e perVec e`. -/
def Φ1 (x : Fin 4 → ℚ) : Fin 2 → ℂ := ∑ e : Fin 4, (x e : ℂ) • perVec (e : ℕ)

lemma Φ1_add (x y : Fin 4 → ℚ) : Φ1 (x + y) = Φ1 x + Φ1 y := by
  simp [Φ1, add_smul, Finset.sum_add_distrib]

lemma Φ1_smul (q : ℚ) (x : Fin 4 → ℚ) : Φ1 (q • x) = (q : ℂ) • Φ1 x := by
  simp [Φ1, Finset.smul_sum, smul_smul]

lemma Φ1_zero : Φ1 0 = 0 := by simp [Φ1]

lemma Φ1_eq_zero {x : Fin 4 → ℚ} (h : Φ1 x = 0) : x = 0 := by
  have hli := latBasis.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have h' : ∑ e : Fin 4, ((x e : ℝ)) • latBasis e = 0 := by
    rw [← h, Φ1]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [latBasis_apply, ← Complex.coe_smul, Complex.ofReal_ratCast]
  funext e
  exact_mod_cast hli _ h' e

/-- Copywise coordinates. -/
def Φq (x : Fin m → Fin 4 → ℚ) : Fin m → Fin 2 → ℂ := fun k => Φ1 (x k)

/-- `Φq` as a `ℚ`-linear map. -/
def ΦL : (Fin m → Fin 4 → ℚ) →ₗ[ℚ] (Fin m → Fin 2 → ℂ) where
  toFun := Φq
  map_add' x y := funext fun k => Φ1_add (x k) (y k)
  map_smul' q x := funext fun k => by
    change Φ1 (q • x k) = q • Φ1 (x k)
    rw [Φ1_smul, ← Rat.cast_smul_eq_qsmul ℂ]

/-- Lattice points have integral coordinates. -/
lemma Φ1_int (nn : Fin 4 → ℤ) : Φ1 (fun e => (nn e : ℚ)) = ∑ e : Fin 4, nn e • perVec (e : ℕ) := by
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Rat.cast_intCast, Int.cast_smul_eq_zsmul]

/-- Multiplication by `ζ` in the period coordinates. -/
def Tq (x : Fin 4 → ℚ) : Fin 4 → ℚ
  | 0 => -x 3
  | 1 => x 0 - x 3
  | 2 => x 1 - x 3
  | 3 => x 2 - x 3

lemma Tq_0 (x : Fin 4 → ℚ) : Tq x 0 = -x 3 := rfl
lemma Tq_1 (x : Fin 4 → ℚ) : Tq x 1 = x 0 - x 3 := rfl
lemma Tq_2 (x : Fin 4 → ℚ) : Tq x 2 = x 1 - x 3 := rfl
lemma Tq_3 (x : Fin 4 → ℚ) : Tq x 3 = x 2 - x 3 := rfl

lemma Tq_zero : Tq 0 = 0 := by
  funext j; fin_cases j <;> simp [Tq_0, Tq_1, Tq_2, Tq_3]

lemma Tq_iter_zero (j : ℕ) : Tq^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, Tq_zero]

lemma val3 : ((3 : Fin 4) : ℕ) = 3 := rfl

lemma Φ1_Tq (x : Fin 4 → ℚ) : Φ1 (Tq x) = ![ζ * Φ1 x 0, ζ ^ 2 * Φ1 x 1] := by
  funext j
  fin_cases j
  · simp only [Φ1, Fin.sum_univ_four, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, perVec_eq,
      Tq_0, Tq_1, Tq_2, Tq_3, Fin.val_zero, Fin.val_one, Fin.val_two, val3]
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Fin.isValue, Fin.val_zero]
    push_cast
    linear_combination (-(x 3 : ℂ)) * cJ 0 * zsum
  · simp only [Φ1, Fin.sum_univ_four, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, perVec_eq,
      Tq_0, Tq_1, Tq_2, Tq_3, Fin.val_zero, Fin.val_one, Fin.val_two, val3]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.isValue, Fin.val_one]
    push_cast
    linear_combination (-(x 3 : ℂ)) * cJ 1 * (zsum + (ζ + ζ ^ 3) * z5)

/-- The `σ̄`-coordinate `Σ_e x_e ζ^{4e}`. -/
def Ψq (x : Fin 4 → ℚ) : ℂ := ∑ e : Fin 4, (x e : ℂ) * ζ ^ (4 * (e : ℕ))

lemma Ψq_add (x y : Fin 4 → ℚ) : Ψq (x + y) = Ψq x + Ψq y := by
  simp [Ψq, add_mul, Finset.sum_add_distrib]

lemma Ψq_smul (q : ℚ) (x : Fin 4 → ℚ) : Ψq (q • x) = (q : ℂ) * Ψq x := by
  simp [Ψq, Finset.mul_sum, mul_assoc]

lemma Ψq_zero : Ψq 0 = 0 := by simp [Ψq]

lemma Ψq_single0 : Ψq (Pi.single 0 1) = 1 := by
  simp [Ψq, Fin.sum_univ_four, Pi.single_apply]

lemma Ψq_Tq (x : Fin 4 → ℚ) : Ψq (Tq x) = ζ ^ 4 * Ψq x := by
  simp only [Ψq, Fin.sum_univ_four, Tq_0, Tq_1, Tq_2, Tq_3, Fin.val_zero, Fin.val_one, Fin.val_two, val3]
  push_cast
  linear_combination (-(x 3 : ℂ)) * (zsum + (ζ ^ 3 + ζ ^ 2 * (ζ ^ 5 + 1) + ζ * (ζ ^ 10 + ζ ^ 5 + 1)) * z5)

lemma Ψq_Tq_iter (j : ℕ) (x : Fin 4 → ℚ) : Ψq (Tq^[j] x) = ζ ^ (4 * j) * Ψq x := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', Ψq_Tq, ih, mul_add, pow_add]; ring

lemma Tq_iter_single (e : Fin 4) : Tq^[(e : ℕ)] (Pi.single 0 1) = Pi.single e 1 := by
  fin_cases e <;> funext j <;> fin_cases j <;>
    simp [Function.iterate_succ_apply', Tq_0, Tq_1, Tq_2, Tq_3, Pi.single_apply]

lemma Ψq_alg (x : Fin 4 → ℚ) : IsAlgebraic ℚ (Ψq x) := by
  have hz5 : IsAlgebraic ℚ ζ :=
    ⟨Polynomial.X ^ 5 - 1, Polynomial.X_pow_sub_C_ne_zero (by norm_num) 1, by simp [z5]⟩
  rw [← mem_algebraicClosure_iff]
  refine sum_mem fun e _ => mul_mem ?_ (pow_mem (mem_algebraicClosure_iff.mpr hz5) _)
  exact mem_algebraicClosure_iff.mpr ((eq_ratCast (algebraMap ℚ ℂ) (x e)) ▸ isAlgebraic_algebraMap (x e))

/-- Copywise `Tq`. -/
def TmI {ι : Type*} (x : ι → Fin 4 → ℚ) : ι → Fin 4 → ℚ := fun k => Tq (x k)

lemma TmI_iter {ι : Type*} (j : ℕ) (x : ι → Fin 4 → ℚ) (k : ι) : (TmI^[j] x) k = Tq^[j] (x k) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', TmI, ih]

lemma Φq_TmI (x : Fin m → Fin 4 → ℚ) : Φq (TmI x) = Dz (Φq x) := by
  funext k
  rw [Φq, TmI, Φ1_Tq]
  rfl

/-! ### The rational subspace -/

/-- **`W = {x ∈ ℚ^{4m} : Φq x ∈ t}`**. -/
def Wsub (t : Submodule ℂ (Fin m → Fin 2 → ℂ)) : Submodule ℚ (Fin m → Fin 4 → ℚ) :=
  (t.restrictScalars ℚ).comap ΦL

lemma mem_Wsub {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} {x : Fin m → Fin 4 → ℚ} : x ∈ Wsub t ↔ Φq x ∈ t :=
  Iff.rfl

lemma Wsub_TmI {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (ht : LSG.W88.IsAbelianTangentA t)
    {x : Fin m → Fin 4 → ℚ} (hx : x ∈ Wsub t) : TmI x ∈ Wsub t := by
  rw [mem_Wsub, Φq_TmI]
  exact Dz_mem ht hx

lemma Wsub_TmI_iter {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (ht : LSG.W88.IsAbelianTangentA t) (j : ℕ)
    {x : Fin m → Fin 4 → ℚ} (hx : x ∈ Wsub t) : TmI^[j] x ∈ Wsub t := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact Wsub_TmI ht ih

/-- **`2 dim_ℂ t ≤ dim_ℚ W`**: the lattice points of `t` lie in `Φq W`. -/
lemma finrank_t_le {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (ht : LSG.W88.IsAbelianTangentA t) :
    2 * finrank ℂ t ≤ finrank ℚ (Wsub t) := by
  set bW := Module.finBasis ℚ (Wsub t)
  have hle : (t.restrictScalars ℝ : Submodule ℝ (Fin m → Fin 2 → ℂ)) ≤
      Submodule.span ℝ (Set.range fun j => ΦL (bW j : Fin m → Fin 4 → ℚ)) := by
    rw [ht, Submodule.span_le]
    rintro z ⟨hzt, hzl⟩
    choose nn hnn using fun k => LSG.W88.latt_repr' (hzl k)
    set x : Fin m → Fin 4 → ℚ := fun k e => (nn k e : ℚ)
    have hx : ΦL x = z := funext fun k => by
      change Φ1 (fun e => (nn k e : ℚ)) = z k
      rw [Φ1_int, hnn k]
    have hxW : x ∈ Wsub t := by rw [mem_Wsub]; change ΦL x ∈ t; rw [hx]; exact hzt
    have hsum := bW.sum_repr ⟨x, hxW⟩
    have hx' : x = ∑ j, bW.repr ⟨x, hxW⟩ j • (bW j : Fin m → Fin 4 → ℚ) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [← hx, hx', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, ← Rat.cast_smul_eq_qsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have h1 : finrank ℝ (t.restrictScalars ℝ) = 2 * finrank ℂ t := finrank_real_of_complex ↥t
  have h2 := Submodule.finrank_mono hle
  have h3 := finrank_range_le_card (R := ℝ) fun j => ΦL (bW j : Fin m → Fin 4 → ℚ)
  rw [Fintype.card_fin] at h3
  unfold Set.finrank at h3
  omega

end LSG.JacBlockV
