import Mathlib
import LSG.ME.PhOp
import LSG.ME.OrderTransl

/-!
# Philippon's operators preserve multihomogeneity (STAGE2 §11, S6)

* `aeval_two_monomial`, **`isWH_of_scale_two`**: (characteristic `0`) if rescaling the `k`-th
  elliptic block by `2` multiplies `f` by `2^n`, then `f` is homogeneous of degree `n` there.
* **`isHomE_phOp`**: `phOp g w c c' κ Q` is homogeneous of degree `2 d` if `Q` is of degree `d`
  (the laws have bidegree `(2, 2)`; `addPt_scl_left`).
-/

open MvPolynomial LSG.Elliptic

namespace LSG.ME

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- Rescaling the `k`-th elliptic block by `2`. -/
noncomputable def sc2 (k : Fin m) :
    MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Var d₀ d₁ m) K :=
  aeval fun v => C ((2 : K) ^ wk k v) * X v

theorem sc2_monomial (k : Fin m) (n : Var d₀ d₁ m →₀ ℕ) (c : K) :
    sc2 k (monomial n c) = monomial n (c * 2 ^ Finsupp.weight (wk k) n) := by
  classical
  rw [sc2, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [show (∏ v, ((2 : K) ^ wk k v) ^ n v) = 2 ^ (∑ v, n v • wk k v) by
    rw [← Finset.prod_pow_eq_pow_sum]; exact Finset.prod_congr rfl fun v _ => by
      rw [← pow_mul, smul_eq_mul, mul_comm]]
  rw [monomial_eq, algebraMap_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), C_mul]
  ring

theorem coeff_sc2 (k : Fin m) (f : MvPolynomial (Var d₀ d₁ m) K) (s : Var d₀ d₁ m →₀ ℕ) :
    (sc2 k f).coeff s = 2 ^ Finsupp.weight (wk k) s * f.coeff s := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [coeff_sum]
  simp only [sc2_monomial, coeff_monomial]
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [hb]) (fun h => by
    simp [MvPolynomial.notMem_support_iff.mp h])]
  simp [mul_comm]

/-- **Homogeneity from the scaling by `2`.** -/
theorem isWH_of_scale_two [CharZero K] {k : Fin m} {f : MvPolynomial (Var d₀ d₁ m) K} {n : ℕ}
    (h : sc2 k f = C ((2 : K) ^ n) * f) : f.IsWeightedHomogeneous (wk k) n := by
  intro s hs
  have hc := congrArg (fun q => q.coeff s) h
  simp only [coeff_sc2, coeff_C_mul] at hc
  have h2 : (2 : K) ^ Finsupp.weight (wk k) s = 2 ^ n := mul_right_cancel₀ hs hc
  have : ((2 ^ Finsupp.weight (wk k) s : ℕ) : K) = ((2 ^ n : ℕ) : K) := by push_cast; exact h2
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective this)

/-- **Philippon's operators are multihomogeneous.** -/
theorem isHomE_phOp [CharZero K] (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m)
    (c c' : Fin m → Fin 2) (κ : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hQ : IsHomE Q d) : IsHomE (phOp g₂ g₃ g w c c' κ Q) (2 • d) := by
  intro k
  refine isWH_of_scale_two ?_
  set ψ := (sc2 k : MvPolynomial (Var d₀ d₁ m) K →ₐ[K] _).toRingHom
  have hψC : ∀ a : K, ψ (C a) = C a := fun a => by simp [ψ, sc2]
  set u : Fin m → PowerSeries (MvPolynomial (Var d₀ d₁ m) K) := fun j =>
    if j = k then PowerSeries.C (C 2) else 1
  have hsub : (fun v => PowerSeries.map ψ (phSub g₂ g₃ g w c c' v)) =
      scl (u ^ 2) (phSub g₂ g₃ g w c c') := by
    funext v
    rw [phSub, addPt_map (PowerSeries.map ψ) (fun a => by
      simp [PowerSeries.algebraMap_apply, hψC])]
    have hA : (fun v => PowerSeries.map ψ (PowerSeries.C (X v))) =
        scl u (fun v => PowerSeries.C (X v : MvPolynomial (Var d₀ d₁ m) K)) := by
      funext v
      rw [PowerSeries.map_C]
      cases v with
      | x i => simp [ψ, sc2, scl, sc]
      | y j => simp [ψ, sc2, scl, sc]
      | z j => simp [ψ, sc2, scl, sc]
      | e j i =>
        simp only [scl_e, u, ψ, sc2, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, wk_e]
        split_ifs <;> simp [mul_comm]
    have hB : (fun v => PowerSeries.map ψ (PowerSeries.map C (phPt g₂ g₃ g w c' v))) =
        fun v => PowerSeries.map C (phPt g₂ g₃ g w c' v) := by
      funext v
      have hψc : ψ.comp C = C := RingHom.ext hψC
      rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hψc]
    rw [hA, hB, addPt_scl_left]
  have key : ψ (phOp g₂ g₃ g w c c' κ Q) = C ((2 : K) ^ (2 * d k)) * phOp g₂ g₃ g w c c' κ Q := by
    rw [phOp, ← PowerSeries.coeff_map, ringHom_aeval (PowerSeries.map ψ) (fun a => by
      simp [PowerSeries.algebraMap_apply, hψC]), hsub, aeval_scl hQ]
    have hprod : (∏ j, (u ^ 2) j ^ d j) = PowerSeries.C (C ((2 : K) ^ (2 * d k))) := by
      rw [Finset.prod_eq_single k (fun j _ hj => by simp [u, hj]) (by simp)]
      simp only [Pi.pow_apply, u, ↓reduceIte]
      rw [← pow_mul, ← map_pow, ← map_pow]
    rw [hprod, PowerSeries.coeff_C_mul]
  simpa [ψ, smul_eq_mul] using key

end LSG.ME
