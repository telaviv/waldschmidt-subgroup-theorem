import Mathlib
import LSG.MEV.Flat
import LSG.ME.Order

/-!
# Invariant derivations of `G̃` in fixed charts; flows and the Taylor formula

* `Dv ch w`: the derivation of `ℂ[Var]` with `X ↦ ξ`, `Y ↦ ηY`, `Z ↦ −ηZ` and, in `E^♮` block `k`,
  the chart derivation `dvalB (ch k)` of direction `w_k = (ζ_k, β_k)` (`s = ζ_k/2`); degree `+2` in
  each `E^♮` block. **`Dv_add`, `Dv_smul`**: linear in `w`; **`Dv_comm`**: `Dv ch w`, `Dv ch w'`
  commute exactly (same charts).
* `IsVFlow ch w Γ`: `Γ' = Dv ch w (X)(Γ)`; **`deriv_aeval_vflow`**, **`taylorV`**:
  `n! [zⁿ] Q(Γ) = (Dv^n Q)(Γ(0))`.
* **`ZG_isVFlow`**: the canonical formal point is a flow in the canonical charts.
* **`polarize`**: for commuting `A, B`, vanishing of `φ((αA + βB)ⁿ Q)` for all `α, β` and `n ≤ N`
  gives `φ(AⁱBʲQ) = 0` for `i + j ≤ N` (characteristic `0`).
* **`dv_words_of_ordGt`**: formal order `> N` at `p` gives `(Dv_w^i Dv_{w'}^j Q)(p) = 0` for
  `w, w' ∈ W`, `i + j ≤ N` (canonical charts at `p`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk c2)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Commutation of the chart derivations -/

theorem dvalB_comm {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (D D' : Derivation S T T)
    (a : Fin 2) (g₂ g₃ s β s' β' : T) (P : Fin 5 → T) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0)
    (hg₂' : D' g₂ = 0) (hg₃' : D' g₃ = 0) (hs : D s' = 0) (hβ : D β' = 0) (hs' : D' s = 0)
    (hβ' : D' β = 0) (hP : ∀ l, D (P l) = dvalB a g₂ g₃ s β P l)
    (hP' : ∀ l, D' (P l) = dvalB a g₂ g₃ s' β' P l) (l : Fin 5) :
    D (dvalB a g₂ g₃ s' β' P l) = D' (dvalB a g₂ g₃ s β P l) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2; have h3 := hP 3; have h4 := hP 4
  have h0' := hP' 0; have h1' := hP' 1; have h2' := hP' 2; have h3' := hP' 3; have h4' := hP' 4
  fin_cases a <;> fin_cases l <;>
    simp only [dvalB, c2, rhoh, Pe, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons] at h0 h1 h2 h3 h4 h0' h1' h2' h3' h4' ⊢ <;>
    simp only [map_add, map_sub, map_neg, map_mul, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
      smul_eq_mul, nsmul_eq_mul, LSG.ME.D_ofNat, h0, h1, h2, h3, h4, h0', h1', h2', h3', h4', hg₂,
      hg₃, hg₂', hg₃', hs, hβ, hs', hβ', mul_zero, zero_mul, add_zero, zero_add, sub_zero,
      Derivation.map_one_eq_zero, Nat.cast_ofNat] <;>
    ring

/-! ### The derivations -/

variable (Ls) in
/-- The values of the chart derivation on the variables. -/
noncomputable def dvV (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) :
    Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .x i => C (w.1 i)
  | .y j => C (w.2.1 j) * X (.y j)
  | .z j => -C (w.2.1 j) * X (.z j)
  | .e k l => dvalB (ch k) (C (g2L Ls k)) (C (g3L Ls k)) (C ((w.2.2 k).1 / 2)) (C (w.2.2 k).2)
      (bvars d₀ d₁ k) l

variable (Ls) in
/-- **The invariant derivation** of direction `w` in the charts `ch`. -/
noncomputable def Dv (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  mkDerivation ℂ (dvV Ls ch w)

theorem Dv_X (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    Dv Ls ch w (X v) = dvV Ls ch w v := mkDerivation_X _ _ _

theorem dvalB_add {T : Type*} [CommRing T] (a : Fin 2) (g₂ g₃ s β s' β' : T) (P : Fin 5 → T)
    (l : Fin 5) : dvalB a g₂ g₃ (s + s') (β + β') P l =
      dvalB a g₂ g₃ s β P l + dvalB a g₂ g₃ s' β' P l := by
  fin_cases a <;> fin_cases l <;> simp [dvalB] <;> ring

theorem dvalB_smul {T : Type*} [CommRing T] (a : Fin 2) (g₂ g₃ c s β : T) (P : Fin 5 → T)
    (l : Fin 5) : dvalB a g₂ g₃ (c * s) (c * β) P l = c * dvalB a g₂ g₃ s β P l := by
  fin_cases a <;> fin_cases l <;> simp [dvalB] <;> ring

theorem Dv_add (ch : Fin m → Fin 2) (w w' : LieV ℂ d₀ d₁ m) :
    Dv Ls ch (w + w') = Dv Ls ch w + Dv Ls ch w' := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply, Dv_X, Dv_X, Dv_X]
  cases v with
  | x i => simp [dvV]
  | y j => simp [dvV]; ring
  | z j => simp [dvV]; ring
  | e k l =>
    simp only [dvV, Prod.snd_add, Pi.add_apply, Prod.fst_add, add_div, map_add]
    exact dvalB_add _ _ _ _ _ _ _ _ _

theorem Dv_smul (ch : Fin m → Fin 2) (a : ℂ) (w : LieV ℂ d₀ d₁ m) :
    Dv Ls ch (a • w) = a • Dv Ls ch w := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.smul_apply, Dv_X, Dv_X, smul_eq_C_mul]
  cases v with
  | x i => simp [dvV]
  | y j => simp [dvV]; ring
  | z j => simp [dvV]; ring
  | e k l =>
    simp only [dvV, Prod.smul_snd, Pi.smul_apply, Prod.smul_fst, smul_eq_mul]
    rw [show a * (w.2.2 k).1 / 2 = a * ((w.2.2 k).1 / 2) by ring, map_mul, map_mul]
    exact dvalB_smul _ _ _ _ _ _ _ _

theorem Dv_C (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (a : ℂ) :
    Dv Ls ch w (C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]; exact (Dv Ls ch w).map_algebraMap a

/-- **The chart derivations commute.** -/
theorem Dv_comm (ch : Fin m → Fin 2) (w w' : LieV ℂ d₀ d₁ m) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    Dv Ls ch w (Dv Ls ch w' Q) = Dv Ls ch w' (Dv Ls ch w Q) := by
  have h : ⁅Dv Ls ch w, Dv Ls ch w'⁆ = 0 := by
    refine MvPolynomial.derivation_ext fun v => ?_
    rw [Derivation.commutator_apply, Derivation.zero_apply, Dv_X, Dv_X, sub_eq_zero]
    cases v with
    | x i => simp [dvV, Dv_C]
    | y j => simp [dvV, Dv_C, Dv_X]; ring
    | z j => simp [dvV, Dv_C, Dv_X]; ring
    | e k l =>
      simp only [dvV]
      exact dvalB_comm _ _ _ _ _ _ _ _ _ _ (Dv_C _ _ _) (Dv_C _ _ _) (Dv_C _ _ _) (Dv_C _ _ _)
        (Dv_C _ _ _) (Dv_C _ _ _) (Dv_C _ _ _) (Dv_C _ _ _)
        (fun l' => by simp only [bvars]; rw [Dv_X]; rfl)
        (fun l' => by simp only [bvars]; rw [Dv_X]; rfl) l
  have := congrArg (fun D => D Q) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
  exact this

/-! ### Flows and the Taylor formula -/

section Flow

variable {R : Type*} [CommRing R] [Algebra ℂ R]

local notation "dz" => (PowerSeries.derivative (R := R))

variable (Ls) in
/-- `Γ` is a flow of `Dv ch w`. -/
def IsVFlow (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (Γ : Var d₀ d₁ m → PowerSeries R) : Prop :=
  ∀ v, dz (Γ v) = aeval Γ (dvV Ls ch w v)

theorem deriv_aeval_vflow {ch : Fin m → Fin 2} {w : LieV ℂ d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsVFlow Ls ch w Γ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    dz (aeval Γ Q) = aeval Γ (Dv Ls ch w Q) := by
  rw [LSG.ME.derivative_aeval, Dv, LSG.ME.mkDerivation_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [hΓ v, map_mul, mul_comm]

theorem iterate_deriv_aeval_vflow {ch : Fin m → Fin 2} {w : LieV ℂ d₀ d₁ m}
    {Γ : Var d₀ d₁ m → PowerSeries R} (hΓ : IsVFlow Ls ch w Γ) (n : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    dz^[n] (aeval Γ Q) = aeval Γ ((Dv Ls ch w)^[n] Q) := by
  induction n generalizing Q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, deriv_aeval_vflow hΓ, ih, Function.iterate_succ_apply]

/-- **Taylor formula** along a flow. -/
theorem taylorV {ch : Fin m → Fin 2} {w : LieV ℂ d₀ d₁ m} {Γ : Var d₀ d₁ m → PowerSeries R}
    (hΓ : IsVFlow Ls ch w Γ) (n : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    (n.factorial : R) * PowerSeries.coeff n (aeval Γ Q) =
      aeval (fun v => PowerSeries.constantCoeff (Γ v)) ((Dv Ls ch w)^[n] Q) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative, iterate_deriv_aeval_vflow hΓ,
    LSG.ME.constantCoeff_aeval (K := ℂ)]

end Flow

theorem derivative_rescale_exp (a : ℂ) :
    PowerSeries.derivative (R := ℂ) (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    PowerSeries.coeff_C_mul, map_inv₀, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The canonical charts at a point. -/
noncomputable def chartsV (p : GPtV d₀ d₁ Ls) : Fin m → Fin 2 := fun k => chartV (p.2.2 k)

/-- **The canonical formal point is a flow** in the canonical charts. -/
theorem ZG_isVFlow (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) :
    IsVFlow Ls (chartsV p) w (ZG Ls p w) := by
  intro v
  cases v with
  | x i =>
    simp [ZG, ExpV, dvV, PowerSeries.algebraMap_apply]
  | y j =>
    simp only [ZG, ExpV, dvV, map_mul, aeval_C, aeval_X, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_C, mul_zero, add_zero, derivative_rescale_exp,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | z j =>
    simp only [ZG, ExpV, dvV, map_mul, map_neg, aeval_C, aeval_X, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_C, mul_zero, add_zero, derivative_rescale_exp,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | e k l =>
    have h := (ZB_spec (p.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2).1.ode l
    simp only [ZG]
    rw [h, dvV, ← AlgHom.coe_toRingHom, dvalB_map]
    simp only [AlgHom.coe_toRingHom, aeval_C]
    congr 1
    funext l'; simp [bvars, ZG]

/-! ### Polarization -/

theorem polarize {M : Type*} [AddCommGroup M] [Module ℂ M] (A B : Module.End ℂ M)
    (hAB : Commute A B) (φ : M →ₗ[ℂ] ℂ) (Q : M) (N : ℕ)
    (h : ∀ α β : ℂ, ∀ n ≤ N, φ (((α • A + β • B) ^ n) Q) = 0) {i j : ℕ} (hij : i + j ≤ N) :
    φ ((A ^ i * B ^ j) Q) = 0 := by
  classical
  set n := i + j
  -- the polynomial in `α`
  set p : Polynomial ℂ := ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((n.choose k : ℂ) * φ ((A ^ k * B ^ (n - k)) Q)) * Polynomial.X ^ k with hpdef
  have hp : ∀ α : ℂ, p.eval α = 0 := by
    intro α
    have h1 := h α 1 n hij
    rw [one_smul, (hAB.smul_left α).add_pow, LinearMap.sum_apply, map_sum] at h1
    rw [hpdef, Polynomial.eval_finset_sum, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_pow]
    rw [smul_mul_assoc, smul_mul_assoc]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.mul_apply,
      Module.End.natCast_apply, map_nsmul, nsmul_eq_mul]
    ring
  have hp0 : p = 0 := Polynomial.funext fun α => by rw [hp α, Polynomial.eval_zero]
  have hcoef := congrArg (fun q => q.coeff i) hp0
  simp only [hpdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoef
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
    (fun hi => absurd (Finset.mem_range.mpr (by omega)) hi)] at hcoef
  simp only [ite_true] at hcoef
  have hch : (n.choose i : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [show n - i = j by omega] at hcoef
  exact (mul_eq_zero.mp hcoef).resolve_left hch

end LSG.MEV
