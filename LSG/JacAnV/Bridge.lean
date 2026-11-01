/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.Laws

/-!
# M2.2: the `pderiv` ↔ `fderiv` bridge for the fibre laws

The fibre laws `lawT` (`Laws.lean`) are stated with Fréchet partials of `lawK`. The `VBlock` instance defines its
laws from the polynomial data by `MvPolynomial.pderiv`. Here:
* **`mvPoly_hasFDerivAt`**: `D_x eval(p) = Σ_i proj_i · eval_x (∂p/∂X_i)`, for any `p : MvPolynomial σ ℂ`;
* **`A1Facts.dXlaw_eq_pderiv`**, **`A1Facts.dYlaw_eq_pderiv`**: if `eval (Sum.elim X Y) P = lawK k m X Y`, then
  `∂_X law(X, Y)[S] = Σ_a S_a · eval (∂P/∂X_a)` and `∂_Y law(X, Y)[S'] = Σ_a S'_a · eval (∂P/∂Y_a)`.
-/

noncomputable section

open MvPolynomial

namespace LSG.JacAn

/-- **The derivative of a polynomial function is given by its formal partials.** -/
theorem mvPoly_hasFDerivAt {σ : Type*} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun x => eval x p)
      (∑ i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).smulRight (eval x (pderiv i p))) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (∑ i, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).smulRight
        (eval x (pderiv i (C a)))) = 0 := by simp
    rw [e]
    simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    refine ((hp.add hq).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
    simp [Finset.sum_add_distrib, mul_add]
  | mul_X p i hp =>
    have hX : HasFDerivAt (fun x : σ → ℂ => x i) (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i) x :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).hasFDerivAt
    have h := hp.mul hX
    refine (h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_X, map_add, map_mul, eval_X]
    simp only [Pi.single_apply, apply_ite (eval x), map_one, map_zero, mul_add, Finset.sum_add_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring

/-- `V ↦ Sum.elim V 0`. -/
def elimL : (Fin 9 → ℂ) →L[ℂ] (Fin 9 ⊕ Fin 9 → ℂ) := LinearMap.toContinuousLinearMap
  { toFun := fun V => Sum.elim V 0
    map_add' := fun V W => by funext i; cases i <;> simp
    map_smul' := fun a V => by funext i; cases i <;> simp }

/-- `V ↦ Sum.elim 0 V`. -/
def elimR : (Fin 9 → ℂ) →L[ℂ] (Fin 9 ⊕ Fin 9 → ℂ) := LinearMap.toContinuousLinearMap
  { toFun := fun V => Sum.elim 0 V
    map_add' := fun V W => by funext i; cases i <;> simp
    map_smul' := fun a V => by funext i; cases i <;> simp }

lemma hasFDerivAt_elimL (X Y : Fin 9 → ℂ) :
    HasFDerivAt (fun X : Fin 9 → ℂ => (Sum.elim X Y : Fin 9 ⊕ Fin 9 → ℂ)) elimL X :=
  (elimL.hasFDerivAt.add_const (Sum.elim (0 : Fin 9 → ℂ) Y)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun X' => by funext i; cases i <;> simp [elimL])

lemma hasFDerivAt_elimR (X Y : Fin 9 → ℂ) :
    HasFDerivAt (fun Y : Fin 9 → ℂ => (Sum.elim X Y : Fin 9 ⊕ Fin 9 → ℂ)) elimR Y :=
  (elimR.hasFDerivAt.add_const (Sum.elim X (0 : Fin 9 → ℂ))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun Y' => by funext i; cases i <;> simp [elimR])

variable (A : A1Facts)

/-- **`∂_X law` is the formal `X`-partial of the law polynomial.** -/
theorem A1Facts.dXlaw_eq_pderiv {k m : Fin 9} {P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ}
    (hP : ∀ X Y, eval (Sum.elim X Y) P = A.lawK k m X Y) (X Y S : P9) :
    A.dXlaw k m X Y S = ∑ a, S a * eval (Sum.elim X Y) (pderiv (Sum.inl a) P) := by
  have h := (mvPoly_hasFDerivAt P (Sum.elim X Y)).comp X (hasFDerivAt_elimL X Y)
  have e : (fun X => A.lawK k m X Y) = (fun x => eval x P) ∘ fun X : Fin 9 → ℂ => (Sum.elim X Y : _ → ℂ) :=
    funext fun X => (hP X Y).symm
  unfold A1Facts.dXlaw
  rw [e, h.fderiv]
  simp [ContinuousLinearMap.sum_apply, Fintype.sum_sum_type, elimL, elimR]

/-- **`∂_Y law` is the formal `Y`-partial of the law polynomial.** -/
theorem A1Facts.dYlaw_eq_pderiv {k m : Fin 9} {P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ}
    (hP : ∀ X Y, eval (Sum.elim X Y) P = A.lawK k m X Y) (X Y S : P9) :
    A.dYlaw k m X Y S = ∑ a, S a * eval (Sum.elim X Y) (pderiv (Sum.inr a) P) := by
  have h := (mvPoly_hasFDerivAt P (Sum.elim X Y)).comp Y (hasFDerivAt_elimR X Y)
  have e : (fun Y => A.lawK k m X Y) = (fun x => eval x P) ∘ fun Y : Fin 9 → ℂ => (Sum.elim X Y : _ → ℂ) :=
    funext fun Y => (hP X Y).symm
  unfold A1Facts.dYlaw
  rw [e, h.fderiv]
  simp [ContinuousLinearMap.sum_apply, Fintype.sum_sum_type, elimL, elimR]

end LSG.JacAn
