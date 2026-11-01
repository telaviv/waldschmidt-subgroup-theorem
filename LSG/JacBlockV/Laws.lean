/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.Model
import LSG.JacAnV.Bridge

/-!
# M2.4b: the (3,3) addition laws of `A_σ̄^♮` by polarisation (fields `nLV`, `ld`, `lawV*`, M2.1.4)

The laws are **defined** from A1's law polynomials `lawP k m = spMv (Data.law k m)` by `pderiv` and `rename`, never
stored expanded. For `m : Fin 9` and fibre indices `s, s' : Fin 3` (charts `c = fc s`, `c' = fc s'`), with
`D^X_c L = Σ_a W^{(c)}_{0a}(X) ∂L/∂X_a` and `D^Y_{c'} L = Σ_a W^{(c')}_{0a}(Y) ∂L/∂Y_a` (`DXp`, `DYp`):

* `X_k`-part: `X_c Y_{c'} L_{k,m}(X, Y)`;
* `T_t`-part (`k = fc t`):
  `T_s Y_{c'} L_{k,m} + U_{s'} X_c L_{k,m} − (1/6)(Y_{c'} D^X_c L_{k,m} + X_c D^Y_{c'} L_{k,m})`.

This is `X_c Y_{c'} · lawT` (`LSG.JacAnV.Laws`) after the chart substitution `X_c S_a = X_a T_c − ⅓ W^{(c)}_{0a}(X)`
(the Plücker relations) and Euler. Correctness (`evalLawV_lawVI`) is semantic: `ThetaData.lawT_eq`, the
`pderiv` bridge `A1Facts.dXlaw_eq_pderiv`/`dYlaw_eq_pderiv`, `plucker`, and Euler `dXlaw_self`/`dYlaw_self`.

* `lawVV : Fin 81 → Idx → MvPolynomial (Idx ⊕ Idx) ℂ` (index `(m, s, s')` through `e81`);
* `lawVV_hom` (bidegree `(3, 3)`; `isWH_pderiv`), `lawVV_eq`, `lawVV_complete`.
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV

namespace LSG.JacBlockV

open LSG.JacBlock

/-- `Fin 9 ⊕ Fin 9 → Idx ⊕ Idx` (the `X`- and `Y`-variables of an `A`-law). -/
def ιL : Fin 9 ⊕ Fin 9 → Idx ⊕ Idx := Sum.map Sum.inl Sum.inl

/-- A1's law polynomial `L_{k,m}` (`k`-th coordinate of the law `m`). -/
def lawP (k m : Fin 9) : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ := spMv (Data.law k m)

/-- `D^X_c P = Σ_a W^{(c)}_{0a}(X) ∂P/∂X_a`. -/
def DXp (c : Fin 9) (P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ) : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ :=
  ∑ a : Fin 9, rename Sum.inl (Wmv c 0 a) * pderiv (Sum.inl a) P

/-- `D^Y_c P = Σ_a W^{(c)}_{0a}(Y) ∂P/∂Y_a`. -/
def DYp (c : Fin 9) (P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ) : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ :=
  ∑ a : Fin 9, rename Sum.inr (Wmv c 0 a) * pderiv (Sum.inr a) P

/-- **The law `(m, s, s')`** on `(X, T; Y, U)`. -/
def lawVI (m : Fin 9) (s s' : Fin 3) : Idx → MvPolynomial (Idx ⊕ Idx) ℂ :=
  Sum.elim
    (fun k => rename ιL (X (Sum.inl (fcV s)) * X (Sum.inr (fcV s')) * lawP k m))
    (fun t => X (Sum.inl (Sum.inr s)) * rename ιL (X (Sum.inr (fcV s')) * lawP (fcV t) m) +
      X (Sum.inr (Sum.inr s')) * rename ιL (X (Sum.inl (fcV s)) * lawP (fcV t) m) -
      C (1 / 6 : ℂ) * rename ιL (X (Sum.inr (fcV s')) * DXp (fcV s) (lawP (fcV t) m) +
        X (Sum.inl (fcV s)) * DYp (fcV s') (lawP (fcV t) m)))

/-- The 81 law indices `(m, s, s')`. -/
def e81 : Fin 9 × Fin 3 × Fin 3 ≃ Fin 81 :=
  (Equiv.prodCongr (Equiv.refl (Fin 9)) finProdFinEquiv).trans finProdFinEquiv

/-- **The 81 laws.** -/
def lawVV (i : Fin 81) : Idx → MvPolynomial (Idx ⊕ Idx) ℂ :=
  lawVI (e81.symm i).1 (e81.symm i).2.1 (e81.symm i).2.2

lemma lawVV_e81 (m : Fin 9) (s s' : Fin 3) : lawVV (e81 (m, s, s')) = lawVI m s s' := by
  simp [lawVV]

/-! ### Bidegree -/

lemma ιL_w (i : Fin 9 ⊕ Fin 9) : LSG.MEBV.biWV Idx (ιL i) = LSG.MEB.biW 9 i := by
  cases i <;> rfl

lemma lawP_hom (k m : Fin 9) : (lawP k m).IsWeightedHomogeneous (LSG.MEB.biW 9) (2, 2) :=
  spMv_isWeightedHomogeneous _ (law_deg k m)

lemma DXp_hom (c k m : Fin 9) : (DXp c (lawP k m)).IsWeightedHomogeneous (LSG.MEB.biW 9) (3, 2) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => isWH_of_eq ?_ (by decide : 2 • ((1, 0) : ℕ × ℕ) + (1, 2) = (3, 2))
  exact (isWH_rename_hom (w' := LSG.MEB.biW 9) (u := ((1, 0) : ℕ × ℕ)) (fun _ => rfl) (Wmv_hom c 0 a)).mul
    (isWH_pderiv (d' := ((1, 2) : ℕ × ℕ)) (lawP_hom k m) (Sum.inl a) rfl)

lemma DYp_hom (c k m : Fin 9) : (DYp c (lawP k m)).IsWeightedHomogeneous (LSG.MEB.biW 9) (2, 3) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => isWH_of_eq ?_ (by decide : 2 • ((0, 1) : ℕ × ℕ) + (2, 1) = (2, 3))
  exact (isWH_rename_hom (w' := LSG.MEB.biW 9) (u := ((0, 1) : ℕ × ℕ)) (fun _ => rfl) (Wmv_hom c 0 a)).mul
    (isWH_pderiv (d' := ((2, 1) : ℕ × ℕ)) (lawP_hom k m) (Sum.inr a) rfl)

/-- **The laws have bidegree `(3, 3)`.** -/
theorem lawVI_hom (m : Fin 9) (s s' : Fin 3) (k : Idx) :
    (lawVI m s s' k).IsWeightedHomogeneous (LSG.MEBV.biWV Idx) (3, 3) := by
  have hX : ∀ i, (X i : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ).IsWeightedHomogeneous (LSG.MEB.biW 9) (LSG.MEB.biW 9 i) :=
    fun i => isWeightedHomogeneous_X ℂ _ i
  have hXV : ∀ i, (X i : MvPolynomial (Idx ⊕ Idx) ℂ).IsWeightedHomogeneous (LSG.MEBV.biWV Idx)
      (LSG.MEBV.biWV Idx i) := fun i => isWeightedHomogeneous_X ℂ _ i
  rcases k with k | t
  · exact isWH_rename ιL_w (isWH_of_eq (((hX _).mul (hX _)).mul (lawP_hom k m)) rfl)
  · refine isWH_sub (IsWeightedHomogeneous.add ?_ ?_) ?_
    · exact isWH_of_eq ((hXV _).mul (isWH_rename ιL_w ((hX _).mul (lawP_hom (fcV t) m)))) rfl
    · exact isWH_of_eq ((hXV _).mul (isWH_rename ιL_w ((hX _).mul (lawP_hom (fcV t) m)))) rfl
    · refine isWH_of_eq ((isWeightedHomogeneous_C _ _).mul (isWH_rename ιL_w (IsWeightedHomogeneous.add
        (isWH_of_eq ((hX _).mul (DXp_hom _ _ _)) rfl) (isWH_of_eq ((hX _).mul (DYp_hom _ _ _)) rfl)))) rfl

theorem lawVV_hom (i : Fin 81) (k : Idx) :
    (lawVV i k).IsWeightedHomogeneous (LSG.MEBV.biWV Idx) (3, 3) := lawVI_hom _ _ _ k

/-! ### Evaluation -/

lemma eval_ιL (Y Z : Idx → ℂ) (P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ) :
    eval (Sum.elim Y Z) (rename ιL P) = eval (Sum.elim (fun c => Y (Sum.inl c)) (fun c => Z (Sum.inl c))) P := by
  have e : (Sum.elim Y Z ∘ ιL) = Sum.elim (fun c => Y (Sum.inl c)) (fun c => Z (Sum.inl c)) := by
    funext i
    cases i <;> rfl
  rw [eval_rename, e]

lemma eval_lawP (k m : Fin 9) (x y : Fin 9 → ℂ) : eval (Sum.elim x y) (lawP k m) = a1Facts.lawK k m x y :=
  congrFun (evalLaw_law m x y) k

lemma eval_DXp (c : Fin 9) (P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ) (x y : Fin 9 → ℂ) :
    eval (Sum.elim x y) (DXp c P) = ∑ a, eval x (Wmv c 0 a) * eval (Sum.elim x y) (pderiv (Sum.inl a) P) := by
  simp [DXp, map_sum, eval_rename, Sum.elim_comp_inl]

lemma eval_DYp (c : Fin 9) (P : MvPolynomial (Fin 9 ⊕ Fin 9) ℂ) (x y : Fin 9 → ℂ) :
    eval (Sum.elim x y) (DYp c P) = ∑ a, eval y (Wmv c 0 a) * eval (Sum.elim x y) (pderiv (Sum.inr a) P) := by
  simp [DYp, map_sum, eval_rename, Sum.elim_comp_inr]

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

/-- The chart substitution inside a derivative sum: `θ_c Σ_a T_a e_a = T_c Σ_a θ_a e_a − ⅓ Σ_a W_{0a}(θ) e_a`. -/
lemma plucker_sum {c : Fin 9} (hc : c ∈ ({0, 4, 8} : Finset (Fin 9))) (z : Fin 2 → ℂ) (w : ℂ) (e : Fin 9 → ℂ) :
    D.thetaN z c * ∑ a, D.fibT a z w * e a =
      D.fibT c z w * ∑ a, D.thetaN z a * e a - 1 / 3 * ∑ a, eval (D.thetaN z) (Wmv c 0 a) * e a := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := plucker D hc a z w
  linear_combination e a * h

/-- **Correctness of the law `(m, s, s')` on the image.** -/
theorem evalLawV_lawVI {κ : ℂ} (hκ : ∀ (u v : Fin 2 → ℂ) (k m : Fin 9),
    a1Facts.lawK k m (D.thetaN u) (D.thetaN v) = κ * D.thetaN (u + v) k * D.thetaN (u - v) m)
    (m : Fin 9) (s s' : Fin 3) (q q' : (Fin 2 → ℂ) × ℂ) :
    LSG.MEBV.evalLawV (lawVI m s s') (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q)
        (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q') =
      (D.thetaN q.1 (fcV s) * D.thetaN q'.1 (fcV s') * (κ * D.thetaN (q.1 - q'.1) m)) •
        LSG.MEBV.liftOf D.thetaN fcV (ΦV D) (q + q') := by
  obtain ⟨u, w⟩ := q
  obtain ⟨v, w'⟩ := q'
  funext i
  rcases i with k | t
  · simp only [LSG.MEBV.evalLawV, lawVI, Sum.elim_inl, Sum.elim_inr, eval_ιL, map_mul, eval_X, LSG.MEBV.liftOf,
      eval_lawP, hκ, Pi.smul_apply, smul_eq_mul, Prod.fst_add]
    ring
  · set c := fcV s
    set c' := fcV s'
    set k := fcV t
    set U := D.thetaN u
    set V := D.thetaN v
    set EX : Fin 9 → ℂ := fun a => eval (Sum.elim U V) (pderiv (Sum.inl a) (lawP k m)) with hEXd
    set EY : Fin 9 → ℂ := fun a => eval (Sum.elim U V) (pderiv (Sum.inr a) (lawP k m)) with hEYd
    have hlawT := D.lawT_eq hκ k m u v w w'
    unfold A1Facts.lawT at hlawT
    rw [a1Facts.dXlaw_eq_pderiv (fun X Y => eval_lawP k m X Y),
      a1Facts.dYlaw_eq_pderiv (fun X Y => eval_lawP k m X Y)] at hlawT
    have hEX : ∑ a, U a * EX a = 2 * a1Facts.lawK k m U V := by
      rw [← a1Facts.dXlaw_self, a1Facts.dXlaw_eq_pderiv (fun X Y => eval_lawP k m X Y)]
    have hEY : ∑ a, V a * EY a = 2 * a1Facts.lawK k m U V := by
      rw [← a1Facts.dYlaw_self, a1Facts.dYlaw_eq_pderiv (fun X Y => eval_lawP k m X Y)]
    have hSX := plucker_sum D (fcV_mem s) u w EX
    have hSY := plucker_sum D (fcV_mem s') v w' EY
    simp only [ThetaData.fibV] at hlawT
    simp only [LSG.MEBV.evalLawV, lawVI, Sum.elim_inr, eval_ιL, map_add, map_sub, map_mul, eval_X, eval_C,
      LSG.MEBV.liftOf, Sum.elim_inl, eval_lawP, eval_DXp, eval_DYp, Pi.smul_apply, smul_eq_mul, Prod.fst_add,
      Prod.snd_add, fibOf_eq]
    linear_combination (U c * V c') * hlawT + (-1 / 2 * V c') * hSX + (-1 / 2 * U c) * hSY +
      (-1 / 2 * V c' * D.fibT c u w) * hEX + (-1 / 2 * U c * D.fibT c' v w') * hEY

theorem lawVV_eq (i : Fin 81) (q q' : (Fin 2 → ℂ) × ℂ) : ∃ κ' : ℂ,
    LSG.MEBV.evalLawV (lawVV i) (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q)
        (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q') = κ' • LSG.MEBV.liftOf D.thetaN fcV (ΦV D) (q + q') := by
  obtain ⟨κ, -, hκ⟩ := D.laws_eq
  exact ⟨_, evalLawV_lawVI D hκ _ _ _ q q'⟩

theorem lawVV_complete (q q' : (Fin 2 → ℂ) × ℂ) : ∃ i,
    LSG.MEBV.evalLawV (lawVV i) (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q)
        (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q') ≠ 0 := by
  obtain ⟨κ, hκ0, hκ⟩ := D.laws_eq
  obtain ⟨c, hc, hcu⟩ := (aBlockD D).chart_cover (D.thetaN q.1) ((aBlockD D).θ_ne q.1) ((aBlockD D).θ_model q.1)
  obtain ⟨c', hc', hcv⟩ := (aBlockD D).chart_cover (D.thetaN q'.1) ((aBlockD D).θ_ne q'.1)
    ((aBlockD D).θ_model q'.1)
  obtain ⟨s, rfl⟩ := fc_charts c hc
  obtain ⟨s', rfl⟩ := fc_charts c' hc'
  set m := nzIdx (D.thetaN (q.1 - q'.1))
  have hm : D.thetaN (q.1 - q'.1) m ≠ 0 := nzIdx_spec (D.thetaN_ne_zero _)
  refine ⟨e81 (m, s, s'), ?_⟩
  rw [lawVV_e81, evalLawV_lawVI D hκ]
  refine smul_ne_zero (mul_ne_zero (mul_ne_zero hcu hcv) (mul_ne_zero hκ0 hm)) fun h0 => ?_
  exact D.thetaN_ne_zero (q + q').1 (funext fun k => by simpa [LSG.MEBV.liftOf] using congrFun h0 (Sum.inl k))

end LSG.JacBlockV
