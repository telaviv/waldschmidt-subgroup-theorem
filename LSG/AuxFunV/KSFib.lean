/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.FpolyV
import LSG.AuxFun.LemmaUFac
import LSG.AuxFunV.AlgV

/-!
# Lemma U for the class `𝒞`: sizes of the fibre factors

The fibre factor `fibFac` is an integer polynomial `FibP κ λ` (depending only on `m` and the
finitely many law choices) evaluated at
* constants: `cᵢ`, `M_ij`, `q_j = (2λ_j(X'_j))⁻¹`, `g₂`, `g₃`, the entries of `X'_j`;
* series: `vᵢ s`, `℘(z₀ + v_j s)`, `℘'(z₀ + v_j s)`, `Z_j(s)` (`fibVals`).

**`ks_fibFac`**: if all of these are `KS ι A B e δ`, the fibre factor is
`KS ι (CF · 2^NF · A^NF) (2B) (e^NF) δ` with `CF, NF` depending only on `m` (`KS.eval_mvpoly`).
**`differentiableAt_fibFac`**.
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair LSG.W88 LSG.W88.Vec MvPolynomial
open LSG.Aux (ellW ellV IsRep zh wpP wpQ xiV lawk lawk_map KS Sz ks_lin)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}

/-- The variables of the fibre polynomial: `(c, v s)` and ten per block. -/
abbrev VarF (m : ℕ) := Fin 2 ⊕ (Fin m × Fin 10)

/-- A variable of the fibre polynomial. -/
abbrev Xv (x : VarF m) : MvPolynomial (VarF m) ℤ := X x

/-- `N_{k,W}` as a polynomial. -/
def NWp (κ : Fin 2) (k : Fin m) : MvPolynomial (VarF m) ℤ :=
  lawk κ (Xv (.inr (k, 2))) (Xv (.inr (k, 3)))
    ![Xv (.inr (k, 4)), Xv (.inr (k, 5)), Xv (.inr (k, 6))]
    ![Xv (.inr (k, 7)), Xv (.inr (k, 8)), 1] 2

/-- `G_k` as a polynomial. -/
def GTp (κ lam : Fin 2) (k : Fin m) : MvPolynomial (VarF m) ℤ :=
  NLaw (Xv (.inr (k, 2))) (Xv (.inr (k, 3))) κ lam 1
    ![Xv (.inr (k, 4)), Xv (.inr (k, 5)), Xv (.inr (k, 6)), 0, 0]
    (ptAff (Xv (.inr (k, 7))) (Xv (.inr (k, 8))) (-Xv (.inr (k, 9)))) 3

/-- The fibre polynomial. -/
def FibP (κ lam : Fin m → Fin 2) : MvPolynomial (VarF m) ℤ :=
  (Xv (.inl 0) + Xv (.inl 1)) * ∏ k, NWp (κ k) k +
    ∑ j, Xv (.inr (j, 0)) * (Xv (.inr (j, 1)) * GTp (κ j) (lam j) j *
      ∏ l ∈ univ.erase j, NWp (κ l) l)

/-- The values of the variables along the line. -/
def fibVals (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (X' : Fin m → Fin 3 → ℂ)
    (cst : Fin r → ℂ) (v : TanV d0 d1 m r) (i : Fin r) : VarF m → ℂ → ℂ
  | .inl a => fun s => ![cst i, v.2.2.2 i * s] a
  | .inr ja => fun s => ![M i ja.1, (2 * mult (lamIdx (X' ja.1)) (X' ja.1))⁻¹, (Ls ja.1).g₂,
      (Ls ja.1).g₃, X' ja.1 0, X' ja.1 1, X' ja.1 2, wpP (Ls ja.1) (v.2.2.1 ja.1) s,
      wpQ (Ls ja.1) (v.2.2.1 ja.1) s, zS (Ls ja.1) (v.2.2.1 ja.1) s] ja.2

lemma aeval_NWp (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r) (i : Fin r) (κ : Fin 2)
    (k : Fin m) (s : ℂ) :
    aeval (fun x => fibVals Ls M X' cst v i x s) (NWp κ k) = NW (Ls k) κ (X' k) (v.2.2.1 k) s := by
  have h := lawk_map (aeval (fun x => fibVals Ls M X' cst v i x s)).toRingHom κ
    (Xv (.inr (k, 2))) (Xv (.inr (k, 3))) ![Xv (.inr (k, 4)), Xv (.inr (k, 5)), Xv (.inr (k, 6))]
    ![Xv (.inr (k, 7)), Xv (.inr (k, 8)), 1] 2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Xv, aeval_X] at h
  rw [NWp, h, NW]
  congr 1
  · funext a; fin_cases a <;> simp [fibVals]
  · funext a; fin_cases a <;> simp [fibVals, xiV]

lemma aeval_GTp (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r) (i : Fin r) (κ : Fin 2)
    (k : Fin m) (s : ℂ) :
    aeval (fun x => fibVals Ls M X' cst v i x s) (GTp κ (lamIdx (X' k)) k) =
      GT (Ls k) κ (X' k) (v.2.2.1 k) s := by
  have h := NLaw_map (aeval (fun x => fibVals Ls M X' cst v i x s)).toRingHom
    (Xv (.inr (k, 2))) (Xv (.inr (k, 3))) κ (lamIdx (X' k)) 1
    ![Xv (.inr (k, 4)), Xv (.inr (k, 5)), Xv (.inr (k, 6)), 0, 0]
    (ptAff (Xv (.inr (k, 7))) (Xv (.inr (k, 8))) (-Xv (.inr (k, 9)))) 3
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Xv, aeval_X] at h
  rw [GTp, h, GT]
  congr 1
  · funext a; fin_cases a <;> simp [fibVals, Phat]
  · funext a; fin_cases a <;> simp [fibVals, Qhat, ptAff]

/-- **The fibre factor is the fibre polynomial evaluated along the line.** -/
theorem aeval_FibP (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r)
    (i : Fin r) (s : ℂ) :
    aeval (fun x => fibVals Ls M X' cst v i x s) (FibP κ fun k => lamIdx (X' k)) =
      fibFac Ls M κ X' cst v i s := by
  simp only [FibP, map_add, map_mul, map_sum, map_prod, aeval_NWp, aeval_GTp, fibFac]
  simp only [Xv, aeval_X]
  simp [fibVals]

/-- The uniform constant `Σ |coefficients|` over all law choices. -/
def CF (m : ℕ) : ℝ :=
  ∑ κl : (Fin m → Fin 2) × (Fin m → Fin 2),
    ∑ e ∈ (FibP κl.1 κl.2).support, |((FibP κl.1 κl.2).coeff e : ℝ)|

/-- The uniform degree bound over all law choices. -/
def NF (m : ℕ) : ℕ :=
  ∑ κl : (Fin m → Fin 2) × (Fin m → Fin 2), (FibP κl.1 κl.2).totalDegree

lemma CF_nonneg (m : ℕ) : 0 ≤ CF m :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

attribute [local irreducible] FibP

/-- **Sizes of the fibre factor.** -/
theorem ks_fibFac (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r)
    (i : Fin r) {A B : ℝ} {e δ : ℕ} (hB : 0 ≤ B) (hA : 1 ≤ A)
    (hval : ∀ x, KS ι A B e δ (fibVals Ls M X' cst v i x)) :
    KS ι (CF m * (2 ^ NF m * A ^ NF m)) (2 * B) (e ^ NF m) δ (fibFac Ls M κ X' cst v i) := by
  classical
  have h := KS.eval_mvpoly (FibP κ fun k => lamIdx (X' k)) (fibVals Ls M X' cst v i) hB hA hval
  have hfun : (fun s => aeval (fun x => fibVals Ls M X' cst v i x s)
      (FibP κ fun k => lamIdx (X' k))) = fibFac Ls M κ X' cst v i :=
    funext fun s => aeval_FibP Ls M κ X' cst v i s
  rw [hfun] at h
  have hdeg : (FibP κ fun k => lamIdx (X' k)).totalDegree ≤ NF m := by
    have := single_le_sum (s := univ) (f := fun κl : (Fin m → Fin 2) × (Fin m → Fin 2) =>
      (FibP κl.1 κl.2).totalDegree) (fun _ _ => Nat.zero_le _)
      (mem_univ (κ, fun k => lamIdx (X' k)))
    exact this
  have hC : ∑ e ∈ (FibP κ fun k => lamIdx (X' k)).support,
      |((FibP κ fun k => lamIdx (X' k)).coeff e : ℝ)| ≤ CF m := by
    have := single_le_sum (s := univ) (f := fun κl : (Fin m → Fin 2) × (Fin m → Fin 2) =>
      ∑ e ∈ (FibP κl.1 κl.2).support, |((FibP κl.1 κl.2).coeff e : ℝ)|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ (κ, fun k => lamIdx (X' k)))
    exact this
  refine h.mono ?_ (by positivity) le_rfl (pow_dvd_pow e hdeg) dvd_rfl
  exact mul_le_mul hC (mul_le_mul (pow_le_pow_right₀ one_le_two hdeg) (pow_le_pow_right₀ hA hdeg)
    (by positivity) (by positivity)) (by positivity) (CF_nonneg m)

/-- The variables are `KS` from the sizes of the constants and of the three series. -/
theorem ks_fibVals (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r) (i : Fin r)
    {A B : ℝ} {e δ : ℕ} (hB : 1 ≤ B) (hA : 1 ≤ A)
    (hc : Sz ι A e (cst i)) (hv : Sz ι (A * B) e (v.2.2.2 i)) (hM : ∀ j, Sz ι A e (M i j))
    (hq : ∀ j, Sz ι A e (2 * mult (lamIdx (X' j)) (X' j))⁻¹)
    (hg₂ : ∀ j, Sz ι A e (Ls j).g₂) (hg₃ : ∀ j, Sz ι A e (Ls j).g₃)
    (hX : ∀ j a, Sz ι A e (X' j a))
    (hP : ∀ j, KS ι A B e δ (wpP (Ls j) (v.2.2.1 j)))
    (hQ : ∀ j, KS ι A B e δ (wpQ (Ls j) (v.2.2.1 j)))
    (hZ : ∀ j, KS ι A B e δ (zS (Ls j) (v.2.2.1 j))) :
    ∀ x, KS ι A B e δ (fibVals Ls M X' cst v i x) := by
  have hB0 : 0 ≤ B := by linarith
  have hconst : ∀ c : ℂ, Sz ι A e c → KS ι A B e δ (fun _ => c) := fun c h => KS.const h hB0
  intro x
  rcases x with a | ⟨j, a⟩
  · fin_cases a
    · exact hconst _ hc
    · have hid : (fun s : ℂ => v.2.2.2 i * s) = fun s => 0 + v.2.2.2 i * s :=
        funext fun s => by ring
      change KS ι A B e δ (fun s => v.2.2.2 i * s)
      rw [hid]
      exact ks_lin ((Sz.zero e).mono_le (by linarith)) hv hB0
  · fin_cases a
    · exact hconst _ (hM j)
    · exact hconst _ (hq j)
    · exact hconst _ (hg₂ j)
    · exact hconst _ (hg₃ j)
    · exact hconst _ (hX j 0)
    · exact hconst _ (hX j 1)
    · exact hconst _ (hX j 2)
    · exact hP j
    · exact hQ j
    · exact hZ j

/-- The fibre factor is differentiable where the base points avoid the lattices. -/
theorem differentiableAt_fibFac (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r)
    (i : Fin r) {s : ℂ} (hs : ∀ k, zh (Ls k) + v.2.2.1 k * s ∉ (Ls k).lattice) :
    DifferentiableAt ℂ (fibFac Ls M κ X' cst v i) s := by
  have hfun : fibFac Ls M κ X' cst v i =
      fun s => aeval (fun x => fibVals Ls M X' cst v i x s) (FibP κ fun k => lamIdx (X' k)) :=
    funext fun s => (aeval_FibP Ls M κ X' cst v i s).symm
  rw [hfun]
  refine differentiableAt_aeval _ _ fun x => ?_
  rcases x with a | ⟨j, a⟩
  · fin_cases a
    · exact differentiableAt_const _
    · exact (differentiableAt_const _).mul differentiableAt_id
  · fin_cases a
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_wpP (Ls j) _ (hs j)
    · exact differentiableAt_wpQ (Ls j) _ (hs j)
    · exact differentiableAt_zS (Ls j) _ (hs j)

end LSG.AuxV
