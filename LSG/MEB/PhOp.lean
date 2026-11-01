/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.PhOpLaw
import LSG.MEB.Ord

/-!
# Philippon's degree-stable operators, built analytically (A4.1a, β)

For `g ∈ G`, `w ∈ Lie G`, law choices `c, c'` and `κ ∈ ℕ`,
`phOp g w c c' κ Q = [t^κ] Q(law_c(X, phPt g w c' t))`, coefficientwise in `X`, where the moving point
`phPt g w c' t = law_{c'}(coords g 1, liftB (t w))` is `g + exp(t w)` on the cone (entire in `t`). No formal
exponential and no flow equation are used.

* `lawSubU c`: the substitution with the second argument as variables of the coefficient ring;
  `lawSub_eq_map`: `lawSub c Y = map (eval Y) ∘ lawSubU c`.
* `tcoef κ f = f⁽ᵏ⁾(0)/κ!`. **`coeff_phOp`**, **`eval_phOp`**:
  `eval x (phOp g w c c' κ Q) = tcoef κ (t ↦ Q(lawPt c x (phPt g w c' t)))`.
* **`phOp_mem_FLE`** (`Q ∈ FLE D ⇒ phOp … Q ∈ FLE (dblB D)`, every `κ`) and **`isHomB_phOp`**
  (`IsHomB Q d ⇒ IsHomB (phOp … Q) (2 • d)`): each coefficient of `phOp` is a Taylor coefficient of the
  corresponding coefficient of a translate `lawSub c Y Q`, which vanishes identically outside the allowed monomials.
* Analyticity: `analyticAt_liftB_comp`, `analyticAt_lawPt`, `analyticAt_phPt`.
-/

open MvPolynomial

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### The universal substitution -/

/-- The images of the variables, with the second argument of the laws as variables of the coefficient ring. -/
noncomputable def lawVarU (c : ∀ k, Fin (B k).nL) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) (MvPolynomial (Var d₀ d₁ B) ℂ)
  | .x i => X (.x i) + C (X (.x i))
  | .y j => C (X (.y j)) * X (.y j)
  | .z j => C (X (.z j)) * X (.z j)
  | .e k a => aeval (Sum.elim (fun b => X (Var.e k b)) (fun b => C (X (Var.e k b)))) ((B k).law (c k) a)

/-- The universal translate. -/
noncomputable def lawSubU (c : ∀ k, Fin (B k).nL) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  aeval (lawVarU c)

theorem map_eval_aeval {σ τ : Type*} (Y : τ → ℂ) (f : σ → MvPolynomial (Var d₀ d₁ B) (MvPolynomial τ ℂ))
    (L : MvPolynomial σ ℂ) :
    map (eval Y) (aeval f L) = aeval (fun s => map (eval Y) (f s)) L := by
  induction L using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, aeval_X]

theorem map_lawVarU (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    map (eval Y) (lawVarU c v) = lawVar c Y v := by
  cases v with
  | x i => simp [lawVarU, lawVar]
  | y j => simp [lawVarU, lawVar]
  | z j => simp [lawVarU, lawVar]
  | e k a =>
    simp only [lawVarU, lawVar, lawE, map_eval_aeval]
    rw [bind₁]
    refine congrArg (fun f => aeval f ((B k).law (c k) a)) (funext fun s => ?_)
    cases s <;> simp

theorem lawSub_eq_map (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ) :
    lawSub c Y Q = map (eval Y) (lawSubU c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [lawSub, lawSubU, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rw [lawSubU, aeval_X, map_lawVarU, lawSub, bind₁_X_right]

theorem coeff_lawSub (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ)
    (μ : Var d₀ d₁ B →₀ ℕ) : (lawSub c Y Q).coeff μ = eval Y ((lawSubU c Q).coeff μ) := by
  rw [lawSub_eq_map, MvPolynomial.coeff_map]

/-! ### Taylor coefficients -/

/-- The Taylor coefficient `[t^κ] f = f⁽ᵏ⁾(0)/κ!`. -/
noncomputable def tcoef (κ : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv κ f 0 / κ.factorial

@[simp] theorem tcoef_zero_fun (κ : ℕ) : tcoef κ (fun _ => (0 : ℂ)) = 0 := by
  simp [tcoef, iteratedDeriv_fun_const_zero]

theorem tcoef_sum_mul {ι : Type*} (s : Finset ι) (κ : ℕ) (f : ι → ℂ → ℂ) (a : ι → ℂ)
    (hf : ∀ i ∈ s, ContDiffAt ℂ κ (f i) 0) :
    tcoef κ (fun t => ∑ i ∈ s, f i t * a i) = ∑ i ∈ s, tcoef κ (f i) * a i := by
  simp only [tcoef]
  rw [iteratedDeriv_fun_sum (f := fun i t => f i t * a i)
    (fun i hi => (hf i hi).mul contDiffAt_const), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_mul_const_field]; ring

/-! ### Analyticity -/

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_liftB_comp {a : E → Tan d₀ d₁ B} {p : E} (ha : AnalyticAt ℂ a p) (v : Var d₀ d₁ B) :
    AnalyticAt ℂ (fun q => liftB (a q) v) p := by
  have h := (liftZ_analyticAt v (a p, 1)).comp (f := fun q => ((a q, 1) : LZ d₀ d₁ B))
    (ha.prod analyticAt_const)
  simpa [Function.comp_def, liftZ_one] using h

theorem analyticAt_lawPt (c : ∀ k, Fin (B k).nL) {x y : E → Var d₀ d₁ B → ℂ} {p : E}
    (hx : ∀ v, AnalyticAt ℂ (fun q => x q v) p) (hy : ∀ v, AnalyticAt ℂ (fun q => y q v) p)
    (v : Var d₀ d₁ B) : AnalyticAt ℂ (fun q => lawPt c (x q) (y q) v) p := by
  cases v with
  | x i => exact (hx _).add (hy _)
  | y j => exact (hy _).mul (hx _)
  | z j => exact (hy _).mul (hx _)
  | e k a =>
    simp only [lawPt, evalLaw]
    refine analyticAt_eval_of (f := fun s q => Sum.elim (fun b => x q (.e k b)) (fun b => y q (.e k b)) s)
      (fun s => ?_) _
    cases s with
    | inl b => exact hx _
    | inr b => exact hy _

end Analytic

/-! ### The operators -/

/-- The moving point `g + exp(t w)` on the cone, computed with the laws `c'`. -/
noncomputable def phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nL) (t : ℂ) :
    Var d₀ d₁ B → ℂ :=
  lawPt c' (coords g 1) (liftB (t • w))

theorem analyticAt_phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nL) (t₀ : ℂ)
    (v : Var d₀ d₁ B) : AnalyticAt ℂ (fun t => phPt g w c' t v) t₀ :=
  analyticAt_lawPt (x := fun _ => coords g 1) (y := fun t : ℂ => liftB (t • w)) c'
    (fun _ => analyticAt_const)
    (fun v => analyticAt_liftB_comp (a := fun t : ℂ => t • w) (analyticAt_id.smul analyticAt_const) v) v

theorem analyticAt_eval_phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nL)
    (a : MvPolynomial (Var d₀ d₁ B) ℂ) (t₀ : ℂ) : AnalyticAt ℂ (fun t => eval (phPt g w c' t) a) t₀ :=
  analyticAt_eval_of (f := fun v t => phPt g w c' t v) (fun v => analyticAt_phPt g w c' t₀ v) a

/-- **Philippon's operator** `δ^κ_g` along `w`: `[t^κ] Q(law_c(X, g + exp(t w)))`. -/
noncomputable def phOp (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c c' : ∀ k, Fin (B k).nL) (κ : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ B) ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ μ ∈ (lawSubU c Q).support,
    monomial μ (tcoef κ fun t => eval (phPt g w c' t) ((lawSubU c Q).coeff μ))

variable (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c c' : ∀ k, Fin (B k).nL) (κ : ℕ)

theorem coeff_phOp (Q : MvPolynomial (Var d₀ d₁ B) ℂ) (μ : Var d₀ d₁ B →₀ ℕ) :
    (phOp g w c c' κ Q).coeff μ = tcoef κ fun t => (lawSub c (phPt g w c' t) Q).coeff μ := by
  simp only [phOp, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, coeff_lawSub]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]
    simp

/-- **Evaluation of `phOp`**: the `κ`-th Taylor coefficient of `Q` along the moving translate. -/
theorem eval_phOp (x : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ) :
    eval x (phOp g w c c' κ Q) = tcoef κ fun t => eval (lawPt c x (phPt g w c' t)) Q := by
  have hrhs : (fun t => eval (lawPt c x (phPt g w c' t)) Q) = fun t =>
      ∑ μ ∈ (lawSubU c Q).support, eval (phPt g w c' t) ((lawSubU c Q).coeff μ) *
        ∏ v ∈ μ.support, x v ^ μ v := by
    funext t
    rw [← eval_lawSub, lawSub_eq_map, eval_map, eval₂_eq]
  rw [hrhs, tcoef_sum_mul _ _ _ _ fun μ _ =>
    (analyticAt_eval_phPt g w c' _ 0).contDiffAt]
  simp only [phOp, map_sum, eval_monomial, Finsupp.prod]

/-! ### Degrees -/

theorem phOp_mem_FLE {D : Blk m → ℕ} {Q : MvPolynomial (Var d₀ d₁ B) ℂ} (hQ : Q ∈ StrongSix.M2.FLE ℂ blk D) :
    phOp g w c c' κ Q ∈ StrongSix.M2.FLE ℂ blk (dblB D) := by
  intro μ hμ
  by_contra hS
  have hμ' : (phOp g w c c' κ Q).coeff μ ≠ 0 := mem_support_iff.mp hμ
  have h0 : ∀ t, (lawSub c (phPt g w c' t) Q).coeff μ = 0 := fun t =>
    notMem_support_iff.mp fun h => hS (lawSub_mem_FLE c _ hQ h)
  rw [coeff_phOp] at hμ'
  simp [h0] at hμ'

theorem isHomB_phOp {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsHomB Q d) :
    IsHomB (phOp g w c c' κ Q) (2 • d) := by
  intro k μ hμ
  by_contra hne
  have h0 : ∀ t, (lawSub c (phPt g w c' t) Q).coeff μ = 0 := fun t =>
    (isHomB_lawSub c _ hQ k).coeff_eq_zero μ hne
  rw [coeff_phOp] at hμ
  simp [h0] at hμ

end LSG.MEB
