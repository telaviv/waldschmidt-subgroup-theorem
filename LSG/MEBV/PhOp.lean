/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.PhOpLaw
import LSG.MEBV.Ord
import LSG.MEB.PhOp

/-!
# Philippon's degree-stable operators, built analytically (M2.5, β)

The `VBlock` analogue of `LSG.MEB.PhOp`. For `g ∈ G̃`, `w ∈ Lie G̃`, law choices `c, c'` and `κ ∈ ℕ`,
`phOp g w c c' κ Q = [t^κ] Q(law_c(X, phPt g w c' t))`, coefficientwise in `X`, where the moving point
`phPt g w c' t = law_{c'}(coords g 1, liftV (t w))` is `g + exp(t w)` on the cone (entire in `t`).

* `lawSubU c`: the substitution with the second argument as variables of the coefficient ring;
  `lawSub_eq_map`: `lawSub c Y = map (eval Y) ∘ lawSubU c`.
* `tcoef κ f = f⁽ᵏ⁾(0)/κ!` (MEB's). **`coeff_phOp`**, **`eval_phOp`**.
* **`phOp_mem_FLE`** (`Q ∈ FLE D ⇒ phOp … Q ∈ FLE (dblB B D)`, every `κ`) and **`isHomV_phOp`**
  (`IsHomV Q d ⇒ IsHomV (phOp … Q) (ldMul B d)`).
* Analyticity: `analyticAt_liftV_comp`, `analyticAt_lawPt`, `analyticAt_phPt`.
* `VBlock.lawV_eq'`, `VBlock.lawV_complete'`: the law fields restated with `VBlock.lift`.
-/

open MvPolynomial

namespace LSG.MEBV

open LSG.MEB (Blk tcoef tcoef_sum_mul)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

theorem VBlock.lawV_eq' (b : VBlock) (i : Fin b.nLV) (p q : (Fin b.g → ℂ) × ℂ) :
    ∃ κ : ℂ, evalLawV (b.lawV i) (b.lift p) (b.lift q) = κ • b.lift (p + q) :=
  b.lawV_eq i p q

theorem VBlock.lawV_complete' (b : VBlock) (p q : (Fin b.g → ℂ) × ℂ) :
    ∃ i, evalLawV (b.lawV i) (b.lift p) (b.lift q) ≠ 0 :=
  b.lawV_complete p q

/-! ### The universal substitution -/

/-- The images of the variables, with the second argument of the laws as variables of the coefficient ring. -/
noncomputable def lawVarU (c : ∀ k, Fin (B k).nLV) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) (MvPolynomial (Var d₀ d₁ B) ℂ)
  | .x i => X (.x i) + C (X (.x i))
  | .y j => C (X (.y j)) * X (.y j)
  | .z j => C (X (.z j)) * X (.z j)
  | .e k a => aeval (Sum.elim (fun b => X (Var.e k b)) (fun b => C (X (Var.e k b)))) ((B k).lawV (c k) a)

/-- The universal translate. -/
noncomputable def lawSubU (c : ∀ k, Fin (B k).nLV) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  aeval (lawVarU c)

theorem map_eval_aeval {σ τ : Type*} (Y : τ → ℂ) (f : σ → MvPolynomial (Var d₀ d₁ B) (MvPolynomial τ ℂ))
    (L : MvPolynomial σ ℂ) :
    map (eval Y) (aeval f L) = aeval (fun s => map (eval Y) (f s)) L := by
  induction L using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, aeval_X]

theorem map_lawVarU (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    map (eval Y) (lawVarU c v) = lawVar c Y v := by
  cases v with
  | x i => simp [lawVarU, lawVar]
  | y j => simp [lawVarU, lawVar]
  | z j => simp [lawVarU, lawVar]
  | e k a =>
    simp only [lawVarU, lawVar, lawE, map_eval_aeval]
    rw [bind₁]
    refine congrArg (fun f => aeval f ((B k).lawV (c k) a)) (funext fun s => ?_)
    cases s <;> simp

theorem lawSub_eq_map (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ) :
    lawSub c Y Q = map (eval Y) (lawSubU c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [lawSub, lawSubU, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rw [lawSubU, aeval_X, map_lawVarU, lawSub, bind₁_X_right]

theorem coeff_lawSub (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ)
    (μ : Var d₀ d₁ B →₀ ℕ) : (lawSub c Y Q).coeff μ = eval Y ((lawSubU c Q).coeff μ) := by
  rw [lawSub_eq_map, MvPolynomial.coeff_map]

/-! ### Analyticity -/

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_liftV_comp {a : E → Tan d₀ d₁ B} {p : E} (ha : AnalyticAt ℂ a p) (v : Var d₀ d₁ B) :
    AnalyticAt ℂ (fun q => liftV (a q) v) p := by
  have h := (liftZ_analyticAt v (a p, 1)).comp (f := fun q => ((a q, 1) : LZ d₀ d₁ B))
    (ha.prod analyticAt_const)
  simpa [Function.comp_def, liftZ_one] using h

theorem analyticAt_lawPt (c : ∀ k, Fin (B k).nLV) {x y : E → Var d₀ d₁ B → ℂ} {p : E}
    (hx : ∀ v, AnalyticAt ℂ (fun q => x q v) p) (hy : ∀ v, AnalyticAt ℂ (fun q => y q v) p)
    (v : Var d₀ d₁ B) : AnalyticAt ℂ (fun q => lawPt c (x q) (y q) v) p := by
  cases v with
  | x i => exact (hx _).add (hy _)
  | y j => exact (hy _).mul (hx _)
  | z j => exact (hy _).mul (hx _)
  | e k a =>
    simp only [lawPt, evalLawV]
    refine LSG.MEB.analyticAt_eval_of
      (f := fun s q => Sum.elim (fun b => x q (.e k b)) (fun b => y q (.e k b)) s) (fun s => ?_) _
    cases s with
    | inl b => exact hx _
    | inr b => exact hy _

end Analytic

/-! ### The operators -/

/-- The moving point `g + exp(t w)` on the cone, computed with the laws `c'`. -/
noncomputable def phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nLV) (t : ℂ) :
    Var d₀ d₁ B → ℂ :=
  lawPt c' (coords g 1) (liftV (t • w))

theorem analyticAt_phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nLV) (t₀ : ℂ)
    (v : Var d₀ d₁ B) : AnalyticAt ℂ (fun t => phPt g w c' t v) t₀ :=
  analyticAt_lawPt (x := fun _ => coords g 1) (y := fun t : ℂ => liftV (t • w)) c'
    (fun _ => analyticAt_const)
    (fun v => analyticAt_liftV_comp (a := fun t : ℂ => t • w) (analyticAt_id.smul analyticAt_const) v) v

theorem analyticAt_eval_phPt (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c' : ∀ k, Fin (B k).nLV)
    (a : MvPolynomial (Var d₀ d₁ B) ℂ) (t₀ : ℂ) : AnalyticAt ℂ (fun t => eval (phPt g w c' t) a) t₀ :=
  LSG.MEB.analyticAt_eval_of (f := fun v t => phPt g w c' t v) (fun v => analyticAt_phPt g w c' t₀ v) a

/-- **Philippon's operator** `δ^κ_g` along `w`: `[t^κ] Q(law_c(X, g + exp(t w)))`. -/
noncomputable def phOp (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c c' : ∀ k, Fin (B k).nLV) (κ : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ B) ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ μ ∈ (lawSubU c Q).support,
    monomial μ (tcoef κ fun t => eval (phPt g w c' t) ((lawSubU c Q).coeff μ))

variable (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c c' : ∀ k, Fin (B k).nLV) (κ : ℕ)

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

theorem phOp_mem_FLE {D : Blk m → ℕ} {Q : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hQ : Q ∈ StrongSix.M2.FLE ℂ blk D) : phOp g w c c' κ Q ∈ StrongSix.M2.FLE ℂ blk (dblB B D) := by
  intro μ hμ
  by_contra hS
  have hμ' : (phOp g w c c' κ Q).coeff μ ≠ 0 := mem_support_iff.mp hμ
  have h0 : ∀ t, (lawSub c (phPt g w c' t) Q).coeff μ = 0 := fun t =>
    notMem_support_iff.mp fun h => hS (lawSub_mem_FLE c _ hQ h)
  rw [coeff_phOp] at hμ'
  simp [h0] at hμ'

theorem isHomV_phOp {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d) :
    IsHomV (phOp g w c c' κ Q) (ldMul B d) := by
  intro k μ hμ
  by_contra hne
  have h0 : ∀ t, (lawSub c (phPt g w c' t) Q).coeff μ = 0 := fun t =>
    (isHomV_lawSub c _ hQ k).coeff_eq_zero μ hne
  rw [coeff_phOp] at hμ
  simp [h0] at hμ

end LSG.MEBV
