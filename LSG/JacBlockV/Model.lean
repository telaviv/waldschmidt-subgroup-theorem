/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.ABlockInst
import LSG.JacBlockV.Period
import LSG.JacBlockV.Poly
import LSG.MEBV.Block

/-!
# M2.4b: the model of `A_σ̄^♮` in `ℙ¹¹` and the fibre lift (fields `fc` … `T_plk`, `lift_per`)

Coordinates `Idx = Fin 9 ⊕ Fin 3`: `X_c = inl c`, `T_t = inr t`, with `T_t` attached to `X_{fcV t}`,
`fcV = ![0, 4, 8]`. Throughout, `D : ThetaData G` is a `θ`-datum over `a1Facts` and the base is
`LSG.JacBlock.aBlockD D` (so `θ = D.thetaN`, `per = kerE G`, `W = Wmv`).

* `ΦV D z t = ⅓ ∂₀θ_{fc t}(z) − θ_{fc t}(z) ℓ(z)`, so that `fibOf θ fcV (ΦV D) z w t = D.fibT (fcV t) z w`
  (`fibOf_eq`); `ΦV_analytic`.
* **Plücker relations** (all charts, from the base field `JacBlock.theta_flow`, so chart 8 is included):
  `plucker`: `θ_c T_l − θ_l T_c = −⅓ W^{(c)}_{0l}(θ)` for `c ∈ {0, 4, 8}` and every `l : Fin 9`;
  `plkV t t' = −⅓ Wmv (fc t) 0 (fc t')` (`plkV_self : plkV t t = 0`), `T_plkV`.
* The fibre generators `gensTV = [plkGen 0 1, plkGen 0 2, plkGen 1 2]`,
  `plkGen t t' = X_{fc t} T_{t'} − X_{fc t'} T_t − plkV t t'` (these are `P₀₄, P₀₈, P₄₈` of M2.1.1), `liftT_modelV`.
* **Fibre flow** `T_flowV` with `WTV t j = ⅓ kQ (fc t) j 0` (`eval_WTV`), from `ThetaData.fibT_flow`.
* **Periods** `lift_perV` (`η = etaB`) on `kerE G`, from `ThetaData.fibT_add_isPer`.
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV

namespace LSG.JacBlockV

open LSG.JacBlock

/-- The coordinates of the model. -/
abbrev Idx := Fin 9 ⊕ Fin 3

/-- `T_t` is attached to `X_{fcV t}`. -/
def fcV : Fin 3 → Fin 9 := ![0, 4, 8]

@[simp] lemma fcV_0 : fcV 0 = 0 := rfl
@[simp] lemma fcV_1 : fcV 1 = 4 := rfl
@[simp] lemma fcV_2 : fcV 2 = 8 := rfl

lemma fcV_mem (t : Fin 3) : fcV t ∈ ({0, 4, 8} : Finset (Fin 9)) := by fin_cases t <;> simp

lemma fcV_cases (t : Fin 3) : fcV t = 0 ∨ fcV t = 4 ∨ fcV t = 8 := by fin_cases t <;> simp

lemma fc_charts : ∀ c ∈ ({0, 4, 8} : Finset (Fin 9)), ∃ t, fcV t = c := by
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- The Plücker quadrics `plk_{tt'} = −⅓ W^{(fc t)}_{0, fc t'}`. -/
def plkV (t t' : Fin 3) : MvPolynomial (Fin 9) ℂ := C (-(1 / 3 : ℂ)) * Wmv (fcV t) 0 (fcV t')

lemma plkV_self (t : Fin 3) : plkV t t = 0 := by simp [plkV, Wmv_chart]

lemma plkV_hom (t t' : Fin 3) : (plkV t t').IsHomogeneous 2 := by
  have := (isHomogeneous_C (Fin 9) (-(1 / 3 : ℂ))).mul (Wmv_hom (fcV t) 0 (fcV t'))
  rwa [zero_add] at this

/-- The fibre generator `X_{fc t} T_{t'} − X_{fc t'} T_t − plk_{tt'}(X)`. -/
def plkGen (t t' : Fin 3) : MvPolynomial Idx ℂ :=
  X (Sum.inl (fcV t)) * X (Sum.inr t') - X (Sum.inl (fcV t')) * X (Sum.inr t) - rename Sum.inl (plkV t t')

/-- The fibre generators `P₀₄, P₀₈, P₄₈`. -/
def gensTV : List (MvPolynomial Idx ℂ) := [plkGen 0 1, plkGen 0 2, plkGen 1 2]

lemma plkGen_hom (t t' : Fin 3) : (plkGen t t').IsHomogeneous 2 := by
  unfold plkGen
  refine IsHomogeneous.sub (IsHomogeneous.sub ?_ ?_) ((plkV_hom t t').rename_isHomogeneous)
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)

lemma gensTV_hom : ∀ Q ∈ gensTV, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d := by
  intro Q hQ
  simp only [gensTV, List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl | rfl <;> exact ⟨2, by norm_num, plkGen_hom _ _⟩

lemma eval_plkGen (Y : Idx → ℂ) (t t' : Fin 3) :
    eval Y (plkGen t t') = Y (Sum.inl (fcV t)) * Y (Sum.inr t') - Y (Sum.inl (fcV t')) * Y (Sum.inr t) -
      eval (fun c => Y (Sum.inl c)) (plkV t t') := by
  simp only [plkGen, map_sub, map_mul, eval_X, eval_rename]
  rfl

/-! ### The fibre flow quadrics `WT t j = ⅓ kQ (fc t) j 0` -/

/-- `⅓ Q_{fc t, j0}` as polynomials. -/
def WTV : Fin 3 → Fin 2 → MvPolynomial (Fin 9) ℂ := ![
  ![mon 1 [1, 0], mon 1 [2, 0]],
  ![mon (-3 / 4) [0, 2] + mon (-3 / 2) [1, 8] + mon (3 / 2) [3, 3] + mon (1 / 4) [4, 6],
    mon 1 [0, 3] + mon 1 [1, 1] + mon (-3 / 2) [2, 8] + mon (-1 / 4) [4, 7]],
  ![mon 3 [1, 1] + mon (3 / 2) [2, 8] + mon (3 / 4) [4, 7], mon 1 [1, 2] + mon (-1 / 2) [5, 7]]]

lemma eval_WTV (t : Fin 3) (j : Fin 2) (x : Fin 9 → ℂ) :
    eval x (WTV t j) = 1 / 3 * kQ (fcV t) j 0 x := by
  fin_cases t <;> fin_cases j <;> simp [WTV, kQ, mIdx, fcV] <;> ring

lemma WTV_hom (t : Fin 3) (j : Fin 2) : (WTV t j).IsHomogeneous 2 := by
  fin_cases t <;> fin_cases j <;> simp only [WTV, Matrix.cons_val, Fin.isValue, Fin.zero_eta,
    Fin.mk_one, Fin.reduceFinMk] <;>
    first | exact isHomogeneous_zero _ _ _ | apply_rules [IsHomogeneous.add, isHomogeneous_mon]

/-! ### The fibre lift -/

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

/-- `Φ(z)_t = ⅓ ∂₀θ_{fc t}(z) − θ_{fc t}(z) ℓ(z)`. -/
def ΦV (z : Fin 2 → ℂ) (t : Fin 3) : ℂ :=
  1 / 3 * pd 0 (cmpV D.thetaN (fcV t)) z - D.thetaN z (fcV t) * D.ellK z

lemma fibOf_eq (z : Fin 2 → ℂ) (w : ℂ) (t : Fin 3) :
    LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z w t = D.fibT (fcV t) z w := by
  unfold LSG.MEBV.fibOf ΦV ThetaData.fibT; ring

theorem ΦV_analytic (z : Fin 2 → ℂ) : AnalyticAt ℂ (ΦV D) z := by
  rw [analyticAt_pi_iff]
  intro t
  exact ((((ent_cmp D.analyticAt_thetaN (fcV t)).pd 0).const_mul (1 / 3)).sub
    ((ent_cmp D.analyticAt_thetaN (fcV t)).mul (ent_lin D.ellK))) z

/-- **The Plücker relations in every chart** (chart 8 through the base field `theta_flow`). -/
theorem plucker {c : Fin 9} (hc : c ∈ ({0, 4, 8} : Finset (Fin 9))) (l : Fin 9) (z : Fin 2 → ℂ) (w : ℂ) :
    D.thetaN z c * D.fibT l z w - D.thetaN z l * D.fibT c z w =
      -(1 / 3) * eval (D.thetaN z) (Wmv c 0 l) := by
  have h := theta_flow D c hc 0 l z
  have hd := (D.analyticAt_thetaN z).differentiableAt
  unfold ThetaData.fibT
  rw [pd_cmp hd, pd_cmp hd]
  linear_combination (-1 / 3 : ℂ) * h

theorem T_plkV (t t' : Fin 3) (z : Fin 2 → ℂ) (w : ℂ) :
    D.thetaN z (fcV t) * LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z w t' -
        D.thetaN z (fcV t') * LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z w t =
      eval (D.thetaN z) (plkV t t') := by
  rw [fibOf_eq, fibOf_eq, plucker D (fcV_mem t)]
  simp [plkV]

theorem liftT_modelV (q : (Fin 2 → ℂ) × ℂ) :
    ∀ Q ∈ gensTV, eval (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q) Q = 0 := by
  have key : ∀ t t', eval (LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q) (plkGen t t') = 0 := by
    intro t t'
    rw [eval_plkGen]
    simp only [LSG.MEBV.liftOf, Sum.elim_inl, Sum.elim_inr]
    rw [T_plkV]
    ring
  intro Q hQ
  simp only [gensTV, List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl | rfl <;> exact key _ _

/-- **The fibre flow** `θ_c ∂_jT_t − T_t ∂_jθ_c = ⅓ Q_{c,j0}(θ)`, `c = fc t`. -/
theorem T_flowV (t : Fin 3) (j : Fin 2) (z : Fin 2 → ℂ) (w : ℂ) :
    D.thetaN z (fcV t) * fderiv ℂ (fun z' => LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z' w t) z (Pi.single j 1) -
        LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z w t * fderiv ℂ D.thetaN z (Pi.single j 1) (fcV t) =
      eval (D.thetaN z) (WTV t j) := by
  have h := D.fibT_flow (fcV_cases t) j z w
  have e : (fun z' => LSG.MEBV.fibOf D.thetaN fcV (ΦV D) z' w t) = fun z' => D.fibT (fcV t) z' w :=
    funext fun z' => fibOf_eq D z' w t
  rw [e, fibOf_eq, eval_WTV, ← h, pd_cmp (D.analyticAt_thetaN z).differentiableAt]
  rfl

/-- **Translation by a period of `A^♮_σ̄`** rescales the lift (all `ω ∈ kerE G`). -/
theorem lift_perV (ω : Fin 2 → ℂ) (hω : ω ∈ kerE G) (q : (Fin 2 → ℂ) × ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ LSG.MEBV.liftOf D.thetaN fcV (ΦV D) (q + (ω, D.etaB ω)) =
      c • LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q := by
  have hP : IsPer G ω := isPer_of_mem_kerE hω
  refine ⟨D.facN ω q.1, D.facN_ne_zero_isPer hP q.1, funext fun i => ?_⟩
  rcases i with c | t
  · simp only [LSG.MEBV.liftOf, Sum.elim_inl, Prod.fst_add, Pi.smul_apply, smul_eq_mul, D.thetaN_add hP]
  · simp only [LSG.MEBV.liftOf, Sum.elim_inr, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul,
      fibOf_eq]
    exact D.fibT_add_isPer hP _ _ _

end LSG.JacBlockV
