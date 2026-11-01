/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.PhOp

/-!
# Philippon's operators and the order of vanishing (M2.5, β)

The `VBlock` analogue of `LSG.MEB.PhOpTwo`: the inputs of Roy's vanishing claim for α's chain. All statements are
for multihomogeneous `P` and the frozen `OrdGtV`.

* `evalLawV_smul`: the laws of `b` have bidegree `(ld, ld)`; **`lawPt_liftZ`**: the law of two lifted points is a
  scaled lift of the sum (`lawV_eq`). Comparison lemmas `isBigO_eval_liftZ_rel` (any law) and
  `isBigO_liftV_of_rel` (good law, nonzero blocks at the base point).
* **`phOp_mem_vanish`**: order `> n` at `h₀ + g` makes `phOp g w c c' κ P` vanish at `h₀` for `κ ≤ n` (every `c, c'`).
* **`ordGtV_of_phOp_mem_vanish`**: conversely (good law choices from `lawV_complete`).
* **`ordGtV_phOp`** (the two-parameter lemma): order `> N` at `y + σ` and `κ + T ≤ N` give order `> T` of
  `phOp σ w' c c' κ P` at `y`.
* **`ordGtV_lawSub`** (translation invariance, every law choice).
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEBV

open LSG.MEB (tcoef)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Laws on lifted points -/

/-- The laws are bihomogeneous of bidegree `(ld, ld)`. -/
theorem evalLawV_smul (b : VBlock) (i : Fin b.nLV) (s r : ℂ) (X Y : b.Idx → ℂ) :
    evalLawV (b.lawV i) (s • X) (r • Y) = (s ^ b.ld * r ^ b.ld) • evalLawV (b.lawV i) X Y := by
  funext a
  let F : ℕ × ℕ →+ (Fin 2 → ℕ) :=
    { toFun := fun pq => ![pq.1, pq.2]
      map_zero' := by funext j; fin_cases j <;> rfl
      map_add' := fun p q => by funext j; fin_cases j <;> rfl }
  have hL := LSG.MEB.isWH_map_weight (b.lawV_hom i a) F
  have h := LSG.MEB.eval_scale (fun v => F (biWV b.Idx v)) ![s, r] (Sum.elim X Y) hL
  have e1 : (fun v => (∏ j, (![s, r] : Fin 2 → ℂ) j ^ F (biWV b.Idx v) j) * Sum.elim X Y v) =
      Sum.elim (s • X) (r • Y) := by
    funext v
    cases v <;> simp [F, biWV, Fin.prod_univ_two]
  rw [e1] at h
  simp only [evalLawV, Pi.smul_apply, smul_eq_mul, h]
  simp [F, Fin.prod_univ_two]

/-- **The law of two lifted points** is a scaled lift of the sum. -/
theorem lawPt_liftZ (c : ∀ k, Fin (B k).nLV) (a b : Tan d₀ d₁ B) (μ ν : Fin m → ℂ) :
    ∃ κ : Fin m → ℂ, lawPt c (liftZ a μ) (liftZ b ν) = liftZ (a + b) κ := by
  choose κ hκ using fun k => (B k).lawV_eq' (c k) (a.blkV k) (b.blkV k)
  refine ⟨fun k => μ k ^ (B k).ld * ν k ^ (B k).ld * κ k, ?_⟩
  funext v
  cases v with
  | x i => simp [lawPt, liftZ]
  | y j => simp [lawPt, liftZ, Complex.exp_add, mul_comm]
  | z j => simp [lawPt, liftZ, Complex.exp_add, mul_comm]
  | e k a' =>
    have h1 : (fun b' => liftZ a μ (.e k b')) = μ k • (B k).lift (a.blkV k) := by
      funext b'; simp [liftZ]
    have h2 : (fun b' => liftZ b ν (.e k b')) = ν k • (B k).lift (b.blkV k) := by
      funext b'; simp [liftZ]
    simp only [lawPt]
    rw [h1, h2, evalLawV_smul, hκ k]
    simp [liftZ, mul_assoc]

/-! ### Comparison lemmas -/

theorem continuousAt_blkPt_of_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → Var d₀ d₁ B → ℂ} {x : E} (h : ∀ v, AnalyticAt ℂ (fun q => F q v) x) (k : Fin m) :
    ContinuousAt (fun q => blkPt (F q) k) x :=
  continuousAt_pi.mpr fun b => (h (.e k b)).continuousAt

/-- **Any law**: if `F x' = liftZ (a x') κ(x')` for some scalars, then `P ∘ F = O(P ∘ liftV ∘ a)`. -/
theorem isBigO_eval_liftZ_rel {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E} {F : E → Var d₀ d₁ B → ℂ}
    {a : E → Tan d₀ d₁ B} (ha : Continuous a) (hF : ∀ v, AnalyticAt ℂ (fun q => F q v) x)
    (hrel : ∀ q, ∃ κ : Fin m → ℂ, F q = liftZ (a q) κ) :
    (fun q => eval (F q) P) =O[𝓝 x] fun q => eval (liftV (a q)) P := by
  simp_rw [← liftZ_one]
  refine isBigO_eval_blockwise hP F (fun q => liftZ (a q) 1) (continuousAt_blkPt_of_analytic hF)
    (fun k => (continuous_blkPt_liftZ ha 1 k).continuousAt) (fun k => blkPt_liftZ_one_ne _ k)
    (Eventually.of_forall fun q => ?_)
  obtain ⟨κ, hκ⟩ := hrel q
  exact ⟨κ, by rw [hκ, ← liftZ_mul_eq, one_mul]⟩

/-- **Good law**: if moreover the blocks of `F x` are nonzero, then `P ∘ liftV ∘ a = O(P ∘ F)`. -/
theorem isBigO_liftV_of_rel {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E} {F : E → Var d₀ d₁ B → ℂ}
    {a : E → Tan d₀ d₁ B} (ha : Continuous a) (hF : ∀ v, AnalyticAt ℂ (fun q => F q v) x)
    (hF0 : ∀ k, blkPt (F x) k ≠ 0) (hrel : ∀ q, ∃ κ : Fin m → ℂ, F q = liftZ (a q) κ) :
    (fun q => eval (liftV (a q)) P) =O[𝓝 x] fun q => eval (F q) P := by
  simp_rw [← liftZ_one]
  have hne : ∀ᶠ q in 𝓝 x, ∀ k, blkPt (F q) k ≠ 0 :=
    eventually_all.mpr fun k => (continuousAt_blkPt_of_analytic hF k).eventually_ne (hF0 k)
  refine isBigO_eval_blockwise hP (fun q => liftZ (a q) 1) F
    (fun k => (continuous_blkPt_liftZ ha 1 k).continuousAt) (continuousAt_blkPt_of_analytic hF) hF0
    (hne.mono fun q hq => ?_)
  obtain ⟨κ, hκ⟩ := hrel q
  have hκ0 : ∀ k, κ k ≠ 0 := fun k h0 => hq k (by rw [hκ, blkPt_liftZ, h0, zero_smul])
  refine ⟨κ⁻¹, ?_⟩
  rw [hκ, ← liftZ_mul_eq]
  congr 1
  funext k
  simp [hκ0 k]

/-! ### The zeros of the operator family -/

/-- **Philippon, Prop. 4.4, first half**: order `> n` along `W` at `h₀ + g` makes the operators of order `≤ n`
vanish at `h₀`, for every law choice. -/
theorem phOp_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ} {h₀ g : GPt d₀ d₁ B} (h : OrdGtV W P n (h₀ + g))
    {w : Tan d₀ d₁ B} (hw : w ∈ W) {κ : ℕ} (hκ : κ ≤ n) (c c' : ∀ k, Fin (B k).nLV) :
    phOp g w c c' κ P ∈ vanish {h₀} := by
  refine mem_vanish.mpr fun h' hh' lam => ?_
  rw [Set.mem_singleton_iff] at hh'
  subst hh'
  set ĥ := liftG h' with hĥ
  set ĝ := liftG g with hĝ
  obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ ĥ lam
  rw [expG_liftG] at hμ
  have hO : OrdAt W P n (ĥ + ĝ) := (ordGtV_iff hP).mp h _ (by simp [ĥ, ĝ, expG_liftG])
  rw [eval_phOp, tcoef, div_eq_zero_iff]
  left
  have hφa : ∀ t₀, ∀ v, AnalyticAt ℂ (fun t => lawPt c (coords h' lam) (phPt g w c' t) v) t₀ :=
    fun t₀ => analyticAt_lawPt c (fun _ => analyticAt_const) (analyticAt_phPt g w c' t₀)
  refine LSG.MEB.iteratedDeriv_eq_zero_of_isBigO (n := n + 1)
    (LSG.MEB.analyticAt_eval_of (f := fun v t => lawPt c (coords h' lam) (phPt g w c' t) v) (hφa 0) P)
    ?_ κ (Nat.lt_succ_of_le hκ)
  refine IsBigO.trans ?_ ((ordAt_iff_one hP).mp hO w hw)
  rw [lineF_one]
  refine isBigO_eval_liftZ_rel hP (a := fun t : ℂ => ĥ + ĝ + t • w) (by fun_prop) (hφa 0) fun t => ?_
  obtain ⟨κ₁, h1⟩ := lawPt_liftZ c' ĝ (t • w) 1 1
  obtain ⟨κ₂, h2⟩ := lawPt_liftZ c ĥ (ĝ + t • w) μ κ₁
  refine ⟨κ₂, ?_⟩
  simp only [phPt, coords_one_eq_liftV, ← hĝ, ← liftZ_one, h1, hμ, h2]
  rw [add_assoc]

/-- **Philippon, Prop. 4.4, second half**: if all operators of order `≤ n` along `W` (all law choices) vanish at
`h₀`, then `P` has order `> n` along `W` at `h₀ + g`. -/
theorem ordGtV_of_phOp_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ} {h₀ g : GPt d₀ d₁ B}
    (h : ∀ w ∈ W, ∀ κ ≤ n, ∀ c c' : ∀ k, Fin (B k).nLV, phOp g w c c' κ P ∈ vanish {h₀}) :
    OrdGtV W P n (h₀ + g) := by
  set ĥ := liftG h₀ with hĥ
  set ĝ := liftG g with hĝ
  choose c' hc' using fun k => (B k).lawV_complete' (ĝ.blkV k) 0
  choose c hc using fun k => (B k).lawV_complete' (ĥ.blkV k) (ĝ.blkV k + 0)
  refine ⟨ĥ + ĝ, by simp [ĥ, ĝ, expG_liftG], fun w hw k hk => ?_⟩
  set F : ℂ → Var d₀ d₁ B → ℂ := fun t => lawPt c (coords h₀ 1) (phPt g w c' t)
  have hFa : ∀ t₀, ∀ v, AnalyticAt ℂ (fun t => F t v) t₀ :=
    fun t₀ => analyticAt_lawPt c (fun _ => analyticAt_const) (analyticAt_phPt g w c' t₀)
  have hrel : ∀ t, ∃ κ : Fin m → ℂ, F t = liftZ (ĥ + ĝ + t • w) κ := fun t => by
    obtain ⟨κ₁, h1⟩ := lawPt_liftZ c' ĝ (t • w) 1 1
    obtain ⟨κ₂, h2⟩ := lawPt_liftZ c ĥ (ĝ + t • w) 1 κ₁
    refine ⟨κ₂, ?_⟩
    simp only [F, phPt, coords_one_eq_liftV, ← hĥ, ← hĝ, ← liftZ_one, h1, h2]
    rw [add_assoc]
  -- the blocks of `F 0` are nonzero (good laws)
  have hF0 : ∀ k, blkPt (F 0) k ≠ 0 := by
    intro k hk0
    have ea : (fun b => coords g 1 (.e k b)) = (B k).lift (ĝ.blkV k) := by
      funext b; simp [coords, VBlock.rep, ĝ, liftG_blkV]
    have eb : (fun b => liftV ((0 : ℂ) • w) (.e k b)) = (B k).lift 0 := by
      funext b; simp [liftV, Tan.blkV]; rfl
    have e1 : (fun b => phPt g w c' 0 (.e k b)) =
        evalLawV ((B k).lawV (c' k)) ((B k).lift (ĝ.blkV k)) ((B k).lift 0) := by
      show evalLawV _ (fun b => coords g 1 (.e k b)) (fun b => liftV ((0 : ℂ) • w) (.e k b)) = _
      rw [ea, eb]
    obtain ⟨κ', hκ'⟩ := (B k).lawV_eq' (c' k) (ĝ.blkV k) 0
    have hκ'0 : κ' ≠ 0 := by
      rintro rfl
      exact hc' k (by rw [hκ', zero_smul])
    have ec : (fun b => coords h₀ 1 (.e k b)) = (1 : ℂ) • (B k).lift (ĥ.blkV k) := by
      funext b; simp [coords, VBlock.rep, ĥ, liftG_blkV]
    have e2 : blkPt (F 0) k = (κ' ^ (B k).ld) • evalLawV ((B k).lawV (c k)) ((B k).lift (ĥ.blkV k))
        ((B k).lift (ĝ.blkV k + 0)) := by
      show evalLawV _ (fun b => coords h₀ 1 (.e k b)) (fun b => phPt g w c' 0 (.e k b)) = _
      rw [ec, e1, hκ', evalLawV_smul]
      simp
    rw [e2] at hk0
    exact hc k ((smul_eq_zero.mp hk0).resolve_left (pow_ne_zero _ hκ'0))
  -- `F` has order `> n` at `0`
  have hFO : (fun t => eval (F t) P) =O[𝓝 0] fun t => ‖t‖ ^ (n + 1) := by
    refine LSG.MEB.isBigO_of_iteratedDeriv_eq_zero
      (LSG.MEB.analyticAt_eval_of (f := fun v t => F t v) (hFa 0) P) fun κ hκ => ?_
    have h1 := mem_vanish.mp (h w hw κ (Nat.lt_succ_iff.mp hκ) c c') h₀ (Set.mem_singleton _) 1
    rw [eval_phOp, tcoef, div_eq_zero_iff] at h1
    exact h1.resolve_right (by exact_mod_cast κ.factorial_ne_zero)
  have hL := (isBigO_liftV_of_rel hP (a := fun t : ℂ => ĥ + ĝ + t • w) (by fun_prop) (hFa 0) hF0
    hrel).trans hFO
  refine LSG.MEB.iteratedDeriv_eq_zero_of_isBigO ?_ hL k (Nat.lt_succ_of_le hk)
  simpa [lineF_one] using analyticAt_lineF P (ĥ + ĝ) w 1 0

/-! ### Translations -/

/-- **Translation invariance** of the order, for every law choice. -/
theorem ordGtV_lawSub {W : Submodule ℂ (Tan d₀ d₁ B)} {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hQ : IsHomV Q d) {n : ℕ} {y v : GPt d₀ d₁ B} (h : OrdGtV W Q n (y + v)) (c : ∀ k, Fin (B k).nLV)
    (lam : Fin m → ℂˣ) : OrdGtV W (lawSub c (coords v lam) Q) n y := by
  set u := liftG y with hu
  set vh := liftG v with hvh
  obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ vh lam
  rw [expG_liftG] at hμ
  have hO : OrdAt W Q n (u + vh) := (ordGtV_iff hQ).mp h _ (by simp [u, vh, expG_liftG])
  refine ⟨u, expG_liftG y, fun w hw k hk => ?_⟩
  set F : ℂ → Var d₀ d₁ B → ℂ := fun s => lawPt c (liftV (u + s • w)) (coords v lam)
  have hFa : ∀ s₀, ∀ v', AnalyticAt ℂ (fun s => F s v') s₀ := fun s₀ =>
    analyticAt_lawPt c (analyticAt_liftV_comp (a := fun s : ℂ => u + s • w) (by fun_prop))
      (fun _ => analyticAt_const)
  have hfun : (fun s : ℂ => eval (liftV (u + s • w)) (lawSub c (coords v lam) Q)) =
      fun s => eval (F s) Q := by
    funext s; rw [eval_lawSub]
  rw [hfun]
  refine LSG.MEB.iteratedDeriv_eq_zero_of_isBigO (n := n + 1)
    (LSG.MEB.analyticAt_eval_of (f := fun v' s => F s v') (hFa 0) Q) ?_ k (Nat.lt_succ_of_le hk)
  refine IsBigO.trans ?_ ((ordAt_iff_one hQ).mp hO w hw)
  rw [lineF_one]
  refine isBigO_eval_liftZ_rel hQ (a := fun s : ℂ => u + vh + s • w) (by fun_prop) (hFa 0) fun s => ?_
  obtain ⟨κ, hκ⟩ := lawPt_liftZ c (u + s • w) vh 1 μ
  refine ⟨κ, ?_⟩
  simp only [F, ← liftZ_one, hμ, hκ]
  rw [add_right_comm]

/-! ### The two-parameter lemma -/

/-- **The two-parameter lemma** (Philippon's `δ^T ∘ δ^κ`): if `P` has order `> N` along `W` at `y + σ`, `w' ∈ W`
and `κ + T ≤ N`, then `phOp σ w' c c' κ P` has order `> T` along `W` at `y`, for every law choice. -/
theorem ordGtV_phOp {W : Submodule ℂ (Tan d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hP : IsHomV P d) {N T κ : ℕ} {y σ : GPt d₀ d₁ B} (h : OrdGtV W P N (y + σ)) {w' : Tan d₀ d₁ B}
    (hw' : w' ∈ W) (hκ : κ + T ≤ N) (c c' : ∀ k, Fin (B k).nLV) :
    OrdGtV W (phOp σ w' c c' κ P) T y := by
  set u := liftG y with hu
  set sh := liftG σ with hsh
  have hO : OrdAt W P N (u + sh) := (ordGtV_iff hP).mp h _ (by simp [u, sh, expG_liftG])
  refine ⟨u, expG_liftG y, fun w hw i hi => ?_⟩
  let Fq : ℂ × ℂ → Var d₀ d₁ B → ℂ := fun q => lawPt c (liftV (u + q.1 • w)) (phPt σ w' c' q.2)
  have hFa : ∀ q₀, ∀ v, AnalyticAt ℂ (fun q => Fq q v) q₀ := fun q₀ =>
    analyticAt_lawPt c (analyticAt_liftV_comp (a := fun q : ℂ × ℂ => u + q.1 • w)
      (analyticAt_const.add (analyticAt_fst.smul analyticAt_const)))
      (fun v => (analyticAt_phPt σ w' c' q₀.2 v).comp (f := fun q : ℂ × ℂ => q.2) analyticAt_snd)
  let G : ℂ × ℂ → ℂ := fun q => eval (Fq q) P
  have hG : AnalyticOnNhd ℂ G univ := fun q₀ _ =>
    LSG.MEB.analyticAt_eval_of (f := fun v q => Fq q v) (hFa q₀) P
  -- the function along `w` is a Taylor coefficient of `G`
  have hfun : (fun s : ℂ => eval (liftV (u + s • w)) (phOp σ w' c c' κ P)) =
      fun s => iteratedDeriv κ (fun t' => G (s, t')) 0 / κ.factorial := by
    funext s; rw [eval_phOp, tcoef]
  rw [hfun, iteratedDeriv_div_const, div_eq_zero_iff]
  left
  -- `G = O(‖q‖^{N+1})`
  let F₂ : ℂ × ℂ → ℂ := fun q => eval (liftV (u + sh + (q.1 • w + q.2 • w'))) P
  have hF₂a : AnalyticOnNhd ℂ F₂ univ := fun q₀ _ => by
    have haff : AnalyticAt ℂ (fun q : ℂ × ℂ => u + sh + (q.1 • w + q.2 • w')) q₀ :=
      analyticAt_const.add ((analyticAt_fst.smul analyticAt_const).add
        (analyticAt_snd.smul analyticAt_const))
    have hv : ∀ v, AnalyticAt ℂ (fun q : ℂ × ℂ => liftV (u + sh + (q.1 • w + q.2 • w')) v) q₀ :=
      fun v => analyticAt_liftV_comp haff v
    exact LSG.MEB.analyticAt_eval_of hv P
  have hF₂ : F₂ =O[𝓝 0] fun q => ‖q‖ ^ (N + 1) := by
    refine LSG.MEB.isBigO_of_diag hF₂a fun v k hk => ?_
    have hmem : v.1 • w + v.2 • w' ∈ W := W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hw')
    have e : (fun r : ℂ => F₂ (r • v)) = lineF P (u + sh) (v.1 • w + v.2 • w') 1 := by
      funext r
      simp only [F₂, lineF, liftZ_one, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    rw [e]
    exact hO 1 _ hmem k (Nat.lt_succ_iff.mp hk)
  have hGO : G =O[𝓝 0] fun q => ‖q‖ ^ (N + 1) := by
    refine IsBigO.trans ?_ hF₂
    refine isBigO_eval_liftZ_rel hP (a := fun q : ℂ × ℂ => u + sh + (q.1 • w + q.2 • w'))
      (by fun_prop) (hFa 0) fun q => ?_
    obtain ⟨κ₁, h1⟩ := lawPt_liftZ c' sh (q.2 • w') 1 1
    obtain ⟨κ₂, h2⟩ := lawPt_liftZ c (u + q.1 • w) (sh + q.2 • w') 1 κ₁
    refine ⟨κ₂, ?_⟩
    simp only [Fq, phPt, coords_one_eq_liftV, ← hsh, ← liftZ_one, h1, h2]
    congr 1
    abel
  exact LSG.MEB.iteratedDeriv_iteratedDeriv_snd_eq_zero hG hGO (by omega)

end LSG.MEBV
