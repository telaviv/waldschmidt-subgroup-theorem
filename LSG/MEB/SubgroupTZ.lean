/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupLie
import LSG.MEB.Deriv
import LSG.MEB.Chain

/-!
# Zariski tangent directions lie in the analytic Lie algebra (A4.3, β′)

ME's `SubgroupTangent` (`TZ_subset_lieAlg`) for abstract blocks. Here there is no Euler correction at points where a
chart form vanishes: `eval_Dh_liftB` holds at every lifted point, whatever the value of the chart forms.

* **`ordGtB_of_lawSub`**: the converse of `ordGtB_lawSub` for a *good* law choice (`Good y v c`).
* `mem_vanish_of_liftB`, `eval_liftB_eq_zero_of_mem_vanish`: membership of a multihomogeneous polynomial through the
  lift `liftB`.
* `ordGtB_span_iff`: order `> 1` along `ℂ ∙ w` at a point of `E` is the vanishing of the first derivative at every
  lift.
* **`ordGtB_one_of_one`** (translation): order `> 1` along `W` of every multihomogeneous element of `I(H)` at one point
  of a Zariski-closed subgroup `H` gives it at every point of `H`; `ordGtB_one_of_coset`: the same from a point of a
  coset `H + h`.
* **`mem_lieAlg_of_deriv`**: if the first derivative along `w` of every multihomogeneous element of `I(H)` vanishes
  at every point of `H`, then `w ∈ lieAlg H` (`Dh ch w` maps these elements into `I(H)`; iterating, `s ↦ P(liftB (s w))`
  has infinite order at `0`, hence vanishes identically).
* **`mem_lieAlg_of_ordGtB`**: the same from order `> 1` along `ℂ ∙ w` at a single point of `H`.
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Blocks of substituted points -/

theorem blkPt_lawPt (c : ∀ k, Fin (B k).nL) (x y : Var d₀ d₁ B → ℂ) (k : Fin m) :
    blkPt (lawPt c x y) k = evalLaw ((B k).law (c k)) (blkPt x k) (blkPt y k) := by
  funext b; rfl

theorem blkPt_coords_one (g : GPt d₀ d₁ B) (k : Fin m) : blkPt (coords g 1) k = (B k).rep (g.2.2 k) := by
  funext b; simp [blkPt, coords]

/-! ### Reverse translation (good law) -/

/-- **Converse of `ordGtB_lawSub`** for a good law choice. -/
theorem ordGtB_of_lawSub {W : Submodule ℂ (Tan d₀ d₁ B)} {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hQ : IsHomB Q d) {n : ℕ} {y v : GPt d₀ d₁ B} {c : ∀ k, Fin (B k).nL} (hc : Good y v c)
    (h : OrdGtB W (lawSub c (coords v 1) Q) n y) : OrdGtB W Q n (y + v) := by
  set u := liftOf y with hu
  set vh := liftOf v with hvh
  have hO : OrdAt W (lawSub c (coords v 1) Q) n u :=
    (ordGtB_iff (isHomB_lawSub c _ hQ)).mp h _ (expG_liftOf y)
  refine ⟨u + vh, by simp [u, vh, expG_liftOf], fun w hw k hk => ?_⟩
  set F : ℂ → Var d₀ d₁ B → ℂ := fun s => lawPt c (liftB (u + s • w)) (coords v 1)
  have hFa : ∀ s₀, ∀ v', AnalyticAt ℂ (fun s => F s v') s₀ := fun s₀ =>
    analyticAt_lawPt c (analyticAt_liftB_comp (a := fun s : ℂ => u + s • w) (by fun_prop))
      (fun _ => analyticAt_const)
  refine iteratedDeriv_eq_zero_of_isBigO (n := n + 1)
    (analyticAt_eval_of (f := fun v' (s : ℂ) => liftB (u + vh + s • w) v')
      (fun v' => analyticAt_liftB_comp (by fun_prop) v') Q) ?_ k (Nat.lt_succ_of_le hk)
  have h1 : (fun s : ℂ => eval (liftB (u + vh + s • w)) Q) =O[𝓝 0] fun s => eval (F s) Q := by
    refine isBigO_liftB_of_rel hQ (a := fun s : ℂ => u + vh + s • w) (by fun_prop) (hFa 0) (fun k' => ?_)
      fun s => ?_
    · have e : blkPt (F 0) k' = evalLaw ((B k').law (c k')) ((B k').rep (y.2.2 k')) ((B k').rep (v.2.2 k')) := by
        simp only [F, zero_smul, add_zero, blkPt_lawPt, blkPt_coords_one]
        rw [hu, ← coords_one_eq_liftB, blkPt_coords_one]
      rw [e]; exact hc k'
    · obtain ⟨κ, hκ⟩ := lawPt_liftZ c (u + s • w) vh 1 1
      refine ⟨κ, ?_⟩
      simp only [F, coords_one_eq_liftB, ← liftZ_one]
      rw [add_right_comm]; exact hκ
  refine h1.trans ?_
  have h2 := (ordAt_iff_one (isHomB_lawSub c _ hQ)).mp hO w hw
  rw [lineF_one] at h2
  simpa [F, eval_lawSub] using h2

/-! ### Membership through the lift -/

theorem eval_liftB_eq_zero_of_mem_vanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ vanish E) {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ E) : eval (liftB u) P = 0 := by
  obtain ⟨lam, hlam⟩ := coords_expG u
  rw [← hlam]; exact mem_vanish.mp hP _ hu lam

theorem mem_vanish_of_liftB {E : Set (GPt d₀ d₁ B)} {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hQ : IsHomB Q d) (h : ∀ u, expG d₀ d₁ B u ∈ E → eval (liftB u) Q = 0) : Q ∈ vanish E := by
  refine mem_vanish.mpr fun g hg lam => ?_
  obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ (liftOf g) lam
  rw [expG_liftOf] at hμ
  rw [hμ, show μ = 1 * μ by simp, eval_liftZ_mul hQ, liftZ_one, h _ (by rwa [expG_liftOf]), mul_zero]

theorem isHomB_of_mem_homogVanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ homogVanish E) : ∃ d, IsHomB P d := by
  obtain ⟨d, hd⟩ := hP.2
  exact ⟨d, isHomB_iff_wV.mpr hd⟩

/-! ### Order `> 1` along a line -/

/-- The first derivative along `w` at the lift `u`. -/
noncomputable def dirD (P : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) : ℂ :=
  deriv (fun r : ℂ => eval (liftB (u + r • w)) P) 0

theorem ordGtB_span_iff {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hP : IsHomB P d) (hPv : P ∈ vanish E) {g : GPt d₀ d₁ B} (hg : g ∈ E) (w : Tan d₀ d₁ B) :
    OrdGtB (ℂ ∙ w) P 1 g ↔ ∀ u, expG d₀ d₁ B u = g → dirD P u w = 0 := by
  constructor
  · intro h u hu
    have h1 := (ordGtB_iff hP).mp h u hu 1 w (Submodule.mem_span_singleton_self w) 1 le_rfl
    rw [lineF_one, iteratedDeriv_one] at h1
    exact h1
  · intro h
    refine ⟨liftOf g, expG_liftOf g, fun w' hw' k hk => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    interval_cases k
    · simp only [iteratedDeriv_zero, zero_smul, add_zero]
      exact eval_liftB_eq_zero_of_mem_vanish hPv (by rwa [expG_liftOf])
    · rw [iteratedDeriv_one]
      have e : (fun s : ℂ => eval (liftB (liftOf g + s • a • w)) P) =
          fun s => (fun r : ℂ => eval (liftB (liftOf g + r • w)) P) (a * s) := by
        funext s; rw [smul_smul, mul_comm]
      rw [e, deriv_comp_mul_left a (fun r : ℂ => eval (liftB (liftOf g + r • w)) P) 0, mul_zero]
      have := h (liftOf g) (expG_liftOf g)
      rw [dirD] at this
      rw [this, smul_zero]

/-! ### Translation inside a subgroup -/

variable {H : Set (GPt d₀ d₁ B)}

theorem gtransl_self_of_mem (hH : IsSubgroupG H) {g : GPt d₀ d₁ B} (hg : g ∈ H) : gtransl g H = H := by
  rw [gtransl_eq_of_sub_mem hH (b := 0) (by simpa using hg), gtransl_zero]

/-- **Translation**: order `> 1` along `W` at one point `g₀ ∈ H` of every multihomogeneous element of `I(H)` gives it
at every point of `H`. -/
theorem ordGtB_one_of_one (hH : IsSubgroupG H) {W : Submodule ℂ (Tan d₀ d₁ B)} {g₀ : GPt d₀ d₁ B}
    (hg₀ : g₀ ∈ H) (h₀ : ∀ P ∈ homogVanish H, OrdGtB W P 1 g₀) :
    ∀ g ∈ H, ∀ P ∈ homogVanish H, OrdGtB W P 1 g := by
  intro g hg P hP
  obtain ⟨d, hd⟩ := isHomB_of_mem_homogVanish hP
  obtain ⟨c, hc⟩ := exists_good g₀ (g - g₀)
  have hmem : τ (-(g₀ - g)) c P ∈ vanish (gtransl (g₀ - g) H) := transl_mem_vanish_gtransl _ c hP.1
  have hm : g₀ - g ∈ H := by simpa [sub_eq_add_neg] using hH.add_mem _ hg₀ _ (hH.neg_mem _ hg)
  rw [gtransl_self_of_mem hH hm, neg_sub] at hmem
  have hτ : τ (g - g₀) c P ∈ homogVanish H :=
    ⟨hmem, ⟨_, isHomB_iff_wV.mp (isHomB_transl (g - g₀) c hd)⟩⟩
  have := ordGtB_of_lawSub hd hc (h₀ _ hτ)
  simpa using this

/-- **From a coset**: order `> 1` along `W` at a point `g'` of `H + h` of every multihomogeneous element of
`I(H + h)` gives order `> 1` at `g' - h ∈ H` of every multihomogeneous element of `I(H)`. -/
theorem ordGtB_one_of_coset {W : Submodule ℂ (Tan d₀ d₁ B)} {h g' : GPt d₀ d₁ B}
    (h₀ : ∀ P ∈ homogVanish (gtransl h H), OrdGtB W P 1 g') :
    ∀ P ∈ homogVanish H, OrdGtB W P 1 (g' + -h) := by
  intro P hP
  obtain ⟨d, hd⟩ := isHomB_of_mem_homogVanish hP
  obtain ⟨c, hc⟩ := exists_good g' (-h)
  have hτ : τ (-h) c P ∈ homogVanish (gtransl h H) :=
    ⟨transl_mem_vanish_gtransl h c hP.1, ⟨_, isHomB_iff_wV.mp (isHomB_transl (-h) c hd)⟩⟩
  exact ordGtB_of_lawSub hd hc (h₀ _ hτ)

/-! ### `Dh` preserves `I(H)` along tangent directions -/

theorem Dh_mem_vanish_of_dirD {E : Set (GPt d₀ d₁ B)} (ch : ∀ k, Fin (B k).N) (hch : ∀ k, ch k ∈ (B k).charts)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) (hPv : P ∈ vanish E)
    {w : Tan d₀ d₁ B} (h : ∀ u, expG d₀ d₁ B u ∈ E → dirD P u w = 0) : Dh ch w P ∈ vanish E :=
  mem_vanish_of_liftB (isHomB_Dh ch w hP) fun u hu => by
    rw [eval_Dh_liftB ch hch hP, show deriv (fun r : ℂ => eval (liftB (u + r • w)) P) 0 = dirD P u w from rfl,
      h u hu, eval_liftB_eq_zero_of_mem_vanish hPv hu]
    ring

/-! ### Infinite order along `w` -/

/-- The line function `s ↦ P(liftB (s w))`. -/
noncomputable def lineW (P : MvPolynomial (Var d₀ d₁ B) ℂ) (w : Tan d₀ d₁ B) (s : ℂ) : ℂ :=
  eval (liftB (s • w)) P

theorem analyticAt_lineW (P : MvPolynomial (Var d₀ d₁ B) ℂ) (w : Tan d₀ d₁ B) (s₀ : ℂ) :
    AnalyticAt ℂ (lineW P w) s₀ :=
  analyticAt_eval_of (f := fun v (s : ℂ) => liftB (s • w) v) (fun v => analyticAt_liftB_comp (by fun_prop) v) P

theorem dirD_smul_eq_deriv (P : MvPolynomial (Var d₀ d₁ B) ℂ) (w : Tan d₀ d₁ B) (s : ℂ) :
    dirD P (s • w) w = deriv (lineW P w) s := by
  have e : (fun r : ℂ => eval (liftB (s • w + r • w)) P) = fun r => lineW P w (r + s) := by
    funext r; simp only [lineW, add_smul, add_comm]
  rw [dirD, e, deriv_comp_add_const, zero_add]

/-- A chart at the identity: all chart forms are nonzero at `liftB 0`. -/
theorem exists_chart_zero : ∃ ch : ∀ k, Fin (B k).N, (∀ k, ch k ∈ (B k).charts) ∧
    eval (liftB (0 : Tan d₀ d₁ B)) (Lc ch) ≠ 0 := by
  have h := fun k => (B k).chart_cover ((B k).θ 0) ((B k).θ_ne 0) ((B k).θ_model 0)
  choose ch hch hne using h
  refine ⟨ch, hch, ?_⟩
  rw [Lc, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  rw [eval_Lk_liftB]; exact hne k

theorem continuousAt_DhCorr (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) (d : Fin m → ℕ) :
    ContinuousAt (fun s : ℂ => ∑ k, eval (liftB (s • w)) (Lo ch k) *
        fderiv ℂ (B k).θ ((s • w).2.2 k) (w.2.2 k) (ch k) * d k) 0 := by
  refine tendsto_finsetSum _ fun k _ => ?_
  refine ((continuous_eval_liftB_affine (Lo ch k) 0 w).continuousAt.congr ?_ |>.mul ?_).mul continuousAt_const
  · exact Eventually.of_forall fun s => by simp
  have hf : ContinuousAt (fun z => fderiv ℂ (B k).θ z) (((0 : ℂ) • w).2.2 k) :=
    ((B k).θ_analytic _).fderiv.continuousAt
  have hz : Continuous fun s : ℂ => (s • w).2.2 k := by fun_prop
  exact (continuous_apply (ch k)).continuousAt.comp
    ((ContinuousLinearMap.apply ℂ _ (w.2.2 k)).continuous.continuousAt.comp (hf.comp hz.continuousAt))

/-- **Infinite order**: if the first derivative along `w` of every multihomogeneous element of `I(H)` vanishes at
every point of `H` (`0 ∈ H`), then each `s ↦ P(liftB (s w))` is `O(sⁿ)` for every `n`. -/
theorem lineW_isBigO {E : Set (GPt d₀ d₁ B)} (h0 : (0 : GPt d₀ d₁ B) ∈ E) {w : Tan d₀ d₁ B}
    (hall : ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomB P d → P ∈ vanish E →
      ∀ u, expG d₀ d₁ B u ∈ E → dirD P u w = 0) (n : ℕ) :
    ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomB P d → P ∈ vanish E →
      lineW P w =O[𝓝 0] fun s => ‖s‖ ^ n := by
  obtain ⟨ch, hch, hL⟩ := exists_chart_zero (d₀ := d₀) (d₁ := d₁) (B := B)
  induction n with
  | zero =>
    intro P d _ _
    simpa using (analyticAt_lineW P w 0).continuousAt.isBigO_one ℝ
  | succ n ih =>
    intro P d hP hPv
    have hD := ih _ _ (isHomB_Dh ch w hP) (Dh_mem_vanish_of_dirD ch hch hP hPv (hall P d hP hPv))
    have hPn := ih P d hP hPv
    -- `Lc · (lineW P w)' = lineW (Dh P) w + corr · lineW P w`
    set Lf : ℂ → ℂ := fun s => eval (liftB (s • w)) (Lc ch)
    set cf : ℂ → ℂ := fun s => ∑ k, eval (liftB (s • w)) (Lo ch k) *
        fderiv ℂ (B k).θ ((s • w).2.2 k) (w.2.2 k) (ch k) * d k
    have hid : ∀ s, Lf s * deriv (lineW P w) s = lineW (Dh ch w P) w s + cf s * lineW P w s := fun s => by
      have := eval_Dh_liftB ch hch hP (s • w) w
      rw [show deriv (fun r : ℂ => eval (liftB (s • w + r • w)) P) 0 = dirD P (s • w) w from rfl,
        dirD_smul_eq_deriv] at this
      simp only [lineW, Lf, cf]
      rw [this]; ring
    have hLc : ContinuousAt Lf 0 :=
      (continuous_eval_liftB_affine (Lc ch) 0 w).continuousAt.congr
        (Eventually.of_forall fun s => by simp [Lf])
    have hL0 : Lf 0 ≠ 0 := by simpa [Lf] using hL
    have hinv : (fun s => (Lf s)⁻¹) =O[𝓝 0] fun _ => (1 : ℝ) := (hLc.inv₀ hL0).isBigO_one ℝ
    have hderiv : deriv (lineW P w) =O[𝓝 0] fun s => ‖s‖ ^ n := by
      have hne : ∀ᶠ s in 𝓝 0, Lf s ≠ 0 := hLc.eventually_ne hL0
      have hsum : (fun s => lineW (Dh ch w P) w s + cf s * lineW P w s) =O[𝓝 0] fun s => ‖s‖ ^ n :=
        hD.add (by simpa only [one_mul] using ((continuousAt_DhCorr ch w d).isBigO_one ℝ).mul hPn)
      have := hinv.mul hsum
      simp only [one_mul] at this
      refine this.congr' (hne.mono fun s hs => ?_) (Eventually.of_forall fun _ => rfl)
      beta_reduce
      rw [← hid s, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [← isBigO_pow_iff (analyticAt_lineW P w 0)]
    intro i hi
    cases i with
    | zero =>
      simp only [iteratedDeriv_zero, lineW, zero_smul]
      exact eval_liftB_eq_zero_of_mem_vanish hPv (by simpa using h0)
    | succ j =>
      rw [iteratedDeriv_succ']
      exact (isBigO_pow_iff ((analyticAt_lineW P w 0).deriv)).mpr hderiv j (by omega)

/-- **Tangent directions are Lie directions**: if the first derivative along `w` of every multihomogeneous element
of `I(H)` vanishes at every point of `H`, then `w ∈ lieAlg H`. -/
theorem mem_lieAlg_of_dirD (hH : IsSubgroupG H) (hc : IsZClosed H) {w : Tan d₀ d₁ B}
    (hall : ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomB P d → P ∈ vanish H →
      ∀ u, expG d₀ d₁ B u ∈ H → dirD P u w = 0) : w ∈ lieAlg hH := by
  intro s
  rw [mem_Htil, expG_mem_iff hc]
  intro P hP
  obtain ⟨d, hd⟩ := isHomB_of_mem_homogVanish hP
  have hO := lineW_isBigO hH.zero_mem hall
  have htop : analyticOrderAt (lineW P w) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analyticAt_lineW P w 0)]
    exact (isBigO_pow_iff (analyticAt_lineW P w 0)).mpr (hO n P d hd hP.1)
  have h0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (analyticAt_lineW P w)).mp htop
  exact congrFun h0 s

/-- **`TZ ⊆ lieAlg`**: order `> 1` along `ℂ ∙ w` at one point of `H` of every multihomogeneous element of `I(H)`
forces `w ∈ lieAlg H`. -/
theorem mem_lieAlg_of_ordGtB (hH : IsSubgroupG H) (hc : IsZClosed H) {w : Tan d₀ d₁ B} {g₀ : GPt d₀ d₁ B}
    (hg₀ : g₀ ∈ H) (h₀ : ∀ P ∈ homogVanish H, OrdGtB (ℂ ∙ w) P 1 g₀) : w ∈ lieAlg hH := by
  have hall := ordGtB_one_of_one hH hg₀ h₀
  refine mem_lieAlg_of_dirD hH hc fun P d hP hPv u hu => ?_
  have hPh : P ∈ homogVanish H := ⟨hPv, ⟨d, isHomB_iff_wV.mp hP⟩⟩
  exact (ordGtB_span_iff hP hPv hu w).mp (hall _ hu P hPh) u rfl

end LSG.MEB
