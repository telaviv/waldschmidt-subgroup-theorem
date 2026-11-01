/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7VPoly
import LSG.W88.Sec7Taylor
import LSG.MEV.SubgroupDimV
import LSG.MEV.Canon

/-!
# W88 §7 for the class `𝒞`: analytic vanishing gives formal order (`OrdGt`)

`OrdGt Ls W Q n g` is defined through the formal points `phPt g w c' = law_{c'}(rep g, ExpV w)`
(`LSG.MEV.Chain`). For `g = exp(liftT y)` and `w = liftT w₀`:

1. **`tps_FVb_ray`**: the formal exponential `ExpBlock a b` of one `E^♮` block is the Taylor series
of
   the `V`-normalised analytic lift `c ↦ FVb(c a, c b)` at the identity (both are flows of the
   `V`-chart
   field, `bField = dvalB 0` (`bField_eq_dvalB`), with the same initial value; `eq_of_isBFlow`).
2. **`tps_law`**: the laws commute with Taylor series (`NLaw_map` applied to a generic polynomial).
3. **`exists_law_unit`**: analytically,
`law_c(rep exp(z₀, 0), FVb(c a, 0)) = κ(c) • ellN(z₀ + c a, 0)` near
   `c = 0`, with `κ` analytic (`NLaw_repV`, `NLaw_smul`).
4. **`ordGt_of_vanishAlongV`**: by homogeneity,
`PpolyV(phPt-analytic(c)) = Π κ_k(c)^D · PsiV(y + c w₀)`
   near `0`, so `VanishAlong` gives the vanishing of the low Taylor coefficients.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module LSG.MEV Filter Topology
open LSG.W88.Vec (TanV)
open LSG.AuxV (MonoV PsiV ellN)
open LSG.Aux (ellW tco)
open LSG.ME (g2L g3L)

noncomputable section

namespace LSG.W88

variable {d0 d1 m r : ℕ}

/-! ### The `V`-chart field -/

theorem bField_eq_dvalB (g₂ g₃ a b : ℂ) (P : Fin 5 → ℂ) (l : Fin 5) :
    bField g₂ g₃ a b P l = dvalB 0 g₂ g₃ (a / 2) b P l := by
  fin_cases l <;> simp only [bField, dvalB, LSG.ME.c2, rhoh, Pe, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Algebra.algebraMap_self, RingHom.id_apply] <;> ring1

theorem eval_dvalPoly (g₂ g₃ s β : ℂ) (x : Fin 5 → ℂ) (l : Fin 5) :
    eval x (dvalPoly (g₂ := g₂) (g₃ := g₃) 0 s β l) = dvalB 0 g₂ g₃ s β x l := by
  rw [dvalPoly, dvalB_map (eval x)]
  simp only [eval_C, Function.comp_def, eval_X]

/-! ### The formal exponential at the identity -/

section Ray

variable (L : PeriodPair)

theorem ellW_two_zero : ellW L 2 0 = -2 := by
  have := congrFun (LSG.AuxV.ellN_at_zero L 0) 1
  rw [LSG.AuxV.ellN_one] at this; simpa [ptO] using this

theorem eventually_ellW_ray (a : ℂ) : ∀ᶠ c : ℂ in 𝓝 0, ellW L 2 (c * a) ≠ 0 := by
  have hc : ContinuousAt (fun c : ℂ => ellW L 2 (c * a)) 0 :=
    ((LSG.Aux.differentiable_ellW L 2).continuous.comp (by fun_prop)).continuousAt
  have h0 : ellW L 2 ((0 : ℂ) * a) ≠ 0 := by rw [zero_mul, ellW_two_zero]; norm_num
  exact hc.eventually_ne h0

theorem analyticAt_ellN_ray (z₀ a b : ℂ) (i : Fin 5) :
    AnalyticAt ℂ (fun c : ℂ => ellN L (z₀ + c * a) (c * b) i) 0 := by
  have hf : Differentiable ℂ (fun c : ℂ => (z₀ + c * a, c * b)) := by fun_prop
  exact ((LSG.AuxV.differentiable_ellN L i).comp hf).analyticAt 0

theorem analyticAt_FVb_ray (a b : ℂ) (i : Fin 5) :
    AnalyticAt ℂ (fun c : ℂ => FVb L (c * a) (c * b) i) 0 := by
  have hf : Differentiable ℂ fun c : ℂ => c * a := by fun_prop
  have h1 : AnalyticAt ℂ (fun c : ℂ => ellW L 2 (c * a)) 0 :=
    ((LSG.Aux.differentiable_ellW L 2).comp hf).analyticAt 0
  have h2 := analyticAt_ellN_ray L 0 a b i
  simp only [zero_add] at h2
  have : (fun c : ℂ => FVb L (c * a) (c * b) i) =
      fun c => (ellW L 2 (c * a))⁻¹ * ellN L (c * a) (c * b) i := by
    funext c; simp [FVb]
  rw [this]
  exact (h1.inv (by simp [ellW_two_zero])).mul h2

theorem hasDerivAt_FVb_ray {a b c₀ : ℂ} (h : ellW L 2 (c₀ * a) ≠ 0) (i : Fin 5) :
    HasDerivAt (fun c : ℂ => FVb L (c * a) (c * b) i)
      (bField L.g₂ L.g₃ a b (FVb L (c₀ * a) (c₀ * b)) i) c₀ := by
  have h0 := hasDerivAt_FVb_line L h (c₀ * b) a b i
  have h1 := HasDerivAt.comp_sub_const c₀ c₀ (by rw [sub_self]; exact h0)
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun c => ?_)
  simp only
  congr 1 <;> ring

/-- **The formal exponential of `E^♮` is the Taylor series of the `V`-normalised lift.** -/
theorem tps_FVb_ray (a b : ℂ) :
    (fun i => tps (fun c => FVb L (c * a) (c * b) i)) = ExpBlock L.g₂ L.g₃ a b := by
  have hflow : IsBFlow (R := ℂ) L.g₂ L.g₃ 0 (a / 2) b
      (fun i => tps (fun c => FVb L (c * a) (c * b) i)) := by
    refine ⟨?_, fun l => ?_⟩
    · change tps (fun c => FVb L (c * a) (c * b) 1) = 1
      have hev : (fun c => FVb L (c * a) (c * b) 1) =ᶠ[𝓝 0] fun _ => 1 :=
        (eventually_ellW_ray L a).mono fun c hc => FVb_V L hc _
      rw [tps_congr hev, tps_const]; rfl
    · rw [derivative_tps]
      have hev : deriv (fun c => FVb L (c * a) (c * b) l) =ᶠ[𝓝 0] fun c =>
          eval (fun i => FVb L (c * a) (c * b) i)
            (dvalPoly (g₂ := L.g₂) (g₃ := L.g₃) 0 (a / 2) b l) :=
        (eventually_ellW_ray L a).mono fun c hc => by
          rw [(hasDerivAt_FVb_ray L hc l).deriv]
          beta_reduce
          rw [eval_dvalPoly, bField_eq_dvalB]
      rw [tps_congr hev, tps_eval (fun i c => FVb L (c * a) (c * b) i)
        (fun i => analyticAt_FVb_ray L a b i), aeval_dvalPoly]
  have h2 := ExpBlock_isBFlow (K := ℂ) L.g₂ L.g₃ (a / 2) b
  rw [mul_div_cancel₀ _ (two_ne_zero' ℂ)] at h2
  refine eq_of_isBFlow hflow h2 fun l => ?_
  rw [constantCoeff_tps, constantCoeff_ExpBlock]
  simp only [zero_mul]
  rw [FVb_zero]

end Ray

/-! ### Laws and Taylor series -/

/-- The law `c(P₀, ·)` as a polynomial in the second argument. -/
def lawPoly (cc : LC) (g₂ g₃ : ℂ) (P₀ : Fin 5 → ℂ) (i : Fin 5) : MvPolynomial (Fin 5) ℂ :=
  nlawc cc (C g₂) (C g₃) (fun l => C (P₀ l)) X i

theorem eval_lawPoly (cc : LC) (g₂ g₃ : ℂ) (P₀ x : Fin 5 → ℂ) (i : Fin 5) :
    eval x (lawPoly cc g₂ g₃ P₀ i) = nlawc cc g₂ g₃ P₀ x i := by
  rw [lawPoly, nlawc, NLaw_map (eval x)]
  simp only [eval_C, Function.comp_def, eval_X]
  rfl

theorem aeval_lawPoly (cc : LC) (g₂ g₃ : ℂ) (P₀ : Fin 5 → ℂ) (Γ : Fin 5 → PowerSeries ℂ)
    (i : Fin 5) :
    aeval Γ (lawPoly cc g₂ g₃ P₀ i) = nlawc cc (algebraMap ℂ _ g₂) (algebraMap ℂ _ g₃)
      (fun l => PowerSeries.C (P₀ l)) Γ i := by
  rw [lawPoly, nlawc, ← AlgHom.coe_toRingHom, NLaw_map]
  simp only [AlgHom.coe_toRingHom, aeval_C]
  congr 1
  · funext l; simp
  · funext l; simp

/-- **The laws commute with Taylor series.** -/
theorem tps_law (cc : LC) (g₂ g₃ : ℂ) (P₀ : Fin 5 → ℂ) (F : Fin 5 → ℂ → ℂ)
    (hF : ∀ l, AnalyticAt ℂ (F l) 0) (i : Fin 5) :
    tps (fun c => nlawc cc g₂ g₃ P₀ (fun l => F l c) i) =
      nlawc cc (algebraMap ℂ _ g₂) (algebraMap ℂ _ g₃) (fun l => PowerSeries.C (P₀ l))
        (fun l => tps (F l)) i := by
  rw [← aeval_lawPoly, ← tps_eval F hF]
  congr 1; funext c; rw [eval_lawPoly]

/-! ### The law value along a ray, analytically -/

section LawRay

variable (L : PeriodPair)

theorem law_ray_eq (cc : LC) (z₀ a c : ℂ) :
    ∃ s : ℂ, nlawc cc L.g₂ L.g₃ (repV (expV L (z₀, 0))) (FVb L (c * a) (c * 0)) =
      s • ellN L (z₀ + c * a) 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := LSG.AuxV.ellN_eq_smul_expN L (c * a) 0
  obtain ⟨c₂, hc₂, h₂⟩ := LSG.AuxV.ellN_eq_smul_expN L (z₀ + c * a) 0
  obtain ⟨μ, hμ⟩ := NLaw_repV (expV L (z₀, 0)) (expV L (c * a, 0)) cc.1 cc.2.1 cc.2.2
  have hF : FVb L (c * a) (c * 0) = ((ellW L 2 (c * a))⁻¹ * c₁) • repV (expV L (c * a, 0)) := by
    rw [mul_zero, FVb, h₁, repV_expV, smul_smul]
  have hsum : expV L (z₀, 0) + expV L (c * a, 0) = expV L (z₀ + c * a, 0) := by
    rw [← expV_add, Prod.mk_add_mk, add_zero]
  refine ⟨((ellW L 2 (c * a))⁻¹ * c₁) ^ 3 * μ * c₂⁻¹, ?_⟩
  have hs := NLaw_smul L.g₂ L.g₃ cc.1 cc.2.1 cc.2.2 (repV (expV L (z₀, 0)))
    (repV (expV L (c * a, 0))) 1 ((ellW L 2 (c * a))⁻¹ * c₁)
  rw [one_smul, one_mul] at hs
  rw [nlawc, hF, hs, hμ, hsum, repV_expV, h₂]
  simp only [smul_smul]
  congr 1
  field_simp

theorem exists_law_unit (cc : LC) (z₀ a : ℂ) :
    ∃ κ : ℂ → ℂ, AnalyticAt ℂ κ 0 ∧ ∀ᶠ c : ℂ in 𝓝 0,
      nlawc cc L.g₂ L.g₃ (repV (expV L (z₀, 0))) (FVb L (c * a) (c * 0)) =
        κ c • ellN L (z₀ + c * a) 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, ellN L z₀ 0 i ≠ 0 := by
    by_contra h
    push Not at h
    exact LSG.AuxV.ellN_ne_zero L z₀ 0 (funext h)
  have hlaw : AnalyticAt ℂ (fun c => nlawc cc L.g₂ L.g₃ (repV (expV L (z₀, 0)))
      (FVb L (c * a) (c * 0)) i₀) 0 := by
    have := LSG.ME.analyticAt_eval (f := fun l c => FVb L (c * a) (c * 0) l)
      (fun l => analyticAt_FVb_ray L a 0 l) (lawPoly cc L.g₂ L.g₃ (repV (expV L (z₀, 0))) i₀)
    simp only [eval_lawPoly] at this
    exact this
  have hE := analyticAt_ellN_ray L z₀ a 0 i₀
  simp only [mul_zero] at hE
  refine ⟨fun c => nlawc cc L.g₂ L.g₃ (repV (expV L (z₀, 0))) (FVb L (c * a) (c * 0)) i₀ /
    ellN L (z₀ + c * a) 0 i₀, hlaw.div hE (by simpa using hi₀), ?_⟩
  filter_upwards [hE.continuousAt.eventually_ne (by simpa using hi₀)] with c hc
  obtain ⟨s, hs⟩ := law_ray_eq L cc z₀ a c
  rw [hs]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end LawRay

/-! ### Homogeneity at points of `ℂ` -/

/-- Rescaling of the `E^♮` blocks of a point of `ℂ^{Var}`. -/
def sclE {n : ℕ} (u : Fin m → ℂ) (x : Var n d1 m → ℂ) : Var n d1 m → ℂ
  | .e k c => u k * x (.e k c)
  | v => x v

theorem eval_sclE {n : ℕ} {Q : MvPolynomial (Var n d1 m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (u : Fin m → ℂ) (x : Var n d1 m → ℂ) :
    eval (sclE u x) Q = (∏ k, u k ^ d k) * eval x Q := by
  have h := aeval_sclV hQ (fun k => PowerSeries.C (u k)) (fun v => PowerSeries.C (x v))
  have h2 := congrArg PowerSeries.constantCoeff h
  rw [LSG.ME.constantCoeff_aeval, map_mul, LSG.ME.constantCoeff_aeval, map_prod] at h2
  have e1 : (fun v => PowerSeries.constantCoeff (sclV (fun k => PowerSeries.C (u k))
      (fun v => PowerSeries.C (x v)) v)) = sclE u x := by
    funext v
    cases v with
    | e k c => simp [sclV, sclE]
    | x i => exact PowerSeries.constantCoeff_C _
    | y j => exact PowerSeries.constantCoeff_C _
    | z j => exact PowerSeries.constantCoeff_C _
  rw [e1] at h2
  simp only [map_pow, PowerSeries.constantCoeff_C] at h2
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact h2

/-! ### The analytic formal point -/

/-- The analytic version of `phPt (exp (liftT y)) (liftT w) cs`. -/
def PhiV (Ls : Fin m → PeriodPair) (cs : Fin m → LC) (y w : TanV d0 d1 m r) :
    Var (d0 + r) d1 m → ℂ → ℂ
  | .x i => fun c => Fin.append y.1 y.2.2.2 i + Fin.append w.1 w.2.2.2 i * c
  | .y j => fun c => Complex.exp (y.2.1 j) * Complex.exp (w.2.1 j * c)
  | .z j => fun c => Complex.exp (-y.2.1 j) * Complex.exp (-w.2.1 j * c)
  | .e k i => fun c => nlawc (cs k) (Ls k).g₂ (Ls k).g₃ (repV (expV (Ls k) (y.2.2.1 k, 0)))
      (FVb (Ls k) (c * w.2.2.1 k) (c * 0)) i

theorem analyticAt_PhiV (Ls : Fin m → PeriodPair) (cs : Fin m → LC) (y w : TanV d0 d1 m r)
    (v : Var (d0 + r) d1 m) : AnalyticAt ℂ (PhiV Ls cs y w v) 0 := by
  cases v with
  | x i => exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  | y j => exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)
  | z j => exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)
  | e k i =>
    have := LSG.ME.analyticAt_eval (f := fun l c => FVb (Ls k) (c * w.2.2.1 k) (c * 0) l)
      (fun l => analyticAt_FVb_ray (Ls k) _ 0 l)
      (lawPoly (cs k) (Ls k).g₂ (Ls k).g₃ (repV (expV (Ls k) (y.2.2.1 k, 0))) i)
    simp only [eval_lawPoly] at this
    exact this

theorem tps_lin (A B : ℂ) :
    tps (fun c => A + B * c) = PowerSeries.C A + PowerSeries.C B * PowerSeries.X := by
  ext j
  rw [coeff_tps, LSG.Aux.tco_lin]
  rcases j with _ | _ | j <;> simp

theorem tps_mul_exp (A B : ℂ) :
    tps (fun c => A * Complex.exp (B * c)) =
      PowerSeries.C A * PowerSeries.rescale B (PowerSeries.exp ℂ) := by
  ext j
  rw [coeff_tps, LSG.Aux.tco_const_mul, LSG.Aux.tco_cexp, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- **`tps ∘ PhiV` is the formal point `phPt`.** -/
theorem tps_PhiV (Ls : Fin m → PeriodPair) (cs : Fin m → LC) (y w : TanV d0 d1 m r) :
    (fun v => tps (PhiV Ls cs y w v)) =
      phPt Ls (expGV Ls (liftT y)) (toLie (liftT w)) cs := by
  funext v
  cases v with
  | x i =>
    simp only [PhiV, phPt, ExpV, tps_lin]
    rfl
  | y j =>
    simp only [PhiV, phPt, ExpV, tps_mul_exp]
    simp [expGV, GPtV.ym, LSG.ME.expU]
  | z j =>
    simp only [PhiV, phPt, ExpV, tps_mul_exp]
    simp [expGV, GPtV.ym, LSG.ME.expU, Complex.exp_neg]
  | e k i =>
    simp only [PhiV, phPt]
    rw [tps_law _ _ _ _ (fun l c => FVb (Ls k) (c * w.2.2.1 k) (c * 0) l)
      (fun l => analyticAt_FVb_ray (Ls k) _ 0 l)]
    rw [tps_FVb_ray]
    rfl

/-! ### Vanishing of low derivatives of a product -/

theorem iteratedDeriv_mul_eq_zero {u f : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hf : AnalyticAt ℂ f 0)
    {T : ℕ} (h : ∀ j < T, iteratedDeriv j f 0 = 0) : ∀ j < T, iteratedDeriv j (u * f) 0 = 0 := by
  intro j hj
  rw [iteratedDeriv_mul hu.contDiffAt hf.contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h (j - i) (lt_of_le_of_lt (Nat.sub_le j i) hj), mul_zero]

/-! ### The bridge -/

/-- **Analytic vanishing of `PsiV` along `W` gives the formal order of `PpolyV` along `liftT W`.**
-/
theorem ordGt_of_vanishAlongV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (W : Submodule ℂ (TanV d0 d1 m r)) {T : ℝ}
    {y : TanV d0 d1 m r} (hv : LSG.W88.VanishAlong (PsiV Ls M μs p) W T y) {n : ℕ}
    (hn : (n : ℝ) < T) :
    OrdGt Ls ((W.map liftT).map
        (toLie : TanG (d0 + r) d1 m ≃ₗ[ℂ] LieV ℂ (d0 + r) d1 m).toLinearMap)
      (PpolyV M μs p) n (expGV Ls (liftT y)) := by
  intro w' hw' cs
  obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hw'
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hw₁
  choose κ hκan hκ using fun k => exists_law_unit (Ls k) (cs k) (y.2.2.1 k) (w.2.2.1 k)
  set Q := PpolyV M μs p
  set f : ℂ → ℂ := fun c => eval (fun v => PhiV Ls cs y w v c) Q with hf
  set u : ℂ → ℂ := fun c => ∏ k, κ k c ^ D with hu
  set g : ℂ → ℂ := fun c => PsiV Ls M μs p (y + c • w) with hg
  have hfan : AnalyticAt ℂ f 0 := LSG.ME.analyticAt_eval (analyticAt_PhiV Ls cs y w) Q
  have huan : AnalyticAt ℂ u 0 := Finset.analyticAt_fun_prod _ fun k _ => (hκan k).pow D
  have hgan : AnalyticAt ℂ g 0 := LSG.AuxV.analyticAt_PsiV_line Ls M μs p y w
  -- `f = u · g` near `0`
  have hfug : f =ᶠ[𝓝 0] u * g := by
    filter_upwards [eventually_all.mpr hκ] with c hc
    have hpt : (fun v => PhiV Ls cs y w v c) = sclE (fun k => κ k c) (ptV Ls (y + c • w)) := by
      funext v
      cases v with
      | x i =>
        simp only [PhiV, sclE, ptV]
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp <;> ring
      | y j =>
        simp only [PhiV, sclE, ptV, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Complex.exp_add]; ring_nf
      | z j =>
        simp only [PhiV, sclE, ptV, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [neg_add, Complex.exp_add]; ring_nf
      | e k i =>
        simp only [PhiV, sclE, ptV]
        rw [hc k]
        simp
    change eval (fun v => PhiV Ls cs y w v c) Q = (∏ k, κ k c ^ D) * PsiV Ls M μs p (y + c • w)
    rw [hpt, eval_sclE (isHomV_PpolyV M μs p), eval_PpolyV]
  have hzero : ∀ j < n + 1, iteratedDeriv j f 0 = 0 := by
    intro j hj
    rw [(hfug.iteratedDeriv j).eq_of_nhds]
    refine iteratedDeriv_mul_eq_zero huan hgan (fun i hi => ?_) j hj
    refine hv w hw i (lt_of_le_of_lt ?_ hn)
    exact_mod_cast Nat.lt_succ_iff.mp hi
  intro i hi
  change PowerSeries.coeff i (aeval (phPt Ls (expGV Ls (liftT y)) (toLie (liftT w)) cs) Q) = 0
  rw [← tps_PhiV, ← tps_eval _ (analyticAt_PhiV Ls cs y w), coeff_tps]
  change iteratedDeriv i f 0 / _ = 0
  rw [hzero i (Nat.lt_succ_of_le hi), zero_div]

end LSG.W88
