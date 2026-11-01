import Mathlib
import LSG.ME.SubgroupLift
import LSG.ME.SubgroupDhat
import LSG.ME.SubgroupExpSurj

/-!
# Zariski tangent space = analytic Lie algebra (STAGE2 §5, item 4; PLAN R1 (c))

For a Zariski-closed subgroup `H ⊆ G(ℂ)`, the **Zariski tangent space at the identity**
`TZ H = {w | (D_w P)(0) = 0 for all P ∈ vanish H}` (`D_w` the chart derivation of `LSG.ME.Deriv` with
the canonical charts at `0`) equals the analytic Lie algebra `lieAlg H = linPart (exp⁻¹ H)`
(**`mem_TZ_iff`**).

Proof of `TZ ⊆ lieAlg` (the direction needed for Wüstholz's transversal functions):
1. (**`eval_Dhat_lift_eq_zero`**, first order) for `P ∈ vanish H` multihomogeneous and
   `p ∈ exp⁻¹ H` with `V ≠ 0` at `exp p`, the derivative of `P` along `c ↦ exp(p + c w)` (in a
   `V`-normalised lift) vanishes: compare with the translate `τ_g P ∈ vanish H` (`g = exp p`) along
   `c ↦ exp(c w)`, whose derivative at `0` vanishes because `w ∈ TZ H`; the two lifts differ by an
   analytic factor that is nonzero at `0`.
2. (**`Dhat_mem_homogVanish`**) hence `D̂_w` maps the multihomogeneous part of `vanish H` to itself
   (surjectivity of `exp`; at points with some `V_k = 0`, Euler's identity).
3. (**`TZ_subset_lieAlg`**) along `c ↦ exp(c w)` the `n`-th derivative of `P` is `D̂_w^n P`, which
   vanishes at `0`; so `P(exp(c w)) ≡ 0` near `0` (infinite analytic order), for all `P`
   simultaneously on a fixed disc (identity theorem), so `c w ∈ exp⁻¹ H` for small, hence all, `c`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.W88 (Tan)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

variable (Ls) in
/-- **The Zariski tangent space at the identity.** -/
def TZ (H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) : Set (Tan d₀ d₁ m) :=
  {w | ∀ P ∈ vanish H, eval (coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1)
    (Dw (g2L Ls) (g3L Ls) (chartAt (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) w P) = 0}

theorem mem_TZ {w : Tan d₀ d₁ m} : w ∈ TZ Ls H ↔ ∀ P ∈ vanish H,
    eval (coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1)
      (Dw (g2L Ls) (g3L Ls) (chartAt (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) w P) = 0 := Iff.rfl

theorem chartAt_zero : chartAt (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) = fun _ => 1 := by
  funext k; rfl

variable (Ls) in
theorem expG_zero : expG (d₀ := d₀) (d₁ := d₁) Ls 0 = 0 := (expGHom Ls).map_zero

/-- The properties of a family of `V`-normalised lifts on `U`. -/
def IsVLift (Ls : Fin m → PeriodPair) (U : Fin m → Set ℂ) (F : Fin m → ℂ → Fin 3 → ℂ) : Prop :=
  (∀ k, IsOpen (U k)) ∧ (∀ k i, AnalyticOnNhd ℂ (fun z => F k z i) (U k)) ∧
    ∀ k, ∀ z ∈ U k, F k z 1 = 1 ∧
      (∃ c : ℂ, c ≠ 0 ∧ F k z = c • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) z)) ∧
      ∀ i, HasDerivAt (fun z => F k z i) (chartVf (g2L Ls k) (g3L Ls k) (F k z) i) z

variable (Ls) in
theorem exists_VLifts (z : Fin m → ℂ)
    (hz : ∀ k, z k ∈ (Ls k).lattice ∨ (Ls k).derivWeierstrassP (z k) ≠ 0) :
    ∃ U F, IsVLift Ls U F ∧ ∀ k, z k ∈ U k := by
  choose U hU hzU F hF hFe using fun k => exists_VLift (Ls k) (z k) (hz k)
  exact ⟨U, F, ⟨hU, hF, hFe⟩, hzU⟩

theorem IsVLift.liftX_eq {U : Fin m → Set ℂ} {F : Fin m → ℂ → Fin 3 → ℂ} (hF : IsVLift Ls U F)
    {p : Tan d₀ d₁ m} (hp : ∀ k, p.2.2 k ∈ U k) :
    ∃ lam, liftX F p = coords (expG Ls p) lam :=
  LSG.ME.liftX_eq Ls fun k => (hF.2.2 k _ (hp k)).2.1

theorem IsVLift.V_eq {U : Fin m → Set ℂ} {F : Fin m → ℂ → Fin 3 → ℂ} (hF : IsVLift Ls U F)
    {p : Tan d₀ d₁ m} (hp : ∀ k, p.2.2 k ∈ U k) (k : Fin m) : liftX F p (.e k 1) = 1 :=
  (hF.2.2 k _ (hp k)).1

/-! ### The derivative along a line -/

/-- **Derivative along a line** in a `V`-normalised lift: `D̂_w`. -/
theorem hasDerivAt_line {U : Fin m → Set ℂ} {F : Fin m → ℂ → Fin 3 → ℂ} (hF : IsVLift Ls U F)
    (q w : Tan d₀ d₁ m) (c₀ : ℂ) (hc : ∀ k, (q + c₀ • w).2.2 k ∈ U k)
    (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    HasDerivAt (fun c : ℂ => eval (liftX F (q + c • w)) P)
      (eval (liftX F (q + c₀ • w)) (Dhat (g2L Ls) (g3L Ls) w P)) c₀ := by
  classical
  have hV1 : ∀ k, liftX F (q + c₀ • w) (.e k 1) = 1 := hF.V_eq hc
  have key := hasDerivAt_eval (c₀ := c₀) (Y := fun c => liftX F (q + c • w))
    (Y' := fun v => eval (liftX F (q + c₀ • w)) (dhat (g2L Ls) (g3L Ls) w v)) ?_ P
  · refine key.congr_deriv ?_
    rw [Dhat, map_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [map_mul, mul_comm]
  · intro v
    have hv : eval (liftX F (q + c₀ • w)) (dhat (g2L Ls) (g3L Ls) w v) =
        eval (liftX F (q + c₀ • w)) (dval (g2L Ls) (g3L Ls) (fun _ => 1) w v) := by
      simp only [dhat, map_mul, eval_Vfac_of_V hV1, one_mul]
    rw [hv]
    have hline : ∀ a b : ℂ, HasDerivAt (fun c : ℂ => a + c * b) b c₀ := fun a b => by
      simpa using ((hasDerivAt_id c₀).mul_const b).const_add a
    cases v with
    | x i =>
      show HasDerivAt (fun c : ℂ => q.1 i + c * w.1 i) _ c₀
      simpa [dval] using hline (q.1 i) (w.1 i)
    | y j =>
      show HasDerivAt (fun c : ℂ => Complex.exp (q.2.1 j + c * w.2.1 j)) _ c₀
      refine (hline _ _).cexp.congr_deriv ?_
      simp [dval, liftX, mul_comm]
    | z j =>
      show HasDerivAt (fun c : ℂ => Complex.exp (-(q.2.1 j + c * w.2.1 j))) _ c₀
      refine (hline _ _).neg.cexp.congr_deriv ?_
      simp [dval, liftX, mul_comm]
    | e k i =>
      show HasDerivAt (fun c : ℂ => F k (q.2.2 k + c * w.2.2 k) i) _ c₀
      have h1 := (hF.2.2 k _ (hc k)).2.2 i
      refine (HasDerivAt.comp (h₂ := fun z => F k z i) c₀ h1 (hline _ _)).congr_deriv ?_
      simp only [dval, map_mul, eval_C, eval_chartPoly_one]
      rw [mul_comm]
      rfl

/-! ### Two lifts of the same point -/

theorem coordsZ_eq_scale (G : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) (ν : Fin m → ℂ) (lam : Fin m → ℂˣ)
    (h1 : ∀ k, coords G lam (.e k 1) = 1) :
    coordsZ G ν = fun v => (∏ k, coordsZ G ν (.e k 1) ^ wV v k) * coords G lam v := by
  funext v
  cases v with
  | x i => simp [coords, wV]
  | y j => simp [coords, wV]
  | z j => simp [coords, wV]
  | e k c =>
    have := h1 k
    simp only [coords, coordsZ_e] at this ⊢
    simp only [wV, Pi.single_apply, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
      Finset.mem_univ, ite_true, coordsZ_e]
    linear_combination (-(ν k * rep (G.2.2 k) c)) * this

/-! ### First order -/

/-- **First-order step.** -/
theorem eval_Dhat_lift_eq_zero (hH : IsSubgroupG H) {w : Tan d₀ d₁ m} (hw : w ∈ TZ Ls H)
    {p : Tan d₀ d₁ m} (hp : expG Ls p ∈ H) {U : Fin m → Set ℂ} {F : Fin m → ℂ → Fin 3 → ℂ}
    (hF : IsVLift Ls U F) (hpU : ∀ k, p.2.2 k ∈ U k) {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ homogVanish H) : eval (liftX F p) (Dhat (g2L Ls) (g3L Ls) w P) = 0 := by
  classical
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hΔ := discr_g2L Ls
  obtain ⟨d, hd⟩ := hP.2
  obtain ⟨U₀, F₀, hF₀, h0U⟩ := exists_VLifts Ls (0 : Fin m → ℂ)
    (fun k => Or.inl (Ls k).lattice.zero_mem)
  set g := expG Ls p
  obtain ⟨ch, hch⟩ := exists_good h2 hΔ (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) g
  -- the lift at `0` is `coords 0 1`
  have hlift0 : liftX F₀ (0 : Tan d₀ d₁ m) = coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1 := by
    funext v
    cases v with
    | x i => rfl
    | y j => simp [liftX, coords]
    | z j => simp [liftX, coords]
    | e k c =>
      obtain ⟨hV, ⟨a, -, ha⟩, -⟩ := hF₀.2.2 k 0 (h0U k)
      have hO : rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) 0) = O := by
        rw [expE_zero]; rfl
      rw [ha, hO] at hV
      simp [O] at hV
      show F₀ k 0 c = _
      rw [ha, hO, hV]
      simp [coords, rep]
  have hV0 : ∀ k, coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1 (.e k 1) = 1 := fun k => by
    simp [coords, rep, O]
  -- the functions
  let ψ : ℂ → ℂ := fun c => eval (liftX F (p + c • w)) P
  let φ : ℂ → ℂ := fun c => eval (liftX F₀ (0 + c • w)) (τ (g2L Ls) (g3L Ls) g ch P)
  let R : MvPolynomial (Var d₀ d₁ m) ℂ :=
    ∏ k, translVar (g2L Ls) (g3L Ls) g ch (.e k 1) ^ d k
  let S : ℂ → ℂ := fun c => eval (liftX F₀ (0 + c • w)) R
  have hp0 : ∀ k, (p + (0 : ℂ) • w).2.2 k ∈ U k := by simpa using hpU
  have h00 : ∀ k, ((0 : Tan d₀ d₁ m) + (0 : ℂ) • w).2.2 k ∈ U₀ k := by simpa using h0U
  have hψ := hasDerivAt_line hF p w 0 hp0 P
  have hφ := hasDerivAt_line hF₀ 0 w 0 h00 (τ (g2L Ls) (g3L Ls) g ch P)
  have hS := hasDerivAt_line hF₀ 0 w 0 h00 R
  simp only [zero_smul, add_zero] at hψ hφ hS
  -- `φ'(0) = 0`
  have hφ0 : eval (liftX F₀ 0) (Dhat (g2L Ls) (g3L Ls) w (τ (g2L Ls) (g3L Ls) g ch P)) = 0 := by
    rw [hlift0, eval_Dhat_of_V _ _ hV0, ← chartAt_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)]
    exact mem_TZ.mp hw _ (transl_mem_vanish _ _ h2 hΔ hH hp ch hP.1)
  -- `ψ(0) = 0`
  have hψ0 : ψ 0 = 0 := by
    obtain ⟨lam, hlam⟩ := hF.liftX_eq (p := p + (0 : ℂ) • w) hp0
    simp only [ψ]
    rw [hlam]
    simpa using mem_vanish.mp hP.1 _ (by simpa using hp) lam
  -- `S(0) ≠ 0`
  have hS0 : S 0 ≠ 0 := by
    obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hch
    simp only [S, zero_smul, add_zero, hlift0, R, map_prod, map_pow]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
    have := hμ 1 (X (.e k 1))
    rw [τ, aeval_X] at this
    rw [this]
    simp only [eval_X, coords, coordsZ_e, zero_add, one_pow, one_mul]
    refine mul_ne_zero (Units.ne_zero _) ?_
    obtain ⟨hV, ⟨a, -, ha⟩, -⟩ := hF.2.2 k _ (hpU k)
    rw [ha] at hV
    intro h0
    simp only [Pi.smul_apply, smul_eq_mul] at hV
    rw [show g.2.2 k = expE (Ls k) (p.2.2 k) from rfl] at h0
    rw [h0, mul_zero] at hV
    exact zero_ne_one hV
  -- `φ = S ψ` near `0`
  have hN : ∀ᶠ c in 𝓝 (0 : ℂ), (∀ k, ((0 : Tan d₀ d₁ m) + c • w).2.2 k ∈ U₀ k) ∧
      ∀ k, (p + c • w).2.2 k ∈ U k := by
    refine (eventually_all.mpr fun k => ?_).and (eventually_all.mpr fun k => ?_)
    · have hc : Continuous fun c : ℂ => ((0 : Tan d₀ d₁ m) + c • w).2.2 k := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds ((hF₀.1 k).mem_nhds (by simpa using h0U k))
    · have hc : Continuous fun c : ℂ => (p + c • w).2.2 k := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds ((hF.1 k).mem_nhds (by simpa using hpU k))
  have heq : φ =ᶠ[𝓝 0] fun c => S c * ψ c := by
    filter_upwards [hN] with c ⟨hc₀, hc⟩
    obtain ⟨lam, hlam⟩ := hF₀.liftX_eq hc₀
    obtain ⟨lam', hlam'⟩ := hF.liftX_eq hc
    obtain ⟨ν, hν⟩ := eval_transl h2 hΔ g (expG Ls (0 + c • w)) ch lam
    have hsum : expG Ls (0 + c • w) + g = expG Ls (p + c • w) := by
      rw [← expG_add, zero_add, add_comm]
    have h1 : ∀ k, coords (expG Ls (p + c • w)) lam' (.e k 1) = 1 := fun k => by
      rw [← hlam']; exact hF.V_eq hc k
    have hφc : φ c = eval (coordsZ (expG Ls (p + c • w)) ν) P := by
      simp only [φ]; rw [hlam, hν, hsum]
    have hSc : S c = ∏ k, coordsZ (expG Ls (p + c • w)) ν (.e k 1) ^ d k := by
      simp only [S, R, map_prod, map_pow]
      refine Finset.prod_congr rfl fun k _ => ?_
      have := hν (X (.e k 1))
      rw [τ, aeval_X, hsum] at this
      rw [hlam, this, eval_X]
    have hψc : ψ c = eval (coords (expG Ls (p + c • w)) lam') P := by
      simp only [ψ]; rw [hlam']
    have hsc := coordsZ_eq_scale _ ν lam' h1
    rw [hφc, hSc, hψc]
    conv_lhs => rw [hsc]
    rw [eval_scale wV _ _ hd]
  -- conclude
  have hprod := hS.mul hψ
  have hφ' := hprod.congr_of_eventuallyEq heq
  have huniq := hφ.unique hφ'
  rw [hφ0] at huniq
  simp only [S, ψ, zero_smul, add_zero] at hψ0 hS0 huniq
  rw [hψ0, mul_zero, zero_add] at huniq
  exact (mul_eq_zero.mp huniq.symm).resolve_left hS0

/-- **`D̂_w` preserves the multihomogeneous part of `vanish H`** for `w ∈ TZ H`. -/
theorem Dhat_mem_homogVanish (hH : IsSubgroupG H) {w : Tan d₀ d₁ m} (hw : w ∈ TZ Ls H)
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ homogVanish H) :
    Dhat (g2L Ls) (g3L Ls) w P ∈ homogVanish H := by
  classical
  obtain ⟨d, hd⟩ := hP.2
  have hD := isWeightedHomogeneous_Dhat (g2L Ls) (g3L Ls) hd w
  refine ⟨mem_vanish.mpr fun g' hg' lam => ?_, _, hD⟩
  obtain ⟨p, rfl⟩ := expG_surjective Ls g'
  by_cases hV : ∀ k, p.2.2 k ∈ (Ls k).lattice ∨ (Ls k).derivWeierstrassP (p.2.2 k) ≠ 0
  · obtain ⟨U, F, hF, hpU⟩ := exists_VLifts Ls p.2.2 hV
    obtain ⟨lam₁, hlam₁⟩ := hF.liftX_eq hpU
    have := eval_Dhat_lift_eq_zero hH hw hg' hF hpU hP
    rw [hlam₁] at this
    exact (eval_coords_eq_zero_iff hD _ lam₁ lam).mp this
  · push Not at hV
    obtain ⟨k, hkL, hk'⟩ := hV
    have hrep : rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) (p.2.2 k)) =
        ![(Ls k).weierstrassP (p.2.2 k), (Ls k).derivWeierstrassP (p.2.2 k), 1] :=
      rep_expE_of_notMem (Ls k) hkL
    refine (eval_coords_eq_zero_iff hD _ 1 lam).mp ?_
    refine eval_Dhat_eq_zero_of_V (g2L Ls) (g3L Ls) hd (mem_vanish.mp hP.1 _ hg' 1)
      (k := k) ?_ ?_ ?_ w
    · simp [coords, expG, hrep, hk']
    · simp [coords, expG, hrep]
    · have := Fv_rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) two_ne_zero ((expG Ls p).2.2 k)
      simpa [coords] using this

/-! ### Iteration -/

/-- **`TZ H ⊆ lieAlg H`.** -/
theorem TZ_subset_lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) {w : Tan d₀ d₁ m}
    (hw : w ∈ TZ Ls H) : w ∈ lieAlg Ls hH hc := by
  classical
  obtain ⟨U₀, F₀, hF₀, h0U⟩ := exists_VLifts Ls (0 : Fin m → ℂ)
    (fun k => Or.inl (Ls k).lattice.zero_mem)
  let f : MvPolynomial (Var d₀ d₁ m) ℂ → ℂ → ℂ := fun Q c => eval (liftX F₀ (0 + c • w)) Q
  set B := {c : ℂ | ∀ k, ((0 : Tan d₀ d₁ m) + c • w).2.2 k ∈ U₀ k}
  have hBo : IsOpen B := by
    have : B = ⋂ k, (fun c : ℂ => ((0 : Tan d₀ d₁ m) + c • w).2.2 k) ⁻¹' U₀ k := by
      ext c; simp [B]
    rw [this]
    exact isOpen_iInter_of_finite fun k => (hF₀.1 k).preimage (by fun_prop)
  have h0B : (0 : ℂ) ∈ B := fun k => by simpa using h0U k
  have hderiv : ∀ Q, ∀ c ∈ B, HasDerivAt (f Q) (f (Dhat (g2L Ls) (g3L Ls) w Q) c) c :=
    fun Q c hc => hasDerivAt_line hF₀ 0 w c hc Q
  have hf0 : ∀ Q ∈ homogVanish H, f Q 0 = 0 := by
    intro Q hQ
    obtain ⟨lam, hlam⟩ := hF₀.liftX_eq (p := (0 : Tan d₀ d₁ m) + (0 : ℂ) • w) h0B
    simp only [f]
    rw [hlam]
    exact mem_vanish.mp hQ.1 _ (by simpa [expG_zero] using hH.zero_mem) lam
  have hiter : ∀ n, ∀ Q ∈ homogVanish H, iteratedDeriv n (f Q) 0 = 0 := by
    intro n
    induction n with
    | zero => intro Q hQ; simpa using hf0 Q hQ
    | succ n ih =>
      intro Q hQ
      rw [iteratedDeriv_succ']
      have hev : deriv (f Q) =ᶠ[𝓝 0] f (Dhat (g2L Ls) (g3L Ls) w Q) := by
        filter_upwards [hBo.mem_nhds h0B] with c hc
        exact (hderiv Q c hc).deriv
      rw [hev.iteratedDeriv_eq n]
      exact ih _ (Dhat_mem_homogVanish hH hw hQ)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBo 0 h0B
  have han : ∀ Q, AnalyticOnNhd ℂ (f Q) (Metric.ball 0 r) := by
    intro Q c hc
    refine analyticAt_eval (f := fun x c => liftX F₀ (0 + c • w) x) (fun x => ?_) Q
    cases x with
    | x i => show AnalyticAt ℂ (fun c : ℂ => 0 + c * w.1 i) c; fun_prop
    | y j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (0 + c * w.2.1 j)) c; fun_prop
    | z j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (-(0 + c * w.2.1 j))) c; fun_prop
    | e k i =>
      show AnalyticAt ℂ (fun c : ℂ => F₀ k (0 + c * w.2.2 k) i) c
      exact AnalyticAt.comp (g := fun z => F₀ k z i) (f := fun c : ℂ => 0 + c * w.2.2 k)
        (hF₀.2.1 k i _ (hball hc k)) (by fun_prop)
  have hzero : ∀ Q ∈ homogVanish H, ∀ c ∈ Metric.ball (0 : ℂ) r, f Q c = 0 := by
    intro Q hQ
    have htop : analyticOrderAt (f Q) 0 = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han Q 0 (Metric.mem_ball_self hr))).mpr
        fun i _ => hiter i Q hQ
    exact (han Q).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected (Metric.mem_ball_self hr) (analyticOrderAt_eq_top.mp htop)
  have hsmall : ∀ c ∈ Metric.ball (0 : ℂ) r, c • w ∈ Htil Ls hH := by
    intro c hcb
    have hcB := hball hcb
    have := (mem_iff_liftX hc fun k => (hF₀.2.2 k _ (hcB k)).2.1).mpr fun Q hQ => hzero Q hQ c hcb
    simpa [mem_Htil] using this
  refine mem_lieAlg.mpr fun c => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (‖c‖ / r)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (norm_nonneg c) hr.le) hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hmem : (c / N) • w ∈ Htil Ls hH := by
    refine hsmall _ ?_
    rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
    rwa [div_lt_iff₀ hr, mul_comm] at hN
  have := (Htil Ls hH).nsmul_mem hmem N
  rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_div_cancel₀ _ hN0] at this

/-- **`lieAlg H ⊆ TZ H`.** -/
theorem lieAlg_subset_TZ (hH : IsSubgroupG H) (hc : IsZClosed H) {w : Tan d₀ d₁ m}
    (hw : w ∈ lieAlg Ls hH hc) : w ∈ TZ Ls H := by
  classical
  obtain ⟨U₀, F₀, hF₀, h0U⟩ := exists_VLifts Ls (0 : Fin m → ℂ)
    (fun k => Or.inl (Ls k).lattice.zero_mem)
  refine mem_TZ.mpr fun P hP => ?_
  have h00 : ∀ k, ((0 : Tan d₀ d₁ m) + (0 : ℂ) • w).2.2 k ∈ U₀ k := by simpa using h0U
  have hd := hasDerivAt_line hF₀ 0 w 0 h00 P
  have hev : (fun c : ℂ => eval (liftX F₀ (0 + c • w)) P) =ᶠ[𝓝 0] fun _ => 0 := by
    have hN : ∀ᶠ c in 𝓝 (0 : ℂ), ∀ k, ((0 : Tan d₀ d₁ m) + c • w).2.2 k ∈ U₀ k := by
      refine eventually_all.mpr fun k => ?_
      have hc : Continuous fun c : ℂ => ((0 : Tan d₀ d₁ m) + c • w).2.2 k := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds ((hF₀.1 k).mem_nhds (by simpa using h0U k))
    filter_upwards [hN] with c hc
    obtain ⟨lam, hlam⟩ := hF₀.liftX_eq hc
    rw [hlam]
    exact mem_vanish.mp hP _ (by simpa using mem_Htil.mp (mem_lieAlg.mp hw c)) lam
  have h0 := (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev
  have := hd.unique h0
  have hlift0 : liftX F₀ ((0 : Tan d₀ d₁ m) + (0 : ℂ) • w) =
      coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1 := by
    funext v
    cases v with
    | x i => simp [liftX, coords]
    | y j => simp [liftX, coords]
    | z j => simp [liftX, coords]
    | e k c =>
      obtain ⟨hV, ⟨a, -, ha⟩, -⟩ := hF₀.2.2 k 0 (h0U k)
      have hO : rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) 0) = O := by
        rw [expE_zero]; rfl
      rw [ha, hO] at hV
      simp [O] at hV
      simp only [liftX, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        mul_zero, add_zero, zero_smul]
      show F₀ k 0 c = _
      rw [ha, hO, hV]
      simp [coords, rep]
  have hV0 : ∀ k, coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1 (.e k 1) = 1 := fun k => by
    simp [coords, rep, O]
  rw [hlift0, eval_Dhat_of_V _ _ hV0] at this
  rw [chartAt_zero]
  exact this

/-- **Zariski tangent space = analytic Lie algebra** (PLAN R1 (c)). -/
theorem mem_TZ_iff (hH : IsSubgroupG H) (hc : IsZClosed H) {w : Tan d₀ d₁ m} :
    w ∈ TZ Ls H ↔ w ∈ lieAlg Ls hH hc :=
  ⟨TZ_subset_lieAlg hH hc, lieAlg_subset_TZ hH hc⟩

end LSG.ME
