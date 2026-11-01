import Mathlib
import LSG.ME.SubgroupProj
import LSG.Weierstrass.Dictionary
import LSG.Subgroups.Torus
import LSG.W88.Statement

/-!
# The analytic Lie algebra of a Zariski-closed subgroup (STAGE2 §5, item 3; `K = ℂ`)

Curves from period pairs: `g₂ k = (Ls k).g₂`, `g₃ k = (Ls k).g₃`. The exponential map
`expG : Tan → G`, `(a, b, z) ↦ (a, e^b, expE(z_k))`, is an additive homomorphism (`expGHom`).
For a Zariski-closed subgroup `H ⊆ G`, `Htil H = exp⁻¹(H)`:

* **`isClosed_Htil`**: `Htil H` is closed (local analytic lifts of `expE` to the cone: `℘, ℘'` off
  the lattice, `(z − l)³ · (℘, ℘', 1)` near a lattice point `l`; then `homogVanish`);
* **`per_le_Htil`**: `Per Ls ≤ Htil H`;
* **`smul_mem_Htil`**: real lines in `Htil H` are complex lines (identity theorem along
  `c ↦ c • v`, a clopen argument in `ℂ`); hence `lieAlg H`, the linear part, is a `ℂ`-subspace
  (`restrictScalars_lieAlg`);
* **`exists_abelianTangent_Htil`**: `Htil H ∩ (0 × 0 × ℂ^m)` has an abelian tangent space `t`
  (`IsAbelianTangent`), `z ∈ t ↔ (0, 0, z) ∈ lieAlg H`, with finitely many cosets of `t + Λ`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.W88 (Tan Per IsAbelianTangent)

namespace LSG.ME

variable {d₀ d₁ m : ℕ}

/-! ### Generic continuity / analyticity of polynomial evaluation -/

theorem continuousAt_eval {X σ : Type*} [TopologicalSpace X] {f : σ → X → ℂ} {x : X}
    (hf : ∀ v, ContinuousAt (f v) x) (Q : MvPolynomial σ ℂ) :
    ContinuousAt (fun y => eval (fun v => f v y) Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact continuousAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (hf v)

theorem analyticAt_eval {σ : Type*} {f : σ → ℂ → ℂ} {c : ℂ} (hf : ∀ v, AnalyticAt ℂ (f v) c)
    (Q : MvPolynomial σ ℂ) : AnalyticAt ℂ (fun y => eval (fun v => f v y) Q) c := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (hf v)

/-! ### Local lifts of `expE` to the cone -/

/-- **Local analytic lifts.** Near every `z₀`, `expE` lifts to an analytic map to the cone. -/
theorem exists_coneLift (L : PeriodPair) (z₀ : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ F : ℂ → Fin 3 → ℂ,
      (∀ i, AnalyticOnNhd ℂ (fun z => F z i) U) ∧
      ∀ z ∈ U, ∃ c : ℂ, c ≠ 0 ∧ F z = c • rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z) := by
  by_cases h₀ : z₀ ∈ L.lattice
  · -- near a lattice point: `(z − z₀)³ · (℘, ℘', 1)`
    let l₀ : L.lattice := ⟨z₀, h₀⟩
    let F : ℂ → Fin 3 → ℂ := fun z =>
      ![(z - z₀) + (z - z₀) ^ 3 * (L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2),
        (z - z₀) ^ 3 * L.derivWeierstrassPExcept z₀ z - 2, (z - z₀) ^ 3]
    refine ⟨(L.lattice \ {z₀})ᶜ, L.isOpen_compl_lattice_sdiff, by simp, F, fun i => ?_,
      fun z hz => ?_⟩
    · have h1 := L.analyticOnNhd_weierstrassPExcept z₀
      have h2 := L.analyticOnNhd_derivWeierstrassPExcept z₀
      have hid : AnalyticOnNhd ℂ (fun z : ℂ => z - z₀) (L.lattice \ {z₀})ᶜ :=
        fun z _ => analyticAt_id.sub analyticAt_const
      fin_cases i
      · exact hid.add ((hid.pow 3).mul (h1.sub fun _ _ => analyticAt_const))
      · exact ((hid.pow 3).mul h2).sub fun _ _ => analyticAt_const
      · exact hid.pow 3
    · by_cases hz₀ : z = z₀
      · subst hz₀
        refine ⟨-2, by norm_num, ?_⟩
        rw [expE_of_mem L h₀]
        funext i
        fin_cases i <;> simp [F, rep, O]
      · have hzL : z ∉ L.lattice := fun h => hz ⟨h, hz₀⟩
        have hw : z - z₀ ≠ 0 := sub_ne_zero.mpr hz₀
        refine ⟨(z - z₀) ^ 3, pow_ne_zero 3 hw, ?_⟩
        rw [expE_of_notMem L hzL]
        have e1 := L.weierstrassPExcept_def l₀ z
        have e2 := L.derivWeierstrassPExcept_def l₀ z
        simp only [l₀] at e1 e2
        funext i
        fin_cases i
        · simp only [F, rep, e1]
          simp
          field_simp
          ring
        · simp only [F, rep, e2]
          simp
          field_simp
          ring
        · simp [F, rep]
  · -- off the lattice: `(℘, ℘', 1)`
    refine ⟨(L.lattice : Set ℂ)ᶜ, L.isClosed_lattice.isOpen_compl, h₀,
      fun z => ![L.weierstrassP z, L.derivWeierstrassP z, 1], fun i => ?_, fun z hz => ?_⟩
    · fin_cases i
      · exact L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl
      · exact L.analyticOnNhd_derivWeierstrassP
      · exact fun _ _ => analyticAt_const
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [expE_of_notMem L hz]
      funext i
      fin_cases i <;> simp [rep, mul_div_cancel₀]

/-! ### The exponential map -/

variable (Ls : Fin m → PeriodPair)

/-- `g₂` of the curves. -/
noncomputable def g2L : Fin m → ℂ := fun k => (Ls k).g₂
/-- `g₃` of the curves. -/
noncomputable def g3L : Fin m → ℂ := fun k => (Ls k).g₃

theorem discr_g2L (k : Fin m) : g2L Ls k ^ 3 - 27 * g3L Ls k ^ 2 ≠ 0 := discr_ne_zero (Ls k)

/-- `e^b` as a unit. -/
noncomputable def expU (b : ℂ) : ℂˣ := Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)

/-- **The exponential map** `Tan → G`. -/
noncomputable def expG (p : Tan d₀ d₁ m) : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) :=
  (p.1, Additive.ofMul fun j => expU (p.2.1 j), fun k => expE (Ls k) (p.2.2 k))

theorem expG_add (p q : Tan d₀ d₁ m) : expG Ls (p + q) = expG Ls p + expG Ls q := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show Additive.ofMul _ = Additive.ofMul ((fun j => expU (p.2.1 j)) * fun j => expU (q.2.1 j))
    congr 1
    funext j
    exact Units.ext (by simp [expU, Complex.exp_add])
  · funext k
    exact expE_add (Ls k) _ _

/-- `expG` as an additive homomorphism. -/
noncomputable def expGHom : Tan d₀ d₁ m →+ GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) :=
  AddMonoidHom.mk' (expG Ls) (expG_add Ls)

@[simp] theorem expGHom_apply (p : Tan d₀ d₁ m) : expGHom Ls p = expG Ls p := rfl

/-- The lift of `expG` to the cone with chosen local lifts `F`. -/
noncomputable def liftX (F : Fin m → ℂ → Fin 3 → ℂ) (p : Tan d₀ d₁ m) : Var d₀ d₁ m → ℂ
  | .x i => p.1 i
  | .y j => Complex.exp (p.2.1 j)
  | .z j => Complex.exp (-p.2.1 j)
  | .e k c => F k (p.2.2 k) c

theorem liftX_eq {F : Fin m → ℂ → Fin 3 → ℂ} {p : Tan d₀ d₁ m}
    (hF : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ F k (p.2.2 k) = c • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k)
      (expE (Ls k) (p.2.2 k))) :
    ∃ lam, liftX F p = coords (expG Ls p) lam := by
  choose c hc0 hc using hF
  refine ⟨fun k => Units.mk0 (c k) (hc0 k), funext fun v => ?_⟩
  cases v with
  | x i => rfl
  | y j => rfl
  | z j => simp [liftX, coords, expG, GPt.ym, expU, Complex.exp_neg]
  | e k i => simp [liftX, coords, expG, hc k]

/-! ### The preimage of a Zariski-closed subgroup -/

variable {Ls} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-- A subgroup of `G` as an `AddSubgroup`. -/
noncomputable def IsSubgroupG.toAddSubgroup (hH : IsSubgroupG H) : AddSubgroup (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))
    where
  carrier := H
  add_mem' {a b} ha hb := hH.add_mem a ha b hb
  zero_mem' := hH.zero_mem
  neg_mem' {a} ha := hH.neg_mem a ha

variable (Ls) in
/-- **`exp⁻¹(H)`**. -/
noncomputable def Htil (hH : IsSubgroupG H) : AddSubgroup (Tan d₀ d₁ m) :=
  hH.toAddSubgroup.comap (expGHom Ls)

theorem mem_Htil {hH : IsSubgroupG H} {p : Tan d₀ d₁ m} : p ∈ Htil Ls hH ↔ expG Ls p ∈ H :=
  Iff.rfl

/-- On the domain of a local lift, membership in `H` is the vanishing of the multihomogeneous
equations at the lift. -/
theorem mem_iff_liftX (hc : IsZClosed H) {F : Fin m → ℂ → Fin 3 → ℂ} {p : Tan d₀ d₁ m}
    (hF : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ F k (p.2.2 k) = c • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k)
      (expE (Ls k) (p.2.2 k))) :
    expG Ls p ∈ H ↔ ∀ Q ∈ homogVanish H, eval (liftX F p) Q = 0 := by
  obtain ⟨lam, hlam⟩ := liftX_eq Ls hF
  rw [hlam]
  constructor
  · intro hp Q hQ; exact mem_vanish.mp hQ.1 _ hp lam
  · intro h
    rw [← zeros_homogVanish hc]
    intro Q hQ lam'
    obtain ⟨d, hd⟩ := hQ.2
    exact (eval_coords_eq_zero_iff hd _ lam lam').mp (h Q hQ)

/-- Local lifts at a point of `ℂ^m`. -/
theorem exists_lifts (z : Fin m → ℂ) :
    ∃ U : Fin m → Set ℂ, (∀ k, IsOpen (U k)) ∧ (∀ k, z k ∈ U k) ∧ ∃ F : Fin m → ℂ → Fin 3 → ℂ,
      (∀ k i, AnalyticOnNhd ℂ (fun w => F k w i) (U k)) ∧
      ∀ k, ∀ w ∈ U k, ∃ c : ℂ, c ≠ 0 ∧
        F k w = c • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) w) := by
  choose U hU hzU F hF hFe using fun k => exists_coneLift (Ls k) (z k)
  exact ⟨U, hU, hzU, F, hF, hFe⟩

/-- **`exp⁻¹(H)` is closed.** -/
theorem isClosed_Htil (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsClosed (Htil Ls hH : Set (Tan d₀ d₁ m)) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p₀ hp₀
  obtain ⟨U, hU, hzU, F, hF, hFe⟩ := exists_lifts (Ls := Ls) p₀.2.2
  have hnot : ¬ ∀ Q ∈ homogVanish H, eval (liftX F p₀) Q = 0 := fun h =>
    hp₀ ((mem_iff_liftX hc fun k => hFe k _ (hzU k)).mpr h)
  push Not at hnot
  obtain ⟨Q, hQ, hne⟩ := hnot
  have hcont : ContinuousAt (fun p : Tan d₀ d₁ m => eval (liftX F p) Q) p₀ := by
    refine continuousAt_eval (f := fun v p => liftX F p v) (fun v => ?_) Q
    cases v with
    | x i => exact ((continuous_apply i).comp continuous_fst).continuousAt
    | y j => exact (Complex.continuous_exp.comp
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd))).continuousAt
    | z j => exact (Complex.continuous_exp.comp
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).neg).continuousAt
    | e k i =>
      exact ContinuousAt.comp (f := fun p : Tan d₀ d₁ m => p.2.2 k) (g := fun w => F k w i)
        (hF k i _ (hzU k)).continuousAt (by fun_prop)
  have hU' : ∀ᶠ p in 𝓝 p₀, ∀ k, p.2.2 k ∈ U k := by
    refine eventually_all.mpr fun k => ?_
    exact ((continuous_apply k).comp (continuous_snd.comp continuous_snd)).continuousAt.preimage_mem_nhds
      ((hU k).mem_nhds (hzU k))
  filter_upwards [hcont.eventually_ne hne, hU'] with p hp hpU
  intro hmem
  exact hp ((mem_iff_liftX hc fun k => hFe k _ (hpU k)).mp hmem Q hQ)

/-- **`Per Ls ⊆ exp⁻¹(H)`.** -/
theorem per_le_Htil (hH : IsSubgroupG H) : Per Ls ≤ Htil Ls hH := by
  rintro p ⟨h1, h2, h3⟩
  rw [mem_Htil]
  have : expG Ls p = 0 := by
    refine Prod.ext h1 (Prod.ext ?_ ?_)
    · show Additive.ofMul _ = Additive.ofMul 1
      congr 1
      funext j
      obtain ⟨k, hk⟩ := h2 j
      refine Units.ext ?_
      simp only [expU, Units.val_mk0, Pi.one_apply, Units.val_one, hk]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * k = k * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    · funext k
      exact expE_of_mem (Ls k) (h3 k)
  rw [this]; exact hH.zero_mem

/-! ### Complex lines -/

/-- **Local step of the identity theorem.** -/
theorem eventually_of_frequently (hH : IsSubgroupG H) (hc : IsZClosed H) (v : Tan d₀ d₁ m)
    (c₀ : ℂ) (hfr : ∃ᶠ c in 𝓝[≠] c₀, c • v ∈ Htil Ls hH) : ∀ᶠ c in 𝓝 c₀, c • v ∈ Htil Ls hH := by
  obtain ⟨U, hU, hzU, F, hF, hFe⟩ := exists_lifts (Ls := Ls) (c₀ • v).2.2
  set W := {c : ℂ | ∀ k, c * v.2.2 k ∈ U k}
  have hW : IsOpen W := by
    have : W = ⋂ k, (fun c : ℂ => c * v.2.2 k) ⁻¹' U k := by ext c; simp [W]
    rw [this]
    exact isOpen_iInter_of_finite fun k => (hU k).preimage (by fun_prop)
  have hc₀W : c₀ ∈ W := fun k => by simpa using hzU k
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW c₀ hc₀W
  have hsnd : ∀ c : ℂ, (c • v).2.2 = fun k => c * v.2.2 k := fun c => by
    funext k; simp
  have hlift : ∀ c ∈ Metric.ball c₀ r, ∀ k, ∃ a : ℂ, a ≠ 0 ∧
      F k ((c • v).2.2 k) = a • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) ((c • v).2.2 k))
      := fun c hc k => hFe k _ (by rw [hsnd]; exact hball hc k)
  have hzero : ∀ Q ∈ homogVanish H, ∀ c ∈ Metric.ball c₀ r, eval (liftX F (c • v)) Q = 0 := by
    intro Q hQ
    have han : AnalyticOnNhd ℂ (fun c : ℂ => eval (liftX F (c • v)) Q) (Metric.ball c₀ r) := by
      intro c hc
      refine analyticAt_eval (f := fun x c => liftX F (c • v) x) (fun x => ?_) Q
      cases x with
      | x i => show AnalyticAt ℂ (fun c : ℂ => c * v.1 i) c; fun_prop
      | y j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (c * v.2.1 j)) c; fun_prop
      | z j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (-(c * v.2.1 j))) c; fun_prop
      | e k i =>
        have h1 := hF k i _ (hball hc k)
        show AnalyticAt ℂ (fun c : ℂ => F k (c * v.2.2 k) i) c
        exact AnalyticAt.comp (g := fun w => F k w i) (f := fun c : ℂ => c * v.2.2 k) h1
          (by fun_prop)
    refine han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball c₀ r).isPreconnected
      (Metric.mem_ball_self hr) ?_
    have hev : ∀ᶠ c in 𝓝[≠] c₀, c ∈ Metric.ball c₀ r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds c₀ hr)
    refine (hfr.and_eventually hev).mono fun c ⟨hcH, hcB⟩ => ?_
    exact (mem_iff_liftX hc (hlift c hcB)).mp hcH Q hQ
  filter_upwards [Metric.ball_mem_nhds c₀ hr] with c hcB
  exact (mem_iff_liftX hc (hlift c hcB)).mpr fun Q hQ => hzero Q hQ c hcB

/-- **Real lines in `exp⁻¹(H)` are complex lines.** -/
theorem smul_mem_Htil (hH : IsSubgroupG H) (hc : IsZClosed H) (v : Tan d₀ d₁ m)
    (hv : ∀ s : ℝ, s • v ∈ Htil Ls hH) (c : ℂ) : c • v ∈ Htil Ls hH := by
  set Z := {c : ℂ | c • v ∈ Htil Ls hH}
  set A := {c : ℂ | ∀ᶠ c' in 𝓝 c, c' ∈ Z}
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun c₀ hc₀ => ?_
    by_cases hA : c₀ ∈ A
    · exact hA
    refine eventually_of_frequently hH hc v c₀ ?_
    rw [Filter.frequently_iff]
    intro W hW
    obtain ⟨W', hW'o, hc₀W', hsub⟩ := mem_nhdsWithin.mp hW
    obtain ⟨c₁, hc₁W, hc₁A⟩ := mem_closure_iff.mp hc₀ W' hW'o hc₀W'
    have hne : c₁ ≠ c₀ := fun h => hA (h ▸ hc₁A)
    exact ⟨c₁, hsub ⟨hc₁W, hne⟩, hc₁A.self_of_nhds⟩
  have h0 : (0 : ℂ) ∈ A := by
    refine eventually_of_frequently hH hc v 0 ?_
    have hreal : ∀ s : ℝ, ((s : ℂ) • v) ∈ Htil Ls hH := fun s => by
      rw [Complex.coe_smul]; exact hv s
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun s hs => by simpa using hs)
    exact ht.frequently (Frequently.of_forall fun s => hreal s)
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨0, h0⟩
  have hcA : c ∈ A := huniv ▸ mem_univ c
  exact hcA.self_of_nhds

variable (Ls) in
/-- **The analytic Lie algebra** `linPart (exp⁻¹ H)`, as a complex subspace. -/
noncomputable def lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) : Submodule ℂ (Tan d₀ d₁ m) where
  carrier := LSG.Subgroups.linPart (Htil Ls hH)
  add_mem' := (LSG.Subgroups.linPart (Htil Ls hH)).add_mem
  zero_mem' := (LSG.Subgroups.linPart (Htil Ls hH)).zero_mem
  smul_mem' a v hv := fun s => by
    rw [← smul_assoc]
    exact smul_mem_Htil hH hc v hv _

theorem restrictScalars_lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (lieAlg Ls hH hc).restrictScalars ℝ = LSG.Subgroups.linPart (Htil Ls hH) :=
  Submodule.ext fun _ => Iff.rfl

theorem mem_lieAlg {hH : IsSubgroupG H} {hc : IsZClosed H} {v : Tan d₀ d₁ m} :
    v ∈ lieAlg Ls hH hc ↔ ∀ c : ℂ, c • v ∈ Htil Ls hH := by
  constructor
  · intro hv c; exact smul_mem_Htil hH hc v hv c
  · intro hv s
    rw [← Complex.coe_smul]
    exact hv _

theorem lieAlg_le_Htil {hH : IsSubgroupG H} {hc : IsZClosed H} {v : Tan d₀ d₁ m}
    (hv : v ∈ lieAlg Ls hH hc) : v ∈ Htil Ls hH := by
  simpa using mem_lieAlg.mp hv 1

/-! ### The abelian part -/

/-- `z ↦ (0, 0, z)`. -/
def inAb (z : Fin m → ℂ) : Tan d₀ d₁ m := (0, 0, z)

theorem inAb_smul (c : ℂ) (z : Fin m → ℂ) : inAb (d₀ := d₀) (d₁ := d₁) (c • z) = c • inAb z := by
  simp [inAb]

theorem inAb_real_smul (s : ℝ) (z : Fin m → ℂ) :
    inAb (d₀ := d₀) (d₁ := d₁) (s • z) = s • inAb z := by
  simp [inAb]

variable (Ls) in
/-- `exp⁻¹(H) ∩ (0 × 0 × ℂ^m)`, as a subgroup of `ℂ^m`. -/
noncomputable def Sab (hH : IsSubgroupG H) : AddSubgroup (Fin m → ℂ) where
  carrier := {z | inAb (d₀ := d₀) (d₁ := d₁) z ∈ Htil Ls hH}
  add_mem' {a b} ha hb := by
    have := (Htil Ls hH).add_mem ha hb
    simpa [inAb] using this
  zero_mem' := by
    show ((0, 0, 0) : Tan d₀ d₁ m) ∈ Htil Ls hH
    exact (Htil Ls hH).zero_mem
  neg_mem' {a} ha := by
    have := (Htil Ls hH).neg_mem ha
    simpa [inAb] using this

/-- **The abelian tangent space.** `exp⁻¹(H) ∩ (0 × 0 × ℂ^m)` has linear part an abelian tangent
space `t`, with `z ∈ t ↔ (0, 0, z) ∈ lieAlg H`, and is a finite union of cosets of `t + Λ`. -/
theorem exists_abelianTangent_Htil (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ∃ t : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls t ∧
      (∀ z, z ∈ t ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      ∃ F : Finset (Fin m → ℂ), (∀ f ∈ F, inAb (d₀ := d₀) (d₁ := d₁) f ∈ Htil Ls hH) ∧
        ∀ x, inAb (d₀ := d₀) (d₁ := d₁) x ∈ Htil Ls hH → ∃ f ∈ F, ∃ v ∈ t, ∃ l : Fin m → ℂ,
          (∀ j, l j ∈ (Ls j).lattice) ∧ x = f + v + l := by
  have hcl : IsClosed (Sab (d₀ := d₀) (d₁ := d₁) Ls hH : Set (Fin m → ℂ)) :=
    (isClosed_Htil hH hc).preimage (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hΛ : ∀ z : Fin m → ℂ, (∀ j, z j ∈ (Ls j).lattice) → z ∈ Sab (d₀ := d₀) (d₁ := d₁) Ls hH :=
    fun z hz => per_le_Htil hH ⟨rfl, fun i => ⟨0, by simp [inAb]⟩, hz⟩
  have hC : ∀ v, (∀ s : ℝ, s • v ∈ Sab (d₀ := d₀) (d₁ := d₁) Ls hH) →
      ∀ c : ℂ, c • v ∈ Sab (d₀ := d₀) (d₁ := d₁) Ls hH := by
    intro v hv c
    show inAb (c • v) ∈ Htil Ls hH
    rw [inAb_smul]
    exact smul_mem_Htil hH hc _ (fun s => by rw [← inAb_real_smul]; exact hv s) c
  obtain ⟨t, hab, hlin, F, hFS, hF⟩ := LSG.Subgroups.exists_abelianTangent Ls _ hcl hΛ hC
  refine ⟨t, hab, fun z => ?_, F, fun f hf => hFS hf, fun x hx => hF x hx⟩
  have : z ∈ t ↔ z ∈ LSG.Subgroups.linPart (Sab (d₀ := d₀) (d₁ := d₁) Ls hH) := by
    rw [← hlin]; rfl
  rw [this]
  show (∀ s : ℝ, inAb (s • z) ∈ Htil Ls hH) ↔ ∀ s : ℝ, s • inAb z ∈ Htil Ls hH
  simp only [inAb_real_smul]

end LSG.ME
