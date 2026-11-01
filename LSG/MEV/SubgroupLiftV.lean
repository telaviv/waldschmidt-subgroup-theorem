import Mathlib
import LSG.MEV.ChartDerivV
import LSG.MEV.SubgroupLie
import LSG.ME.SubgroupLift

/-!
# The `V`-normalised lift of `exp_{G̃}` and its derivative along lines

One block: `FVb L z w = ellN(z, w) / ellN(z, w)_V` (defined where `ellW L 2 z = σ³℘′ ≠ 0`, i.e.
`V ≠ 0` at `exp(z, w)`); off the lattice it is `(℘/℘′, 1, 1/℘′, (w − ζ)/℘′, (w − ζ) − 2℘²/℘′)`.
* **`hasDerivAt_FVb_line`**: `d/dc FVb(z + c a, w + c b) |₀ = bField g₂ g₃ a b (FVb z w)`.
  Off the lattice by direct computation (`℘′′ = 6℘² − g₂/2`, `℘′² = 4℘³ − g₂℘ − g₃`, `ζ′ = −℘`;
  `T₁ = W T₃ + 2U²`), at lattice points by continuity of the derivative of an analytic function.
* `FV Ls p`: the lift `liftV p (1/V)` of `expGV p` (all `V`-coordinates `1`); **`hasDerivAt_FV`**:
  `d/dc FV(p + c w)_v |_{c₀} = DV w (FV (p + c₀ w)) v`, hence (**`hasDerivAt_eval_FV`**)
  `d/dc Q(FV(p + c w)) = (D̂_w Q)(FV(p + c w))`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.AuxV (ellN)
open PeriodPair
open LSG.Aux (ellW)

namespace LSG.MEV

noncomputable section

theorem hasDerivAt_mul_self_zero {G : ℂ → ℂ} (b : ℂ) (hG : ContinuousAt G 0) :
    HasDerivAt (fun c => c * b * G c) (b * G 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have : ∀ᶠ c in 𝓝[≠] (0 : ℂ), b * G c = slope (fun c => c * b * G c) 0 c := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [slope_def_field]
    have hc' : c ≠ 0 := hc
    simp only [zero_mul, sub_zero]
    field_simp
  exact ((continuousAt_const.mul hG).tendsto.mono_left nhdsWithin_le_nhds).congr' this

/-! ### One block -/

section Block

variable (L : PeriodPair)

/-- The `V`-normalised lift of one block. -/
def FVb (z w : ℂ) : Fin 5 → ℂ := (ellW L 2 z)⁻¹ • ellN L z w

theorem bField_lin (g₂ g₃ a b : ℂ) (P : Fin 5 → ℂ) (i : Fin 5) :
    bField g₂ g₃ a b P i = a * bField g₂ g₃ 1 0 P i + b * bField g₂ g₃ 0 1 P i := by
  fin_cases i <;> simp [bField] <;> ring

/-- The fibre direction of `FVb`. -/
def FBb (z : ℂ) : Fin 5 → ℂ := (ellW L 2 z)⁻¹ • ![0, 0, 0, ellW L 0 z, ellW L 2 z]

theorem FVb_affine (z w w' : ℂ) : FVb L z w' = FVb L z w + (w' - w) • FBb L z := by
  funext i
  fin_cases i <;> simp [FVb, FBb, LSG.AuxV.ellN] <;> ring

theorem FVb_V {z : ℂ} (hz : ellW L 2 z ≠ 0) (w : ℂ) : FVb L z w 1 = 1 := by
  simp [FVb, LSG.AuxV.ellN, hz]

theorem differentiableAt_FVb {z : ℂ} (hz : ellW L 2 z ≠ 0) (w : ℂ) (i : Fin 5) :
    DifferentiableAt ℂ (fun z => FVb L z w i) z := by
  simp only [FVb, Pi.smul_apply, smul_eq_mul]
  exact (((LSG.Aux.differentiable_ellW L 2) z).inv hz).mul
    ((LSG.AuxV.differentiable_ellN_left L w i) z)

theorem FVb_off {z : ℂ} (hz : z ∉ L.lattice) (w : ℂ) :
    FVb L z w = (℘'[L] z)⁻¹ • ptAff (℘[L] z) (℘'[L] z) (w - zeta L z) := by
  rw [FVb, LSG.AuxV.ellN_eq_off L hz, (LSG.Aux.ellW_eq_off L hz).2, smul_smul]
  have hs : sigma L z ^ 3 ≠ 0 := pow_ne_zero _ (sigma_ne_zero L hz)
  have hs0 := sigma_ne_zero L hz
  by_cases hp : ℘'[L] z = 0
  · simp [hp]
  · congr 1; field_simp

/-- **The `z`-derivative off the lattice.** -/
theorem hasDerivAt_FVb_off {z : ℂ} (hz : z ∉ L.lattice) (hp : ℘'[L] z ≠ 0) (w : ℂ) (i : Fin 5) :
    HasDerivAt (fun z => FVb L z w i) (bField L.g₂ L.g₃ 1 0 (FVb L z w) i) z := by
  have hU : ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice ∧ ℘'[L] z' ≠ 0 :=
    Filter.Eventually.and
      (show ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice from L.isClosed_lattice.isOpen_compl.mem_nhds hz)
      ((L.analyticOnNhd_derivWeierstrassP z hz).continuousAt.eventually_ne hp)
  have hFV : ∀ᶠ z' in 𝓝 z, FVb L z' w =
      ![℘[L] z' / ℘'[L] z', 1, 1 / ℘'[L] z', (w - zeta L z') / ℘'[L] z',
        (w - zeta L z') - 2 * ℘[L] z' ^ 2 / ℘'[L] z'] := hU.mono fun z' ⟨h1, h2⟩ => by
    rw [FVb_off L h1]
    funext j
    fin_cases j <;> simp [ptAff] <;> field_simp
  have h0 := LSG.ME.hasDerivAt_Faff L hz hp 0
  have h2 := LSG.ME.hasDerivAt_Faff L hz hp 2
  have hζ := hasDerivAt_zeta L hz
  have hP := hasDerivAt_weierstrassP L hz
  have hP' := hasDerivAt_derivWeierstrassP L hz
  have hsq := L.derivWeierstrassP_sq z hz
  have e4 : HasDerivAt (fun z => (w - zeta L z) - 2 * ℘[L] z ^ 2 / ℘'[L] z)
      (2 * L.g₂ * (℘[L] z / ℘'[L] z) ^ 2 + 3 * L.g₃ * (℘[L] z / ℘'[L] z) * (1 / ℘'[L] z)) z := by
    refine (((hasDerivAt_const z w).sub hζ).sub
      (((hP.pow 2).const_mul 2).div hP' hp)).congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    linear_combination (-3 * ℘[L] z) * hsq
  have hval : FVb L z w = ![℘[L] z / ℘'[L] z, 1, 1 / ℘'[L] z, (w - zeta L z) / ℘'[L] z,
      (w - zeta L z) - 2 * ℘[L] z ^ 2 / ℘'[L] z] := hFV.self_of_nhds
  rw [hval]
  have hc : ∀ (j : Fin 5) (g : ℂ → ℂ) (g' : ℂ), HasDerivAt g g' z →
      (∀ᶠ z' in 𝓝 z, FVb L z' w j = g z') → HasDerivAt (fun z => FVb L z w j) g' z :=
    fun j g g' hg he => hg.congr_of_eventuallyEq he
  fin_cases i
  · refine hc 0 _ _ (h0.congr_deriv ?_) (hFV.mono fun z' h => by rw [h]; rfl)
    simp [bField, LSG.ME.chartVf, LSG.ME.Faff]
  · refine hc 1 _ _ ((hasDerivAt_const z (1 : ℂ)).congr_deriv ?_)
      (hFV.mono fun z' h => by rw [h]; rfl)
    simp [bField]
  · refine hc 2 _ _ (h2.congr_deriv ?_) (hFV.mono fun z' h => by rw [h]; rfl)
    simp [bField, LSG.ME.chartVf, LSG.ME.Faff]
  · -- `T₁ = W T₃ + 2U²`
    have h0' : HasDerivAt (fun z => ℘[L] z / ℘'[L] z)
        (LSG.ME.chartVf L.g₂ L.g₃ (LSG.ME.Faff L z) 0) z := h0
    have h2' : HasDerivAt (fun z => 1 / ℘'[L] z)
        (LSG.ME.chartVf L.g₂ L.g₃ (LSG.ME.Faff L z) 2) z := h2
    have hT := (h2'.mul e4).add ((h0'.pow 2).const_mul 2)
    refine hc 3 _ _ (hT.congr_deriv ?_) (hU.mono fun z' ⟨_, h2⟩ => ?_)
    · simp [bField, LSG.ME.chartVf, LSG.ME.Faff]; ring
    · rw [FVb_off L ‹_›]
      simp [ptAff]; field_simp; ring
  · refine hc 4 _ _ (e4.congr_deriv ?_) (hFV.mono fun z' h => by rw [h]; rfl)
    simp [bField]

/-- **The `z`-derivative wherever `V ≠ 0`** (continuity at lattice points). -/
theorem hasDerivAt_FVb {z : ℂ} (hz : ellW L 2 z ≠ 0) (w : ℂ) (i : Fin 5) :
    HasDerivAt (fun z => FVb L z w i) (bField L.g₂ L.g₃ 1 0 (FVb L z w) i) z := by
  set U := {z : ℂ | ellW L 2 z ≠ 0}
  have hUo : IsOpen U := isOpen_ne_fun (LSG.Aux.differentiable_ellW L 2).continuous continuous_const
  have hdiff : DifferentiableOn ℂ (fun z => FVb L z w i) U := fun z hz =>
    (differentiableAt_FVb L hz w i).differentiableWithinAt
  have han := hdiff.analyticOnNhd hUo
  refine (differentiableAt_FVb L hz w i).hasDerivAt.congr_deriv ?_
  -- equality off the lattice, then continuity
  have hoff : ∀ z' ∈ U, z' ∉ L.lattice →
      deriv (fun z => FVb L z w i) z' = bField L.g₂ L.g₃ 1 0 (FVb L z' w) i := fun z' hz' hl => by
    have hp : ℘'[L] z' ≠ 0 := by
      intro h; apply hz'; rw [(LSG.Aux.ellW_eq_off L hl).2, h, mul_zero]
    exact (hasDerivAt_FVb_off L hl hp w i).deriv
  have hc1 : ContinuousAt (deriv fun z => FVb L z w i) z := (han z hz).deriv.continuousAt
  have hc2 : ContinuousAt (fun z => bField L.g₂ L.g₃ 1 0 (FVb L z w) i) z := by
    have hcomp : ∀ j, ContinuousAt (fun z => FVb L z w j) z := fun j =>
      (differentiableAt_FVb L hz w j).continuousAt
    fin_cases i <;> simp only [bField] <;> (try fun_prop)
  have hev : (deriv fun z => FVb L z w i) =ᶠ[𝓝[≠] z]
      fun z => bField L.g₂ L.g₃ 1 0 (FVb L z w) i := by
    have h1 : ∀ᶠ z' in 𝓝[≠] z, z' ∉ L.lattice := by
      have := L.compl_lattice_sdiff_singleton_mem_nhds z
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z' h h'
      exact fun hl => h ⟨hl, h'⟩
    filter_upwards [h1, nhdsWithin_le_nhds (hUo.mem_nhds hz)] with z' h h' using hoff z' h' h
  exact tendsto_nhds_unique ((hc1.tendsto.mono_left nhdsWithin_le_nhds))
    ((hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)

/-- **The derivative along a line**: `bField a b`. -/
theorem hasDerivAt_FVb_line {z : ℂ} (hz : ellW L 2 z ≠ 0) (w a b : ℂ) (i : Fin 5) :
    HasDerivAt (fun c : ℂ => FVb L (z + c * a) (w + c * b) i)
      (bField L.g₂ L.g₃ a b (FVb L z w) i) 0 := by
  have e : (fun c : ℂ => FVb L (z + c * a) (w + c * b) i) =
      fun c => FVb L (z + c * a) w i + c * b * FBb L (z + c * a) i := by
    funext c; rw [FVb_affine L (z + c * a) w (w + c * b)]; simp
  rw [e]
  have h1 : HasDerivAt (fun c : ℂ => FVb L (z + c * a) w i)
      (bField L.g₂ L.g₃ 1 0 (FVb L z w) i * a) 0 := by
    have hl : HasDerivAt (fun c : ℂ => z + c * a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const a).const_add z
    exact (hasDerivAt_FVb L hz w i).comp_of_eq (0 : ℂ) hl (by simp)
  have hFB : ContinuousAt (fun c : ℂ => FBb L (z + c * a) i) 0 := by
    have h2c := ((LSG.Aux.differentiable_ellW L 2) z).continuousAt.inv₀ hz
    have : ContinuousAt (fun z => FBb L z i) z := by
      fin_cases i
      · simpa [FBb] using continuousAt_const
      · simpa [FBb] using continuousAt_const
      · simpa [FBb] using continuousAt_const
      · simp only [FBb, Pi.smul_apply, smul_eq_mul]
        exact h2c.mul ((LSG.Aux.differentiable_ellW L 0) z).continuousAt
      · simp only [FBb, Pi.smul_apply, smul_eq_mul]
        exact h2c.mul ((LSG.Aux.differentiable_ellW L 2) z).continuousAt
    exact this.comp_of_eq (by fun_prop) (by simp)
  have h2 : HasDerivAt (fun c : ℂ => c * b * FBb L (z + c * a) i) (b * FBb L z i) 0 := by
    simpa using hasDerivAt_mul_self_zero b hFB
  refine (h1.add h2).congr_deriv ?_
  have hb : FBb L z i = bField L.g₂ L.g₃ 0 1 (FVb L z w) i := by
    fin_cases i <;> simp [FBb, FVb, bField, LSG.AuxV.ellN, hz]
  rw [hb, bField_lin L.g₂ L.g₃ a b]; ring

end Block

/-! ### All blocks -/

variable {d₀ d₁ m : ℕ} (Ls : Fin m → PeriodPair)

/-- **The `V`-normalised lift** of `expGV p`. -/
def FV (p : TanG d₀ d₁ m) : Var d₀ d₁ m → ℂ := liftV Ls p fun k => (ellW (Ls k) 2 (p.2.2.1 k))⁻¹

/-- `V ≠ 0` in every block of `expGV p`. -/
def GoodV (p : TanG d₀ d₁ m) : Prop := ∀ k, ellW (Ls k) 2 (p.2.2.1 k) ≠ 0

variable {Ls}

theorem FV_e (p : TanG d₀ d₁ m) (k : Fin m) (c : Fin 5) :
    FV Ls p (.e k c) = FVb (Ls k) (p.2.2.1 k) (p.2.2.2 k) c := by
  simp [FV, liftV, FVb]

theorem FV_V {p : TanG d₀ d₁ m} (hp : GoodV Ls p) (k : Fin m) : FV Ls p (.e k 1) = 1 := by
  rw [FV_e]; exact FVb_V _ (hp k) _

/-- `FV p` is a cone representative of `expGV p`. -/
theorem FV_eq_coords {p : TanG d₀ d₁ m} (hp : GoodV Ls p) :
    ∃ ν : Fin m → ℂˣ, FV Ls p = coords (expGV Ls p) ν := by
  obtain ⟨c, hc⟩ := liftV_eq Ls p
  refine ⟨fun k => Units.mk0 _ (inv_ne_zero (hp k)) * c k, ?_⟩
  rw [FV, hc]; rfl

theorem goodV_eventually {p : TanG d₀ d₁ m} (hp : GoodV Ls p) (w : TanG d₀ d₁ m) :
    ∀ᶠ c : ℂ in 𝓝 0, GoodV Ls (p + c • w) := by
  refine Filter.eventually_all.mpr fun k => ?_
  have hc : ContinuousAt (fun c : ℂ => ellW (Ls k) 2 ((p + c • w).2.2.1 k)) 0 := by
    have : Continuous (fun c : ℂ => (p + c • w).2.2.1 k) := by
      simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]; fun_prop
    exact ((LSG.Aux.differentiable_ellW (Ls k) 2).continuous.comp this).continuousAt
  exact hc.eventually_ne (by simpa using hp k)

/-- **The derivative of the lift along a line.** -/
theorem hasDerivAt_FV {p : TanG d₀ d₁ m} (hp : GoodV Ls p) (w : TanG d₀ d₁ m) (v : Var d₀ d₁ m) :
    HasDerivAt (fun c : ℂ => FV Ls (p + c • w) v) (DV Ls w (FV Ls p) v) 0 := by
  rw [DV_of_V Ls (FV_V hp)]
  cases v with
  | x i =>
    simpa [FV, liftV, dvalE] using ((hasDerivAt_id (0 : ℂ)).mul_const (w.1 i)).const_add (p.1 i)
  | y j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (p.2.1 j)).cexp
    simpa [FV, liftV, dvalE, mul_comm] using h
  | z j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (p.2.1 j)).neg.cexp
    simpa [FV, liftV, dvalE, mul_comm, neg_add] using h
  | e k c =>
    have h := hasDerivAt_FVb_line (Ls k) (hp k) (p.2.2.2 k) (w.2.2.1 k) (w.2.2.2 k) c
    simp only [FV_e, dvalE]
    convert h using 2

/-- **Chain rule**: `d/dc Q(FV(p + c w)) = (D̂_w Q)(FV p)`. -/
theorem hasDerivAt_eval_FV {p : TanG d₀ d₁ m} (hp : GoodV Ls p) (w : TanG d₀ d₁ m)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    HasDerivAt (fun c : ℂ => eval (FV Ls (p + c • w)) Q) (eval (FV Ls p) (Dh Ls w Q)) 0 := by
  classical
  have h := LSG.ME.hasDerivAt_eval (Y := fun c : ℂ => FV Ls (p + c • w)) (c₀ := 0)
    (fun v => hasDerivAt_FV hp w v) Q
  rw [eval_Dh]
  simpa using h

/-- The chain rule at an arbitrary parameter `c₀`. -/
theorem hasDerivAt_eval_FV_at {p w : TanG d₀ d₁ m} {c₀ : ℂ} (hp : GoodV Ls (p + c₀ • w))
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    HasDerivAt (fun c : ℂ => eval (FV Ls (p + c • w)) Q)
      (eval (FV Ls (p + c₀ • w)) (Dh Ls w Q)) c₀ := by
  have h := HasDerivAt.comp_sub_const c₀ c₀ (by rw [sub_self]; exact hasDerivAt_eval_FV hp w Q)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c => ?_)
  simp only [add_assoc, ← add_smul, add_sub_cancel]

end

end LSG.MEV
