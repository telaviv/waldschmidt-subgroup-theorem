import Mathlib
import LSG.MEV.SubgroupExp
import LSG.AuxFunV.ExpCoordsN

/-!
# `H̃ = exp⁻¹(H)` is closed, real lines in `H̃` are complex lines (gap G2 of STAGE5_MEV §6.4)

The abelian layer (`LSG.ME.SubgroupLie`) uses *local* analytic lifts of `expE` to the cone. For `E^♮`
there is a **global entire lift**: `ellN L z w = (σ³℘, σ³℘′, σ³, wσ³ − σ²σ′, wσ³℘′ + κ_σ)`
(`LSG.AuxV.ellN`, phase-1 analytic layer), with `ellN L z w = c • expN L z w`, `c ≠ 0`, for **all**
`(z, w)` (`ellN_eq_smul_expN`), and `expN = repV ∘ expV` (`repV_expV`).

* `liftV p μ`: the cone vector `(a, e^b, e^{−b}, μ_k · ellN(z_k, w_k))`; `liftV_eq`: it is
  `coordsZ (expGV p) ν` with `ν_k = μ_k c_k`.
* **`mem_iff_liftV`**: for `Z` Zariski closed, `expGV p ∈ Z ↔ ∀ P ∈ vanish Z, ∀ μ, P(liftV p μ) = 0`.
* `differentiable_eval_liftV`: `p ↦ P(liftV p μ)` is entire on `T_G̃`.
* **`isClosed_expGV_preimage`**, **`isClosed_Htil`**: preimages of Zariski-closed sets are closed.
* **`smul_mem_Htil`**: if `ℝ v ⊆ H̃` then `ℂ v ⊆ H̃` (identity theorem for the entire functions
  `c ↦ P(liftV (c v) μ)`, which vanish on `ℝ`); more generally `smul_mem_of_frequently`.
* **`restrictScalars_lieAlg`**: `lieAlg Ls hH` (complex lines) is the real linear part
  `linPart H̃` (the definition of the abelian layer).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.W88.Vec (TanV)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} (Ls : Fin m → PeriodPair)

/-- The global entire lift of `expGV` to the cone, with block scalings `μ`. -/
def liftV (p : TanG d₀ d₁ m) (μ : Fin m → ℂ) : Var d₀ d₁ m → ℂ
  | .x i => p.1 i
  | .y j => Complex.exp (p.2.1 j)
  | .z j => Complex.exp (-p.2.1 j)
  | .e k c => μ k * LSG.AuxV.ellN (Ls k) (p.2.2.1 k) (p.2.2.2 k) c

/-- **The lift is a cone representative**: `liftV p μ = coordsZ (expGV p) (μ · c)`. -/
theorem liftV_eq (p : TanG d₀ d₁ m) :
    ∃ c : Fin m → ℂˣ, ∀ μ, liftV Ls p μ = coordsZ (expGV Ls p) fun k => μ k * c k := by
  choose c hc0 hc using fun k => LSG.AuxV.ellN_eq_smul_expN (Ls k) (p.2.2.1 k) (p.2.2.2 k)
  refine ⟨fun k => Units.mk0 (c k) (hc0 k), fun μ => funext fun v => ?_⟩
  cases v with
  | x i => rfl
  | y j => simp [liftV, coordsZ, expGV, GPtV.ym, LSG.ME.expU]
  | z j => simp [liftV, coordsZ, expGV, GPtV.ym, LSG.ME.expU, Complex.exp_neg]
  | e k i =>
    simp only [liftV, coordsZ_e, hc k, Pi.smul_apply, smul_eq_mul, Units.val_mk0]
    rw [show (expGV Ls p).2.2 k = expV (Ls k) (p.2.2.1 k, p.2.2.2 k) from rfl, repV_expV]
    ring

variable {Ls}

/-- **Membership via the lift.** -/
theorem mem_iff_liftV {Z : Set (GPtV d₀ d₁ Ls)} (hc : IsZClosed Z) (p : TanG d₀ d₁ m) :
    expGV Ls p ∈ Z ↔ ∀ P ∈ vanish Z, ∀ μ : Fin m → ℂˣ, eval (liftV Ls p fun k => μ k) P = 0 := by
  obtain ⟨c, hc'⟩ := liftV_eq Ls p
  constructor
  · intro hp P hP μ
    rw [hc']
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ hp lam) _
  · intro h
    rw [← zeros_vanish hc]
    intro P hP lam
    have := h P hP fun k => lam k / c k
    rw [hc'] at this
    have e : coords (expGV Ls p) lam =
        coordsZ (expGV Ls p) fun k => ((lam k / c k : ℂˣ) : ℂ) * (c k : ℂ) := by
      funext v
      cases v with
      | x i => rfl
      | y j => rfl
      | z j => rfl
      | e k i => simp only [coords, coordsZ_e, ← Units.val_mul, div_mul_cancel]
    rw [e]; exact this

/-- The coordinates of the lift are entire functions on `T_G̃`. -/
theorem differentiable_liftV (μ : Fin m → ℂ) (v : Var d₀ d₁ m) :
    Differentiable ℂ fun p : TanG d₀ d₁ m => liftV Ls p μ v := by
  cases v with
  | x i => show Differentiable ℂ fun p : TanG d₀ d₁ m => p.1 i; fun_prop
  | y j => show Differentiable ℂ fun p : TanG d₀ d₁ m => Complex.exp (p.2.1 j); fun_prop
  | z j => show Differentiable ℂ fun p : TanG d₀ d₁ m => Complex.exp (-p.2.1 j); fun_prop
  | e k i =>
    refine (differentiable_const _).mul ?_
    have h1 : Differentiable ℂ fun p : TanG d₀ d₁ m => (p.2.2.1 k, p.2.2.2 k) := by fun_prop
    exact (LSG.AuxV.differentiable_ellN (Ls k) i).comp h1

/-- Polynomials evaluated at the lift are entire. -/
theorem differentiable_eval_liftV (μ : Fin m → ℂ) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    Differentiable ℂ fun p : TanG d₀ d₁ m => eval (liftV Ls p μ) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_liftV μ v)

/-- **Preimages of Zariski-closed sets are closed.** -/
theorem isClosed_expGV_preimage {Z : Set (GPtV d₀ d₁ Ls)} (hc : IsZClosed Z) :
    IsClosed (expGV (d₀ := d₀) (d₁ := d₁) Ls ⁻¹' Z) := by
  have : expGV (d₀ := d₀) (d₁ := d₁) Ls ⁻¹' Z =
      ⋂ P ∈ vanish Z, ⋂ μ : Fin m → ℂˣ,
        {p | eval (liftV Ls p fun k => (μ k : ℂ)) P = 0} := by
    ext p
    simp only [mem_preimage, mem_iInter, mem_ofPred_eq]
    exact mem_iff_liftV hc p
  rw [this]
  exact isClosed_biInter fun P _ => isClosed_iInter fun μ =>
    isClosed_eq (differentiable_eval_liftV _ P).continuous continuous_const

/-- **`exp⁻¹(H)` is closed.** -/
theorem isClosed_Htil {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsClosed (Htil Ls hH : Set (TanG d₀ d₁ m)) :=
  isClosed_expGV_preimage hc

/-! ### Complex lines -/

/-- **Identity theorem along a line**: if `c • v ∈ exp⁻¹(Z)` for `c` accumulating at some `c₀`,
then for all `c`. -/
theorem smul_mem_of_frequently {Z : Set (GPtV d₀ d₁ Ls)} (hc : IsZClosed Z) (v : TanG d₀ d₁ m)
    (c₀ : ℂ) (hfr : ∃ᶠ c in 𝓝[≠] c₀, expGV Ls (c • v) ∈ Z) (c : ℂ) : expGV Ls (c • v) ∈ Z := by
  rw [mem_iff_liftV hc]
  intro P hP μ
  have hd : Differentiable ℂ fun c : ℂ => eval (liftV Ls (c • v) fun k => (μ k : ℂ)) P :=
    (differentiable_eval_liftV _ P).comp (differentiable_id.smul_const v)
  have han : AnalyticOnNhd ℂ (fun c : ℂ => eval (liftV Ls (c • v) fun k => (μ k : ℂ)) P) univ :=
    fun c _ => hd.analyticAt c
  refine han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ c₀)
    ?_ (mem_univ c)
  exact hfr.mono fun c hcZ => (mem_iff_liftV hc _).mp hcZ P hP μ

/-- **Real lines in `exp⁻¹(Z)` are complex lines** (`Z` Zariski closed). -/
theorem smul_mem_of_real {Z : Set (GPtV d₀ d₁ Ls)} (hc : IsZClosed Z) (v : TanG d₀ d₁ m)
    (hv : ∀ s : ℝ, expGV Ls (s • v) ∈ Z) (c : ℂ) : expGV Ls (c • v) ∈ Z := by
  refine smul_mem_of_frequently hc v 0 ?_ c
  have hreal : ∀ s : ℝ, expGV Ls ((s : ℂ) • v) ∈ Z := fun s => by
    rw [Complex.coe_smul]; exact hv s
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs => by simpa using hs)
  exact ht.frequently (Frequently.of_forall fun s => hreal s)

variable {H : Set (GPtV d₀ d₁ Ls)}

/-- **Real lines in `H̃` are complex lines.** -/
theorem smul_mem_Htil (hH : IsSubgroupG H) (hc : IsZClosed H) (v : TanG d₀ d₁ m)
    (hv : ∀ s : ℝ, s • v ∈ Htil Ls hH) (c : ℂ) : c • v ∈ Htil Ls hH :=
  smul_mem_of_real hc v hv c

/-- **`lieAlg` is the real linear part of `H̃`** (the definition of the abelian layer). -/
theorem restrictScalars_lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (lieAlg Ls hH).restrictScalars ℝ = LSG.Subgroups.linPart (Htil Ls hH) := by
  ext v
  simp only [Submodule.restrictScalars_mem, LSG.Subgroups.mem_linPart]
  constructor
  · intro hv s; rw [← Complex.coe_smul]; exact hv _
  · intro hv c; exact smul_mem_Htil hH hc v hv c

theorem mem_lieAlg_iff_real (hH : IsSubgroupG H) (hc : IsZClosed H) {v : TanG d₀ d₁ m} :
    v ∈ lieAlg Ls hH ↔ ∀ s : ℝ, s • v ∈ Htil Ls hH := by
  rw [← LSG.Subgroups.mem_linPart, ← restrictScalars_lieAlg hH hc]; rfl

end

end LSG.MEV
