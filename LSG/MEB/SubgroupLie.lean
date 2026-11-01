/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.PhOp
import LSG.MEB.StabG

/-!
# The analytic Lie algebra of a Zariski-closed subgroup and its identity component (A4.3, β)

For a Zariski-closed subgroup `H ⊆ G` (`LSG.ME.SubgroupLie`, `SubgroupIrred` for abstract blocks; the lift is just
`liftB`, so no local lifts are needed):

* `Htil hH = exp⁻¹(H)`, an additive subgroup of `Tan`; **`isClosed_Htil`** (`H` is cut out by multihomogeneous
  polynomials, `zeros_homogVanish`), `Per_le_Htil`, `expG_eq_zero_of_mem_Per`;
* **`smul_mem_Htil_of_real`**: real lines in `Htil` are complex lines (identity theorem along `c ↦ c • v`);
* **`lieAlg hH`** `= {v | ∀ c : ℂ, exp(c v) ∈ H}`, a `ℂ`-subspace; `mem_lieAlg`, `lieAlg_mono`;
* `mem_vanish_expG_image_iff`, **`vanish_expG_image_isPrime`**: for a complex subspace `T`, `I(exp T)` is prime
  (identity theorem on the connected space `T × ℂ^m`);
* **`H0 hH = zcl (exp (lieAlg hH))`**: `H0_isSubgroup`, `isZClosed_H0`, `H0_subset`, **`vanish_H0_isPrime`**,
  **`lieAlg_H0`** (`lieAlg H⁰ = lieAlg H`).
-/

open MvPolynomial Filter Topology Set

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### The preimage of a subgroup -/

/-- The kernel of `expG` contains the periods. -/
theorem expG_eq_zero_of_mem_Per {ω : Tan d₀ d₁ B} (hω : ω ∈ Per d₀ d₁ B) : expG d₀ d₁ B ω = 0 := by
  obtain ⟨h1, h2, h3⟩ := hω
  refine Prod.ext h1 (Prod.ext ?_ ?_)
  · change Additive.ofMul _ = Additive.ofMul 1
    congr 1
    funext j
    obtain ⟨n, hn⟩ := h2 j
    refine Units.ext ?_
    simp only [expU, Units.val_mk0, Units.val_one, Pi.one_apply, hn]
    rw [show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  · funext k
    exact (QuotientAddGroup.eq_zero_iff _).mpr (h3 k)

variable {H : Set (GPt d₀ d₁ B)}

/-- `exp⁻¹(H)` for a subgroup `H`. -/
def Htil (hH : IsSubgroupG H) : AddSubgroup (Tan d₀ d₁ B) where
  carrier := {u | expG d₀ d₁ B u ∈ H}
  zero_mem' := by simpa using hH.zero_mem
  add_mem' {a b} ha hb := by simpa [map_add] using hH.add_mem _ ha _ hb
  neg_mem' {a} ha := by simpa [map_neg] using hH.neg_mem _ ha

theorem mem_Htil {hH : IsSubgroupG H} {u : Tan d₀ d₁ B} : u ∈ Htil hH ↔ expG d₀ d₁ B u ∈ H := Iff.rfl

theorem Per_le_Htil (hH : IsSubgroupG H) : Per d₀ d₁ B ≤ Htil hH := fun ω hω => by
  rw [mem_Htil, expG_eq_zero_of_mem_Per hω]; exact hH.zero_mem

/-- Membership in a Zariski-closed `H` through the lift: `exp u ∈ H` iff every multihomogeneous element of
`I(H)` vanishes at `liftB u`. -/
theorem expG_mem_iff (hc : IsZClosed H) (u : Tan d₀ d₁ B) :
    expG d₀ d₁ B u ∈ H ↔ ∀ P ∈ homogVanish H, eval (liftB u) P = 0 := by
  constructor
  · intro hu P hP
    obtain ⟨lam, hlam⟩ := coords_expG u
    rw [← hlam]
    exact mem_vanish.mp hP.1 _ hu lam
  · intro h
    rw [← zeros_homogVanish hc]
    intro P hP lam
    obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ u lam
    obtain ⟨d, hd⟩ := hP.2
    rw [hμ, show μ = 1 * μ by simp, liftZ_mul_eq, eval_scale wV μ _ hd, liftZ_one, h P hP, mul_zero]

theorem continuous_eval_liftB (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    Continuous fun u : Tan d₀ d₁ B => eval (liftB u) P :=
  continuous_iff_continuousAt.mpr fun u =>
    (analyticAt_eval_of (f := fun v (u : Tan d₀ d₁ B) => liftB u v)
      (fun v => analyticAt_liftB_comp analyticAt_id v) P).continuousAt

/-- **`exp⁻¹(H)` is closed.** -/
theorem isClosed_Htil (hH : IsSubgroupG H) (hc : IsZClosed H) : IsClosed (Htil hH : Set (Tan d₀ d₁ B)) := by
  have : (Htil hH : Set (Tan d₀ d₁ B)) = ⋂ P ∈ homogVanish H, {u | eval (liftB u) P = 0} := by
    ext u
    simp only [SetLike.mem_coe, mem_Htil, expG_mem_iff hc, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isClosed_biInter fun P _ => isClosed_eq (continuous_eval_liftB P) continuous_const

/-- **Real lines in `exp⁻¹(H)` are complex lines** (identity theorem). -/
theorem smul_mem_Htil_of_real (hH : IsSubgroupG H) (hc : IsZClosed H) {v : Tan d₀ d₁ B}
    (hv : ∀ s : ℝ, (s : ℂ) • v ∈ Htil hH) (c : ℂ) : c • v ∈ Htil hH := by
  rw [mem_Htil, expG_mem_iff hc]
  intro P hP
  set f : ℂ → ℂ := fun c => eval (liftB (c • v)) P
  have hf : AnalyticOnNhd ℂ f univ := fun c₀ _ =>
    analyticAt_eval_of (f := fun w (c : ℂ) => liftB (c • v) w)
      (fun w => analyticAt_liftB_comp (analyticAt_id.smul analyticAt_const) w) P
  have hreal : ∀ s : ℝ, f s = 0 := fun s => (expG_mem_iff hc _).mp (hv s) P hP
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ) : ℕ → ℂ) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h1
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero, inv_eq_zero]
        positivity
    exact ht.frequently (Frequently.of_forall fun n => hreal _)
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ 0) hfreq
    (mem_univ c)

/-! ### The Lie algebra -/

/-- **The analytic Lie algebra** `{v | exp(ℂ v) ⊆ H}`. -/
def lieAlg (hH : IsSubgroupG H) : Submodule ℂ (Tan d₀ d₁ B) where
  carrier := {v | ∀ c : ℂ, c • v ∈ Htil hH}
  add_mem' {v w} hv hw c := by rw [smul_add]; exact (Htil hH).add_mem (hv c) (hw c)
  zero_mem' c := by simpa using (Htil hH).zero_mem
  smul_mem' a v hv c := by rw [smul_smul]; exact hv _

theorem mem_lieAlg {hH : IsSubgroupG H} {v : Tan d₀ d₁ B} :
    v ∈ lieAlg hH ↔ ∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ H := Iff.rfl

theorem lieAlg_le_Htil (hH : IsSubgroupG H) {v : Tan d₀ d₁ B} (hv : v ∈ lieAlg hH) : v ∈ Htil hH := by
  simpa using hv 1

theorem mem_lieAlg_iff_real (hH : IsSubgroupG H) (hc : IsZClosed H) {v : Tan d₀ d₁ B} :
    v ∈ lieAlg hH ↔ ∀ s : ℝ, (s : ℂ) • v ∈ Htil hH :=
  ⟨fun h s => h s, fun h c => smul_mem_Htil_of_real hH hc h c⟩

theorem lieAlg_mono {H' : Set (GPt d₀ d₁ B)} (hH : IsSubgroupG H) (hH' : IsSubgroupG H') (h : H ⊆ H') :
    lieAlg hH ≤ lieAlg hH' := fun _ hv c => h (hv c)

/-! ### Vanishing ideals of exponential images of subspaces -/

theorem mem_vanish_expG_image_iff (T : Submodule ℂ (Tan d₀ d₁ B)) {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanish (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B))) ↔ ∀ u ∈ T, ∀ μ, eval (liftZ u μ) P = 0 := by
  constructor
  · intro hP u hu μ
    obtain ⟨lam₀, h0⟩ := coords_expG u
    rw [liftZ_eq_coordsZ h0]
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ ⟨u, hu, rfl⟩ lam) _
  · intro h
    refine mem_vanish.mpr ?_
    rintro _ ⟨u, hu, rfl⟩ lam
    obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ u lam
    rw [hμ]; exact h u hu μ

/-- **`I(exp T)` is prime** for a complex subspace `T` (identity theorem on `T × ℂ^m`). -/
theorem vanish_expG_image_isPrime (T : Submodule ℂ (Tan d₀ d₁ B)) :
    (vanish (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B)))).IsPrime := by
  let F : MvPolynomial (Var d₀ d₁ B) ℂ → ↥T × (Fin m → ℂ) → ℂ := fun P q => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) P
  have hF : ∀ P, AnalyticOnNhd ℂ (F P) univ := fun P q _ => by
    have h1 : AnalyticAt ℂ (fun q : ↥T × (Fin m → ℂ) => (q.1 : Tan d₀ d₁ B)) q :=
      (T.subtypeL.analyticAt _).comp analyticAt_fst
    have hL : AnalyticAt ℂ (fun q : ↥T × (Fin m → ℂ) => (((q.1 : Tan d₀ d₁ B), q.2) : LZ d₀ d₁ B)) q :=
      h1.prod analyticAt_snd
    show AnalyticAt ℂ (fun q : ↥T × (Fin m → ℂ) => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) P) q
    exact AnalyticAt.comp (g := fun r : LZ d₀ d₁ B => eval (liftZ r.1 r.2) P)
      (f := fun q : ↥T × (Fin m → ℂ) => (((q.1 : Tan d₀ d₁ B), q.2) : LZ d₀ d₁ B))
      (analyticAt_eval_liftZ P _) hL
  have hmem : ∀ P, P ∈ vanish (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B))) ↔ ∀ q, F P q = 0 := fun P => by
    rw [mem_vanish_expG_image_iff]
    exact ⟨fun h q => h q.1 q.1.2 q.2, fun h u hu μ => h (⟨u, hu⟩, μ)⟩
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanish (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B))) :=
      htop ▸ Submodule.mem_top
    have := (hmem 1).mp h1 (0, 0)
    simp [F] at this
  have hfh : ∀ q, F P q * F Q q = 0 := fun q => by
    have := (hmem _).mp hPQ q
    simpa [F] using this
  by_cases hP : P ∈ vanish (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B)))
  · exact Or.inl hP
  right
  obtain ⟨q₀, hq₀⟩ : ∃ q, F P q ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP ((hmem P).mpr hcon)
  have hev : F Q =ᶠ[𝓝 q₀] 0 := by
    filter_upwards [(hF P q₀ (mem_univ _)).continuousAt.eventually_ne hq₀] with q hq
    exact (mul_eq_zero.mp (hfh q)).resolve_left hq
  have hzero := (hF Q).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_univ (𝕜 := ℝ)).isPreconnected (mem_univ q₀) hev
  exact (hmem Q).mpr fun q => hzero (mem_univ q)

/-! ### The identity component -/

theorem isSubgroupG_expG_image (T : Submodule ℂ (Tan d₀ d₁ B)) :
    IsSubgroupG (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B))) where
  zero_mem := ⟨0, T.zero_mem, map_zero _⟩
  add_mem := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨u + v, T.add_mem hu hv, map_add _ _ _⟩
  neg_mem := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨-u, T.neg_mem hu, map_neg _ _⟩

/-- **The identity component** `H⁰ = zcl (exp (lieAlg H))`. -/
def H0 (hH : IsSubgroupG H) : Set (GPt d₀ d₁ B) :=
  zcl (expG d₀ d₁ B '' (lieAlg hH : Set (Tan d₀ d₁ B)))

theorem H0_isSubgroup (hH : IsSubgroupG H) : IsSubgroupG (H0 hH) :=
  zcl_isSubgroup (isSubgroupG_expG_image _)

theorem isZClosed_H0 (hH : IsSubgroupG H) : IsZClosed (H0 hH) := isZClosed_zcl _

theorem H0_subset (hH : IsSubgroupG H) (hc : IsZClosed H) : H0 hH ⊆ H := by
  refine zcl_minimal hc ?_
  rintro _ ⟨v, hv, rfl⟩
  exact lieAlg_le_Htil hH hv

theorem expG_mem_H0 (hH : IsSubgroupG H) {v : Tan d₀ d₁ B} (hv : v ∈ lieAlg hH) : expG d₀ d₁ B v ∈ H0 hH :=
  subset_zcl _ ⟨v, hv, rfl⟩

/-- **`I(H⁰)` is prime.** -/
theorem vanish_H0_isPrime (hH : IsSubgroupG H) : (vanish (H0 hH)).IsPrime := by
  rw [H0, vanish_zcl]
  exact vanish_expG_image_isPrime _

/-- **`H⁰` has the same Lie algebra as `H`.** -/
theorem lieAlg_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) : lieAlg (H0_isSubgroup hH) = lieAlg hH := by
  refine le_antisymm (lieAlg_mono _ hH (H0_subset hH hc)) fun v hv c => ?_
  exact expG_mem_H0 hH (Submodule.smul_mem _ c hv)

end LSG.MEB
