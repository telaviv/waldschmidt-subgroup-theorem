/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ExpKer

/-!
# Following moving divisors without nondegeneracy, and periods in the kernel (STAGE_A2 §8, route (e′))

`follow_trans` needed `T(A(t)) ≠ 0` along the path only to normalise. Here the statement is kept in parallelism form and
propagated through zeros of `T` by the identity theorem:

* `flow_eventuallyEq`: two chart-0 flow solutions with the same value at a point agree near it (step 1: local
  exponentials are base-independent);
* `FollowGood t`: `T(A(t) + w) ∥ V w` near `0` for every chart-0 flow solution `V` near `0` with `V 0 = [D(t)]`;
* **`follow_par`** (step 2): `FollowGood t` for all `t ∈ [0,1]`, for every continuous path of generic divisors from the
  base pair; **no hypothesis `T ≠ 0`**;
* `exists_ne_zero_of_open`: density lemma (identity theorem);
* **`expP_periodic_of_paths`** (step 3): two such paths with a common end give `E (z + (A(1) − A'(1))) = E z`;
  **no `hT`, no `hXn`**.
-/

noncomputable section

open Polynomial Metric Set Filter Topology
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

/-- **Step 1**: chart-0 flow solutions with the same value at `w₀` agree near `w₀`. -/
lemma flow_eventuallyEq {V₁ V₂ : (Fin 2 → ℂ) → P9} {w₀ : Fin 2 → ℂ}
    (h₁ : ∀ᶠ w in 𝓝 w₀, HasFDerivAt V₁ (flowCLM flowW 1 (V₁ w)) w)
    (h₂ : ∀ᶠ w in 𝓝 w₀, HasFDerivAt V₂ (flowCLM flowW 1 (V₂ w)) w) (h0 : V₁ w₀ = V₂ w₀) :
    V₁ =ᶠ[𝓝 w₀] V₂ := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (h₁.and h₂)
  have := flow_unique flowW contDiff_flowW 1 (fun w hw => (hb w hw).1) (fun w hw => (hb w hw).2) h0
  filter_upwards [ball_mem_nhds w₀ hr] with w hw using this w hw

/-- **Density lemma**: an analytic function on a connected open set, nonzero somewhere, is nonzero somewhere in every
nonempty open subset. -/
lemma exists_ne_zero_of_open {D V : Set (Fin 2 → ℂ)} (hD : IsPreconnected D) {f : (Fin 2 → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f D) {z₀ : Fin 2 → ℂ} (hz₀ : z₀ ∈ D) (hf0 : f z₀ ≠ 0) (hV : IsOpen V)
    (hVD : V ⊆ D) {v : Fin 2 → ℂ} (hv : v ∈ V) : ∃ u ∈ V, f u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : f =ᶠ[𝓝 v] 0 := by
    filter_upwards [hV.mem_nhds hv] with u hu using hcon u hu
  exact hf0 (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVD hv) h0 hz₀)

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

/-- Chart-0 flow solution near `0`. -/
def FlowNear (V : (Fin 2 → ℂ) → P9) : Prop := ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), HasFDerivAt V (flowCLM flowW 1 (V w)) w

/-- The local exponential at a generic pair is a chart-0 flow solution near `0` (in `w`), analytic near `0`. -/
lemma psi_flowNear {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} (hp' : p' ∈ dom2 B₁' B₂') (hx' : p'.1 ≠ p'.2) :
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), HasFDerivAt (fun w => psiJ hp' hx' (abel2 B₁' B₂' p' + w))
      (flowCLM flowW 1 (psiJ hp' hx' (abel2 B₁' B₂' p' + w))) w ∧
      AnalyticAt ℂ (fun w => psiJ hp' hx' (abel2 B₁' B₂' p' + w)) w := by
  have ht : Tendsto (fun w : Fin 2 → ℂ => abel2 B₁' B₂' p' + w) (𝓝 0) (𝓝 (abel2 B₁' B₂' p')) := by
    have hc : Continuous (fun w : Fin 2 → ℂ => abel2 B₁' B₂' p' + w) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  filter_upwards [ht.eventually (grant_localExp_flow hp' hx'), ht.eventually (eventually_analyticAt_psiJ hp' hx')]
    with w hw han
  refine ⟨?_, han.comp (analyticAt_const.add analyticAt_id)⟩
  have := hw.2.comp w ((hasFDerivAt_id w).const_add (abel2 B₁' B₂' p'))
  simpa [psiJ] using this

/-- The follow property at time `t` (for given path data). -/
def FollowGood (k : ℕ) (Ab : ℝ → (Fin 2 → ℂ)) (Dm : ℝ → P9) (t : ℝ) : Prop :=
  ∀ V : (Fin 2 → ℂ) → P9, FlowNear V → V 0 = Dm t →
    ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (transP (A := A) (hp := hp) (hx := hx) k (Ab t + w)) (V w)

/-- **Step 2: follow without nondegeneracy.** -/
theorem follow_par (k : ℕ) {u₁ Y₁ u₂ Y₂ : ℝ → ℂ} {A₁ A₂ : ℝ → (Fin 2 → ℂ)}
    (hA₁ : IsAbelAlong f₅ 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f₅ 2 u₂ Y₂ A₂) (hA₁0 : A₁ 0 = 0) (hA₂0 : A₂ 0 = 0)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t)
    (hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    ∀ t ∈ Icc (0 : ℝ) 1, FollowGood (A := A) (hp := hp) (hx := hx) k (fun t => A₁ t + A₂ t)
      (fun t => grantJ (mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t))) t := by
  set R := 2 ^ k * G.ε
  set T := transP (A := A) (hp := hp) (hx := hx) k
  set Ab : ℝ → (Fin 2 → ℂ) := fun t => A₁ t + A₂ t
  set Dm : ℝ → P9 := fun t => grantJ (mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t))
  have hAc : ContinuousOn Ab (Icc 0 1) := (hA₁.continuousOn hu₁).add (hA₂.continuousOn hu₂)
  have hTan : ∀ w ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ T w := fun w hw => analyticOn_transP G k w hw
  -- the local lemma at each time
  have hlocal : ∀ s ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ t ∈ ball s δ ∩ Icc (0 : ℝ) 1,
      (FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm t → FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm s) ∧
      (FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm s → FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm t) := by
    intro s hs
    obtain ⟨B₁', B₂', hp', hY1, hY2, hev⟩ := localExp_follow hA₁ hA₂ hu₁ hu₂ hdiag hs
    set p' : ℂ × ℂ := (u₁ s, u₂ s)
    have hx' : p'.1 ≠ p'.2 := hdiag s hs
    set Ψ : (Fin 2 → ℂ) → P9 := fun w => psiJ hp' hx' (abel2 B₁' B₂' p' + w)
    have hΨ0 : Ψ 0 = Dm s := by
      simp only [Ψ, Dm, add_zero, psiJ, localExp_abel2_self, mumford_eq_mumfordPts]
      change grantJ (mumfordPts (u₁ s) (B₁'.Y (u₁ s)) (u₂ s) (B₂'.Y (u₂ s))) =
        grantJ (mumfordPts (u₁ s) (Y₁ s) (u₂ s) (Y₂ s))
      rw [hY1, hY2]
    -- the ball of `Ψ`
    have hUo : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Ab s + w ∈ ball (0 : Fin 2 → ℂ) R := by
      have hc : ContinuousAt (fun w : Fin 2 → ℂ => Ab s + w) 0 := (continuous_const.add continuous_id).continuousAt
      exact hc.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds (hU s hs))
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp ((psi_flowNear hp' hx').and hUo)
    -- (L1) upgrade on the ball
    have upgrade : ∀ w₁ ∈ ball (0 : Fin 2 → ℂ) ρ,
        (∀ᶠ w in 𝓝 w₁, Par (T (Ab s + w)) (Ψ w)) → ∀ w ∈ ball (0 : Fin 2 → ℂ) ρ, Par (T (Ab s + w)) (Ψ w) :=
      fun w₁ hw₁ h => par_of_eventually (convex_ball _ _).isPreconnected
        (fun w hw => (hTan _ (hball w hw).2).comp (analyticAt_const.add analyticAt_id))
        (fun w hw => (hball w hw).1.2) hw₁ h
    -- (L2) matching along the path
    have hδ : ∀ᶠ t in 𝓝[Icc 0 1] s, Ab t - Ab s ∈ ball (0 : Fin 2 → ℂ) ρ := by
      have hc : ContinuousWithinAt (fun t => Ab t - Ab s) (Icc 0 1) s := (hAc s hs).sub continuousWithinAt_const
      exact hc.preimage_mem_nhdsWithin (by simpa using ball_mem_nhds (0 : Fin 2 → ℂ) hρ)
    obtain ⟨δ, hδpos, hδb⟩ := Metric.mem_nhdsWithin_iff.mp (hδ.and hev)
    refine ⟨δ, hδpos, fun t ht => ?_⟩
    obtain ⟨hdt, hloc⟩ := hδb ht
    set d := Ab t - Ab s
    -- the shifted local exponential is a flow solution near `0` with value `[D(t)]`
    have hVt_flow : FlowNear (fun w' => Ψ (d + w')) := by
      have hc : ContinuousAt (fun w' : Fin 2 → ℂ => d + w') 0 := (continuous_const.add continuous_id).continuousAt
      have hmem : ball (0 : Fin 2 → ℂ) ρ ∈ 𝓝 ((fun w' : Fin 2 → ℂ => d + w') 0) := by
        simpa using isOpen_ball.mem_nhds hdt
      filter_upwards [hc.preimage_mem_nhds hmem] with w' hw'
      have := ((hball _ hw').1.1).comp w' ((hasFDerivAt_id w').const_add d)
      simpa using this
    have hVt0 : (fun w' => Ψ (d + w')) 0 = Dm t := by
      simp only [Ψ, add_zero, Dm, psiJ, d]
      rw [hloc]
    have hshift : ∀ᶠ w' in 𝓝 (0 : Fin 2 → ℂ), d + w' ∈ ball (0 : Fin 2 → ℂ) ρ := by
      have hc : ContinuousAt (fun w' : Fin 2 → ℂ => d + w') 0 := (continuous_const.add continuous_id).continuousAt
      exact hc.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hdt)
    have hAt : Ab t = Ab s + d := by simp only [d]; abel
    constructor
    · -- closedness direction: good at `t` gives good at `s`
      intro ht_good V hV hV0
      have h1 := ht_good _ hVt_flow hVt0
      -- `Par (T (Ab s + w)) (Ψ w)` near `w = d`
      have h2 : ∀ᶠ w in 𝓝 d, Par (T (Ab s + w)) (Ψ w) := by
        have ht : Tendsto (fun w : Fin 2 → ℂ => w - d) (𝓝 d) (𝓝 0) := by
          have h := (tendsto_id (x := 𝓝 d)).sub (tendsto_const_nhds (x := d))
          rwa [sub_self] at h
        filter_upwards [ht.eventually h1] with w hw
        have e : Ab t + (w - d) = Ab s + w := by rw [hAt]; abel
        have e' : d + (w - d) = w := by abel
        rw [e, e'] at hw
        exact hw
      have hall := upgrade d hdt h2
      have hVΨ : V =ᶠ[𝓝 (0 : Fin 2 → ℂ)] Ψ :=
        flow_eventuallyEq hV (by filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) hρ] with w hw using (hball w hw).1.1)
          (hV0.trans hΨ0.symm)
      filter_upwards [hVΨ, ball_mem_nhds (0 : Fin 2 → ℂ) hρ] with w hw hwb
      rw [hw]; exact hall w hwb
    · -- openness direction: good at `s` gives good at `t`
      intro hs_good V hV hV0
      have h1 := hs_good Ψ (by filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) hρ] with w hw using (hball w hw).1.1)
        hΨ0
      have hall := upgrade 0 (mem_ball_self hρ) h1
      have hVV : V =ᶠ[𝓝 (0 : Fin 2 → ℂ)] (fun w' => Ψ (d + w')) := flow_eventuallyEq hV hVt_flow (hV0.trans hVt0.symm)
      filter_upwards [hVV, hshift] with w' hw' hw's
      rw [hw', hAt, add_assoc]
      exact hall _ hw's
  -- clopen argument on `[0, 1]`
  have hpc := Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  set S : Set (Icc (0 : ℝ) 1) := {t | FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm t}
  have hnbhd : ∀ s : Icc (0 : ℝ) 1, ∃ N ∈ 𝓝 s, ∀ t ∈ N, (t ∈ S → s ∈ S) ∧ (s ∈ S → t ∈ S) := by
    intro s
    obtain ⟨δ, hδ, h⟩ := hlocal s s.2
    refine ⟨{t : Icc (0 : ℝ) 1 | (t : ℝ) ∈ ball (s : ℝ) δ},
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ), fun t ht => h t ⟨ht, t.2⟩⟩
  have hop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨N, hN, h⟩ := hnbhd s
    filter_upwards [hN] with t ht using (h t ht).2 hs
  have hcl : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨N, hN, h⟩ := hnbhd s
    filter_upwards [hN] with t ht htS using hs ((h t ht).1 htS)
  have h0S : (⟨0, by simp⟩ : Icc (0 : ℝ) 1) ∈ S := by
    change FollowGood (A := A) (hp := hp) (hx := hx) k Ab Dm 0
    intro V hV hV0
    obtain ⟨δ, hδ, hl⟩ := link G k
    have hΨb := psi_flowNear hp hx
    have hVΨ : V =ᶠ[𝓝 (0 : Fin 2 → ℂ)] (fun w => psiJ hp hx (abel2 B₁ B₂ p + w)) :=
      flow_eventuallyEq hV (by filter_upwards [hΨb] with w hw using hw.1)
        (by rw [hV0]; simp only [Dm, hstart, add_zero, psiJ, localExp_abel2_self])
    filter_upwards [hVΨ, ball_mem_nhds (0 : Fin 2 → ℂ) hδ] with w hw hwδ
    rw [hw, ← hl w hwδ]
    simp only [Ab, hA₁0, hA₂0, add_zero, zero_add]
    exact (par_normalize 0 _).symm
  have hSu : S = univ := by
    rcases isClopen_iff.mp ⟨hcl, hop⟩ with h | h
    · exact absurd (h ▸ h0S) (Set.notMem_empty _)
    · exact h
  intro t ht
  have : (⟨t, ht⟩ : Icc (0 : ℝ) 1) ∈ S := hSu ▸ mem_univ _
  exact this

/-- **Step 3: periods from two paths with a common end, without nondegeneracy.** Two continuous paths of generic
divisors from the base pair to a common end, with path Abel integrals `A = A₁ + A₂` and `A' = A₁' + A₂'`, give
`E (z + (A(1) − A'(1))) = E z`. -/
theorem expP_periodic_of_paths (k : ℕ) {u₁ Y₁ u₂ Y₂ v₁ Z₁ v₂ Z₂ : ℝ → ℂ} {A₁ A₂ A₁' A₂' : ℝ → (Fin 2 → ℂ)}
    (hA₁ : IsAbelAlong f₅ 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f₅ 2 u₂ Y₂ A₂) (hA₁0 : A₁ 0 = 0) (hA₂0 : A₂ 0 = 0)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t)
    (hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hA₁' : IsAbelAlong f₅ 2 v₁ Z₁ A₁') (hA₂' : IsAbelAlong f₅ 2 v₂ Z₂ A₂') (hA₁0' : A₁' 0 = 0)
    (hA₂0' : A₂' 0 = 0) (hv₁ : ContinuousOn v₁ (Icc 0 1)) (hv₂ : ContinuousOn v₂ (Icc 0 1))
    (hdiag' : ∀ t ∈ Icc (0 : ℝ) 1, v₁ t ≠ v₂ t)
    (hstart' : mumfordPts (v₁ 0) (Z₁ 0) (v₂ 0) (Z₂ 0) = mumford B₁ B₂ p)
    (hU' : ∀ t ∈ Icc (0 : ℝ) 1, A₁' t + A₂' t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hend : mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1) = mumfordPts (v₁ 1) (Z₁ 1) (v₂ 1) (Z₂ 1))
    (hcU : (A₁ 1 + A₂ 1) - (A₁' 1 + A₂' 1) ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    {z : Fin 2 → ℂ} (hz : z ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hzc : z + ((A₁ 1 + A₂ 1) - (A₁' 1 + A₂' 1)) ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε)) :
    expP G (z + ((A₁ 1 + A₂ 1) - (A₁' 1 + A₂' 1))) = expP G z := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hpos : 0 < 2 ^ k * G.ε := by have := G.pos; positivity
  set R := 2 ^ k * G.ε
  set a := A₁ 1 + A₂ 1
  set b := A₁' 1 + A₂' 1
  set c := a - b
  have hTan : ∀ w ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ (transP (A := A) (hp := hp) (hx := hx) k) w :=
    fun w hw => analyticOn_transP G k w hw
  -- the local exponential at the common end
  obtain ⟨B₁'', B₂'', hp'', hY1, hY2, -⟩ := localExp_follow hA₁ hA₂ hu₁ hu₂ hdiag h1
  have hx'' : (u₁ 1, u₂ 1).1 ≠ (u₁ 1, u₂ 1).2 := hdiag 1 h1
  set Ψ : (Fin 2 → ℂ) → P9 := fun w => psiJ hp'' hx'' (abel2 B₁'' B₂'' (u₁ 1, u₂ 1) + w)
  have hΨf : FlowNear Ψ := by filter_upwards [psi_flowNear hp'' hx''] with w hw using hw.1
  have hΨ0 : Ψ 0 = grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1)) := by
    simp only [Ψ, add_zero, psiJ, localExp_abel2_self, mumford_eq_mumfordPts]
    show grantJ (mumfordPts (u₁ 1) (B₁''.Y (u₁ 1)) (u₂ 1) (B₂''.Y (u₂ 1))) =
      grantJ (mumfordPts (u₁ 1) (Y₁ 1) (u₂ 1) (Y₂ 1))
    rw [hY1, hY2]
  have hPa := follow_par G k hA₁ hA₂ hA₁0 hA₂0 hu₁ hu₂ hdiag hstart hU 1 h1 Ψ hΨf hΨ0
  have hPb := follow_par G k hA₁' hA₂' hA₁0' hA₂0' hv₁ hv₂ hdiag' hstart' hU' 1 h1 Ψ hΨf
    (by rw [hΨ0, hend])
  have hab : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), Par (transP (A := A) (hp := hp) (hx := hx) k (a + w))
      (transP (A := A) (hp := hp) (hx := hx) k (b + w)) := by
    filter_upwards [hPa, hPb] with w hwa hwb
    exact hwa.trans hwb.symm (m := 0) (by simp [Ψ, psiJ_zero])
  have hnear : ∀ᶠ u in 𝓝 b, Par (transP (A := A) (hp := hp) (hx := hx) k (u + c))
      (transP (A := A) (hp := hp) (hx := hx) k u) := by
    have ht : Tendsto (fun u : Fin 2 → ℂ => u - b) (𝓝 b) (𝓝 0) := by
      have h := (tendsto_id (x := 𝓝 b)).sub (tendsto_const_nhds (x := b))
      rwa [sub_self] at h
    filter_upwards [ht.eventually hab] with u hu
    have e1 : a + (u - b) = u + c := by simp only [c]; abel
    have e2 : b + (u - b) = u := by abel
    rw [e1, e2] at hu
    exact hu
  -- the domain
  have hmemD : ∀ u, u + c ∈ ball (0 : Fin 2 → ℂ) R ↔ u ∈ ball (-c) R := fun u => by
    rw [mem_ball_zero_iff, mem_ball, dist_eq_norm, sub_neg_eq_add]
  set D : Set (Fin 2 → ℂ) := ball 0 R ∩ ball (-c) R
  have hDo : IsOpen D := isOpen_ball.inter isOpen_ball
  have hDc : IsPreconnected D := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hbD : b ∈ D := ⟨hU' 1 h1, (hmemD b).mp (by simpa [c] using hU 1 h1)⟩
  have h0D : (0 : Fin 2 → ℂ) ∈ D := ⟨mem_ball_self hpos, (hmemD 0).mp (by simpa using hcU)⟩
  have hcD : -c ∈ D := ⟨by rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp hcU,
    (hmemD (-c)).mp (by simp [hpos])⟩
  -- three analytic scalar functions on `D`, each nonzero somewhere
  obtain ⟨l, hl, hT0⟩ := transP_zero G k
  set f₁ : (Fin 2 → ℂ) → ℂ := fun u => transP (A := A) (hp := hp) (hx := hx) k u 0
  set f₂ : (Fin 2 → ℂ) → ℂ := fun u => transP (A := A) (hp := hp) (hx := hx) k (u + c) 0
  set f₃ : (Fin 2 → ℂ) → ℂ :=
    fun u => A.law0 (transP (A := A) (hp := hp) (hx := hx) k u) (A.negP (baseP hp hx)) 4
  have hf₁ : AnalyticOnNhd ℂ f₁ D := fun u hu => (analyticAt_pi_iff.mp (hTan u hu.1)) 0
  have hf₂ : AnalyticOnNhd ℂ f₂ D := fun u hu =>
    (analyticAt_pi_iff.mp (AnalyticAt.comp (g := transP (A := A) (hp := hp) (hx := hx) k)
      (f := fun u => u + c) (hTan _ ((hmemD u).mpr hu.2)) (analyticAt_id.add analyticAt_const))) 0
  have hf₃ : AnalyticOnNhd ℂ f₃ D := fun u hu =>
    (analyticAt_pi_iff.mp (analyticAt_law0_comp (hTan u hu.1))) 4
  have hT00 : transP (A := A) (hp := hp) (hx := hx) k 0 0 ≠ 0 := by rw [hT0]; simp [baseP_zero, hl]
  have hf₁0 : f₁ 0 ≠ 0 := hT00
  have hf₂0 : f₂ (-c) ≠ 0 := by simp only [f₂, neg_add_cancel]; exact hT00
  have hf₃0 : f₃ 0 ≠ 0 := by
    simp only [f₃, hT0, A.law0_smul_left, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero 2 hl) G.hP₀
  -- an open set near `b` where everything is nonzero
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  set V₀ := ball b r₀ ∩ D
  have hV₀ : IsOpen V₀ := isOpen_ball.inter hDo
  have hV₀D : V₀ ⊆ D := inter_subset_right
  obtain ⟨u₁', hu₁', hf₁u⟩ := exists_ne_zero_of_open hDc hf₁ h0D hf₁0 hV₀ hV₀D
    ⟨mem_ball_self hr₀, hbD⟩
  set V₁ := V₀ ∩ f₁ ⁻¹' {0}ᶜ
  have hV₁D : V₁ ⊆ D := inter_subset_left.trans hV₀D
  have hV₁ : IsOpen V₁ :=
    ((hf₁.continuousOn).mono hV₀D).isOpen_inter_preimage hV₀ isOpen_compl_singleton
  obtain ⟨u₂', hu₂', hf₂u⟩ := exists_ne_zero_of_open hDc hf₂ hcD hf₂0 hV₁ hV₁D
    (show u₁' ∈ V₁ from ⟨hu₁', hf₁u⟩)
  set V₂ := V₁ ∩ f₂ ⁻¹' {0}ᶜ
  have hV₂D : V₂ ⊆ D := inter_subset_left.trans hV₁D
  have hV₂ : IsOpen V₂ :=
    ((hf₂.continuousOn).mono hV₁D).isOpen_inter_preimage hV₁ isOpen_compl_singleton
  obtain ⟨u₃', hu₃', hf₃u⟩ := exists_ne_zero_of_open hDc hf₃ h0D hf₃0 hV₂ hV₂D
    (show u₂' ∈ V₂ from ⟨hu₂', hf₂u⟩)
  set V₃ := V₂ ∩ f₃ ⁻¹' {0}ᶜ
  have hV₃ : IsOpen V₃ :=
    ((hf₃.continuousOn).mono hV₂D).isOpen_inter_preimage hV₂ isOpen_compl_singleton
  have hu₃V : u₃' ∈ V₃ := ⟨hu₃', hf₃u⟩
  have hu₃D : u₃' ∈ D := hV₂D hu₃'
  -- on `V₃`, `Ẽ (u + c) ∥ Ẽ u`
  have hpar3 : ∀ᶠ u in 𝓝 u₃', Par (expLift A hp hx k (u + c)) (expLift A hp hx k u) := by
    filter_upwards [hV₃.mem_nhds hu₃V] with u hu
    obtain ⟨⟨⟨⟨hub, huD⟩, h1u⟩, h2u⟩, h3u⟩ := hu
    have h1u' : transP (A := A) (hp := hp) (hx := hx) k u 0 ≠ 0 := h1u
    have h2u' : transP (A := A) (hp := hp) (hx := hx) k (u + c) 0 ≠ 0 := h2u
    have h3u' : A.law0 (transP (A := A) (hp := hp) (hx := hx) k u) (A.negP (baseP hp hx)) 4 ≠ 0 := h3u
    have hp' := hball₀ u hub
    have hν : transP (A := A) (hp := hp) (hx := hx) k (u + c) 0 /
        transP (A := A) (hp := hp) (hx := hx) k u 0 ≠ 0 := div_ne_zero h2u' h1u'
    have hTν := hp'.symm.eq_smul h1u'
    have hi1 := inv_trans G k ((hmemD u).mpr huD.2)
    have hi2 := inv_trans G k huD.1
    rw [hTν, A.law0_smul_left] at hi1
    exact (hi1.of_smul_right (pow_ne_zero 2 hν)).trans hi2.symm h3u'
  have hpar := par_of_eventually hDc (F₁ := fun u => expLift A hp hx k (u + c)) (F₂ := expLift A hp hx k)
    (fun u hu => AnalyticAt.comp (g := expLift A hp hx k) (f := fun u => u + c)
      (analyticOn_expLift G k (u + c) ((hmemD u).mpr hu.2)) (analyticAt_id.add analyticAt_const))
    (fun u hu => analyticOn_expLift G k u hu.1) hu₃D hpar3 z ⟨hz, (hmemD z).mp hzc⟩
  rw [expP_eq G (G.mem_small hzc), expP_eq G (G.mem_small hz)]
  exact mk_eq_of_par _ _ hpar

end LSG.JacAn
