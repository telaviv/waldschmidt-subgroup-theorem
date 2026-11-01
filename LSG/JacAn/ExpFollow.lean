/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.ExpHom
import LSG.JacAn.Follow

/-!
# The a6 plug-in: `E` follows moving divisors

Let `t ↦ D(t) = (u₁(t), Y₁(t)) + (u₂(t), Y₂(t))` be a continuous path of generic divisors on `y² = 4x⁵ + 1` starting at
the base pair `p`, with path Abel integrals `A₁, A₂` (`Continuation.lean`), and `A = A₁ + A₂`. Then

  **`follow_trans`**: `T(A(t)) ∥ grantJ (mumfordPts D(t))` for all `t ∈ [0, 1]`,

where `T w = law0 (Ẽ w) P₀` (i.e. `E(A(t)) ⊕ P₀ = [D(t)]`), under the nondegeneracy `T(A(t)) ≠ 0` along the path
(`law0` vanishes exactly when `E(A(t)) − P₀ ∈ Θ`, a complex-codimension-1 condition that a generic path avoids).
Proof: the set of good times is closed (continuity) and open: near a good time `s`, `normalize 0 ∘ T(A(s) + ·)` and the
local exponential based at `D(s)` are chart-0 flow solutions with the same value at `0` ((U)), and `localExp_follow`
identifies the latter along the path.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

lemma Par.zero_ne {X Y : P9} (h : Par X Y) (hY : Y 0 = 1) (hX : X ≠ 0) : X 0 ≠ 0 := by
  intro h0
  apply hX
  funext a
  have := h a 0
  rw [h0, hY] at this
  simpa using this

lemma Par.normalize_eq {X Y : P9} (h : Par X Y) (hY : Y 0 = 1) (hX0 : X 0 ≠ 0) : normalize 0 X = Y := by
  have he : X = (X 0 / Y 0) • Y := h.symm.eq_smul (by rw [hY]; exact one_ne_zero)
  rw [hY, div_one] at he
  rw [normalize, he]
  simp [smul_smul, hX0, hY]

lemma grantJ_zero (m : Fin 4 → ℂ) : grantJ m 0 = 1 := by simp [grantJ]

lemma continuous_grantJ : Continuous grantJ := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [grantJ] <;> simp <;> fun_prop

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

/-- **The a6 plug-in**: `E` (translated by `P₀`) follows a moving generic divisor. -/
theorem follow_trans (k : ℕ) {u₁ Y₁ u₂ Y₂ : ℝ → ℂ} {A₁ A₂ : ℝ → (Fin 2 → ℂ)}
    (hA₁ : IsAbelAlong f₅ 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f₅ 2 u₂ Y₂ A₂) (hA₁0 : A₁ 0 = 0) (hA₂0 : A₂ 0 = 0)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hY₁ : ContinuousOn Y₁ (Icc 0 1)) (hY₂ : ContinuousOn Y₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t)
    (hstart : mumfordPts (u₁ 0) (Y₁ 0) (u₂ 0) (Y₂ 0) = mumford B₁ B₂ p)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, A₁ t + A₂ t ∈ ball (0 : Fin 2 → ℂ) (2 ^ k * G.ε))
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, transP (A := A) (hp := hp) (hx := hx) k (A₁ t + A₂ t) ≠ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, Par (transP (A := A) (hp := hp) (hx := hx) k (A₁ t + A₂ t))
      (grantJ (mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t))) := by
  obtain ⟨a₀, ha₀, hTz⟩ := transP_zero G k
  set R := 2 ^ k * G.ε
  set T := transP (A := A) (hp := hp) (hx := hx) k
  set Ab : ℝ → (Fin 2 → ℂ) := fun t => A₁ t + A₂ t
  set Dm : ℝ → P9 := fun t => grantJ (mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t))
  have hAc : ContinuousOn Ab (Icc 0 1) := (hA₁.continuousOn hu₁).add (hA₂.continuousOn hu₂)
  have hTan : ∀ w ∈ ball (0 : Fin 2 → ℂ) R, AnalyticAt ℂ T w := fun w hw => analyticOn_transP G k w hw
  -- continuity of both sides on `[0, 1]`
  have hTc : ContinuousOn (fun t => T (Ab t)) (Icc 0 1) := fun t ht =>
    (hTan _ (hU t ht)).continuousAt.comp_continuousWithinAt (f := Ab) (hAc t ht)
  have hDc : ContinuousOn Dm (Icc 0 1) := by
    intro t ht
    have hd : u₁ t - u₂ t ≠ 0 := sub_ne_zero.mpr (hdiag t ht)
    have h1 := hu₁ t ht; have h2 := hu₂ t ht; have h3 := hY₁ t ht; have h4 := hY₂ t ht
    have hm : ContinuousWithinAt (fun t => mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t)) (Icc 0 1) t := by
      rw [continuousWithinAt_pi]
      intro i
      fin_cases i
      · exact h1.add h2
      · exact h1.mul h2
      · exact (h3.sub h4).div (h1.sub h2) hd
      · exact ((h1.mul h4).sub (h2.mul h3)).div (h1.sub h2) hd
    exact continuous_grantJ.continuousAt.comp_continuousWithinAt hm
  -- the set of good times, on the subtype `[0, 1]`
  have hpc := Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  set S : Set (Icc (0 : ℝ) 1) := {t | Par (T (Ab t)) (Dm t)}
  have hcl : IsClosed S := by
    have hS : S = ⋂ a : Fin 9, ⋂ b : Fin 9,
        {t : Icc (0 : ℝ) 1 | T (Ab t) a * Dm t b = T (Ab t) b * Dm t a} := by
      ext t; simp [S, Par]
    rw [hS]
    have cT : ∀ a, Continuous (fun t : Icc (0 : ℝ) 1 => T (Ab t) a) := fun a =>
      (continuous_apply a).comp hTc.domRestrict
    have cD : ∀ a, Continuous (fun t : Icc (0 : ℝ) 1 => Dm t a) := fun a =>
      (continuous_apply a).comp hDc.domRestrict
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ((cT a).mul (cD b)) ((cT b).mul (cD a))
  have hop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 := s.2
    have hTs : T (Ab s) ≠ 0 := hT s hsI
    have hT0 : T (Ab s) 0 ≠ 0 := Par.zero_ne hs (grantJ_zero _) hTs
    obtain ⟨B₁', B₂', hp', hY1, hY2, hev⟩ :=
      localExp_follow hA₁ hA₂ hu₁ hu₂ hdiag hsI
    set p' : ℂ × ℂ := (u₁ s, u₂ s)
    have hx' : p'.1 ≠ p'.2 := hdiag s hsI
    -- the two flow solutions near `0`
    have hUo : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), w + Ab s ∈ ball (0 : Fin 2 → ℂ) R := by
      have hc : ContinuousAt (fun w : Fin 2 → ℂ => w + Ab s) 0 := (continuous_id.add continuous_const).continuousAt
      have : ball (0 : Fin 2 → ℂ) R ∈ 𝓝 ((fun w : Fin 2 → ℂ => w + Ab s) 0) := by
        simpa using isOpen_ball.mem_nhds (hU s hsI)
      exact hc.preimage_mem_nhds this
    have hne0 : ∀ᶠ w in 𝓝 (0 : Fin 2 → ℂ), T (w + Ab s) 0 ≠ 0 := by
      have hc : ContinuousAt (fun w : Fin 2 → ℂ => T (w + Ab s) 0) 0 := by
        have h1 : ContinuousAt T (0 + Ab s) := by rw [zero_add]; exact (hTan _ (hU s hsI)).continuousAt
        exact (continuous_apply 0).continuousAt.comp
          (h1.comp_of_eq (continuous_id.add continuous_const).continuousAt rfl)
      exact hc.eventually_ne (by simpa using hT0)
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hUo.and hne0).and (eventually_psi_flow_onQ A hp' hx'))
    have hsol : ∀ w ∈ ball (0 : Fin 2 → ℂ) ρ,
        normalize 0 (T (w + Ab s)) = psiJ hp' hx' (abel2 B₁' B₂' p' + w) := by
      refine flow_unique flowW contDiff_flowW 1 (fun w hw => ?_) (fun w hw => (hball w hw).2.1.2) ?_
      · obtain ⟨⟨hwU, hw0⟩, -⟩ := hball w hw
        have hPF := (PF0_transP G k _ hwU).comp_add (hTan _ hwU).differentiableAt
        have hd : DifferentiableAt ℂ (fun w => T (w + Ab s)) w :=
          ((hTan _ hwU).comp_of_eq (analyticAt_id.add analyticAt_const) rfl).differentiableAt
        exact hPF.hasFDerivAt_normalize flowW_smul hd hw0
      · rw [zero_add, add_zero]
        rw [Par.normalize_eq hs (grantJ_zero _) hT0]
        simp only [Dm, psiJ, localExp_abel2_self, mumford_eq_mumfordPts]
        show grantJ (mumfordPts (u₁ s) (Y₁ s) (u₂ s) (Y₂ s)) =
          grantJ (mumfordPts (u₁ s) (B₁'.Y (u₁ s)) (u₂ s) (B₂'.Y (u₂ s)))
        rw [hY1, hY2]
    -- along the path
    have hAs : ∀ᶠ t in 𝓝[Icc 0 1] (s : ℝ), Ab t - Ab s ∈ ball (0 : Fin 2 → ℂ) ρ := by
      have hc : ContinuousWithinAt (fun t => Ab t - Ab s) (Icc 0 1) s :=
        (hAc s hsI).sub continuousWithinAt_const
      have : ball (0 : Fin 2 → ℂ) ρ ∈ 𝓝 ((fun t => Ab t - Ab s) (s : ℝ)) := by
        simpa using ball_mem_nhds (0 : Fin 2 → ℂ) hρ
      exact hc.preimage_mem_nhdsWithin this
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.mp (hAs.and hev)
    have hn : {t : Icc (0 : ℝ) 1 | (t : ℝ) ∈ ball (s : ℝ) δ} ∈ 𝓝 s :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ)
    filter_upwards [hn] with t ht
    obtain ⟨hAt, hloc⟩ := hδb ⟨ht, t.2⟩
    have h := hsol _ hAt
    rw [sub_add_cancel] at h
    show Par (T (Ab t)) (Dm t)
    have hD : Dm t = psiJ hp' hx' (abel2 B₁' B₂' p' + (Ab t - Ab s)) := by
      simp only [Dm, psiJ]
      rw [← hloc]
    rw [hD, ← h]
    exact (par_normalize 0 _).symm
  have h0S : (⟨0, by simp⟩ : Icc (0 : ℝ) 1) ∈ S := by
    show Par (T (Ab 0)) (Dm 0)
    simp only [Ab, hA₁0, hA₂0, add_zero]
    rw [hTz]
    refine Par.smul_left _ ?_
    simp only [Dm, hstart, baseP, psiJ, localExp_abel2_self]
    exact par_self _
  have hSu : S = univ := by
    rcases isClopen_iff.mp ⟨hcl, hop⟩ with h | h
    · exact absurd (h ▸ h0S) (Set.notMem_empty _)
    · exact h
  intro t ht
  have : (⟨t, ht⟩ : Icc (0 : ℝ) 1) ∈ S := hSu ▸ mem_univ _
  exact this

end LSG.JacAn
