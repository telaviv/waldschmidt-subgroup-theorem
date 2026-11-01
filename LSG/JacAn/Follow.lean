/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.Continuation
import LSG.JacAn.Abel2

/-!
# The local exponential follows a moving divisor (exp-free half of a6, genus 2)

Let `t ↦ D(t) = (u₁(t), Y₁(t)) + (u₂(t), Y₂(t))`, `t ∈ [0, 1]`, be a continuous family of generic divisors
(`Yᵢ ≠ 0`, `u₁ ≠ u₂`) and `A₁, A₂` the Abel integrals along the two paths (`Continuation.lean`). Then near every
parameter `s` the local exponential based at `D(s)` maps `z(s) + (A(t) − A(s))` to the Mumford coordinates of `D(t)`
(`localExp_follow`), where `A = A₁ + A₂`.

This is the statement a4 plugs into: if the global `E` agrees near `z(s)` with `Ψ ∘ localExp` (up to the
translation `c_s`), then `t ↦ E(z₀ + A(t))` and `t ↦ Ψ(mumfordPts D(t))` agree near every `s`; both sides are
continuous, so `patch_unique`/`abelAlong_unique`-type connectedness on `[0, 1]` gives agreement for all `t`.
-/

noncomputable section

open Polynomial Metric Set Filter Topology

namespace LSG.JacAn

/-- Intrinsic Mumford coordinates `(s₁, s₂, b₁, b₀)` of `(x₁, y₁) + (x₂, y₂)`. -/
def mumfordPts (x₁ y₁ x₂ y₂ : ℂ) : Fin 4 → ℂ :=
  ![x₁ + x₂, x₁ * x₂, (y₁ - y₂) / (x₁ - x₂), (x₁ * y₂ - x₂ * y₁) / (x₁ - x₂)]

variable {f : ℂ[X]}

lemma mumford_eq_mumfordPts (B₁ B₂ : LocalBranch f 2) (q : ℂ × ℂ) :
    mumford B₁ B₂ q = mumfordPts q.1 (B₁.Y q.1) q.2 (B₂.Y q.2) := rfl

variable {u₁ Y₁ u₂ Y₂ : ℝ → ℂ} {A₁ A₂ : ℝ → (Fin 2 → ℂ)}

/-- **The local exponential follows the moving divisor.** -/
theorem localExp_follow (hA₁ : IsAbelAlong f 2 u₁ Y₁ A₁) (hA₂ : IsAbelAlong f 2 u₂ Y₂ A₂)
    (hu₁ : ContinuousOn u₁ (Icc 0 1)) (hu₂ : ContinuousOn u₂ (Icc 0 1))
    (hdiag : ∀ t ∈ Icc (0 : ℝ) 1, u₁ t ≠ u₂ t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ B₁ B₂ : LocalBranch f 2, ∃ hp : (u₁ s, u₂ s) ∈ dom2 B₁ B₂,
      B₁.Y (u₁ s) = Y₁ s ∧ B₂.Y (u₂ s) = Y₂ s ∧
      ∀ᶠ t in 𝓝[Icc 0 1] s,
        localExp hp (hdiag s hs) (abel2 B₁ B₂ (u₁ s, u₂ s) + ((A₁ t + A₂ t) - (A₁ s + A₂ s))) =
          mumfordPts (u₁ t) (Y₁ t) (u₂ t) (Y₂ t) := by
  obtain ⟨B₁, ε₁, hε₁, hB₁⟩ := hA₁ s hs
  obtain ⟨B₂, ε₂, hε₂, hB₂⟩ := hA₂ s hs
  have hs₁ := hB₁ s ⟨mem_ball_self hε₁, hs⟩
  have hs₂ := hB₂ s ⟨mem_ball_self hε₂, hs⟩
  have hp : (u₁ s, u₂ s) ∈ dom2 B₁ B₂ := ⟨hs₁.1, hs₂.1⟩
  refine ⟨B₁, B₂, hp, hs₁.2.1, hs₂.2.1, ?_⟩
  have hx := hdiag s hs
  -- the pair `t ↦ (u₁ t, u₂ t)` is continuous within `[0, 1]`
  have hcq : ContinuousWithinAt (fun t => (u₁ t, u₂ t)) (Icc 0 1) s := (hu₁ s hs).prodMk (hu₂ s hs)
  have hinv : ∀ᶠ t in 𝓝[Icc 0 1] s,
      abelInv hp hx (abel2 B₁ B₂ (u₁ t, u₂ t)) = (u₁ t, u₂ t) :=
    hcq.eventually (abelInv_abel2 hp hx)
  filter_upwards [hinv, inter_mem_nhdsWithin (Icc 0 1) (ball_mem_nhds s (lt_min hε₁ hε₂)),
    self_mem_nhdsWithin] with t ht hball htI
  have htb₁ : t ∈ ball s ε₁ := ball_subset_ball (min_le_left _ _) hball.2
  have htb₂ : t ∈ ball s ε₂ := ball_subset_ball (min_le_right _ _) hball.2
  have ht₁ := hB₁ t ⟨htb₁, htI⟩
  have ht₂ := hB₂ t ⟨htb₂, htI⟩
  have i₁ := hs₁.2.2 t ⟨htb₁, htI⟩
  have i₂ := hs₂.2.2 t ⟨htb₂, htI⟩
  have hz : abel2 B₁ B₂ (u₁ s, u₂ s) + ((A₁ t + A₂ t) - (A₁ s + A₂ s)) = abel2 B₁ B₂ (u₁ t, u₂ t) := by
    simp only [abel2]
    rw [sub_eq_iff_eq_add.mp i₁, sub_eq_iff_eq_add.mp i₂]; abel
  rw [hz]
  simp only [localExp, Function.comp, ht, mumford_eq_mumfordPts, ht₁.2.1, ht₂.2.1]

end LSG.JacAn
