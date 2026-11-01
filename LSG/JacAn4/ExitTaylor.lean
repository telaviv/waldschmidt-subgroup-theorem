/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# A4.1b (S-c): leaving a hypersurface along a curve with a nonvanishing higher derivative

**`taylor_exit`**: if `h₀, …, h_K : ℝ → ℂ` satisfy `h_j' = h_{j+1}` on `(−ε, ε)` (`j < K`), `h_j(0) = 0` (`j < K`),
`h_K` is continuous at `0` and `h_K(0) ≠ 0`, then `h₀(t) ≠ 0` for small `t ≠ 0`.
The proof compares `h_{K−m}` with `t^m h_K(0)/m!` (error `≤ η |h_K(0)| |t|^m`, `η = 1/(2 K!)`) by the mean value
inequality, `m = 0, …, K`.
-/

open Set Filter Topology

namespace LSG.JacAn

lemma hasDerivAt_powFact (m : ℕ) (c : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (((s ^ (m + 1) / (m + 1).factorial : ℝ)) : ℂ) * c)
      ((((s ^ m / m.factorial : ℝ)) : ℂ) * c) s := by
  have h := ((hasDerivAt_pow (m + 1) s).div_const ((m + 1).factorial : ℝ)).ofReal_comp.mul_const c
  convert h using 2
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hm1 : ((m + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
  push_cast [Nat.factorial_succ]
  field_simp

lemma abs_le_of_mem_uIcc0 {s t : ℝ} (hs : s ∈ uIcc 0 t) : |s| ≤ |t| := by
  rw [mem_uIcc] at hs
  refine abs_le.mpr ⟨?_, ?_⟩ <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    linarith [le_abs_self t, neg_abs_le t, abs_nonneg t]

/-- **Exit along a curve with a nonvanishing higher derivative.** -/
theorem taylor_exit {K : ℕ} {h : ℕ → ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ j < K, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (h j) (h (j + 1) t) t) (hc : ContinuousAt (h K) 0)
    (h0 : ∀ j < K, h j 0 = 0) (hK : h K 0 ≠ 0) : ∃ δ > 0, ∀ t : ℝ, t ≠ 0 → |t| < δ → h 0 t ≠ 0 := by
  set c := h K 0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hK
  set η : ℝ := 1 / (2 * K.factorial)
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.continuousAt_iff.mp hc (η * ‖c‖) (by positivity)
  set δ := min ε δ₁
  have hδ : 0 < δ := lt_min hε hδ₁
  have claim : ∀ m ≤ K, ∀ t : ℝ, |t| < δ →
      ‖h (K - m) t - (((t ^ m / m.factorial : ℝ)) : ℂ) * c‖ ≤ η * ‖c‖ * |t| ^ m := by
    intro m
    induction m with
    | zero =>
      intro _ t ht
      have := hb (x := t) (by rw [Real.dist_eq, sub_zero]; exact ht.trans_le (min_le_right _ _))
      rw [dist_eq_norm] at this
      simpa using this.le
    | succ m ih =>
      intro hm t ht
      set j := K - (m + 1)
      have hj1 : j + 1 = K - m := by omega
      have hjK : j < K := by omega
      set g : ℝ → ℂ := fun s => h j s - (((s ^ (m + 1) / (m + 1).factorial : ℝ)) : ℂ) * c
      have hsub : uIcc 0 t ⊆ Ioo (-ε) ε := fun s hs => by
        have hst : |s| ≤ |t| := abs_le_of_mem_uIcc0 hs
        have := ht.trans_le (min_le_left ε δ₁)
        constructor <;> linarith [neg_abs_le s, le_abs_self s]
      have hgd : ∀ s ∈ uIcc 0 t, HasDerivWithinAt g
          (h (K - m) s - (((s ^ m / m.factorial : ℝ)) : ℂ) * c) (uIcc 0 t) s := fun s hs => by
        have h1 := hd j hjK s (hsub hs)
        rw [hj1] at h1
        exact (h1.sub (hasDerivAt_powFact m c s)).hasDerivWithinAt
      have hbound : ∀ s ∈ uIcc 0 t,
          ‖h (K - m) s - (((s ^ m / m.factorial : ℝ)) : ℂ) * c‖ ≤ η * ‖c‖ * |t| ^ m := fun s hs => by
        have hst : |s| ≤ |t| := abs_le_of_mem_uIcc0 hs
        refine (ih (by omega) s (hst.trans_lt ht)).trans ?_
        gcongr
      have hmv := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hgd hbound
        left_mem_uIcc right_mem_uIcc
      have hg0 : g 0 = 0 := by simp [g, h0 j hjK]
      rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
      calc ‖h (K - (m + 1)) t - (((t ^ (m + 1) / (m + 1).factorial : ℝ)) : ℂ) * c‖ = ‖g t‖ := rfl
        _ ≤ η * ‖c‖ * |t| ^ m * |t| := hmv
        _ = η * ‖c‖ * |t| ^ (m + 1) := by ring
  refine ⟨δ, hδ, fun t ht0 ht hzero => ?_⟩
  have h1 := claim K le_rfl t ht
  rw [Nat.sub_self, hzero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_pow, Nat.abs_cast] at h1
  have htp : 0 < |t| ^ K := pow_pos (abs_pos.mpr ht0) K
  have hKf : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have : |t| ^ K / K.factorial * ‖c‖ ≤ (1 / (2 * K.factorial)) * ‖c‖ * |t| ^ K := h1
  have h2 : |t| ^ K / K.factorial * ‖c‖ = 2 * ((1 / (2 * K.factorial)) * ‖c‖ * |t| ^ K) := by
    field_simp
  nlinarith [mul_pos (mul_pos (by positivity : (0 : ℝ) < 1 / (2 * K.factorial)) hcpos) htp]

end LSG.JacAn
