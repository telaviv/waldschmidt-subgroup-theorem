/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Grid

/-!
# Interpolation on a product grid with a different node set in each coordinate

As `LSG.Aux.grid_interp`, with nodes `Z j ⊂ D(0, r)` in coordinate `j`, all of the same size
`Nn` and with uniform Lagrange constants. Used for Tier 2, where coordinate `j` carries a grid of
the lattice `ℤα_j + ℤβ_j`.

* `LSG.Aux.grid_interp2`.
-/

open Complex Finset

namespace LSG.Aux

variable {n : ℕ}

/-- **Interpolation on a product grid `Π_j Z j`.** -/
theorem grid_interp2 (F : (Fin n → ℂ) → ℂ) (hF : Differentiable ℂ F) (Z : Fin n → Finset ℂ)
    (Nn : ℕ) (hZc : ∀ j, (Z j).card = Nn)
    {r R ε M Λr ΛR C : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hZr : ∀ j, ∀ ζ ∈ Z j, ‖ζ‖ ≤ r)
    (hΛr : ∀ j, ∀ ζ ∈ Z j, ∀ w : ℂ, ‖w‖ ≤ r → ‖lagBasis (Z j) ζ w‖ ≤ Λr)
    (hΛR : ∀ j, ∀ ζ ∈ Z j, ∀ w : ℂ, ‖w‖ = R → ‖lagBasis (Z j) ζ w‖ ≤ ΛR)
    (hC : Nn * Λr + Nn * ΛR * (2 * r / (R - r)) ^ Nn ≤ C) (hC1 : 1 ≤ C)
    (hε0 : 0 ≤ ε) (hM0 : 0 ≤ M)
    (hgrid : ∀ g : Fin n → ℂ, (∀ j, g j ∈ Z j) → ‖F g‖ ≤ ε)
    (hM : ∀ z : Fin n → ℂ, ‖z‖ ≤ R → ‖F z‖ ≤ M) {z : Fin n → ℂ} (hz : ‖z‖ ≤ r) :
    ‖F z‖ ≤ C ^ n * (ε + n * (2 * r / (R - r)) ^ Nn * M) := by
  set q : ℝ := 2 * r / (R - r) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have key : ∀ k : ℕ, k ≤ n → ∀ z : Fin n → ℂ, ‖z‖ ≤ r → (∀ j : Fin n, k ≤ j.val → z j ∈ Z j) →
      ‖F z‖ ≤ C ^ k * (ε + k * q ^ Nn * M) := by
    intro k
    induction k with
    | zero =>
      intro _ z _ hzZ
      simpa using hgrid z fun j => hzZ j (Nat.zero_le _)
    | succ k ih =>
      intro hk z hz hzZ
      set j₀ : Fin n := ⟨k, hk⟩
      set εk : ℝ := C ^ k * (ε + k * q ^ Nn * M) with hεk
      have hεk0 : 0 ≤ εk := by positivity
      let f : ℂ → ℂ := fun w => F (Function.update z j₀ w)
      have hf : Differentiable ℂ f := fun w =>
        (hF _).comp w (hasFDerivAt_update z w).differentiableAt
      have hfZ : ∀ ζ ∈ Z j₀, ‖f ζ‖ ≤ εk := by
        intro ζ hζ
        refine ih (Nat.le_of_succ_le hk) _ (norm_update_le hz (hZr j₀ ζ hζ)) fun j hj => ?_
        rcases eq_or_ne j j₀ with rfl | hne
        · simpa using hζ
        · rw [Function.update_of_ne hne]
          refine hzZ j ?_
          have : j.val ≠ k := fun h => hne (Fin.ext h)
          omega
      have hfR : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M := fun w hw =>
        hM _ (norm_update_le (hz.trans hrR.le) hw.le)
      have h1 := norm_le_interp f hf (Z j₀) hr hrR (hZr j₀) hfZ hfR (hΛr j₀) (hΛR j₀)
        (show ‖z j₀‖ ≤ r from (norm_le_pi_norm z j₀).trans hz)
      have hfz : f (z j₀) = F z := by simp [f]
      rw [hfz, hZc j₀] at h1
      calc ‖F z‖ ≤ Nn * Λr * εk + (M + Nn * ΛR * εk) * q ^ Nn := h1
        _ = (Nn * Λr + Nn * ΛR * q ^ Nn) * εk + q ^ Nn * M := by ring
        _ ≤ C * εk + C ^ (k + 1) * (q ^ Nn * M) :=
            add_le_add (mul_le_mul_of_nonneg_right hC hεk0)
              (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hC1))
        _ = C ^ (k + 1) * (ε + ((k + 1 : ℕ) : ℝ) * q ^ Nn * M) := by
            rw [hεk]; push_cast; ring
  exact key n le_rfl z hz fun j hj => absurd j.isLt (by omega)

end LSG.Aux
