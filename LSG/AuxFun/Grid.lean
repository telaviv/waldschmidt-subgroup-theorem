/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Lagrange

/-!
# Interpolation on a Cartesian product grid in `ℂⁿ`

The replacement for W83's Lemma 2.3 on product grids (`STAGE3_D2.md`, O2): if an entire function
`F` on `ℂⁿ` (sup norm = W83's polydisc norm) is at most `ε` on the grid `Zⁿ`, `Z ⊂ D(0, r)`, and at
most `M` on the polydisc of radius `R`, then on the polydisc of radius `r`

  `|F| ≤ Cⁿ (ε + n q^{#Z} M)`,  `q = 2r/(R − r)`,

where `C ≥ #Z·Λ_r + #Z·Λ_R·q^{#Z}` (Lagrange constants as in `LSG.Aux.norm_le_interp`). The proof
frees one coordinate at a time, applying the one-variable estimate on the coordinate line
`w ↦ F (update z j w)`.

* `LSG.Aux.grid_interp`.
-/

open Complex Finset

namespace LSG.Aux

variable {n : ℕ}

lemma norm_update_le {z : Fin n → ℂ} {j : Fin n} {w : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖Function.update z j w‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg w).trans hw)).mpr fun i => ?_
  rcases eq_or_ne i j with rfl | h
  · simpa using hw
  · rw [Function.update_of_ne h]; exact (norm_le_pi_norm z i).trans hz

/-- **Interpolation on a product grid.** -/
theorem grid_interp (F : (Fin n → ℂ) → ℂ) (hF : Differentiable ℂ F) (Z : Finset ℂ)
    {r R ε M Λr ΛR C : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hZr : ∀ ζ ∈ Z, ‖ζ‖ ≤ r)
    (hΛr : ∀ ζ ∈ Z, ∀ w : ℂ, ‖w‖ ≤ r → ‖lagBasis Z ζ w‖ ≤ Λr)
    (hΛR : ∀ ζ ∈ Z, ∀ w : ℂ, ‖w‖ = R → ‖lagBasis Z ζ w‖ ≤ ΛR)
    (hC : Z.card * Λr + Z.card * ΛR * (2 * r / (R - r)) ^ Z.card ≤ C) (hC1 : 1 ≤ C)
    (hε0 : 0 ≤ ε) (hM0 : 0 ≤ M)
    (hgrid : ∀ g : Fin n → ℂ, (∀ j, g j ∈ Z) → ‖F g‖ ≤ ε)
    (hM : ∀ z : Fin n → ℂ, ‖z‖ ≤ R → ‖F z‖ ≤ M) {z : Fin n → ℂ} (hz : ‖z‖ ≤ r) :
    ‖F z‖ ≤ C ^ n * (ε + n * (2 * r / (R - r)) ^ Z.card * M) := by
  set q : ℝ := 2 * r / (R - r) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  -- the claim with the first `k` coordinates freed
  have key : ∀ k : ℕ, k ≤ n → ∀ z : Fin n → ℂ, ‖z‖ ≤ r → (∀ j : Fin n, k ≤ j.val → z j ∈ Z) →
      ‖F z‖ ≤ C ^ k * (ε + k * q ^ Z.card * M) := by
    intro k
    induction k with
    | zero =>
      intro _ z _ hzZ
      simpa using hgrid z fun j => hzZ j (Nat.zero_le _)
    | succ k ih =>
      intro hk z hz hzZ
      set j₀ : Fin n := ⟨k, hk⟩
      set εk : ℝ := C ^ k * (ε + k * q ^ Z.card * M) with hεk
      have hεk0 : 0 ≤ εk := by positivity
      let f : ℂ → ℂ := fun w => F (Function.update z j₀ w)
      have hf : Differentiable ℂ f := fun w =>
        (hF _).comp w (hasFDerivAt_update z w).differentiableAt
      have hfZ : ∀ ζ ∈ Z, ‖f ζ‖ ≤ εk := by
        intro ζ hζ
        refine ih (Nat.le_of_succ_le hk) _ (norm_update_le hz (hZr ζ hζ)) fun j hj => ?_
        rcases eq_or_ne j j₀ with rfl | hne
        · simpa using hζ
        · rw [Function.update_of_ne hne]
          refine hzZ j ?_
          have : j.val ≠ k := fun h => hne (Fin.ext h)
          omega
      have hfR : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M := fun w hw =>
        hM _ (norm_update_le (hz.trans hrR.le) hw.le)
      have h1 := norm_le_interp f hf Z hr hrR hZr hfZ hfR hΛr hΛR
        (show ‖z j₀‖ ≤ r from (norm_le_pi_norm z j₀).trans hz)
      have hfz : f (z j₀) = F z := by simp [f]
      rw [hfz] at h1
      calc ‖F z‖ ≤ Z.card * Λr * εk + (M + Z.card * ΛR * εk) * q ^ Z.card := h1
        _ = (Z.card * Λr + Z.card * ΛR * q ^ Z.card) * εk + q ^ Z.card * M := by ring
        _ ≤ C * εk + C ^ (k + 1) * (q ^ Z.card * M) :=
            add_le_add (mul_le_mul_of_nonneg_right hC hεk0)
              (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hC1))
        _ = C ^ (k + 1) * (ε + ((k + 1 : ℕ) : ℝ) * q ^ Z.card * M) := by
            rw [hεk]; push_cast; ring
  exact key n le_rfl z hz fun j hj => absurd j.isLt (by omega)

end LSG.Aux
