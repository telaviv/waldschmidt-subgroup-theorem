/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.TaylorK
import LSG.Weierstrass.Basic

/-!
# Taylor coefficients of `℘` at the half period `z₀ = ω₁/2` (Stage 3, D3)

For `c ∈ ℂ` put `P_c(s) = ℘(z₀ + c s)`, `Q_c(s) = ℘'(z₀ + c s)`. Near `s = 0`,
`P_c' = c Q_c` and `Q_c' = c (6 P_c² − g₂/2)`, with `P_c(0) = e₁ = ℘(z₀)`, `Q_c(0) = 0`. The Taylor
coefficients satisfy

  `(j+1) p_{j+1} = c q_j`,   `(j+1) q_{j+1} = c (6 Σ_{i ≤ j} p_i p_{j−i} − (g₂/2)[j = 0])`,

so, if `c, e₁, g₂/2` lie in a number field `K`, the coefficients are in `K` with
`house ≤ A Bʲ` and denominators `E (E²)ʲ j!` (`KS`), `B` linear in `house c`
(**`ks_wpSeries`**). This replaces Bertrand's Lemma 7 (W_UPGRADE §1.2(b)) for elliptic factors.
-/

open Complex Finset Filter Topology PeriodPair

noncomputable section

namespace LSG.Aux

variable (L : PeriodPair)

/-- The base point `z₀ = ω₁/2`. -/
def zh : ℂ := L.ω₁ / 2

lemma zh_notMem : zh L ∉ L.lattice := L.ω₁_div_two_notMem_lattice

lemma derivWp_zh : ℘'[L] (zh L) = 0 := LSG.Weierstrass.derivWeierstrassP_half L L.ω₁_mem_lattice

/-- `P_c(s) = ℘(z₀ + c s)`. -/
def wpP (c : ℂ) (s : ℂ) : ℂ := ℘[L] (zh L + c * s)

/-- `Q_c(s) = ℘'(z₀ + c s)`. -/
def wpQ (c : ℂ) (s : ℂ) : ℂ := ℘'[L] (zh L + c * s)

lemma eventually_notMem (c : ℂ) : ∀ᶠ s in 𝓝 (0 : ℂ), zh L + c * s ∉ L.lattice := by
  have hc : Continuous fun s : ℂ => zh L + c * s := by fun_prop
  have := hc.continuousAt (x := 0) |>.preimage_mem_nhds
    ((LSG.Weierstrass.isOpen_compl_lattice L).mem_nhds (by simpa using zh_notMem L))
  exact this

lemma analyticAt_wpP (c : ℂ) : AnalyticAt ℂ (wpP L c) 0 := by
  have h := L.analyticOnNhd_weierstrassP (zh L) (zh_notMem L)
  exact h.comp_of_eq (by fun_prop) (by simp)

lemma analyticAt_wpQ (c : ℂ) : AnalyticAt ℂ (wpQ L c) 0 := by
  have h := L.analyticOnNhd_derivWeierstrassP (zh L) (zh_notMem L)
  exact h.comp_of_eq (by fun_prop) (by simp)

lemma deriv_wpP (c : ℂ) : deriv (wpP L c) =ᶠ[𝓝 0] fun s => c * wpQ L c s := by
  filter_upwards [eventually_notMem L c] with s hs
  have h1 := LSG.Weierstrass.hasDerivAt_weierstrassP L hs
  have h2 : HasDerivAt (fun s : ℂ => zh L + c * s) c s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_add (zh L)
  have := h1.comp s h2
  rw [show (wpP L c) = ℘[L] ∘ fun s => zh L + c * s from rfl, this.deriv, wpQ]; ring

lemma deriv_wpQ (c : ℂ) :
    deriv (wpQ L c) =ᶠ[𝓝 0] fun s => c * (6 * (wpP L c s * wpP L c s) + (-(L.g₂ / 2))) := by
  filter_upwards [eventually_notMem L c] with s hs
  have h1 := LSG.Weierstrass.hasDerivAt_derivWeierstrassP L hs
  have h2 : HasDerivAt (fun s : ℂ => zh L + c * s) c s := by
    simpa using ((hasDerivAt_id s).const_mul c).const_add (zh L)
  have := h1.comp s h2
  rw [show (wpQ L c) = ℘'[L] ∘ fun s => zh L + c * s from rfl, this.deriv, wpP]; ring

lemma tco_wpP_succ (c : ℂ) (j : ℕ) : (j + 1) * tco (j + 1) (wpP L c) = c * tco j (wpQ L c) := by
  rw [← tco_deriv, tco_congr (deriv_wpP L c), tco_const_mul]

lemma tco_wpQ_succ (c : ℂ) (j : ℕ) : (j + 1) * tco (j + 1) (wpQ L c) =
    c * (6 * ∑ i ∈ range (j + 1), tco i (wpP L c) * tco (j - i) (wpP L c) -
      if j = 0 then L.g₂ / 2 else 0) := by
  rw [← tco_deriv, tco_congr (deriv_wpQ L c), tco_const_mul]
  have ha := analyticAt_wpP L c
  have h6 : AnalyticAt ℂ (fun s => 6 * (wpP L c s * wpP L c s)) 0 :=
    analyticAt_const.mul (ha.mul ha)
  have := tco_add h6 (analyticAt_const (v := -(L.g₂ / 2))) j
  simp only [Pi.add_def] at this
  rw [this, tco_const_mul, tco_const]
  have hm := tco_mul ha ha j
  simp only [Pi.mul_def] at hm
  rw [hm]
  split_ifs <;> ring

lemma tco_wpP_zero (c : ℂ) : tco 0 (wpP L c) = ℘[L] (zh L) := by simp [tco, wpP]

lemma tco_wpQ_zero (c : ℂ) : tco 0 (wpQ L c) = 0 := by simp [tco, wpQ, derivWp_zh]

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- **Sizes of the Taylor coefficients of `℘(z₀ + c s)` and `℘'(z₀ + c s)`.** -/
theorem ks_wpSeries {c : ℂ} {Hc Ae Ag A B : ℝ} {E : ℕ} (hc : Sz ι Hc E c)
    (he : Sz ι Ae E (℘[L] (zh L))) (hg : Sz ι Ag (E ^ 2) (L.g₂ / 2)) (hA : 1 ≤ A) (hAe : Ae ≤ A)
    (hB1 : 1 ≤ B) (hB : Hc * (6 * A + Ag) ≤ B) :
    KS ι A B E (E ^ 2) (wpP L c) ∧ KS ι A B E (E ^ 2) (wpQ L c) := by
  have hHc : 0 ≤ Hc := hc.nonneg
  have hAg : 0 ≤ Ag := hg.nonneg
  have hBc : Hc ≤ B := by nlinarith
  -- the joint statement
  have key : ∀ j, Sz ι (A * B ^ j) (E * (E ^ 2) ^ j * j.factorial) (tco j (wpP L c)) ∧
      Sz ι (A * B ^ j) (E * (E ^ 2) ^ j * j.factorial) (tco j (wpQ L c)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases j with _ | j
      · refine ⟨?_, ?_⟩
        · rw [tco_wpP_zero]; simpa using he.mono_le hAe
        · rw [tco_wpQ_zero]; exact (Sz.zero _).mono_le (by simpa using by linarith)
      · have hj1 : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have hpos : (0 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
        refine ⟨?_, ?_⟩
        · -- `p_{j+1} = c q_j / (j+1)`
          have hq := (ih j (Nat.lt_succ_self j)).2
          have h1 := (hc.mul hq).div_nat (n := j + 1) (by omega)
          have heq : tco (j + 1) (wpP L c) = c * tco j (wpQ L c) / ((j + 1 : ℕ) : ℂ) := by
            rw [← tco_wpP_succ]; push_cast; field_simp
          rw [heq]
          refine h1.mono ?_ ?_
          · rw [div_le_iff₀ hpos]
            have h0 : 0 ≤ A * B ^ j := by positivity
            have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero j)
            have h2 : 0 ≤ A * B ^ (j + 1) := by positivity
            calc Hc * (A * B ^ j) ≤ B * (A * B ^ j) := mul_le_mul_of_nonneg_right hBc h0
              _ = A * B ^ (j + 1) * 1 := by ring
              _ ≤ A * B ^ (j + 1) * ((j + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hj1 h2
          · refine ⟨E, ?_⟩
            rw [Nat.factorial_succ]; ring
        · -- `q_{j+1} = c (6 Σ p_i p_{j−i} − [j=0] g₂/2) / (j+1)`
          have hsum : Sz ι (∑ i ∈ range (j + 1), A * A * B ^ j) (E ^ 2 * (E ^ 2) ^ j * j.factorial)
              (∑ i ∈ range (j + 1), tco i (wpP L c) * tco (j - i) (wpP L c)) := by
            refine Sz.sum _ fun i hi => ?_
            have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
            have hi' := (ih i (by omega)).1
            have hk' := (ih (j - i) (by omega)).1
            refine (hi'.mul hk').mono (le_of_eq ?_) ?_
            · have : B ^ j = B ^ i * B ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
              rw [this]; ring
            · have hδ : (E ^ 2) ^ j = (E ^ 2) ^ i * (E ^ 2) ^ (j - i) := by
                rw [← pow_add, Nat.add_sub_cancel' hij]
              obtain ⟨q, hq⟩ := Nat.factorial_mul_factorial_dvd_factorial hij
              refine ⟨q, ?_⟩
              rw [hδ, hq]; ring
          have hg' : Sz ι (if j = 0 then Ag else 0) (E ^ 2 * (E ^ 2) ^ j * j.factorial)
              (if j = 0 then L.g₂ / 2 else 0) := by
            split_ifs with hj
            · subst hj; simpa using hg
            · exact Sz.zero _
          have hinner := (hsum.nat_mul 6).sub hg'
          have h1 := (hc.mul hinner).div_nat (n := j + 1) (by omega)
          have heq : tco (j + 1) (wpQ L c) = c * ((6 : ℕ) * ∑ i ∈ range (j + 1),
              tco i (wpP L c) * tco (j - i) (wpP L c) - if j = 0 then L.g₂ / 2 else 0) /
                ((j + 1 : ℕ) : ℂ) := by
            have := tco_wpQ_succ L c j
            push_cast
            field_simp
            linear_combination this
          rw [heq]
          refine h1.mono ?_ ?_
          · rw [div_le_iff₀ hpos, sum_const, card_range, nsmul_eq_mul]
            have hBj : 1 ≤ B ^ j := one_le_pow₀ hB1
            have hif : (if j = 0 then Ag else 0) ≤ Ag * B ^ j := by
              split_ifs
              · nlinarith
              · positivity
            have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero j)
            calc Hc * ((6 : ℕ) * (((j + 1 : ℕ) : ℝ) * (A * A * B ^ j)) +
                  (if j = 0 then Ag else 0))
                ≤ Hc * ((6 : ℕ) * (((j + 1 : ℕ) : ℝ) * (A * A * B ^ j)) +
                  ((j + 1 : ℕ) : ℝ) * (Ag * B ^ j)) := by
                  gcongr
                  calc (if j = 0 then Ag else 0) ≤ Ag * B ^ j := hif
                    _ = 1 * (Ag * B ^ j) := (one_mul _).symm
                    _ ≤ ((j + 1 : ℕ) : ℝ) * (Ag * B ^ j) := by gcongr
              _ = (Hc * (6 * A + Ag / A)) * A * B ^ j * ((j + 1 : ℕ) : ℝ) := by
                  push_cast; field_simp
              _ ≤ B * A * B ^ j * ((j + 1 : ℕ) : ℝ) := by
                  gcongr
                  calc Hc * (6 * A + Ag / A) ≤ Hc * (6 * A + Ag) := by
                        gcongr
                        exact div_le_self hAg hA
                    _ ≤ B := hB
              _ = A * B ^ (j + 1) * ((j + 1 : ℕ) : ℝ) := by ring
          · refine ⟨1, ?_⟩
            rw [Nat.factorial_succ]; ring
  exact ⟨⟨analyticAt_wpP L c, fun j => (key j).1⟩, ⟨analyticAt_wpQ L c, fun j => (key j).2⟩⟩

end LSG.Aux
