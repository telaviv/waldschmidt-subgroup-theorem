/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.TaylorK

/-!
# Algebraic Taylor coefficients of solutions of quadratic ODEs (STAGE_A3 §3.2)

The `n`-dimensional analogue of `ks_wpSeries` (`WpSeries.lean`): if `V : Fin n → ℂ → ℂ` is analytic at `0` with
`V_l' = Σ_{a,b} q_{lab} V_a V_b` near `0`, the coefficients `q_{lab}` have size `(H, d_q)` and the initial values
`V_l(0)` have size `(A, E)` (in a number field `K ↪ ℂ`), then every `V_l` is `KS ι A B E (d_q E)` as soon as
`1 ≤ A`, `1 ≤ B` and `n² H A ≤ B`:
the `j`-th Taylor coefficient has house `≤ A Bʲ` and denominator `E (d_q E)ʲ j!`.

* `tco_finsum`, `analyticAt_finsum`;
* **`ks_quadODE`**.
-/

open Finset Filter Topology

noncomputable section

namespace LSG.Aux

lemma analyticAt_finsum {α : Type*} (s : Finset α) {f : α → ℂ → ℂ} (hf : ∀ a ∈ s, AnalyticAt ℂ (f a) 0) :
    AnalyticAt ℂ (fun x => ∑ a ∈ s, f a x) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (analyticAt_const (v := (0 : ℂ)))
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun b hb => hf b (mem_insert_of_mem hb))

lemma tco_finsum {α : Type*} (s : Finset α) {f : α → ℂ → ℂ} (hf : ∀ a ∈ s, AnalyticAt ℂ (f a) 0) (j : ℕ) :
    tco j (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, tco j (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tco_const]
  | insert a s ha ih =>
    have hs : ∀ b ∈ s, AnalyticAt ℂ (f b) 0 := fun b hb => hf b (mem_insert_of_mem hb)
    have he : (fun x => ∑ b ∈ insert a s, f b x) = f a + fun x => ∑ b ∈ s, f b x := by
      funext x; simp [sum_insert ha]
    rw [he, tco_add (hf a (mem_insert_self a s)) (analyticAt_finsum s hs), ih hs, sum_insert ha]

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- **Taylor coefficients of a quadratic ODE system.** -/
theorem ks_quadODE {n : ℕ} {V : Fin n → ℂ → ℂ} (hV : ∀ l, AnalyticAt ℂ (V l) 0)
    {q : Fin n → Fin n → Fin n → ℂ}
    (hODE : ∀ l, deriv (V l) =ᶠ[𝓝 0] fun s => ∑ a, ∑ b, q l a b * (V a s * V b s))
    {H A B : ℝ} {E dq : ℕ} (hq : ∀ l a b, Sz ι H dq (q l a b)) (h0 : ∀ l, Sz ι A E (V l 0))
    (hA : 1 ≤ A) (hB1 : 1 ≤ B) (hB : (n : ℝ) ^ 2 * H * A ≤ B) :
    ∀ l, KS ι A B E (dq * E) (V l) := by
  intro l₀
  have hH : 0 ≤ H := (hq l₀ l₀ l₀).nonneg
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have key : ∀ j, ∀ l, Sz ι (A * B ^ j) (E * (dq * E) ^ j * j.factorial) (tco j (V l)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro l
      rcases j with _ | j
      · simpa [tco] using h0 l
      · have hpos : (0 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
        -- the recursion
        have han : ∀ a b, AnalyticAt ℂ (fun s => q l a b * (V a s * V b s)) 0 := fun a b =>
          analyticAt_const.mul ((hV a).mul (hV b))
        have hinner : ∀ a, AnalyticAt ℂ (fun s => ∑ b, q l a b * (V a s * V b s)) 0 := fun a =>
          analyticAt_finsum _ fun b _ => han a b
        have hrec : ((j + 1 : ℕ) : ℂ) * tco (j + 1) (V l) =
            ∑ a, ∑ b, q l a b * ∑ i ∈ range (j + 1), tco i (V a) * tco (j - i) (V b) := by
          have h1 := tco_deriv (V l) j
          rw [tco_congr (hODE l), tco_finsum _ (fun a _ => hinner a)] at h1
          push_cast
          rw [← h1]
          refine sum_congr rfl fun a _ => ?_
          rw [tco_finsum _ (fun b _ => han a b)]
          refine sum_congr rfl fun b _ => ?_
          rw [tco_const_mul]
          have hm := tco_mul (hV a) (hV b) j
          simp only [Pi.mul_def] at hm
          rw [hm]
        have hj1 : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have heq : tco (j + 1) (V l) =
            (∑ a, ∑ b, q l a b * ∑ i ∈ range (j + 1), tco i (V a) * tco (j - i) (V b)) /
              ((j + 1 : ℕ) : ℂ) := by
          rw [← hrec]; field_simp
        -- sizes
        have hterm : ∀ a b, ∀ i ∈ range (j + 1), Sz ι (H * (A * A * B ^ j))
            (dq * (E * E * (dq * E) ^ j * j.factorial)) (q l a b * (tco i (V a) * tco (j - i) (V b))) := by
          intro a b i hi
          have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
          refine ((hq l a b).mul ((ih i (by omega) a).mul (ih (j - i) (by omega) b))).mono
            (le_of_eq ?_) ?_
          · have : B ^ j = B ^ i * B ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
            rw [this]; ring
          · have hδ : (dq * E) ^ j = (dq * E) ^ i * (dq * E) ^ (j - i) := by
              rw [← pow_add, Nat.add_sub_cancel' hij]
            obtain ⟨r, hr⟩ := Nat.factorial_mul_factorial_dvd_factorial hij
            refine ⟨r, ?_⟩
            rw [hδ, hr]; ring
        have hsum : Sz ι (∑ a : Fin n, ∑ b : Fin n, ∑ i ∈ range (j + 1), H * (A * A * B ^ j))
            (dq * (E * E * (dq * E) ^ j * j.factorial))
            (∑ a, ∑ b, q l a b * ∑ i ∈ range (j + 1), tco i (V a) * tco (j - i) (V b)) := by
          refine Sz.sum _ fun a _ => Sz.sum _ fun b _ => ?_
          rw [mul_sum]
          exact Sz.sum _ fun i hi => hterm a b i hi
        have h1 := hsum.div_nat (n := j + 1) (by omega)
        rw [heq]
        refine h1.mono ?_ ?_
        · simp only [sum_const, card_range, card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [div_le_iff₀ hpos]
          have hAB : 0 ≤ A * B ^ j := by positivity
          have h2 : (n : ℝ) * ((n : ℝ) * (((j + 1 : ℕ) : ℝ) * (H * (A * A * B ^ j)))) =
              ((n : ℝ) ^ 2 * H * A) * (A * B ^ j) * ((j + 1 : ℕ) : ℝ) := by ring
          rw [h2]
          have h3 : ((n : ℝ) ^ 2 * H * A) * (A * B ^ j) ≤ B * (A * B ^ j) :=
            mul_le_mul_of_nonneg_right hB hAB
          calc ((n : ℝ) ^ 2 * H * A) * (A * B ^ j) * ((j + 1 : ℕ) : ℝ)
              ≤ B * (A * B ^ j) * ((j + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h3 hpos.le
            _ = A * B ^ (j + 1) * ((j + 1 : ℕ) : ℝ) := by ring
        · refine ⟨1, ?_⟩
          rw [Nat.factorial_succ]; ring
  exact ⟨hV l₀, fun j => key j l₀⟩

end LSG.Aux
