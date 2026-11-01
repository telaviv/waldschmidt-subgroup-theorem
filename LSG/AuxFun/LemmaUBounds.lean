/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUFac

/-!
# Lemma U: elementary bounds used in the parameter bookkeeping (Stage 3, D3b)

* `Sz.norm_le`: `|z| ≤ A` for `z` of size `(A, d)`.
* `pow_le_exp_of_log_le`, `log_mul_le_log_succ`, `factorial_le_exp`, `natPow_le_exp`.
* `prod_fct`: products over `Fct` of functions defined by cases.
* `contDiff_Psi`, `analyticAt_Psi_line`: smoothness of `Ψ = Σ p_l M_l`.
* `sz_natComb`, `sz_expComb`: sizes of `Σ hⱼ xⱼ` and `Π xⱼ^{hⱼ}`.
-/

open Complex Finset LSG.W88
open scoped ContDiff

noncomputable section

namespace LSG.Aux

variable {d0 d1 m D : ℕ}
variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

lemma Sz.norm_le {A : ℝ} {d : ℕ} {z : ℂ} (h : Sz ι A d z) : ‖z‖ ≤ A := by
  obtain ⟨x, rfl, hx, -⟩ := h
  exact (NumberField.norm_embedding_le_house x ι).trans hx

lemma pow_le_exp_of_log_le {x a : ℝ} (hx : 0 < x) (h : Real.log x ≤ a) (n : ℕ) :
    x ^ n ≤ Real.exp (n * a) := by
  rw [← Real.exp_log hx, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n))

lemma le_exp_of_log_le {x a : ℝ} (hx : 0 < x) (h : Real.log x ≤ a) : x ≤ Real.exp a := by
  rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr h

/-- `log (S a) ≤ (1 + log a / log 2) log (S + 1)` for `S ≥ 1`, `a ≥ 1`. -/
lemma log_mul_le_log_succ {S a : ℝ} (hS : 1 ≤ S) (ha : 1 ≤ a) :
    Real.log (S * a) ≤ (1 + Real.log a / Real.log 2) * Real.log (S + 1) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS1 : Real.log 2 ≤ Real.log (S + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  rw [Real.log_mul (by linarith) (by linarith)]
  have h1 : Real.log S ≤ Real.log (S + 1) := Real.log_le_log (by linarith) (by linarith)
  have h3 : Real.log a ≤ Real.log a / Real.log 2 * Real.log (S + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]
    exact mul_le_mul_of_nonneg_left hS1 hla
  nlinarith

lemma factorial_le_exp (k T : ℕ) (hk : k ≤ T) :
    (k.factorial : ℝ) ≤ Real.exp ((T + 1) * Real.log (T + 2)) := by
  have h1 : (k.factorial : ℝ) ≤ (T + 2 : ℝ) ^ (T + 1) := by
    have : k.factorial ≤ (T + 2) ^ (T + 1) := by
      calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
        _ ≤ (T + 2) ^ k := Nat.pow_le_pow_left (by omega) k
        _ ≤ (T + 2) ^ (T + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  refine h1.trans (le_of_eq ?_)
  rw [← Real.exp_log (by positivity : (0 : ℝ) < T + 2), ← Real.exp_nat_mul, Real.exp_log
    (by positivity)]
  push_cast; ring_nf

/-- `(c (T+1))^k ≤ exp ((1 + log c / log 2) (T + 1) log (T + 2))` for `k ≤ T`, `c ≥ 1`. -/
lemma natPow_le_exp {c : ℝ} (hc : 1 ≤ c) (k T : ℕ) (hk : k ≤ T) :
    (c * (T + 1)) ^ k ≤ Real.exp ((1 + Real.log c / Real.log 2) * ((T + 1) * Real.log (T + 2))) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT2 : Real.log 2 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num) (by linarith [
    (Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlog : Real.log (c * (T + 1)) ≤ (1 + Real.log c / Real.log 2) * Real.log (T + 2) := by
    rw [Real.log_mul (by linarith) (by positivity)]
    have h1 : Real.log (T + 1) ≤ Real.log (T + 2) := Real.log_le_log (by positivity) (by linarith)
    have h3 : Real.log c ≤ Real.log c / Real.log 2 * Real.log (T + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h2]
      exact mul_le_mul_of_nonneg_left hT2 hlc
    nlinarith
  refine (pow_le_exp_of_log_le (by positivity) hlog k).trans (Real.exp_le_exp.mpr ?_)
  have hk' : (k : ℝ) ≤ T + 1 := by exact_mod_cast (by omega : k ≤ T + 1)
  have h0 : 0 ≤ (1 + Real.log c / Real.log 2) * Real.log (T + 2) := by
    have : 0 ≤ Real.log (T + 2) := le_trans h2.le hT2
    positivity
  nlinarith

lemma prod_fct {M : Type*} [CommSemiring M] (a b c : M) (A₀ A₁ N : ℕ) :
    ∏ f : Fct d0 d1 m, (match f with
      | .inl _ => a | .inr (.inl _) => b | .inr (.inr _) => c) ^ (match f with
      | .inl _ => A₀ | .inr (.inl _) => A₁ | .inr (.inr _) => N) =
      a ^ (d0 * A₀) * b ^ (d1 * A₁) * c ^ (m * 3 * N) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [prod_const, card_univ, Fintype.card_fin, Fintype.card_prod, ← pow_mul]
  ring

lemma sum_fct (A₀ A₁ N : ℕ) :
    ∑ f : Fct d0 d1 m, (match f with
      | .inl _ => A₀ | .inr (.inl _) => A₁ | .inr (.inr _) => N) = d0 * A₀ + d1 * A₁ + m * 3 * N := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [sum_const, card_univ, Fintype.card_fin, Fintype.card_prod, smul_eq_mul]
  ring

/-- The exponent bounds of the basic factors. -/
def Nfac (A₀ A₁ N : ℕ) : Fct d0 d1 m → ℕ
  | .inl _ => A₀
  | .inr (.inl _) => A₁
  | .inr (.inr _) => N

lemma sum_Nfac (A₀ A₁ N : ℕ) :
    ∑ f : Fct d0 d1 m, Nfac A₀ A₁ N f = d0 * A₀ + d1 * A₁ + m * 3 * N := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Nfac, sum_const, card_univ, Fintype.card_fin, Fintype.card_prod, smul_eq_mul]
  ring

lemma prod_Afac_pow (aT hM C HX' H : ℝ) (A₀ A₁ N : ℕ) :
    ∏ f : Fct d0 d1 m, Afac aT hM C HX' H f ^ Nfac A₀ A₁ N f =
      aT ^ (d0 * A₀) * hM ^ (d1 * A₁) * AE C HX' H ^ (m * 3 * N) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Afac, Nfac, prod_const, card_univ, Fintype.card_fin, Fintype.card_prod, ← pow_mul]
  ring

lemma prod_efac_pow (d dM l dX' : ℕ) (A₀ A₁ N : ℕ) :
    ∏ f : Fct d0 d1 m, efac d dM l dX' f ^ Nfac A₀ A₁ N f =
      d ^ (d0 * A₀) * dM ^ (d1 * A₁) * eE l dX' d ^ (m * 3 * N) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [efac, Nfac, prod_const, card_univ, Fintype.card_fin, Fintype.card_prod, ← pow_mul]
  ring

/-! ### Smoothness of `Ψ` -/

lemma contDiff_coordF (Ls : Fin m → PeriodPair) (f : Fct d0 d1 m) :
    ContDiff ℂ ∞ (coordF Ls f) := by
  rcases f with i | i | ⟨k, c⟩
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d0 => ℂ) i).contDiff.comp
      contDiff_fst
  · exact Complex.contDiff_exp.comp ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin d1 => ℂ) i).contDiff.comp (contDiff_fst.comp contDiff_snd))
  · exact (differentiable_ellW (Ls k) c).contDiff.comp ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin m => ℂ) k).contDiff.comp (contDiff_snd.comp contDiff_snd))

lemma contDiff_Psi (Ls : Fin m → PeriodPair) {L : ℕ} (μs : Fin L → Mono d0 d1 m D)
    (p : Fin L → ℤ) : ContDiff ℂ ∞ (Psi Ls μs p) := by
  unfold Psi
  refine ContDiff.sum fun l _ => contDiff_const.mul ?_
  have : (μs l).eval Ls = fun x => ∏ f, coordF Ls f x ^ (μs l).expo f :=
    funext (Mono.eval_eq_prod Ls (μs l))
  rw [this]
  exact contDiff_prod fun f _ => (contDiff_coordF Ls f).pow _

lemma analyticAt_Psi_line (Ls : Fin m → PeriodPair) {L : ℕ} (μs : Fin L → Mono d0 d1 m D)
    (p : Fin L → ℤ) (t v : Tan d0 d1 m) : AnalyticAt ℂ (fun s : ℂ => Psi Ls μs p (t + s • v)) 0 := by
  have h : Differentiable ℂ (fun s : ℂ => Psi Ls μs p (t + s • v)) :=
    ((contDiff_Psi Ls μs p).differentiable (by simp)).comp (by fun_prop)
  exact h.analyticAt 0

/-! ### Sizes of the coordinates of `exp_G(t)` -/

lemma sz_natComb {μ : ℕ} {H : ℝ} {d : ℕ} (hH : 0 ≤ H) {x : Fin μ → ℂ}
    (hx : ∀ j, Sz ι H d (x j)) {S : ℕ} (h : Fin μ → ℕ) (hh : ∀ j, h j ≤ S) :
    Sz ι (S * μ * H) d (∑ j, (h j : ℂ) * x j) := by
  refine (Sz.sum univ fun j _ => (hx j).nat_mul (h j)).mono_le ?_
  calc ∑ j, (h j : ℝ) * H ≤ ∑ _j : Fin μ, (S : ℝ) * H :=
        sum_le_sum fun j _ => by gcongr; exact_mod_cast hh j
    _ = S * μ * H := by simp; ring

lemma sz_expComb {μ : ℕ} {H : ℝ} {d : ℕ} (hH : 1 ≤ H) {x : Fin μ → ℂ}
    (hx : ∀ j, Sz ι H d (x j)) {S : ℕ} (h : Fin μ → ℕ) (hh : ∀ j, h j ≤ S) :
    Sz ι (H ^ (μ * S)) (d ^ (μ * S)) (∏ j, x j ^ h j) := by
  refine (Sz.prod univ fun j _ => (hx j).pow (h j)).mono ?_ ?_
  · rw [prod_pow_eq_pow_sum]
    refine pow_le_pow_right₀ hH ?_
    calc ∑ j, h j ≤ ∑ _j : Fin μ, S := sum_le_sum fun j _ => hh j
      _ = μ * S := by simp
  · rw [prod_pow_eq_pow_sum]
    refine pow_dvd_pow d ?_
    calc ∑ j, h j ≤ ∑ _j : Fin μ, S := sum_le_sum fun j _ => hh j
      _ = μ * S := by simp

end LSG.Aux
