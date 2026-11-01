/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.LemmaUDir
import LSG.AuxFun.LemmaUArith

/-!
# Lemma U at every point of `Y(S)`: the main theorem (Stage 3, D3b)

**`LSG.Aux.lemmaU_core`**: see `LSG/AuxFun/LemmaU.lean` for the statement in words.
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 PeriodPair NumberField
open scoped ContDiff

noncomputable section

namespace LSG.Aux

variable {d0 d1 m : ℕ}
variable {K : Type*} [Field K] [NumberField K]

lemma exp_le_exp_mul_sq {c S : ℝ} (hc : 0 ≤ c) (hS : 1 ≤ S) :
    Real.exp c ≤ Real.exp (c * S ^ 2) :=
  Real.exp_le_exp.mpr (le_mul_of_one_le_right hc (by nlinarith))

lemma mul_le_exp_add {x y a b : ℝ} (hy0 : 0 ≤ y) (hx : x ≤ Real.exp a) (hy : y ≤ Real.exp b) :
    x * y ≤ Real.exp (a + b) := by
  rw [Real.exp_add]
  exact mul_le_mul hx hy hy0 (Real.exp_pos a).le

/-- The constant `exp(c)` as a bound: `x ≤ exp (log x)`. -/
lemma le_exp_log {x : ℝ} (hx : 0 < x) : x ≤ Real.exp (Real.log x) := (Real.exp_log hx).ge

/-- `(x)^n ≤ exp (n K S²)` from `x ≤ exp (K S²)`. -/
lemma pow_le_exp_of_le {x a : ℝ} (hx : 0 ≤ x) (h : x ≤ Real.exp a) (n : ℕ) :
    x ^ n ≤ Real.exp (n * a) := by
  rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ hx h n

set_option maxHeartbeats 4000000 in
/-- **Lemma U at every point of `Y(S)`.** -/
theorem lemmaU_core (Ls : Fin m → PeriodPair) (ι : K →+* ℂ) (V : Submodule ℂ (Tan d0 d1 m))
    {μ τ : ℕ} (Dt : LUData (d0 := d0) (d1 := d1) Ls ι μ τ) (hyV : ∀ j, Dt.y j ∈ V)
    (hwV : ∀ r, Dt.w r ∈ V) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (D L : ℕ) (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ)
      (S T A₀ A₁ : ℕ) (B U : ℝ), 1 ≤ S → 0 ≤ B →
      (∀ l i, (μs l).α i ≤ A₀) → (∀ l i, (μs l).β i ≤ A₁) → (∀ l, |(p l : ℝ)| ≤ Real.exp B) →
      (∀ z ∈ V, ‖z‖ ≤ c₀ * S → ‖Psi Ls μs p z‖ ≤ Real.exp (-U)) →
      c₀ * (B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S +
        (D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2)) ≤ U →
      ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
        VanishAlong (Psi Ls μs p) (Submodule.span ℂ (Set.range Dt.w)) T (∑ j, h j • Dt.y j) := by
  classical
  set H := Dt.H with hHdef
  set d := Dt.d with hddef
  have hH : 1 ≤ H := Dt.hH
  have hd : 1 ≤ d := Dt.hd
  have hH0 : 0 < H := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdR
  -- algebraic points
  choose Ak hAk0 hAk using fun k => exists_alg_points_S (Ls k) (Dt.hγ₂ k) (Dt.hγ₃ k)
    (fun j => (Dt.y j).2.2 k) (fun j => Dt.X₀ j k) (fun j => Dt.hX₀ j k)
    (fun j => ⟨H, d, hd, Dt.hX₀s j k⟩)
  set Aa := ∑ k, Ak k with hAadef
  have hAa0 : 0 ≤ Aa := sum_nonneg fun k _ => hAk0 k
  have hAkAa : ∀ k, Ak k ≤ Aa := fun k => single_le_sum (fun j _ => hAk0 j) (mem_univ k)
  -- weighted denominators
  choose lk hlk1 hlk₂ hlk₃ using fun k => exists_wden (Dt.γ₂ k) (Dt.γ₃ k)
  set l := ∏ k, lk k with hldef
  have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by
    have := hlk1 k; omega)
  have hint : ∀ n : ℕ, IsIntegral ℤ (n : K) := fun n => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ))
  have hlint : ∀ k, IsIntegral ℤ ((l : K) ^ 4 * Dt.γ₂ k) ∧
      IsIntegral ℤ ((l : K) ^ 6 * Dt.γ₃ k) := by
    intro k
    have hsplit : l = lk k * ∏ j ∈ univ.erase k, lk j :=
      (mul_prod_erase univ lk (mem_univ k)).symm
    set r := ∏ j ∈ univ.erase k, lk j
    rw [hsplit]
    constructor
    · have e : ((lk k * r : ℕ) : K) ^ 4 * Dt.γ₂ k =
          ((r ^ 4 : ℕ) : K) * ((lk k : K) ^ 4 * Dt.γ₂ k) := by push_cast; ring
      rw [e]; exact (hint _).mul (hlk₂ k)
    · have e : ((lk k * r : ℕ) : K) ^ 6 * Dt.γ₃ k =
          ((r ^ 6 : ℕ) : K) * ((lk k : K) ^ 6 * Dt.γ₃ k) := by push_cast; ring
      rw [e]; exact (hint _).mul (hlk₃ k)
  -- sizes of the laws
  have hsz : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (C * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2)
          (lawk κ (Ls k).g₂ (Ls k).g₃ P Q i) := by
    intro k
    obtain ⟨C, hC0, hC⟩ := sz_lawk ι (le_max_left (house (Dt.γ₂ k)) (house (Dt.γ₃ k)))
      (le_max_right _ _) (hlint k).1 (hlint k).2
    exact ⟨C, hC0, fun κ P Q Hp Hq dp dq hP hQ i => by
      have := hC κ P Q Hp Hq dp dq hP hQ i; rwa [Dt.hγ₂ k, Dt.hγ₃ k] at this⟩
  choose Ck hCk0 hCk using hsz
  set Cl := 1 + ∑ k, Ck k with hCldef
  have hCl1 : 1 ≤ Cl := by have := sum_nonneg fun k (_ : k ∈ univ) => hCk0 k; linarith
  have hlaw : ∀ k (κ : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (Cl * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2)
          (lawk κ (Ls k).g₂ (Ls k).g₃ P Q i) := by
    intro k κ P Q Hp Hq dp dq hP hQ i
    refine (hCk k κ P Q Hp Hq dp dq hP hQ i).mono_le ?_
    have : Ck k ≤ Cl := by
      have := single_le_sum (f := Ck) (fun j _ => hCk0 j) (mem_univ k); linarith
    have h0 : 0 ≤ Hp ^ 2 * Hq ^ 2 := by positivity
    nlinarith
  -- archimedean bound for the laws
  choose C'k hC'k0 hC'k using fun k : Fin m => exists_lawk_bound (max ‖(Ls k).g₂‖ ‖(Ls k).g₃‖)
  set C'l := 1 + ∑ k, C'k k with hC'ldef
  have hC'l1 : 1 ≤ C'l := by have := sum_nonneg fun k (_ : k ∈ univ) => hC'k0 k; linarith
  have hC'kl : ∀ k, C'k k ≤ C'l := fun k => by
    have := single_le_sum (f := C'k) (fun j _ => hC'k0 j) (mem_univ k); linarith
  -- charts and discs
  choose ρ₀ cch hρ₀ hcch hchart using fun k => exists_chart (Ls k)
  choose ρx Mx hρx hρx1 hMx hxi using fun k => exists_xi_bound (Ls k)
  set ρ₁ : ℝ := 1 / (1 + ∑ k, (1 / ρ₀ k + 1 / ρx k)) with hρ₁def
  have hSig : 0 ≤ ∑ k, (1 / ρ₀ k + 1 / ρx k) := sum_nonneg fun k _ => by
    have := hρ₀ k; have := hρx k; positivity
  have hρ₁ : 0 < ρ₁ := by positivity
  have hρ₁le : ∀ k, ρ₁ ≤ ρ₀ k ∧ ρ₁ ≤ ρx k := by
    intro k
    have hk := single_le_sum (f := fun k => 1 / ρ₀ k + 1 / ρx k) (fun j _ => by
      have := hρ₀ j; have := hρx j; positivity) (mem_univ k)
    have h0 := hρ₀ k; have h1 := hρx k
    have i0 : 0 ≤ 1 / ρ₀ k := one_div_nonneg.mpr h0.le
    have i1 : 0 ≤ 1 / ρx k := one_div_nonneg.mpr h1.le
    constructor
    · calc ρ₁ ≤ 1 / (1 / ρ₀ k) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = ρ₀ k := one_div_one_div _
    · calc ρ₁ ≤ 1 / (1 / ρx k) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = ρx k := one_div_one_div _
  have hρ₁1 : ρ₁ ≤ 1 := by
    rw [hρ₁def, div_le_one (by positivity)]; linarith
  set Mξ := 1 + ∑ k, Mx k with hMξdef
  have hMξ1 : 1 ≤ Mξ := by
    have := sum_nonneg fun k (_ : k ∈ univ) => (zero_le_one.trans (hMx k)); linarith
  have hMxξ : ∀ k, Mx k ≤ Mξ := fun k => by
    have := single_le_sum (f := Mx) (fun j _ => zero_le_one.trans (hMx j)) (mem_univ k); linarith
  set cc := ∑ k, cch k with hccdef
  have hcc0 : 0 ≤ cc := sum_nonneg fun k _ => hcch k
  have hcchcc : ∀ k, cch k ≤ cc := fun k => single_le_sum (fun j _ => hcch j) (mem_univ k)
  set Y := ∑ j, ‖Dt.y j‖ with hYdef
  have hY0 : 0 ≤ Y := sum_nonneg fun j _ => norm_nonneg _
  set Wn := ∑ r, ‖Dt.w r‖ with hWndef
  have hWn0 : 0 ≤ Wn := sum_nonneg fun r _ => norm_nonneg _
  -- the exponent constants
  set KX : ℝ := Real.log Cl + 2 * Aa + 2 * Real.log H with hKXdef
  set KAE : ℝ := Real.log 144 + Real.log Cl + 2 * KX + 2 * Real.log H with hKAEdef
  set KR : ℝ := Real.log C'l + 2 * KX + 2 * Real.log Mξ + cc * (1 + Y) ^ 2 with hKRdef
  set KeE : ℝ := 36 * Real.log l + 4 * Aa + 6 * Real.log d with hKeEdef
  set cρ : ℝ := (1 + Wn) / ρ₁ with hcρdef
  set KB : ℝ := 1 + Real.log (4 * (1 + 7 * τ * H ^ 2)) / Real.log 2 with hKBdef
  set Kρ : ℝ := 1 + Real.log cρ / Real.log 2 with hKρdef
  set deg : ℕ := Module.finrank ℚ K with hdegdef
  set Ka : ℝ := 1 + Real.log ((μ + 1) * H) / Real.log 2 with hKadef
  set κ1 : ℝ := m * KR + deg * (3 * m * KeE + 3 * m * (1 + KAE)) with hκ1def
  set κ2 : ℝ := deg * (d0 * Real.log d / Real.log 2 + d0 + d0 * Ka) with hκ2def
  set κ3 : ℝ := deg * (d1 * μ * Real.log d + d1 + d1 * μ * Real.log H) with hκ3def
  set κ4 : ℝ := Kρ + deg * (2 * Real.log d / Real.log 2 + 1 + KB) with hκ4def
  set c₀ : ℝ := 2 + Y + κ1 + κ2 + κ3 + κ4 + 2 * deg with hc₀def
  -- nonnegativity of the constants
  have hlogCl : 0 ≤ Real.log Cl := Real.log_nonneg hCl1
  have hlogC'l : 0 ≤ Real.log C'l := Real.log_nonneg hC'l1
  have hlogMξ : 0 ≤ Real.log Mξ := Real.log_nonneg hMξ1
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg (show (1 : ℝ) ≤ l by exact_mod_cast hl1)
  have hKX : 0 ≤ KX := by positivity
  have hKAE : 0 ≤ KAE := by
    have : 0 ≤ Real.log 144 := Real.log_nonneg (by norm_num)
    positivity
  have hKR : 0 ≤ KR := by positivity
  have hKeE : 0 ≤ KeE := by positivity
  have hcρ1 : 1 ≤ cρ := by
    rw [hcρdef, le_div_iff₀ hρ₁]; linarith
  have hB4 : 1 ≤ 4 * (1 + 7 * (τ : ℝ) * H ^ 2) := by
    have : 0 ≤ 7 * (τ : ℝ) * H ^ 2 := by positivity
    linarith
  have hKB : 0 ≤ KB := by have := Real.log_nonneg hB4; positivity
  have hKρ : 0 ≤ Kρ := by have := Real.log_nonneg hcρ1; positivity
  have hμH : 1 ≤ ((μ : ℝ) + 1) * H :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)]) hH
  have hKa : 0 ≤ Ka := by have := Real.log_nonneg hμH; positivity
  have hκ1 : 0 ≤ κ1 := by positivity
  have hκ2 : 0 ≤ κ2 := by positivity
  have hκ3 : 0 ≤ κ3 := by positivity
  have hκ4 : 0 ≤ κ4 := by positivity
  have hdeg0 : (0 : ℝ) ≤ deg := Nat.cast_nonneg _
  refine ⟨c₀, by rw [hc₀def]; linarith, fun D L μs p S T A₀ A₁ B U hS hB hα hβ hp hsmall hbud h
    hh => ?_⟩
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  set t : Tan d0 d1 m := ∑ j, h j • Dt.y j with htdef
  have ht0' : ∀ i, t.1 i = ∑ j, (h j : ℂ) * (Dt.y j).1 i := by
    intro i; simp [htdef, Prod.fst_sum, Finset.sum_apply, nsmul_eq_mul]
  have ht1' : ∀ i, t.2.1 i = ∑ j, (h j : ℂ) * (Dt.y j).2.1 i := by
    intro i; simp [htdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, nsmul_eq_mul]
  have ht2' : ∀ k, t.2.2 k = ∑ j, (h j : ℂ) * (Dt.y j).2.2 k := by
    intro k; simp [htdef, Prod.snd_sum, Finset.sum_apply, nsmul_eq_mul]
  have htn : ‖t‖ ≤ S * Y := by
    refine (norm_sum_le _ _).trans ?_
    rw [hYdef, mul_sum]
    refine sum_le_sum fun j _ => norm_nsmul_le.trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh j) (norm_nonneg _)
  have htk : ∀ k, ‖t.2.2 k‖ ≤ S * Y := fun k =>
    ((norm_le_pi_norm _ k).trans ((norm_snd_le _).trans (norm_snd_le _))).trans htn
  have htV : t ∈ V := V.sum_mem fun j _ => V.smul_of_tower_mem _ (hyV j)
  -- algebraic points `X_k` and their translates `X'_k`
  choose Xk dXk hXk hdXk hdXkle hXks using fun k => hAk k S hS h hh
  set dX := ∏ k, dXk k with hdXdef
  set HX := Real.exp (Aa * S ^ 2) with hHXdef
  have hHX1 : 1 ≤ HX := Real.one_le_exp (by positivity)
  have hdX1 : 1 ≤ dX := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by
    have := hdXk k; omega)
  have hdXle : (dX : ℝ) ≤ HX := by
    rw [hdXdef, hHXdef, Nat.cast_prod, hAadef, sum_mul, Real.exp_sum]
    exact prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) fun k _ => hdXkle k
  have hXs : ∀ k i, Sz ι HX dX (Xk k i) := fun k i =>
    (hXks k i).mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hAkAa k) (by positivity)))
      (dvd_prod_of_mem _ (mem_univ k))
  set E1 : Fin m → Fin 3 → ℂ := fun k => ![℘[Ls k] (zh (Ls k)), 0, 1] with hE1def
  have hE1s : ∀ k i, Sz ι H d (E1 k i) := by
    intro k i
    fin_cases i
    · exact Dt.he₁ k
    · exact (Sz.zero d).mono_le (zero_le_one.trans hH)
    · exact Sz.one.mono hH (one_dvd d)
  have hXrep : ∀ k, IsRep (Ls k) (t.2.2 k) (Xk k) := fun k => by rw [ht2']; exact hXk k
  choose κA hκA using fun k => isRep_lawk (Ls k) (hXrep k) (isRep_half (Ls k))
  set X' : Fin m → Fin 3 → ℂ := fun k => lawk (κA k) (Ls k).g₂ (Ls k).g₃ (Xk k) (E1 k)
    with hX'def
  have hX'rep : ∀ k, IsRep (Ls k) (t.2.2 k + zh (Ls k)) (X' k) := hκA
  set HX' := Cl * HX ^ 2 * H ^ 2 with hHX'def
  set dX' := l ^ 12 * dX ^ 2 * d ^ 2 with hdX'def
  have hHX'1 : 1 ≤ HX' :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCl1 (one_le_pow₀ hHX1))
      (one_le_pow₀ hH)
  have hdX'1 : 1 ≤ dX' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hX's : ∀ k i, Sz ι HX' dX' (X' k i) := fun k i =>
    hlaw k (κA k) (Xk k) (E1 k) HX H dX d (hXs k) (hE1s k) i
  choose κB hκB using fun k => isRep_lawk (Ls k) (hX'rep k) (isRep_half (Ls k))
  -- sizes of the coordinates of `t`
  set aT : ℝ := S * (μ + 1) * H with haTdef
  have haT1 : 1 ≤ aT :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hSR
      (by linarith only [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)])) hH
  have ht0 : ∀ i, Sz ι aT d (t.1 i) := fun i => by
    rw [ht0']
    refine (sz_natComb hH0.le (fun j => Dt.ha j i) h hh).mono_le ?_
    rw [haTdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only)
      (by positivity)) hH0.le
  set hM : ℝ := H ^ (μ * S) with hhMdef
  set dM : ℕ := d ^ (μ * S) with hdMdef
  have ht1 : ∀ i, Sz ι hM dM (exp (t.2.1 i)) := fun i => by
    rw [ht1', Complex.exp_sum]
    have : ∀ j, exp ((h j : ℂ) * (Dt.y j).2.1 i) = exp ((Dt.y j).2.1 i) ^ h j := fun j => by
      rw [← Complex.exp_nat_mul]
    simp_rw [this]
    exact sz_expComb hH (fun j => Dt.hb j i) h hh
  -- the law bounds, discs and charts, uniformly in `k`
  have hlawB : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) i,
      ‖lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i‖ ≤ C'l * ‖P‖ ^ 2 * ‖Q‖ ^ 2 := by
    intro k κ' P Q i
    refine (hC'k k κ' i _ _ (le_max_left _ _) (le_max_right _ _) P Q).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC'kl k) (sq_nonneg _))
      (sq_nonneg _)
  have hxi' : ∀ k (u : ℂ), ‖u‖ ≤ ρ₁ → zh (Ls k) + u ∉ (Ls k).lattice ∧
      ‖℘[Ls k] (zh (Ls k) + u)‖ ≤ Mξ ∧ ‖℘'[Ls k] (zh (Ls k) + u)‖ ≤ Mξ := by
    intro k u hu
    obtain ⟨h1, h2, h3⟩ := hxi k u (hu.trans (hρ₁le k).2)
    exact ⟨h1, h2.trans (hMxξ k), h3.trans (hMxξ k)⟩
  have hchart' : ∀ k, ∃ j : Fin 3, ∀ z : ℂ, ‖z‖ ≤ ρ₁ →
      Real.exp (-(cc * (1 + S * Y) ^ 2)) ≤ ‖ellV (Ls k) (t.2.2 k + z) j‖ := by
    intro k
    obtain ⟨j, hj⟩ := hchart k (t.2.2 k)
    refine ⟨j, fun z hz => le_trans (Real.exp_le_exp.mpr ?_) (hj z (hz.trans (hρ₁le k).1))⟩
    have h1 : (1 + ‖t.2.2 k‖) ^ 2 ≤ (1 + S * Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [htk k]) 2
    have h2 : cch k * (1 + ‖t.2.2 k‖) ^ 2 ≤ cc * (1 + S * Y) ^ 2 :=
      mul_le_mul (hcchcc k) h1 (by positivity) hcc0
    linarith only [h2]
  -- one direction of the grid
  have key : ∀ c : Fin τ → ℕ, (∀ r, c r ≤ T) → ∀ k < T,
      iteratedDeriv k (fun s : ℂ => Psi Ls μs p (t + s • ∑ r, (c r : ℂ) • Dt.w r)) 0 = 0 := by
    intro c hc
    set v : Tan d0 d1 m := ∑ r, (c r : ℂ) • Dt.w r with hvdef
    have hv0' : ∀ i, v.1 i = ∑ r, (c r : ℂ) * (Dt.w r).1 i := by
      intro i; simp [hvdef, Prod.fst_sum, Finset.sum_apply]
    have hv1' : ∀ i, v.2.1 i = ∑ r, (c r : ℂ) * (Dt.w r).2.1 i := by
      intro i; simp [hvdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    have hv2' : ∀ k, v.2.2 k = ∑ r, (c r : ℂ) * (Dt.w r).2.2 k := by
      intro k; simp [hvdef, Prod.snd_sum, Finset.sum_apply]
    have hvn : ‖v‖ ≤ T * Wn := by
      refine (norm_sum_le _ _).trans ?_
      rw [hWndef, mul_sum]
      refine sum_le_sum fun r _ => ?_
      rw [norm_smul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc r) (norm_nonneg _)
    have hvV : v ∈ V := V.sum_mem fun r _ => V.smul_mem _ (hwV r)
    set aV : ℝ := T * τ * H with haVdef
    have haV : 0 ≤ aV := by positivity
    have hv0 : ∀ i, Sz ι aV d (v.1 i) := fun i => by
      rw [hv0']; exact sz_natComb hH0.le (fun r => Dt.hw0 r i) c hc
    have hv1 : ∀ i, Sz ι aV d (v.2.1 i) := fun i => by
      rw [hv1']; exact sz_natComb hH0.le (fun r => Dt.hw1 r i) c hc
    have hv2 : ∀ k, Sz ι aV d (v.2.2 k) := fun k => by
      rw [hv2']; exact sz_natComb hH0.le (fun r => Dt.hw2 r k) c hc
    have hsm : ∀ s : ℂ, ‖s‖ ≤ ρ₁ / (1 + ‖v‖) → ‖Psi Ls μs p (t + s • v)‖ ≤ Real.exp (-U) := by
      intro s hs
      refine hsmall _ (V.add_mem htV (V.smul_mem s hvV)) ?_
      have h1 : ‖s • v‖ ≤ ρ₁ := by
        rw [norm_smul]
        calc ‖s‖ * ‖v‖ ≤ ρ₁ / (1 + ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
          _ ≤ ρ₁ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith only [hρ₁, norm_nonneg v]
      have h2 : ‖t + s • v‖ ≤ S * Y + 1 := (norm_add_le _ _).trans (by linarith only [htn, h1, hρ₁1])
      have h3 : S * Y + 1 ≤ c₀ * S := by
        have hc0 : 2 + Y ≤ c₀ := by rw [hc₀def]; linarith only [hκ1, hκ2, hκ3, hκ4, hdeg0]
        nlinarith only [hc0, hSR, hY0]
      exact h2.trans h3
    exact lemmaU_dir Ls ι μs p hα hβ hp hB t v κB X' hX'rep (fun k => (hκB k).1) hH hd haT1 haV
      (one_le_pow₀ hH) (Nat.one_le_iff_ne_zero.mpr (by positivity)) hHX'1 hdX'1 hl1 hCl1 hlaw
      ht0 hv0 ht1 hv1 hv2 hX's Dt.he₁ Dt.hg₂ hρ₁ (zero_le_one.trans hC'l1) hMξ1 hlawB hxi'
      hchart' hsm (fun k hk => lemmaU_arith hS hk hH hd hCl1 hC'l1 hMξ1 hAa0 hcc0 hY0 hWn0 hρ₁
        hρ₁1 hl1 hB hdX1 hdXle (norm_nonneg v) hvn hbud)
  -- polarization
  intro w hw k hk
  have hkT : k < T := by exact_mod_cast hk
  exact iteratedDeriv_line_eq_zero_of_span (contDiff_Psi Ls μs p) t Dt.w k
    (fun c hc => key c (fun r => (hc r).trans hkT.le) k hkT) hw

end LSG.Aux
