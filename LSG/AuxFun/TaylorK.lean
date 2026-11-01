/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.NFSize

/-!
# Taylor coefficients at `0` with algebraic sizes (Stage 3, D3)

* `tco j f = f^{(j)}(0) / j!`; `tco_add`, `tco_mul` (Leibniz: Cauchy product), `tco_const_mul`,
  `tco_deriv`, `tco_const`, `tco_lin`, `tco_cexp`, `tco_congr` (germs), `norm_tco_le` (Cauchy).
* `iteratedDeriv_eq_zero_of_mul`: if `u(0) ≠ 0` and `(u f)^{(j)}(0) = 0` for `j < T`, then
  `f^{(j)}(0) = 0` for `j < T`.
* `KS ι A B e δ f`: `f` analytic at `0` and `tco j f` has size `(A Bʲ, e δʲ j!)`. Closure: `KS.add`,
  `KS.const_mul`, `KS.const`, `KS.mono`, and the **asymmetric product** `KS.mul_basic`: a product
  with base `2B` times a factor with base `B` keeps base `2B` (constant `× 2`). So a product of `N`
  factors of base `B` has base `2B` and constant `2^N Π Aᵢ` (`KS.mul_pow_basic`).
-/

open Finset

noncomputable section

namespace LSG.Aux

/-- The `j`-th Taylor coefficient at `0`. -/
def tco (j : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv j f 0 / j.factorial

lemma tco_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) (j : ℕ) : tco j f = tco j g := by
  unfold tco; rw [(h.iteratedDeriv j).eq_of_nhds]

lemma tco_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    tco j (f + g) = tco j f + tco j g := by
  unfold tco; rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt]; ring

lemma tco_const_mul (c : ℂ) (f : ℂ → ℂ) (j : ℕ) : tco j (fun s => c * f s) = c * tco j f := by
  unfold tco; rw [iteratedDeriv_const_mul_field]; ring

lemma tco_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    tco j (f * g) = ∑ i ∈ range (j + 1), tco i f * tco (j - i) g := by
  unfold tco
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hc := Nat.choose_mul_factorial_mul_factorial hij
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((j - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (j - i).factorial_ne_zero
  have h3 : ((j.choose i : ℕ) : ℂ) * i.factorial * (j - i).factorial = j.factorial := by
    exact_mod_cast hc
  have h4 : ((j.choose i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hij).ne'
  rw [← h3]
  field_simp

lemma tco_const (c : ℂ) (j : ℕ) : tco j (fun _ => c) = if j = 0 then c else 0 := by
  unfold tco; rw [iteratedDeriv_const]; split_ifs with h <;> simp [h]

lemma tco_deriv (f : ℂ → ℂ) (j : ℕ) : tco j (deriv f) = (j + 1) * tco (j + 1) f := by
  unfold tco
  rw [iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

lemma tco_cexp (b : ℂ) (j : ℕ) :
    tco j (fun s => Complex.exp (b * s)) = b ^ j / j.factorial := by
  unfold tco; rw [iteratedDeriv_cexp_const_mul]; simp

lemma tco_lin (a b : ℂ) (j : ℕ) :
    tco j (fun s => a + b * s) = if j = 0 then a else if j = 1 then b else 0 := by
  have hf : AnalyticAt ℂ (fun _ : ℂ => a) 0 := analyticAt_const
  have hg : AnalyticAt ℂ (fun s : ℂ => b * s) 0 := analyticAt_const.mul analyticAt_id
  have := tco_add hf hg j
  simp only [Pi.add_def] at this
  rw [this, tco_const, tco_const_mul]
  unfold tco
  rw [iteratedDeriv_fun_id_zero]
  rcases j with _ | _ | j <;> simp

/-- **Cauchy's estimate** for Taylor coefficients. -/
lemma norm_tco_le {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M)
    (j : ℕ) : ‖tco j f‖ ≤ M / R ^ j := by
  unfold tco
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR hf hM
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hj]
  calc ‖iteratedDeriv j f 0‖ ≤ j.factorial * M / R ^ j := this
    _ = M / R ^ j * j.factorial := by ring

/-- Vanishing of low-order derivatives survives division by a unit. -/
lemma iteratedDeriv_eq_zero_of_mul {u f : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hf : AnalyticAt ℂ f 0) {T : ℕ} (h : ∀ j < T, iteratedDeriv j (u * f) 0 = 0) :
    ∀ j < T, iteratedDeriv j f 0 = 0 := by
  intro j hj
  have hui : AnalyticAt ℂ u⁻¹ 0 := hu.inv hu0
  have hev : f =ᶠ[nhds 0] u⁻¹ * (u * f) := by
    filter_upwards [hu.continuousAt.eventually_ne hu0] with s hs
    simp only [Pi.mul_apply, Pi.inv_apply]
    field_simp
  rw [(hev.iteratedDeriv j).eq_of_nhds, iteratedDeriv_mul hui.contDiffAt (hu.mul hf).contDiffAt]
  refine sum_eq_zero fun i hi => ?_
  rw [h (j - i) (lt_of_le_of_lt (Nat.sub_le j i) hj), mul_zero]

lemma geom2_le (n : ℕ) : ∑ i ∈ range n, (2 : ℝ) ^ i ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith [pow_pos (two_pos : (0 : ℝ) < 2) n]

/-! ### Series with algebraic Taylor coefficients of controlled size -/

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ)

/-- `f` is analytic at `0` and `tco j f` has size `(A Bʲ, e δʲ j!)`. -/
def KS (A B : ℝ) (e δ : ℕ) (f : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ ∀ j, Sz ι (A * B ^ j) (e * δ ^ j * j.factorial) (tco j f)

variable {ι}

namespace KS

lemma mono {A A' B B' : ℝ} {e e' δ δ' : ℕ} {f : ℂ → ℂ} (h : KS ι A B e δ f) (hA : A ≤ A')
    (hB0 : 0 ≤ B) (hB : B ≤ B') (he : e ∣ e') (hδ : δ ∣ δ') : KS ι A' B' e' δ' f := by
  refine ⟨h.1, fun j => (h.2 j).mono ?_ ?_⟩
  · have hA0 : 0 ≤ A := by
      have := (h.2 0).nonneg; simpa using this
    exact mul_le_mul hA (pow_le_pow_left₀ hB0 hB j) (pow_nonneg hB0 j) (hA0.trans hA)
  · exact mul_dvd_mul (mul_dvd_mul he (pow_dvd_pow_of_dvd hδ j)) dvd_rfl

lemma add {A A' B : ℝ} {e δ : ℕ} {f g : ℂ → ℂ} (hf : KS ι A B e δ f) (hg : KS ι A' B e δ g) :
    KS ι (A + A') B e δ (f + g) := by
  refine ⟨hf.1.add hg.1, fun j => ?_⟩
  rw [tco_add hf.1 hg.1, add_mul]
  exact (hf.2 j).add (hg.2 j)

lemma const_mul {a A B : ℝ} {d e δ : ℕ} {c : ℂ} {f : ℂ → ℂ} (hc : Sz ι a d c)
    (hf : KS ι A B e δ f) : KS ι (a * A) B (d * e) δ (fun s => c * f s) := by
  refine ⟨analyticAt_const.mul hf.1, fun j => ?_⟩
  rw [tco_const_mul]
  have := hc.mul (hf.2 j)
  convert this using 1 <;> ring

lemma const {a B : ℝ} {d δ : ℕ} {c : ℂ} (hc : Sz ι a d c) (hB : 0 ≤ B) :
    KS ι a B d δ (fun _ => c) := by
  refine ⟨analyticAt_const, fun j => ?_⟩
  rw [tco_const]
  rcases j with _ | j
  · simpa using hc
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    refine (Sz.zero _).mono_le ?_
    exact mul_nonneg hc.nonneg (pow_nonneg hB _)

lemma one {B : ℝ} {δ : ℕ} (hB : 0 ≤ B) : KS ι 1 B 1 δ (fun _ => 1) := const Sz.one hB

/-- **Asymmetric product.** -/
lemma mul_basic {A A' B : ℝ} {e e' δ : ℕ} {f g : ℂ → ℂ} (hB : 0 ≤ B) (hf : KS ι A (2 * B) e δ f)
    (hg : KS ι A' B e' δ g) : KS ι (2 * A * A') (2 * B) (e * e') δ (f * g) := by
  refine ⟨hf.1.mul hg.1, fun j => ?_⟩
  rw [tco_mul hf.1 hg.1]
  have hterm : ∀ i ∈ range (j + 1), Sz ι (A * A' * B ^ j * 2 ^ i) (e * e' * δ ^ j * j.factorial)
      (tco i f * tco (j - i) g) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    refine ((hf.2 i).mul (hg.2 (j - i))).mono (le_of_eq ?_) ?_
    · rw [mul_pow]
      have : B ^ j = B ^ i * B ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
      rw [this]; ring
    · have hδ : δ ^ j = δ ^ i * δ ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
      have hf' : i.factorial * (j - i).factorial ∣ j.factorial :=
        Nat.factorial_mul_factorial_dvd_factorial hij
      rw [hδ]
      obtain ⟨q, hq⟩ := hf'
      refine ⟨q, ?_⟩
      rw [hq]; ring
  refine (Sz.sum _ hterm).mono_le ?_
  have hA0 : 0 ≤ A := by have := (hf.2 0).nonneg; simpa using this
  have hA0' : 0 ≤ A' := by have := (hg.2 0).nonneg; simpa using this
  rw [← mul_sum]
  have hgeom : ∑ i ∈ range (j + 1), (2 : ℝ) ^ i ≤ 2 ^ (j + 1) := geom2_le (j + 1)
  calc A * A' * B ^ j * ∑ i ∈ range (j + 1), (2 : ℝ) ^ i
      ≤ A * A' * B ^ j * 2 ^ (j + 1) := by gcongr
    _ = 2 * A * A' * (2 * B) ^ j := by rw [mul_pow, pow_succ]; ring

lemma mul_pow_basic {A A' B : ℝ} {e e' δ : ℕ} {f g : ℂ → ℂ} (hB : 0 ≤ B)
    (hf : KS ι A (2 * B) e δ f) (hg : KS ι A' B e' δ g) (n : ℕ) :
    KS ι (2 ^ n * A * A' ^ n) (2 * B) (e * e' ^ n) δ (fun s => f s * g s ^ n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have := ih.mul_basic hB hg
    convert this using 1
    · ring
    · ring
    · funext s; simp only [Pi.mul_apply]; ring

end KS

end LSG.Aux
