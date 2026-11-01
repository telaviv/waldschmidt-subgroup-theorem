/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Analytic orders of vanishing (STAGE_A4 A4.1a, risk R2)

Pure analysis, no `LSG` imports. The multiplicity estimate `LSG.MEB` measures orders of vanishing *analytically*
(`OrdGtB`: Taylor coefficients along lines). Everything it needs reduces to the following **big-O calculus**, which
avoids symmetric multilinear maps, polarization and two-variable power series:

* one variable (`isBigO_pow_iff`): for `g` analytic at `0`, the first `n` derivatives vanish iff
  `g = O(|t|^n)` (from Mathlib's `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` and `isTheta_pow_sub`);
* several variables (`isBigO_of_diag`, `diag_iff_isBigO`): for `f` entire on a normed space, the derivatives of order
  `< n` along every line through `0` vanish iff `f = O(‖y‖^n)` (power series, `factorial_smul`,
  `isBigO_sub_partialSum_pow`);
* **two parameters** (`isBigO_iteratedDeriv_snd`, `iteratedDeriv_iteratedDeriv_snd_eq_zero`): if
  `G : ℂ × ℂ → ℂ` is entire and `G = O(‖y‖^n)`, then `t ↦ ∂_{t'}^κ G(t, 0)` is analytic and `O(|t|^{n−κ})`, so its
  derivatives of order `< n − κ` vanish at `0` (Cauchy's estimate on the circle `|t'| = |t|`, sup norm on `ℂ × ℂ`).

R2 verdict: Mathlib v4.35 suffices; the formal-exponential fallback is not needed.
-/

open Asymptotics Filter Topology Set

namespace LSG.MEB

/-! ### One variable -/

section OneVar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem frequently_pow_ne_zero (m : ℕ) : ∃ᶠ z in 𝓝 (0 : ℂ), z ^ m ≠ 0 :=
  ((eventually_nhdsWithin_of_forall fun z (hz : z ∈ ({0}ᶜ : Set ℂ)) => pow_ne_zero m hz).frequently).filter_mono
    nhdsWithin_le_nhds

/-- A power bound forces vanishing of the low derivatives. -/
theorem iteratedDeriv_eq_zero_of_isBigO {g : ℂ → E} (hg : AnalyticAt ℂ g 0) {n : ℕ}
    (h : g =O[𝓝 0] fun t => ‖t‖ ^ n) : ∀ i < n, iteratedDeriv i g 0 = 0 := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
  by_cases htop : analyticOrderAt g 0 = ⊤
  · rw [htop]; exact le_top
  have hθ := hg.isTheta_pow_sub htop
  rw [← Nat.cast_analyticOrderNatAt htop, Nat.cast_le]
  by_contra hlt
  push Not at hlt
  have h1 : (fun z : ℂ => z ^ analyticOrderNatAt g 0) =O[𝓝 0] fun t => ‖t‖ ^ n := by
    simpa using hθ.symm.isBigO.trans h
  have h2 : (fun t : ℂ => ‖t‖ ^ n) =o[𝓝 0] fun z : ℂ => z ^ analyticOrderNatAt g 0 := by
    refine (isLittleO_norm_pow_norm_pow hlt).trans_isBigO ?_
    exact isBigO_of_le _ fun z => by simp
  exact h1.not_isLittleO (frequently_pow_ne_zero _) h2

/-- Vanishing of the low derivatives gives a power bound. -/
theorem isBigO_of_iteratedDeriv_eq_zero {g : ℂ → E} (hg : AnalyticAt ℂ g 0) {n : ℕ}
    (h : ∀ i < n, iteratedDeriv i g 0 = 0) : g =O[𝓝 0] fun t => ‖t‖ ^ n := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg, natCast_le_analyticOrderAt hg] at h
  obtain ⟨g', hg', hgg'⟩ := h
  have hb : g' =O[𝓝 0] fun _ => (1 : ℝ) := hg'.continuousAt.isBigO_one ℝ
  have h1 : (fun z : ℂ => (z - 0) ^ n) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ n := isBigO_of_le _ fun z => by simp
  have : (fun z : ℂ => (z - 0) ^ n • g' z) =O[𝓝 0] fun t => ‖t‖ ^ n := by
    simpa using h1.smul hb
  exact this.congr' (hgg'.mono fun z hz => hz.symm) (Eventually.of_forall fun _ => rfl)

/-- **One variable**: `∀ i < n, g⁽ⁱ⁾(0) = 0` iff `g = O(|t|ⁿ)`. -/
theorem isBigO_pow_iff {g : ℂ → E} (hg : AnalyticAt ℂ g 0) {n : ℕ} :
    (∀ i < n, iteratedDeriv i g 0 = 0) ↔ g =O[𝓝 0] fun t => ‖t‖ ^ n :=
  ⟨isBigO_of_iteratedDeriv_eq_zero hg, iteratedDeriv_eq_zero_of_isBigO hg⟩

end OneVar

/-! ### Several variables: lines through `0` -/

section SevVar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The `k`-th derivative along the line `s ↦ s • v` is the diagonal value of the `k`-th Fréchet derivative. -/
theorem iteratedDeriv_line {f : V → ℂ} (hf : ContDiff ℂ ⊤ f) (v : V) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => f (s • v)) 0 = iteratedFDeriv ℂ k f 0 fun _ => v := by
  have hL : (fun s : ℂ => f (s • v)) = f ∘ (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v) := by
    funext s; simp
  rw [hL, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ (by exact_mod_cast le_top)]
  simp

/-- **Lines to big-O**: an entire function whose derivatives of order `< n` vanish along every line through `0` is
`O(‖y‖ⁿ)` at `0`. -/
theorem isBigO_of_diag {f : V → ℂ} (hf : AnalyticOnNhd ℂ f univ) {n : ℕ}
    (h : ∀ v, ∀ k < n, iteratedDeriv k (fun s : ℂ => f (s • v)) 0 = 0) :
    f =O[𝓝 0] fun y => ‖y‖ ^ n := by
  obtain ⟨p, r, hp⟩ := hf 0 (mem_univ _)
  have hcd : ContDiff ℂ ⊤ f := hf.contDiff
  have hpk : ∀ k < n, ∀ v, p k (fun _ => v) = 0 := by
    intro k hk v
    have h1 := hp.factorial_smul v k
    rw [← iteratedDeriv_line hcd, h v k hk] at h1
    have h2 : ((k.factorial : ℂ)) • p k (fun _ => v) = 0 := by
      rw [← h1]; simp
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast k.factorial_ne_zero)
  have hps : ∀ y, p.partialSum n y = 0 := fun y =>
    Finset.sum_eq_zero fun k hk => hpk k (Finset.mem_range.mp hk) y
  have := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow n
  simpa [hps] using this

/-- **Big-O to lines.** -/
theorem diag_of_isBigO {f : V → ℂ} (hf : AnalyticOnNhd ℂ f univ) {n : ℕ}
    (h : f =O[𝓝 0] fun y => ‖y‖ ^ n) (v : V) : ∀ k < n, iteratedDeriv k (fun s : ℂ => f (s • v)) 0 = 0 := by
  refine iteratedDeriv_eq_zero_of_isBigO ?_ ?_
  · exact (hf _ (mem_univ _)).comp (by fun_prop)
  · have hc : Continuous fun s : ℂ => s • v := by fun_prop
    have ht : Tendsto (fun s : ℂ => s • v) (𝓝 0) (𝓝 0) := hc.tendsto' 0 0 (by simp)
    refine (h.comp_tendsto ht).trans ?_
    refine isBigO_of_le' (c := ‖v‖ ^ n) _ fun s => ?_
    simp [norm_smul, mul_pow, mul_comm]

/-- **Several variables**: vanishing along all lines through `0` to order `≥ n` iff `f = O(‖y‖ⁿ)`. -/
theorem diag_iff_isBigO {f : V → ℂ} (hf : AnalyticOnNhd ℂ f univ) {n : ℕ} :
    (∀ v, ∀ k < n, iteratedDeriv k (fun s : ℂ => f (s • v)) 0 = 0) ↔ f =O[𝓝 0] fun y => ‖y‖ ^ n :=
  ⟨isBigO_of_diag hf, diag_of_isBigO hf⟩

end SevVar

/-! ### Two parameters -/

section TwoVar

/-- The `κ`-th derivative in the second variable, as a diagonal value of `iteratedFDeriv`. -/
theorem iteratedDeriv_snd_eq {G : ℂ × ℂ → ℂ} (hG : ContDiff ℂ ⊤ G) (κ : ℕ) (t : ℂ) :
    iteratedDeriv κ (fun t' => G (t, t')) 0 = iteratedFDeriv ℂ κ G (t, 0) fun _ => ((0 : ℂ), (1 : ℂ)) := by
  have hL : (fun t' : ℂ => G (t, t')) =
      (fun y => G ((t, 0) + y)) ∘ (ContinuousLinearMap.inr ℂ ℂ ℂ) := by
    funext t'; simp
  have hG' : ContDiff ℂ ⊤ fun y => G ((t, 0) + y) := hG.comp (contDiff_const.add contDiff_id)
  rw [hL, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hG' _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  simp

/-- `t ↦ ∂_{t'}^κ G(t, 0)` is analytic. -/
theorem analyticAt_iteratedDeriv_snd {G : ℂ × ℂ → ℂ} (hG : AnalyticOnNhd ℂ G univ) (κ : ℕ) (t₀ : ℂ) :
    AnalyticAt ℂ (fun t => iteratedDeriv κ (fun t' => G (t, t')) 0) t₀ := by
  have hcd : ContDiff ℂ ⊤ G := hG.contDiff
  simp_rw [iteratedDeriv_snd_eq hcd]
  have h1 : AnalyticAt ℂ (iteratedFDeriv ℂ κ G) (t₀, 0) := hG.iteratedFDeriv κ _ (mem_univ _)
  have h2 : AnalyticAt ℂ (fun t : ℂ => iteratedFDeriv ℂ κ G (t, 0)) t₀ :=
    h1.comp (f := fun t : ℂ => (t, (0 : ℂ))) (by fun_prop)
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin κ => ℂ × ℂ) ℂ
    (fun _ => ((0 : ℂ), (1 : ℂ)))).analyticAt _ |>.comp h2

/-- **Cauchy's estimate in the second variable**: if `G = O(‖y‖ⁿ)` then `∂_{t'}^κ G(t, 0) = O(|t|^{n−κ})`. -/
theorem isBigO_iteratedDeriv_snd {G : ℂ × ℂ → ℂ} (hG : AnalyticOnNhd ℂ G univ) {n κ : ℕ}
    (h : G =O[𝓝 0] fun y => ‖y‖ ^ n) (hκ : κ ≤ n) :
    (fun t => iteratedDeriv κ (fun t' => G (t, t')) 0) =O[𝓝 0] fun t => ‖t‖ ^ (n - κ) := by
  obtain ⟨C, hC, hCb⟩ := h.exists_pos
  rw [IsBigOWith, Metric.eventually_nhds_iff] at hCb
  obtain ⟨ε, hε, hεb⟩ := hCb
  have hdiff : ∀ t : ℂ, Differentiable ℂ fun t' => G (t, t') := fun t =>
    (hG.contDiff (n := 1)).differentiable one_ne_zero |>.comp (by fun_prop)
  -- the value at `t = 0`
  have h0 : κ < n → iteratedDeriv κ (fun t' => G (0, t')) 0 = 0 := by
    intro hκn
    refine iteratedDeriv_eq_zero_of_isBigO ((hG _ (mem_univ _)).comp (by fun_prop)) ?_ κ hκn
    have ht : Tendsto (fun t' : ℂ => ((0 : ℂ), t')) (𝓝 0) (𝓝 0) :=
      (continuous_const.prodMk continuous_id).tendsto' 0 0 rfl
    refine (h.comp_tendsto ht).trans (isBigO_of_le _ fun t' => ?_)
    simp [Prod.norm_def]
  set C' : ℝ := max (κ.factorial * C) ‖iteratedDeriv κ (fun t' => G (0, t')) 0‖
  refine IsBigO.of_bound C' ?_
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε, hε, fun {t} ht => ?_⟩
  rw [dist_zero_right] at ht
  rcases eq_or_ne t 0 with rfl | ht0
  · rcases lt_or_eq_of_le hκ with hκn | rfl
    · rw [h0 hκn]
      simp only [norm_zero, zero_pow (show n - κ ≠ 0 by omega), mul_zero, le_refl]
    · simp [C']
  · have hR : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) ‖t‖, ‖G (t, z)‖ ≤ C * ‖t‖ ^ n := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      have hnorm : ‖((t, z) : ℂ × ℂ)‖ = ‖t‖ := by simp [Prod.norm_def, hz]
      have := hεb (show dist ((t, z) : ℂ × ℂ) 0 < ε by rw [dist_zero_right, hnorm]; exact ht)
      simpa [hnorm] using this
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le κ hR
      (hdiff t).diffContOnCl hbd
    have hpow : ‖t‖ ^ n / ‖t‖ ^ κ = ‖t‖ ^ (n - κ) := by
      rw [div_eq_iff (pow_ne_zero _ hR.ne'), ← pow_add, Nat.sub_add_cancel hκ]
    calc ‖iteratedDeriv κ (fun t' => G (t, t')) 0‖ ≤ κ.factorial * (C * ‖t‖ ^ n) / ‖t‖ ^ κ := hc
      _ = κ.factorial * C * ‖t‖ ^ (n - κ) := by rw [← hpow]; ring
      _ ≤ C' * ‖‖t‖ ^ (n - κ)‖ := by
        rw [norm_pow, norm_norm]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **The two-parameter lemma, analytic core.** If `G : ℂ × ℂ → ℂ` is entire and `G = O(‖y‖ⁿ)` at `0`, then for
`i + κ < n` the mixed coefficient `∂_t^i ∂_{t'}^κ G(0, 0)` (taken in this order) vanishes. -/
theorem iteratedDeriv_iteratedDeriv_snd_eq_zero {G : ℂ × ℂ → ℂ} (hG : AnalyticOnNhd ℂ G univ) {n κ i : ℕ}
    (h : G =O[𝓝 0] fun y => ‖y‖ ^ n) (hi : i + κ < n) :
    iteratedDeriv i (fun t => iteratedDeriv κ (fun t' => G (t, t')) 0) 0 = 0 :=
  iteratedDeriv_eq_zero_of_isBigO (analyticAt_iteratedDeriv_snd hG κ 0)
    (isBigO_iteratedDeriv_snd hG h (by omega)) i (by omega)

end TwoVar

end LSG.MEB
