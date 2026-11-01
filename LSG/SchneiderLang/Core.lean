/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.SchneiderLang.Setup
import LSG.SchneiderLang.Analytic
import LSG.SchneiderLang.Arith

/-!
# Schneider–Lang: the core argument

Fix a number field `K` with an embedding `σ : K → ℂ`, entire `gᵢ, h` of order `≤ ρ`, `fᵢ = gᵢ/h`
with `fᵢ' = Qᵢ(f)` on `{h ≠ 0}`, `f_{i₁}, f_{i₂}` algebraically independent, and `m > 4 [K:ℚ] ρ`
distinct points `w_j` with `h(w_j) ≠ 0`, `fᵢ(w_j) = σ(x_{ji})`. Then `False`.

Proof (Lang, *Introduction to transcendental numbers*, Ch. III):
1. rescale (`d₀`) so that the derivation `Dop Q̂` and the values `y_{ji} = d₀ x_{ji}` are integral;
2. Siegel: `F = ∑ ξ_{ab} (d₀f_{i₁})^a (d₀f_{i₂})^b`, `ξ ∈ 𝓞 K` not all `0`, vanishing to order `M`
   at all `w_j`;
3. `G = h^{2L} F` is entire and `≢ 0` (algebraic independence); let `s ≥ M` be the least order of
   `G` at the `w_j`, attained at `w_ν`;
4. `γ = Dop^s(P)(y_ν) ∈ 𝓞 K` is nonzero: Liouville gives a lower bound; Schwarz (radius
   `R = s^{1/(2ρ)}`) + Cauchy give an upper bound; `final_ineq` makes them incompatible.
-/

open MvPolynomial Finset NumberField Filter Topology Complex

namespace LSG.SL

set_option maxHeartbeats 4000000 in
theorem core {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) {N : ℕ}
    (g : Fin N → ℂ → ℂ) (h : ℂ → ℂ) (ρ : ℕ) (hρ : 1 ≤ ρ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ i, Differentiable ℂ (g i)) (hh : Differentiable ℂ h)
    (hgC : ∀ i z, ‖g i z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ))
    (hhC : ∀ z, ‖h z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ))
    (Q : Fin N → MvPolynomial (Fin N) K)
    (hQ : ∀ i z, h z ≠ 0 →
      HasDerivAt (fun x => g i x / h x) (eval₂ σ (fun j => g j z / h z) (Q i)) z)
    (i₁ i₂ : Fin N)
    (hind : ∀ P : MvPolynomial (Fin 2) K,
      (∀ z, h z ≠ 0 → eval₂ σ ![g i₁ z / h z, g i₂ z / h z] P = 0) → P = 0)
    (m : ℕ) (hm : 4 * Module.finrank ℚ K * ρ < m) (w : Fin m → ℂ) (hw : Function.Injective w)
    (hwh : ∀ j, h (w j) ≠ 0) (x : Fin m → Fin N → K)
    (hx : ∀ j i, g i (w j) / h (w j) = σ (x j i)) : False := by
  classical
  set d := Module.finrank ℚ K with hd_def
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hm0 : 0 < m := by
    have : 0 < 4 * d * ρ := by positivity
    omega
  have hN : 0 < N := Fin.pos i₁
  /- Step 1: denominators, rescaling, constants. -/
  obtain ⟨d₀, hd₀1, hd₀int⟩ := exists_common_denom
    ((univ.image fun p : Fin m × Fin N => x p.1 p.2) ∪
      (univ.biUnion fun i => (Q i).support.image fun α => (Q i).coeff α))
  have hdx : ∀ j i, IsIntegral ℤ ((d₀ : K) * x j i) := fun j i =>
    hd₀int _ (mem_union_left _ (mem_image.mpr ⟨(j, i), mem_univ _, rfl⟩))
  have hdQ : ∀ i α, IsIntegral ℤ ((d₀ : K) * (Q i).coeff α) := by
    intro i α
    by_cases hα : α ∈ (Q i).support
    · exact hd₀int _ (mem_union_right _
        (mem_biUnion.mpr ⟨i, mem_univ _, mem_image.mpr ⟨α, hα, rfl⟩⟩))
    · rw [notMem_support_iff.mp hα, mul_zero]; exact isIntegral_zero
  set δ : ℕ := 1 + ∑ i, (Q i).totalDegree with hδ_def
  have hδQ : ∀ i, (Q i).totalDegree ≤ δ := fun i => by
    have := single_le_sum (f := fun i => (Q i).totalDegree) (fun _ _ => Nat.zero_le _)
      (mem_univ i)
    omega
  choose Qh hQhdeg hQheval using fun i => exists_scaled σ (Q i) d₀ (hdQ i) (hδQ i)
  set φ : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K) with hφ
  set B : ℝ := 1 + ∑ i, hsum (Qh i) with hB_def
  have hB : ∀ i, hsum (Qh i) ≤ B := fun i => by
    have := single_le_sum (f := fun i => hsum (Qh i)) (fun _ _ => hsum_nonneg _) (mem_univ i)
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ i, hsum (Qh i) := sum_nonneg fun _ _ => hsum_nonneg _
    linarith
  have hβ : 1 ≤ (N : ℝ) * B := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hN) hB1
  let y : Fin m → Fin N → 𝓞 K := fun j i => ⟨(d₀ : K) * x j i, hdx j i⟩
  have hφy : ∀ j i, φ (y j i) = (d₀ : ℂ) * σ (x j i) := by
    intro j i
    change σ ((d₀ : K) * x j i) = _
    rw [map_mul, map_natCast]
  set Y0 : ℝ := 1 + ∑ j, ∑ i, house ((y j i : 𝓞 K) : K) with hY0
  have hY : ∀ j i, house ((y j i : 𝓞 K) : K) ≤ Y0 := by
    intro j i
    have h1 := single_le_sum (f := fun i => house ((y j i : 𝓞 K) : K))
      (fun _ _ => house_nonneg _) (mem_univ i)
    have h2 := single_le_sum (f := fun j => ∑ i, house ((y j i : 𝓞 K) : K))
      (fun _ _ => sum_nonneg fun _ _ => house_nonneg _) (mem_univ j)
    linarith
  have hY1 : 1 ≤ Y0 := by
    have : 0 ≤ ∑ j, ∑ i, house ((y j i : 𝓞 K) : K) :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => house_nonneg _
    linarith
  obtain ⟨c, hc0, hsiegel⟩ := siegel K
  set r : ℝ := 2 + ∑ j, ‖w j‖ with hr_def
  have hwr : ∀ j, ‖w j‖ + 1 ≤ r := by
    intro j
    have := single_le_sum (f := fun j => ‖w j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hr1 : 1 ≤ r := by
    have : 0 ≤ ∑ j, ‖w j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  set h₀ : ℝ := ∏ j, min 1 ‖h (w j)‖ with hh₀_def
  have hh₀pos : 0 < h₀ := prod_pos fun j _ => lt_min one_pos (norm_pos_iff.mpr (hwh j))
  have hmin0 : ∀ j ∈ (univ : Finset (Fin m)), 0 ≤ min 1 ‖h (w j)‖ :=
    fun j _ => le_min zero_le_one (norm_nonneg _)
  have hmin1 : ∀ j ∈ (univ : Finset (Fin m)), min 1 ‖h (w j)‖ ≤ 1 := fun j _ => min_le_left _ _
  have hh₀1 : h₀ ≤ 1 := prod_le_one₀ hmin0 hmin1
  have hh₀le : ∀ j, h₀ ≤ ‖h (w j)‖ := by
    intro j
    rw [hh₀_def, ← mul_prod_erase univ (fun j => min 1 ‖h (w j)‖) (mem_univ j)]
    calc min 1 ‖h (w j)‖ * ∏ k ∈ univ.erase j, min 1 ‖h (w k)‖ ≤ min 1 ‖h (w j)‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (prod_le_one₀ (fun k hk => hmin0 k (mem_of_mem_erase hk))
              (fun k hk => hmin1 k (mem_of_mem_erase hk))) (hmin0 j (mem_univ j))
      _ ≤ ‖h (w j)‖ := by rw [mul_one]; exact min_le_right _ _
  /- Step 2: parameters. -/
  obtain ⟨n, hn2, hpar⟩ := final_ineq (d := d) (m := m) (ρ := ρ) (δ := δ) (d₀ := d₀)
    (β := N * B) (Y := Y0) (c := c) (C := C) (r := r) (h₀ := h₀) hd1 hρ hm hd₀1 hβ hY1 hc0 hC
    hr1 hh₀pos hh₀1
  set L : ℕ := 2 * m * n with hL
  set M : ℕ := m * n ^ 2 with hM
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  /- Step 3: Siegel's lemma. -/
  set Dk := Dop Qh with hDk
  let A : Matrix (Fin m × Fin M) (Fin L × Fin L) (𝓞 K) := fun jk ab =>
    eval (y jk.1) ((Dk ^ (jk.2 : ℕ)) (mon i₁ i₂ ab.1 ab.2))
  have hA0 : A ≠ 0 := by
    intro hA
    have h1 := congrFun (congrFun hA (⟨0, hm0⟩, ⟨0, hM1⟩)) (⟨0, hL1⟩, ⟨0, hL1⟩)
    simp [A, mon] at h1
  have hcardα : Fintype.card (Fin m × Fin M) = m * M := by simp
  have hcardβ : Fintype.card (Fin L × Fin L) = L * L := by simp
  have hentry : ∀ jk ab, house ((A jk ab : 𝓞 K) : K) ≤ Abd (N * B) Y0 δ L M := fun jk ab =>
    (house_entry_le Qh (by linarith) hB hQhdeg i₁ i₂ ab.1.isLt.le ab.2.isLt.le _ (y jk.1) hY1
      (hY jk.1)).trans (Abd_mono hβ hY1 δ L hL1 jk.2.isLt.le)
  have hAbd1 := one_le_Abd hβ hY1 δ L M hL1
  have hpq : 2 * Fintype.card (Fin m × Fin M) ≤ Fintype.card (Fin L × Fin L) := by
    rw [hcardα, hcardβ]
    calc 2 * (m * M) = 2 * (m * m * n * n) := by rw [hM]; ring
      _ ≤ 4 * (m * m * n * n) := Nat.mul_le_mul_right _ (by norm_num)
      _ = L * L := by rw [hL]; ring
  obtain ⟨ξ, hξ0, hξA, hξb⟩ := hsiegel A hA0 (by rw [hcardα]; positivity) hpq _
    (by linarith) hentry
  set Hs : ℝ := Hbd c L (Abd (N * B) Y0 δ L M) with hHs
  have hξH : ∀ ab, house ((ξ ab : 𝓞 K) : K) ≤ Hs := by
    intro ab
    have := hξb ab
    rw [hcardβ] at this
    exact this
  have hHs0 : 0 ≤ Hs := (house_nonneg _).trans (hξH (⟨0, hL1⟩, ⟨0, hL1⟩))
  /- Step 4: the auxiliary polynomial and functions. -/
  let Pc : MvPolynomial (Fin N) (𝓞 K) := ∑ ab : Fin L × Fin L, ξ ab • mon i₁ i₂ ab.1 ab.2
  have hDPc : ∀ k (yv : Fin N → 𝓞 K), eval yv ((Dk ^ k) Pc) =
      ∑ ab : Fin L × Fin L, ξ ab * eval yv ((Dk ^ k) (mon i₁ i₂ ab.1 ab.2)) := by
    intro k yv
    simp only [Pc, map_sum, map_smul, smul_eval]
  have hvan : ∀ j, ∀ k < M, eval (y j) ((Dk ^ k) Pc) = 0 := by
    intro j k hk
    have h1 := congrFun hξA (j, ⟨k, hk⟩)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, A] at h1
    rw [hDPc, ← h1]
    exact sum_congr rfl fun ab _ => mul_comm _ _
  let u : ℂ → Fin N → ℂ := fun z i => (d₀ : ℂ) * (g i z / h z)
  let F : ℂ → ℂ := fun z => eval₂ φ (u z) Pc
  set U : Set ℂ := {z | h z ≠ 0} with hU_def
  have hU : IsOpen U := isOpen_ne_fun hh.continuous continuous_const
  have hd₀C : (d₀ : ℂ) ≠ 0 := by exact_mod_cast (show d₀ ≠ 0 by omega)
  set c' : ℂ := ((d₀ : ℂ) ^ δ)⁻¹ with hc'
  have hu : ∀ z ∈ U, ∀ i, HasDerivAt (fun x => u x i) (c' * eval₂ φ (u z) (Qh i)) z := by
    intro z hz i
    have h1 := (hQ i z hz).const_mul (d₀ : ℂ)
    have h2 := hQheval i (fun j => g j z / h z)
    convert h1 using 1
    change c' * eval₂ φ (fun i => (d₀ : ℂ) * (g i z / h z)) (Qh i) = _
    rw [h2, hc', pow_succ]
    field_simp
  have hFder : ∀ z ∈ U, ∀ k, iteratedDeriv k F z = c' ^ k * eval₂ φ (u z) ((Dk ^ k) Pc) :=
    fun z hz k => iteratedDeriv_eval₂_Dop φ Qh hU c' hu Pc k z hz
  have hFan : ∀ z ∈ U, AnalyticAt ℂ F z := by
    intro z hz
    have hdiff : DifferentiableOn ℂ F U := fun v hv =>
      (hasDerivAt_Dop φ Qh (hu v hv) Pc).differentiableAt.differentiableWithinAt
    exact hdiff.analyticAt (hU.mem_nhds hz)
  have huw : ∀ j, u (w j) = fun i => φ (y j i) := by
    intro j
    funext i
    change (d₀ : ℂ) * (g i (w j) / h (w j)) = _
    rw [hx j i, hφy]
  have hevw : ∀ j P, eval₂ φ (u (w j)) P = φ (eval (y j) P) := by
    intro j P
    rw [huw]
    change _ = φ (eval₂ (RingHom.id _) (y j) P)
    rw [hom_eval₂, RingHom.comp_id]
  let G : ℂ → ℂ := fun z => ∑ ab : Fin L × Fin L, φ (ξ ab) * (((d₀ : ℂ) * g i₁ z) ^ (ab.1 : ℕ) *
    ((d₀ : ℂ) * g i₂ z) ^ (ab.2 : ℕ) * h z ^ (2 * L - ab.1 - ab.2))
  have hGd : Differentiable ℂ G := by
    have h1 := hg i₁
    have h2 := hg i₂
    fun_prop
  have hFexp : ∀ z, F z = ∑ ab : Fin L × Fin L,
      φ (ξ ab) * (u z i₁ ^ (ab.1 : ℕ) * u z i₂ ^ (ab.2 : ℕ)) := by
    intro z
    simp only [F, Pc, eval₂_sum, smul_eq_C_mul, eval₂_mul, eval₂_C, mon, eval₂_pow, eval₂_X]
  have hGF : ∀ z ∈ U, G z = h z ^ (2 * L) * F z := by
    intro z hz
    have hz' : h z ≠ 0 := hz
    rw [hFexp, mul_sum]
    refine sum_congr rfl fun ab _ => ?_
    have hab : (ab.1 : ℕ) + ab.2 ≤ 2 * L := by
      have := ab.1.isLt; have := ab.2.isLt; omega
    have hpow : h z ^ (2 * L) = h z ^ (2 * L - ab.1 - ab.2) * h z ^ (ab.1 : ℕ) *
        h z ^ (ab.2 : ℕ) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hpow]
    simp only [u, div_pow, mul_pow]
    field_simp
  /- Step 5: `G ≢ 0`. -/
  let P2 : MvPolynomial (Fin 2) K := ∑ ab : Fin L × Fin L,
    monomial (expo ab.1 ab.2) ((ξ ab : K) * (d₀ : K) ^ ((ab.1 : ℕ) + ab.2))
  have hd₀K : (d₀ : K) ≠ 0 := by exact_mod_cast (show d₀ ≠ 0 by omega)
  have hP2 : P2 ≠ 0 := by
    apply poly2_ne_zero
    intro h0
    apply hξ0
    funext ab
    have h1 := congrFun h0 ab
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hd₀K, false_and, or_false] at h1
    simpa using h1
  have hP2eval : ∀ z, eval₂ σ ![g i₁ z / h z, g i₂ z / h z] P2 = F z := by
    intro z
    rw [hFexp]
    simp only [P2, eval₂_sum, eval₂_monomial_expo]
    refine sum_congr rfl fun ab _ => ?_
    simp only [u, map_mul, map_pow, map_natCast, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_pow, pow_add]
    rw [show φ (ξ ab) = σ ((ξ ab : 𝓞 K) : K) from rfl]
    ring
  obtain ⟨z₀, hz₀, hFz₀⟩ : ∃ z, h z ≠ 0 ∧ F z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP2 (hind P2 fun z hz => by rw [hP2eval]; exact hcon z hz)
  have hG0 : G ≠ 0 := by
    intro h0
    have h1 := congrFun h0 z₀
    rw [Pi.zero_apply, hGF z₀ hz₀] at h1
    exact mul_ne_zero (pow_ne_zero _ hz₀) hFz₀ h1
  have hGan : ∀ z, AnalyticAt ℂ G z := fun z => hGd.analyticAt z
  have hGtop : ∀ v, analyticOrderAt G v ≠ ⊤ := fun v h0 =>
    hG0 ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero v hGan).mp h0)
  /- Step 6: orders of vanishing. -/
  have hGev : ∀ z ∈ U, G =ᶠ[𝓝 z] (fun v => h v ^ (2 * L)) * F := fun z hz => by
    filter_upwards [hU.mem_nhds hz] with v hv using hGF v hv
  have hordGF : ∀ j, analyticOrderAt G (w j) = analyticOrderAt F (w j) := by
    intro j
    rw [analyticOrderAt_congr (hGev _ (hwh j)),
      analyticOrderAt_mul (show AnalyticAt ℂ (fun v => h v ^ (2 * L)) (w j) from
        (hh.analyticAt _).pow _) (hFan _ (hwh j)),
      (analyticOrderAt_eq_zero (f := fun v => h v ^ (2 * L)) (z₀ := w j)).mpr
        (Or.inr (pow_ne_zero _ (hwh j))), zero_add]
  have hordM : ∀ j, (M : ℕ∞) ≤ analyticOrderAt G (w j) := by
    intro j
    rw [hordGF, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFan _ (hwh j))]
    intro k hk
    rw [hFder _ (hwh j), hevw, hvan j k hk, map_zero, mul_zero]
  have : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
  obtain ⟨ν, -, hν⟩ := exists_min_image univ (fun j => analyticOrderNatAt G (w j)) univ_nonempty
  set s := analyticOrderNatAt G (w ν) with hs_def
  have hsord : ∀ j, (s : ℕ∞) ≤ analyticOrderAt G (w j) := by
    intro j
    rw [← Nat.cast_analyticOrderNatAt (hGtop (w j))]
    exact_mod_cast hν j (mem_univ _)
  have hsν : analyticOrderAt F (w ν) = s := by
    rw [← hordGF, hs_def, Nat.cast_analyticOrderNatAt (hGtop _)]
  have hMs : M ≤ s := by
    have h1 := hordM ν
    rw [← Nat.cast_analyticOrderNatAt (hGtop _)] at h1
    exact_mod_cast h1
  obtain ⟨hvanν, hnzν⟩ :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hFan _ (hwh ν))).mp hsν
  /- Step 7: the algebraic number `γ` and Liouville. -/
  set γ : 𝓞 K := eval (y ν) ((Dk ^ s) Pc) with hγ_def
  have hγF : iteratedDeriv s F (w ν) = c' ^ s * φ γ := by rw [hFder _ (hwh ν), hevw]
  have hγ0 : γ ≠ 0 := by
    intro h0
    apply hnzν
    rw [hγF, h0, map_zero, mul_zero]
  have hliou := one_le_norm_mul_house_pow γ hγ0 σ
  have hhouse : house ((γ : 𝓞 K) : K) ≤
      ((L * L : ℕ) : ℝ) * Hs * Abd (N * B) Y0 δ L s := by
    have e : ((γ : 𝓞 K) : K) = ∑ ab : Fin L × Fin L,
        ((ξ ab : 𝓞 K) : K) * ((eval (y ν) ((Dk ^ s) (mon i₁ i₂ ab.1 ab.2)) : 𝓞 K) : K) := by
      rw [hγ_def, hDPc]
      simp only [map_sum, map_mul]
    rw [e]
    refine (house_sum_le' _ _).trans ?_
    calc ∑ ab : Fin L × Fin L, house (((ξ ab : 𝓞 K) : K) *
          ((eval (y ν) ((Dk ^ s) (mon i₁ i₂ ab.1 ab.2)) : 𝓞 K) : K))
        ≤ ∑ _ab : Fin L × Fin L, Hs * Abd (N * B) Y0 δ L s :=
          sum_le_sum fun ab _ => (house_mul_le _ _).trans (mul_le_mul (hξH ab)
            (house_entry_le Qh (by linarith) hB hQhdeg i₁ i₂ ab.1.isLt.le ab.2.isLt.le s (y ν)
              hY1 (hY ν)) (house_nonneg _) hHs0)
      _ = ((L * L : ℕ) : ℝ) * Hs * Abd (N * B) Y0 δ L s := by
          rw [sum_const, card_univ, hcardβ, nsmul_eq_mul]; ring
  /- Step 8: the analytic upper bound. -/
  obtain ⟨h2r, hfin⟩ := hpar n le_rfl L M rfl rfl s hMs
  set R := Rad ρ s with hR_def
  have hrR : r < R := by linarith
  set E : ℝ := Real.exp (C * (1 + R) ^ ρ) with hE_def
  have hR0 : 0 < R := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set Bg : ℝ := ((L * L : ℕ) : ℝ) * Hs * (d₀ : ℝ) ^ (2 * L) * E ^ (2 * L) with hBg
  have hGR : ∀ v : ℂ, ‖v‖ = R → ‖G v‖ ≤ Bg := by
    intro v hv
    have hgv : ∀ i, ‖g i v‖ ≤ E := fun i => by
      have := hgC i v
      rwa [hv] at this
    have hhv : ‖h v‖ ≤ E := by
      have := hhC v
      rwa [hv] at this
    exact norm_G_le (fun ab => φ (ξ ab)) (fun ab => (norm_embedding_le_house _ σ).trans (hξH ab))
      _ _ _ hE1 d₀ hd₀1 (hgv i₁) (hgv i₂) hhv
  have hZ : (univ.image w).card = m := by
    rw [card_image_of_injective _ hw, card_univ, Fintype.card_fin]
  have hDG := norm_iteratedDeriv_le_of_zeros hGd (univ.image w) s
    (fun v hv => by obtain ⟨j, -, rfl⟩ := mem_image.mp hv; exact hsord j) hrR
    (fun v hv => by obtain ⟨j, -, rfl⟩ := mem_image.mp hv; linarith [hwr j]) hGR (hwr ν)
  rw [hZ] at hDG
  have hLeib : iteratedDeriv s G (w ν) = h (w ν) ^ (2 * L) * iteratedDeriv s F (w ν) := by
    rw [(hGev _ (hwh ν)).iteratedDeriv_eq s]
    exact iteratedDeriv_mul_eq_of_vanish (show AnalyticAt ℂ (fun v => h v ^ (2 * L)) (w ν) from
      (hh.analyticAt _).pow _).contDiffAt
      (hFan _ (hwh ν)).contDiffAt hvanν
  have hhν : h (w ν) ≠ 0 := hwh ν
  have hσγ : ‖σ ((γ : 𝓞 K) : K)‖ ≤ (d₀ : ℝ) ^ (δ * s) * s.factorial *
      (Bg * (2 * r / (R - r)) ^ (s * m)) / h₀ ^ (2 * L) := by
    have e1 : σ ((γ : 𝓞 K) : K) = (d₀ : ℂ) ^ (δ * s) * (iteratedDeriv s G (w ν) / h (w ν) ^ (2 * L)) := by
      rw [hLeib, mul_div_cancel_left₀ _ (pow_ne_zero _ hhν), hγF, hc', inv_pow, ← pow_mul,
        mul_comm δ s]
      change φ γ = _
      field_simp
    rw [e1, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    have hhpow : h₀ ^ (2 * L) ≤ ‖h (w ν)‖ ^ (2 * L) := pow_le_pow_left₀ hh₀pos.le (hh₀le ν) _
    have hnum0 : 0 ≤ (s.factorial : ℝ) * (Bg * (2 * r / (R - r)) ^ (s * m)) :=
      (norm_nonneg _).trans hDG
    calc (d₀ : ℝ) ^ (δ * s) * (‖iteratedDeriv s G (w ν)‖ / ‖h (w ν)‖ ^ (2 * L))
        ≤ (d₀ : ℝ) ^ (δ * s) * ((s.factorial : ℝ) * (Bg * (2 * r / (R - r)) ^ (s * m)) /
            h₀ ^ (2 * L)) := by
          gcongr
      _ = _ := by ring
  /- Step 9: contradiction. -/
  have hkey := hliou.trans (mul_le_mul hσγ (pow_le_pow_left₀ (house_nonneg _) hhouse _)
    (pow_nonneg (house_nonneg _) _) ((norm_nonneg _).trans hσγ))
  linarith

end LSG.SL
