/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.LemmaULine
import LSG.AuxFun.Polarize
import LSG.AuxFun.LemmaU

/-!
# A5.5d: Lemma U at every point of `Y(S)` (`STAGE_A5.md` D2)

**`lemmaU_A`** (the analogue of `LSG.Aux.lemmaU_core`). Data `LUDataA`: generators `y_j` whose `G_a`-coordinates
and `e^{b}`-coordinates have size `(H, d)` over a number field `K` and whose block parts are periods in `lat`, and a
spanning family `w_r` of `W` with coordinates of size `(H, d)`. There is `c₀` such that if `Ψ = Σ p_l M_l`
(`|p_l| ≤ e^B`, `G_a`/`G_m` exponents `≤ A₀, A₁`) satisfies `|Ψ| ≤ e^{−U}` on `V ∩ B(0, c₀ S)` and `c₀ · Bud ≤ U`,
then `Ψ` vanishes to order `≥ T` along `W` at every `Σ h_j y_j`, `0 ≤ h_j ≤ S`.

Proof: `lemmaU_line` on the grid directions `Σ c_r w_r` (`c_r ≤ k < T`), then polarization
(`LSG.Aux.iteratedDeriv_line_eq_zero_of_span`). The radius `ρ₀` and the lower bound `θ_m` of `|θ_{i₀}|` on
`B(0, ρ₀)` come from continuity at `0` (`exists_theta_lower`).
-/

open Complex Finset Module Metric LSG.W88
open scoped ContDiff Topology

noncomputable section

namespace LSG.AuxA

open LSG.MEB LSG.Aux

variable {K : Type*} [Field K] [NumberField K]
variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {D : ℕ}

/-- The arithmetic data of Lemma U on `G_a^{d₀} × G_m^{d₁} × ∏ B_k`. -/
structure LUDataA (ι : K →+* ℂ) (An : ∀ k, AbBlockAn (B k)) (μ τ : ℕ) where
  y : Fin μ → Tan d₀ d₁ B
  w : Fin τ → Tan d₀ d₁ B
  H : ℝ
  d : ℕ
  hH : 1 ≤ H
  hd : 1 ≤ d
  ha : ∀ j i, Sz ι H d ((y j).1 i)
  hb : ∀ j i, Sz ι H d (Complex.exp ((y j).2.1 i))
  hlat : ∀ j k, (y j).2.2 k ∈ (An k).lat
  hw0 : ∀ r i, Sz ι H d ((w r).1 i)
  hw1 : ∀ r i, Sz ι H d ((w r).2.1 i)
  hw2 : ∀ r k i, Sz ι H d ((w r).2.2 k i)

/-- A radius and a lower bound for `|θ_{i₀}|` near `0`, uniform in the blocks. -/
theorem exists_theta_lower (B : Fin m → AbBlock) :
    ∃ ρ₀ θm : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ 0 < θm ∧ θm ≤ 1 ∧
      ∀ k (z : Fin (B k).g → ℂ), ‖z‖ ≤ ρ₀ → θm ≤ ‖(B k).θ z (B k).i₀‖ := by
  have hk : ∀ k, ∃ ε > 0, ∀ z : Fin (B k).g → ℂ, ‖z‖ < ε → ‖(B k).θ 0 (B k).i₀‖ / 2 < ‖(B k).θ z (B k).i₀‖ := by
    intro k
    have hc : ContinuousAt (fun z => ‖(B k).θ z (B k).i₀‖) 0 :=
      ((analyticAt_pi_iff.mp ((B k).θ_analytic 0)) (B k).i₀).continuousAt.norm
    have h0 : 0 < ‖(B k).θ 0 (B k).i₀‖ := norm_pos_iff.mpr (B k).θ_i₀
    have := Metric.continuousAt_iff.mp hc (‖(B k).θ 0 (B k).i₀‖ / 2) (by positivity)
    obtain ⟨ε, hε, h⟩ := this
    refine ⟨ε, hε, fun z hz => ?_⟩
    have h' := h (x := z) (by simpa using hz)
    rw [Real.dist_eq, abs_lt] at h'
    linarith
  choose ε hε hεz using hk
  set c : Fin m → ℝ := fun k => ‖(B k).θ 0 (B k).i₀‖
  have hc : ∀ k, 0 < c k := fun k => norm_pos_iff.mpr (B k).θ_i₀
  refine ⟨1 / (1 + ∑ k, 2 / ε k), 1 / (1 + ∑ k, 2 / c k), ?_, ?_, ?_, ?_, ?_⟩
  · have := sum_nonneg fun k (_ : k ∈ univ) => (by have := hε k; positivity : (0 : ℝ) ≤ 2 / ε k)
    positivity
  · have := sum_nonneg fun k (_ : k ∈ univ) => (by have := hε k; positivity : (0 : ℝ) ≤ 2 / ε k)
    rw [div_le_one (by positivity)]; linarith
  · have := sum_nonneg fun k (_ : k ∈ univ) => (by have := hc k; positivity : (0 : ℝ) ≤ 2 / c k)
    positivity
  · have := sum_nonneg fun k (_ : k ∈ univ) => (by have := hc k; positivity : (0 : ℝ) ≤ 2 / c k)
    rw [div_le_one (by positivity)]; linarith
  · intro k z hz
    have hs1 : 2 / ε k ≤ ∑ k, 2 / ε k :=
      single_le_sum (f := fun k => 2 / ε k) (fun k _ => by have := hε k; positivity) (mem_univ k)
    have hs2 : 2 / c k ≤ ∑ k, 2 / c k :=
      single_le_sum (f := fun k => 2 / c k) (fun k _ => by have := hc k; positivity) (mem_univ k)
    have hεk := hε k
    have hck := hc k
    have hz' : ‖z‖ < ε k := by
      refine lt_of_le_of_lt hz ?_
      rw [div_lt_iff₀ (by have := sum_nonneg fun k (_ : k ∈ univ) =>
        (by have := hε k; positivity : (0 : ℝ) ≤ 2 / ε k); positivity)]
      have : 2 / ε k * ε k = 2 := by field_simp
      nlinarith
    refine le_trans ?_ (hεz k z hz').le
    rw [div_le_iff₀ (by have := sum_nonneg fun k (_ : k ∈ univ) =>
      (by have := hc k; positivity : (0 : ℝ) ≤ 2 / c k); positivity)]
    have : 2 / c k * c k = 2 := by field_simp
    change 1 ≤ c k / 2 * (1 + ∑ k, 2 / c k)
    nlinarith

theorem contDiff_PsiA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) : ContDiff ℂ ∞ (PsiA μs p) := by
  have hx : ∀ i, ContDiff ℂ ∞ fun u : Tan d₀ d₁ B => u.1 i := fun i => by fun_prop
  have hb : ∀ j, ContDiff ℂ ∞ fun u : Tan d₀ d₁ B => Complex.exp (u.2.1 j) := fun j => by fun_prop
  have hθ : ∀ k c, ContDiff ℂ ∞ fun u : Tan d₀ d₁ B => (B k).θ (u.2.2 k) c := fun k c =>
    (contDiff_iff_contDiffAt.mpr fun z => ((analyticAt_pi_iff.mp ((B k).θ_analytic z)) c).contDiffAt).comp
      (by fun_prop)
  unfold PsiA
  refine ContDiff.sum fun l _ => contDiff_const.mul ?_
  unfold MonoA.eval
  have h1 := contDiff_prod (t := univ) (f := fun i (u : Tan d₀ d₁ B) => u.1 i ^ (μs l).α i)
    fun i _ => (hx i).pow _
  have h2 := contDiff_prod (t := univ) (f := fun j (u : Tan d₀ d₁ B) => Complex.exp (u.2.1 j) ^ (μs l).β j)
    fun j _ => (hb j).pow _
  have h3 := contDiff_prod (t := univ)
    (f := fun k (u : Tan d₀ d₁ B) => ∏ c, (B k).θ (u.2.2 k) (fidx (B k) c) ^ (μs l).γ k c)
    fun k _ => contDiff_prod (t := univ)
      (f := fun c (u : Tan d₀ d₁ B) => (B k).θ (u.2.2 k) (fidx (B k) c) ^ (μs l).γ k c)
      fun c _ => (hθ k _).pow _
  exact (h1.mul h2).mul h3

lemma norm_natComb_le {E : Type*} [SeminormedAddCommGroup E] {μ S : ℕ} (h : Fin μ → ℕ) (hh : ∀ j, h j ≤ S)
    (y : Fin μ → E) : ‖∑ j, h j • y j‖ ≤ S * ∑ j, ‖y j‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => norm_nsmul_le.trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh j) (norm_nonneg _)

set_option maxHeartbeats 2000000 in
-- the final assembly elaborates many size hypotheses
/-- **Lemma U at every point of `Y(S)`.** -/
theorem lemmaU_A {ι : K →+* ℂ} (An : ∀ k, AbBlockAn (B k)) (Tay : ∀ k, AbBlockTay (B k) ι)
    (V : Submodule ℂ (Tan d₀ d₁ B)) {μ τ : ℕ} (Dt : LUDataA ι An μ τ) (hyV : ∀ j, Dt.y j ∈ V)
    (hwV : ∀ r, Dt.w r ∈ V) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (D L : ℕ) (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (S T A₀ A₁ : ℕ)
      (Bp U : ℝ), 1 ≤ S → 0 ≤ Bp → (∀ l i, (μs l).α i ≤ A₀) → (∀ l j, (μs l).β j ≤ A₁) →
      (∀ l, |(p l : ℝ)| ≤ Real.exp Bp) →
      (∀ z ∈ V, ‖z‖ ≤ c₀ * S → ‖PsiA μs p z‖ ≤ Real.exp (-U)) →
      c₀ * budU Bp L A₀ A₁ D S T ≤ U →
      ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
        VanishAlong (PsiA μs p) (Submodule.span ℂ (Set.range Dt.w)) T (∑ j, h j • Dt.y j) := by
  classical
  obtain ⟨ρ₀, θm, hρ₀, hρ₀1, hθm, hθm1, hθ⟩ := exists_theta_lower B
  set Ys : ℝ := ∑ j, ‖Dt.y j‖
  set Wn : ℝ := ∑ r, ‖Dt.w r‖
  have hYs : 0 ≤ Ys := sum_nonneg fun _ _ => norm_nonneg _
  have hWn : 0 ≤ Wn := sum_nonneg fun _ _ => norm_nonneg _
  set k₀ := kLU (d₀ := d₀) (d₁ := d₁) An Tay μ τ Dt.H Dt.d Ys Wn ρ₀ θm
  refine ⟨max (max k₀ (Ys + 1)) 1, le_max_right _ _, ?_⟩
  intro D L μs p S T A₀ A₁ Bp U hS hBp hα hβ hp hsm hU h hh
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hbud := bud_pos (L := L) (A₀ := A₀) (A₁ := A₁) (D := D) (T := T) hS hBp
  set t : Tan d₀ d₁ B := ∑ j, h j • Dt.y j with htdef
  have htV : t ∈ V := V.sum_mem fun j _ => V.toAddSubgroup.nsmul_mem (hyV j) _
  have htn : ‖t‖ ≤ S * Ys := norm_natComb_le h hh Dt.y
  -- the coordinates of `t`
  have ht1 : ∀ i, t.1 i = ∑ j, (h j : ℂ) * (Dt.y j).1 i := fun i => by
    rw [htdef, Prod.fst_sum, Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [nsmul_eq_mul]
  have ht21 : ∀ i, t.2.1 i = ∑ j, (h j : ℂ) * (Dt.y j).2.1 i := fun i => by
    rw [htdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [nsmul_eq_mul]
  have ht22 : ∀ k, t.2.2 k = ∑ j, h j • (Dt.y j).2.2 k := fun k => by
    rw [htdef, Prod.snd_sum, Prod.snd_sum, Finset.sum_apply]; rfl
  have hlat : ∀ k, t.2.2 k ∈ (An k).lat := fun k => by
    rw [ht22]; exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.nsmul_mem _ (Dt.hlat j k) _
  have hta : ∀ i, Sz ι (S * (μ + 1) * Dt.H) Dt.d (t.1 i) := fun i => by
    rw [ht1]
    refine (sz_natComb (by linarith [Dt.hH]) (fun j => Dt.ha j i) h hh).mono_le ?_
    have := Dt.hH
    gcongr; linarith
  have hte : ∀ i, Sz ι (Dt.H ^ (μ * S)) (Dt.d ^ (μ * S)) (Complex.exp (t.2.1 i)) := fun i => by
    have e : Complex.exp (t.2.1 i) = ∏ j, Complex.exp ((Dt.y j).2.1 i) ^ h j := by
      rw [ht21, Complex.exp_sum]
      refine prod_congr rfl fun j _ => ?_
      rw [← Complex.exp_nat_mul]
    rw [e]; exact sz_expComb Dt.hH (fun j => Dt.hb j i) h hh
  intro w' hw' k hk
  have hkT : k < T := by exact_mod_cast hk
  refine iteratedDeriv_line_eq_zero_of_span (contDiff_PsiA μs p) t Dt.w k (fun c hc => ?_) hw'
  set v : Tan d₀ d₁ B := ∑ r, (c r : ℂ) • Dt.w r with hvdef
  have hvV : v ∈ V := V.sum_mem fun r _ => V.smul_mem _ (hwV r)
  have hc' : ∀ r, c r ≤ T := fun r => (hc r).trans hkT.le
  have hvn : ‖v‖ ≤ T * Wn := by
    have : v = ∑ r, c r • Dt.w r := by
      rw [hvdef]; refine sum_congr rfl fun r _ => ?_; rw [Nat.cast_smul_eq_nsmul]
    rw [this]; exact norm_natComb_le c hc' Dt.w
  have hTH : ∀ z, Sz ι (k * τ * Dt.H) Dt.d z → Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d z := fun z hz =>
    hz.mono_le (by
      have := Dt.hH
      have hk' : (k : ℝ) ≤ T + 1 := by have : (k : ℝ) < T := by exact_mod_cast hkT
                                       linarith
      gcongr; linarith)
  have hv0 : ∀ i, Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d (v.1 i) := fun i => by
    have e : v.1 i = ∑ r, (c r : ℂ) * (Dt.w r).1 i := by
      rw [hvdef, Prod.fst_sum, Finset.sum_apply]; simp
    rw [e]; exact hTH _ (sz_natComb (by linarith [Dt.hH]) (fun r => Dt.hw0 r i) c hc)
  have hv1 : ∀ i, Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d (v.2.1 i) := fun i => by
    have e : v.2.1 i = ∑ r, (c r : ℂ) * (Dt.w r).2.1 i := by
      rw [hvdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]; simp
    rw [e]; exact hTH _ (sz_natComb (by linarith [Dt.hH]) (fun r => Dt.hw1 r i) c hc)
  have hv2 : ∀ k' i, Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d (v.2.2 k' i) := fun k' i => by
    have e : v.2.2 k' i = ∑ r, (c r : ℂ) * (Dt.w r).2.2 k' i := by
      rw [hvdef, Prod.snd_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_apply]; simp
    rw [e]; exact hTH _ (sz_natComb (by linarith [Dt.hH]) (fun r => Dt.hw2 r k' i) c hc)
  have hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₀ / (1 + T * Wn) → ‖PsiA μs p (t + s • v)‖ ≤ Real.exp (-U) := by
    intro s hs
    refine hsm _ (V.add_mem htV (V.smul_mem s hvV)) ?_
    have h1TW : 0 < 1 + T * Wn := by positivity
    have hsv : ‖s • v‖ ≤ ρ₀ := by
      rw [norm_smul]
      calc ‖s‖ * ‖v‖ ≤ ρ₀ / (1 + T * Wn) * (T * Wn) := mul_le_mul hs hvn (norm_nonneg _) (by positivity)
        _ ≤ ρ₀ / (1 + T * Wn) * (1 + T * Wn) := by gcongr; linarith
        _ = ρ₀ := by field_simp
    calc ‖t + s • v‖ ≤ ‖t‖ + ‖s • v‖ := norm_add_le _ _
      _ ≤ S * Ys + 1 := by linarith
      _ ≤ (Ys + 1) * S := by nlinarith
      _ ≤ max (max k₀ (Ys + 1)) 1 * S := by
          gcongr; exact (le_max_right _ _).trans (le_max_left _ _)
  have hU' : k₀ * budU Bp L A₀ A₁ D S T ≤ U :=
    le_trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hbud.le) hU
  exact lemmaU_line An Tay μs p hα hβ hp hBp hS t v hlat Dt.hH Dt.hd hta hte hv0 hv1 hv2 htn hvn hYs hWn
    hρ₀ hρ₀1 hθm hθm1 hθ hsmall hU' k hkT

end LSG.AuxA
