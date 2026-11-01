/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.LemmaULine
import LSG.AuxFunA.LemmaUMain

/-!
# M2.6.5c: Lemma U for `MonoAV` at every point of `Y(S)`

**`lemmaU_AV`**, the analogue of `LSG.AuxA.lemmaU_A`. Data `LUDataAV`: generators `y_j` whose `G_a`-, `e^b`- and fibre
coordinates `s − M η(z)` (`sPart`) have size `(H, d)` over a number field `K` and whose block parts are periods in
`lat`, a spanning family `w_r` of `W` with coordinates of size `(H, d)`, and the entries of `M` of size `(H, d)`.
There is `c₀` such that if `Ψ = Σ p_l M_l` (`|p_l| ≤ e^B`, `G_a`/`G_m` exponents `≤ A₀, A₁`, block degree `D + F`)
satisfies `|Ψ| ≤ e^{−U}` on `V ∩ B(0, c₀ S)` and `c₀ · Bud(D + F) ≤ U`, then `Ψ` vanishes to order `≥ T` along `W` at
every `Σ h_j y_j`, `0 ≤ h_j ≤ S`.

Proof: `lemmaU_lineV` on the grid directions, then polarization. The fibre part of `Σ h_j y_j` is
`Σ h_j sPart(y_j) + M η(Σ h_j z_j)` (`η` is additive on the periods, `sPart_natComb`).
-/

open Complex Finset Module Metric LSG.W88
open scoped ContDiff Topology

noncomputable section

namespace LSG.AuxAV

open LSG.MEBV LSG.AuxA LSG.Aux
open LSG.MEB (AbBlock)

variable {K : Type*} [Field K] [NumberField K]
variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {D F : ℕ}

/-- The arithmetic data of Lemma U. -/
structure LUDataAV (ι : K →+* ℂ) (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) (μ τ : ℕ) where
  y : Fin μ → TanAV d₀ d₁ r B
  w : Fin τ → TanAV d₀ d₁ r B
  H : ℝ
  d : ℕ
  hH : 1 ≤ H
  hd : 1 ≤ d
  ha : ∀ j i, Sz ι H d ((y j).1 i)
  hb : ∀ j i, Sz ι H d (Complex.exp ((y j).2.1 i))
  hlat : ∀ j k, (y j).2.2.1 k ∈ (An k).an.lat
  hs : ∀ j i, Sz ι H d (sPart M (y j) i)
  hw0 : ∀ r i, Sz ι H d ((w r).1 i)
  hw1 : ∀ r i, Sz ι H d ((w r).2.1 i)
  hw2 : ∀ r k i, Sz ι H d ((w r).2.2.1 k i)
  hw3 : ∀ r i, Sz ι H d ((w r).2.2.2 i)
  hM : ∀ i j, Sz ι H d (M i j)

/-- `sPart` is additive on points with base parts in the periods. -/
theorem sPart_natComb (M : Matrix (Fin r) (Fin m) ℂ) {μ : ℕ} (y : Fin μ → TanAV d₀ d₁ r B)
    (hy : ∀ j k, (y j).2.2.1 k ∈ (B k).base.per) (h : Fin μ → ℕ) (i : Fin r) :
    sPart M (∑ j, h j • y j) i = ∑ j, (h j : ℂ) * sPart M (y j) i := by
  have hη : ∀ k, (B k).η ((∑ j, h j • y j).2.2.1 k) = ∑ j, (h j : ℂ) * (B k).η ((y j).2.2.1 k) := by
    intro k
    have e : (∑ j, h j • y j).2.2.1 k = ∑ j, h j • (y j).2.2.1 k := by
      rw [Prod.snd_sum, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]; rfl
    rw [e]
    -- additivity of `η` on the periods
    have hadd : ∀ (s : Finset (Fin μ)), (B k).η (∑ j ∈ s, h j • (y j).2.2.1 k) =
        ∑ j ∈ s, (h j : ℂ) * (B k).η ((y j).2.2.1 k) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [(B k).η_zero]
      | insert a s ha ih =>
        rw [sum_insert ha, sum_insert ha, (B k).η_add ((B k).base.per.nsmul_mem (hy a k) _)
          ((B k).base.per.sum_mem fun j _ => (B k).base.per.nsmul_mem (hy j k) _), ih]
        congr 1
        induction h a with
        | zero => simp [(B k).η_zero]
        | succ n ihn =>
          rw [succ_nsmul, (B k).η_add ((B k).base.per.nsmul_mem (hy a k) _) (hy a k), ihn]
          push_cast; ring
    exact hadd univ
  unfold sPart
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, etaB, hη]
  have e2 : (∑ j, h j • y j).2.2.2 i = ∑ j, (h j : ℂ) * (y j).2.2.2 i := by
    rw [Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [nsmul_eq_mul]
  rw [e2]
  simp only [mul_sub, sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

set_option maxHeartbeats 2000000 in
-- the final assembly elaborates many size hypotheses
/-- **Lemma U at every point of `Y(S)`.** -/
theorem lemmaU_AV {ι : K →+* ℂ} (An : ∀ k, VBlockAn (B k)) (Tay : ∀ k, VBlockTay (B k) ι)
    (M : Matrix (Fin r) (Fin m) ℂ) (V : Submodule ℂ (TanAV d₀ d₁ r B)) {μ τ : ℕ}
    (Dt : LUDataAV ι An M μ τ) (hyV : ∀ j, Dt.y j ∈ V) (hwV : ∀ r, Dt.w r ∈ V) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (D F L : ℕ) (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ) (S T A₀ A₁ : ℕ)
      (Bp U : ℝ), 1 ≤ S → 0 ≤ Bp → (∀ l i, (νs l).μ.α i ≤ A₀) → (∀ l j, (νs l).μ.β j ≤ A₁) →
      (∀ l, |(p l : ℝ)| ≤ Real.exp Bp) →
      (∀ z ∈ V, ‖z‖ ≤ c₀ * S → ‖PsiAV M νs p z‖ ≤ Real.exp (-U)) →
      c₀ * budU Bp L A₀ A₁ (D + F) S T ≤ U →
      ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
        VanishAlong (PsiAV M νs p) (Submodule.span ℂ (Set.range Dt.w)) T (∑ j, h j • Dt.y j) := by
  classical
  obtain ⟨ρ₀, θm, hρ₀, hρ₀1, hθm, hθm1, hθ⟩ := exists_theta_lower (Bb B)
  set Ys : ℝ := ∑ j, ‖Dt.y j‖
  set Wn : ℝ := ∑ r, ‖Dt.w r‖
  have hYs : 0 ≤ Ys := sum_nonneg fun _ _ => norm_nonneg _
  have hWn : 0 ≤ Wn := sum_nonneg fun _ _ => norm_nonneg _
  set k₀ := kLUV (d₀ := d₀) (d₁ := d₁) (r := r) An Tay μ τ Dt.H Dt.d Ys Wn ρ₀ θm
  refine ⟨max (max k₀ (Ys + 1)) 1, le_max_right _ _, ?_⟩
  intro D F L νs p S T A₀ A₁ Bp U hS hBp hα hβ hp hsm hU h hh
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hbud := bud_pos (L := L) (A₀ := A₀) (A₁ := A₁) (D := D + F) (T := T) hS hBp
  set t : TanAV d₀ d₁ r B := ∑ j, h j • Dt.y j with htdef
  have htV : t ∈ V := V.sum_mem fun j _ => V.toAddSubgroup.nsmul_mem (hyV j) _
  have htn : ‖t‖ ≤ S * Ys := norm_natComb_le h hh Dt.y
  have ht1 : ∀ i, t.1 i = ∑ j, (h j : ℂ) * (Dt.y j).1 i := fun i => by
    rw [htdef, Prod.fst_sum, Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [nsmul_eq_mul]
  have ht21 : ∀ i, t.2.1 i = ∑ j, (h j : ℂ) * (Dt.y j).2.1 i := fun i => by
    rw [htdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    simp [nsmul_eq_mul]
  have ht22 : ∀ k, t.2.2.1 k = ∑ j, h j • (Dt.y j).2.2.1 k := fun k => by
    rw [htdef, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]; rfl
  have hlat : ∀ k, t.2.2.1 k ∈ (An k).an.lat := fun k => by
    rw [ht22]; exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.nsmul_mem _ (Dt.hlat j k) _
  have hta : ∀ i, Sz ι (S * (μ + 1) * Dt.H) Dt.d (t.1 i) := fun i => by
    rw [ht1]
    refine (sz_natComb (by linarith [Dt.hH]) (fun j => Dt.ha j i) h hh).mono_le ?_
    have := Dt.hH
    gcongr; linarith
  have hts : ∀ i, Sz ι (S * (μ + 1) * Dt.H) Dt.d (sPart M t i) := fun i => by
    rw [htdef, sPart_natComb M Dt.y (fun j k => (An k).an.lat_le (Dt.hlat j k)) h i]
    refine (sz_natComb (by linarith [Dt.hH]) (fun j => Dt.hs j i) h hh).mono_le ?_
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
  refine iteratedDeriv_line_eq_zero_of_span (contDiff_PsiAV M νs p) t Dt.w k (fun c hc => ?_) hw'
  set v : TanAV d₀ d₁ r B := ∑ r, (c r : ℂ) • Dt.w r with hvdef
  have hvV : v ∈ V := V.sum_mem fun r _ => V.smul_mem _ (hwV r)
  have hc' : ∀ r, c r ≤ T := fun r => (hc r).trans hkT.le
  have hvn : ‖v‖ ≤ T * Wn := by
    have : v = ∑ r, c r • Dt.w r := by
      rw [hvdef]; refine sum_congr rfl fun r _ => ?_; rw [Nat.cast_smul_eq_nsmul]
    rw [this]; exact norm_natComb_le c hc' Dt.w
  have hTH : ∀ z, Sz ι (k * τ * Dt.H) Dt.d z → Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d z := fun z hz =>
    hz.mono_le (by
      have := Dt.hH
      have hk' : (k : ℝ) ≤ T + 1 := by
        have : (k : ℝ) < T := by exact_mod_cast hkT
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
  have hv2 : ∀ k' i, Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d (v.2.2.1 k' i) := fun k' i => by
    have e : v.2.2.1 k' i = ∑ r, (c r : ℂ) * (Dt.w r).2.2.1 k' i := by
      rw [hvdef, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Finset.sum_apply]; simp
    rw [e]; exact hTH _ (sz_natComb (by linarith [Dt.hH]) (fun r => Dt.hw2 r k' i) c hc)
  have hv3 : ∀ i, Sz ι ((T + 1) * (τ + 1) * Dt.H) Dt.d (v.2.2.2 i) := fun i => by
    have e : v.2.2.2 i = ∑ r, (c r : ℂ) * (Dt.w r).2.2.2 i := by
      rw [hvdef, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Finset.sum_apply]; simp
    rw [e]; exact hTH _ (sz_natComb (by linarith [Dt.hH]) (fun r => Dt.hw3 r i) c hc)
  have hsmall : ∀ s : ℂ, ‖s‖ ≤ ρ₀ / (1 + T * Wn) → ‖PsiAV M νs p (t + s • v)‖ ≤ Real.exp (-U) := by
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
  have hU' : k₀ * budU Bp L A₀ A₁ (D + F) S T ≤ U :=
    le_trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hbud.le) hU
  exact lemmaU_lineV An Tay M νs p hα hβ hp hBp hS t v hlat Dt.hH Dt.hd hta hte hts hv0 hv1 hv2 hv3 Dt.hM
    htn hvn hYs hWn hρ₀ hρ₀1 hθm hθm1 hθ hsmall hU' k hkT

end LSG.AuxAV
