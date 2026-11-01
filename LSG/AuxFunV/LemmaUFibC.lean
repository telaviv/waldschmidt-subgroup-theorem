/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.LemmaUArithV
import LSG.AuxFunV.DefectSizeMain

/-!
# Lemma U for the class `𝒞`: data and the constants of the fibre factors

* `LUDataV`: the arithmetic data of Lemma U for `G ∈ 𝒞` (the abelian `LUData` plus the fibre
  values `s_j − M ζ(z_j)` of the generators, the fibre coordinates of `W`, the entries of `M`, and
  `g₂, g₃` themselves).
* `cstOf t i = sᵢ(t) − Σ_j M_ij W_j(t_j)`: the constants of the fibre factors (`FpolyV_eq`).
* **`cstOf_eq`**: `cstOf t i = Σ_k h_k (s_k − Mζ(z_k))ᵢ + Σ_j M_ij (D_j(h) − zdef(t_j + z₀, z₀))`
  for `t = Σ h_k y_k` (`fibreValue_sum`).
* **`exists_fib_consts`**: there is `c_F` with `cstOf t i` and `(2 λ_k(X'_k))⁻¹` of size
  `e^{c_F S²}` for all `h ≤ S` (accumulated defects `exists_defect_sizes_S`, the defect at the
  translation `exists_defect_frac`, inverses `sz_inv`).
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair LSG.W88 LSG.W88.Vec
open LSG.Aux (IsRep Sz zh isRep_half exists_alg_points_S sz_natComb)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}
variable {K : Type*} [Field K] [NumberField K]

/-- The arithmetic data of Lemma U for the class `𝒞`. -/
structure LUDataV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (ι : K →+* ℂ)
    (μ τ : ℕ) where
  y : Fin μ → TanV d0 d1 m r
  w : Fin τ → TanV d0 d1 m r
  X₀ : Fin μ → Fin m → Fin 3 → ℂ
  γ₂ : Fin m → K
  γ₃ : Fin m → K
  H : ℝ
  d : ℕ
  hH : 1 ≤ H
  hd : 1 ≤ d
  hγ₂ : ∀ k, ι (γ₂ k) = (Ls k).g₂
  hγ₃ : ∀ k, ι (γ₃ k) = (Ls k).g₃
  ha : ∀ j i, Sz ι H d ((y j).1 i)
  hb : ∀ j i, Sz ι H d (exp ((y j).2.1 i))
  hX₀ : ∀ j k, IsRep (Ls k) ((y j).2.2.1 k) (X₀ j k)
  hX₀s : ∀ j k i, Sz ι H d (X₀ j k i)
  hw0 : ∀ r i, Sz ι H d ((w r).1 i)
  hw1 : ∀ r i, Sz ι H d ((w r).2.1 i)
  hw2 : ∀ r k, Sz ι H d ((w r).2.2.1 k)
  hw3 : ∀ r i, Sz ι H d ((w r).2.2.2 i)
  he₁ : ∀ k, Sz ι H d (℘[Ls k] (zh (Ls k)))
  hg₂ : ∀ k, Sz ι H d ((Ls k).g₂ / 2)
  hg₂' : ∀ k, Sz ι H d (Ls k).g₂
  hg₃' : ∀ k, Sz ι H d (Ls k).g₃
  hτ : ∀ j i, Sz ι H d ((y j).2.2.2 i - M.mulVec (zetaV Ls (y j).2.2.1) i)
  hM : ∀ i j, Sz ι H d (M i j)

/-- The constants of the fibre factors at `t`. -/
def cstOf (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (t : TanV d0 d1 m r)
    (i : Fin r) : ℂ :=
  t.2.2.2 i - ∑ j, M i j * Wpar (Ls j) (t.2.2.1 j)

lemma zh_add_zh (L : PeriodPair) : zh L + zh L = L.ω₁ := by simp only [zh]; ring

lemma Wpar_eq (L : PeriodPair) (u : ℂ) : Wpar L u = zeta L u + zdef L (u + zh L) (zh L) := by
  have h := zeta_add L L.ω₁_mem_lattice u
  rw [Wpar, zdef, add_assoc u, zh_add_zh, h]; ring

/-- **The constants of the fibre factors along `Σ h_k y_k`.** -/
theorem cstOf_eq {μ : ℕ} (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (y : Fin μ → TanV d0 d1 m r) (h : Fin μ → ℕ) (i : Fin r) :
    cstOf Ls M (∑ k, h k • y k) i =
      ∑ k, (h k : ℂ) * ((y k).2.2.2 i - M.mulVec (zetaV Ls (y k).2.2.1) i) +
        ∑ j, M i j * (Dsum (Ls j) (fun k => (y k).2.2.1 j) h -
          zdef (Ls j) ((∑ k, h k • y k).2.2.1 j + zh (Ls j)) (zh (Ls j))) := by
  have hv := congrFun (fibreValue_sum Ls M y h) i
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hv
  unfold cstOf
  simp only [Wpar_eq, mul_add, sum_add_distrib]
  have hz : ∑ j, M i j * zeta (Ls j) ((∑ k, h k • y k).2.2.1 j) =
      M.mulVec (zetaV Ls (∑ k, h k • y k).2.2.1) i := by
    simp [Matrix.mulVec, dotProduct, zetaV]
  have hD : (M.mulVec fun j => Dsum (Ls j) (fun k => (y k).2.2.1 j) h) i =
      ∑ j, M i j * Dsum (Ls j) (fun k => (y k).2.2.1 j) h := by
    simp [Matrix.mulVec, dotProduct]
  rw [hz]
  have hj : ∑ j, M i j * (Dsum (Ls j) (fun k => (y k).2.2.1 j) h -
      zdef (Ls j) ((∑ k, h k • y k).2.2.1 j + zh (Ls j)) (zh (Ls j))) =
      ∑ j, M i j * Dsum (Ls j) (fun k => (y k).2.2.1 j) h -
        ∑ j, M i j * zdef (Ls j) ((∑ k, h k • y k).2.2.1 j + zh (Ls j)) (zh (Ls j)) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  rw [hj, ← hD]
  linear_combination hv

variable {ι : K →+* ℂ}

lemma szS_of_sz {A : ℝ} {d : ℕ} {S : ℝ} {z : ℂ} (h : Sz ι A d z) (hd : 1 ≤ d) (hA : 1 ≤ A)
    (hS : 1 ≤ S) : SzS ι (Real.log A + Real.log d) S z := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hlA := Real.log_nonneg hA
  have hld := Real.log_nonneg hd'
  refine SzS.of_sz h hd ?_ ?_
  · calc A = Real.exp (Real.log A) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- **Sizes of the constants of the fibre factors.** -/
theorem exists_fib_consts (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {μ τ : ℕ}
    (Dt : LUDataV (d0 := d0) (d1 := d1) Ls M ι μ τ) {cX : ℝ} (hcX : 0 ≤ cX) :
    ∃ cF : ℝ, 0 ≤ cF ∧ ∀ S : ℕ, 1 ≤ S → ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
      ∀ X' : Fin m → Fin 3 → ℂ,
      (∀ k, IsRep (Ls k) ((∑ j, h j • Dt.y j).2.2.1 k + zh (Ls k)) (X' k)) →
      (∀ k a, SzS ι cX S (X' k a)) →
      (∀ i, SzS ι cF S (cstOf Ls M (∑ j, h j • Dt.y j) i)) ∧
      (∀ k, SzS ι cF S (2 * mult (lamIdx (X' k)) (X' k))⁻¹) := by
  classical
  set H := Dt.H
  set d := Dt.d
  have hH := Dt.hH
  have hd := Dt.hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlH := Real.log_nonneg hH
  have hld := Real.log_nonneg hdR
  set n := Module.finrank ℚ K
  -- accumulated defects
  choose Bd hBd0 hBd using fun k => exists_defect_sizes_S (Ls k) (Dt.hγ₂ k) (Dt.hγ₃ k)
    (fun j => (Dt.y j).2.2.1 k) (fun j => Dt.X₀ j k) (fun j => Dt.hX₀ j k)
    (fun j => ⟨H, d, hd, Dt.hX₀s j k⟩)
  set Bm := ∑ k, Bd k
  have hBm0 : 0 ≤ Bm := sum_nonneg fun k _ => hBd0 k
  have hBdm : ∀ k, Bd k ≤ Bm := fun k => single_le_sum (fun j _ => hBd0 j) (mem_univ k)
  -- the constants
  set cH : ℝ := Real.log H + Real.log d
  have hcH : 0 ≤ cH := add_nonneg hlH hld
  set c₁ : ℝ := Bm + (2 * n + 1) * Bm
  set c₂ : ℝ := Real.log 16 + 3 * Real.log H + 3 * Real.log d + 8 * cX
  have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hc₂ : 0 ≤ c₂ := by positivity
  set c₃ : ℝ := c₂ + (2 * n + 1) * c₂
  set cT : ℝ := cH + (c₁ + c₃ + 1)
  set cτ : ℝ := Real.log (μ + 1) + 1 + cH
  have hlμ : 0 ≤ Real.log ((μ : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg μ :
    (0 : ℝ) ≤ μ)])
  set cq : ℝ := (2 * n + 1) * (cX + Real.log 2 + 3 * cX)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨cτ + m * (cT + 1) + 1 + cq, by positivity, fun S hS h hh X' hX' hXs => ?_⟩
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hS2 : (1 : ℝ) ≤ (S : ℝ) ^ 2 := one_le_pow₀ hSR
  set t := ∑ j, h j • Dt.y j
  -- common denominators for the entries of `X'_k`
  have hXc : ∀ k, ∃ e : ℕ, 1 ≤ e ∧ (e : ℝ) ≤ Real.exp (3 * cX * (S : ℝ) ^ 2) ∧
      ∀ a, Sz ι (Real.exp (cX * (S : ℝ) ^ 2)) e (X' k a) := by
    intro k
    obtain ⟨e, he, hele, hes⟩ := SzS.common (hXs k)
    exact ⟨e, he, by simpa using hele, hes⟩
  choose eX heX heXle heXs using hXc
  have hEX1 : 1 ≤ Real.exp (cX * (S : ℝ) ^ 2) := Real.one_le_exp (by positivity)
  constructor
  · intro i
    rw [cstOf_eq Ls M Dt.y h i]
    -- the `τ`-part
    have hτp : SzS ι cτ S (∑ k, (h k : ℂ) * ((Dt.y k).2.2.2 i -
        M.mulVec (zetaV Ls (Dt.y k).2.2.1) i)) := by
      have h1 := sz_natComb (le_trans zero_le_one hH) (fun k => Dt.hτ k i) h hh
      refine SzS.of_sz h1 hd ?_ ?_
      · have hSe : (S : ℝ) ≤ Real.exp ((S : ℝ) ^ 2) := by
          have := Real.add_one_le_exp ((S : ℝ) ^ 2); nlinarith
        have hμe : (μ : ℝ) ≤ Real.exp (Real.log (μ + 1) * (S : ℝ) ^ 2) := by
          calc (μ : ℝ) ≤ μ + 1 := by linarith
            _ = Real.exp (Real.log (μ + 1)) := (Real.exp_log (by positivity)).symm
            _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
        have hHe : H ≤ Real.exp (cH * (S : ℝ) ^ 2) := by
          calc H = Real.exp (Real.log H) := (Real.exp_log (by linarith)).symm
            _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
        calc (S : ℝ) * μ * H ≤ Real.exp ((S : ℝ) ^ 2) *
              Real.exp (Real.log (μ + 1) * (S : ℝ) ^ 2) * Real.exp (cH * (S : ℝ) ^ 2) := by
              gcongr
          _ = Real.exp (cτ * (S : ℝ) ^ 2) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [cτ]; ring
      · calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log (by linarith)).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
    -- the block terms
    have hterm : ∀ j, SzS ι cT S (M i j * (Dsum (Ls j) (fun k => (Dt.y k).2.2.1 j) h -
        zdef (Ls j) (t.2.2.1 j + zh (Ls j)) (zh (Ls j)))) := by
      intro j
      have hMs : SzS ι cH S (M i j) := szS_of_sz (Dt.hM i j) hd hH hSR
      -- the accumulated defect
      obtain ⟨N, δ, dD, hδ, hNδ, hdD, hdDle, hSN, hSδ⟩ := hBd j S hS h hh
      have hNs : SzS ι Bm S N :=
        (SzS.of_sz hSN hdD le_rfl hdDle).mono (hBdm j) hSR
      have hδs : SzS ι Bm S δ := (SzS.of_sz hSδ hdD le_rfl hdDle).mono (hBdm j) hSR
      have hD : Dsum (Ls j) (fun k => (Dt.y k).2.2.1 j) h = N * δ⁻¹ := by
        rw [← hNδ]; field_simp
      have hDs : SzS ι c₁ S (Dsum (Ls j) (fun k => (Dt.y k).2.2.1 j) h) := by
        rw [hD]; exact hNs.mul (hδs.inv hδ hBm0)
      -- the defect at the translation
      have hE1 : ∀ a, Sz ι H d (![℘[Ls j] (zh (Ls j)), 0, 1] a) := by
        intro a; fin_cases a
        · exact Dt.he₁ j
        · exact (Sz.zero d).mono_le (zero_le_one.trans hH)
        · exact Sz.one.mono hH (one_dvd d)
      obtain ⟨nz, ez, hez, hnez, hSn, hSe⟩ := exists_defect_frac (Ls j) (Dt.hg₂' j) hH
        (hX' j) (isRep_half (Ls j)) hEX1 hH (heXs j) hE1
      have hbound : 16 * H * Real.exp (cX * (S : ℝ) ^ 2) ^ 2 * H ^ 2 ≤
          Real.exp (c₂ * (S : ℝ) ^ 2) := by
        have e1 : 16 * H * Real.exp (cX * (S : ℝ) ^ 2) ^ 2 * H ^ 2 =
            Real.exp (Real.log 16 + 3 * Real.log H + 2 * cX * (S : ℝ) ^ 2) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
            show 3 * Real.log H = Real.log (H ^ 3) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_log (by positivity), ← Real.exp_nat_mul]
          push_cast; ring_nf
        rw [e1]
        refine Real.exp_le_exp.mpr ?_
        simp only [c₂]; nlinarith
      have hdbound : ((d * eX j ^ 2 * d ^ 2 : ℕ) : ℝ) ≤ Real.exp (c₂ * (S : ℝ) ^ 2) := by
        push_cast
        have he := heXle j
        have e1 : (d : ℝ) * (d : ℝ) ^ 2 = Real.exp (3 * Real.log d) := by
          rw [show 3 * Real.log d = Real.log ((d : ℝ) ^ 3) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_log (by positivity)]; ring
        calc (d : ℝ) * (eX j : ℝ) ^ 2 * (d : ℝ) ^ 2 = (d * (d : ℝ) ^ 2) * (eX j : ℝ) ^ 2 := by ring
          _ ≤ Real.exp (3 * Real.log d) * Real.exp (3 * cX * (S : ℝ) ^ 2) ^ 2 := by
              rw [e1]; gcongr
          _ = Real.exp (3 * Real.log d + 6 * cX * (S : ℝ) ^ 2) := by
              rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
          _ ≤ Real.exp (c₂ * (S : ℝ) ^ 2) := by
              refine Real.exp_le_exp.mpr ?_; simp only [c₂]; nlinarith
      have hd1 : 1 ≤ d * eX j ^ 2 * d ^ 2 := Nat.one_le_iff_ne_zero.mpr (by
        have := heX j; positivity)
      have hns : SzS ι c₂ S nz := SzS.of_sz hSn hd1 hbound hdbound
      have hes : SzS ι c₂ S ez := SzS.of_sz hSe hd1 hbound hdbound
      have hzd : zdef (Ls j) (t.2.2.1 j + zh (Ls j)) (zh (Ls j)) = nz * ez⁻¹ := by
        rw [← hnez]; field_simp
      have hzds : SzS ι c₃ S (zdef (Ls j) (t.2.2.1 j + zh (Ls j)) (zh (Ls j))) := by
        rw [hzd]; exact hns.mul (hes.inv hez hc₂)
      have hc₁ : 0 ≤ c₁ := by positivity
      have hc₃ : 0 ≤ c₃ := by positivity
      exact hMs.mul (hDs.sub hzds hc₁ hc₃ hSR)
    have hcT : 0 ≤ cT := by positivity
    have hsum := SzS.sum univ hcT hSR fun j _ => hterm j
    rw [card_univ, Fintype.card_fin] at hsum
    refine (hτp.add hsum (by positivity) (by positivity) hSR).mono ?_ hSR
    have : 0 ≤ cq := by positivity
    linarith
  · intro k
    have hm := mult_lamIdx_ne_zero (Ls k) (hX' k)
    have h2 : SzS ι (cX + Real.log 2 + 3 * cX) S (2 * mult (lamIdx (X' k)) (X' k)) := by
      have hmult : ∀ a : Fin 2, Sz ι (Real.exp (cX * (S : ℝ) ^ 2)) (eX k) (mult a (X' k)) := by
        intro a; fin_cases a
        · exact heXs k 1
        · exact heXs k 2
      have h1 := (hmult (lamIdx (X' k))).nat_mul 2
      push_cast at h1
      refine SzS.of_sz h1 (heX k) ?_ ?_
      · calc 2 * Real.exp (cX * (S : ℝ) ^ 2) = Real.exp (Real.log 2 + cX * (S : ℝ) ^ 2) := by
              rw [Real.exp_add, Real.exp_log (by norm_num)]
          _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
      · exact (heXle k).trans (Real.exp_le_exp.mpr (by nlinarith))
    refine (h2.inv (mul_ne_zero two_ne_zero hm) (by positivity)).mono ?_ hSR
    have : 0 ≤ cτ + m * (cT + 1) + 1 := by positivity
    simp only [cq]; linarith

end LSG.AuxV
