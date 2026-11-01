/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.DefectSize

/-!
# Sizes of the accumulated `ζ`-defect along `Σ hⱼ zⱼ` (balanced splitting)

`Dsum L z h = Σⱼ hⱼ ζ(zⱼ) − ζ(Σⱼ hⱼ zⱼ)`. Given cone representatives of `exp_E(zⱼ)` with
coordinates in a number field `K` (the data of `LSG.Aux.exists_alg_points`):

* **`exists_defect_sizes`**: for `hⱼ ≤ 2^k`, `δ · Dsum(h) = N` with `δ ≠ 0` and `N, δ` of house and
  common denominator `≤ e^{B 4^k}`;
* **`exists_defect_sizes_S`**: for `hⱼ ≤ S`, the bound `e^{B S²}`.

Recursion: `D(h) = D(h₁) + D(h₂) + zdef(u₁, u₂)` (`h₁ = ⌈h/2⌉`, `h₂ = ⌊h/2⌋`), the defect as a
fraction `n/e` of forms in the base representatives (`exists_defect_frac`, base representatives
from `exists_alg_points`), `δ = δ₁ δ₂ e`, `N = N₁ δ₂ e + N₂ δ₁ e + n δ₁ δ₂`. The fibre size obeys
`s(k+1) ≤ 2 s(k) + 4 A 4^k + c`, hence `s(k) ≤ B 4^k` with `B = 2A + …`.
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair
open LSG.Aux (IsRep Sz exists_den exists_alg_points exists_rep_finset)

noncomputable section

namespace LSG.AuxV

variable (L : PeriodPair)

/-- The accumulated `ζ`-defect `Σⱼ hⱼ ζ(zⱼ) − ζ(Σⱼ hⱼ zⱼ)`. -/
def Dsum {μ : ℕ} (z : Fin μ → ℂ) (h : Fin μ → ℕ) : ℂ :=
  ∑ j, (h j : ℂ) * zeta L (z j) - zeta L (∑ j, (h j : ℂ) * z j)

/-- The defect along a finite set. -/
def DsumF {μ : ℕ} (z : Fin μ → ℂ) (s : Finset (Fin μ)) : ℂ :=
  ∑ j ∈ s, zeta L (z j) - zeta L (∑ j ∈ s, z j)

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

lemma sz_max_one {H : ℝ} {d : ℕ} {x : ℂ} (h : Sz ι H d x) : Sz ι (max H 1) d x :=
  h.mono_le (le_max_left _ _)

/-- Base data: the defect along a finite set is a fraction of algebraic numbers. -/
lemma exists_defect_finset {G : ℝ} {dg : ℕ} (hgS : Sz ι G dg L.g₂) (hG : 1 ≤ G) (hdg : 1 ≤ dg)
    {γ₂ γ₃ : K}
    (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ} (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ)
    (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) (s : Finset (Fin μ)) :
    ∃ (N δ : ℂ) (H : ℝ) (d : ℕ), δ ≠ 0 ∧ δ * DsumF L z s = N ∧ 1 ≤ d ∧
      Sz ι H d N ∧ Sz ι H d δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, 1, 1, 1, one_ne_zero, by simp [DsumF, LSG.W88.Vec.zeta_zero], le_rfl,
      (Sz.zero (ι := ι) 1).mono_le zero_le_one, Sz.one⟩
  | insert a s ha ih =>
    obtain ⟨N, δ, H, d, hδ, hN, hd, hSN, hSδ⟩ := ih
    obtain ⟨X, HX, dX, hX, hdX, hXs⟩ := exists_rep_finset L h₂ h₃ z X₀ hX₀ hK s
    obtain ⟨H', d', hd', hX'⟩ := hK a
    obtain ⟨n, e, he, hne, hSn, hSe⟩ := exists_defect_frac L hgS hG hX (hX₀ a)
      (le_max_right HX 1) (le_max_right H' 1) (fun i => sz_max_one (hXs i))
      (fun i => sz_max_one (hX' i))
    set C : ℝ := 16 * G * max HX 1 ^ 2 * max H' 1 ^ 2
    set de : ℕ := dg * dX ^ 2 * d' ^ 2
    have hC0 : 0 ≤ C := hSe.nonneg
    have hH0 : 0 ≤ H := hSN.nonneg
    refine ⟨N * e + n * δ, δ * e, H * C + C * H, d * de, mul_ne_zero hδ he, ?_, ?_, ?_, ?_⟩
    · have hD : DsumF L z (insert a s) = DsumF L z s + zdef L (∑ j ∈ s, z j) (z a) := by
        unfold DsumF zdef
        rw [sum_insert ha, sum_insert ha, add_comm (z a)]
        ring
      rw [hD, ← hN, ← hne]; ring
    · have : 1 ≤ de := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact (hSN.mul hSe).add ((hSn.mul hSδ).mono le_rfl (dvd_of_eq (mul_comm _ _)))
    · exact (hSδ.mul hSe).mono_le (le_add_of_nonneg_right (by positivity))

/-- Exponential bookkeeping of one splitting step. -/
lemma step_bound {E Eb Ab B c G : ℝ} {k : ℕ} {dg : ℕ} (hE : E = Real.exp (B * 4 ^ k - c))
    (hEb : Eb = Real.exp (Ab * 4 ^ k)) (hexpc : Real.exp c = 48 * G * dg) (hG : 1 ≤ G)
    (hAB : 2 * Ab ≤ B) :
    E * E * (48 * G * dg) * (Eb ^ 2 * Eb ^ 2) ≤ Real.exp (B * 4 ^ (k + 1) - c) := by
  have hEb4 : Eb ^ 2 * Eb ^ 2 = Real.exp (4 * Ab * 4 ^ k) := by
    rw [hEb, ← pow_add, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hkey : Real.exp (B * 4 ^ (k + 1) - c) =
      E * E * Real.exp c * Real.exp (4 * Ab * 4 ^ k) * Real.exp ((2 * B - 4 * Ab) * 4 ^ k) := by
    rw [hE, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; rw [pow_succ]; ring
  have hslack : 1 ≤ Real.exp ((2 * B - 4 * Ab) * 4 ^ k) :=
    Real.one_le_exp (mul_nonneg (by linarith) (by positivity))
  rw [hkey, hexpc, hEb4]
  have h48 : 0 ≤ 48 * G * dg := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have h0 : 0 ≤ E * E * (48 * G * dg) * Real.exp (4 * Ab * 4 ^ k) :=
    mul_nonneg (mul_nonneg (mul_self_nonneg E) h48) (Real.exp_pos _).le
  exact le_mul_of_one_le_right h0 hslack

/-- **Sizes of the accumulated `ζ`-defect, `hⱼ ≤ 2^k`**: `δ · D(h) = N`, `δ ≠ 0`, house and
denominator of `N, δ` at most `e^{B 4^k}`. -/
theorem exists_defect_sizes {γ₂ γ₃ : K} (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ}
    (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ) (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∀ h : Fin μ → ℕ, (∀ j, h j ≤ 2 ^ k) →
      ∃ (N δ : ℂ) (d : ℕ), δ ≠ 0 ∧ δ * Dsum L z h = N ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (B * 4 ^ k) ∧ Sz ι (Real.exp (B * 4 ^ k)) d N ∧
        Sz ι (Real.exp (B * 4 ^ k)) d δ := by
  classical
  -- the size of `g₂`
  obtain ⟨dg, hdg1, hdgi⟩ := exists_den γ₂
  set G : ℝ := max (NumberField.house γ₂) 1
  have hG1 : 1 ≤ G := le_max_right _ _
  have hgS : Sz ι G dg L.g₂ := ⟨γ₂, h₂, le_max_left _ _, hdgi⟩
  -- base points
  obtain ⟨Ab, hAb0, hAb⟩ := exists_alg_points L h₂ h₃ z X₀ hX₀ hK
  -- base data for the `0/1` vectors
  choose Ns δs Hs ds hδs hNs hds hSN hSδ using fun s : Finset (Fin μ) =>
    exists_defect_finset L hgS hG1 hdg1 h₂ h₃ z X₀ hX₀ hK s
  set B₀ : ℝ := ∑ s : Finset (Fin μ), (|Hs s| + ds s) + 1
  have hHB : ∀ s, Hs s ≤ B₀ := fun s => by
    have := single_le_sum (f := fun s : Finset (Fin μ) => |Hs s| + (ds s : ℝ))
      (fun s _ => by positivity) (mem_univ s)
    linarith [le_abs_self (Hs s), (Nat.cast_nonneg (ds s) : (0 : ℝ) ≤ ds s)]
  have hdB : ∀ s, (ds s : ℝ) ≤ B₀ := fun s => by
    have := single_le_sum (f := fun s : Finset (Fin μ) => |Hs s| + (ds s : ℝ))
      (fun s _ => by positivity) (mem_univ s)
    linarith [abs_nonneg (Hs s)]
  have hB1 : 1 ≤ B₀ := by
    have : 0 ≤ ∑ s : Finset (Fin μ), (|Hs s| + (ds s : ℝ)) := sum_nonneg fun s _ => by positivity
    linarith
  have hdg1' : (1 : ℝ) ≤ dg := by exact_mod_cast hdg1
  set c : ℝ := Real.log (48 * G) + Real.log dg
  have hc0 : 0 ≤ c := add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hdg1')
  have hexpc : Real.exp c = 48 * G * dg := by
    simp only [c]; rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by positivity)]
  set B : ℝ := 2 * Ab + Real.log B₀ + c
  have hlogB : 0 ≤ Real.log B₀ := Real.log_nonneg hB1
  have hB0 : 0 ≤ B := by positivity
  have hAB : 2 * Ab ≤ B := by simp only [B]; linarith
  refine ⟨B, hB0, ?_⟩
  have main : ∀ k : ℕ, ∀ h : Fin μ → ℕ, (∀ j, h j ≤ 2 ^ k) →
      ∃ (N δ : ℂ) (d : ℕ), δ ≠ 0 ∧ δ * Dsum L z h = N ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (B * 4 ^ k - c) ∧ Sz ι (Real.exp (B * 4 ^ k - c)) d N ∧
        Sz ι (Real.exp (B * 4 ^ k - c)) d δ := by
    intro k
    induction k with
    | zero =>
      intro h hh
      set s : Finset (Fin μ) := univ.filter fun j => h j = 1
      have hcoef : ∀ j, (h j : ℂ) = if h j = 1 then 1 else 0 := fun j => by
        have := hh j
        simp only [pow_zero] at this
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
        · simp [h0]
        · simp [h1]
      have hD : Dsum L z h = DsumF L z s := by
        unfold Dsum DsumF
        simp only [s, sum_filter, hcoef, ite_mul, one_mul, zero_mul]
      have hexp : B₀ ≤ Real.exp (B * 4 ^ 0 - c) := by
        have : B * 4 ^ 0 - c = 2 * Ab + Real.log B₀ := by simp only [pow_zero, mul_one, B]; ring
        rw [this, Real.exp_add, Real.exp_log (by linarith)]
        exact le_mul_of_one_le_left (by linarith) (Real.one_le_exp (by positivity))
      refine ⟨Ns s, δs s, ds s, hδs s, by rw [hD]; exact hNs s, hds s, (hdB s).trans hexp,
        (hSN s).mono_le ((hHB s).trans hexp), (hSδ s).mono_le ((hHB s).trans hexp)⟩
    | succ k ih =>
      intro h hh
      set h1 : Fin μ → ℕ := fun j => (h j + 1) / 2
      set h2 : Fin μ → ℕ := fun j => h j / 2
      have hh1 : ∀ j, h1 j ≤ 2 ^ k := fun j => by
        have := hh j; rw [pow_succ] at this; simp only [h1]; omega
      have hh2 : ∀ j, h2 j ≤ 2 ^ k := fun j => by
        have := hh j; rw [pow_succ] at this; simp only [h2]; omega
      obtain ⟨N₁, δ₁, d₁, hδ₁, hN₁, hd₁, hd₁le, hSN₁, hSδ₁⟩ := ih h1 hh1
      obtain ⟨N₂, δ₂, d₂, hδ₂, hN₂, hd₂, hd₂le, hSN₂, hSδ₂⟩ := ih h2 hh2
      obtain ⟨X₁, db₁, hX₁, hdb₁, hdb₁le, hSX₁⟩ := hAb k h1 hh1
      obtain ⟨X₂, db₂, hX₂, hdb₂, hdb₂le, hSX₂⟩ := hAb k h2 hh2
      set Eb := Real.exp (Ab * 4 ^ k) with hEbdef
      have hEb1 : 1 ≤ Eb := Real.one_le_exp (by positivity)
      obtain ⟨n, e, he, hne, hSn, hSe⟩ := exists_defect_frac L hgS hG1 hX₁ hX₂ hEb1 hEb1 hSX₁ hSX₂
      set u₁ := ∑ j, (h1 j : ℂ) * z j
      set u₂ := ∑ j, (h2 j : ℂ) * z j
      have hcast : ∀ j, (h j : ℂ) = (h1 j : ℂ) + (h2 j : ℂ) := fun j => by
        simp only [h1, h2]; exact_mod_cast (by omega : h j = (h j + 1) / 2 + h j / 2)
      have hD : Dsum L z h = Dsum L z h1 + Dsum L z h2 + zdef L u₁ u₂ := by
        have hu : ∑ j, (h j : ℂ) * z j = u₁ + u₂ := by
          simp only [u₁, u₂, ← sum_add_distrib, hcast, add_mul]
        have hz : ∑ j, (h j : ℂ) * zeta L (z j) =
            ∑ j, (h1 j : ℂ) * zeta L (z j) + ∑ j, (h2 j : ℂ) * zeta L (z j) := by
          simp only [← sum_add_distrib, hcast, add_mul]
        unfold Dsum zdef
        rw [hu, hz]; ring
      set E := Real.exp (B * 4 ^ k - c) with hEdef
      have hE0 : 0 < E := Real.exp_pos _
      set Cb : ℝ := 16 * G * Eb ^ 2 * Eb ^ 2
      set de : ℕ := dg * db₁ ^ 2 * db₂ ^ 2
      set D' : ℕ := d₁ * d₂ * de
      have t1 : Sz ι (E * E * Cb) D' (N₁ * δ₂ * e) := (hSN₁.mul hSδ₂).mul hSe
      have t2 : Sz ι (E * E * Cb) D' (N₂ * δ₁ * e) :=
        ((hSN₂.mul hSδ₁).mul hSe).mono (le_of_eq (by ring)) (dvd_of_eq (by simp only [D']; ring))
      have t3 : Sz ι (E * E * Cb) D' (n * (δ₁ * δ₂)) :=
        (hSn.mul (hSδ₁.mul hSδ₂)).mono (le_of_eq (by ring)) (dvd_of_eq (by simp only [D']; ring))
      have tδ : Sz ι (E * E * Cb) D' (δ₁ * δ₂ * e) := (hSδ₁.mul hSδ₂).mul hSe
      have hstep := step_bound hEdef hEbdef hexpc hG1 hAB
      have hbound : 3 * (E * E * Cb) ≤ Real.exp (B * 4 ^ (k + 1) - c) := by
        refine le_trans ?_ hstep
        have e1 : 3 * (E * E * Cb) = E * E * (48 * G) * (Eb ^ 2 * Eb ^ 2) := by
          simp only [Cb]; ring
        have h0 : 0 ≤ E * E * (48 * G) * (Eb ^ 2 * Eb ^ 2) :=
          mul_nonneg (mul_nonneg (mul_self_nonneg E) (by linarith)) (by positivity)
        rw [e1, show E * E * (48 * G * dg) * (Eb ^ 2 * Eb ^ 2) =
          E * E * (48 * G) * (Eb ^ 2 * Eb ^ 2) * dg by ring]
        exact le_mul_of_one_le_right h0 hdg1'
      have hdbound : (D' : ℝ) ≤ Real.exp (B * 4 ^ (k + 1) - c) := by
        refine le_trans ?_ hstep
        simp only [D', de]; push_cast
        have hb : (db₁ : ℝ) ^ 2 * (db₂ : ℝ) ^ 2 ≤ Eb ^ 2 * Eb ^ 2 := by gcongr
        have hG48 : (1 : ℝ) ≤ 48 * G := by linarith
        calc (d₁ : ℝ) * d₂ * (dg * db₁ ^ 2 * db₂ ^ 2)
            = (d₁ : ℝ) * d₂ * dg * ((db₁ : ℝ) ^ 2 * (db₂ : ℝ) ^ 2) := by ring
          _ ≤ E * E * dg * (Eb ^ 2 * Eb ^ 2) := by gcongr
          _ ≤ E * E * (48 * G * dg) * (Eb ^ 2 * Eb ^ 2) := by
              have : 0 ≤ E * E * dg * (Eb ^ 2 * Eb ^ 2) := by positivity
              nlinarith
      refine ⟨N₁ * δ₂ * e + N₂ * δ₁ * e + n * (δ₁ * δ₂), δ₁ * δ₂ * e,
        D', mul_ne_zero (mul_ne_zero hδ₁ hδ₂) he, ?_, ?_, hdbound, ?_, ?_⟩
      · rw [hD, ← hN₁, ← hN₂, ← hne]; ring
      · have : 1 ≤ de := Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      · refine ((t1.add t2).add t3).mono_le ?_
        linarith [hbound]
      · refine tδ.mono_le ?_
        have : 0 ≤ E * E * Cb := by positivity
        linarith [hbound]
  intro k h hh
  obtain ⟨N, δ, d, hδ, hN, hd, hdle, hSN, hSδ⟩ := main k h hh
  have hle : Real.exp (B * 4 ^ k - c) ≤ Real.exp (B * 4 ^ k) :=
    Real.exp_le_exp.mpr (by linarith)
  exact ⟨N, δ, d, hδ, hN, hd, hdle.trans hle, hSN.mono_le hle, hSδ.mono_le hle⟩

/-- **Sizes of the accumulated `ζ`-defect, `hⱼ ≤ S`**: house and denominator `≤ e^{B S²}`. -/
theorem exists_defect_sizes_S {γ₂ γ₃ : K} (h₂ : ι γ₂ = L.g₂) (h₃ : ι γ₃ = L.g₃) {μ : ℕ}
    (z : Fin μ → ℂ) (X₀ : Fin μ → Fin 3 → ℂ) (hX₀ : ∀ j, IsRep L (z j) (X₀ j))
    (hK : ∀ j, ∃ H : ℝ, ∃ d : ℕ, 1 ≤ d ∧ ∀ i, Sz ι H d (X₀ j i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : ℕ, 1 ≤ S → ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
      ∃ (N δ : ℂ) (d : ℕ), δ ≠ 0 ∧ δ * Dsum L z h = N ∧ 1 ≤ d ∧
        (d : ℝ) ≤ Real.exp (B * S ^ 2) ∧ Sz ι (Real.exp (B * S ^ 2)) d N ∧
        Sz ι (Real.exp (B * S ^ 2)) d δ := by
  obtain ⟨B, hB0, hB⟩ := exists_defect_sizes L h₂ h₃ z X₀ hX₀ hK
  refine ⟨4 * B, by positivity, fun S hS h hh => ?_⟩
  set k := Nat.log 2 S + 1
  have hlt : S < 2 ^ k := Nat.lt_pow_succ_log_self (by norm_num) S
  have hle : 2 ^ k ≤ 2 * S := by
    have := Nat.pow_log_le_self 2 (by omega : S ≠ 0)
    simp only [k, pow_succ]; omega
  obtain ⟨N, δ, d, hδ, hN, hd, hdle, hSN, hSδ⟩ := hB k h fun j => (hh j).trans hlt.le
  have h4 : B * 4 ^ k ≤ 4 * B * S ^ 2 := by
    have : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    have h2 : ((2 : ℝ) ^ k) ≤ 2 * S := by exact_mod_cast hle
    have h0 : (0 : ℝ) ≤ 2 ^ k := by positivity
    calc B * ((2 : ℝ) ^ k) ^ 2 ≤ B * (2 * S) ^ 2 := by gcongr
      _ = 4 * B * S ^ 2 := by ring
  have hE := Real.exp_le_exp.mpr h4
  exact ⟨N, δ, d, hδ, hN, hd, hdle.trans hE, hSN.mono_le hE, hSδ.mono_le hE⟩

/-- **The fibre value of `exp_G` along `Σ hₖ yₖ`** (class `𝒞`, push-out along `M`):
`s − M ζ(z)` at `Σ hₖ yₖ` is `Σ hₖ (sₖ − M ζ(zₖ)) + M · (D_j(h))_j`, with the per-curve accumulated
defects `D_j = Dsum (Ls j)` bounded by `exists_defect_sizes_S`. -/
theorem fibreValue_sum {d0 d1 m r μ : ℕ} (Ls : Fin m → PeriodPair)
    (M : Matrix (Fin r) (Fin m) ℂ) (y : Fin μ → LSG.W88.Vec.TanV d0 d1 m r) (h : Fin μ → ℕ) :
    (∑ k, h k • y k).2.2.2 - M.mulVec (LSG.W88.Vec.zetaV Ls (∑ k, h k • y k).2.2.1) =
      ∑ k, (h k : ℂ) • ((y k).2.2.2 - M.mulVec (LSG.W88.Vec.zetaV Ls (y k).2.2.1)) +
        M.mulVec (fun j => Dsum (Ls j) (fun k => (y k).2.2.1 j) h) := by
  have hz : (∑ k, h k • y k).2.2.1 = fun j => ∑ k, (h k : ℂ) * (y k).2.2.1 j := by
    funext j
    simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Prod.smul_snd, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul]
  have hs : (∑ k, h k • y k).2.2.2 = ∑ k, (h k : ℂ) • (y k).2.2.2 := by
    simp only [Prod.snd_sum, Prod.smul_snd, ← Nat.cast_smul_eq_nsmul ℂ]
  have hD : (fun j => Dsum (Ls j) (fun k => (y k).2.2.1 j) h) =
      ∑ k, (h k : ℂ) • LSG.W88.Vec.zetaV Ls (y k).2.2.1 -
        LSG.W88.Vec.zetaV Ls (∑ k, h k • y k).2.2.1 := by
    funext j
    rw [hz]
    simp only [Dsum, LSG.W88.Vec.zetaV, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hD, hs, Matrix.mulVec_sub, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
  abel

end LSG.AuxV
