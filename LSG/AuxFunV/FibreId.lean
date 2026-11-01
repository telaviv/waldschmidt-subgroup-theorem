/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.MonoV
import LSG.AuxFunV.KSTools
import LSG.AuxFun.LemmaUId

/-!
# The fibre coordinate along a line, through the eight laws of `E^♮` (Stage 5, phase 2)

Lemma U at a point `t` translates `exp_E(t_k + c s)` to the base point `z₀ = ω₁/2`:
`law_κ(X', ξ(s)) = R(s) · ellV(t_k + c s)` (`lawk_eq_smul_ellV`), `X'` a representative of
`exp_E(t_k + z₀)`, `ξ(s) = (℘(z₀ + cs), ℘'(z₀ + cs), 1)`. For the fibre we use the natural law
`(κ, λ, W)` of `E^♮` at
* `P̂ = (X', 0, 0)` (the point `(t_k + z₀, ζ(t_k + z₀))`, fibre coordinate `0`; only `T_λ = 0`
  enters the law's `T₁`-entry, with `λ = W` if `X'_W ≠ 0` and `λ = V` otherwise), and
* `Q̂(s) = (℘, ℘', 1, −Z(s), −℘' Z(s) − 2℘²)(z₀ + cs)` (`Qhat`, the point `(z₀ + cs, ζ(z₀))`,
  `Z = zS` the `ζ`-increment).

**`gT_eq`**: `NLaw_{κ,λ,W}(P̂, Q̂(s))₃ = 2 λ(X') R(s) · ellN(t_k + c s, W_k)₃` with the constant
fibre parameter `W_k = ζ(t_k + z₀) + ζ(z₀) − η(ω₁)`. Uniform in all configurations (it comes from
`NLaw_expN_all`). The left side is a polynomial in algebraic constants and the series
`℘(z₀+cs), ℘'(z₀+cs), Z(s)`; the right side is `R(s)` times the `T₁`-coordinate of `exp_{E^♮}`.

**`fibF_eq_ellN`**: the fibre forms in terms of the `T₁`-coordinates for any lift `W`.
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair LSG.W88.Vec
open LSG.Aux (ellW ellV IsRep zh wpP wpQ xiV lawk isRep_affine isRep_ellV lawk_eq_smul_ellV
  sigmaMult zh_notMem)

noncomputable section

namespace LSG.AuxV

variable (L : PeriodPair)

/-- `Q̂(s)`: the point `(z₀ + c s, ζ(z₀))` of `E^♮` in affine model coordinates. -/
def Qhat (c s : ℂ) : Fin 5 → ℂ := ptAff (wpP L c s) (wpQ L c s) (-(zS L c s))

/-- `P̂ = (X', 0, 0)`. -/
def Phat (X : Fin 3 → ℂ) : Fin 5 → ℂ := ![X 0, X 1, X 2, 0, 0]

lemma Qhat_eq_expN {c s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    Qhat L c s = expN L (zh L + c * s) (zeta L (zh L)) := by
  rw [expN_of_notMem L hs, Qhat, zS]
  congr 1; ring

lemma Pe_Qhat (c s : ℂ) : Pe (Qhat L c s) = xiV L c s := by
  funext i; fin_cases i <;> rfl

lemma Pe_Phat (X : Fin 3 → ℂ) : Pe (Phat X) = X := by
  funext i; fin_cases i <;> rfl

/-- The base part of `expN` represents `exp_E`. -/
lemma isRep_Pe_expN (z w : ℂ) : IsRep L z (Pe (expN L z w)) := by
  by_cases hz : z ∈ L.lattice
  · rw [expN_of_mem L hz]
    have hO : Pe (ptO (w - zeta L z)) = (O : Fin 3 → ℂ) := by
      funext i; fin_cases i <;> rfl
    rw [hO]
    refine ⟨fun h => by simpa [O] using congrFun h 1, Fv_O _ _, ?_⟩
    rw [toPoint_O, expE_of_mem L hz]
    rfl
  · rw [expN_of_notMem L hz]
    have : Pe (ptAff (℘[L] z) (℘'[L] z) (w - zeta L z)) = ![℘[L] z, ℘'[L] z, 1] := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact isRep_affine L hz

/-- `exp_{E^♮}` is invariant under the periods `(λ, η(λ))`. -/
lemma expN_add_lattice {lam : ℂ} (hlam : lam ∈ L.lattice) (z w : ℂ) :
    expN L (z + lam) (w + eta L lam) = expN L z w := by
  have hw : w + eta L lam - zeta L (z + lam) = w - zeta L z := by
    rw [zeta_add L hlam z]; ring
  by_cases hz : z ∈ L.lattice
  · have hz' : z + lam ∈ L.lattice := L.lattice.add_mem hz hlam
    rw [expN_of_mem L hz', expN_of_mem L hz, hw]
  · have hz' : z + lam ∉ L.lattice := add_notMem_lattice L hz hlam
    rw [expN_of_notMem L hz', expN_of_notMem L hz, hw, L.weierstrassP_add_coe z ⟨lam, hlam⟩,
      L.derivWeierstrassP_add_coe z ⟨lam, hlam⟩]

/-- The `T₁`-entry of a law only sees `Pe P` and `T_λ(P)`. -/
lemma NLaw_three_congr {R : Type*} [CommRing R] (g₂ g₃ : R) (i j k : Fin 2) {P P' : Fin 5 → R}
    (Q : Fin 5 → R) (hPe : Pe P = Pe P') (hT : LSG.Elliptic.tcoord j P = LSG.Elliptic.tcoord j P') :
    NLaw g₂ g₃ i j k P Q 3 = NLaw g₂ g₃ i j k P' Q 3 := by
  simp only [NLaw, hPe, hT]

lemma Pe_NLaw {R : Type*} [CommRing R] (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 5 → R) :
    Pe (NLaw g₂ g₃ i j k P Q) =
      (2 * (mult j (Pe P) * mult k (Pe Q))) • lawSel g₂ g₃ i (Pe P) (Pe Q) := by
  funext c; fin_cases c <;> rfl

lemma lawSel_eq_lawk {R : Type*} [CommRing R] (g₂ g₃ : R) (i : Fin 2) (P Q : Fin 3 → R) :
    lawSel g₂ g₃ i P Q = lawk i g₂ g₃ P Q := rfl

lemma smul_left_cancel_of_ne {n : ℕ} {a b : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0)
    (h : a • v = b • v) : a = b := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h'; push Not at h'; exact hv (funext h')
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hi this

/-- The `λ`-choice: `W` (index `1`) if `X'_W ≠ 0`, `V` (index `0`) otherwise. -/
def lamIdx (X : Fin 3 → ℂ) : Fin 2 := if X 2 ≠ 0 then 1 else 0

lemma mult_lamIdx_ne_zero {u : ℂ} {X : Fin 3 → ℂ} (hX : IsRep L u X) :
    mult (lamIdx X) X ≠ 0 := by
  unfold lamIdx
  split_ifs with h
  · exact h
  · push Not at h
    change X 1 ≠ 0
    intro h1
    have hF := hX.2.1
    simp only [Fv, F, h, h1] at hF
    have hU : X 0 = 0 := by
      have : 4 * X 0 ^ 3 = 0 := by linear_combination -hF
      simpa using this
    exact hX.1 (by funext i; fin_cases i <;> simp [hU, h1, h])

/-- **The fibre coordinate along the line, through the natural law.** -/
theorem gT_eq {u c s : ℂ} {X : Fin 3 → ℂ} (hX : IsRep L (u + zh L) X)
    (hs : zh L + c * s ∉ L.lattice) (κ : Fin 2) {j : Fin 3} (hj : ellV L (u + c * s) j ≠ 0) :
    NLaw L.g₂ L.g₃ κ (lamIdx X) 1 (Phat X) (Qhat L c s) 3 =
      2 * mult (lamIdx X) X * (lawk κ L.g₂ L.g₃ X (xiV L c s) j / ellV L (u + c * s) j) *
        ellN L (u + c * s) (zeta L (u + zh L) + zeta L (zh L) - eta L L.ω₁) 3 := by
  classical
  set E₀ := expN L (u + zh L) (zeta L (u + zh L))
  set R := lawk κ L.g₂ L.g₃ X (xiV L c s) j / ellV L (u + c * s) j
  set Wk := zeta L (u + zh L) + zeta L (zh L) - eta L L.ω₁
  -- `X ∝ Pe E₀`
  have hE₀ := isRep_Pe_expN L (u + zh L) (zeta L (u + zh L))
  obtain ⟨c₁, hc₁, hXc⟩ := (toPoint_eq_iff two_ne_zero (discr_ne_zero L) hX.2.1 hE₀.2.1 hX.1
    hE₀.1).mp (hX.2.2.trans hE₀.2.2.symm)
  -- `T_λ` vanishes on both sides
  have hT : LSG.Elliptic.tcoord (lamIdx X) (Phat X) =
      LSG.Elliptic.tcoord (lamIdx X) (c₁ • E₀) := by
    unfold lamIdx
    by_cases hz : u + zh L ∈ L.lattice
    · have hE : E₀ = ptO 0 := by simp only [E₀]; rw [expN_of_mem L hz, sub_self]
      split_ifs <;> simp [LSG.Elliptic.tcoord, Phat, hE, ptO]
    · have hE : E₀ = ptAff (℘[L] (u + zh L)) (℘'[L] (u + zh L)) 0 := by
        simp only [E₀]; rw [expN_of_notMem L hz, sub_self]
      have hX2 : X 2 ≠ 0 := by
        rw [hXc]; change (c₁ • Pe E₀) 2 ≠ 0
        rw [hE]; simp [Pe, ptAff, hc₁]
      simp [hX2, LSG.Elliptic.tcoord, Phat, hE, ptAff]
  have hPe : Pe (Phat X) = Pe (c₁ • E₀) := by rw [Pe_Phat, Pe_smul, hXc]
  rw [NLaw_three_congr L.g₂ L.g₃ κ (lamIdx X) 1 (Qhat L c s) hPe hT]
  -- the law at the true points
  set A := NLaw L.g₂ L.g₃ κ (lamIdx X) 1 (c₁ • E₀) (Qhat L c s)
  obtain ⟨C, hC⟩ := NLaw_expN_all L (u + zh L) (zeta L (u + zh L)) (zh L + c * s)
    (zeta L (zh L)) κ (lamIdx X) 1
  have hsum : expN L (u + zh L + (zh L + c * s)) (zeta L (u + zh L) + zeta L (zh L)) =
      expN L (u + c * s) Wk := by
    have := expN_add_lattice L L.ω₁_mem_lattice (u + c * s) Wk
    rw [← this]
    congr 1
    · simp only [zh]; ring
    · simp only [Wk]; ring
  have hA : A = (c₁ ^ 3 * C) • expN L (u + c * s) Wk := by
    simp only [A]
    have := NLaw_smul (g₂ := L.g₂) (g₃ := L.g₃) (i := κ) (j := lamIdx X) (k := 1) (P := E₀)
      (Q := Qhat L c s) c₁ 1
    rw [one_smul] at this
    rw [this, Qhat_eq_expN L hs, hC, hsum, smul_smul]
    ring_nf
  obtain ⟨C₂, hC₂, hN⟩ := ellN_eq_smul_expN L (u + c * s) Wk
  -- base parts
  have hl : lawk κ L.g₂ L.g₃ X (xiV L c s) = R • ellV L (u + c * s) :=
    lawk_eq_smul_ellV L hX hs κ hj
  have hV : ellV L (u + c * s) = C₂ • Pe (expN L (u + c * s) Wk) := by
    rw [← Pe_ellN L (u + c * s) Wk, hN, Pe_smul]
  have hbase : Pe A = (2 * mult (lamIdx X) X * R * C₂) • Pe (expN L (u + c * s) Wk) := by
    simp only [A]
    rw [Pe_NLaw, Pe_Qhat, ← hPe, Pe_Phat, lawSel_eq_lawk, hl, hV]
    have hm : mult 1 (xiV L c s) = 1 := rfl
    rw [hm, smul_smul, smul_smul]
    congr 1; ring
  have hcoef : c₁ ^ 3 * C = 2 * mult (lamIdx X) X * R * C₂ := by
    rw [hA, Pe_smul] at hbase
    exact smul_left_cancel_of_ne (isRep_Pe_expN L _ _).1 hbase
  rw [hA, hcoef, hN]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The fibre forms through the `T₁`-coordinates**, for any lift `W` of the fibre. -/
theorem fibF_eq_ellN {m r : ℕ} (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (i : Fin r) (z : Fin m → ℂ) (s : Fin r → ℂ) (W : Fin m → ℂ) :
    fibF Ls M i z s = (s i - ∑ j, M i j * W j) * ∏ l, ellW (Ls l) 0 (z l) +
      ∑ j, M i j * (ellN (Ls j) (z j) (W j) 3 * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l)) := by
  unfold fibF
  have hj : ∀ j, M i j * (ellN (Ls j) (z j) (W j) 3 * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l)) =
      M i j * W j * ∏ l, ellW (Ls l) 0 (z l) -
        M i j * (zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l)) := by
    intro j
    rw [ellN_three, ← mul_prod_erase univ (fun l => ellW (Ls l) 0 (z l)) (mem_univ j)]
    ring
  rw [sum_congr rfl fun j _ => hj j, sum_sub_distrib, ← sum_mul]
  ring

end LSG.AuxV
