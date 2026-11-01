/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.AlgV
import LSG.AuxFun.AlgPoints

/-!
# Sizes of the fibre coordinates of `exp_{E^♮}(Σ hⱼ yⱼ)` (Stage 5, phase 1, item 2)

For the vector-extension class the fibre value of `exp_G` at `y ∈ Λ(G)` is `s − M ζ(z)`
(algebraic by definition of `LamV`); at `Σ hⱼ yⱼ` it is
`Σ hⱼ (sⱼ − M ζ(zⱼ)) + M · D(h)`, where, per curve,

  `D(h) = Σⱼ hⱼ ζ(zⱼ) − ζ(Σⱼ hⱼ zⱼ)`   (`Dsum`)

is the accumulated `ζ`-defect. This file bounds `D(h)` **as a fraction** `N/δ` with
`N, δ ∈ K` of house and denominator `≤ e^{B S²}` for `hⱼ ≤ S` (`exists_defect_sizes_S`) — the
route "base addition + `ζ` addition formula" of `VECEXT.md`: balanced splitting
`h = ⌈h/2⌉ + ⌊h/2⌋`, `D(h) = D(h₁) + D(h₂) + zdef(u₁, u₂)` with
`zdef(u, v) = ζ(u) + ζ(v) − ζ(u + v)`, and

* `zdef = 0` if `u`, `v` or `u + v` is a lattice point (`zdef_eq_zero`);
* `zdef = −(℘'u − ℘'v)/(2(℘u − ℘v)) = −(V₁W₂ − V₂W₁)/(2(U₁W₂ − U₂W₁))` generically
  (`zeta_add_eq`);
* `zdef = −(12℘(u)² − g₂)/(4℘'(u)) = −(12U₁² − g₂W₁²)/(4V₁W₁)` if `u − v ∈ Λ`
  (**`zeta_two_mul`**, the doubling formula, from `NLaw_dbl` and `NLaw_expN_of_add`).

In terms of cone representatives `X₁, X₂` of `exp_E(u), exp_E(v)` the numerator and denominator
are forms of bidegree `≤ (2, 2)` (`exists_defect_frac`), so the fraction sizes obey
`s_f(k+1) ≤ 2 s_f(k) + 4 s_b(k) + c` with the base sizes `s_b(k) ≍ 4^k` of
`LSG.Aux.exists_alg_points`: geometric, `s_f(k) ≍ 4^k`. (The eight `(3,3)` laws of `E^♮` would
give `6^k = S^{2.58}`: the fraction form keeps the `S²` of W83.)

A fraction suffices for Lemma U: the fibre values enter the auxiliary function polynomially (degree
`≤ D`), so one multiplies by `δ^D`.
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair
open LSG.Aux (IsRep Sz isRep_affine exists_den exists_alg_points exists_rep_finset)

noncomputable section

namespace LSG.AuxV

variable (L : PeriodPair)

/-- The `ζ`-defect `ζ(u) + ζ(v) − ζ(u + v)`. -/
def zdef (u v : ℂ) : ℂ := zeta L u + zeta L v - zeta L (u + v)

/-- **Doubling formula for `ζ`**: `ζ(2u) = 2ζ(u) + (12℘(u)² − g₂)/(4℘'(u))` for `2u ∉ Λ`. -/
theorem zeta_two_mul {u : ℂ} (h2 : u + u ∉ L.lattice) :
    zeta L (u + u) = 2 * zeta L u + (12 * ℘[L] u ^ 2 - L.g₂) / (4 * ℘'[L] u) := by
  have hu : u ∉ L.lattice := fun h => h2 (add_mem h h)
  have hy : ℘'[L] u ≠ 0 := derivWeierstrassP_ne_zero L (by rwa [two_mul])
  obtain ⟨i, j, k, -, -, -, hne⟩ := NLaw_complete (K := ℂ) two_ne_zero (discr_ne_zero L)
    (Fn_expN L u 0) (Fn_expN L u 0) (Pe_expN_ne_zero L u 0) (Pe_expN_ne_zero L u 0)
  have hA := NLaw_expN_of_add L hu hu h2 0 0 i j k
  rw [expN_of_notMem L hu, expN_of_notMem L h2] at hA
  rw [expN_of_notMem L hu] at hne
  have hB := NLaw_dbl (L.derivWeierstrassP_sq u hu) hy (0 - zeta L u) (0 - zeta L u) i j k
  set c := NLaw L.g₂ L.g₃ i j k (ptAff (℘[L] u) (℘'[L] u) (0 - zeta L u))
    (ptAff (℘[L] u) (℘'[L] u) (0 - zeta L u)) 2
  have hc : c ≠ 0 := by
    intro h0; apply hne; rw [hA, h0, zero_smul]
  have h3 := congrFun (hA.symm.trans hB) 3
  simp only [ptAff, Pi.smul_apply, smul_eq_mul, Matrix.cons_val] at h3
  have h3' := mul_left_cancel₀ hc h3
  unfold dblSlope at h3'
  have h4 : (12 * ℘[L] u ^ 2 - L.g₂) / (2 * ℘'[L] u) / 2 =
      (12 * ℘[L] u ^ 2 - L.g₂) / (4 * ℘'[L] u) := by
    field_simp; ring
  linear_combination -h3' + h4

lemma zdef_eq_zero {u v : ℂ} (h : u ∈ L.lattice ∨ v ∈ L.lattice ∨ u + v ∈ L.lattice) :
    zdef L u v = 0 := by
  unfold zdef
  rcases h with h | h | h
  · rw [add_comm u v, zeta_add L h v, zeta_of_mem' L h]; ring
  · rw [zeta_add L h u, zeta_of_mem' L h]; ring
  · have hv : v = -u + (u + v) := by ring
    have e := zeta_add L h (-u)
    rw [← hv, LSG.Weierstrass.zeta_neg] at e
    rw [e, zeta_of_mem' L h]; ring

lemma zdef_generic {u v : ℂ} (hu : u ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : u + v ∉ L.lattice) (hm : u - v ∉ L.lattice) :
    zdef L u v = -(℘'[L] u - ℘'[L] v) / (2 * (℘[L] u - ℘[L] v)) := by
  unfold zdef
  rw [zeta_add_eq L hu hv hp hm]; ring

lemma zdef_dbl {u v : ℂ} (hp : u + v ∉ L.lattice) (hm : u - v ∈ L.lattice) :
    zdef L u v = -(12 * ℘[L] u ^ 2 - L.g₂) / (4 * ℘'[L] u) := by
  have hn : -(u - v) ∈ L.lattice := L.lattice.neg_mem hm
  have h2 : u + u ∉ L.lattice := fun h => hp (by
    have := sub_mem h hm
    rwa [show u + u - (u - v) = u + v by ring] at this)
  have ev : zeta L v = zeta L u + eta L (-(u - v)) := by
    rw [← zeta_add L hn u]; congr 1; ring
  have euv : zeta L (u + v) = zeta L (u + u) + eta L (-(u - v)) := by
    rw [← zeta_add L hn (u + u)]; congr 1; ring
  unfold zdef
  rw [ev, euv, zeta_two_mul L h2]
  ring

/-- A cone representative of `exp_E(u)`, `u ∉ Λ`, is `W • (℘(u), ℘'(u), 1)` with `W ≠ 0`. -/
lemma isRep_eq_of_notMem {u : ℂ} {X : Fin 3 → ℂ} (hX : IsRep L u X) (hu : u ∉ L.lattice) :
    X 2 ≠ 0 ∧ X 0 = X 2 * ℘[L] u ∧ X 1 = X 2 * ℘'[L] u := by
  classical
  have hY := isRep_affine L hu
  have heq : toPoint L.g₂ L.g₃ X = toPoint L.g₂ L.g₃ ![℘[L] u, ℘'[L] u, 1] := by
    rw [hX.2.2, hY.2.2]
  obtain ⟨c, hc, hXc⟩ := (toPoint_eq_iff two_ne_zero (discr_ne_zero L) hX.2.1 hY.2.1 hX.1
    hY.1).mp heq
  have h2 : X 2 = c := by rw [hXc]; simp
  refine ⟨h2 ▸ hc, ?_, ?_⟩ <;> rw [hXc] <;> simp

/-! ### The defect as a fraction of forms in the representatives -/

section Sizes

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

/-- **The `ζ`-defect as a fraction** `n/e` of forms of bidegree `≤ (2, 2)` in cone
representatives `X, Y` of `exp_E(u)`, `exp_E(v)`. -/
theorem exists_defect_frac {G : ℝ} {dg : ℕ} (hg : Sz ι G dg L.g₂) (hG : 1 ≤ G)
    {u v : ℂ} {X Y : Fin 3 → ℂ} (hX : IsRep L u X) (hY : IsRep L v Y)
    {H₁ H₂ : ℝ} {d₁ d₂ : ℕ} (hH₁ : 1 ≤ H₁) (hH₂ : 1 ≤ H₂)
    (hXs : ∀ i, Sz ι H₁ d₁ (X i)) (hYs : ∀ i, Sz ι H₂ d₂ (Y i)) :
    ∃ n e : ℂ, e ≠ 0 ∧ e * zdef L u v = n ∧
      Sz ι (16 * G * H₁ ^ 2 * H₂ ^ 2) (dg * d₁ ^ 2 * d₂ ^ 2) n ∧
      Sz ι (16 * G * H₁ ^ 2 * H₂ ^ 2) (dg * d₁ ^ 2 * d₂ ^ 2) e := by
  have hH : 1 ≤ H₁ * H₂ := one_le_mul_of_one_le_of_one_le hH₁ hH₂
  have hB1 : H₁ * H₂ ≤ G * H₁ ^ 2 * H₂ ^ 2 := by
    have : H₁ * H₂ ≤ (H₁ * H₂) ^ 2 := le_self_pow₀ hH two_ne_zero
    nlinarith
  have hB2 : H₁ ^ 2 ≤ G * H₁ ^ 2 * H₂ ^ 2 := by
    have : 1 ≤ G * H₂ ^ 2 := one_le_mul_of_one_le_of_one_le hG (one_le_pow₀ hH₂)
    nlinarith [sq_nonneg H₁]
  have hBG : G * H₁ ^ 2 ≤ G * H₁ ^ 2 * H₂ ^ 2 := by
    have : 0 ≤ G * H₁ ^ 2 := by positivity
    nlinarith [one_le_pow₀ (n := 2) hH₂]
  have hd12 : d₁ * d₂ ∣ dg * d₁ ^ 2 * d₂ ^ 2 := ⟨dg * d₁ * d₂, by ring⟩
  have hd11 : d₁ * d₁ ∣ dg * d₁ ^ 2 * d₂ ^ 2 := ⟨dg * d₂ ^ 2, by ring⟩
  -- products of coordinates
  have pXY : ∀ a b, Sz ι (H₁ * H₂) (d₁ * d₂) (X a * Y b) := fun a b => (hXs a).mul (hYs b)
  have pYX : ∀ a b, Sz ι (H₁ * H₂) (d₁ * d₂) (X a * Y b) := pXY
  by_cases h0 : u ∈ L.lattice ∨ v ∈ L.lattice ∨ u + v ∈ L.lattice
  · refine ⟨0, 1, one_ne_zero, by rw [zdef_eq_zero L h0, mul_zero], ?_, ?_⟩
    · exact (Sz.zero (ι := ι) _).mono (by positivity) dvd_rfl
    · refine (Sz.one (ι := ι)).mono ?_ (one_dvd _)
      nlinarith [one_le_pow₀ (n := 2) hH₁, one_le_pow₀ (n := 2) hH₂,
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (n := 2) hH₁) (one_le_pow₀ (n := 2) hH₂)]
  push Not at h0
  obtain ⟨hu, hv, hp⟩ := h0
  obtain ⟨hX2, hX0, hX1⟩ := isRep_eq_of_notMem L hX hu
  obtain ⟨hY2, hY0, hY1⟩ := isRep_eq_of_notMem L hY hv
  by_cases hm : u - v ∈ L.lattice
  · -- doubling
    have hy : ℘'[L] u ≠ 0 := derivWeierstrassP_ne_zero L (by
      intro h; apply hp
      have := sub_mem h hm
      rwa [show 2 * u - (u - v) = u + v by ring] at this)
    refine ⟨-(12 * X 0 ^ 2 - L.g₂ * X 2 ^ 2), 4 * (X 1 * X 2), ?_, ?_, ?_, ?_⟩
    · rw [hX1]; exact mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hX2 hy) hX2)
    · rw [zdef_dbl L hp hm, hX0, hX1]; field_simp
    · have h12 : Sz ι (12 * (H₁ * H₁)) (d₁ * d₁) (12 * X 0 ^ 2) := by
        have := ((hXs 0).mul (hXs 0)).nat_mul 12
        push_cast at this; rw [sq]; exact this
      have hgX : Sz ι (G * (H₁ * H₁)) (dg * (d₁ * d₁)) (L.g₂ * X 2 ^ 2) := by
        rw [sq]; exact hg.mul ((hXs 2).mul (hXs 2))
      refine ((h12.mono le_rfl (Dvd.intro_left _ rfl)).sub hgX).neg.mono ?_ ?_
      · nlinarith
      · exact ⟨d₂ ^ 2, by ring⟩
    · have := ((hXs 1).mul (hXs 2)).nat_mul 4
      push_cast at this
      refine this.mono ?_ hd11
      nlinarith
  · -- generic
    have hne := pdiff_ne L hu hv hp hm
    refine ⟨-(X 1 * Y 2 - Y 1 * X 2), 2 * (X 0 * Y 2 - Y 0 * X 2), ?_, ?_, ?_, ?_⟩
    · rw [hX0, hY0]
      have : X 2 * ℘[L] u * Y 2 - Y 2 * ℘[L] v * X 2 = X 2 * Y 2 * (℘[L] u - ℘[L] v) := by ring
      rw [this]
      exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hX2 hY2) hne)
    · rw [zdef_generic L hu hv hp hm, hX0, hX1, hY0, hY1]; field_simp
    · have h1 : Sz ι (H₁ * H₂) (d₁ * d₂) (Y 1 * X 2) := by
        rw [mul_comm (Y 1)]; exact pXY 2 1
      refine ((pXY 1 2).sub h1).neg.mono ?_ hd12
      nlinarith
    · have h1 : Sz ι (H₁ * H₂) (d₁ * d₂) (Y 0 * X 2) := by
        rw [mul_comm (Y 0)]; exact pYX 2 0
      have := ((pXY 0 2).sub h1).nat_mul 2
      push_cast at this
      refine this.mono ?_ hd12
      nlinarith

end Sizes

end LSG.AuxV
