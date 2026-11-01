/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Lattice2

/-!
# Representatives of a lattice grid modulo a period lattice of rank `κ` (Tier 2)

Coordinates: `ℂⁿ ⊃ Λ̂ = Π_j (ℤα_j + ℤβ_j)`, indexed by `Idx n = Fin n × Fin 2`. The grid is
`{gpt v : |v_c| ≤ A}`, `gpt v = ((v_{j,0} α_j + v_{j,1} β_j)/K)_j`. The periods are
`ω_i = perVec (P i)` with integer coordinates `P i : Idx n → ℤ`, `i < κ` (any rank-`κ` subgroup of
`Λ̂`, possibly `ℂ`-dependent).

**Counting without Smith normal form.** Fix `κ` index positions `I` such that the minor
`M_{t,i} = P_i(I_t)` has `d = det M ≠ 0`. For a grid index `v` write `w_t = v(I_t) = Kd u_t + w⁰_t`,
`0 ≤ w⁰_t < |Kd|`, and subtract the period `K Σ_i y_i P_i`, `y = adj(M) u`: since
`M adj(M) = d·1`, the remainder `s` has `s(I_t) = w⁰_t`. So every grid point is `gpt s + ω` with `s`
in the set `condIdx2` of indices with `s(I_t) ∈ [0, |Kd|)` and all `|s_c| ≤ B`, which has
`|Kd|^κ (2B+1)^{2n−κ}` elements. With `B ≍ A` and `A/K ≍ r` this is the κ-saving `≍ (2A)^{2n}/r^κ`.

* `LSG.Aux.gpt`, `LSG.Aux.perVec`, `LSG.Aux.minorMat`, `LSG.Aux.condIdx2`, `LSG.Aux.card_condIdx2`.
* `LSG.Aux.lat_decomp`.
-/

open Complex Finset

namespace LSG.Aux

variable {n κ : ℕ}

/-- Real coordinates of `Λ̂`: `(j, 0) ↦ α_j`, `(j, 1) ↦ β_j`. -/
abbrev Idx (n : ℕ) := Fin n × Fin 2

/-- The grid point of index `v`. -/
noncomputable def gpt (α β : Fin n → ℂ) (K : ℕ) (v : Idx n → ℤ) : Fin n → ℂ :=
  fun j => ((v (j, 0) : ℂ) * α j + (v (j, 1) : ℂ) * β j) / K

/-- The element of `Λ̂` with integer coordinates `x`. -/
def perVec (α β : Fin n → ℂ) (x : Idx n → ℤ) : Fin n → ℂ :=
  fun j => (x (j, 0) : ℂ) * α j + (x (j, 1) : ℂ) * β j

/-- The `κ × κ` minor of the period coordinates at the positions `I`. -/
def minorMat (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) : Matrix (Fin κ) (Fin κ) ℤ :=
  Matrix.of fun t i => P i (I t)

/-- `Σ_{i,t} |adj(M)_{i,t}|`. -/
def cAdj (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) : ℤ :=
  ∑ i, ∑ t, |(minorMat P I).adjugate i t|

/-- `Σ_{i,c} |P_i(c)|`. -/
def cP (P : Fin κ → Idx n → ℤ) : ℤ := ∑ i, ∑ c, |P i c|

lemma perVec_sum (α β : Fin n → ℂ) (P : Fin κ → Idx n → ℤ) (y : Fin κ → ℤ) :
    perVec α β (∑ i, y i • P i) = ∑ i, (y i : ℂ) • perVec α β (P i) := by
  funext j
  simp only [perVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  rw [sum_mul, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

lemma gpt_add (α β : Fin n → ℂ) {K : ℕ} (hK : K ≠ 0) (s x : Idx n → ℤ) :
    gpt α β K (s + (K : ℤ) • x) = gpt α β K s + perVec α β x := by
  have hK' : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK
  funext j
  simp only [gpt, perVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- `gpt v` is the lattice node of `latNodes` in each coordinate. -/
lemma gpt_eq_lnode (α β : Fin n → ℂ) {A K : ℕ} (p : Fin n → ℕ × ℕ) :
    gpt α β K (fun c => ((if c.2 = 0 then (p c.1).1 else (p c.1).2 : ℕ) : ℤ) - A) =
      fun j => lnode (α j) (β j) A K (p j) := by
  funext j
  simp [gpt, lnode]

lemma norm_perVec_le (α β : Fin n → ℂ) {S X : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ j, ‖α j‖ + ‖β j‖ ≤ S) (x : Idx n → ℤ) (hX0 : 0 ≤ X) (hx : ∀ c, |(x c : ℝ)| ≤ X) :
    ‖perVec α β x‖ ≤ S * X := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  simp only [perVec]
  calc ‖(x (j, 0) : ℂ) * α j + (x (j, 1) : ℂ) * β j‖
      ≤ |(x (j, 0) : ℝ)| * ‖α j‖ + |(x (j, 1) : ℝ)| * ‖β j‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ X * ‖α j‖ + X * ‖β j‖ := by gcongr <;> exact hx _
    _ = X * (‖α j‖ + ‖β j‖) := by ring
    _ ≤ X * S := by gcongr; exact hS j
    _ = S * X := by ring

lemma gpt_eq_div (α β : Fin n → ℂ) (K : ℕ) (v : Idx n → ℤ) :
    gpt α β K v = (K : ℂ)⁻¹ • perVec α β v := by
  funext j; simp [gpt, perVec, div_eq_inv_mul]

lemma norm_gpt_le (α β : Fin n → ℂ) {K : ℕ} (hK : K ≠ 0) {S V : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ j, ‖α j‖ + ‖β j‖ ≤ S) (v : Idx n → ℤ) (hV0 : 0 ≤ V) (hv : ∀ c, |(v c : ℝ)| ≤ V) :
    ‖gpt α β K v‖ ≤ S * V / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  rw [gpt_eq_div, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_perVec_le α β hS0 hS v hV0 hv) hKpos.le

/-- The condition indices: `s(I_t) ∈ [0, Kd)`, all other `|s_c| ≤ B`. -/
noncomputable def condIdx2 (I : Fin κ → Idx n) (Kd B : ℕ) : Finset (Idx n → ℤ) :=
  Fintype.piFinset fun c =>
    if c ∈ univ.image I then Ico (0 : ℤ) Kd else Icc (-(B : ℤ)) B

lemma card_condIdx2 {I : Fin κ → Idx n} (hI : Function.Injective I) (Kd B : ℕ) :
    (condIdx2 I Kd B).card = Kd ^ κ * (2 * B + 1) ^ (2 * n - κ) := by
  classical
  rw [condIdx2, Fintype.card_piFinset]
  have h1 : ∀ c, (if c ∈ univ.image I then Ico (0 : ℤ) Kd else Icc (-(B : ℤ)) B).card =
      if c ∈ univ.image I then Kd else 2 * B + 1 := by
    intro c; split_ifs <;> simp [Int.card_Icc]
    omega
  rw [prod_congr rfl fun c _ => h1 c, prod_ite, prod_const, prod_const]
  have hc1 : (univ.filter fun c : Idx n => c ∈ univ.image I).card = κ := by
    rw [filter_mem_eq_inter, univ_inter, card_image_of_injective _ hI, card_univ,
      Fintype.card_fin]
  have hc2 : (univ.filter fun c : Idx n => c ∉ univ.image I).card = 2 * n - κ := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Idx n)))
      (p := fun c => c ∈ univ.image I)
    rw [hc1, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    omega
  rw [hc1, hc2]

/-- **Decomposition of lattice-grid indices modulo the periods.** -/
theorem lat_decomp (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) (hd : (minorMat P I).det ≠ 0)
    {K A : ℕ} (hK : K ≠ 0) (v : Idx n → ℤ) (hv : ∀ c, |v c| ≤ A) :
    ∃ s : Idx n → ℤ, ∃ y : Fin κ → ℤ, v = s + (K : ℤ) • ∑ i, y i • P i ∧
      (∀ t, 0 ≤ s (I t) ∧ s (I t) < ((K : ℤ) * (minorMat P I).det).natAbs) ∧
      (∀ c, |s c| ≤ A + cAdj P I * cP P * (A + K)) ∧
      (∀ c, (K : ℤ) * |(∑ i, y i • P i) c| ≤ cAdj P I * cP P * (A + K)) := by
  set M := minorMat P I
  set d := M.det
  have hKz : (0 : ℤ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hKd : (K : ℤ) * d ≠ 0 := mul_ne_zero hKz.ne' hd
  have hd1 : 1 ≤ |d| := Int.one_le_abs hd
  set w : Fin κ → ℤ := fun t => v (I t)
  set u : Fin κ → ℤ := fun t => w t / ((K : ℤ) * d)
  set y : Fin κ → ℤ := Matrix.mulVec M.adjugate u
  set x : Idx n → ℤ := ∑ i, y i • P i
  -- size of `u`, `y`, `x`
  have hu : ∀ t, (K : ℤ) * |u t| ≤ A + K := by
    intro t
    have hdiv := Int.mul_ediv_add_emod (w t) ((K : ℤ) * d)
    have hm0 := Int.emod_nonneg (w t) hKd
    have hm1 := Int.emod_lt (w t) hKd
    have hw : |w t| ≤ A := hv (I t)
    have habs : ((K : ℤ) * d).natAbs = (K : ℤ) * |d| := by
      rw [Int.natCast_natAbs, abs_mul, abs_of_pos hKz]
    rw [habs] at hm1
    have h1 : |(K : ℤ) * d * u t| ≤ |w t| + w t % ((K : ℤ) * d) := by
      rw [show (K : ℤ) * d * u t = w t - w t % ((K : ℤ) * d) by simp only [u]; linarith]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hm0]
    rw [abs_mul, abs_mul, abs_of_pos hKz] at h1
    have hu0 := abs_nonneg (u t)
    rcases eq_or_lt_of_le hu0 with h | h
    · rw [← h, mul_zero]; positivity
    · have : (K : ℤ) * (|u t| - 1) ≤ (K : ℤ) * |d| * (|u t| - 1) := by
        have : (0 : ℤ) ≤ (K : ℤ) * (|u t| - 1) := mul_nonneg hKz.le (by omega)
        nlinarith
      nlinarith
  have hy : ∀ i, (K : ℤ) * |y i| ≤ cAdj P I * (A + K) := by
    intro i
    have h1 : (K : ℤ) * |y i| ≤ ∑ t, |M.adjugate i t| * ((K : ℤ) * |u t|) := by
      simp only [y, Matrix.mulVec, dotProduct]
      calc (K : ℤ) * |∑ t, M.adjugate i t * u t| ≤ (K : ℤ) * ∑ t, |M.adjugate i t * u t| := by
            gcongr; exact abs_sum_le_sum_abs _ _
        _ = ∑ t, |M.adjugate i t| * ((K : ℤ) * |u t|) := by
            rw [mul_sum]; refine sum_congr rfl fun t _ => ?_; rw [abs_mul]; ring
    have h2 : ∑ t, |M.adjugate i t| * ((K : ℤ) * |u t|) ≤ ∑ t, |M.adjugate i t| * (A + K) :=
      sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hu t) (abs_nonneg _)
    have h3 : ∑ t, |M.adjugate i t| ≤ cAdj P I :=
      single_le_sum (f := fun i => ∑ t, |M.adjugate i t|)
        (fun i _ => sum_nonneg fun t _ => abs_nonneg _) (mem_univ i)
    have hAK : (0 : ℤ) ≤ A + K := by positivity
    calc (K : ℤ) * |y i| ≤ ∑ t, |M.adjugate i t| * (A + K) := h1.trans h2
      _ = (∑ t, |M.adjugate i t|) * (A + K) := by rw [sum_mul]
      _ ≤ cAdj P I * (A + K) := mul_le_mul_of_nonneg_right h3 hAK
  have hcAdj0 : 0 ≤ cAdj P I := sum_nonneg fun i _ => sum_nonneg fun t _ => abs_nonneg _
  have hx3 : ∀ c, (K : ℤ) * |x c| ≤ cAdj P I * cP P * (A + K) := by
    intro c
    have hAK : (0 : ℤ) ≤ A + K := by positivity
    calc (K : ℤ) * |x c| ≤ (K : ℤ) * ∑ i, |y i| * |P i c| := by
          gcongr
          simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun i _ => abs_mul _ _
      _ = ∑ i, ((K : ℤ) * |y i|) * |P i c| := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (cAdj P I * (A + K)) * |P i c| :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
      _ = cAdj P I * (A + K) * ∑ i, |P i c| := by rw [mul_sum]
      _ ≤ cAdj P I * (A + K) * cP P := by
          gcongr
          exact sum_le_sum fun i _ => single_le_sum (f := fun c => |P i c|)
            (fun c _ => abs_nonneg _) (mem_univ c)
      _ = cAdj P I * cP P * (A + K) := by ring
  refine ⟨v - (K : ℤ) • x, y, by abel, ?_, fun c => ?_, hx3⟩
  rotate_left
  · have := hx3 c
    calc |(v - (K : ℤ) • x) c| = |v c - (K : ℤ) * x c| := by simp
      _ ≤ |v c| + |(K : ℤ) * x c| := abs_sub _ _
      _ ≤ A + cAdj P I * cP P * (A + K) := by
          rw [abs_mul, abs_of_pos hKz]; exact add_le_add (hv c) this
  -- the minor coordinates of `x`
  · have hMx : ∀ t, x (I t) = d * u t := by
      intro t
      have h1 : x (I t) = (Matrix.mulVec M y) t := by
        simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, M,
          minorMat, Matrix.of_apply]
        exact sum_congr rfl fun i _ => mul_comm _ _
      rw [h1]
      simp only [y, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      rfl
    intro t
    have hst : (v - (K : ℤ) • x) (I t) = w t % ((K : ℤ) * d) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hMx t, u]
      have := Int.mul_ediv_add_emod (w t) ((K : ℤ) * d)
      simp only [w] at this ⊢
      linarith
    rw [hst]
    exact ⟨Int.emod_nonneg _ hKd, Int.emod_lt _ hKd⟩

end LSG.Aux
