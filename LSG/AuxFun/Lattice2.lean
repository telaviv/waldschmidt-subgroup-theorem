/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Progression

/-!
# Lagrange constants for a grid of a lattice `ℤα + ℤβ ⊂ ℂ` (Tier 2)

Nodes `ζ_p = ((p₁ − A) α + (p₂ − A) β)/K`, `p ∈ [0, 2A]²`, for `α, β` linearly independent over
`ℝ` (`D = Im(ᾱβ) ≠ 0`); `M = (2A+1)²` nodes. This is the one-variable node set of a coordinate
whose period group is a lattice (`STAGE3_D2.md`, O2, Tier 2).

**Node products without shell counting.** With `c₀ = |D|/(|α| + |β|)`,
`|ζ_p − ζ_{p'}| ≥ (c₀/K) max(|u|, |v|)` (`u, v` the index differences), and for integers
`(u, v) ≠ 0`, `max(|u|,|v|)² ≥ max(|u|,1)·max(|v|,1)`. The right side is a product of two
one-variable factors, so `∏_{p' ≠ p} |ζ_p − ζ_{p'}| ≥ (c₀/K)^{M−1} ((2A)!/4^A)^{2A+1}` follows from
the factorial products of `LSG.Aux.prod_abs_sub_erase`. Consequently
`|ℓ_p(w)| ≤ (max(X, 1) e²)^M` for `|w| ≤ ρ`, `X = (ρK + (|α|+|β|)A)/(c₀A)`.

* `LSG.Aux.lnode`, `LSG.Aux.latBox`, `LSG.Aux.latNodes`, `LSG.Aux.card_latNodes`.
* `LSG.Aux.norm_lagBasis_lat_le`.
-/

open Complex Finset
open scoped Nat

namespace LSG.Aux

/-- The node of index `p ∈ [0, 2A]²`. -/
noncomputable def lnode (α β : ℂ) (A K : ℕ) (p : ℕ × ℕ) : ℂ :=
  (((p.1 : ℂ) - A) * α + ((p.2 : ℂ) - A) * β) / K

/-- The index box `[0, 2A]²`. -/
def latBox (A : ℕ) : Finset (ℕ × ℕ) := range (2 * A + 1) ×ˢ range (2 * A + 1)

/-- The lattice grid. -/
noncomputable def latNodes (α β : ℂ) (A K : ℕ) : Finset ℂ := (latBox A).image (lnode α β A K)

/-- `Im(ᾱ (xα + yβ)) = y D`, `Im(β̄ (xα + yβ)) = −x D`. -/
lemma im_coords (α β : ℂ) (x y : ℝ) :
    ((starRingEnd ℂ) α * ((x : ℂ) * α + (y : ℂ) * β)).im = y * ((starRingEnd ℂ) α * β).im ∧
    ((starRingEnd ℂ) β * ((x : ℂ) * α + (y : ℂ) * β)).im = -(x * ((starRingEnd ℂ) α * β).im) := by
  simp only [mul_im, mul_re, add_re, add_im, conj_re, conj_im, ofReal_re, ofReal_im]
  constructor <;> ring

lemma coord_bound {α β : ℂ} (x y : ℝ) :
    |x| * |((starRingEnd ℂ) α * β).im| ≤ ‖β‖ * ‖(x : ℂ) * α + (y : ℂ) * β‖ ∧
    |y| * |((starRingEnd ℂ) α * β).im| ≤ ‖α‖ * ‖(x : ℂ) * α + (y : ℂ) * β‖ := by
  obtain ⟨h1, h2⟩ := im_coords α β x y
  constructor
  · have := abs_im_le_norm ((starRingEnd ℂ) β * ((x : ℂ) * α + (y : ℂ) * β))
    rw [h2, abs_neg, abs_mul, norm_mul, Complex.norm_conj] at this
    exact this
  · have := abs_im_le_norm ((starRingEnd ℂ) α * ((x : ℂ) * α + (y : ℂ) * β))
    rw [h1, abs_mul, norm_mul, Complex.norm_conj] at this
    exact this

/-- The lower bound `|uα + vβ| ≥ c₀ max(|u|, |v|)`, `c₀ = |D| / (|α| + |β|)`. -/
lemma lower_bound {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) (x y : ℝ) :
    |((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) * max |x| |y| ≤ ‖(x : ℂ) * α + (y : ℂ) * β‖ := by
  obtain ⟨h1, h2⟩ := coord_bound (α := α) (β := β) x y
  have hs : 0 < ‖α‖ + ‖β‖ := by
    rcases eq_or_ne α 0 with rfl | hα
    · simp at hD
    · have := norm_pos_iff.mpr hα; positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  have hw := norm_nonneg ((x : ℂ) * α + (y : ℂ) * β)
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h]
    nlinarith [norm_nonneg β]
  · rw [max_eq_left h]
    nlinarith [norm_nonneg α]

lemma lnode_sub (α β : ℂ) (A K : ℕ) (p p' : ℕ × ℕ) :
    lnode α β A K p - lnode α β A K p' =
      ((((p.1 : ℝ) - p'.1 : ℝ) : ℂ) * α + (((p.2 : ℝ) - p'.2 : ℝ) : ℂ) * β) / K := by
  unfold lnode; push_cast; ring

lemma lnode_injective {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) {A K : ℕ} (hK : K ≠ 0) :
    Function.Injective (lnode α β A K) := by
  intro p p' h
  have h0 : lnode α β A K p - lnode α β A K p' = 0 := sub_eq_zero.mpr h
  rw [lnode_sub, div_eq_zero_iff, or_iff_left (Nat.cast_ne_zero.mpr hK)] at h0
  obtain ⟨h1, h2⟩ := coord_bound (α := α) (β := β) ((p.1 : ℝ) - p'.1) ((p.2 : ℝ) - p'.2)
  rw [h0, norm_zero, mul_zero] at h1 h2
  have hD' : 0 < |((starRingEnd ℂ) α * β).im| := abs_pos.mpr hD
  have e1 : |(p.1 : ℝ) - p'.1| = 0 := le_antisymm (by nlinarith [abs_nonneg ((p.1 : ℝ) - p'.1)])
    (abs_nonneg _)
  have e2 : |(p.2 : ℝ) - p'.2| = 0 := le_antisymm (by nlinarith [abs_nonneg ((p.2 : ℝ) - p'.2)])
    (abs_nonneg _)
  rw [abs_eq_zero, sub_eq_zero, Nat.cast_inj] at e1 e2
  exact Prod.ext e1 e2

lemma card_latNodes {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) {A K : ℕ} (hK : K ≠ 0) :
    (latNodes α β A K).card = (2 * A + 1) ^ 2 := by
  rw [latNodes, card_image_of_injective _ (lnode_injective hD hK), latBox, card_product,
    card_range, sq]

lemma norm_lnode_le (α β : ℂ) {A K : ℕ} {p : ℕ × ℕ} (hp : p ∈ latBox A) :
    ‖lnode α β A K p‖ ≤ (‖α‖ + ‖β‖) * A / K := by
  simp only [latBox, mem_product, mem_range] at hp
  have h1 : ‖((p.1 : ℂ) - A)‖ ≤ A := by
    rw [show ((p.1 : ℂ) - A) = (((p.1 : ℝ) - A : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    have : (p.1 : ℝ) ≤ 2 * A := by exact_mod_cast (by omega : p.1 ≤ 2 * A)
    constructor <;> linarith [(Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1)]
  have h2 : ‖((p.2 : ℂ) - A)‖ ≤ A := by
    rw [show ((p.2 : ℂ) - A) = (((p.2 : ℝ) - A : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    have : (p.2 : ℝ) ≤ 2 * A := by exact_mod_cast (by omega : p.2 ≤ 2 * A)
    constructor <;> linarith [(Nat.cast_nonneg p.2 : (0 : ℝ) ≤ p.2)]
  unfold lnode
  rw [norm_div, Complex.norm_natCast]
  gcongr
  calc ‖((p.1 : ℂ) - A) * α + ((p.2 : ℂ) - A) * β‖
      ≤ ‖((p.1 : ℂ) - A)‖ * ‖α‖ + ‖((p.2 : ℂ) - A)‖ * ‖β‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ A * ‖α‖ + A * ‖β‖ := by gcongr
    _ = (‖α‖ + ‖β‖) * A := by ring

/-- For integers `(u, v) ≠ 0`: `max(|u|,|v|)² ≥ max(|u|,1) max(|v|,1)`. -/
lemma max_sq_ge {u v : ℤ} (h : u ≠ 0 ∨ v ≠ 0) :
    max |(u : ℝ)| 1 * max |(v : ℝ)| 1 ≤ (max |(u : ℝ)| |(v : ℝ)|) ^ 2 := by
  have hu1 : u ≠ 0 → 1 ≤ |(u : ℝ)| := fun hu => by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hu
  have hv1 : v ≠ 0 → 1 ≤ |(v : ℝ)| := fun hv => by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hv
  have hmu : |(u : ℝ)| ≤ max |(u : ℝ)| |(v : ℝ)| := le_max_left _ _
  have hmv : |(v : ℝ)| ≤ max |(u : ℝ)| |(v : ℝ)| := le_max_right _ _
  by_cases hu : u = 0
  · have hv := h.resolve_left (not_not.mpr hu)
    subst hu
    simp only [Int.cast_zero, abs_zero]
    rw [max_eq_right zero_le_one, max_eq_left (hv1 hv), max_eq_right (abs_nonneg _), one_mul, sq]
    nlinarith [hv1 hv]
  by_cases hv : v = 0
  · subst hv
    simp only [Int.cast_zero, abs_zero]
    rw [max_eq_right zero_le_one, max_eq_left (hu1 hu), max_eq_left (abs_nonneg _), mul_one, sq]
    nlinarith [hu1 hu]
  rw [max_eq_left (hu1 hu), max_eq_left (hv1 hv), sq]
  exact mul_le_mul hmu hmv (abs_nonneg _) ((abs_nonneg _).trans hmu)

/-- One-variable factor: `∏_{i < N} max(|k − i|, 1) = k! (N − 1 − k)!`. -/
lemma prod_max_abs {N k : ℕ} (hk : k < N) :
    ∏ i ∈ range N, max |(k : ℝ) - i| 1 = (k ! : ℝ) * ((N - 1 - k) ! : ℝ) := by
  rw [← mul_prod_erase _ _ (mem_range.mpr hk), sub_self, abs_zero, max_eq_right zero_le_one,
    one_mul, ← prod_abs_sub_erase hk]
  refine prod_congr rfl fun i hi => max_eq_left ?_
  have hik : i ≠ k := ne_of_mem_erase hi
  have : (1 : ℤ) ≤ |(k : ℤ) - i| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hik.symm))
  have : (1 : ℝ) ≤ |((k : ℤ) - i : ℤ)| := by exact_mod_cast this
  simpa using this

/-- **Node products of the lattice grid.** -/
lemma prod_lat_lower {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) {A K : ℕ} (hK : K ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ latBox A) :
    (|((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) / K) ^ ((2 * A + 1) ^ 2 - 1) *
        (((2 * A)! : ℝ) / 2 ^ (2 * A)) ^ (2 * A + 1) ≤
      ∏ p' ∈ (latBox A).erase p, ‖lnode α β A K p - lnode α β A K p'‖ := by
  set c : ℝ := |((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) / K with hc
  have hc0 : 0 ≤ c := by positivity
  set F : ℝ := ((2 * A)! : ℝ) / 2 ^ (2 * A)
  have hF0 : 0 ≤ F := by positivity
  set N := 2 * A + 1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  simp only [latBox, mem_product, mem_range] at hp
  let Q : ℕ × ℕ → ℝ := fun p' => max |(p.1 : ℝ) - p'.1| 1 * max |(p.2 : ℝ) - p'.2| 1
  -- each factor squared
  have hfac : ∀ p' ∈ (latBox A).erase p,
      c ^ 2 * Q p' ≤ ‖lnode α β A K p - lnode α β A K p'‖ ^ 2 := by
    intro p' hp'
    have hne : p' ≠ p := ne_of_mem_erase hp'
    have hlb := lower_bound hD ((p.1 : ℝ) - p'.1) ((p.2 : ℝ) - p'.2)
    rw [lnode_sub, norm_div, Complex.norm_natCast]
    have huv : ((p.1 : ℤ) - p'.1) ≠ 0 ∨ ((p.2 : ℤ) - p'.2) ≠ 0 := by
      by_contra hh
      rw [not_or, not_not, not_not] at hh
      exact hne (Prod.ext (by omega) (by omega))
    have hms := max_sq_ge huv
    push_cast at hms
    have hQ : Q p' ≤ (max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2|) ^ 2 := hms
    have hm0 : 0 ≤ max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2| :=
      le_max_of_le_left (abs_nonneg _)
    set X := ‖(((p.1 : ℝ) - p'.1 : ℝ) : ℂ) * α + (((p.2 : ℝ) - p'.2 : ℝ) : ℂ) * β‖
    have hX : c * K * max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2| ≤ X := by
      rw [hc, div_mul_cancel₀ _ hKpos.ne']; exact hlb
    have hX' : c * max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2| ≤ X / K := by
      rw [le_div_iff₀ hKpos]; linarith
    calc c ^ 2 * Q p' ≤ c ^ 2 * (max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2|) ^ 2 := by gcongr
      _ = (c * max |(p.1 : ℝ) - p'.1| |(p.2 : ℝ) - p'.2|) ^ 2 := by ring
      _ ≤ (X / K) ^ 2 := by gcongr
  -- the product of the `Q`
  have hQp : Q p = 1 := by simp [Q]
  have hQprod : (F ^ N) ^ 2 ≤ ∏ p' ∈ latBox A, Q p' := by
    rw [latBox, prod_product]
    simp only [Q]
    rw [prod_congr rfl fun a _ => prod_mul_distrib, prod_mul_distrib]
    simp only [prod_const, card_range]
    rw [prod_pow, prod_max_abs hp.2, prod_max_abs hp.1]
    have h1 := factorial_div_two_pow_le (m := 2 * A) (k := p.1) (by omega)
    have h2 := factorial_div_two_pow_le (m := 2 * A) (k := p.2) (by omega)
    rw [show 2 * A + 1 - 1 - p.1 = 2 * A - p.1 by omega,
      show 2 * A + 1 - 1 - p.2 = 2 * A - p.2 by omega]
    rw [sq]
    exact mul_le_mul (pow_le_pow_left₀ hF0 h1 N) (pow_le_pow_left₀ hF0 h2 N) (by positivity)
      (by positivity)
  have hcard : ((latBox A).erase p).card = N ^ 2 - 1 := by
    rw [card_erase_of_mem (by simp [latBox]; omega), latBox, card_product, card_range, sq]
  -- squares
  have hsq : (c ^ (N ^ 2 - 1) * F ^ N) ^ 2 ≤
      (∏ p' ∈ (latBox A).erase p, ‖lnode α β A K p - lnode α β A K p'‖) ^ 2 := by
    rw [← prod_pow]
    calc (c ^ (N ^ 2 - 1) * F ^ N) ^ 2 = (c ^ 2) ^ (N ^ 2 - 1) * (F ^ N) ^ 2 := by ring
      _ ≤ (c ^ 2) ^ (N ^ 2 - 1) * ∏ p' ∈ latBox A, Q p' := by gcongr
      _ = (c ^ 2) ^ (N ^ 2 - 1) * ∏ p' ∈ (latBox A).erase p, Q p' := by
          rw [prod_erase _ hQp]
      _ = ∏ p' ∈ (latBox A).erase p, c ^ 2 * Q p' := by
          rw [prod_mul_distrib (f := fun _ => c ^ 2) (g := Q), prod_const, hcard]
      _ ≤ ∏ p' ∈ (latBox A).erase p, ‖lnode α β A K p - lnode α β A K p'‖ ^ 2 :=
          prod_le_prod₀ (fun p' _ => by
            have : 0 ≤ Q p' := mul_nonneg (le_max_of_le_right zero_le_one)
              (le_max_of_le_right zero_le_one)
            positivity) hfac
  exact (pow_le_pow_iff_left₀ (by positivity) (prod_nonneg fun _ _ => norm_nonneg _)
    two_ne_zero).mp hsq

/-- The numerical core: `(XA)^{M−1} / ((2A)!/4^A)^{2A+1} ≤ (max(X,1) e²)^M`, `M = (2A+1)²`. -/
lemma lat_const_le {A : ℕ} (hA : 1 ≤ A) {X : ℝ} (hX : 0 ≤ X) :
    (X * A) ^ ((2 * A + 1) ^ 2 - 1) / ((((2 * A)! : ℝ) / 2 ^ (2 * A)) ^ (2 * A + 1)) ≤
      (max X 1 * Real.exp 2) ^ ((2 * A + 1) ^ 2) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have he0 : 0 < Real.exp (2 * A) := Real.exp_pos _
  -- `(2A)!/4^A ≥ A^{2A}/e^{2A}`
  have hfact : (A : ℝ) ^ (2 * A) / Real.exp (2 * A) ≤ ((2 * A)! : ℝ) / 2 ^ (2 * A) := by
    have h := Real.pow_div_factorial_le_exp ((2 * A : ℕ) : ℝ) (Nat.cast_nonneg _) (2 * A)
    have hf : (0 : ℝ) < ((2 * A)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_iff₀ hf] at h
    rw [div_le_div_iff₀ he0 (by positivity)]
    push_cast at h
    calc (A : ℝ) ^ (2 * A) * 2 ^ (2 * A) = (2 * A) ^ (2 * A) := by rw [mul_pow, mul_comm]
      _ ≤ Real.exp (2 * A) * ((2 * A)! : ℝ) := by linarith
      _ = ((2 * A)! : ℝ) * Real.exp (2 * A) := by ring
  set F : ℝ := ((2 * A)! : ℝ) / 2 ^ (2 * A)
  set G : ℝ := (A : ℝ) ^ (2 * A)
  have hG0 : 0 < G := by positivity
  have hexp : (2 * A + 1) ^ 2 - 1 = 2 * A + 2 * A * (2 * A + 1) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]; ring
  have hFN : (G / Real.exp (2 * A)) ^ (2 * A + 1) ≤ F ^ (2 * A + 1) :=
    pow_le_pow_left₀ (by positivity) hfact _
  have hm1 : 1 ≤ max X 1 := le_max_right _ _
  -- `A^{2A} ≤ e^{2A²}`
  have hGe : G ≤ Real.exp (2 * A * A) := by
    have h1 : (A : ℝ) ≤ Real.exp A := by linarith [Real.add_one_le_exp (A : ℝ)]
    calc G = (A : ℝ) ^ (2 * A) := rfl
      _ ≤ Real.exp A ^ (2 * A) := by gcongr
      _ = Real.exp (2 * A * A) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hexp, div_le_iff₀ (lt_of_lt_of_le (by positivity) hFN)]
  calc (X * A) ^ (2 * A + 2 * A * (2 * A + 1))
      = X ^ (2 * A + 2 * A * (2 * A + 1)) * (G * G ^ (2 * A + 1)) := by
        rw [mul_pow, pow_add, pow_mul]; ring
    _ ≤ max X 1 ^ ((2 * A + 1) ^ 2) * (G * G ^ (2 * A + 1)) := by
        gcongr
        calc X ^ (2 * A + 2 * A * (2 * A + 1)) ≤ max X 1 ^ (2 * A + 2 * A * (2 * A + 1)) := by
              gcongr; exact le_max_left _ _
          _ ≤ max X 1 ^ ((2 * A + 1) ^ 2) := pow_le_pow_right₀ hm1 (by nlinarith)
    _ = max X 1 ^ ((2 * A + 1) ^ 2) * G * Real.exp (2 * A) ^ (2 * A + 1) *
          (G / Real.exp (2 * A)) ^ (2 * A + 1) := by
        rw [div_pow]; field_simp
    _ ≤ max X 1 ^ ((2 * A + 1) ^ 2) * Real.exp (2 * A * A) * Real.exp (2 * A) ^ (2 * A + 1) *
          F ^ (2 * A + 1) := by gcongr
    _ = max X 1 ^ ((2 * A + 1) ^ 2) *
          (Real.exp (2 * A * A) * Real.exp (2 * A) ^ (2 * A + 1)) * F ^ (2 * A + 1) := by ring
    _ ≤ max X 1 ^ ((2 * A + 1) ^ 2) * Real.exp 2 ^ ((2 * A + 1) ^ 2) * F ^ (2 * A + 1) := by
        have hE : Real.exp (2 * A * A) * Real.exp (2 * A) ^ (2 * A + 1) ≤
            Real.exp 2 ^ ((2 * A + 1) ^ 2) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          push_cast; nlinarith
        gcongr
    _ = (max X 1 * Real.exp 2) ^ ((2 * A + 1) ^ 2) * F ^ (2 * A + 1) := by rw [mul_pow]

/-- **Lagrange basis bound for the lattice grid.** -/
theorem norm_lagBasis_lat_le {α β : ℂ} (hD : ((starRingEnd ℂ) α * β).im ≠ 0) {A K : ℕ}
    (hK : K ≠ 0) (hA : 1 ≤ A) {p : ℕ × ℕ} (hp : p ∈ latBox A) {ρ : ℝ} (hρ : 0 ≤ ρ) {w : ℂ}
    (hw : ‖w‖ ≤ ρ) :
    ‖lagBasis (latNodes α β A K) (lnode α β A K p) w‖ ≤
      (max ((ρ * K + (‖α‖ + ‖β‖) * A) / (|((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) * A)) 1 *
        Real.exp 2) ^ ((2 * A + 1) ^ 2) := by
  set c₀ : ℝ := |((starRingEnd ℂ) α * β).im| / (‖α‖ + ‖β‖) with hc₀
  have hs : 0 < ‖α‖ + ‖β‖ := by
    rcases eq_or_ne α 0 with rfl | hα
    · simp at hD
    · have := norm_pos_iff.mpr hα; positivity
  have hc0 : 0 < c₀ := div_pos (abs_pos.mpr hD) hs
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hinj := lnode_injective (A := A) hD hK
  unfold lagBasis latNodes
  rw [← image_erase hinj, prod_image (fun i _ j _ h => hinj h), norm_prod]
  simp only [norm_div]
  rw [prod_div_distrib]
  have hcard : ((latBox A).erase p).card = (2 * A + 1) ^ 2 - 1 := by
    rw [card_erase_of_mem hp, latBox, card_product, card_range, sq]
  have hnum : ∏ p' ∈ (latBox A).erase p, ‖w - lnode α β A K p'‖ ≤
      (ρ + (‖α‖ + ‖β‖) * A / K) ^ ((2 * A + 1) ^ 2 - 1) := by
    rw [← hcard, ← prod_const]
    refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p' hp' => ?_
    exact (norm_sub_le _ _).trans (add_le_add hw (norm_lnode_le α β (mem_of_mem_erase hp')))
  have hden := prod_lat_lower hD hK hp
  rw [← hc₀] at hden
  have hFpos : (0 : ℝ) < ((2 * A)! : ℝ) / 2 ^ (2 * A) := by
    have : (0 : ℝ) < ((2 * A)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  have hdpos :
      0 < (c₀ / K) ^ ((2 * A + 1) ^ 2 - 1) * (((2 * A)! : ℝ) / 2 ^ (2 * A)) ^ (2 * A + 1) := by
    positivity
  set X : ℝ := (ρ * K + (‖α‖ + ‖β‖) * A) / (c₀ * A)
  have hX0 : 0 ≤ X := by positivity
  calc (∏ p' ∈ (latBox A).erase p, ‖w - lnode α β A K p'‖) /
        ∏ p' ∈ (latBox A).erase p, ‖lnode α β A K p - lnode α β A K p'‖
      ≤ (ρ + (‖α‖ + ‖β‖) * A / K) ^ ((2 * A + 1) ^ 2 - 1) /
          ((c₀ / K) ^ ((2 * A + 1) ^ 2 - 1) * (((2 * A)! : ℝ) / 2 ^ (2 * A)) ^ (2 * A + 1)) :=
        div_le_div₀ (by positivity) hnum hdpos hden
    _ = (X * A) ^ ((2 * A + 1) ^ 2 - 1) / ((((2 * A)! : ℝ) / 2 ^ (2 * A)) ^ (2 * A + 1)) := by
        rw [← div_div, ← div_pow]
        congr 2
        simp only [X]
        field_simp
    _ ≤ (max X 1 * Real.exp 2) ^ ((2 * A + 1) ^ 2) := lat_const_le hA hX0

end LSG.Aux
