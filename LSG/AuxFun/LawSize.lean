/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.NFSize
import LSG.Elliptic.AdditionLaws

/-!
# Sizes of the addition laws (Stage 3, D1)

`lawk k = ![law₁, law₂] k` (the complete system of `LSG.Elliptic.AdditionLaws`).

* `lawk_map`: the laws commute with ring homomorphisms;
* `lawk_wt`: weighted homogeneity (weights `U : 2, V : 3, W : 0, g₂ : 4, g₃ : 6`), used for
  denominators;
* `lawk_quad`: `lawk k P Q` as a quadratic form in `Q` whose coefficients are values of the law;
* `exists_lawk_bound`: `|lawk k P Q| ≤ C |P|² |Q|²` for `|g₂|, |g₃| ≤ G` (compactness + bihomogeneity);
* **`sz_lawk`**: if the coordinates of `P, Q` have sizes `(H_P, d_P)`, `(H_Q, d_Q)`, then those of
  `lawk k P Q` have size `(C H_P² H_Q², λ¹² d_P² d_Q²)`, `λ` a denominator for `(g₂, g₃)` in weights.
-/

open Finset NumberField LSG.Elliptic

noncomputable section

namespace LSG.Aux

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The two addition laws. -/
def lawk (k : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![law₁ g₂ g₃ P Q, law₂ g₂ g₃ P Q] k

/-- Weighted scaling `(U, V, W) ↦ (λ²U, λ³V, W)`. -/
def wt (l : R) (P : Fin 3 → R) : Fin 3 → R := ![l ^ 2 * P 0, l ^ 3 * P 1, P 2]

lemma lawk_map (f : R →+* S) (k : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (i : Fin 3) :
    f (lawk k g₂ g₃ P Q i) = lawk k (f g₂) (f g₃) (f ∘ P) (f ∘ Q) i := by
  fin_cases k <;> fin_cases i <;>
  · simp [lawk, law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W, map_ofNat]

lemma lawk_smul (k : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (u v : R) :
    lawk k g₂ g₃ (u • P) (v • Q) = (u * v) ^ 2 • lawk k g₂ g₃ P Q := by
  fin_cases k
  · exact law₁_smul g₂ g₃ P Q u v
  · exact law₂_smul g₂ g₃ P Q u v

lemma lawk_wt (k : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (l : R) (i : Fin 3) :
    lawk k (l ^ 4 * g₂) (l ^ 6 * g₃) (wt l P) (wt l Q) i =
      l ^ (6 + 3 * k.val) * wt l (lawk k g₂ g₃ P Q) i := by
  fin_cases k <;> fin_cases i <;>
  · simp [lawk, wt, law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W]
    ring

/-- The unit vectors and their sums. -/
def e3 (a : Fin 3) : Fin 3 → R := Pi.single a 1

lemma lawk_quad (k : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (i : Fin 3) :
    lawk k g₂ g₃ P Q i =
      ∑ a : Fin 3, lawk k g₂ g₃ P (e3 a) i * Q a ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3, (if a < b then
        (lawk k g₂ g₃ P (e3 a + e3 b) i - lawk k g₂ g₃ P (e3 a) i - lawk k g₂ g₃ P (e3 b) i) *
          Q a * Q b else 0) := by
  fin_cases k <;> fin_cases i <;>
  · simp [lawk, e3, Fin.sum_univ_three, law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W,
      Pi.single_apply]
    ring

end Algebra

/-! ### Archimedean bound -/

lemma continuous_lawk (k : Fin 2) (i : Fin 3) :
    Continuous fun x : (ℂ × ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      lawk k x.1.1 x.1.2 x.2.1 x.2.2 i := by
  fin_cases k <;> fin_cases i <;>
  · simp only [lawk, law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W]
    fun_prop

/-- `|lawk k P Q| ≤ C |P|² |Q|²` uniformly for `|g₂|, |g₃| ≤ G`. -/
theorem exists_lawk_bound (G : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 2) (i : Fin 3) (g₂ g₃ : ℂ),
    ‖g₂‖ ≤ G → ‖g₃‖ ≤ G → ∀ P Q : Fin 3 → ℂ, ‖lawk k g₂ g₃ P Q i‖ ≤ C * ‖P‖ ^ 2 * ‖Q‖ ^ 2 := by
  set s : Set ((ℂ × ℂ) × (Fin 3 → ℂ) × (Fin 3 → ℂ)) :=
    (Metric.closedBall 0 G ×ˢ Metric.closedBall 0 G) ×ˢ
      (Metric.closedBall 0 1 ×ˢ Metric.closedBall 0 1)
  have hs : IsCompact s :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hb : ∀ k i, ∃ C, ∀ x ∈ s, ‖lawk k x.1.1 x.1.2 x.2.1 x.2.2 i‖ ≤ C := fun k i =>
    hs.exists_bound_of_continuousOn (continuous_lawk k i).continuousOn
  choose C hC using hb
  refine ⟨∑ k, ∑ i, |C k i|, by positivity, fun k i g₂ g₃ h₂ h₃ P Q => ?_⟩
  have hCle : C k i ≤ ∑ k, ∑ i, |C k i| :=
    (le_abs_self _).trans ((single_le_sum (f := fun i => |C k i|) (fun _ _ => abs_nonneg _)
      (mem_univ i)).trans (single_le_sum (f := fun k => ∑ i, |C k i|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ k)))
  by_cases hP : P = 0
  · subst hP
    have := lawk_smul k g₂ g₃ (0 : Fin 3 → ℂ) Q 0 1
    simp only [zero_smul, one_smul, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    rw [this]; simp
  by_cases hQ : Q = 0
  · subst hQ
    have := lawk_smul k g₂ g₃ P (0 : Fin 3 → ℂ) 1 0
    simp only [zero_smul, one_smul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    rw [this]; simp
  have hp : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  set P' : Fin 3 → ℂ := ((‖P‖⁻¹ : ℝ) : ℂ) • P
  set Q' : Fin 3 → ℂ := ((‖Q‖⁻¹ : ℝ) : ℂ) • Q
  have hP' : ‖P'‖ ≤ 1 := by
    simp only [P', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [inv_mul_cancel₀ hp.ne']
  have hQ' : ‖Q'‖ ≤ 1 := by
    simp only [Q', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [inv_mul_cancel₀ hq.ne']
  have hPP : P = ((‖P‖ : ℝ) : ℂ) • P' := by
    simp only [P', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne', Complex.ofReal_one,
      one_smul]
  have hQQ : Q = ((‖Q‖ : ℝ) : ℂ) • Q' := by
    simp only [Q', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hq.ne', Complex.ofReal_one,
      one_smul]
  have hmem : ((g₂, g₃), P', Q') ∈ s := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simpa [s]
  have h1 := hC k i _ hmem
  simp only at h1
  have key : lawk k g₂ g₃ P Q i =
      (((‖P‖ : ℝ) : ℂ) * ((‖Q‖ : ℝ) : ℂ)) ^ 2 * lawk k g₂ g₃ P' Q' i := by
    conv_lhs => rw [hPP, hQQ]
    rw [lawk_smul]; rfl
  rw [key, norm_mul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_norm, abs_norm]
  calc (‖P‖ * ‖Q‖) ^ 2 * ‖lawk k g₂ g₃ P' Q' i‖ ≤ (‖P‖ * ‖Q‖) ^ 2 * C k i := by gcongr
    _ ≤ (‖P‖ * ‖Q‖) ^ 2 * ∑ k, ∑ i, |C k i| := by gcongr
    _ = (∑ k, ∑ i, |C k i|) * ‖P‖ ^ 2 * ‖Q‖ ^ 2 := by ring

/-! ### Sizes -/

variable {K : Type*} [Field K] [NumberField K]

lemma house_le_of {α : K} {B : ℝ} (hB : 0 ≤ B) (h : ∀ σ : K →+* ℂ, ‖σ α‖ ≤ B) : house α ≤ B := by
  rw [house_eq_sup']
  have : (univ.sup' univ_nonempty fun φ : K →+* ℂ => ‖φ α‖₊) ≤ ⟨B, hB⟩ :=
    Finset.sup'_le _ _ fun φ _ => by exact_mod_cast h φ
  exact_mod_cast this

omit [NumberField K] in
lemma isIntegral_lawk {γ₂ γ₃ : K} (h₂ : IsIntegral ℤ γ₂) (h₃ : IsIntegral ℤ γ₃) {x y : Fin 3 → K}
    (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) (k : Fin 2) (i : Fin 3) :
    IsIntegral ℤ (lawk k γ₂ γ₃ x y i) := by
  let f := (integralClosure ℤ K).val.toRingHom
  have := lawk_map f k ⟨γ₂, h₂⟩ ⟨γ₃, h₃⟩ (fun j => ⟨x j, hx j⟩) (fun j => ⟨y j, hy j⟩) i
  have hm : f (lawk k ⟨γ₂, h₂⟩ ⟨γ₃, h₃⟩ (fun j => ⟨x j, hx j⟩) (fun j => ⟨y j, hy j⟩) i) ∈
      integralClosure ℤ K := SetLike.coe_mem _
  rw [this] at hm
  exact hm

variable (ι : K →+* ℂ)

/-- **Sizes of the addition laws.** -/
theorem sz_lawk {γ₂ γ₃ : K} {G : ℝ} (hG₂ : house γ₂ ≤ G) (hG₃ : house γ₃ ≤ G) {l : ℕ}
    (hl₂ : IsIntegral ℤ ((l : K) ^ 4 * γ₂)) (hl₃ : IsIntegral ℤ ((l : K) ^ 6 * γ₃)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (C * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2) (lawk k (ι γ₂) (ι γ₃) P Q i) := by
  obtain ⟨C, hC0, hC⟩ := exists_lawk_bound G
  refine ⟨9 * C, by positivity, fun k P Q Hp Hq dp dq hP hQ i => ?_⟩
  choose x hxP hxH hxI using hP
  choose y hyQ hyH hyI using hQ
  have hPx : P = ι ∘ x := funext fun j => (hxP j).symm
  have hQy : Q = ι ∘ y := funext fun j => (hyQ j).symm
  refine ⟨lawk k γ₂ γ₃ x y i, ?_, ?_, ?_⟩
  · rw [lawk_map, hPx, hQy]
  · have hHp : 0 ≤ Hp := (house_nonneg _).trans (hxH 0)
    have hHq : 0 ≤ Hq := (house_nonneg _).trans (hyH 0)
    refine house_le_of (by positivity) fun σ => ?_
    rw [lawk_map]
    have h₂ : ‖σ γ₂‖ ≤ G := (norm_embedding_le_house γ₂ σ).trans hG₂
    have h₃ : ‖σ γ₃‖ ≤ G := (norm_embedding_le_house γ₃ σ).trans hG₃
    have hnx : ‖σ ∘ x‖ ≤ Hp := (pi_norm_le_iff_of_nonneg hHp).mpr fun j =>
      (norm_embedding_le_house _ σ).trans (hxH j)
    have hny : ‖σ ∘ y‖ ≤ Hq := (pi_norm_le_iff_of_nonneg hHq).mpr fun j =>
      (norm_embedding_le_house _ σ).trans (hyH j)
    calc ‖lawk k (σ γ₂) (σ γ₃) (σ ∘ x) (σ ∘ y) i‖ ≤ C * ‖σ ∘ x‖ ^ 2 * ‖σ ∘ y‖ ^ 2 :=
          hC k i _ _ h₂ h₃ _ _
      _ ≤ C * Hp ^ 2 * Hq ^ 2 := by gcongr
      _ ≤ 9 * C * Hp ^ 2 * Hq ^ 2 := by
          have : 0 ≤ C * Hp ^ 2 * Hq ^ 2 := by positivity
          linarith
  · -- weighted homogeneity
    set lK : K := (l : K)
    have hwx : ∀ j, IsIntegral ℤ (wt lK (fun j => (dp : K) * x j) j) := by
      intro j
      have hl : IsIntegral ℤ lK := by
        simpa [lK] using isIntegral_algebraMap (R := ℤ) (A := K) (x := (l : ℤ))
      fin_cases j
      · simpa [wt] using (hl.pow 2).mul (hxI 0)
      · simpa [wt] using (hl.pow 3).mul (hxI 1)
      · simpa [wt] using hxI 2
    have hwy : ∀ j, IsIntegral ℤ (wt lK (fun j => (dq : K) * y j) j) := by
      intro j
      have hl : IsIntegral ℤ lK := by
        simpa [lK] using isIntegral_algebraMap (R := ℤ) (A := K) (x := (l : ℤ))
      fin_cases j
      · simpa [wt] using (hl.pow 2).mul (hyI 0)
      · simpa [wt] using (hl.pow 3).mul (hyI 1)
      · simpa [wt] using hyI 2
    have hint := isIntegral_lawk hl₂ hl₃ hwx hwy k i
    rw [lawk_wt] at hint
    have hsm : (fun j => (dp : K) * x j) = (dp : K) • x := rfl
    have hsm' : (fun j => (dq : K) * y j) = (dq : K) • y := rfl
    rw [hsm, hsm', lawk_smul] at hint
    have hl : IsIntegral ℤ lK := by
      simpa [lK] using isIntegral_algebraMap (R := ℤ) (A := K) (x := (l : ℤ))
    -- `l ^ (6 + 3k) · l^{w_i} · (dp dq)² · law` is integral; pad to `l ^ 12`
    have key : ∃ a : ℕ, ((l ^ 12 * dp ^ 2 * dq ^ 2 : ℕ) : K) * lawk k γ₂ γ₃ x y i =
        lK ^ a * (lK ^ (6 + 3 * k.val) * wt lK (((dp : K) * dq) ^ 2 • lawk k γ₂ γ₃ x y) i) := by
      fin_cases k <;> fin_cases i
      · exact ⟨4, by simp [wt, lK]; ring⟩
      · exact ⟨3, by simp [wt, lK]; ring⟩
      · exact ⟨6, by simp [wt, lK]; ring⟩
      · exact ⟨1, by simp [wt, lK]; ring⟩
      · exact ⟨0, by simp [wt, lK]; ring⟩
      · exact ⟨3, by simp [wt, lK]; ring⟩
    obtain ⟨a, ha⟩ := key
    rw [ha]
    exact (hl.pow a).mul hint

end LSG.Aux
