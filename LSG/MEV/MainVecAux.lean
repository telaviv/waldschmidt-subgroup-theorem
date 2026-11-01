import Mathlib
import LSG.MEV.SliceWustVCoset
import LSG.MEV.MainVecInv
import LSG.MEV.SubgroupHilbV3
import LSG.MEV.AVO
import LSG.MEV.HomPhOp
import LSG.ME.MainAbAux

/-!
# Pieces of the `G̃` assembly (STAGE5_MEV §10)

* `biUnion_gtransl_coverV`: translates of `GV` as unions of cosets of `H⁰`.
* **`Zs_subset_translV`**: the normalised zeros of Roy's ideal `A` satisfy `h + V ⊆ Z(L_r)`.
* **`hfun_cosets_ge_c`**: the sliced coset count with a multiplicative constant in the
  unsliced lower bound (needed for `hfun_H0_geV`, whose elliptic factor is `(⌊tD/2⌋+1)`).
* `lower_deg3`: a polynomial lower bound through `t ↦ 3t + c`.
* `CstV`, **`final_arith_v`**: the final arithmetic of the `G̃` estimate.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE hfun hdata HasData)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Covers -/

/-- Translates of `GV` as unions of cosets of `H ⊆ GV`. -/
theorem biUnion_gtransl_coverV [DecidableEq (GPtV d₀ d₁ Ls)] {H GV : Set (GPtV d₀ d₁ Ls)}
    (hGV : IsSubgroupG GV) (hHGV : H ⊆ GV) (Rc : Finset (GPtV d₀ d₁ Ls))
    (hRc : ∀ c ∈ Rc, c ∈ GV) (hcov : GV ⊆ ⋃ c ∈ Rc, gtransl c H) (X : Finset (GPtV d₀ d₁ Ls)) :
    (⋃ a ∈ X, gtransl a GV) = ⋃ b ∈ (X ×ˢ Rc).image (fun p => p.2 + p.1), gtransl b H := by
  classical
  ext x
  simp only [Set.mem_iUnion, mem_gtransl, Finset.mem_image, Finset.mem_product, exists_prop]
  constructor
  · rintro ⟨a, ha, hxa⟩
    have := hcov hxa
    simp only [Set.mem_iUnion, mem_gtransl, exists_prop] at this
    obtain ⟨c, hc, hxc⟩ := this
    refine ⟨c + a, ⟨(a, c), ⟨ha, hc⟩, rfl⟩, ?_⟩
    rwa [show x - (c + a) = x - a - c by abel]
  · rintro ⟨b, ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩, hx⟩
    refine ⟨a, ha, ?_⟩
    have := hGV.add_mem _ (hHGV hx) _ (hRc c hc)
    rwa [show x - (c + a) + c = x - a by abel] at this

/-! ### Normalised zeros of Roy's ideal -/

/-- **Normalised zeros of `A`**: `Zs α A ⊆ {h | h + V ⊆ Z(L_r)}`. -/
theorem Zs_subset_translV (α : Fin m → ℂ) (W : Submodule ℂ (LieV ℂ d₀ d₁ m))
    (S : Finset (GPtV d₀ d₁ Ls)) {P : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}
    (hP : IsHomV P d) (T r : ℕ) (V : Set (GPtV d₀ d₁ Ls)) :
    Zs (Ls := Ls) α (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span {Q' | ∃ Q ∈
      gensR2 Ls W S P T r, ∃ v ∈ V, ∃ c, Q' = τ Ls v c Q}) ⊆
      {h | gtransl h V ⊆ zeros (Lr2 Ls W S P T r : Set _)} := by
  intro g hg
  refine zeros_transl_subset (gensR2 Ls W S P T r) V ?_
  rw [mem_zeros_iff_le_vanish]
  refine sup_le (IG_le_vanish _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨Q, ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩, v, hv, c, rfl⟩
  have hhom := isHomV_iff_wtV.mp (isHomV_transl (isHomV_phOp σ w c₁ c₂ κ hP) v c)
  have h0 := hg.2 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨_, ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩,
    v, hv, c, rfl⟩))
  refine mem_vanish.mpr fun g' hg' lam => ?_
  rw [Set.mem_singleton_iff.mp hg']
  rw [nrm] at h0
  exact (eval_coords_eq_zero_iff hhom g _ lam).mp h0

/-! ### The sliced coset count with a constant -/

theorem hfun_P_transl_ge_c (D : Blk m → ℕ) {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (a : GPtV d₀ d₁ Ls) (α : Fin m → ℂ)
    (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a V)) (L : ℕ → ℕ) (c : ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ c * hfun blk D ℂ (vanish V) t) (t : ℕ) :
    L t ≤ c * 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
  have hpa := vanish_gtransl_isPrime hV hp a
  have h2 := hfun_le_transl D V a t
  have h3 := hfun_le_of_hom α hpa hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs)
    D (3 * t)
  set P := ∏ k : Fin m, (t * D (.e k) + 1)
  set hP := hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t)
  have hP0 : 0 < P := Finset.prod_pos fun k _ => Nat.succ_pos _
  have h4 := prod_three_le D t
  have hchain : L t * P ≤ c * 24 ^ m * hP * P := by
    calc L t * P ≤ c * hfun blk D ℂ (vanish V) t := hL t
      _ ≤ c * (8 ^ m * hfun blk D ℂ (vanish (gtransl a V)) (3 * t)) := Nat.mul_le_mul_left _ h2
      _ ≤ c * (8 ^ m * ((∏ k : Fin m, (3 * t * D (.e k) + 1)) * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ c * (8 ^ m * ((3 ^ m * P) * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4))
      _ = c * 24 ^ m * hP * P := by
          rw [show (24 : ℕ) ^ m = 8 ^ m * 3 ^ m by rw [← mul_pow]; norm_num]; ring
  exact Nat.le_of_mul_le_mul_right hchain hP0

/-- **The sliced coset count** with a constant `c` in the unsliced lower bound. -/
theorem hfun_cosets_ge_c (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → ℂ)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) (L : ℕ → ℕ) (c : ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ c * hfun blk D ℂ (vanish V) t) :
    ∃ c' : ℕ, ∀ t, R.card * L t ≤
      c * 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (3 * t + c') := by
  obtain ⟨c', hc'⟩ := hfun_sum_cosets_P D hD α hV hp R hα hdist
  refine ⟨c', fun t => ?_⟩
  calc R.card * L t = ∑ _a ∈ R, L t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ R, c * 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) :=
        Finset.sum_le_sum fun a ha => hfun_P_transl_ge_c D hV hp a α (hα a ha) L c hL t
    _ = c * 24 ^ m * ∑ a ∈ R, hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
        rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (hc' (3 * t))

/-! ### A polynomial lower bound through `t ↦ 3t + c` -/

theorem lower_deg3 {g : ℕ → ℤ} {a : ℕ} {c : ℤ} (hg : HasData g a c) {P : Polynomial ℤ}
    (hP : P ≠ 0) {C : ℤ} (hC : 0 < C) {c₁ : ℕ}
    (hle : ∀ t : ℕ, P.eval (t : ℤ) ≤ C * g (3 * t + c₁))
    (hnn : ∀ t : ℕ, 0 ≤ P.eval (t : ℤ)) :
    P.natDegree ≤ a ∧ (a = P.natDegree →
      P.leadingCoeff * P.natDegree.factorial ≤ C * (3 ^ a * c)) := by
  have hp := StrongSix.M2.hasData_poly hP
  have hG := StrongSix.M2.HasData.smul (HasData.comp_mul (c := 3) (by norm_num)
    (LSG.ME.HasData.addShift' hg c₁)) hC.ne'
  rcases hp.compare hG (Filter.Eventually.of_forall fun t => by
      simpa using hle t) (Filter.Eventually.of_forall hnn) with h | ⟨h, h'⟩
  · exact ⟨h.le, fun e => by omega⟩
  · refine ⟨h.le, fun _ => ?_⟩
    simpa using h'

/-! ### The final arithmetic -/

/-- The constant of the `G̃` estimate (`n = d₀ + d₁ + 2m`). -/
def CstV (d₀ d₁ m : ℕ) : ℕ :=
  (d₀ + d₁ + 2 * m) ^ (d₀ + d₁ + 2 * m) * d₀ ^ d₀ * d₁ ^ d₁ * 2 ^ (d₀ + d₁ + 2 * m) * 48 ^ m *
    3 ^ (d₀ + d₁ + 2 * m) * (d₀ + d₁ + 2 * m).factorial * 9 ^ d₀ * 18 ^ d₁ * 486 ^ m

theorem final_arith_v {d₀ d₁ m ℓ e t₀ t₁ t₂ T nF nR k D₀ D₁ D₂ κ : ℕ} {deg0 degA degIG : ℤ}
    (hℓ : ℓ ≤ d₀ + d₁ + 2 * m) (he : e ≤ d₀ + d₁ + 2 * m) (ht₂ : t₂ ≤ d₀ + d₁ + 2 * m)
    (hκ : κ ≤ d₀ ^ d₀ * d₁ ^ d₁)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (_h0 : 0 ≤ deg0)
    (A1 : ((nR * (9 * D₀) ^ t₀ * (9 * D₁) ^ t₁ * (9 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * 2 ^ t₂ * 48 ^ m : ℕ) : ℤ) * (3 ^ e * deg0))
    (A2 : (((k + 1) ^ ℓ : ℕ) : ℤ) * deg0 ≤ degA) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ (((d₀ + d₁ + 2 * m).factorial * (9 * D₀) ^ d₀ * (2 * (9 * D₁)) ^ d₁ *
      ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 : ℕ) : ℤ)) :
    T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤
      CstV d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) := by
  set n := d₀ + d₁ + 2 * m
  set X := (9 * D₀) ^ t₀ * (9 * D₁) ^ t₁ * (9 * D₂) ^ t₂
  set L := ℓ ^ ℓ
  set P := (k + 1) ^ ℓ
  have hDX : D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ X := by
    simp only [X]
    gcongr <;> omega
  have hfac : 1 ≤ e.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)
  have s1 : T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ L * P * (nR * X * e.factorial) := by
    calc T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ = T ^ ℓ * nF * (D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂) := by
          ring
      _ ≤ (L * P) * nR * (X * e.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul hT hF) (hDX.trans (Nat.le_mul_of_pos_right _ hfac))
      _ = L * P * (nR * X * e.factorial) := by ring
  set κ' := κ * 2 ^ t₂ * 48 ^ m
  have s2 : ((L * P * (nR * X * e.factorial) : ℕ) : ℤ) ≤ (L : ℤ) * κ' * 3 ^ e * degIG := by
    have hA1 : ((nR * X * e.factorial : ℕ) : ℤ) ≤ (κ' : ℤ) * (3 ^ e * deg0) := by
      simpa [X, κ', mul_assoc] using A1
    calc ((L * P * (nR * X * e.factorial) : ℕ) : ℤ)
        = (L : ℤ) * P * ((nR * X * e.factorial : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (L : ℤ) * P * ((κ' : ℤ) * (3 ^ e * deg0)) := by gcongr
      _ = (L : ℤ) * κ' * 3 ^ e * ((P : ℤ) * deg0) := by push_cast; ring
      _ ≤ (L : ℤ) * κ' * 3 ^ e * degA :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast A2) (by positivity)
      _ ≤ (L : ℤ) * κ' * 3 ^ e * degIG := by gcongr
  have s3 : (L : ℤ) * κ' * 3 ^ e * degIG ≤
      ((CstV d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) : ℕ) : ℤ) := by
    have hL : L ≤ n ^ n := LSG.ME.pow_self_mono hℓ
    have h3e : 3 ^ e ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) he
    have h2t : 2 ^ t₂ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) ht₂
    have hprod : ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 = 486 ^ m * D₂ ^ (2 * m) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul, ← mul_pow]
      congr 1; ring
    calc (L : ℤ) * κ' * 3 ^ e * degIG
        ≤ (L : ℤ) * κ' * 3 ^ e * (((d₀ + d₁ + 2 * m).factorial * (9 * D₀) ^ d₀ *
            (2 * (9 * D₁)) ^ d₁ * ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 : ℕ) : ℤ) := by gcongr
      _ = (((L * κ' * 3 ^ e) * ((d₀ + d₁ + 2 * m).factorial * (9 * D₀) ^ d₀ *
            (2 * (9 * D₁)) ^ d₁ * ∏ _k : Fin m, 6 * (9 * D₂) ^ 2) : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((CstV d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m) : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          have e1 : (2 * (9 * D₁)) ^ d₁ = 18 ^ d₁ * D₁ ^ d₁ := by rw [← mul_assoc, mul_pow]; norm_num
          rw [hprod, mul_pow, e1, CstV]
          calc L * (κ * 2 ^ t₂ * 48 ^ m) * 3 ^ e * ((d₀ + d₁ + 2 * m).factorial *
                (9 ^ d₀ * D₀ ^ d₀) * (18 ^ d₁ * D₁ ^ d₁) * (486 ^ m * D₂ ^ (2 * m)))
              = (L * κ * 2 ^ t₂ * 3 ^ e) * (48 ^ m * (d₀ + d₁ + 2 * m).factorial * 9 ^ d₀ *
                  18 ^ d₁ * 486 ^ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m)) := by ring
            _ ≤ (n ^ n * (d₀ ^ d₀ * d₁ ^ d₁) * 2 ^ n * 3 ^ n) * (48 ^ m *
                  (d₀ + d₁ + 2 * m).factorial * 9 ^ d₀ * 18 ^ d₁ * 486 ^ m * D₀ ^ d₀ * D₁ ^ d₁ *
                  D₂ ^ (2 * m)) := by gcongr
            _ = _ := by ring
  exact_mod_cast (show ((T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ : ℕ) : ℤ) ≤ _ from
    (Nat.cast_le.mpr s1).trans (s2.trans s3))

end

end LSG.MEV
