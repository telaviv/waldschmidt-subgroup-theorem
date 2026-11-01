/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Chain
import LSG.W88.K11Lin

/-!
# Auxiliary lemmas for the assembly of `MultEstB` (A4.5, α; generic parts of `LSG.ME.MainAbAux`)

* `finrank_torusLie`, `finrank_submodule_prod`, `finrank_tanOf`.
* `HasData.addShift'`, **`deg_le_of_hfun'`**, **`lower_deg`**, `lin3` and its data (copied from `ME.MainAbAux`,
  where they are generic).
* `pow_self_mono`, `CstB`, **`final_arith_B`** (the final arithmetic with the block constants).
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata HasData)

namespace LSG.MEB

theorem finrank_torusLie {d₁ : ℕ} (U : Submodule ℚ (Fin d₁ → ℚ)) :
    finrank ℂ (LSG.W88.torusLie U) + finrank ℚ U = d₁ :=
  LSG.W88.K11.finrank_annC U

theorem finrank_submodule_prod {R M N : Type*} [Field R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N)
    [FiniteDimensional R p] [FiniteDimensional R q] :
    finrank R ↥(p.prod q) = finrank R p + finrank R q := by
  let e : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩,
        ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

theorem finrank_tanOf {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} (h0 : Submodule ℂ (Fin d₀ → ℂ))
    (U : Submodule ℚ (Fin d₁ → ℚ)) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    finrank ℂ (tanOf (B := B) h0 U t) + finrank ℚ U = finrank ℂ h0 + d₁ + finrank ℂ t := by
  rw [tanOf, finrank_submodule_prod, finrank_submodule_prod]
  have := finrank_torusLie U
  omega

theorem HasData.addShift' {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) (e : ℕ) :
    HasData (fun k => f (k + e)) a c := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    refine StrongSix.M2.hasData_congr ih.shift (Filter.Eventually.of_forall fun k => ?_)
    change f (k + 1 + e) = f (k + (e + 1))
    congr 1
    omega

section Generic

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] (β : σ → ι)
  (D : ι → ℕ)

/-- **Comparison of degrees** (generic `deg_le_of_hfun`). -/
theorem deg_le_of_hfun' {J A : Ideal (MvPolynomial σ ℂ)} (hJ : J ≠ ⊤) (hA : A ≠ ⊤)
    (hdimEq : (hdata β D ℂ A).1 = (hdata β D ℂ J).1) {κ c : ℕ} (hκ : 1 ≤ κ)
    (h : ∀ t, κ * hfun β D ℂ J t ≤ hfun β D ℂ A (t + c)) :
    (κ : ℤ) * (hdata β D ℂ J).2 ≤ (hdata β D ℂ A).2 := by
  have hf := (StrongSix.M2.hdata_spec β D ℂ hJ).smul (κ := (κ : ℤ))
    (by exact_mod_cast (by omega : κ ≠ 0))
  have hg := HasData.addShift' (StrongSix.M2.hdata_spec β D ℂ hA) c
  rcases hf.compare hg (Filter.Eventually.of_forall fun t => by exact_mod_cast h t)
      (Filter.Eventually.of_forall fun _ => by positivity) with h1 | ⟨-, h2⟩
  · omega
  · exact h2

end Generic

/-- **A polynomial lower bound through `t ↦ 2t + c`.** -/
theorem lower_deg {g : ℕ → ℤ} {a : ℕ} {c : ℤ} (hg : HasData g a c) {P : Polynomial ℤ}
    (hP : P ≠ 0) {C : ℤ} (hC : 0 < C) {c₁ : ℕ}
    (hle : ∀ t : ℕ, P.eval (t : ℤ) ≤ C * g (2 * t + c₁))
    (hnn : ∀ t : ℕ, 0 ≤ P.eval (t : ℤ)) :
    P.natDegree ≤ a ∧ (a = P.natDegree →
      P.leadingCoeff * P.natDegree.factorial ≤ C * (2 ^ a * c)) := by
  have hp := StrongSix.M2.hasData_poly hP
  have hG := StrongSix.M2.HasData.smul (HasData.comp_two (HasData.addShift' hg c₁)) hC.ne'
  rcases hp.compare hG (Filter.Eventually.of_forall fun t => by
      simpa using hle t) (Filter.Eventually.of_forall hnn) with h | ⟨h, h'⟩
  · exact ⟨h.le, fun e => by omega⟩
  · exact ⟨h.le, fun _ => h'⟩

/-- `N (a X + 1)^h (b X + 1)^r (c X + 1)^s`. -/
noncomputable def lin3 (N a b c h r s : ℕ) : Polynomial ℤ :=
  Polynomial.C (N : ℤ) * (Polynomial.C (a : ℤ) * Polynomial.X + 1) ^ h *
    (Polynomial.C (b : ℤ) * Polynomial.X + 1) ^ r * (Polynomial.C (c : ℤ) * Polynomial.X + 1) ^ s

theorem lin3_eval (N a b c h r s t : ℕ) :
    (lin3 N a b c h r s).eval (t : ℤ) =
      ((N * (a * t + 1) ^ h * (b * t + 1) ^ r * (c * t + 1) ^ s : ℕ) : ℤ) := by
  simp [lin3]

theorem lin3_data {N a b c : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h r s : ℕ) :
    lin3 N a b c h r s ≠ 0 ∧ (lin3 N a b c h r s).natDegree = h + r + s ∧
      (lin3 N a b c h r s).leadingCoeff = (N : ℤ) * a ^ h * b ^ r * c ^ s := by
  have lin : ∀ x : ℕ, 1 ≤ x → (Polynomial.C (x : ℤ) * Polynomial.X + 1).natDegree = 1 ∧
      (Polynomial.C (x : ℤ) * Polynomial.X + 1).leadingCoeff = (x : ℤ) ∧
      Polynomial.C (x : ℤ) * Polynomial.X + 1 ≠ 0 := fun x hx => by
    have hx0 : (x : ℤ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have h1 := Polynomial.natDegree_linear (b := (1 : ℤ)) hx0
    rw [map_one] at h1
    have h2 := Polynomial.leadingCoeff_linear (b := (1 : ℤ)) hx0
    rw [map_one] at h2
    refine ⟨h1, h2, fun h0 => ?_⟩
    rw [h0, Polynomial.natDegree_zero] at h1
    omega
  obtain ⟨a1, a2, a3⟩ := lin a ha
  obtain ⟨b1, b2, b3⟩ := lin b hb
  obtain ⟨c1, c2, c3⟩ := lin c hc
  have hN0 : Polynomial.C (N : ℤ) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact_mod_cast (by omega : N ≠ 0)
  have h0 : lin3 N a b c h r s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 (pow_ne_zero _ a3)) (pow_ne_zero _ b3))
      (pow_ne_zero _ c3)
  refine ⟨h0, ?_, ?_⟩
  · rw [lin3, Polynomial.natDegree_mul (mul_ne_zero (mul_ne_zero hN0 (pow_ne_zero _ a3))
      (pow_ne_zero _ b3)) (pow_ne_zero _ c3), Polynomial.natDegree_mul (mul_ne_zero hN0
      (pow_ne_zero _ a3)) (pow_ne_zero _ b3), Polynomial.natDegree_mul hN0 (pow_ne_zero _ a3),
      Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, a1, b1, c1]
    ring
  · rw [lin3, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow,
      Polynomial.leadingCoeff_pow, a2, b2, c2]

theorem pow_self_mono {a b : ℕ} (h : a ≤ b) : a ^ a ≤ b ^ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.one_le_pow _ _ hb
  · exact (Nat.pow_le_pow_left h a).trans (Nat.pow_le_pow_right (by omega) h)

/-- The constant of `MultEstB`: `n = d₀ + d₁ + Σ g_k`, `cL` the coset lower-bound constant, `cG` the
Hilbert constant `cB` of the sliced explicit ideal. -/
def CstB (n d₀ d₁ cL cG : ℕ) : ℕ :=
  n ^ n * d₀ ^ d₀ * d₁ ^ d₁ * cL * 2 ^ n * n.factorial * cG * 4 ^ n

/-- **The final arithmetic.** -/
theorem final_arith_B {n d₀ d₁ sg ℓ e t₀ t₁ t₂ T nF nR k D₀ D₁ D₂ κ cL cG : ℕ}
    {deg0 degA degIG : ℤ} (hn : n = d₀ + d₁ + sg)
    (hℓ : ℓ ≤ n) (he : e ≤ n) (hκ : κ ≤ d₀ ^ d₀ * d₁ ^ d₁)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (h0 : 0 ≤ deg0)
    (A1 : ((nR * (4 * D₀) ^ t₀ * (4 * D₁) ^ t₁ * (4 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0))
    (A2 : (((k + 1) ^ ℓ : ℕ) : ℤ) * deg0 ≤ degA) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ ((n.factorial * cG * (4 * D₀) ^ d₀ * (4 * D₁) ^ d₁ * (4 * D₂) ^ sg : ℕ) : ℤ)) :
    T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤
      CstB n d₀ d₁ cL cG * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg := by
  set X := (4 * D₀) ^ t₀ * (4 * D₁) ^ t₁ * (4 * D₂) ^ t₂
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
  have s2 : ((L * P * (nR * X * e.factorial) : ℕ) : ℤ) ≤
      (L : ℤ) * κ * cL * 2 ^ e * degIG := by
    have hA1 : ((nR * X * e.factorial : ℕ) : ℤ) ≤ ((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0) := by
      simpa [X, mul_assoc] using A1
    calc ((L * P * (nR * X * e.factorial) : ℕ) : ℤ)
        = (L : ℤ) * P * ((nR * X * e.factorial : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (L : ℤ) * P * (((κ * cL : ℕ) : ℤ) * (2 ^ e * deg0)) := by gcongr
      _ = (L : ℤ) * κ * cL * 2 ^ e * ((P : ℤ) * deg0) := by push_cast; ring
      _ ≤ (L : ℤ) * κ * cL * 2 ^ e * degA :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast A2) (by positivity)
      _ ≤ (L : ℤ) * κ * cL * 2 ^ e * degIG := by gcongr
  have s3 : (L : ℤ) * κ * cL * 2 ^ e * degIG ≤
      ((CstB n d₀ d₁ cL cG * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg : ℕ) : ℤ) := by
    have hL : L ≤ n ^ n := pow_self_mono hℓ
    have h2e : 2 ^ e ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) he
    calc (L : ℤ) * κ * cL * 2 ^ e * degIG
        ≤ (L : ℤ) * κ * cL * 2 ^ e * ((n.factorial * cG * (4 * D₀) ^ d₀ * (4 * D₁) ^ d₁ *
            (4 * D₂) ^ sg : ℕ) : ℤ) := by gcongr
      _ = (((L * κ * cL * 2 ^ e) * (n.factorial * cG * (4 * D₀) ^ d₀ * (4 * D₁) ^ d₁ *
            (4 * D₂) ^ sg) : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((CstB n d₀ d₁ cL cG * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          rw [mul_pow, mul_pow, mul_pow, CstB]
          have h4 : 4 ^ n = 4 ^ d₀ * 4 ^ d₁ * 4 ^ sg := by rw [hn, pow_add, pow_add]
          calc L * κ * cL * 2 ^ e * (n.factorial * cG * (4 ^ d₀ * D₀ ^ d₀) *
                (4 ^ d₁ * D₁ ^ d₁) * (4 ^ sg * D₂ ^ sg))
              = (L * κ * 2 ^ e) * (cL * n.factorial * cG * (4 ^ d₀ * 4 ^ d₁ * 4 ^ sg) *
                  D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg) := by ring
            _ ≤ (n ^ n * (d₀ ^ d₀ * d₁ ^ d₁) * 2 ^ n) * (cL * n.factorial * cG *
                  (4 ^ d₀ * 4 ^ d₁ * 4 ^ sg) * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ sg) := by gcongr
            _ = _ := by rw [← h4]; ring
  exact_mod_cast (show ((T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ : ℕ) : ℤ) ≤ _ from
    (Nat.cast_le.mpr s1).trans (s2.trans s3))

end LSG.MEB
