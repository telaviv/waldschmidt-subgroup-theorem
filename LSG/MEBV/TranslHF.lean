/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.StabG
import LSG.MEB.TranslHF

/-!
# Hilbert functions of translates (M2.5, β)

The `VBlock` analogue of `LSG.MEB.TranslHF`. Translations multiply the degree of block `k` by `ld_k`
(`dblB B`); every `ld_k` is at most `2^{eL B}` with `eL B = Σ_k ld_k`, so:

* **`hfun_le_transl`**: `H(I(E); t) ≤ (∏_k nLV_k) · H(I(E + g); 2^{eL B} t)`. Proof: `P ↦ (τ (−g) c P mod I(E + g))_c`
  (all law choices `c`) is injective modulo `I(E)` on `FLE(tD)` and lands in `FLE(2^{eL} t D)`.
* `HasData.comp_pow_two` (from MEB's generic `HasData.comp_two`): `t ↦ f (2^e t)` keeps the dimension.
* **`hdim_vanish_gtransl`**: `hdim I(E + g) = hdim I(E)` for `E ≠ ∅`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata HasData hdata_spec finrank_comap_subtype)

namespace LSG.MEBV

open LSG.MEB (Blk)

/-! ### Data of `t ↦ f (2^e t)` -/

/-- **Rescaling the variable by `2^e`** keeps the dimension. -/
theorem HasData.comp_pow_two {f : ℕ → ℤ} {b : ℕ} {d : ℤ} (h : HasData f b d) :
    ∀ e : ℕ, HasData (fun t => f (2 ^ e * t)) b (2 ^ (b * e) * d)
  | 0 => by simpa using h
  | e + 1 => by
    have h' := LSG.MEB.HasData.comp_two (HasData.comp_pow_two h e)
    have e1 : (fun t => f (2 ^ e * (2 * t))) = fun t => f (2 ^ (e + 1) * t) := by
      funext t; congr 1; ring
    have e2 : (2 : ℤ) ^ b * (2 ^ (b * e) * d) = 2 ^ (b * (e + 1)) * d := by ring
    rw [e1, e2] at h'
    exact h'

/-- If `0 ≤ f t ≤ C · g (2^e t)` eventually, then `dim f ≤ dim g`. -/
theorem HasData.le_of_le_comp_pow {f g : ℕ → ℤ} {a b e : ℕ} {c d C : ℤ} (hC : C ≠ 0)
    (hf : HasData f a c) (hg : HasData g b d) (hle : ∀ᶠ t in Filter.atTop, f t ≤ C * g (2 ^ e * t))
    (hnn : ∀ᶠ t in Filter.atTop, 0 ≤ f t) : a ≤ b := by
  have h := StrongSix.M2.HasData.smul (HasData.comp_pow_two hg e) hC
  rcases StrongSix.M2.HasData.compare hf h hle hnn with h' | ⟨h', -⟩ <;> omega

/-! ### The Hilbert-function comparison -/

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

variable (B) in
/-- The exponent `eL B = Σ_k ld_k`: every `ld_k ≤ 2^{eL B}`. -/
def eL : ℕ := ∑ k, (B k).ld

theorem ld_le_two_pow (k : Fin m) : (B k).ld ≤ 2 ^ eL B := by
  have h1 : (B k).ld ≤ eL B := Finset.single_le_sum (f := fun k => (B k).ld) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ k)
  exact h1.trans (Nat.lt_two_pow_self).le

theorem bmulB_le (b : Blk m) : bmulB B b ≤ 2 ^ eL B := by
  cases b with
  | e k => exact ld_le_two_pow k
  | _ => exact Nat.one_le_two_pow

theorem dblB_le (D : Blk m → ℕ) (t : ℕ) : dblB B (t • D) ≤ (2 ^ eL B * t) • D := fun b => by
  simp only [dblB, Pi.smul_apply, smul_eq_mul]
  calc bmulB B b * (t * D b) ≤ 2 ^ eL B * (t * D b) := Nat.mul_le_mul_right _ (bmulB_le b)
    _ = 2 ^ eL B * t * D b := by ring

variable (B) in
/-- The number of law choices `∏_k nLV_k`. -/
def nLaw : ℕ := ∏ k, (B k).nLV

theorem card_lawChoice : Fintype.card (∀ k, Fin (B k).nLV) = nLaw B := by
  simp [nLaw, Fintype.card_pi]

set_option maxSynthPendingDepth 10 in
/-- **Hilbert functions of translates**, with constant loss `∏ nLV_k` and `t ↦ 2^{eL B} t`. -/
theorem hfun_le_transl (D : Blk m → ℕ) (E : Set (GPt d₀ d₁ B)) (g : GPt d₀ d₁ B) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤ nLaw B * hfun blk D ℂ (vanish (gtransl g E)) (2 ^ eL B * t) := by
  classical
  set F₁ := FLE ℂ blk (t • D)
  set F₂ := FLE ℂ blk ((2 ^ eL B * t) • D)
  set E' := gtransl g E
  set N : Submodule ℂ F₂ := ((vanish E').restrictScalars ℂ).comap F₂.subtype
  have hτ : ∀ c, ∀ P ∈ F₁, τ (-g) c P ∈ F₂ := fun c P hP =>
    StrongSix.M2.FLE_mono ℂ blk (dblB_le D t) (transl_mem_FLE (-g) c hP)
  let φ : (∀ k, Fin (B k).nLV) → (F₁ →ₗ[ℂ] F₂ ⧸ N) := fun c =>
    N.mkQ ∘ₗ ((τ (-g) c).toLinearMap.restrict (hτ c))
  let Ψ : F₁ →ₗ[ℂ] ((∀ k, Fin (B k).nLV) → F₂ ⧸ N) := LinearMap.pi φ
  have hker : LinearMap.ker Ψ ≤ ((vanish E).restrictScalars ℂ).comap F₁.subtype := by
    intro x hx
    have hc : ∀ c, τ (-g) c (x : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanish E' := by
      intro c
      have := congrFun (LinearMap.mem_ker.mp hx) c
      simp only [Ψ, φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    refine mem_vanish.mpr fun e he ν => ?_
    have hh : e + g ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨c, hgood⟩ := exists_good (e + g) (-g)
    obtain ⟨μ, hμ⟩ := eval_transl_good hgood
    obtain ⟨lam, hlam⟩ := exists_pow_mul μ ν
    have := mem_vanish.mp (hc c) (e + g) hh lam
    rw [hμ, hlam, add_neg_cancel_right] at this
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 : finrank ℂ (LinearMap.range Ψ) ≤ finrank ℂ ((∀ k, Fin (B k).nLV) → F₂ ⧸ N) :=
    Submodule.finrank_le _
  have e3 : finrank ℂ ((∀ k, Fin (B k).nLV) → F₂ ⧸ N) = nLaw B * finrank ℂ (F₂ ⧸ N) := by
    have hfr := Module.finrank_pi_fintype ℂ (ι := ∀ k, Fin (B k).nLV) (M := fun _ => ↥F₂ ⧸ N)
    rw [hfr, Finset.sum_const, Finset.card_univ, card_lawChoice, smul_eq_mul]
  have e4 : finrank ℂ (F₂ ⧸ N) = hfun blk D ℂ (vanish E') (2 ^ eL B * t) := by
    have := Submodule.finrank_quotient_add_finrank N
    rw [finrank_comap_subtype, inf_comm] at this
    change finrank ℂ (F₂ ⧸ N) = finrank ℂ F₂ - finrank ℂ ↥((vanish E').restrictScalars ℂ ⊓ F₂)
    omega
  have e5 : finrank ℂ (LinearMap.ker Ψ) ≤ finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := by
    have := Submodule.finrank_mono hker
    rwa [finrank_comap_subtype, inf_comm] at this
  have e6 : hfun blk D ℂ (vanish E) t =
      finrank ℂ F₁ - finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := rfl
  rw [e6, ← e4]
  omega

theorem nLaw_pos : 0 < nLaw B := by
  refine Finset.prod_pos fun k _ => ?_
  obtain ⟨i, -⟩ := (B k).lawV_complete' 0 0
  exact Nat.pos_of_ne_zero fun h => (h ▸ i).elim0

/-- **Translates have the same Hilbert dimension.** -/
theorem hdim_vanish_gtransl (D : Blk m → ℕ) {E : Set (GPt d₀ d₁ B)} (hE : E.Nonempty)
    (g : GPt d₀ d₁ B) :
    (hdata blk D ℂ (vanish (gtransl g E))).1 = (hdata blk D ℂ (vanish E)).1 := by
  have hE' : (gtransl g E).Nonempty := hE.image _
  have hf := hdata_spec blk D ℂ (vanish_ne_top hE)
  have hg := hdata_spec blk D ℂ (vanish_ne_top hE')
  have hC : ((nLaw B : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (nLaw_pos (B := B)).ne'
  have le1 := HasData.le_of_le_comp_pow (e := eL B) hC hf hg
    (Filter.Eventually.of_forall fun t => by exact_mod_cast hfun_le_transl D E g t)
    (Filter.Eventually.of_forall fun t => by positivity)
  have le2 := HasData.le_of_le_comp_pow (e := eL B) hC hg hf
    (Filter.Eventually.of_forall fun t => by
      have := hfun_le_transl D (gtransl g E) (-g) t
      rw [gtransl_gtransl_neg] at this
      exact_mod_cast this)
    (Filter.Eventually.of_forall fun t => by positivity)
  omega

end LSG.MEBV
