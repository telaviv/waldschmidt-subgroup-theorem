/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.StabG
import StrongSix.M2.DimsData

/-!
# Hilbert functions of translates (A4.2, α)

Translations double the abelian block degrees (`dblB`), so (as in `LSG.ME.TranslHF`):

* **`hfun_le_transl`**: `H(I(E); t) ≤ (∏_k nL_k) · H(I(E + g); 2t)`. Proof: `P ↦ (τ (−g) c P mod I(E + g))_c`
  (all law choices `c`) is injective modulo `I(E)` on `FLE(tD)` and lands in `FLE(2tD)`.
* `HasData.comp_two` (copied from `ME.TranslHF`): if `f` has data `(b, d)`, then `t ↦ f (2t)` has data
  `(b, 2^b d)`.
* **`hdim_vanish_gtransl`**: `hdim I(E + g) = hdim I(E)` for `E ≠ ∅`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata HasData hdata_spec finrank_comap_subtype)

namespace LSG.MEB

/-! ### Data of `t ↦ f (2t)` -/

section Doubling

open StrongSix.M2 (Δ)

/-- `T f (s) = f (s + 1) + f s` (so that `Δ (f ∘ 2·) = (Δ T f) ∘ 2·`). -/
def Tdbl (f : ℕ → ℤ) : ℕ → ℤ := fun s => f (s + 1) + f s

theorem Δ_comp_two (f : ℕ → ℤ) : Δ (fun t => f (2 * t)) = fun t => Δ (Tdbl f) (2 * t) := by
  funext t
  simp only [fwdDiff, Tdbl]
  rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]
  ring

theorem Δ_Tdbl_comm : Function.Commute Δ Tdbl := fun f => by
  funext s
  simp only [fwdDiff, Tdbl]
  ring

theorem iter_Δ_comp_two (n : ℕ) : ∀ f : ℕ → ℤ,
    Δ^[n] (fun t => f (2 * t)) = fun t => ((Δ ∘ Tdbl)^[n] f) (2 * t) := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [Function.iterate_succ_apply, Δ_comp_two, ih, Function.iterate_succ_apply]
    rfl

theorem Tdbl_iter_eventually {u : ℕ → ℤ} {d : ℤ} (hu : ∀ᶠ k in Filter.atTop, u k = d) (n : ℕ) :
    ∀ᶠ k in Filter.atTop, (Tdbl^[n] u) k = 2 ^ n * d := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp ih
    refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
    rw [Function.iterate_succ_apply']
    simp only [Tdbl]
    rw [hk0 k hk, hk0 (k + 1) (by omega), pow_succ]
    ring

/-- **Doubling the variable** keeps the dimension. -/
theorem HasData.comp_two {f : ℕ → ℤ} {b : ℕ} {d : ℤ} (h : HasData f b d) :
    HasData (fun t => f (2 * t)) b (2 ^ b * d) := by
  refine ⟨mul_ne_zero (pow_ne_zero _ two_ne_zero) h.1, ?_⟩
  rw [iter_Δ_comp_two, Δ_Tdbl_comm.comp_iterate, Function.comp_apply]
  rw [show Δ^[b] (Tdbl^[b] f) = Tdbl^[b] (Δ^[b] f) from (Δ_Tdbl_comm.iterate_iterate b b) f]
  have h2 : Filter.Tendsto (fun t : ℕ => 2 * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun a => ⟨a, fun t ht => by omega⟩
  exact h2.eventually (Tdbl_iter_eventually h.2 b)

/-- If `0 ≤ f t ≤ C · g (2t)` eventually, then `dim f ≤ dim g`. -/
theorem HasData.le_of_le_comp_two {f g : ℕ → ℤ} {a b : ℕ} {c d C : ℤ} (hC : C ≠ 0)
    (hf : HasData f a c) (hg : HasData g b d) (hle : ∀ᶠ t in Filter.atTop, f t ≤ C * g (2 * t))
    (hnn : ∀ᶠ t in Filter.atTop, 0 ≤ f t) : a ≤ b := by
  have h := StrongSix.M2.HasData.smul (HasData.comp_two hg) hC
  rcases StrongSix.M2.HasData.compare hf h hle hnn with h' | ⟨h', -⟩ <;> omega

end Doubling

/-! ### The Hilbert-function comparison -/

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

theorem dblB_le (D : Blk m → ℕ) (t : ℕ) : dblB (t • D) ≤ (2 * t) • D := fun b => by
  simp only [dblB, Pi.smul_apply, smul_eq_mul]
  have : bmulB b ≤ 2 := by cases b <;> simp [bmulB]
  calc bmulB b * (t * D b) ≤ 2 * (t * D b) := Nat.mul_le_mul_right _ this
    _ = 2 * t * D b := by ring

variable (B) in
/-- The number of law choices `∏_k nL_k`. -/
def nLaw : ℕ := ∏ k, (B k).nL

theorem card_lawChoice : Fintype.card (∀ k, Fin (B k).nL) = nLaw B := by
  simp [nLaw, Fintype.card_pi]

set_option maxSynthPendingDepth 10 in
/-- **Hilbert functions of translates**, with constant loss `∏ nL_k` and `t ↦ 2t`. -/
theorem hfun_le_transl (D : Blk m → ℕ) (E : Set (GPt d₀ d₁ B)) (g : GPt d₀ d₁ B) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤ nLaw B * hfun blk D ℂ (vanish (gtransl g E)) (2 * t) := by
  classical
  set F₁ := FLE ℂ blk (t • D)
  set F₂ := FLE ℂ blk ((2 * t) • D)
  set E' := gtransl g E
  set N : Submodule ℂ F₂ := ((vanish E').restrictScalars ℂ).comap F₂.subtype
  have hτ : ∀ c, ∀ P ∈ F₁, τ (-g) c P ∈ F₂ := fun c P hP =>
    StrongSix.M2.FLE_mono ℂ blk (dblB_le D t) (transl_mem_FLE (-g) c hP)
  let φ : (∀ k, Fin (B k).nL) → (F₁ →ₗ[ℂ] F₂ ⧸ N) := fun c =>
    N.mkQ ∘ₗ ((τ (-g) c).toLinearMap.restrict (hτ c))
  let Ψ : F₁ →ₗ[ℂ] ((∀ k, Fin (B k).nL) → F₂ ⧸ N) := LinearMap.pi φ
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
    obtain ⟨lam, hlam⟩ := exists_sq_mul μ ν
    have := mem_vanish.mp (hc c) (e + g) hh lam
    rw [hμ, hlam, add_neg_cancel_right] at this
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 : finrank ℂ (LinearMap.range Ψ) ≤ finrank ℂ ((∀ k, Fin (B k).nL) → F₂ ⧸ N) :=
    Submodule.finrank_le _
  have e3 : finrank ℂ ((∀ k, Fin (B k).nL) → F₂ ⧸ N) = nLaw B * finrank ℂ (F₂ ⧸ N) := by
    have hfr := Module.finrank_pi_fintype ℂ (ι := ∀ k, Fin (B k).nL) (M := fun _ => ↥F₂ ⧸ N)
    rw [hfr, Finset.sum_const, Finset.card_univ, card_lawChoice, smul_eq_mul]
  have e4 : finrank ℂ (F₂ ⧸ N) = hfun blk D ℂ (vanish E') (2 * t) := by
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
  obtain ⟨i, -⟩ := (B k).law_complete 0 0
  exact Nat.pos_of_ne_zero fun h => (h ▸ i).elim0

/-- **Translates have the same Hilbert dimension.** -/
theorem hdim_vanish_gtransl (D : Blk m → ℕ) {E : Set (GPt d₀ d₁ B)} (hE : E.Nonempty)
    (g : GPt d₀ d₁ B) :
    (hdata blk D ℂ (vanish (gtransl g E))).1 = (hdata blk D ℂ (vanish E)).1 := by
  have hE' : (gtransl g E).Nonempty := hE.image _
  have hf := hdata_spec blk D ℂ (vanish_ne_top hE)
  have hg := hdata_spec blk D ℂ (vanish_ne_top hE')
  have hC : ((nLaw B : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (nLaw_pos (B := B)).ne'
  have le1 := HasData.le_of_le_comp_two hC hf hg
    (Filter.Eventually.of_forall fun t => by exact_mod_cast hfun_le_transl D E g t)
    (Filter.Eventually.of_forall fun t => by positivity)
  have le2 := HasData.le_of_le_comp_two hC hg hf
    (Filter.Eventually.of_forall fun t => by
      have := hfun_le_transl D (gtransl g E) (-g) t
      rw [gtransl_gtransl_neg] at this
      exact_mod_cast this)
    (Filter.Eventually.of_forall fun t => by positivity)
  omega

end LSG.MEB
