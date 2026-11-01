import Mathlib
import LSG.MEV.PhOp

/-!
# Roy's chain with Philippon's operators on `G̃` (chain v2 for `E^♮` blocks; first part)

* `LowZero n f`: `f` has no terms of degree `≤ n`.
* **`OrdGt W Q n p`** (formal order `> n` along `W` at `p`): for all `w ∈ W` and all law choices
  `c'`, `Q(p + exp(z w))` has no terms of degree `≤ n`, the formal point `p + exp(z w)` being
  `phPt p w c' = law_{c'}(rep p, ExpV w)`. (The abelian code uses the flow through `p` instead;
  here the formal point is built from the identity by the laws.) `ordIdeal W n E` is an ideal
  containing `I_G̃` (`IG_le_ordIdeal`), antitone in `n`.
* `sig S r`, `gensR2 r = {phOp σ w c c' κ P : σ ∈ Σ[r], w ∈ W, κ ≤ r T}`, `Lr2 r = I_G̃ ⊔ (gensR2 r)`;
  monotone (`Lr2_mono`).
* **Degrees**: `gensR2_mem_FLE` (`FLE (tplE D)`: `E^♮` degrees `≤ 3D`, the others `≤ D`), and the
  generators of Roy's `A` (translates) lie in `FLE (tplE (tplE D)) ≤ FLE (9 • D)`
  (`transl_gensR2_mem_FLE`, `tplE_tplE_le`), independent of `T` and `r`.

The rest of the chain (`zeros_phOp`, `ordGt_transl`, `Lr2_le_vanish_zero`, `exists_flat2`,
`ordGt_phOp`, `hAVO2`, the bridge to derivation words) is in `LSG.MEV.ChainV`, `LSG.MEV.Flat`,
`LSG.MEV.AVO`, on top of the `E^♮` curve lemma (`LSG.MEV.Curve`, `LSG.MEV.Canon`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Formal order -/

section Low

variable {A : Type*} [CommRing A]

/-- `f` has no terms of degree `≤ n`. -/
def LowZero (n : ℕ) (f : PowerSeries A) : Prop := ∀ i ≤ n, PowerSeries.coeff i f = 0

theorem LowZero.mul_left {n : ℕ} {f : PowerSeries A} (hf : LowZero n f) (g : PowerSeries A) :
    LowZero n (g * f) := fun i hi => by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [hf p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega), mul_zero]

theorem LowZero.mono {n n' : ℕ} {f : PowerSeries A} (hf : LowZero n' f) (h : n ≤ n') :
    LowZero n f := fun i hi => hf i (hi.trans h)

theorem LowZero.add {n : ℕ} {f g : PowerSeries A} (hf : LowZero n f) (hg : LowZero n g) :
    LowZero n (f + g) := fun i hi => by rw [map_add, hf i hi, hg i hi, add_zero]

theorem lowZero_zero (n : ℕ) : LowZero n (0 : PowerSeries A) := fun i _ => map_zero _

end Low

variable (Ls) in
/-- **Formal order `> n` along `W` at `p`**: for every `w ∈ W` and every law choice, the power series
`Q(p + exp(z w))` has no terms of degree `≤ n`. -/
def OrdGt (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) (n : ℕ)
    (p : GPtV d₀ d₁ Ls) : Prop :=
  ∀ w ∈ W, ∀ c' : Fin m → LC, LowZero n (aeval (phPt Ls p w c') Q)

variable (Ls) in
/-- The ideal of polynomials of formal order `> n` along `W` at every point of `E`. -/
noncomputable def ordIdeal (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ) (E : Set (GPtV d₀ d₁ Ls)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) where
  carrier := {Q | ∀ p ∈ E, OrdGt Ls W Q n p}
  add_mem' hP hQ p hp w hw c' := by rw [map_add]; exact (hP p hp w hw c').add (hQ p hp w hw c')
  zero_mem' p _ w _ c' := by rw [map_zero]; exact lowZero_zero n
  smul_mem' a Q hQ p hp w hw c' := by
    rw [smul_eq_mul, map_mul]; exact (hQ p hp w hw c').mul_left _

theorem mem_ordIdeal {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {n : ℕ} {E : Set (GPtV d₀ d₁ Ls)}
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} : Q ∈ ordIdeal Ls W n E ↔ ∀ p ∈ E, OrdGt Ls W Q n p :=
  Iff.rfl

theorem ordIdeal_anti (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) {n n' : ℕ} (h : n ≤ n')
    (E : Set (GPtV d₀ d₁ Ls)) : ordIdeal Ls W n' E ≤ ordIdeal Ls W n E :=
  fun _ hQ p hp w hw c' => (hQ p hp w hw c').mono h

/-- The formal point `p + exp(z w)` lies on `G̃`: every element of `I_G̃` vanishes on it. -/
theorem aeval_phPt_IG (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    aeval (phPt Ls p w c') Q = 0 := by
  have hle : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤
      RingHom.ker (aeval (phPt Ls p w c')).toRingHom := by
    rw [IG, Ideal.ofList, Ideal.span_le]
    rintro _ hP
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hP
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hP with (⟨j, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · simp only [YZ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul, aeval_X, map_one]
      rw [phPt_YZ, sub_self]
    · have h := (phPt_FG p w c' k).1
      simp only [Fn, F] at h
      simp only [Fk, F, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_sub, map_mul,
        map_pow, aeval_X, aeval_C, map_ofNat, g2L, g3L]
      exact h
    · have h := (phPt_FG p w c' k).2
      simp only [Gn, Gfib] at h
      simp only [Gk, Gfib, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_sub, map_mul,
        map_pow, aeval_X, map_ofNat]
      exact h
  exact hle hQ

theorem IG_le_ordIdeal (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ) (E : Set (GPtV d₀ d₁ Ls)) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ ordIdeal Ls W n E := fun _ hQ p _ w _ c' => by
  rw [aeval_phPt_IG p w c' hQ]; exact lowZero_zero n

/-! ### The chain -/

/-- `Σ[r]`: sums of `r` elements of `S`. -/
def sig (S : Finset (GPtV d₀ d₁ Ls)) (r : ℕ) : Set (GPtV d₀ d₁ Ls) :=
  {g | ∃ σ : Fin r → GPtV d₀ d₁ Ls, (∀ i, σ i ∈ S) ∧ g = ∑ i, σ i}

theorem sig_mono {S : Finset (GPtV d₀ d₁ Ls)} (hS : (0 : GPtV d₀ d₁ Ls) ∈ S) (r : ℕ) :
    sig S r ⊆ sig S (r + 1) := by
  rintro g ⟨σ, hσ, rfl⟩
  refine ⟨Fin.snoc σ 0, fun i => ?_, ?_⟩
  · induction i using Fin.lastCases with
    | last => simpa using hS
    | cast i => simpa using hσ i
  · rw [Fin.sum_univ_castSucc]; simp

variable (Ls) (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (S : Finset (GPtV d₀ d₁ Ls))
  (P : MvPolynomial (Var d₀ d₁ m) ℂ) (T : ℕ)

/-- Generators of `L_r`: Philippon's operators `δ^κ_σ P`, `σ ∈ Σ[r]`, `w ∈ W`, `κ ≤ r T`. -/
def gensR2 (r : ℕ) : Set (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  {Q | ∃ σ ∈ sig S r, ∃ w ∈ W, ∃ κ ≤ r * T, ∃ c c' : Fin m → LC, Q = phOp Ls σ w c c' κ P}

/-- Roy's ideal `L_r = I_G̃ + (gensR2 r)`. -/
noncomputable def Lr2 (r : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span (gensR2 Ls W S P T r)

variable {Ls W S P T}

theorem gensR2_mono (hS : (0 : GPtV d₀ d₁ Ls) ∈ S) (r : ℕ) :
    gensR2 Ls W S P T r ⊆ gensR2 Ls W S P T (r + 1) := by
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  exact ⟨σ, sig_mono hS r hσ, w, hw, κ, by nlinarith, c, c', rfl⟩

theorem Lr2_mono (hS : (0 : GPtV d₀ d₁ Ls) ∈ S) (r : ℕ) :
    Lr2 Ls W S P T r ≤ Lr2 Ls W S P T (r + 1) :=
  sup_le_sup_left (Ideal.span_mono (gensR2_mono hS r)) _

theorem Lr2_mono' (hS : (0 : GPtV d₀ d₁ Ls) ∈ S) {r r' : ℕ} (h : r ≤ r') :
    Lr2 Ls W S P T r ≤ Lr2 Ls W S P T r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Lr2_mono hS n)

/-- **Block degrees of the generators**: `FLE (tplE D)` for all `r`, `T`. -/
theorem gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE ℂ blk D) (r : ℕ) :
    ∀ Q ∈ gensR2 Ls W S P T r, Q ∈ FLE ℂ blk (tplE D) := by
  rintro _ ⟨σ, _, w, _, κ, _, c, c', rfl⟩
  exact phOp_mem_FLE σ w c c' κ hPD

theorem tplE_tplE_le (D : Blk m → ℕ) : tplE (tplE D) ≤ 9 • D := fun b => by
  simp only [tplE, Pi.smul_apply, smul_eq_mul]
  have := bmulV_le_three b
  calc bmulV b * (bmulV b * D b) ≤ 3 * (3 * D b) :=
        Nat.mul_le_mul this (Nat.mul_le_mul_right _ this)
    _ = 9 * D b := by ring

/-- Translates of generators (the generators of Roy's `A`): `FLE (tplE (tplE D)) ⊆ FLE (9 • D)`. -/
theorem transl_gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE ℂ blk D) (r : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ gensR2 Ls W S P T r) (v : GPtV d₀ d₁ Ls)
    (c : Fin m → LC) : τ Ls v c Q ∈ FLE ℂ blk (9 • D) :=
  LSG.ME.fle_le (transl_mem_FLE v c (gensR2_mem_FLE hPD r Q hQ)) (tplE_tplE_le D)

/-- The generators of `L_r` preserve `I_G̃`-membership: `L_r ⊇ I_G̃`, and `phOp` of an element of
`I_G̃` lies in `I_G̃` (so only `P ∉ I_G̃` matters). -/
theorem IG_le_Lr2 (r : ℕ) : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ Lr2 Ls W S P T r :=
  le_sup_left

end LSG.MEV
