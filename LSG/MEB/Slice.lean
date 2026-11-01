/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.TranslHF

/-!
# Affine slices of the multi-cone (A4.2, α; template `LSG.ME.Slice`)

The Hilbert-function part of the multiplicity estimate is run on **affine slices**
`sl α I = I + (ℓ_k − 1)_k`, with one linear chart form `ℓ_k = Σ_c α_{k,c} X_{k,c}` per block (for an elliptic
block, ME used `V + α W`; here the form is arbitrary, which is what B5 is stated for).

* `lsl α k`, `sl α I`; `lval α g k = ℓ_k(rep g_k)`; `nrm α g` the normalised cone representative;
  `vanishS α E`; `sl_vanish_le`: `sl α (vanish E) ≤ vanishS α E`.
* **`hom_mem_vanish_of_mem_sl`**: a multihomogeneous element of `sl α (vanish E)` lies in `vanish E`, for
  `vanish E` prime and all `ℓ_k ∉ vanish E`.
* **`hfun_le_sl`**: `H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)` (same hypotheses).
* **`exists_good_alpha`**: chart forms avoiding finitely many translates of a nonempty set.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- Chart-form coefficients: one linear form per block. -/
abbrev Alpha (B : Fin m → AbBlock) : Type := ∀ k, Fin (B k).N → ℂ

/-- The chart form `ℓ_k = Σ_c α_{k,c} X_{k,c}`. -/
noncomputable def lsl (α : Alpha B) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ c, C (α k c) * X (.e k c)

/-- The affine slice `I + (ℓ_k − 1)_k`. -/
noncomputable def sl (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  I ⊔ Ideal.span (Set.range fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1)

/-- `ℓ_k(rep g_k)`. -/
noncomputable def lval (α : Alpha B) (g : GPt d₀ d₁ B) (k : Fin m) : ℂ :=
  ∑ c, α k c * (B k).rep (g.2.2 k) c

open Classical in
/-- The normalised cone representative (`ℓ_k = 1` when `lval ≠ 0`). -/
noncomputable def nrm (α : Alpha B) (g : GPt d₀ d₁ B) : Var d₀ d₁ B → ℂ :=
  coords g fun k => if h : lval α g k = 0 then 1 else Units.mk0 (lval α g k)⁻¹ (inv_ne_zero h)

/-- Polynomials vanishing at the normalised representatives of the points of `E` with all
`ℓ_k(rep g_k) ≠ 0`. -/
noncomputable def vanishS (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  StrongSix.M2.vanish' (nrm α) {g | g ∈ E ∧ ∀ k, lval α g k ≠ 0}

theorem eval_lsl (α : Alpha B) (x : Var d₀ d₁ B → ℂ) (k : Fin m) :
    eval x (lsl (d₀ := d₀) (d₁ := d₁) α k) = ∑ c, α k c * x (.e k c) := by
  simp [lsl, map_sum]

theorem eval_coords_lsl (α : Alpha B) (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (k : Fin m) :
    eval (coords g lam) (lsl α k) = lam k * lval α g k := by
  rw [eval_lsl, lval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [coords_e]; ring

theorem sl_vanish_le (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    sl α (vanish E) ≤ vanishS α E := by
  refine sup_le (fun P hP => (StrongSix.M2.mem_vanish' _).mpr fun g hg =>
    mem_vanish.mp hP g hg.1 _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
  rw [map_sub, nrm, eval_coords_lsl]
  simp [hg.2 k]

theorem isWeightedHomogeneous_lsl (α : Alpha B) (k : Fin m) :
    IsWeightedHomogeneous wV (lsl (d₀ := d₀) (d₁ := d₁) α k) (Pi.single k 1) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_
  exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X ℂ wV (Var.e k c : Var d₀ d₁ B)) _

/-- **Multihomogeneous elements of a slice.** -/
theorem hom_mem_vanish_of_mem_sl (α : Alpha B) {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wV Q d)
    (hQs : Q ∈ sl α (vanish E)) : Q ∈ vanish E := by
  classical
  have hprod : ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ∉ vanish E := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
    exact hℓ k hk
  have hmul : Q * ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ∈ vanish E := by
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [map_mul, map_prod]
    by_cases h0 : ∃ k, lval α g k = 0
    · obtain ⟨k, hk⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_coords_lsl, hk, mul_zero]),
        mul_zero]
    push_neg at h0
    have hn := (StrongSix.M2.mem_vanish' _).mp (sl_vanish_le α E hQs) g ⟨hg, h0⟩
    rw [nrm, eval_coords_eq_zero_iff hQ g _ lam] at hn
    rw [hn, zero_mul]
  exact (hp.mem_or_mem hmul).resolve_right hprod

/-! ### The dimension count -/

section HFun

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  (β : σ → ι) (D : ι → ℕ)

/-- The submodule `J ∩ FLE(tD)` of `FLE(tD)`. -/
noncomputable abbrev Nsub (J : Ideal (MvPolynomial σ ℂ)) (t : ℕ) :
    Submodule ℂ (FLE ℂ β (t • D)) :=
  (J.restrictScalars ℂ).comap (FLE ℂ β (t • D)).subtype

theorem hfun_eq_finrank_quotient (J : Ideal (MvPolynomial σ ℂ)) (t : ℕ) :
    hfun β D ℂ J t = finrank ℂ (FLE ℂ β (t • D) ⧸ Nsub β D J t) := by
  have h1 := Submodule.finrank_quotient_add_finrank (Nsub β D J t)
  have h2 : finrank ℂ (Nsub β D J t) = finrank ℂ ↥(J.restrictScalars ℂ ⊓ FLE ℂ β (t • D)) := by
    rw [Nsub, StrongSix.M2.finrank_comap_subtype, inf_comm]
  unfold hfun
  omega

end HFun

theorem bdeg_e_eq_weight (s : Var d₀ d₁ B →₀ ℕ) (k : Fin m) :
    StrongSix.M2.bdeg blk s (.e k) = Finsupp.weight wV s k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    StrongSix.M2.bdeg]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases v <;> simp [blk, wV, Pi.single_apply, eq_comm]

/-- The block degrees with the abelian ones replaced by `e`. -/
def Dcut (t : ℕ) (D : Blk m → ℕ) (e : Fin m → ℕ) : Blk m → ℕ
  | .x => t * D .x
  | .yz => t * D .yz
  | .e k => e k

theorem comp_mem_FLE {t : ℕ} {D : Blk m → ℕ} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ FLE ℂ blk (t • D)) (e : Fin m → ℕ) :
    weightedHomogeneousComponent wV e P ∈ FLE ℂ blk (Dcut t D e) := by
  classical
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at hP ⊢
  intro s hs
  have hs' : s ∈ P.support := by
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hs
    split_ifs at hs with h
    · exact MvPolynomial.mem_support_iff.mpr hs
    · exact absurd rfl hs
  have hw : Finsupp.weight wV s = e := by
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hs
    split_ifs at hs with h
    · exact h
    · exact absurd rfl hs
  have hS := hP hs'
  intro b
  cases b with
  | x => exact hS .x
  | yz => exact hS .yz
  | e k => rw [bdeg_e_eq_weight, hw]; rfl

theorem fle_X_single (v : Var d₀ d₁ B) :
    (X v : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ FLE ℂ blk (Pi.single (blk v) 1) :=
  mem_FLE_of_isWH (isWeightedHomogeneous_X ℂ wB v) le_rfl

theorem lsl_mem_FLE (α : Alpha B) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k ∈ FLE ℂ blk (Pi.single (Blk.e k) 1) := by
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (fle_X_single (Var.e k c))

theorem finrank_quotient_le_of_ker_le {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : V →ₗ[ℂ] W) {N : Submodule ℂ V} (h : LinearMap.ker f ≤ N) :
    finrank ℂ (V ⧸ N) ≤ finrank ℂ W := by
  have h1 := Submodule.finrank_quotient_add_finrank N
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_mono h
  have h4 := Submodule.finrank_le (LinearMap.range f)
  omega

/-- **Slicing loses at most `∏ (t D_k + 1)`**, for any ideal `I` whose multihomogeneous elements lie
in `vanish E` (`vanish E` prime, all `ℓ_k ∉ vanish E`). -/
theorem hfun_le_of_hom (α : Alpha B) {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ))
    (hI : ∀ (Q : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsWeightedHomogeneous wV Q d →
      Q ∈ I → Q ∈ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤ (∏ k, (t * D (.e k) + 1)) * hfun blk D ℂ I t := by
  classical
  set F := FLE ℂ blk (t • D)
  set N : Fin m → ℕ := fun k => t * D (.e k)
  let Ix := (k : Fin m) → Fin (N k + 1)
  let ev : Ix → (Fin m → ℕ) := fun e k => (e k : ℕ)
  let L : Ix → MvPolynomial (Var d₀ d₁ B) ℂ := fun e =>
    ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ^ (N k - ev e k)
  have hLmem : ∀ e (P : MvPolynomial (Var d₀ d₁ B) ℂ), P ∈ F →
      L e * weightedHomogeneousComponent wV (ev e) P ∈ F := by
    intro e P hP
    have h1 : L e ∈ FLE ℂ blk (∑ k, (N k - ev e k) • Pi.single (Blk.e k) 1) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun k _ => StrongSix.M2.pow_mem_FLE' (lsl_mem_FLE α k) _
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ h1 (comp_mem_FLE hP (ev e)))
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    cases b with
    | x => simp [Dcut]
    | yz => simp [Dcut]
    | e k =>
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      have := (e k).isLt
      have hN : N k = t * D (.e k) := rfl
      simp only [ite_true, mul_one, Dcut, ev]
      omega
  let φ : Ix → F →ₗ[ℂ] F := fun e =>
    ((LinearMap.mulLeft ℂ (L e) ∘ₗ (weightedHomogeneousComponent wV (ev e)).restrictScalars ℂ) ∘ₗ
      F.subtype).codRestrict F fun P => hLmem e P P.2
  let Φ : F →ₗ[ℂ] (Ix → F ⧸ Nsub blk D I t) :=
    LinearMap.pi fun e => (Nsub blk D I t).mkQ ∘ₗ φ e
  have hker : LinearMap.ker Φ ≤ Nsub blk D (vanish E) t := by
    intro P hP
    have hcomp : ∀ e, weightedHomogeneousComponent wV (ev e) (P : MvPolynomial (Var d₀ d₁ B) ℂ) ∈
        vanish E := by
      intro e
      have h0 := congrFun (LinearMap.mem_ker.mp hP) e
      simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hs : L e * weightedHomogeneousComponent wV (ev e) (P : MvPolynomial (Var d₀ d₁ B) ℂ) ∈
          I := h0
      have hhom : IsWeightedHomogeneous wV (L e * weightedHomogeneousComponent wV (ev e)
          (P : MvPolynomial (Var d₀ d₁ B) ℂ)) (∑ k, (N k - ev e k) • Pi.single k 1 + ev e) :=
        (IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_lsl α k).pow _).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      have hv := hI _ _ hhom hs
      have hL : L e ∉ vanish E := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
        exact hℓ k (hp.mem_of_pow_mem _ hk)
      exact (hp.mem_or_mem hv).resolve_left hL
    have hsum : (P : MvPolynomial (Var d₀ d₁ B) ℂ) =
        ∑ e : Ix, weightedHomogeneousComponent wV (ev e) P := by
      ext s
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      by_cases hs : (P : MvPolynomial (Var d₀ d₁ B) ℂ).coeff s = 0
      · simp [hs]
      have hsS : s ∈ StrongSix.M2.S blk (t • D) := by
        have h' : (P : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ FLE ℂ blk (t • D) := P.2
        rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at h'
        exact h' (MvPolynomial.mem_support_iff.mpr hs)
      have hb : ∀ k, Finsupp.weight wV s k < N k + 1 := fun k => by
        have := hsS (.e k)
        rw [bdeg_e_eq_weight] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact Nat.lt_succ_of_le this
      let e₀ : Ix := fun k => ⟨Finsupp.weight wV s k, hb k⟩
      rw [Finset.sum_eq_single e₀ (fun e _ he => ite_eq_right_iff.mpr fun hw =>
          absurd (funext fun k => Fin.ext (congrFun hw k).symm) he) (by simp)]
      simp only [↓reduceIte]
    change (P : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanish E
    rw [hsum]
    exact Ideal.sum_mem _ fun e _ => hcomp e
  have h := finrank_quotient_le_of_ker_le Φ hker
  rw [← hfun_eq_finrank_quotient, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, ← hfun_eq_finrank_quotient] at h
  have hcard : Fintype.card Ix = ∏ k, (t * D (.e k) + 1) := by
    simp [Ix, Fintype.card_pi, N]
  rw [← hcard]
  calc hfun blk D ℂ (vanish E) t ≤ Fintype.card Ix • hfun blk D ℂ I t := h
    _ = _ := smul_eq_mul _ _

/-- **Slicing loses at most `∏ (t D_k + 1)`**: for `vanish E` prime with all `ℓ_k ∉ vanish E`,
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)`. -/
theorem hfun_le_sl (α : Alpha B) {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤
      (∏ k, (t * D (.e k) + 1)) * hfun blk D ℂ (sl α (vanish E)) t :=
  hfun_le_of_hom α hp hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_sl α hp hℓ hQ hs) D t

/-! ### Choice of the chart forms -/

/-- **Good chart forms** for finitely many translates of a nonempty set: `ℓ_k ∉ I(a + V)`. -/
theorem exists_good_alpha {V : Set (GPt d₀ d₁ B)} (hV : V.Nonempty) (R : Finset (GPt d₀ d₁ B)) :
    ∃ α : Alpha B, ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V) := by
  classical
  obtain ⟨v, hv⟩ := hV
  -- for each block, avoid the finitely many hyperplanes `{α_k | α_k · rep (v + a)_k = 0}`
  have hblk : ∀ k, ∃ αk : Fin (B k).N → ℂ, ∀ a ∈ R,
      ∑ c, αk c * (B k).rep ((v + a).2.2 k) c ≠ 0 := by
    intro k
    let p : R → Submodule ℂ (Fin (B k).N → ℂ) := fun a =>
      LinearMap.ker (Fintype.linearCombination ℂ ((B k).rep ((v + a.1).2.2 k)))
    have hp : ∀ a, p a ≠ ⊤ := by
      intro a htop
      apply (B k).rep_ne_zero ((v + a.1).2.2 k)
      funext c
      have := LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top : (Pi.single c 1) ∈ p a)
      simpa [Fintype.linearCombination_apply, Pi.single_apply] using this
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
    refine ⟨x, fun a ha h0 => hx ⟨a, ha⟩ (LinearMap.mem_ker.mpr ?_)⟩
    simpa [Fintype.linearCombination_apply, mul_comm] using h0
  choose α hα using hblk
  refine ⟨α, fun a ha k hmem => hα k a ha ?_⟩
  have h0 := mem_vanish.mp hmem (v + a) ⟨v, hv, rfl⟩ 1
  rw [eval_coords_lsl] at h0
  simpa [lval] using h0

end LSG.MEB
