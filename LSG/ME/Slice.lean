import Mathlib
import LSG.ME.SubgroupHilb2
import LSG.ME.TranslHF

/-!
# Affine slices of the multi-cone (STAGE2 §11, item S2)

The filtered Hilbert function of an ideal of the multi-cone sees the *irrelevant* components
`{X_k = 0}` (STAGE2 §11). The Hilbert-function part of the multiplicity estimate is therefore run on
**affine slices** `sl α I = I + (ℓ_k − 1)_k`, `ℓ_k = V_k + α_k W_k` (one chart form per elliptic
block), which only see the points with all `ℓ_k(rep g_k) ≠ 0`, at their normalised cone
representative `ℓ_k = 1`.

* `lsl α k = V_k + α_k W_k`, `sl α I`; `lval α g k = ℓ_k(rep g_k)`; `nrm α g` the normalised cone
  representative; `vanishS α E` the polynomials vanishing at the normalised representatives of the
  points of `E` with all `lval ≠ 0`; `sl_vanish_le`: `sl α (vanish E) ≤ vanishS α E`.
* **`hom_mem_vanish_of_mem_sl`**: a multihomogeneous element of `sl α (vanish E)` lies in
  `vanish E`, for `vanish E` prime and all `ℓ_k ∉ vanish E`.
* **`hfun_le_sl`**: `H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)` (same hypotheses):
  decompose by elliptic multidegree `e`, homogenise each component with `∏ ℓ_k^{t D_k − e_k}`.
  With `hfun_H0_ge''` this gives the sliced lower bound for `H⁰` of degree `t₀ + t₁ + t₂`.
* **`hfun_sl_coset_ge`**: for every coset `a + H⁰` with all `ℓ_k ∉ I(a + H⁰)`:
  `(tD₀/t₀+1)^{t₀} (tD₁/t₁+1)^{t₁} ((tD₂+1)²)^{t₂} (tD₂+1)^{m−t₂} ≤
  2^m (2tD₂+1)^m · H(sl α I(a + H⁰); 2t)`, with `t₀ = dim h₀`, `t₁ = d₁ − dim U` of the product
  decomposition (`ML`) and `t₂ = dim t`: a polynomial lower bound of degree `t₀ + t₁ + t₂`.
-/

open MvPolynomial LSG.Elliptic Module
open StrongSix.M2 (FLE hfun)

namespace LSG.ME

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- The chart form `ℓ_k = V_k + α_k W_k`. -/
noncomputable def lsl (α : Fin m → K) (k : Fin m) : MvPolynomial (Var d₀ d₁ m) K :=
  X (.e k 1) + C (α k) * X (.e k 2)

/-- The affine slice `I + (ℓ_k − 1)_k`. -/
noncomputable def sl (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  I ⊔ Ideal.span (Set.range fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1)

/-- `ℓ_k(rep g_k)`. -/
def lval (α : Fin m → K) (g : GPt K d₀ d₁ g₂ g₃) (k : Fin m) : K :=
  rep (g.2.2 k) 1 + α k * rep (g.2.2 k) 2

open Classical in
/-- The normalised cone representative (`ℓ_k = 1` when `lval ≠ 0`). -/
noncomputable def nrm (α : Fin m → K) (g : GPt K d₀ d₁ g₂ g₃) : Var d₀ d₁ m → K :=
  coords g fun k => if h : lval α g k = 0 then 1 else Units.mk0 (lval α g k)⁻¹ (inv_ne_zero h)

/-- Polynomials vanishing at the normalised representatives of the points of `E` with all
`ℓ_k(rep g_k) ≠ 0`. -/
noncomputable def vanishS (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  StrongSix.M2.vanish' (nrm α) {g | g ∈ E ∧ ∀ k, lval α g k ≠ 0}

theorem eval_coords_lsl (α : Fin m → K) (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (k : Fin m) :
    eval (coords g lam) (lsl α k) = lam k * lval α g k := by
  simp [lsl, lval, coords]; ring

theorem sl_vanish_le (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    sl α (vanish E) ≤ vanishS α E := by
  refine sup_le (fun P hP => (StrongSix.M2.mem_vanish' _).mpr fun g hg =>
    mem_vanish.mp hP g hg.1 _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
  rw [map_sub, nrm, eval_coords_lsl]
  simp [hg.2 k]

theorem isWeightedHomogeneous_lsl (α : Fin m → K) (k : Fin m) :
    IsWeightedHomogeneous wV (lsl (d₀ := d₀) (d₁ := d₁) α k) (Pi.single k 1) := by
  refine IsWeightedHomogeneous.add ?_ ?_
  · exact isWeightedHomogeneous_X K wV (Var.e k 1 : Var d₀ d₁ m)
  · exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X K wV (Var.e k 2 : Var d₀ d₁ m)) _

/-- **Multihomogeneous elements of a slice.** -/
theorem hom_mem_vanish_of_mem_sl [Infinite K] (α : Fin m → K) {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wV Q d)
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
    push Not at h0
    have hn := (StrongSix.M2.mem_vanish' _).mp (sl_vanish_le α E hQs) g ⟨hg, h0⟩
    rw [nrm, eval_coords_eq_zero_iff hQ g _ lam] at hn
    rw [hn, zero_mul]
  exact (hp.mem_or_mem hmul).resolve_right hprod

/-! ### The dimension count -/

theorem bdeg_e_eq_weight (s : Var d₀ d₁ m →₀ ℕ) (k : Fin m) :
    StrongSix.M2.bdeg blk s (.e k) = Finsupp.weight wV s k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    StrongSix.M2.bdeg]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases v <;> simp [blk, wV, Pi.single_apply, eq_comm]

/-- The block degrees with the elliptic ones replaced by `e`. -/
def Dcut (t : ℕ) (D : Blk m → ℕ) (e : Fin m → ℕ) : Blk m → ℕ
  | .x => t * D .x
  | .yz => t * D .yz
  | .e k => e k

theorem comp_mem_FLE {t : ℕ} {D : Blk m → ℕ} {P : MvPolynomial (Var d₀ d₁ m) K}
    (hP : P ∈ FLE K blk (t • D)) (e : Fin m → ℕ) :
    weightedHomogeneousComponent wV e P ∈ FLE K blk (Dcut t D e) := by
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

theorem lsl_mem_FLE (α : Fin m → K) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k ∈ FLE K blk (Pi.single (Blk.e k) 1) := by
  have h1 := fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k 1)
  have h2 := fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k 2)
  rw [blk_e] at h1 h2
  refine fle_add h1 ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ h2

theorem finrank_quotient_le_of_ker_le {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) {N : Submodule K V} (h : LinearMap.ker f ≤ N) :
    finrank K (V ⧸ N) ≤ finrank K W := by
  have h1 := Submodule.finrank_quotient_add_finrank N
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_mono h
  have h4 := Submodule.finrank_le (LinearMap.range f)
  omega

/-- **Slicing loses at most `∏ (t D_k + 1)`**, for any ideal `I` whose multihomogeneous elements lie
in `vanish E` (`vanish E` prime, all `ℓ_k ∉ vanish E`):
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(I; t)`. -/
theorem hfun_le_of_hom (α : Fin m → K) {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    (I : Ideal (MvPolynomial (Var d₀ d₁ m) K))
    (hI : ∀ (Q : MvPolynomial (Var d₀ d₁ m) K) (d : Fin m → ℕ), IsWeightedHomogeneous wV Q d →
      Q ∈ I → Q ∈ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D K (vanish E) t ≤ (∏ k, (t * D (.e k) + 1)) * hfun blk D K I t := by
  classical
  set F := FLE K blk (t • D)
  set N : Fin m → ℕ := fun k => t * D (.e k)
  let Ix := (k : Fin m) → Fin (N k + 1)
  let ev : Ix → (Fin m → ℕ) := fun e k => (e k : ℕ)
  let L : Ix → MvPolynomial (Var d₀ d₁ m) K := fun e =>
    ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ^ (N k - ev e k)
  have hLmem : ∀ e (P : MvPolynomial (Var d₀ d₁ m) K), P ∈ F →
      L e * weightedHomogeneousComponent wV (ev e) P ∈ F := by
    intro e P hP
    have h1 : L e ∈ FLE K blk (∑ k, (N k - ev e k) • Pi.single (Blk.e k) 1) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun k _ => StrongSix.M2.pow_mem_FLE' (lsl_mem_FLE α k) _
    refine StrongSix.M2.FLE_mono K blk (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE K h1 (comp_mem_FLE hP (ev e)))
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
  -- the map
  let φ : Ix → F →ₗ[K] F := fun e =>
    ((LinearMap.mulLeft K (L e) ∘ₗ (weightedHomogeneousComponent wV (ev e)).restrictScalars K) ∘ₗ
      F.subtype).codRestrict F fun P => hLmem e P P.2
  let Φ : F →ₗ[K] (Ix → F ⧸ Nsub (K := K) blk D I t) :=
    LinearMap.pi fun e => (Nsub (K := K) blk D I t).mkQ ∘ₗ φ e
  have hker : LinearMap.ker Φ ≤ Nsub (K := K) blk D (vanish E) t := by
    intro P hP
    have hcomp : ∀ e, weightedHomogeneousComponent wV (ev e) (P : MvPolynomial (Var d₀ d₁ m) K) ∈
        vanish E := by
      intro e
      have h0 := congrFun (LinearMap.mem_ker.mp hP) e
      simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hs : L e * weightedHomogeneousComponent wV (ev e) (P : MvPolynomial (Var d₀ d₁ m) K) ∈
          I := h0
      have hhom : IsWeightedHomogeneous wV (L e * weightedHomogeneousComponent wV (ev e)
          (P : MvPolynomial (Var d₀ d₁ m) K)) (∑ k, (N k - ev e k) • Pi.single k 1 + ev e) :=
        (IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_lsl α k).pow _).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      have hv := hI _ _ hhom hs
      have hL : L e ∉ vanish E := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
        exact hℓ k (hp.mem_of_pow_mem _ hk)
      exact (hp.mem_or_mem hv).resolve_left hL
    -- `P` is the sum of its components in the box
    have hsum : (P : MvPolynomial (Var d₀ d₁ m) K) =
        ∑ e : Ix, weightedHomogeneousComponent wV (ev e) P := by
      ext s
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      by_cases hs : (P : MvPolynomial (Var d₀ d₁ m) K).coeff s = 0
      · simp [hs]
      have hsS : s ∈ StrongSix.M2.S blk (t • D) := by
        have h' : (P : MvPolynomial (Var d₀ d₁ m) K) ∈ FLE K blk (t • D) := P.2
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
    change (P : MvPolynomial (Var d₀ d₁ m) K) ∈ vanish E
    rw [hsum]
    exact Ideal.sum_mem _ fun e _ => hcomp e
  have h := finrank_quotient_le_of_ker_le Φ hker
  rw [← hfun_eq_finrank_quotient, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    ← hfun_eq_finrank_quotient] at h
  have hcard : Fintype.card Ix = ∏ k, (t * D (.e k) + 1) := by
    simp [Ix, Fintype.card_pi, N]
  rw [← hcard]
  calc hfun blk D K (vanish E) t ≤ Fintype.card Ix • hfun blk D K I t := h
    _ = _ := smul_eq_mul _ _

/-- **Slicing loses at most `∏ (t D_k + 1)`**: for `vanish E` prime with all `ℓ_k ∉ vanish E`,
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)`. -/
theorem hfun_le_sl [Infinite K] (α : Fin m → K) {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D K (vanish E) t ≤
      (∏ k, (t * D (.e k) + 1)) * hfun blk D K (sl α (vanish E)) t :=
  hfun_le_of_hom α hp hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_sl α hp hℓ hQ hs) D t

/-! ### The sliced lower bound for cosets of `H⁰` -/

section Coset

open LSG.W88 (Tan IsAbelianTangent)

variable {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-- **The sliced Hilbert lower bound for a coset of `H⁰`.** -/
theorem hfun_sl_coset_ge (hH : IsSubgroupG H) (hc : IsZClosed H) (α : Fin m → ℂ)
    (a : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))
    (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH hc))) (D₀ D₁ D₂ t : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      (t * D₀ / finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) + 1) ^
          finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) *
        (t * D₁ / (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) + 1) ^
          (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) *
        ((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb * (t * D₂ + 1) ^ (m - finrank ℂ tAb) ≤
      2 ^ m * (2 * t * D₂ + 1) ^ m *
        hfun blk (Dfun D₀ D₁ D₂) ℂ (sl α (vanish (gtransl a (H0 Ls hH hc)))) (2 * t) := by
  obtain ⟨tAb, hab, htAb, hle⟩ := hfun_H0_ge'' hH hc _ _ (prodSet_ML_subset_projL hH hc)
    D₀ D₁ D₂ t
  refine ⟨tAb, hab, htAb, le_trans hle ?_⟩
  have hp0 := vanish_H0_isPrime (Ls := Ls) hH hc
  have hc0 := isZClosed_H0 (Ls := Ls) hH hc
  have h2 := hfun_le_transl two_ne_zero (discr_g2L Ls) (Dfun D₀ D₁ D₂) (H0 Ls hH hc) a t
  have h3 := hfun_le_sl α (vanish_gtransl_isPrime two_ne_zero (discr_g2L Ls) hc0 hp0 a) hℓ
    (Dfun D₀ D₁ D₂) (2 * t)
  have hprod : ∏ k : Fin m, (2 * t * Dfun (m := m) D₀ D₁ D₂ (.e k) + 1) = (2 * t * D₂ + 1) ^ m := by
    simp [Dfun]
  rw [hprod] at h3
  calc hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH hc)) t
      ≤ 2 ^ m * hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (gtransl a (H0 Ls hH hc))) (2 * t) := h2
    _ ≤ 2 ^ m * ((2 * t * D₂ + 1) ^ m *
          hfun blk (Dfun D₀ D₁ D₂) ℂ (sl α (vanish (gtransl a (H0 Ls hH hc)))) (2 * t)) :=
        Nat.mul_le_mul_left _ h3
    _ = _ := by ring

end Coset

end LSG.ME
