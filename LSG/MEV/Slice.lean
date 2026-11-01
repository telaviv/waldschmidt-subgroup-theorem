import Mathlib
import LSG.MEV.IGNull
import LSG.MEV.Assoc
import LSG.ME.SliceIG

/-!
# Affine slices of the `E^♮` multi-cone (STAGE2 §11 ported to `G̃`, STAGE5_MEV §4)

The cone over `X = V(F, G) ⊂ ℙ⁴` contains the irrelevant plane `U = V = W = 0`. As in the abelian
case (`LSG.ME.Slice`) the Hilbert-function part of the multiplicity estimate is run on **affine
slices** `sl α I = I + (ℓ_k − 1)_k`, `ℓ_k = V_k + α_k W_k` (one *base* chart form per `E^♮`
block; the fibre coordinates `T₁, T₃` are not sliced). `ℓ_k` vanishes on the irrelevant plane, so
the sliced zero sets consist of normalised representatives of points of `G̃` only.

* `wtV`: the multigrading by `E^♮` blocks; `isHomV_iff_wtV` (the same as `IsHomV`).
* `lsl α k`, `sl α I`, `lval α g k = ℓ_k(repV g_k)`, `nrm α g`, `vanishS α E`, `sl_vanish_le`.
* `coords_mul`, `eval_coords_eq_zero_iff` (multihomogeneous polynomials vanish at all or none of
  the cone representatives of a point).
* **`hom_mem_vanish_of_mem_sl`**: a multihomogeneous element of `sl α (vanish E)` lies in
  `vanish E` (`vanish E` prime, all `ℓ_k ∉ vanish E`).
* **`hfun_le_of_hom`**, **`hfun_le_sl`**:
  `H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)`.
-/

open MvPolynomial LSG.Elliptic Module
open StrongSix.M2 (FLE hfun)
open LSG.ME (Blk Nsub hfun_eq_finrank_quotient finrank_quotient_le_of_ker_le fle_X fle_add)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ}

/-- The multigrading by the `E^♮` blocks. -/
def wtV : Var d₀ d₁ m → Fin m → ℕ
  | .e k _ => Pi.single k 1
  | _ => 0

@[simp] theorem wtV_e (k : Fin m) (c : Fin 5) : wtV (.e k c : Var d₀ d₁ m) = Pi.single k 1 := rfl

theorem weight_wtV_apply (s : Var d₀ d₁ m →₀ ℕ) (k : Fin m) :
    Finsupp.weight wtV s k = Finsupp.weight (LSG.MEV.wb blk (Blk.e k)) s := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases v <;> simp [wtV, LSG.MEV.wb, blk, Pi.single_apply, eq_comm]

/-- `IsHomV` is multihomogeneity for `wtV`. -/
theorem isHomV_iff_wtV {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} :
    IsHomV Q d ↔ IsWeightedHomogeneous wtV Q d := by
  constructor
  · intro h s hs
    funext k
    rw [weight_wtV_apply]; exact h k hs
  · intro h k s hs
    rw [← weight_wtV_apply, h hs]

section Field

variable {K : Type*} [Field K]

/-- The chart form `ℓ_k = V_k + α_k W_k`. -/
noncomputable def lsl (α : Fin m → K) (k : Fin m) : MvPolynomial (Var d₀ d₁ m) K :=
  X (.e k 1) + C (α k) * X (.e k 2)

/-- The affine slice `I + (ℓ_k − 1)_k`. -/
noncomputable def sl (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  I ⊔ Ideal.span (Set.range fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1)

theorem le_sl (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : I ≤ sl α I :=
  le_sup_left

theorem lsl_sub_one_mem_sl (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) (k : Fin m) :
    lsl α k - 1 ∈ sl α I :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

theorem sl_mono (α : Fin m → K) {I J : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (h : I ≤ J) :
    sl α I ≤ sl α J :=
  sup_le_sup_right h _

theorem isWeightedHomogeneous_lsl (α : Fin m → K) (k : Fin m) :
    IsWeightedHomogeneous wtV (lsl (d₀ := d₀) (d₁ := d₁) α k) (Pi.single k 1) := by
  refine IsWeightedHomogeneous.add ?_ ?_
  · exact isWeightedHomogeneous_X K wtV (Var.e k 1 : Var d₀ d₁ m)
  · exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X K wtV (Var.e k 2 : Var d₀ d₁ m)) _

theorem bdeg_e_eq_weight (s : Var d₀ d₁ m →₀ ℕ) (k : Fin m) :
    StrongSix.M2.bdeg blk s (.e k) = Finsupp.weight wtV s k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    StrongSix.M2.bdeg]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases v <;> simp [blk, wtV, Pi.single_apply, eq_comm]

/-- The block degrees with the elliptic ones replaced by `e`. -/
def Dcut (t : ℕ) (D : Blk m → ℕ) (e : Fin m → ℕ) : Blk m → ℕ
  | .x => t * D .x
  | .yz => t * D .yz
  | .e k => e k

theorem comp_mem_FLE {t : ℕ} {D : Blk m → ℕ} {P : MvPolynomial (Var d₀ d₁ m) K}
    (hP : P ∈ FLE K blk (t • D)) (e : Fin m → ℕ) :
    weightedHomogeneousComponent wtV e P ∈ FLE K blk (Dcut t D e) := by
  classical
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at hP ⊢
  intro s hs
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hs
  split_ifs at hs with hw
  · have hS := hP (MvPolynomial.mem_support_iff.mpr hs)
    intro b
    cases b with
    | x => exact hS .x
    | yz => exact hS .yz
    | e k => rw [bdeg_e_eq_weight, hw]; rfl
  · exact absurd rfl hs

theorem lsl_mem_FLE (α : Fin m → K) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k ∈ FLE K blk (Pi.single (Blk.e k) 1) := by
  have h1 := fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k 1)
  have h2 := fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k 2)
  rw [blk_e] at h1 h2
  refine fle_add h1 ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ h2

end Field

/-! ### Points, normalised representatives -/

variable {Ls : Fin m → PeriodPair}

/-- `ℓ_k(repV g_k)`. -/
noncomputable def lval (α : Fin m → ℂ) (g : GPtV d₀ d₁ Ls) (k : Fin m) : ℂ :=
  repV (g.2.2 k) 1 + α k * repV (g.2.2 k) 2

open Classical in
/-- The normalised cone representative (`ℓ_k = 1` where `lval ≠ 0`). -/
noncomputable def nrm (α : Fin m → ℂ) (g : GPtV d₀ d₁ Ls) : Var d₀ d₁ m → ℂ :=
  coords g fun k => if h : lval α g k = 0 then 1 else Units.mk0 (lval α g k)⁻¹ (inv_ne_zero h)

/-- Polynomials vanishing at the normalised representatives of the points of `E` with all
`ℓ_k(repV g_k) ≠ 0`. -/
noncomputable def vanishS (α : Fin m → ℂ) (E : Set (GPtV d₀ d₁ Ls)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  StrongSix.M2.vanish' (nrm α) {g | g ∈ E ∧ ∀ k, lval α g k ≠ 0}

theorem eval_coords_lsl (α : Fin m → ℂ) (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) (k : Fin m) :
    eval (coords g lam) (lsl α k) = lam k * lval α g k := by
  simp [lsl, lval, coords]; ring

theorem sl_vanish_le (α : Fin m → ℂ) (E : Set (GPtV d₀ d₁ Ls)) :
    sl α (vanish E) ≤ vanishS α E := by
  refine sup_le (fun P hP => (StrongSix.M2.mem_vanish' _).mpr fun g hg =>
    mem_vanish.mp hP g hg.1 _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
  rw [map_sub, nrm, eval_coords_lsl]
  simp [hg.2 k]

/-- Rescaling the cone coordinates. -/
theorem coords_mul (g : GPtV d₀ d₁ Ls) (μ lam : Fin m → ℂˣ) :
    coords g (fun k => μ k * lam k) =
      fun v => (∏ k, ((μ k : ℂˣ) : ℂ) ^ wtV v k) * coords g lam v := by
  funext v
  cases v with
  | x i => simp [coords, wtV]
  | y j => simp [coords, wtV]
  | z j => simp [coords, wtV]
  | e k c =>
    simp only [coords, coordsZ_e, wtV, Units.val_mul, Pi.single_apply, pow_ite, pow_one,
      pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- Multihomogeneous polynomials vanish at all or none of the cone representatives of `g`. -/
theorem eval_coords_eq_zero_iff {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wtV Q d) (g : GPtV d₀ d₁ Ls) (lam lam' : Fin m → ℂˣ) :
    eval (coords g lam) Q = 0 ↔ eval (coords g lam') Q = 0 := by
  have e : lam' = fun k => (lam' k * (lam k)⁻¹) * lam k := by
    funext k; rw [inv_mul_cancel_right]
  rw [e, coords_mul, LSG.ME.eval_scale wtV _ _ hQ, mul_eq_zero, or_iff_right]
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Units.ne_zero _))

theorem prod_lsl_notMem {s : Finset (Fin m)} {α : Fin m → ℂ} {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k ∈ s, lsl α k ∉ vanish E) :
    ∏ k ∈ s, lsl (d₀ := d₀) (d₁ := d₁) α k ∉ vanish E := by
  intro h
  obtain ⟨k, hk, hk'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
  exact hℓ k hk hk'

/-- **Multihomogeneous elements of a slice.** -/
theorem hom_mem_vanish_of_mem_sl (α : Fin m → ℂ) {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wtV Q d)
    (hQs : Q ∈ sl α (vanish E)) : Q ∈ vanish E := by
  classical
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
  exact (hp.mem_or_mem hmul).resolve_right (prod_lsl_notMem hp fun k _ => hℓ k)

/-! ### Slicing loses at most `∏ (t D_k + 1)` -/

/-- **Slicing loses at most `∏ (t D_k + 1)`**, for any ideal `I` whose multihomogeneous elements lie
in `vanish E` (`vanish E` prime, all `ℓ_k ∉ vanish E`):
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(I; t)`. -/
theorem hfun_le_of_hom (α : Fin m → ℂ) {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    (I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ))
    (hI : ∀ (Q : MvPolynomial (Var d₀ d₁ m) ℂ) (d : Fin m → ℕ), IsWeightedHomogeneous wtV Q d →
      Q ∈ I → Q ∈ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤ (∏ k, (t * D (.e k) + 1)) * hfun blk D ℂ I t := by
  classical
  set F := FLE ℂ blk (t • D)
  set N : Fin m → ℕ := fun k => t * D (.e k)
  let Ix := (k : Fin m) → Fin (N k + 1)
  let ev : Ix → (Fin m → ℕ) := fun e k => (e k : ℕ)
  let L : Ix → MvPolynomial (Var d₀ d₁ m) ℂ := fun e =>
    ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ^ (N k - ev e k)
  have hLmem : ∀ e (P : MvPolynomial (Var d₀ d₁ m) ℂ), P ∈ F →
      L e * weightedHomogeneousComponent wtV (ev e) P ∈ F := by
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
    ((LinearMap.mulLeft ℂ (L e) ∘ₗ (weightedHomogeneousComponent wtV (ev e)).restrictScalars ℂ) ∘ₗ
      F.subtype).codRestrict F fun P => hLmem e P P.2
  let Φ : F →ₗ[ℂ] (Ix → F ⧸ Nsub (K := ℂ) blk D I t) :=
    LinearMap.pi fun e => (Nsub (K := ℂ) blk D I t).mkQ ∘ₗ φ e
  have hker : LinearMap.ker Φ ≤ Nsub (K := ℂ) blk D (vanish E) t := by
    intro P hP
    have hcomp : ∀ e, weightedHomogeneousComponent wtV (ev e) (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
        vanish E := by
      intro e
      have h0 := congrFun (LinearMap.mem_ker.mp hP) e
      simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hs : L e * weightedHomogeneousComponent wtV (ev e) (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
          I := h0
      have hhom : IsWeightedHomogeneous wtV (L e * weightedHomogeneousComponent wtV (ev e)
          (P : MvPolynomial (Var d₀ d₁ m) ℂ)) (∑ k, (N k - ev e k) • Pi.single k 1 + ev e) :=
        (IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_lsl α k).pow _).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      have hv := hI _ _ hhom hs
      have hL : L e ∉ vanish E := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
        exact hℓ k (hp.mem_of_pow_mem _ hk)
      exact (hp.mem_or_mem hv).resolve_left hL
    have hsum : (P : MvPolynomial (Var d₀ d₁ m) ℂ) =
        ∑ e : Ix, weightedHomogeneousComponent wtV (ev e) P := by
      ext s
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      by_cases hs : (P : MvPolynomial (Var d₀ d₁ m) ℂ).coeff s = 0
      · simp [hs]
      have hsS : s ∈ StrongSix.M2.S blk (t • D) := by
        have h' : (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ FLE ℂ blk (t • D) := P.2
        rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at h'
        exact h' (MvPolynomial.mem_support_iff.mpr hs)
      have hb : ∀ k, Finsupp.weight wtV s k < N k + 1 := fun k => by
        have := hsS (.e k)
        rw [bdeg_e_eq_weight] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact Nat.lt_succ_of_le this
      let e₀ : Ix := fun k => ⟨Finsupp.weight wtV s k, hb k⟩
      rw [Finset.sum_eq_single e₀ (fun e _ he => ite_eq_right_iff.mpr fun hw =>
          absurd (funext fun k => Fin.ext (congrFun hw k).symm) he) (by simp)]
      simp only [↓reduceIte]
    change (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ vanish E
    rw [hsum]
    exact Ideal.sum_mem _ fun e _ => hcomp e
  have h := finrank_quotient_le_of_ker_le Φ hker
  rw [← hfun_eq_finrank_quotient, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    ← hfun_eq_finrank_quotient] at h
  have hcard : Fintype.card Ix = ∏ k, (t * D (.e k) + 1) := by
    simp [Ix, Fintype.card_pi, N]
  rw [← hcard]
  calc hfun blk D ℂ (vanish E) t ≤ Fintype.card Ix • hfun blk D ℂ I t := h
    _ = _ := smul_eq_mul _ _

/-- **Slicing loses at most `∏ (t D_k + 1)`**: for `vanish E` prime with all `ℓ_k ∉ vanish E`,
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(sl α (vanish E); t)`. -/
theorem hfun_le_sl (α : Fin m → ℂ) {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E) (D : Blk m → ℕ) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤
      (∏ k, (t * D (.e k) + 1)) * hfun blk D ℂ (sl α (vanish E)) t :=
  hfun_le_of_hom α hp hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_sl α hp hℓ hQ hs) D t

end LSG.MEV
