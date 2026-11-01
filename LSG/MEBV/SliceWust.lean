/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Comp
import LSG.ME.WustAlg

/-!
# The sliced Wüstholz lemma: algebraic part (M2.5, β; copy of `LSG.MEB.SliceWust`)

The `VBlock` copy of `LSG.MEB.SliceWust`. **One change**: the order-defining derivations `Dw` may satisfy
`[Eul_k, Dw] = cE • Dw` for any constant `cE : ℕ` (`Eul_mem_VOg`, `wustholz_sl_of_data`); MEB has `cE = 1`, the chart
derivations `X_c² ∂` of `LSG.MEBV.Deriv` have `cE = 2`. Only the induction step of `Eul_mem_VOg` sees `cE`.

Generic algebra for the sliced Wüstholz lemma on the multi-cone of `G`, for arbitrary derivations. The generic
lemmas `wustholzM'`, `DL_glued_mem`, `VOg` are imported from `LSG.ME.WustAlg`/`LSG.ME.Order` (generic sections,
STAGE_A4 §1.3).

* `Lsl α = (ℓ_k − 1)_k`, `lpow`, `exists_hom_sl` (homogenisation modulo `L`).
* `hom_mem_vanish_biUnion_of_mem_sl`; **`nzd_sl`**: a multihomogeneous `M ∉ I(C_a)` is a non-zero-divisor modulo
  `sl α I(⋃ C_a)`.
* `Eul k` (Euler derivation of block `k`), `Eul_apply`, `Eul_mem_vanish`, `Eul_mem_VOg`.
* `Dsl α D = D − Σ_k D(ℓ_k) • Eul_k`, `Dsl_mem_Lsl`, `DL_mem_Lsl`.
* **`wustholz_sl_of_data`**: `(k+1)^ℓ · H(sl α J; t) ≤ H(sl α A; t + S₀ c₀)` from glued transversal data.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun DL DL_cons)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The ideal `L = (ℓ_k − 1)` and homogenisation -/

/-- The ideal `(ℓ_k − 1)_k`. -/
noncomputable def Lsl (α : Alpha B) : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Ideal.span (Set.range fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1)

theorem sl_eq (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    sl α I = I ⊔ Lsl α := rfl

theorem Lsl_le_sl (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    Lsl α ≤ sl α I := le_sup_right

theorem le_sl (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) : I ≤ sl α I :=
  le_sup_left

theorem sl_mono (α : Alpha B) {I I' : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (h : I ≤ I') :
    sl α I ≤ sl α I' := sup_le_sup_right h _

theorem lsl_sub_one_mem (α : Alpha B) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k - 1 ∈ Lsl α := Ideal.subset_span ⟨k, rfl⟩

/-- `ℓ^c = ∏ ℓ_k^{c_k}`. -/
noncomputable def lpow (α : Alpha B) (c : Fin m → ℕ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∏ k, lsl α k ^ c k

theorem isWH_lpow (α : Alpha B) (c : Fin m → ℕ) :
    IsWeightedHomogeneous wV (lpow (d₀ := d₀) (d₁ := d₁) α c) c := by
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wV) Finset.univ
    (fun k => lsl (d₀ := d₀) (d₁ := d₁) α k ^ c k) (fun k => c k • Pi.single k 1)
    (fun k _ => (isWeightedHomogeneous_lsl α k).pow (c k))
  unfold lpow
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem lpow_sub_one_mem (α : Alpha B) (c : Fin m → ℕ) :
    lpow (d₀ := d₀) (d₁ := d₁) α c - 1 ∈ Lsl α := by
  rw [← Ideal.Quotient.eq]
  have h : ∀ k, Ideal.Quotient.mk (Lsl (d₀ := d₀) (d₁ := d₁) α) (lsl α k) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]; exact lsl_sub_one_mem α k
  simp [lpow, map_prod, map_pow, h]

theorem lpow_notMem {p : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (hp : p.IsPrime) (α : Alpha B)
    (hℓ : ∀ k, lsl α k ∉ p) (c : Fin m → ℕ) : lpow α c ∉ p := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
  exact hℓ k (hp.mem_of_pow_mem _ hk)

/-- **Homogenisation modulo `L`.** -/
theorem exists_hom_sl (α : Alpha B) (x : MvPolynomial (Var d₀ d₁ B) ℂ) :
    ∃ (N : Fin m → ℕ) (xh : MvPolynomial (Var d₀ d₁ B) ℂ),
      IsWeightedHomogeneous wV xh N ∧ x - xh ∈ Lsl α := by
  classical
  obtain ⟨s, hs⟩ := sum_multiComp x
  set N : Fin m → ℕ := ∑ e ∈ s, e
  have hle : ∀ e ∈ s, e ≤ N := fun e he =>
    Finset.single_le_sum (f := fun e => e) (fun _ _ => zero_le) he
  refine ⟨N, ∑ e ∈ s, lpow α (N - e) * weightedHomogeneousComponent wV e x, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWH_lpow (d₀ := d₀) (d₁ := d₁) α (N - e)).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := wV) e x)
    rwa [tsub_add_cancel_of_le (hle e he)] at this
  · have e0 : x - ∑ e ∈ s, lpow α (N - e) * weightedHomogeneousComponent wV e x =
        ∑ e ∈ s, (weightedHomogeneousComponent wV e x -
          lpow α (N - e) * weightedHomogeneousComponent wV e x) := by
      rw [Finset.sum_sub_distrib]; nth_rewrite 1 [hs]; rfl
    rw [e0]
    refine Ideal.sum_mem _ fun e _ => ?_
    have : weightedHomogeneousComponent wV e x -
        lpow α (N - e) * weightedHomogeneousComponent wV e x =
          -((lpow α (N - e) - 1) * weightedHomogeneousComponent wV e x) := by ring
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ (lpow_sub_one_mem α _))

/-! ### Non-zero-divisors modulo a slice -/

section Nzd

variable (α : Alpha B) {ι : Type*} (s : Finset ι) (C : ι → Set (GPt d₀ d₁ B))

theorem vanish_biUnion_le {a : ι} (ha : a ∈ s) : vanish (⋃ b ∈ s, C b) ≤ vanish (C a) :=
  fun _ hP => (mem_vanish_biUnion s C).mp hP a ha

/-- A multihomogeneous element of `sl α I(⋃ C_a)` lies in `I(⋃ C_a)`. -/
theorem hom_mem_vanish_biUnion_of_mem_sl (hp : ∀ a ∈ s, (vanish (C a)).IsPrime)
    (hℓ : ∀ a ∈ s, ∀ k, lsl α k ∉ vanish (C a)) {Q : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wV Q d)
    (hQs : Q ∈ sl α (vanish (⋃ a ∈ s, C a))) : Q ∈ vanish (⋃ a ∈ s, C a) :=
  (mem_vanish_biUnion s C).mpr fun a ha =>
    hom_mem_vanish_of_mem_sl α (hp a ha) (hℓ a ha) hQ (sl_mono α (vanish_biUnion_le s C ha) hQs)

/-- **Multihomogeneous non-zero-divisors modulo a slice.** -/
theorem nzd_sl (hp : ∀ a ∈ s, (vanish (C a)).IsPrime)
    (hℓ : ∀ a ∈ s, ∀ k, lsl α k ∉ vanish (C a)) {M : MvPolynomial (Var d₀ d₁ B) ℂ}
    {μ : Fin m → ℕ} (hM : IsWeightedHomogeneous wV M μ) (hMn : ∀ a ∈ s, M ∉ vanish (C a))
    (x : MvPolynomial (Var d₀ d₁ B) ℂ) (hx : M * x ∈ sl α (vanish (⋃ a ∈ s, C a))) :
    x ∈ sl α (vanish (⋃ a ∈ s, C a)) := by
  obtain ⟨N, xh, hxh, hdiff⟩ := exists_hom_sl α x
  have hL := Lsl_le_sl α (vanish (⋃ a ∈ s, C a))
  have h1 : M * xh ∈ sl α (vanish (⋃ a ∈ s, C a)) := by
    have e : M * xh = M * x - M * (x - xh) := by ring
    rw [e]; exact sub_mem hx (hL (Ideal.mul_mem_left _ _ hdiff))
  have h2 := hom_mem_vanish_biUnion_of_mem_sl α s C hp hℓ (hM.mul hxh) h1
  have h3 : xh ∈ vanish (⋃ a ∈ s, C a) := by
    rw [mem_vanish_biUnion] at h2 ⊢
    exact fun a ha => ((hp a ha).mem_or_mem (h2 a ha)).resolve_left (hMn a ha)
  have e : x = xh + (x - xh) := by ring
  rw [e]
  exact add_mem (le_sl α _ h3) (hL hdiff)

end Nzd

/-! ### The Euler derivations -/

/-- The Euler derivation of the `k`-th elliptic block. -/
noncomputable def Eul (k : Fin m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  mkDerivation ℂ fun v => wk k v • X v

@[simp] theorem Eul_X (k : Fin m) (v : Var d₀ d₁ B) :
    Eul (d₀ := d₀) (d₁ := d₁) (B := B) k (X v) = wk k v • X v := mkDerivation_X _ _ _

/-- **Euler's identity.** -/
theorem Eul_apply (k : Fin m) {P : MvPolynomial (Var d₀ d₁ B) ℂ} {n : ℕ}
    (hP : P.IsWeightedHomogeneous (wk k) n) : Eul k P = n • P := by
  rw [Eul, LSG.ME.mkDerivation_eq_sum, ← hP.sum_weight_X_mul_pderiv]
  exact Finset.sum_congr rfl fun v _ => smul_mul_assoc _ _ _

theorem Eul_mem_vanish {E : Set (GPt d₀ d₁ B)} (k : Fin m)
    {x : MvPolynomial (Var d₀ d₁ B) ℂ} (hx : x ∈ vanish E) : Eul k x ∈ vanish E := by
  obtain ⟨s, hs⟩ := sum_multiComp x
  rw [hs, map_sum]
  refine Ideal.sum_mem _ fun e _ => ?_
  rw [Eul_apply k (isHomV_iff_wV.mpr (weightedHomogeneousComponent_isWeightedHomogeneous e x) k)]
  exact nsmul_mem (multiComp_mem_vanish e hx) _

/-- An Euler-type derivation preserves the order ideals `VOg` (`[E, Dv i] = cE • Dv i`, any `cE`). -/
theorem Eul_mem_VOg {R ι : Type*} [CommRing R] [Algebra ℂ R] {Dv : ι → Derivation ℂ R R}
    {Ws : Set ι} {J : Ideal R} (E : Derivation ℂ R R) (hJ : ∀ x ∈ J, E x ∈ J) {cE : ℕ}
    (hc : ∀ i x, E (Dv i x) = Dv i (E x) + cE • Dv i x) :
    ∀ (n : ℕ) (x : R), x ∈ LSG.ME.VOg Dv Ws J n → E x ∈ LSG.ME.VOg Dv Ws J n := by
  intro n
  induction n with
  | zero => intro x hx; rw [LSG.ME.mem_VOg_zero] at hx ⊢; exact hJ x hx
  | succ n ih =>
    intro x hx
    rw [LSG.ME.mem_VOg_succ] at hx ⊢
    refine ⟨hJ x hx.1, fun w hw => ?_⟩
    have e : Dv w (E x) = E (Dv w x) - cE • Dv w x := by rw [hc]; abel
    rw [e]
    exact sub_mem (ih _ (hx.2 w hw)) (nsmul_mem (hx.2 w hw) _)

/-! ### The sliced derivations -/

/-- `D′ = D − Σ_k D(ℓ_k) · Eul_k`. -/
noncomputable def Dsl (α : Alpha B)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  D - ∑ k, D (lsl α k) • Eul k

theorem Dsl_apply (α : Alpha B)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))
    (x : MvPolynomial (Var d₀ d₁ B) ℂ) :
    Dsl α D x = D x - ∑ k, D (lsl α k) * Eul k x := by
  rw [Dsl, Derivation.sub_apply, LSG.ME.derivation_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]

theorem Eul_lsl (α : Alpha B) (k k' : Fin m) :
    Eul k' (lsl (d₀ := d₀) (d₁ := d₁) α k) = (Pi.single k 1 : Fin m → ℕ) k' • lsl α k :=
  Eul_apply k' (isHomV_iff_wV.mpr (isWeightedHomogeneous_lsl α k) k')

theorem Dsl_lsl (α : Alpha B)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)) (k : Fin m) :
    Dsl α D (lsl α k) = -(D (lsl α k) * (lsl α k - 1)) := by
  classical
  rw [Dsl_apply]
  simp only [Eul_lsl]
  rw [Finset.sum_eq_single k (fun b _ hb => by
      rw [Pi.single_eq_of_ne hb, zero_smul, mul_zero]) (by simp),
    Pi.single_eq_same, one_smul]
  ring

/-- A derivation mapping the generators of `span S` into `span S` preserves `span S`. -/
theorem der_mem_span {R : Type*} [CommRing R] [Algebra ℂ R] (D : Derivation ℂ R R) {S : Set R}
    (hS : ∀ s ∈ S, D s ∈ Ideal.span S) {x : R} (hx : x ∈ Ideal.span S) : D x ∈ Ideal.span S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx')

/-- **`D′` preserves `L = (ℓ_k − 1)`.** -/
theorem Dsl_mem_Lsl (α : Alpha B)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))
    {x : MvPolynomial (Var d₀ d₁ B) ℂ} (hx : x ∈ Lsl α) : Dsl α D x ∈ Lsl α := by
  refine der_mem_span (Dsl α D) ?_ hx
  rintro _ ⟨k, rfl⟩
  rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Dsl_lsl]
  exact neg_mem (Ideal.mul_mem_left _ _ (lsl_sub_one_mem α k))

theorem DL_mem_Lsl (α : Alpha B) {κ : Type*}
    (D : κ → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    ∀ (l : List κ) {x : MvPolynomial (Var d₀ d₁ B) ℂ}, x ∈ Lsl α →
      DL (fun i => Dsl α (D i)) l x ∈ Lsl α := by
  intro l
  induction l with
  | nil => intro x hx; simpa using hx
  | cons i l ih => intro x hx; rw [DL_cons]; exact ih (Dsl_mem_Lsl α (D i) hx)

/-! ### The abstract sliced Wüstholz lemma -/

/-- **Sliced Wüstholz lemma from glued data.** `J` is stable under the Euler derivations; the
data `(Dᵢ, Qⱼ, M)` satisfies `Dᵢ Qⱼ ≡ δᵢⱼ M (mod J)`, `Qⱼ ∈ J`, and `M` is a non-zero-divisor
modulo `sl α J`; the `Dᵢ` lower the order `LSG.ME.VOg Dw Ws J` by one and the `Dw` satisfy
`[Eul_k, Dw] = cE • Dw`. Then for `A ≤ LSG.ME.VOg Dw Ws J S₀` and `ℓ k ≤ S₀`:
`(k+1)^ℓ · H(sl α J; t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_sl_of_data (α : Alpha B) (D : Blk m → ℕ) {ℓ : ℕ}
    (Dv : Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))
    {J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (hJE : ∀ k, ∀ x ∈ J, Eul k x ∈ J)
    {Q : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ} {M : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hQ : ∀ j, Q j ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (hM : ∀ x, M * x ∈ sl α J → x ∈ sl α J) {c0 : ℕ} (hQdeg : ∀ j, Q j ∈ FLE ℂ blk (c0 • D))
    {ι' : Type*}
    {Dw : ι' → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)}
    {Ws : Set ι'} {cE : ℕ} (hcomm : ∀ k i x, Eul k (Dw i x) = Dw i (Eul k x) + cE • Dw i x)
    (hDv : ∀ i (n : ℕ) x, x ∈ LSG.ME.VOg Dw Ws J (n + 1) → Dv i x ∈ LSG.ME.VOg Dw Ws J n)
    {S0 k : ℕ} (hk : ℓ * k ≤ S0) {A : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)}
    (hA : A ≤ LSG.ME.VOg Dw Ws J S0) (t : ℕ) :
    (k + 1) ^ ℓ * hfun blk D ℂ (sl α J) t ≤ hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  classical
  set D' := fun i => Dsl α (Dv i)
  have hEV : ∀ k' (n : ℕ) x, x ∈ LSG.ME.VOg Dw Ws J n → Eul k' x ∈ LSG.ME.VOg Dw Ws J n :=
    fun k' => Eul_mem_VOg (Eul k') (hJE k') (hcomm k')
  have hD' : ∀ i (n : ℕ) x, x ∈ LSG.ME.VOg Dw Ws J (n + 1) → D' i x ∈ LSG.ME.VOg Dw Ws J n := by
    intro i n x hx
    simp only [D', Dsl_apply]
    refine sub_mem (hDv i n x hx) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ ?_)
    exact LSG.ME.VOg_succ_le n (hEV k' (n + 1) x hx)
  have hJsl := le_sl α J
  refine LSG.ME.wustholzM' blk D D' (fun j => hJsl (hQ j)) (fun i j => hJsl ?_) hM hQdeg hk ?_ t
  · have e : D' i (Q j) - (if i = j then M else 0) =
        (Dv i (Q j) - (if i = j then M else 0)) - ∑ k', Dv i (lsl α k') * Eul k' (Q j) := by
      simp only [D', Dsl_apply]; ring
    rw [e]
    exact sub_mem (hδ i j) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ (hJE k' _ (hQ j)))
  · intro x hx l hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact add_mem (hJsl (LSG.ME.DL_glued_mem D' hD' l (hA hy) hl)) (Lsl_le_sl α J (DL_mem_Lsl α Dv l hz))

end LSG.MEBV
