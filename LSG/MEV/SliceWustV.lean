import Mathlib
import LSG.MEV.WustTrans
import LSG.MEV.SliceCoset
import LSG.ME.SliceWust

/-!
# The sliced Wüstholz lemma for `G̃`: algebraic part (STAGE5_MEV §10)

The analogue of `LSG.ME.SliceWust` for the vector-extension model. For the affine slices
`sl α J = J + (ℓ_k − 1)_k` (`ℓ_k = V_k + α_k W_k`, `LSG.MEV.Slice`), the glued derivations `Dᵢ` are
replaced by `D′ᵢ = Dᵢ − Σ_k Dᵢ(ℓ_k) · Eul_k` (`DslV`), which preserve `L = (ℓ_k − 1)_k`.

* `LslV α`, `lpowV α c = ∏ ℓ_k^{c_k}`, **`exists_hom_slV`** (homogenisation modulo `L`).
* **`nzd_slV`**: a multihomogeneous `M ∉ I(C_a)` (all `a`) is a non-zero-divisor modulo
  `sl α I(⋃ C_a)` (each `I(C_a)` prime, `ℓ_k ∉ I(C_a)`).
* `EulV k` (Euler derivation of the `k`-th `E^♮` block), `EulV_apply`, `EulV_mem_vanish`,
  **`EulV_Dhc`**: `Eul_k ∘ Dhc − Dhc ∘ Eul_k = 2 • Dhc` (`Dhc` raises block degrees by `2`),
  `eul2_mem_VOg`.
* `DslV`, `DslV_mem_Lsl`, `DL_DslV_mem_Lsl`.
* **`wustholz_sl_of_dataV`**: the abstract sliced Wüstholz lemma.
-/

open MvPolynomial LSG.Elliptic Module
open LSG.ME (Blk VOg mem_VOg_zero mem_VOg_succ VOg_succ_le)
open StrongSix.M2 (FLE hfun DL DL_cons)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### The ideal `L = (ℓ_k − 1)` and homogenisation -/

/-- The ideal `(ℓ_k − 1)_k`. -/
def LslV (α : Fin m → ℂ) : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  Ideal.span (Set.range fun k => lsl (d₀ := d₀) (d₁ := d₁) α k - 1)

theorem sl_eqV (α : Fin m → ℂ) (I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    sl α I = I ⊔ LslV α := rfl

theorem LslV_le_sl (α : Fin m → ℂ) (I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    LslV α ≤ sl α I := le_sup_right

theorem lsl_sub_one_memV (α : Fin m → ℂ) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k - 1 ∈ LslV α := Ideal.subset_span ⟨k, rfl⟩

/-- `ℓ^c = ∏ ℓ_k^{c_k}`. -/
def lpowV (α : Fin m → ℂ) (c : Fin m → ℕ) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  ∏ k, lsl α k ^ c k

theorem isWH_lpowV (α : Fin m → ℂ) (c : Fin m → ℕ) :
    IsWeightedHomogeneous wtV (lpowV (d₀ := d₀) (d₁ := d₁) α c) c := by
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wtV) Finset.univ
    (fun k => lsl (d₀ := d₀) (d₁ := d₁) α k ^ c k) (fun k => c k • Pi.single k 1)
    (fun k _ => (isWeightedHomogeneous_lsl α k).pow (c k))
  unfold lpowV
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem lpowV_sub_one_mem (α : Fin m → ℂ) (c : Fin m → ℕ) :
    lpowV (d₀ := d₀) (d₁ := d₁) α c - 1 ∈ LslV α := by
  rw [← Ideal.Quotient.eq]
  have h : ∀ k, Ideal.Quotient.mk (LslV (d₀ := d₀) (d₁ := d₁) α) (lsl α k) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]; exact lsl_sub_one_memV α k
  simp [lpowV, map_prod, map_pow, h]

theorem lpowV_notMem {p : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hp : p.IsPrime) (α : Fin m → ℂ)
    (hℓ : ∀ k, lsl α k ∉ p) (c : Fin m → ℕ) : lpowV α c ∉ p := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
  exact hℓ k (hp.mem_of_pow_mem _ hk)

/-- The multigraded components of `x`, as a finite sum. -/
theorem sum_compV (x : MvPolynomial (Var d₀ d₁ m) ℂ) :
    ∃ s : Finset (Fin m → ℕ), x = ∑ e ∈ s, weightedHomogeneousComponent wtV e x := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := (wtV : Var d₀ d₁ m → Fin m → ℕ)) x
  refine ⟨hfin.toFinset, ?_⟩
  conv_lhs => rw [← finsum_weightedHomogeneousComponent wtV x]
  exact finsum_eq_sum _ hfin

/-- **Homogenisation modulo `L`.** -/
theorem exists_hom_slV (α : Fin m → ℂ) (x : MvPolynomial (Var d₀ d₁ m) ℂ) :
    ∃ (N : Fin m → ℕ) (xh : MvPolynomial (Var d₀ d₁ m) ℂ),
      IsWeightedHomogeneous wtV xh N ∧ x - xh ∈ LslV α := by
  classical
  obtain ⟨s, hs⟩ := sum_compV x
  set N : Fin m → ℕ := ∑ e ∈ s, e
  have hle : ∀ e ∈ s, e ≤ N := fun e he =>
    Finset.single_le_sum (f := fun e => e) (fun _ _ => zero_le) he
  refine ⟨N, ∑ e ∈ s, lpowV α (N - e) * weightedHomogeneousComponent wtV e x, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWH_lpowV (d₀ := d₀) (d₁ := d₁) α (N - e)).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := wtV) e x)
    rwa [tsub_add_cancel_of_le (hle e he)] at this
  · have e0 : x - ∑ e ∈ s, lpowV α (N - e) * weightedHomogeneousComponent wtV e x =
        ∑ e ∈ s, (weightedHomogeneousComponent wtV e x -
          lpowV α (N - e) * weightedHomogeneousComponent wtV e x) := by
      rw [Finset.sum_sub_distrib]; nth_rewrite 1 [hs]; rfl
    rw [e0]
    refine Ideal.sum_mem _ fun e _ => ?_
    have : weightedHomogeneousComponent wtV e x -
        lpowV α (N - e) * weightedHomogeneousComponent wtV e x =
          -((lpowV α (N - e) - 1) * weightedHomogeneousComponent wtV e x) := by ring
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ (lpowV_sub_one_mem α _))

/-! ### Non-zero-divisors modulo a slice -/

section Nzd

variable (α : Fin m → ℂ) {ι : Type*} (s : Finset ι) (C : ι → Set (GPtV d₀ d₁ Ls))

theorem vanish_biUnion_leV {a : ι} (ha : a ∈ s) : vanish (⋃ b ∈ s, C b) ≤ vanish (C a) :=
  fun _ hP => (mem_vanish_biUnionV s C).mp hP a ha

/-- A multihomogeneous element of `sl α I(⋃ C_a)` lies in `I(⋃ C_a)`. -/
theorem hom_mem_vanish_biUnion_of_mem_slV (hp : ∀ a ∈ s, (vanish (C a)).IsPrime)
    (hℓ : ∀ a ∈ s, ∀ k, lsl α k ∉ vanish (C a)) {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wtV Q d)
    (hQs : Q ∈ sl α (vanish (⋃ a ∈ s, C a))) : Q ∈ vanish (⋃ a ∈ s, C a) :=
  (mem_vanish_biUnionV s C).mpr fun a ha =>
    hom_mem_vanish_of_mem_sl α (hp a ha) (hℓ a ha) hQ (sl_mono α (vanish_biUnion_leV s C ha) hQs)

/-- **Multihomogeneous non-zero-divisors modulo a slice.** -/
theorem nzd_slV (hp : ∀ a ∈ s, (vanish (C a)).IsPrime)
    (hℓ : ∀ a ∈ s, ∀ k, lsl α k ∉ vanish (C a)) {M : MvPolynomial (Var d₀ d₁ m) ℂ}
    {μ : Fin m → ℕ} (hM : IsWeightedHomogeneous wtV M μ) (hMn : ∀ a ∈ s, M ∉ vanish (C a))
    (x : MvPolynomial (Var d₀ d₁ m) ℂ) (hx : M * x ∈ sl α (vanish (⋃ a ∈ s, C a))) :
    x ∈ sl α (vanish (⋃ a ∈ s, C a)) := by
  obtain ⟨N, xh, hxh, hdiff⟩ := exists_hom_slV α x
  have hL := LslV_le_sl α (vanish (⋃ a ∈ s, C a))
  have h1 : M * xh ∈ sl α (vanish (⋃ a ∈ s, C a)) := by
    have e : M * xh = M * x - M * (x - xh) := by ring
    rw [e]; exact sub_mem hx (hL (Ideal.mul_mem_left _ _ hdiff))
  have h2 := hom_mem_vanish_biUnion_of_mem_slV α s C hp hℓ (hM.mul hxh) h1
  have h3 : xh ∈ vanish (⋃ a ∈ s, C a) := by
    rw [mem_vanish_biUnionV] at h2 ⊢
    exact fun a ha => ((hp a ha).mem_or_mem (h2 a ha)).resolve_left (hMn a ha)
  have e : x = xh + (x - xh) := by ring
  rw [e]
  exact add_mem (le_sl α _ h3) (hL hdiff)

end Nzd

/-! ### The Euler derivations -/

/-- The Euler derivation of the `k`-th `E^♮` block. -/
def EulV (k : Fin m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  mkDerivation ℂ fun v => wb blk (Blk.e k) v • X v

@[simp] theorem EulV_X (k : Fin m) (v : Var d₀ d₁ m) :
    EulV k (X v) = wb blk (Blk.e k) v • X v := mkDerivation_X _ _ _

/-- **Euler's identity.** -/
theorem EulV_apply (k : Fin m) {P : MvPolynomial (Var d₀ d₁ m) ℂ} {n : ℕ}
    (hP : P.IsWeightedHomogeneous (wb blk (Blk.e k)) n) : EulV k P = n • P := by
  rw [EulV, LSG.ME.mkDerivation_eq_sum, ← hP.sum_weight_X_mul_pderiv]
  exact Finset.sum_congr rfl fun v _ => smul_mul_assoc _ _ _

theorem wEV_eq_wb (k : Fin m) : (wEV k : Var d₀ d₁ m → ℕ) = wb blk (Blk.e k) := by
  funext v
  cases v <;> simp [wEV, wtV, wb, blk, Pi.single_apply, eq_comm]

theorem EulV_mem_vanish {E : Set (GPtV d₀ d₁ Ls)} (k : Fin m)
    {x : MvPolynomial (Var d₀ d₁ m) ℂ} (hx : x ∈ vanish E) : EulV k x ∈ vanish E := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := (wEV k : Var d₀ d₁ m → ℕ)) x
  have hsum : x = ∑ i ∈ hfin.toFinset, weightedHomogeneousComponent (wEV k) i x := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (wEV k) x]
    exact finsum_eq_sum _ hfin
  rw [hsum, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := (wEV k : Var d₀ d₁ m → ℕ))
    i x
  have hh' : (weightedHomogeneousComponent (wEV k) i x).IsWeightedHomogeneous
      (wb blk (Blk.e k)) i := fun {s} hs => by rw [← wEV_eq_wb]; exact hh hs
  rw [EulV_apply k hh']
  exact nsmul_mem (comp_mem_vanish hx k i) _

theorem isWH_wb_X (k : Fin m) (v : Var d₀ d₁ m) :
    (X v : MvPolynomial (Var d₀ d₁ m) ℂ).IsWeightedHomogeneous (wb blk (Blk.e k))
      (wb blk (Blk.e k) v) :=
  isWeightedHomogeneous_X ℂ _ v

/-- **`[Eul_k, Dhc] = 2 • Dhc`.** -/
theorem EulV_Dhc (k : Fin m) (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m)
    (x : MvPolynomial (Var d₀ d₁ m) ℂ) :
    EulV k (Dhc Ls ch w x) = Dhc Ls ch w (EulV k x) + 2 • Dhc Ls ch w x := by
  have h : ⁅(EulV (d₀ := d₀) (d₁ := d₁) k :
      Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) _), Dhc Ls ch w⁆ = 2 • Dhc Ls ch w := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Dhc_X, EulV_apply k (dvh_isWH ch w k v), EulV_X, map_nsmul,
      Dhc_X, Derivation.smul_apply, add_smul, add_sub_cancel_left, Dhc_X]
  have h' := congrArg (fun D : Derivation ℂ _ _ => D x) h
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at h'
  linear_combination h'

/-- An Euler-type derivation with `[E, Dv] = 2 Dv` preserves the order ideals `VOg`. -/
theorem eul2_mem_VOg {R ι : Type*} [CommRing R] [Algebra ℂ R] {Dv : ι → Derivation ℂ R R}
    {Ws : Set ι} {J : Ideal R} (E : Derivation ℂ R R) (hJ : ∀ x ∈ J, E x ∈ J)
    (hc : ∀ i x, E (Dv i x) = Dv i (E x) + 2 • Dv i x) :
    ∀ (n : ℕ) (x : R), x ∈ VOg Dv Ws J n → E x ∈ VOg Dv Ws J n := by
  intro n
  induction n with
  | zero => intro x hx; rw [mem_VOg_zero] at hx ⊢; exact hJ x hx
  | succ n ih =>
    intro x hx
    rw [mem_VOg_succ] at hx ⊢
    refine ⟨hJ x hx.1, fun w hw => ?_⟩
    have e : Dv w (E x) = E (Dv w x) - 2 • Dv w x := by rw [hc]; abel
    rw [e]
    exact sub_mem (ih _ (hx.2 w hw)) (nsmul_mem (hx.2 w hw) 2)

/-! ### The sliced derivations -/

/-- `D′ = D − Σ_k D(ℓ_k) · Eul_k`. -/
def DslV (α : Fin m → ℂ)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  D - ∑ k, D (lsl α k) • EulV k

theorem DslV_apply (α : Fin m → ℂ)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    (x : MvPolynomial (Var d₀ d₁ m) ℂ) :
    DslV α D x = D x - ∑ k, D (lsl α k) * EulV k x := by
  rw [DslV, Derivation.sub_apply, LSG.ME.derivation_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]

theorem EulV_lsl (α : Fin m → ℂ) (k k' : Fin m) :
    EulV k' (lsl (d₀ := d₀) (d₁ := d₁) α k) = (Pi.single k 1 : Fin m → ℕ) k' • lsl α k := by
  refine EulV_apply k' ?_
  have h := isWeightedHomogeneous_lsl (d₀ := d₀) (d₁ := d₁) α k
  intro s hs
  have := congrFun (h hs) k'
  rw [← this, ← wEV_eq_wb, weight_wEV]

theorem DslV_lsl (α : Fin m → ℂ)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ)) (k : Fin m) :
    DslV α D (lsl α k) = -(D (lsl α k) * (lsl α k - 1)) := by
  classical
  rw [DslV_apply]
  simp only [EulV_lsl]
  rw [Finset.sum_eq_single k (fun b _ hb => by
      rw [Pi.single_eq_of_ne hb, zero_smul, mul_zero]) (by simp),
    Pi.single_eq_same, one_smul]
  ring

/-- **`D′` preserves `L = (ℓ_k − 1)`.** -/
theorem DslV_mem_Lsl (α : Fin m → ℂ)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    {x : MvPolynomial (Var d₀ d₁ m) ℂ} (hx : x ∈ LslV α) : DslV α D x ∈ LslV α := by
  refine LSG.ME.der_mem_span (DslV α D) ?_ hx
  rintro _ ⟨k, rfl⟩
  rw [map_sub, Derivation.map_one_eq_zero, sub_zero, DslV_lsl]
  exact neg_mem (Ideal.mul_mem_left _ _ (lsl_sub_one_memV α k))

theorem DL_DslV_mem_Lsl (α : Fin m → ℂ) {κ : Type*}
    (D : κ → Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    ∀ (l : List κ) {x : MvPolynomial (Var d₀ d₁ m) ℂ}, x ∈ LslV α →
      DL (fun i => DslV α (D i)) l x ∈ LslV α := by
  intro l
  induction l with
  | nil => intro x hx; simpa using hx
  | cons i l ih => intro x hx; rw [DL_cons]; exact ih (DslV_mem_Lsl α (D i) hx)

/-! ### The abstract sliced Wüstholz lemma -/

/-- **Sliced Wüstholz lemma from glued data** (vector extensions). `J` is stable under the Euler
derivations; `Dᵢ Qⱼ ≡ δᵢⱼ M (mod J)`, `Qⱼ ∈ J`, `M` a non-zero-divisor modulo `sl α J`; the `Dᵢ`
lower the order `VOg Dw Ws J` by one and `[Eul_k, Dw] = 2 Dw`. Then for `A ≤ VOg Dw Ws J S₀` and
`ℓ k ≤ S₀`: `(k+1)^ℓ · H(sl α J; t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_sl_of_dataV (α : Fin m → ℂ) (D : Blk m → ℕ) {ℓ : ℕ}
    (Dv : Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    {J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hJE : ∀ k, ∀ x ∈ J, EulV k x ∈ J)
    {Q : Fin ℓ → MvPolynomial (Var d₀ d₁ m) ℂ} {M : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : ∀ j, Q j ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (hM : ∀ x, M * x ∈ sl α J → x ∈ sl α J) {c0 : ℕ} (hQdeg : ∀ j, Q j ∈ FLE ℂ blk (c0 • D))
    {ι' : Type*}
    {Dw : ι' → Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ)}
    {Ws : Set ι'} (hcomm : ∀ k i x, EulV k (Dw i x) = Dw i (EulV k x) + 2 • Dw i x)
    (hDv : ∀ i (n : ℕ) x, x ∈ VOg Dw Ws J (n + 1) → Dv i x ∈ VOg Dw Ws J n)
    {S0 k : ℕ} (hk : ℓ * k ≤ S0) {A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)}
    (hA : A ≤ VOg Dw Ws J S0) (t : ℕ) :
    (k + 1) ^ ℓ * hfun blk D ℂ (sl α J) t ≤ hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  classical
  set D' := fun i => DslV α (Dv i)
  have hEV : ∀ k' (n : ℕ) x, x ∈ VOg Dw Ws J n → EulV k' x ∈ VOg Dw Ws J n :=
    fun k' => eul2_mem_VOg (EulV k') (hJE k') (hcomm k')
  have hD' : ∀ i (n : ℕ) x, x ∈ VOg Dw Ws J (n + 1) → D' i x ∈ VOg Dw Ws J n := by
    intro i n x hx
    simp only [D', DslV_apply]
    refine sub_mem (hDv i n x hx) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ ?_)
    exact VOg_succ_le n (hEV k' (n + 1) x hx)
  have hJsl := le_sl α J
  refine LSG.ME.wustholzM' blk D D' (fun j => hJsl (hQ j)) (fun i j => hJsl ?_) hM hQdeg hk ?_ t
  · have e : D' i (Q j) - (if i = j then M else 0) =
        (Dv i (Q j) - (if i = j then M else 0)) - ∑ k', Dv i (lsl α k') * EulV k' (Q j) := by
      simp only [D', DslV_apply]; ring
    rw [e]
    exact sub_mem (hδ i j) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ (hJE k' _ (hQ j)))
  · intro x hx l hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact add_mem (hJsl (LSG.ME.DL_glued_mem D' hD' l (hA hy) hl))
      (LslV_le_sl α J (DL_DslV_mem_Lsl α Dv l hz))

end

end LSG.MEV
