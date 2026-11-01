import Mathlib
import LSG.ME.PhOp

/-!
# From formal order to derivation words (STAGE2 §10)

The bridge needed for Wüstholz's lemma: **formal order `> k` along `W` at `p` implies that all
words of length `≤ k` in the homogenized derivations `Dh_w`, `w ∈ W` (v1, `LSG.ME.Order`), vanish
at every cone representative of `p`** (`vanCan_of_ordGt`; homogeneous `Q`), and conversely
(`ordGt_of_vanCan`).

* `taylor_fexp`: `n! [zⁿ] Q(p + exp(z w)) = (Dh_w^n Q)(p)` (canonical charts, normalized
  representative).
* `Dh_add`, `Dh_smul`: `Dh` is linear in the direction.
* **`comm_Dh`** (commutator identity; exact, not only modulo `I_G`):
  `Lc · [Dh_a, Dh_b] = Dh_a(Lc) · Dh_b − Dh_b(Lc) · Dh_a` (charts in `{V, W}`): the invariant
  derivations commute.
* `perm_eval`: given vanishing of all shorter words, the value of a word at `p` is invariant
  under permutations of its letters.
* `polar`: polarization — vanishing of the pure powers `Dh_w^{n+1}` for all `w ∈ W` gives vanishing
  of all words of length `n + 1` (characteristic `0`).
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (DL DL_cons)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Linearity in the direction -/

theorem dvalh_add (ch : Fin m → Fin 3) (w w' : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    dvalh g₂ g₃ ch (w + w') v = dvalh g₂ g₃ ch w v + dvalh g₂ g₃ ch w' v := by
  cases v <;> simp [dvalh, dval, mult] <;> ring

theorem dvalh_smul (ch : Fin m → Fin 3) (a : K) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    dvalh g₂ g₃ ch (a • w) v = C a * dvalh g₂ g₃ ch w v := by
  cases v <;> simp [dvalh, dval, mult, map_mul] <;> ring

theorem Dh_add (ch : Fin m → Fin 3) (w w' : LieE K d₀ d₁ m) :
    Dh g₂ g₃ ch (w + w') = Dh g₂ g₃ ch w + Dh g₂ g₃ ch w' :=
  MvPolynomial.derivation_ext fun v => by simp [dvalh_add]

theorem Dh_smul (ch : Fin m → Fin 3) (a : K) (w : LieE K d₀ d₁ m) :
    Dh g₂ g₃ ch (a • w) = a • Dh g₂ g₃ ch w :=
  MvPolynomial.derivation_ext fun v => by simp [dvalh_smul, smul_eq_C_mul]

theorem Dh_sum {ι : Type*} (s : Finset ι) (a : ι → K) (f : ι → LieE K d₀ d₁ m) (ch : Fin m → Fin 3)
    (x : MvPolynomial (Var d₀ d₁ m) K) :
    Dh g₂ g₃ ch (∑ i ∈ s, a i • f i) x = ∑ i ∈ s, a i • Dh g₂ g₃ ch (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : Dh g₂ g₃ ch (0 : LieE K d₀ d₁ m) = 0 := by
      have := Dh_smul (g₂ := g₂) (g₃ := g₃) ch (0 : K) (0 : LieE K d₀ d₁ m)
      rwa [zero_smul, zero_smul] at this
    rw [this]; rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Dh_add, Derivation.add_apply, ih, Dh_smul,
      Derivation.smul_apply]

/-! ### The commutator identity -/

section Comm

variable (ch : Fin m → Fin 3) (a a' : LieE K d₀ d₁ m) (k : Fin m)

/-- Polynomials `φ` with `a'ₖ · Dh_a φ = aₖ · Dh_{a'} φ` (e.g. those in the `k`-th elliptic
block). -/
noncomputable def blkSub : Subalgebra K (MvPolynomial (Var d₀ d₁ m) K) where
  carrier := {φ | C (a'.2.2 k) * Dh g₂ g₃ ch a φ = C (a.2.2 k) * Dh g₂ g₃ ch a' φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz, smul_eq_mul] at hx hy ⊢
    linear_combination x * hy + y * hx
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    linear_combination hx + hy
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap, mul_zero]

theorem X_mem_blkSub (i : Fin 3) : X (.e k i) ∈ blkSub (g₂ := g₂) (g₃ := g₃) ch a a' k := by
  change C (a'.2.2 k) * Dh g₂ g₃ ch a (X (.e k i)) = C (a.2.2 k) * Dh g₂ g₃ ch a' (X (.e k i))
  simp only [Dh_X, dvalh, mult, dval]
  ring

theorem aeval_mem_blkSub (f : MvPolynomial (Fin 3) K) :
    aeval (fun i => (X (.e k i) : MvPolynomial (Var d₀ d₁ m) K)) f ∈
      blkSub (g₂ := g₂) (g₃ := g₃) ch a a' k := by
  induction f using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hp (X_mem_blkSub ch a a' k i)

theorem chartPoly_mem_blkSub [CharZero K] (b c : Fin 3) :
    chartPoly g₂ g₃ d₀ d₁ b k c ∈ blkSub (g₂ := g₂) (g₃ := g₃) ch a a' k := by
  rw [chartPoly_eq_half (two_ne_zero' K)]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (1 / 2 : K)) ?_
  have := aeval_mem_blkSub (g₂ := g₂) (g₃ := g₃) ch a a' k
    (c2 b (C (g₂ k)) (C (g₃ k)) (fun i => X i) c)
  rw [← AlgHom.coe_toRingHom, c2_map] at this
  convert this using 2
  · simp
  · simp
  · funext i; simp [bvars]

theorem comm_X [CharZero K] (hch : ∀ k, ch k ≠ 0) (v : Var d₀ d₁ m) :
    Lc d₀ d₁ ch * (Dh g₂ g₃ ch a (Dh g₂ g₃ ch a' (X v)) - Dh g₂ g₃ ch a' (Dh g₂ g₃ ch a (X v))) =
      Dh g₂ g₃ ch a (Lc d₀ d₁ ch) * Dh g₂ g₃ ch a' (X v) -
        Dh g₂ g₃ ch a' (Lc d₀ d₁ ch) * Dh g₂ g₃ ch a (X v) := by
  cases v with
  | x i =>
    simp only [Dh_X, dvalh, mult, dval, Derivation.leibniz, Dh_C, smul_eq_mul, mul_zero]
    ring
  | y j =>
    simp only [Dh_X, dvalh, mult, dval, Derivation.leibniz, Dh_C, smul_eq_mul, mul_zero]
    ring
  | z j =>
    simp only [Dh_X, dvalh, mult, dval, Derivation.leibniz, Dh_C, smul_eq_mul, mul_zero,
      map_neg]
    ring
  | e k c =>
    have hblk := chartPoly_mem_blkSub (g₂ := g₂) (g₃ := g₃) ch a a' k (ch k) c
    change C (a'.2.2 k) * Dh g₂ g₃ ch a _ = C (a.2.2 k) * Dh g₂ g₃ ch a' _ at hblk
    have hL := Lc_eq (K := K) (d₀ := d₀) (d₁ := d₁) ch k
    have hz : ∀ b : LieE K d₀ d₁ m, Dh g₂ g₃ ch b (X (.e k (ch k))) = 0 := fun b => by
      simp [dvalh, mult, dval, chartPoly_self (hch k)]
    have hD : ∀ b : LieE K d₀ d₁ m, Dh g₂ g₃ ch b (Lc d₀ d₁ ch) =
        X (.e k (ch k)) * Dh g₂ g₃ ch b (Lo d₀ d₁ ch k) := fun b => by
      rw [hL, Derivation.leibniz, hz, smul_zero, add_zero, smul_eq_mul]
    simp only [Dh_X, dvalh, mult, dval, Derivation.leibniz, Dh_C, smul_eq_mul, mul_zero]
    rw [hD a, hD a', hL]
    linear_combination (X (.e k (ch k)) * Lo d₀ d₁ ch k * Lo d₀ d₁ ch k) * hblk

/-- **The commutator identity** `Lc · [Dh_a, Dh_{a'}] = Dh_a(Lc) Dh_{a'} − Dh_{a'}(Lc) Dh_a`. -/
theorem comm_Dh [CharZero K] (hch : ∀ k, ch k ≠ 0) (x : MvPolynomial (Var d₀ d₁ m) K) :
    Lc d₀ d₁ ch * (Dh g₂ g₃ ch a (Dh g₂ g₃ ch a' x) - Dh g₂ g₃ ch a' (Dh g₂ g₃ ch a x)) =
      Dh g₂ g₃ ch a (Lc d₀ d₁ ch) * Dh g₂ g₃ ch a' x -
        Dh g₂ g₃ ch a' (Lc d₀ d₁ ch) * Dh g₂ g₃ ch a x := by
  induction x using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add]; linear_combination hp + hq
  | mul_X p v hp =>
    have hv := comm_X (g₂ := g₂) (g₃ := g₃) ch a a' hch v
    simp only [Derivation.leibniz, smul_eq_mul, map_add]
    linear_combination X v * hp + p * hv

end Comm

/-! ### Saturation, permutations, polarization -/

section Sat

variable {R ι : Type*} [CommRing R] [Algebra K R] {Dv : ι → Derivation K R R} {W : Set ι}
  {J : Ideal R}

/-- **Saturation** for `VOg`: a factor that is a nonzerodivisor modulo `J` can be cancelled. -/
theorem satg {u : R} (hu : ∀ y, u * y ∈ J → y ∈ J) :
    ∀ (n : ℕ) (y : R), u * y ∈ VOg Dv W J n → y ∈ VOg Dv W J n := by
  intro n
  induction n with
  | zero => intro y hy; rw [mem_VOg_zero] at hy ⊢; exact hu y hy
  | succ n ih =>
    intro y hy
    have hy' : y ∈ VOg Dv W J n := ih y (VOg_succ_le n hy)
    rw [mem_VOg_succ] at hy ⊢
    refine ⟨VOg_le n hy', fun w hw => ih _ ?_⟩
    have h1 := hy.2 w hw
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := Ideal.mul_mem_left _ (Dv w u) hy'
    have := Ideal.sub_mem _ h1 h2
    rwa [mul_comm y, add_sub_cancel_right] at this

end Sat

section Polar

variable [CharZero K] (ch : Fin m → Fin 3) (hch : ∀ k, ch k ≠ 0) (W : Submodule K (LieE K d₀ d₁ m))
  {x₀ : Var d₀ d₁ m → K} (hLc : eval x₀ (Lc d₀ d₁ ch) ≠ 0)

include hch hLc in
/-- **Permutation invariance**: if all words of length `≤ n` kill `Q` at `x₀`, the value at `x₀`
of a word of length `n + 1` does not depend on the order of its letters. -/
theorem perm_eval {l l' : List (LieE K d₀ d₁ m)} (hp : l.Perm l') :
    ∀ (n : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) K), l.length = n + 1 → (∀ w ∈ l, w ∈ W) →
      Q ∈ VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval x₀)) n →
      eval x₀ (DL (Dh g₂ g₃ ch) l Q) = eval x₀ (DL (Dh g₂ g₃ ch) l' Q) := by
  induction hp with
  | nil => intro n Q h; simp at h
  | @cons x l₁ l₂ hp ih =>
    intro n Q hlen hW hQ
    rcases l₁ with _ | ⟨y, l₁'⟩
    · rw [List.Perm.nil_eq hp]
    · simp only [DL_cons]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hlen; omega⟩
      exact ih n' _ (by simpa using hlen) (fun w hw => hW w (List.mem_cons_of_mem _ hw))
        ((mem_VOg_succ.mp hQ).2 x (hW x List.mem_cons_self))
  | swap x y l =>
    intro n Q hlen hW hQ
    simp only [DL_cons]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hlen; omega⟩
    have hx : x ∈ W := hW x (by simp)
    have hy : y ∈ W := hW y (by simp)
    have hY : Dh g₂ g₃ ch x (Dh g₂ g₃ ch y Q) - Dh g₂ g₃ ch y (Dh g₂ g₃ ch x Q) ∈
        VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval x₀)) n' := by
      refine satg (u := Lc d₀ d₁ ch) (fun z hz => ?_) n' _ ?_
      · rw [RingHom.mem_ker, map_mul] at hz; rw [RingHom.mem_ker]
        exact (mul_eq_zero.mp hz).resolve_left hLc
      · rw [comm_Dh ch x y hch]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ((mem_VOg_succ.mp hQ).2 y hy))
          (Ideal.mul_mem_left _ _ ((mem_VOg_succ.mp hQ).2 x hx))
    have hl : l.length ≤ n' := by simp at hlen; omega
    have := hY l (fun w hw => hW w (by simp [hw])) hl
    rw [map_sub, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  | trans h₁ h₂ ih₁ ih₂ =>
    intro n Q hlen hW hQ
    rw [ih₁ n Q hlen hW hQ]
    exact ih₂ n Q (h₁.length_eq ▸ hlen) (fun w hw => hW w (h₁.symm.subset hw)) hQ

omit [CharZero K] in
/-- Expansion of a pure power of `Dh_{Σ aᵢ fᵢ}` into words. -/
theorem DL_replicate_sum {M : ℕ} (a : Fin M → K) (f : Fin M → LieE K d₀ d₁ m) :
    ∀ (N : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) K),
      DL (Dh g₂ g₃ ch) (List.replicate N (∑ i, a i • f i)) Q =
        ∑ σ : Fin N → Fin M, (∏ s, a (σ s)) • DL (Dh g₂ g₃ ch) (List.ofFn (f ∘ σ)) Q
  | 0, Q => by simp
  | N + 1, Q => by
    rw [List.replicate_succ, DL_cons, Dh_sum, map_sum]
    simp_rw [map_smul, DL_replicate_sum a f N, Finset.smul_sum, smul_smul]
    rw [← (Fin.consEquiv (fun _ => Fin M)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, Function.comp_apply, DL_cons]
    rfl

omit [CharZero K] in
theorem prod_X_eq_monomial {N : ℕ} (σ : Fin N → Fin N) :
    (∏ s, X (σ s) : MvPolynomial (Fin N) K) = monomial (∑ s, Finsupp.single (σ s) 1) 1 := by
  rw [monomial_sum_one]; rfl

theorem sum_single_eq_iff {N : ℕ} (σ : Fin N → Fin N) :
    (∑ s, Finsupp.single (σ s) 1 : Fin N →₀ ℕ) = ∑ s, Finsupp.single s 1 ↔
      Function.Bijective σ := by
  classical
  constructor
  · intro h
    refine Finite.surjective_iff_bijective.mp fun i => ?_
    have := congrArg (fun e : Fin N →₀ ℕ => e i) h
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at this
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => 1)] at this
    simp only [Finset.mem_univ, ite_true] at this
    by_contra hne
    push Not at hne
    rw [Finset.sum_eq_zero fun s _ => ite_eq_right_iff.mpr fun h => absurd h (hne s)] at this
    exact zero_ne_one this
  · intro h
    exact Equiv.sum_comp (Equiv.ofBijective σ h) fun s => (Finsupp.single s 1 : Fin N →₀ ℕ)

include hch hLc in
/-- **Polarization**: if all words of length `≤ n` kill `Q` at `x₀` and all pure powers
`Dh_w^{n+1}`, `w ∈ W`, do too, then all words of length `n + 1` do. -/
theorem polar_core (n : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) K}
    (hQ : Q ∈ VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval x₀)) n)
    (hpow : ∀ w ∈ W, eval x₀ (DL (Dh g₂ g₃ ch) (List.replicate (n + 1) w) Q) = 0)
    (f : Fin (n + 1) → LieE K d₀ d₁ m) (hf : ∀ i, f i ∈ W) :
    eval x₀ (DL (Dh g₂ g₃ ch) (List.ofFn f) Q) = 0 := by
  classical
  set c : (Fin (n + 1) → Fin (n + 1)) → K :=
    fun σ => eval x₀ (DL (Dh g₂ g₃ ch) (List.ofFn (f ∘ σ)) Q)
    with hc
  set Φ : MvPolynomial (Fin (n + 1)) K := ∑ σ : Fin (n + 1) → Fin (n + 1), C (c σ) * ∏ s, X (σ s)
  have hΦ : Φ = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [map_zero]
    have h := hpow (∑ i, a i • f i) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i))
    rw [DL_replicate_sum, map_sum] at h
    simp only [smul_eval] at h
    simp only [Φ, map_sum, map_mul, map_prod, eval_X, eval_C]
    rw [← h]
    exact Finset.sum_congr rfl fun σ _ => mul_comm _ _
  have hcoef := congrArg (fun p : MvPolynomial (Fin (n + 1)) K => p.coeff (∑ s, Finsupp.single s 1))
    hΦ
  simp only [Φ, coeff_sum, coeff_C_mul, prod_X_eq_monomial, coeff_monomial, sum_single_eq_iff,
    mul_ite, mul_one, mul_zero] at hcoef
  rw [show (0 : MvPolynomial (Fin (n + 1)) K).coeff (∑ s, Finsupp.single s 1) = 0 by simp] at hcoef
  have hperm : ∀ σ : Fin (n + 1) → Fin (n + 1), Function.Bijective σ → c σ = c id := by
    intro σ hσ
    have hp := Equiv.Perm.ofFn_comp_perm (Equiv.ofBijective σ hσ) f
    exact perm_eval ch hch W hLc hp n Q (by simp) (fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw; exact hf _) hQ
  have hsw : ∀ σ : Fin (n + 1) → Fin (n + 1),
      (if Function.Bijective σ then c σ else 0) = if Function.Bijective σ then c id else 0 :=
    fun σ => by split_ifs with h
                · exact hperm σ h
                · rfl
  simp_rw [hsw] at hcoef
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hcoef
  have hcard : ((Finset.univ.filter fun σ : Fin (n + 1) → Fin (n + 1) => Function.Bijective σ).card
      : K) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨id, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.bijective_id⟩⟩
  have := (mul_eq_zero.mp hcoef).resolve_left hcard
  simpa [c] using this

include hch hLc in
theorem polar (n : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) K}
    (hQ : Q ∈ VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval x₀)) n)
    (hpow : ∀ w ∈ W, eval x₀ (DL (Dh g₂ g₃ ch) (List.replicate (n + 1) w) Q) = 0) :
    Q ∈ VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval x₀)) (n + 1) := by
  intro l hlW hl
  rcases Nat.lt_or_ge l.length (n + 1) with h | h
  · exact hQ l hlW (by omega)
  have hlen : l.length = n + 1 := by omega
  have hl' : List.ofFn (fun i : Fin (n + 1) => l[i.1]'(by omega)) = l := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    rw [List.getElem_ofFn]
  rw [RingHom.mem_ker, ← hl']
  exact polar_core ch hch W hLc n hQ hpow _ fun i => hlW _ (List.getElem_mem _)

end Polar

/-! ### The bridge -/

section Bridge

variable [CharZero K]

/-- Taylor coefficients of `Q(p + exp(z w))`. -/
theorem taylor_fexp (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (n : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) K) :
    (n.factorial : K) * PowerSeries.coeff n (aeval (fexp g₂ g₃ p w) Q) =
      eval (coords p 1) (DL (Dh g₂ g₃ (chartAt p)) (List.replicate n w) Q) := by
  rw [taylor (fexp_isNFlow p w)]
  simp only [fexp_const]
  rfl

omit [CharZero K] in
theorem eval_coords_Lc (p : GPt K d₀ d₁ g₂ g₃) :
    eval (coords p 1) (Lc d₀ d₁ (chartAt p)) ≠ 0 :=
  eval_Lc_chartAt_ne p 1

/-- Formal order `> k` gives vanishing of all words of length `≤ k` at the normalized
representative. -/
theorem vog_of_ordGt {W : Submodule K (LieE K d₀ d₁ m)} {Q : MvPolynomial (Var d₀ d₁ m) K}
    {p : GPt K d₀ d₁ g₂ g₃} : ∀ {k : ℕ}, OrdGt g₂ g₃ W Q k p →
      Q ∈ VOg (Dh g₂ g₃ (chartAt p)) (W : Set (LieE K d₀ d₁ m)) (RingHom.ker (eval (coords p 1)))
        k
  | 0, h => by
    rw [mem_VOg_zero, RingHom.mem_ker]; exact ordGt_zero_iff.mp h
  | k + 1, h => by
    refine polar (chartAt p) (chartAt_ne p) W (eval_coords_Lc p) k
      (vog_of_ordGt fun w hw i hi => h w hw i (by omega)) fun w hw => ?_
    have := taylor_fexp p w (k + 1) Q
    rw [h w hw (k + 1) le_rfl, mul_zero] at this
    exact this.symm

/-- **The bridge** (Wüstholz's lemma input): formal order `> k` along `W` at `p` implies that every
`Dh`-word of length `≤ k` in `W` (canonical charts) vanishes at every cone representative of `p`
(homogeneous `Q`). -/
theorem vanCan_of_ordGt {W : Submodule K (LieE K d₀ d₁ m)} {Q : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hQ : IsHomE Q d) {k : ℕ} {p : GPt K d₀ d₁ g₂ g₃}
    (h : OrdGt g₂ g₃ W Q k p) : VanCan g₂ g₃ W Q k p := by
  intro l hlW hl
  have h0 := vog_of_ordGt h l hlW hl
  rw [mem_vanish_singleton]
  intro lam
  have hh := isHomE_DL (g₂ := g₂) (g₃ := g₃) hQ (chartAt p) l
  rw [coords_eq_scl p lam]
  change aeval (scl (fun k => (lam k : K)) (coords p 1)) (DL (Dh g₂ g₃ (chartAt p)) l Q) = 0
  rw [aeval_scl hh]
  change _ * eval (coords p 1) _ = 0
  rw [RingHom.mem_ker.mp h0, mul_zero]

/-- The same in all charts. -/
theorem vanAll_of_ordGt {W : Submodule K (LieE K d₀ d₁ m)} {Q : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hQ : IsHomE Q d) {k : ℕ} {p : GPt K d₀ d₁ g₂ g₃}
    (h : OrdGt g₂ g₃ W Q k p) : VanAll g₂ g₃ W Q k p :=
  (vanAll_iff_vanCan two_ne_zero W hQ k p).mpr (vanCan_of_ordGt hQ h)

/-- Conversely, vanishing of the words gives formal order `> k`. -/
theorem ordGt_of_vanCan {W : Submodule K (LieE K d₀ d₁ m)} {Q : MvPolynomial (Var d₀ d₁ m) K}
    {k : ℕ} {p : GPt K d₀ d₁ g₂ g₃} (h : VanCan g₂ g₃ W Q k p) : OrdGt g₂ g₃ W Q k p := by
  intro w hw i hi
  have := taylor_fexp p w i Q
  rw [mem_vanish_singleton.mp (h (List.replicate i w)
    (fun v hv => (List.eq_of_mem_replicate hv) ▸ hw) (by simpa using hi)) 1] at this
  exact (mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))

end Bridge

end LSG.ME
