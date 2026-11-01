import Mathlib

/-!
# Independent functions on the cone over `E` and on products (STAGE2 §5, item 6)

* `monoF n p` (`p : Fin (n+1) × Fin (n+1)`): the cone monomials `U^i W^{j−i}` (`i ≤ j`) and
  `V U^j W^{i−1−j}` (`i > j`), of degree `≤ n`; there are `(n+1)²` of them.
* **`monoF_linearIndependent`**: they are linearly independent as functions on the affine cone
  `coneE a b = {λ (u, v, 1) | λ ≠ 0, v² = 4u³ − a u − b}` (`K` algebraically closed, `2 ≠ 0`). At
  `λ(u, v, 1)` the monomial is `λ^d v^ε u^x` with `(d, ε, x)` determined by `p`; separate `ε` with
  `v ↦ −v` and conclude with `MvPolynomial.funext_set` in `(λ, u)`. So the Hilbert function of the
  cone over `E` in degree `≤ n` is at least `(n+1)²` (the homogeneous part has `≥ 2n + 1`; the
  exact value `3n` is not needed for the lower bound).
* **`indep_prod_fin`**: products of independent families on a finite product of sets are
  independent.
-/

open MvPolynomial

namespace LSG.ME

variable {K : Type*} [Field K]

/-- The cone monomials of degree `≤ n`. -/
def monoF (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) (w : Fin 3 → K) : K :=
  if (p.1 : ℕ) ≤ p.2 then w 0 ^ (p.1 : ℕ) * w 2 ^ ((p.2 : ℕ) - p.1)
  else w 1 * w 0 ^ (p.2 : ℕ) * w 2 ^ ((p.1 : ℕ) - 1 - p.2)

/-- The degree, the `V`-exponent and the `U`-exponent of a cone monomial. -/
def sigF {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : ℕ × ℕ × ℕ :=
  if (p.1 : ℕ) ≤ p.2 then ((p.2 : ℕ), 0, (p.1 : ℕ)) else ((p.1 : ℕ), 1, (p.2 : ℕ))

theorem sigF_injective {n : ℕ} : Function.Injective (sigF (n := n)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [sigF] at h
  split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq] at h
  · exact Prod.ext (Fin.ext h.2.2) (Fin.ext h.1)
  · omega
  · omega
  · exact Prod.ext (Fin.ext h.1) (Fin.ext h.2.2)

theorem sigF_snd_le {n : ℕ} (p : Fin (n + 1) × Fin (n + 1)) : (sigF p).2.1 ≤ 1 := by
  unfold sigF; split_ifs <;> simp

theorem monoF_eval (n : ℕ) (p : Fin (n + 1) × Fin (n + 1)) (l u v : K) :
    monoF n p ![l * u, l * v, l] = l ^ (sigF p).1 * v ^ (sigF p).2.1 * u ^ (sigF p).2.2 := by
  obtain ⟨i, j⟩ := p
  simp only [monoF, sigF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  split_ifs with h
  · simp only [pow_zero, mul_one, mul_pow]
    rw [show (j : ℕ) = i + (j - i) from (Nat.add_sub_cancel' h).symm, pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  · push Not at h
    simp only [pow_one, mul_pow]
    rw [show (i : ℕ) = 1 + j + (i - 1 - j) by omega, pow_add, pow_add]
    simp only [show 1 + (j : ℕ) + (i - 1 - j) - 1 - j = i - 1 - j by omega]
    ring

/-- The affine cone over `E : v² = 4u³ − a u − b` (without the `O`-line). -/
def coneE (a b : K) : Set (Fin 3 → K) :=
  {w | ∃ l u v : K, l ≠ 0 ∧ v ^ 2 = 4 * u ^ 3 - a * u - b ∧ w = ![l * u, l * v, l]}

/-- The two-variable polynomial `Σ_{ε p = e} c_p X₀^{d p} X₁^{x p}`. -/
noncomputable def polE {n : ℕ} (c : Fin (n + 1) × Fin (n + 1) → K) (e : ℕ) : MvPolynomial (Fin 2) K :=
  ∑ p, if (sigF p).2.1 = e then
    monomial (Finsupp.single 0 (sigF p).1 + Finsupp.single 1 (sigF p).2.2) (c p) else 0

theorem eval_polE {n : ℕ} (c : Fin (n + 1) × Fin (n + 1) → K) (e : ℕ) (l u : K) :
    eval ![l, u] (polE c e) =
      ∑ p, if (sigF p).2.1 = e then c p * l ^ (sigF p).1 * u ^ (sigF p).2.2 else 0 := by
  rw [polE, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [eval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp [mul_assoc]
  · simp

theorem coeff_polE {n : ℕ} (c : Fin (n + 1) × Fin (n + 1) → K) (p₀ : Fin (n + 1) × Fin (n + 1)) :
    (polE c (sigF p₀).2.1).coeff (Finsupp.single 0 (sigF p₀).1 + Finsupp.single 1 (sigF p₀).2.2) =
      c p₀ := by
  classical
  rw [polE, coeff_sum, Finset.sum_eq_single p₀]
  · simp [coeff_monomial]
  · intro p _ hp
    split_ifs with he
    · rw [coeff_monomial, if_neg]
      intro hm
      apply hp
      apply sigF_injective
      have h0 := congrArg (· 0) hm
      have h1 := congrArg (· 1) hm
      simp at h0 h1
      exact Prod.ext h0 (Prod.ext he h1)
    · rfl
  · simp

variable [IsAlgClosed K]

/-- **The cone monomials are independent on the cone over `E`.** -/
theorem monoF_linearIndependent (h2 : (2 : K) ≠ 0) (a b : K) (n : ℕ) :
    LinearIndependent K (fun p : Fin (n + 1) × Fin (n + 1) => (coneE a b).restrict (monoF n p)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hval : ∀ l u v : K, l ≠ 0 → v ^ 2 = 4 * u ^ 3 - a * u - b →
      ∑ p, c p * (l ^ (sigF p).1 * v ^ (sigF p).2.1 * u ^ (sigF p).2.2) = 0 := by
    intro l u v hl huv
    have := congrFun hc ⟨![l * u, l * v, l], l, u, v, hl, huv, rfl⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    change ∑ x, c x * monoF n x ![l * u, l * v, l] = 0 at this
    simpa [monoF_eval] using this
  -- the cubic has finitely many roots
  set r : Polynomial K := 4 * Polynomial.X ^ 3 - Polynomial.C a * Polynomial.X - Polynomial.C b
  have hr0 : r ≠ 0 := by
    intro h
    have h3 : r.coeff 3 = 4 := by
      simp only [r, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      rw [show (4 : Polynomial K) = Polynomial.C 4 from (map_ofNat Polynomial.C 4).symm,
        Polynomial.coeff_C_mul_X_pow]
      norm_num
    rw [h, Polynomial.coeff_zero] at h3
    exact h2 (mul_self_eq_zero.mp (by linear_combination -h3))
  have hSu : {u : K | r.eval u ≠ 0}.Infinite := by
    have : {u : K | r.eval u ≠ 0} = ({u : K | r.IsRoot u})ᶜ := by ext; simp [Polynomial.IsRoot]
    rw [this]
    exact (Polynomial.finite_setOfPred_isRoot hr0).infinite_compl
  have hSl : ({0}ᶜ : Set K).Infinite := (Set.finite_singleton 0).infinite_compl
  -- separate `ε = 0` and `ε = 1`
  have hsep : ∀ e : ℕ, e ≤ 1 → polE c e = 0 := by
    intro e he
    refine funext_set (fun i => if i = 0 then ({0}ᶜ : Set K) else {u | r.eval u ≠ 0})
      (fun i => by fin_cases i <;> simp [hSl, hSu]) fun x hx => ?_
    have hx0 : x 0 ≠ 0 := by simpa using hx 0 (Set.mem_univ _)
    have hx1 : r.eval (x 1) ≠ 0 := by simpa using hx 1 (Set.mem_univ _)
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (r.eval (x 1)) (n := 2) (by norm_num)
    have hv' : v ^ 2 = 4 * x 1 ^ 3 - a * x 1 - b := by
      rw [hv]; simp [r]
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv; exact hx1 hv.symm
    have hp := hval (x 0) (x 1) v hx0 hv'
    have hm := hval (x 0) (x 1) (-v) hx0 (by rw [neg_sq]; exact hv')
    have hxe : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hxe, eval_polE, map_zero]
    -- `Σ_{ε=0} = (hp + hm)/2`, `v Σ_{ε=1} = (hp − hm)/2`
    have hsplit : ∀ w : K, (∑ p, c p * (x 0 ^ (sigF p).1 * w ^ (sigF p).2.1 * x 1 ^ (sigF p).2.2)) =
        (∑ p, if (sigF p).2.1 = 0 then c p * x 0 ^ (sigF p).1 * x 1 ^ (sigF p).2.2 else 0) +
        w * ∑ p, if (sigF p).2.1 = 1 then c p * x 0 ^ (sigF p).1 * x 1 ^ (sigF p).2.2 else 0 := by
      intro w
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      have := sigF_snd_le p
      interval_cases h : (sigF p).2.1 <;> simp [h] <;> ring
    rw [hsplit] at hp hm
    interval_cases e
    · have : 2 * (∑ p, if (sigF p).2.1 = 0 then c p * x 0 ^ (sigF p).1 * x 1 ^ (sigF p).2.2
          else 0) = 0 := by linear_combination hp + hm
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 * v) * (∑ p, if (sigF p).2.1 = 1 then c p * x 0 ^ (sigF p).1 *
          x 1 ^ (sigF p).2.2 else 0) = 0 := by linear_combination hp - hm
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hv0)
  intro p
  have := coeff_polE c p
  rw [hsep _ (sigF_snd_le p), MvPolynomial.coeff_zero] at this
  exact this.symm

/-! ### Products -/

/-- **Products of independent families on a product of sets are independent.** -/
theorem indep_prod_fin {κ Y : Type*} [Fintype κ] (g : κ → Y → K) :
    ∀ (r : ℕ) (S : Fin r → Set Y), (∀ l, (S l).Nonempty) →
      (∀ l, LinearIndependent K (fun b => (S l).restrict (g b))) →
      ∀ c : (Fin r → κ) → K, (∀ z : Fin r → Y, (∀ l, z l ∈ S l) →
        ∑ β, c β * ∏ l, g (β l) (z l) = 0) → c = 0 := by
  intro r
  induction r with
  | zero =>
    intro S _ _ c hc
    funext β
    have := hc Fin.elim0 (fun l => Fin.elim0 l)
    rw [Fintype.sum_unique] at this
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at this
    rw [Subsingleton.elim β default]
    exact this
  | succ r ih =>
    intro S hne hS c hc
    classical
    -- coefficients after fixing the first factor
    have hfix : ∀ b, (fun β' : Fin r → κ => c (Fin.cons b β')) = 0 := by
      intro b
      refine ih (fun l => S l.succ) (fun l => hne l.succ) (fun l => hS l.succ) _ fun z' hz' => ?_
      have hli := (Fintype.linearIndependent_iff.mp (hS 0))
      refine hli (fun b => ∑ β', c (Fin.cons b β') * ∏ l, g (β' l) (z' l)) ?_ b
      funext ⟨z₀, hz₀⟩
      have := hc (Fin.cons z₀ z') (fun l => Fin.cases hz₀ hz' l)
      rw [← (Fin.consEquiv fun _ => κ).sum_comp, Fintype.sum_prod_type] at this
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
        Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun β' _ => ?_
      change (c (Fin.cons b β') * ∏ l, g (β' l) (z' l)) * g b z₀ =
        c (Fin.cons b β') * (g b z₀ * ∏ x, g (β' x) (z' x))
      ring
    funext β
    have := congrFun (hfix (β 0)) (Fin.tail β)
    simpa [Fin.cons_self_tail] using this

end LSG.ME
