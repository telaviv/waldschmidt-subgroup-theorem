/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.MEB.Stmt
import LSG.ME.Transl

/-!
# A5.3: the monomials of the auxiliary function on `G_a^{d₀} × G_m^{d₁} × ∏ B_k` (`STAGE_A5.md` D4)

For a family of abelian blocks `B : Fin m → AbBlock`, the auxiliary polynomial uses, in block `k`, only the free
coordinates `X_{i₀}, X_{is 0}, …, X_{is (g−1)}` (`fidx`), with total degree `D` per block:

* `MonoA d₀ d₁ B D` (exponents), `MonoA.eval` (the function on `Tan`), `MonoA.poly` (the cone monomial);
* `PpolyA μs p = Σ p_l M_l`, `PsiA μs p = Σ p_l M_l ∘ liftB`; `eval_PpolyA`: `eval (liftB u) (PpolyA μs p) = PsiA μs p u`;
* `isHomB_PpolyA`, `PpolyA_mem_FLE`: the hypotheses `IsHomB` and `FLE` of `MultEstB`;
* **`exists_PsiA_ne_zero`**: distinct monomials and `p ≠ 0` give `PsiA μs p ≢ 0`.

Nonvanishing: the ratio map `φ_k z = (θ_{is j}(z)/θ_{i₀}(z))_j` is a local diffeomorphism at `0` (`coords_locInv`,
inverse function theorem), so its image contains a ball (`exists_ratio_ball`). On `θ_{i₀} ≠ 0` a monomial is
`Π_k θ_{i₀}(z_k)^D` times a monomial in `(a, e^b, φ(z))`, and a polynomial vanishing on a product of large finite sets
is zero (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).
-/

open MvPolynomial Finset Complex Filter Topology
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE prod_mem_FLE' pow_mem_FLE')

noncomputable section

namespace LSG.AuxA

open LSG.MEB

/-! ### The ratio map of a block -/

/-- The free coordinates of a block: `0 ↦ i₀`, `j + 1 ↦ is j`. -/
def fidx (b : AbBlock) : Fin (b.g + 1) → Fin b.N := Fin.cases b.i₀ b.is

@[simp] lemma fidx_zero (b : AbBlock) : fidx b 0 = b.i₀ := rfl
@[simp] lemma fidx_succ (b : AbBlock) (j : Fin b.g) : fidx b j.succ = b.is j := rfl

/-- The ratio map `z ↦ (θ_{is j}(z)/θ_{i₀}(z))_j`. -/
def ratioMap (b : AbBlock) (z : Fin b.g → ℂ) : Fin b.g → ℂ := fun j => b.θ z (b.is j) / b.θ z b.i₀

lemma analyticAt_ratioMap (b : AbBlock) : AnalyticAt ℂ (ratioMap b) 0 := by
  have hθ := analyticAt_pi_iff.mp (b.θ_analytic 0)
  refine analyticAt_pi_iff.mpr fun j => ?_
  exact (hθ (b.is j)).div (hθ b.i₀) b.θ_i₀

/-- **The image of the ratio map contains a ball** around `φ(0)`, reached from points with `θ_{i₀} ≠ 0`. -/
theorem exists_ratio_ball (b : AbBlock) :
    ∃ ε > 0, ∀ w : Fin b.g → ℂ, dist w (ratioMap b 0) < ε →
      ∃ z, b.θ z b.i₀ ≠ 0 ∧ ratioMap b z = w := by
  obtain ⟨f', hf'⟩ := b.coords_locInv
  have hstrict := (analyticAt_ratioMap b).hasStrictFDerivAt
  have hfd : fderiv ℂ (ratioMap b) 0 = (f' : (Fin b.g → ℂ) →L[ℂ] (Fin b.g → ℂ)) := hf'.fderiv
  rw [hfd] at hstrict
  have hmap := hstrict.map_nhds_eq_of_equiv
  have hU : {z : Fin b.g → ℂ | b.θ z b.i₀ ≠ 0} ∈ 𝓝 (0 : Fin b.g → ℂ) := by
    have hc : ContinuousAt (fun z => b.θ z b.i₀) 0 :=
      ((analyticAt_pi_iff.mp (b.θ_analytic 0)) b.i₀).continuousAt
    exact hc.eventually_ne b.θ_i₀
  have himg : ratioMap b '' {z | b.θ z b.i₀ ≠ 0} ∈ 𝓝 (ratioMap b 0) := by
    rw [← hmap]; exact image_mem_map hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨ε, hε, fun w hw => ?_⟩
  obtain ⟨z, hz, hzw⟩ := hball (Metric.mem_ball.mpr hw)
  exact ⟨z, hz, hzw⟩

/-! ### Monomials -/

variable {m d₀ d₁ : ℕ}

variable (B : Fin m → AbBlock) (d₀ d₁) in
/-- Exponents of a monomial of block degree `D` in the free coordinates. -/
structure MonoA (D : ℕ) where
  α : Fin d₀ → ℕ
  β : Fin d₁ → ℕ
  γ : ∀ k, Fin ((B k).g + 1) → ℕ
  hγ : ∀ k, ∑ c, γ k c = D

variable {B : Fin m → AbBlock} {D : ℕ}

/-- The monomial as a function on `Tan`. -/
def MonoA.eval (μ : MonoA d₀ d₁ B D) (u : Tan d₀ d₁ B) : ℂ :=
  (∏ i, u.1 i ^ μ.α i) * (∏ j, Complex.exp (u.2.1 j) ^ μ.β j) *
    ∏ k, ∏ c, (B k).θ (u.2.2 k) (fidx (B k) c) ^ μ.γ k c

/-- The cone monomial. -/
def MonoA.poly (μ : MonoA d₀ d₁ B D) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  (∏ i, X (Var.x i) ^ μ.α i) * (∏ j, X (Var.y j) ^ μ.β j) *
    ∏ k, ∏ c, X (Var.e k (fidx (B k) c)) ^ μ.γ k c

/-- **The polynomial of the auxiliary function.** -/
def PpolyA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ l, C (p l : ℂ) * (μs l).poly

/-- **The auxiliary function.** -/
def PsiA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (u : Tan d₀ d₁ B) : ℂ :=
  ∑ l, (p l : ℂ) * (μs l).eval u

theorem MonoA.eval_poly (μ : MonoA d₀ d₁ B D) (u : Tan d₀ d₁ B) : MvPolynomial.eval (liftB u) μ.poly = μ.eval u := by
  simp only [MonoA.poly, MonoA.eval, map_mul, map_prod, map_pow, eval_X, liftB]

theorem eval_PpolyA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (u : Tan d₀ d₁ B) :
    MvPolynomial.eval (liftB u) (PpolyA μs p) = PsiA μs p u := by
  simp only [PpolyA, PsiA, map_sum, map_mul, eval_C, MonoA.eval_poly]

theorem MonoA.isHomB_poly (μ : MonoA d₀ d₁ B D) : IsHomB μ.poly (fun _ => D) := by
  intro k
  have hx := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (Var.x i) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.α i) (fun _ => 0)
    (fun i _ => by simpa [wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.x i : Var d₀ d₁ B)).pow (μ.α i))
  have hy := IsWeightedHomogeneous.prod Finset.univ
    (fun j => (X (Var.y j) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.β j) (fun _ => 0)
    (fun j _ => by simpa [wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d₀ d₁ B)).pow (μ.β j))
  have he := IsWeightedHomogeneous.prod Finset.univ
    (fun k' => ∏ c, (X (Var.e k' (fidx (B k') c)) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.γ k' c)
    (fun k' => if k' = k then D else 0) (fun k' _ => by
      have := IsWeightedHomogeneous.prod Finset.univ
        (fun c => (X (Var.e k' (fidx (B k') c)) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.γ k' c)
        (fun c => μ.γ k' c * if k' = k then 1 else 0)
        (fun c _ => by
          simpa [mul_comm, wk] using
            (isWeightedHomogeneous_X ℂ (wk k) (Var.e k' (fidx (B k') c) : Var d₀ d₁ B)).pow (μ.γ k' c))
      convert this using 1
      split_ifs with h
      · simp [μ.hγ k']
      · simp)
  change IsWeightedHomogeneous (wk k) μ.poly D
  unfold MonoA.poly
  convert (hx.mul hy).mul he using 1
  simp

theorem isHomB_PpolyA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) :
    IsHomB (PpolyA μs p) (fun _ => D) := by
  intro k
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [mem_weightedHomogeneousSubmodule]
  simpa using (isWeightedHomogeneous_C (wk k) (p l : ℂ)).mul ((μs l).isHomB_poly k)

theorem MonoA.poly_mem_FLE {A₀ A₁ : ℕ} (μ : MonoA d₀ d₁ B D) (hA : ∑ i, μ.α i ≤ A₀)
    (hB : ∑ j, μ.β j ≤ A₁) : μ.poly ∈ FLE ℂ blk (DfunB A₀ A₁ D) := by
  have h1 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun i => (X (Var.x i) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.α i)
    (fun i => μ.α i • Pi.single (blk (Var.x i : Var d₀ d₁ B)) 1)
    (fun i _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h2 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun j => (X (Var.y j) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.β j)
    (fun j => μ.β j • Pi.single (blk (Var.y j : Var d₀ d₁ B)) 1)
    (fun j _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h3 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun k => ∏ c, (X (Var.e k (fidx (B k) c)) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ μ.γ k c)
    (fun k => ∑ c, μ.γ k c • Pi.single (blk (Var.e k (fidx (B k) c) : Var d₀ d₁ B)) 1)
    (fun k _ => prod_mem_FLE' _ _ _ fun c _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  refine FLE_mono ℂ blk (fun b => ?_) (mul_mem_FLE ℂ (mul_mem_FLE ℂ h1 h2) h3)
  cases b with
  | x => simpa [DfunB, blk, Finset.sum_apply, Pi.single_apply] using hA
  | yz => simpa [DfunB, blk, Finset.sum_apply, Pi.single_apply] using hB
  | e k =>
    simp only [DfunB, blk, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero, zero_add, Blk.e.injEq, mul_ite, mul_one]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [μ.hγ k]

theorem PpolyA_mem_FLE {L A₀ A₁ : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ)
    (hA : ∀ l, ∑ i, (μs l).α i ≤ A₀) (hB : ∀ l, ∑ j, (μs l).β j ≤ A₁) :
    PpolyA μs p ∈ FLE ℂ blk (DfunB A₀ A₁ D) := by
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ ((μs l).poly_mem_FLE (hA l) (hB l))

/-! ### Nonvanishing -/

variable (B d₀ d₁) in
/-- The variables of the dehomogenised polynomial: `a`, `e^b`, and the ratios. -/
abbrev RVarA := Fin d₀ ⊕ Fin d₁ ⊕ (Σ k, Fin (B k).g)

/-- The exponent vector in the dehomogenised variables. -/
def MonoA.rexp (μ : MonoA d₀ d₁ B D) : RVarA d₀ d₁ B → ℕ
  | .inl i => μ.α i
  | .inr (.inl j) => μ.β j
  | .inr (.inr ⟨k, j⟩) => μ.γ k j.succ

/-- On `θ_{i₀} ≠ 0`, a block of a monomial is `θ_{i₀}^D` times a monomial in the ratios. -/
lemma MonoA.block_eq (μ : MonoA d₀ d₁ B D) (k : Fin m) (z : Fin (B k).g → ℂ) (hz : (B k).θ z (B k).i₀ ≠ 0) :
    ∏ c, (B k).θ z (fidx (B k) c) ^ μ.γ k c =
      (B k).θ z (B k).i₀ ^ D * ∏ j, ratioMap (B k) z j ^ μ.γ k j.succ := by
  have hs := μ.hγ k
  rw [Fin.sum_univ_succ] at hs
  rw [Fin.prod_univ_succ, fidx_zero]
  have hj : ∀ j : Fin (B k).g, (B k).θ z (fidx (B k) j.succ) =
      (B k).θ z (B k).i₀ * ratioMap (B k) z j := fun j => by
    rw [fidx_succ, ratioMap]; field_simp
  simp_rw [hj, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, ← mul_assoc, ← pow_add, hs]

/-- **`Ψ ≢ 0` for distinct monomials and `p ≠ 0`.** -/
theorem exists_PsiA_ne_zero {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D)
    (hinj : Function.Injective fun l => (μs l).rexp) (p : Fin L → ℤ) (hp : p ≠ 0) :
    ∃ u, PsiA μs p u ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  -- the dehomogenised polynomial
  let ex : Fin L → (RVarA d₀ d₁ B →₀ ℕ) := fun l => Finsupp.equivFunOnFinite.symm (μs l).rexp
  have hex : Function.Injective ex := fun a b h => hinj (by
    have := congrArg Finsupp.equivFunOnFinite h; simpa [ex] using this)
  let Q : MvPolynomial (RVarA d₀ d₁ B) ℂ := ∑ l, MvPolynomial.monomial (ex l) (p l : ℂ)
  set N : ℕ := ∑ l, ∑ v, (μs l).rexp v
  have hdeg : ∀ v, MvPolynomial.degreeOf v Q ≤ N := by
    intro v
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun l _ => ?_)
    have hm : MvPolynomial.degreeOf v (MvPolynomial.monomial (ex l) (p l : ℂ)) ≤ (μs l).rexp v := by
      by_cases h0 : (p l : ℂ) = 0
      · rw [h0, map_zero]; simp
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ h0]; simp [ex]
    refine hm.trans ?_
    exact (single_le_sum (f := fun v => (μs l).rexp v) (fun _ _ => Nat.zero_le _)
      (mem_univ v)).trans (single_le_sum (f := fun l => ∑ v, (μs l).rexp v)
        (fun _ _ => Nat.zero_le _) (mem_univ l))
  -- the evaluation sets
  choose ε hε hball using fun k => exists_ratio_ball (B k)
  let ptR : ∀ k, Fin (B k).g → ℕ → ℂ := fun k j n => ratioMap (B k) 0 j + (ε k / (2 * (N + 2)) : ℝ) * n
  have hptR_inj : ∀ k j, Function.Injective (ptR k j) := fun k j a b h => by
    have h1 : ((ε k / (2 * (N + 2)) : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ε k / (2 * (N + 2)) := by have := hε k; positivity
      exact_mod_cast this.ne'
    have h2 := mul_left_cancel₀ h1 (add_left_cancel h)
    exact_mod_cast h2
  have hptR_near : ∀ k j n, n < N + 1 → ‖ptR k j n - ratioMap (B k) 0 j‖ < ε k := fun k j n hn => by
    simp only [ptR, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_natCast]
    have hεk := hε k
    have hn' : (n : ℝ) < N + 2 := by have : (n : ℝ) < N + 1 := by exact_mod_cast hn
                                     linarith
    rw [Real.norm_of_nonneg (by positivity)]
    calc ε k / (2 * (N + 2)) * n ≤ ε k / (2 * (N + 2)) * (N + 2) := by gcongr
      _ = ε k / 2 := by field_simp
      _ < ε k := by linarith
  let Sv : RVarA d₀ d₁ B → Finset ℂ := fun v => match v with
    | .inl _ => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
    | .inr (.inl _) => (range (N + 1)).image (fun n : ℕ => ((n + 1 : ℕ) : ℂ))
    | .inr (.inr ⟨k, j⟩) => (range (N + 1)).image (ptR k j)
  have hcard : ∀ v, MvPolynomial.degreeOf v Q < (Sv v).card := by
    intro v
    have h1 := hdeg v
    rcases v with i | i | ⟨k, j⟩
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
    · simp only [Sv]
      rw [card_image_of_injective _ (fun a b h => by
        have := Nat.cast_injective (R := ℂ) h; omega), card_range]; omega
    · simp only [Sv]; rw [card_image_of_injective _ (hptR_inj k j), card_range]; omega
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q Sv hcard fun x hx => ?_
    -- a point of `Tan` above `x`
    have hz : ∀ k, ∃ z, (B k).θ z (B k).i₀ ≠ 0 ∧ ratioMap (B k) z = fun j => x (.inr (.inr ⟨k, j⟩)) := by
      intro k
      refine hball k _ ?_
      rw [dist_pi_lt_iff (hε k)]
      intro j
      obtain ⟨n, hn, hnx⟩ := mem_image.mp (hx (.inr (.inr ⟨k, j⟩)))
      rw [dist_eq_norm, ← hnx]
      exact hptR_near k j n (mem_range.mp hn)
    choose z hz0 hzx using hz
    have hb : ∀ i, x (.inr (.inl i)) ≠ 0 := by
      intro i
      obtain ⟨n, -, hn⟩ := mem_image.mp (hx (.inr (.inl i)))
      rw [← hn]; exact_mod_cast Nat.succ_ne_zero n
    let pt : Tan d₀ d₁ B := (fun i => x (.inl i), fun i => Complex.log (x (.inr (.inl i))), z)
    have hpt := hall pt
    unfold PsiA at hpt
    have hθ : ∏ k, (B k).θ (z k) (B k).i₀ ^ D ≠ 0 :=
      prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hz0 k)
    have hpt' : (∏ k, (B k).θ (z k) (B k).i₀ ^ D) * MvPolynomial.eval x Q = 0 := by
      rw [← hpt]
      simp only [Q, map_sum, MvPolynomial.eval_monomial, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
      unfold MonoA.eval
      simp only [ex, Finsupp.coe_equivFunOnFinite_symm, MonoA.rexp, pt]
      rw [Finset.prod_congr rfl fun k _ => (μs l).block_eq k (z k) (hz0 k)]
      simp only [Complex.exp_log (hb _), hzx, prod_mul_distrib]
      ring
    exact (mul_eq_zero.mp hpt').resolve_left hθ
  -- coefficients
  apply hp
  funext l
  have hc := congrArg (fun q : MvPolynomial (RVarA d₀ d₁ B) ℂ => q.coeff (ex l)) hQ0
  simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [sum_eq_single l (fun b _ hb => if_neg (fun h => hb (hex h))) (by simp)] at hc
  simp only [↓reduceIte, Int.cast_eq_zero] at hc
  simpa using hc

end LSG.AuxA
