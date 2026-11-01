/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Lift
import StrongSix.M2.WustholzGen

/-!
# Translation by an arbitrary vector through the addition laws (M2.5, β)

The `VBlock` analogue of `LSG.MEB.PhOpLaw`. For a law choice `c : ∀ k, Fin (B k).nLV` and a vector `Y : Var → ℂ`,
`lawSub c Y` substitutes `x ↦ x + Y_x`, `y ↦ Y_y · y`, `z ↦ Y_z · z` and, in block `k`,
`(X, T)_k ↦ lawV_{c k}((X, T)_k, Y_k)`. The laws of block `k` have bidegree `(ld_k, ld_k)`, so the factor `2` of
MEB becomes `ld_k` (`dblB B D`, `isHomV_lawSub`).

* `lawPt c X Y`: the substituted point; **`eval_lawSub`**: `eval X (lawSub c Y Q) = eval (lawPt c X Y) Q`.
* `bmulB B`, `dblB B D` (block `k` degree times `ld_k`); **`lawSub_mem_FLE`**, **`isHomV_lawSub`**
  (`IsHomV Q d → IsHomV (lawSub c Y Q) (fun k => ld_k * d k)`): from `lawV_hom` alone.
* The block weight `wB` and `mem_FLE_of_isWH`.
-/

open MvPolynomial StrongSix.M2

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Block degrees as a weight -/

/-- The block weight: `e_{blk v}`. -/
def wB (v : Var d₀ d₁ B) : Blk m → ℕ := Pi.single (blk v) 1

theorem bdeg_eq_weight (s : Var d₀ d₁ B →₀ ℕ) (b : Blk m) :
    bdeg blk s b = Finsupp.weight wB s b := by
  rw [bdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [wB, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : blk v = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem mem_FLE_of_isWH {p : MvPolynomial (Var d₀ d₁ B) ℂ} {d D : Blk m → ℕ}
    (hp : IsWeightedHomogeneous wB p d) (h : d ≤ D) : p ∈ FLE ℂ blk D := by
  rw [FLE, mem_restrictSupport_iff]
  intro s hs b
  rw [bdeg_eq_weight, hp (mem_support_iff.mp hs)]
  exact h b

variable (B) in
/-- Block degrees after translation: block `k` multiplied by `ld_k`. -/
def bmulB : Blk m → ℕ
  | .e k => (B k).ld
  | _ => 1

variable (B) in
/-- `D` with the block degrees multiplied by the law degrees. -/
def dblB (D : Blk m → ℕ) : Blk m → ℕ := fun b => bmulB B b * D b

/-- The block degree of the image of a variable. -/
def eB (v : Var d₀ d₁ B) : Blk m → ℕ := Pi.single (blk v) (bmulB B (blk v))

/-! ### The substitution -/

/-- The law of block `k` with second argument `q`, in the block-`k` variables. -/
noncomputable def lawE (k : Fin m) (i : Fin (B k).nLV) (q : (B k).Idx → ℂ) (a : (B k).Idx) :
    MvPolynomial (Var d₀ d₁ B) ℂ :=
  bind₁ (Sum.elim (fun b => X (Var.e k b)) (fun b => C (q b))) ((B k).lawV i a)

/-- The images of the variables. -/
noncomputable def lawVar (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ
  | .x i => X (.x i) + C (Y (.x i))
  | .y j => C (Y (.y j)) * X (.y j)
  | .z j => C (Y (.z j)) * X (.z j)
  | .e k a => lawE k (c k) (fun b => Y (.e k b)) a

/-- **Translation by the vector `Y`** with law choice `c`. -/
noncomputable def lawSub (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) ℂ :=
  bind₁ (lawVar c Y)

/-- The substituted point `law_c(X, Y)` (blockwise). -/
noncomputable def lawPt (c : ∀ k, Fin (B k).nLV) (x y : Var d₀ d₁ B → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => x (.x i) + y (.x i)
  | .y j => y (.y j) * x (.y j)
  | .z j => y (.z j) * x (.z j)
  | .e k a => evalLawV ((B k).lawV (c k)) (fun b => x (.e k b)) (fun b => y (.e k b)) a

theorem eval_lawE (x : Var d₀ d₁ B → ℂ) (k : Fin m) (i : Fin (B k).nLV) (q : (B k).Idx → ℂ)
    (a : (B k).Idx) :
    eval x (lawE k i q a) = evalLawV ((B k).lawV i) (fun b => x (.e k b)) q a := by
  rw [lawE, LSG.MEB.eval_bind₁', evalLawV]
  refine congrArg (fun f => eval f _) (funext fun s => ?_)
  cases s <;> simp

theorem eval_lawVar (c : ∀ k, Fin (B k).nLV) (x y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    eval x (lawVar c y v) = lawPt c x y v := by
  cases v <;> simp [lawVar, lawPt, eval_lawE]

/-- **Evaluation of a translate.** -/
theorem eval_lawSub (c : ∀ k, Fin (B k).nLV) (x y : Var d₀ d₁ B → ℂ)
    (Q : MvPolynomial (Var d₀ d₁ B) ℂ) :
    eval x (lawSub c y Q) = eval (lawPt c x y) Q := by
  rw [lawSub, LSG.MEB.eval_bind₁']
  exact congrArg (fun f => eval f Q) (funext fun v => eval_lawVar c x y v)

/-! ### Degrees -/

/-- The block-`k` law is homogeneous of degree `ld_k • δ` for any weight that is `δ` on block `k`. -/
theorem isWH_lawE {M : Type*} [AddCommMonoid M] (ω : Var d₀ d₁ B → M) (k : Fin m) (δ : M)
    (hω : ∀ b, ω (.e k b) = δ) (i : Fin (B k).nLV) (q : (B k).Idx → ℂ) (a : (B k).Idx) :
    IsWeightedHomogeneous ω (lawE k i q a) ((B k).ld • δ) := by
  set F : ℕ × ℕ →+ M := (multiplesHom M δ).comp (AddMonoidHom.fst ℕ ℕ)
  have hL := LSG.MEB.isWH_map_weight ((B k).lawV_hom i a) F
  have hF : F (((B k).ld, (B k).ld) : ℕ × ℕ) = (B k).ld • δ := by simp [F]
  rw [hF] at hL
  refine LSG.MEB.isWeightedHomogeneous_bind₁ (fun s => ?_) hL
  cases s with
  | inl b =>
    have := isWeightedHomogeneous_X ℂ ω (Var.e k b)
    simpa [F, biWV, hω] using this
  | inr b =>
    have := isWeightedHomogeneous_C ω (q b)
    simpa [F, biWV] using this

theorem lawVar_mem (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    lawVar c Y v ∈ FLE ℂ blk (eB v) := by
  cases v with
  | x i =>
    show X _ + C _ ∈ FLE ℂ blk (Pi.single Blk.x 1)
    exact Submodule.add_mem _ (mem_FLE_of_isWH (isWeightedHomogeneous_X ℂ wB _) (le_refl _))
      (mem_FLE_of_isWH (isWeightedHomogeneous_C wB _) (fun _ => Nat.zero_le _))
  | y j =>
    have h := mem_FLE_of_isWH (D := Pi.single Blk.yz 1)
      ((isWeightedHomogeneous_X ℂ wB (Var.y j : Var d₀ d₁ B)).C_mul (Y (.y j))) (le_refl _)
    simpa [lawVar, bmulB, wB, eB, blk] using h
  | z j =>
    have h := mem_FLE_of_isWH (D := Pi.single Blk.yz 1)
      ((isWeightedHomogeneous_X ℂ wB (Var.z j : Var d₀ d₁ B)).C_mul (Y (.z j))) (le_refl _)
    simpa [lawVar, bmulB, wB, eB, blk] using h
  | e k a =>
    have h := isWH_lawE (d₀ := d₀) (d₁ := d₁) wB k (Pi.single (Blk.e k) 1) (fun b => rfl) (c k)
      (fun b => Y (.e k b)) a
    refine mem_FLE_of_isWH h (le_of_eq ?_)
    funext b'
    simp [bmulB, eB, blk, Pi.single_apply]

/-- **Block degrees under translation**: the `x`- and `(y, z)`-degrees are preserved, block `k` degrees are
multiplied by at most `ld_k`. -/
theorem lawSub_mem_FLE (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) {D : Blk m → ℕ}
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} (hQ : Q ∈ FLE ℂ blk D) :
    lawSub c Y Q ∈ FLE ℂ blk (dblB B D) := by
  rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S blk D := hQ hn
  rw [lawSub, bind₁_monomial]
  have hpow : ∀ v, lawVar c Y v ^ n v ∈ FLE ℂ blk (n v • eB v) :=
    fun v => pow_mem_FLE' (lawVar_mem c Y v) (n v)
  have hprod := prod_mem_FLE' (K := ℂ) (β := (blk : Var d₀ d₁ B → Blk m)) n.support
    (fun v => lawVar c Y v ^ n v) (fun v => n v • eB v) fun v _ => hpow v
  have hle : (∑ v ∈ n.support, n v • eB v) ≤ dblB B D := by
    intro b
    have hb := hnS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, eB, Pi.single_apply, smul_eq_mul, dblB]
    calc ∑ v ∈ n.support, n v * (if b = blk v then bmulB B (blk v) else 0)
        ≤ ∑ v, n v * (if b = blk v then bmulB B (blk v) else 0) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ v, bmulB B b * (if blk v = b then n v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmulB B b * ∑ v, (if blk v = b then n v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmulB B b * D b := Nat.mul_le_mul_left _ hb
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (FLE_mono ℂ blk hle hprod)

theorem isWH_lawVar (k : Fin m) (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    IsWeightedHomogeneous (wk k) (lawVar c Y v) ((B k).ld * wk k v) := by
  cases v with
  | x i =>
    simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.x i : Var d₀ d₁ B)).add
      (isWeightedHomogeneous_C (wk k) (Y (.x i)))
  | y j => simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d₀ d₁ B)).C_mul _
  | z j => simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.z j : Var d₀ d₁ B)).C_mul _
  | e k' a =>
    have := isWH_lawE (d₀ := d₀) (d₁ := d₁) (wk k) k' (if k' = k then 1 else 0) (fun b => rfl) (c k')
      (fun b => Y (.e k' b)) a
    by_cases h : k' = k
    · subst h; simpa [lawVar, wk] using this
    · simpa [lawVar, wk, h] using this

/-- The block degrees after translation. -/
def ldMul (B : Fin m → VBlock) (d : Fin m → ℕ) : Fin m → ℕ := fun k => (B k).ld * d k

/-- **Homogeneity under translation**: block `k` degrees are multiplied by `ld_k`. -/
theorem isHomV_lawSub (c : ∀ k, Fin (B k).nLV) (Y : Var d₀ d₁ B → ℂ) {Q : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hQ : IsHomV Q d) : IsHomV (lawSub c Y Q) (ldMul B d) := by
  intro k
  have h := LSG.MEB.isWH_map_weight (hQ k) ((multiplesHom ℕ (B k).ld) : ℕ →+ ℕ)
  have e : ((multiplesHom ℕ (B k).ld) (d k)) = ldMul B d k := by simp [ldMul, mul_comm]
  rw [e] at h
  refine LSG.MEB.isWeightedHomogeneous_bind₁ (fun v => ?_) h
  simpa [smul_eq_mul, mul_comm] using isWH_lawVar k c Y v

end LSG.MEBV
