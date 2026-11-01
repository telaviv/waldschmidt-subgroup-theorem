/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Model
import StrongSix.M2.WustholzGen

/-!
# Translation by an arbitrary vector through the addition laws (A4.1a, β)

For a law choice `c : ∀ k, Fin (B k).nL` and a vector `Y : Var → ℂ` (a cone point, or a moving point
`t ↦ Y(t)` for Philippon's operators), `lawSub c Y` substitutes
`x ↦ x + Y_x`, `y ↦ Y_y · y`, `z ↦ Y_z · z` and, in block `k`, `X_k ↦ law_{c k}(X_k, Y_k)`.
The translation `τ g c` of the model is `lawSub c (coords g 1)` (STAGE_A4 §7.3).

* `lawPt c X Y`: the substituted point; **`eval_lawSub`**: `eval X (lawSub c Y Q) = eval (lawPt c X Y) Q`.
* `dblB D` (block degrees `D`, abelian ones doubled); **`lawSub_mem_FLE`**, **`isHomB_lawSub`**
  (`IsHomB Q d → IsHomB (lawSub c Y Q) (2 • d)`): from `law_hom` alone.
* Generic: `IsWeightedHomogeneous.map_weight`, `isWeightedHomogeneous_bind₁`, the block weight `wB` and
  `mem_FLE_of_isWH`.
-/

open MvPolynomial StrongSix.M2

namespace LSG.MEB

/-! ### Generic weighted homogeneity -/

section Generic

variable {σ τ M M' R : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M']

theorem isWH_map_weight {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (h : IsWeightedHomogeneous w φ n) (F : M →+ M') : IsWeightedHomogeneous (F ∘ w) φ (F n) := by
  intro s hs
  rw [← h hs, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  simp [map_nsmul]

/-- Substituting weighted-homogeneous polynomials of the right degrees preserves weighted homogeneity. -/
theorem isWeightedHomogeneous_bind₁ {w : σ → M} {w' : τ → M} {f : σ → MvPolynomial τ R}
    (hf : ∀ v, IsWeightedHomogeneous w' (f v) (w v)) {φ : MvPolynomial σ R} {n : M}
    (hφ : IsWeightedHomogeneous w φ n) : IsWeightedHomogeneous w' (bind₁ f φ) n := by
  classical
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  rw [bind₁_monomial, ← hφ (mem_support_iff.mp hs), Finsupp.weight_apply, Finsupp.sum]
  exact (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hf i).pow (s i)).C_mul _

end Generic

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

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

/-- Block degrees after translation: abelian entries doubled. -/
def bmulB : Blk m → ℕ
  | .e _ => 2
  | _ => 1

/-- `D` with the abelian block degrees doubled. -/
def dblB (D : Blk m → ℕ) : Blk m → ℕ := fun b => bmulB b * D b

/-- The block degree of the image of a variable. -/
def eB (v : Var d₀ d₁ B) : Blk m → ℕ := Pi.single (blk v) (bmulB (blk v))

/-! ### The substitution -/

/-- The law of block `k` with second argument `q`, in the block-`k` variables. -/
noncomputable def lawE (k : Fin m) (i : Fin (B k).nL) (q : Fin (B k).N → ℂ) (a : Fin (B k).N) :
    MvPolynomial (Var d₀ d₁ B) ℂ :=
  bind₁ (Sum.elim (fun b => X (Var.e k b)) (fun b => C (q b))) ((B k).law i a)

/-- The images of the variables. -/
noncomputable def lawVar (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ
  | .x i => X (.x i) + C (Y (.x i))
  | .y j => C (Y (.y j)) * X (.y j)
  | .z j => C (Y (.z j)) * X (.z j)
  | .e k a => lawE k (c k) (fun b => Y (.e k b)) a

/-- **Translation by the vector `Y`** with law choice `c`. -/
noncomputable def lawSub (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) ℂ :=
  bind₁ (lawVar c Y)

/-- The substituted point `law_c(X, Y)` (blockwise). -/
noncomputable def lawPt (c : ∀ k, Fin (B k).nL) (x y : Var d₀ d₁ B → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => x (.x i) + y (.x i)
  | .y j => y (.y j) * x (.y j)
  | .z j => y (.z j) * x (.z j)
  | .e k a => evalLaw ((B k).law (c k)) (fun b => x (.e k b)) (fun b => y (.e k b)) a

theorem eval_bind₁' {σ τ : Type*} (x : τ → ℂ) (f : σ → MvPolynomial τ ℂ) (φ : MvPolynomial σ ℂ) :
    eval x (bind₁ f φ) = eval (fun v => eval x (f v)) φ := by
  simp only [eval, coe_eval₂Hom]
  exact eval₂Hom_bind₁ (RingHom.id ℂ) x f φ

theorem eval_lawE (x : Var d₀ d₁ B → ℂ) (k : Fin m) (i : Fin (B k).nL) (q : Fin (B k).N → ℂ)
    (a : Fin (B k).N) :
    eval x (lawE k i q a) = evalLaw ((B k).law i) (fun b => x (.e k b)) q a := by
  rw [lawE, eval_bind₁', evalLaw]
  refine congrArg (fun f => eval f _) (funext fun s => ?_)
  cases s <;> simp

theorem eval_lawVar (c : ∀ k, Fin (B k).nL) (x y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    eval x (lawVar c y v) = lawPt c x y v := by
  cases v <;> simp [lawVar, lawPt, eval_lawE]

/-- **Evaluation of a translate.** -/
theorem eval_lawSub (c : ∀ k, Fin (B k).nL) (x y : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Var d₀ d₁ B) ℂ) :
    eval x (lawSub c y Q) = eval (lawPt c x y) Q := by
  rw [lawSub, eval_bind₁']
  exact congrArg (fun f => eval f Q) (funext fun v => eval_lawVar c x y v)

/-! ### Degrees -/

/-- The block-`k` law is homogeneous of degree `2 δ` for any weight that is `δ` on block `k`. -/
theorem isWH_lawE {M : Type*} [AddCommMonoid M] (ω : Var d₀ d₁ B → M) (k : Fin m) (δ : M)
    (hω : ∀ b, ω (.e k b) = δ) (i : Fin (B k).nL) (q : Fin (B k).N → ℂ) (a : Fin (B k).N) :
    IsWeightedHomogeneous ω (lawE k i q a) (2 • δ) := by
  set F : ℕ × ℕ →+ M := (multiplesHom M δ).comp (AddMonoidHom.fst ℕ ℕ)
  have hL := isWH_map_weight ((B k).law_hom i a) F
  have hF : F ((2, 2) : ℕ × ℕ) = 2 • δ := by simp [F]
  rw [hF] at hL
  refine isWeightedHomogeneous_bind₁ (fun s => ?_) hL
  cases s with
  | inl b =>
    have := isWeightedHomogeneous_X ℂ ω (Var.e k b)
    simpa [F, biW, hω] using this
  | inr b =>
    have := isWeightedHomogeneous_C ω (q b)
    simpa [F, biW] using this

theorem lawVar_mem (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    lawVar c Y v ∈ FLE ℂ blk (eB v) := by
  cases v with
  | x i =>
    show X _ + C _ ∈ FLE ℂ blk (Pi.single Blk.x 1)
    exact Submodule.add_mem _ (mem_FLE_of_isWH (isWeightedHomogeneous_X ℂ wB _) (le_refl _))
      (mem_FLE_of_isWH (isWeightedHomogeneous_C wB _) (fun _ => Nat.zero_le _))
  | y j =>
    have h := mem_FLE_of_isWH (D := Pi.single Blk.yz 1)
      ((isWeightedHomogeneous_X ℂ wB (Var.y j : Var d₀ d₁ B)).C_mul (Y (.y j))) (le_refl _)
    simpa [lawVar, bmulB, wB, eB] using h
  | z j =>
    have h := mem_FLE_of_isWH (D := Pi.single Blk.yz 1)
      ((isWeightedHomogeneous_X ℂ wB (Var.z j : Var d₀ d₁ B)).C_mul (Y (.z j))) (le_refl _)
    simpa [lawVar, bmulB, wB, eB] using h
  | e k a =>
    have h := isWH_lawE (d₀ := d₀) (d₁ := d₁) wB k (Pi.single (Blk.e k) 1) (fun b => rfl) (c k)
      (fun b => Y (.e k b)) a
    refine mem_FLE_of_isWH h (le_of_eq ?_)
    funext b'
    simp [bmulB, eB, Pi.single_apply]

/-- **Block degrees under translation**: the `x`- and `(y, z)`-degrees are preserved, the abelian ones at most
double. -/
theorem lawSub_mem_FLE (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) {D : Blk m → ℕ}
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} (hQ : Q ∈ FLE ℂ blk D) : lawSub c Y Q ∈ FLE ℂ blk (dblB D) := by
  rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S blk D := hQ hn
  rw [lawSub, bind₁_monomial]
  have hpow : ∀ v, lawVar c Y v ^ n v ∈ FLE ℂ blk (n v • eB v) :=
    fun v => pow_mem_FLE' (lawVar_mem c Y v) (n v)
  have hprod := prod_mem_FLE' (K := ℂ) (β := (blk : Var d₀ d₁ B → Blk m)) n.support
    (fun v => lawVar c Y v ^ n v) (fun v => n v • eB v) fun v _ => hpow v
  have hle : (∑ v ∈ n.support, n v • eB v) ≤ dblB D := by
    intro b
    have hb := hnS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, eB, Pi.single_apply, smul_eq_mul, dblB]
    calc ∑ v ∈ n.support, n v * (if b = blk v then bmulB (blk v) else 0)
        ≤ ∑ v, n v * (if b = blk v then bmulB (blk v) else 0) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ v, bmulB b * (if blk v = b then n v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmulB b * ∑ v, (if blk v = b then n v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmulB b * D b := Nat.mul_le_mul_left _ hb
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (FLE_mono ℂ blk hle hprod)

theorem isWH_lawVar (k : Fin m) (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) (v : Var d₀ d₁ B) :
    IsWeightedHomogeneous (wk k) (lawVar c Y v) (2 * wk k v) := by
  cases v with
  | x i =>
    simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.x i : Var d₀ d₁ B)).add
      (isWeightedHomogeneous_C (wk k) (Y (.x i)))
  | y j => simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d₀ d₁ B)).C_mul _
  | z j => simpa [lawVar, wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.z j : Var d₀ d₁ B)).C_mul _
  | e k' a =>
    have := isWH_lawE (d₀ := d₀) (d₁ := d₁) (wk k) k' (if k' = k then 1 else 0) (fun b => rfl) (c k')
      (fun b => Y (.e k' b)) a
    simpa [lawVar, wk] using this

/-- **Homogeneity under translation**: block degrees double. -/
theorem isHomB_lawSub (c : ∀ k, Fin (B k).nL) (Y : Var d₀ d₁ B → ℂ) {Q : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hQ : IsHomB Q d) : IsHomB (lawSub c Y Q) (2 • d) := by
  intro k
  have h := isWH_map_weight (hQ k) ((multiplesHom ℕ 2) : ℕ →+ ℕ)
  have e : ((multiplesHom ℕ 2) (d k)) = (2 • d) k := by simp [mul_comm]
  rw [e] at h
  refine isWeightedHomogeneous_bind₁ (fun v => ?_) h
  simpa [smul_eq_mul, mul_comm] using isWH_lawVar k c Y v

end LSG.MEB
