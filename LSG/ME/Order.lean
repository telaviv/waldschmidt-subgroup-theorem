import Mathlib
import LSG.ME.Deriv
import LSG.ME.OrderId

/-!
# Order of vanishing along `W`, chart-free (STAGE2 §3)

**Design correction.** `Deriv.VanishesAlong` uses the chart derivations `Dw ch w` at *every* cone
representative `λ · rep g`. These are not homogeneous: the linear part has degree `0` and the
elliptic part degree `+1` in each elliptic block, so at `λ · rep g` the derivation `Dw ch w` acts as
`ξ ∂ + λ ζ D` (not `ξ ∂ + ζ D`). Vanishing for all `λ` therefore forces vanishing along the
"split hull" of `W`, which is much stronger than vanishing along `W` (example, `d₀ = m = 1`,
`w = (1, 1)`, `g = (x₀, (u₀ : v₀ : 1))`: `P = (U − u₀W) − v₀(X − x₀)W` vanishes to order `2`
along `W` at `g`, but `Dw w P = −v₀W + VW` is `v₀ λ (λ − 1) ≠ 0` at `λ · rep g`).

Here we use the **homogenized derivations** `Dh ch w = Lc · D_lin + Σₖ ζₖ (Lc / Lₖ) δₖ`
(`Lc = ∏ₖ Lₖ` the product of the chart forms), homogeneous of degree `1` in every elliptic block.
At a point where all chart forms are nonzero, `Dh ch w` is a unit multiple of the invariant
derivation `D_w`, uniformly in `λ`.

* `Dh`, `Dh_mem_FLE` (degree shift `ellOnes`, as for `Dw`), `Dh_IG`.
* `IsHomE P d`: `P` is homogeneous of degree `d k` in the `k`-th elliptic block. `Dh` raises every
  degree by `1` (`IsHomE.Dh`); Euler's identity (`euler`).
* `VO1 ch W n J`: `{x | D_l x ∈ J for all words l ⊆ W, |l| ≤ n}` (chart `ch`), an ideal.
* `sat`: cancelling a factor that does not vanish at the cone representatives of `g`.
* **`Dh_mem_VO1_chartAt`** (chart change): for `x` homogeneous with `x ∈ VO1 (chartAt g) W (n+1)`,
  every `Dh ch w x` (any chart `ch`, `w ∈ W`) lies in `VO1 (chartAt g) W n`.
* `VanAll W P n g` (order `> n` along `W` at `g`, all charts, all `λ`) and `VanCan` (canonical
  charts); **`vanAll_iff_vanCan`** for homogeneous `P`; `DL_mem_VO1_chartAt` (mixed words).

Translation invariance is in `LSG.ME.OrderTransl`.
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE S bdeg mul_mem_FLE FLE_mono DL DL_cons prod_mem_FLE')

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ}

/-! ### Generalities -/

section General

variable {σ : Type*} [Fintype σ]

/-- `mkDerivation f = Σ_v f v · ∂/∂X_v`. -/
theorem mkDerivation_eq_sum (f : σ → MvPolynomial σ K) (P : MvPolynomial σ K) :
    mkDerivation K f P = ∑ v, f v * pderiv v P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [pderiv_C, mul_zero, Finset.sum_const_zero]
    rw [← algebraMap_eq]; exact Derivation.map_algebraMap _ _
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e : ∀ x, pderiv x (p * X v) =
        p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v + X v * pderiv x p := by
      intro x; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp_rw [e]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, mkDerivation_X]
    have e1 : ∑ x, f x * (p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v) = p * f v := by
      rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb)]; ring)
        (by simp)]
      simp only [Pi.single_eq_same]; ring
    have e2 : ∑ x, f x * (X v * pderiv x p) = X v * ∑ x, f x * pderiv x p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
    simp only [mul_add, Finset.sum_add_distrib, e1, e2]

/-- **Chain rule** for a derivation and a substitution. -/
theorem derivation_aeval (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (f : σ → MvPolynomial σ K) (Q : MvPolynomial σ K) :
    D (aeval f Q) = ∑ v, aeval f (pderiv v Q) * D (f v) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, aeval_C]
    exact Derivation.map_algebraMap _ _
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e : ∀ x, pderiv x (p * X v) =
        p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v + X v * pderiv x p := by
      intro x; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp_rw [e]
    rw [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    have e1 : ∑ x, aeval f (p * (Pi.single x (1 : MvPolynomial σ K) : σ → _) v) * D (f x) =
        aeval f p * D (f v) := by
      rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp)
        (by simp)]
      simp
    have e2 : ∑ x, aeval f (X v * pderiv x p) * D (f x) =
        f v * ∑ x, aeval f (pderiv x p) * D (f x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by rw [map_mul, aeval_X]; ring
    simp only [map_add, add_mul, Finset.sum_add_distrib, e1, e2]

omit [Fintype σ] in
/-- Derivatives of weighted homogeneous polynomials, times a weighted homogeneous factor. -/
theorem isWH_mul_pderiv {w : σ → ℕ} {φ g : MvPolynomial σ K} {n s : ℕ} {i : σ}
    (hφ : φ.IsWeightedHomogeneous w n) (hg : g.IsWeightedHomogeneous w (w i + s)) :
    (g * pderiv i φ).IsWeightedHomogeneous w (n + s) := by
  by_cases hle : w i ≤ n
  · have := hφ.pderiv (i := i) (n' := n - w i) (by omega)
    have h := hg.mul this
    rwa [show w i + s + (n - w i) = n + s by omega] at h
  · have h0 : pderiv i φ = 0 := by
      rw [φ.as_sum, map_sum]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hw := hφ (mem_support_iff.mp hd)
      have hdi : d i = 0 := by
        by_contra h
        have := Finsupp.le_weight_of_ne_zero' w h
        omega
      rw [pderiv_monomial, hdi, Nat.cast_zero, mul_zero, monomial_zero]
    rw [h0, mul_zero]
    exact isWeightedHomogeneous_zero _ _ _

omit [Fintype σ] in
/-- A derivation raising weights by `s` on the variables raises all weights by `s`. -/
theorem isWH_mkDerivation [Finite σ] {w : σ → ℕ} {f : σ → MvPolynomial σ K} {s n : ℕ}
    (hf : ∀ v, (f v).IsWeightedHomogeneous w (w v + s)) {x : MvPolynomial σ K}
    (hx : x.IsWeightedHomogeneous w n) : (mkDerivation K f x).IsWeightedHomogeneous w (n + s) := by
  have := Fintype.ofFinite σ
  rw [mkDerivation_eq_sum]
  exact IsWeightedHomogeneous.sum _ _ _ fun v _ => isWH_mul_pderiv hx (hf v)

omit [Fintype σ] in
/-- Coefficients after scaling `X_v ↦ t^{w v} X_v`. -/
theorem coeff_scale (w : σ → ℕ) (t : K) (P : MvPolynomial σ K) (d : σ →₀ ℕ) :
    (aeval (fun v => C (t ^ w v) * X v) P).coeff d =
      t ^ Finsupp.weight w d * P.coeff d := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n a =>
    rw [aeval_monomial]
    have e : (n.prod fun v e => (C (t ^ w v) * X v : MvPolynomial σ K) ^ e) =
        C (t ^ Finsupp.weight w n) * monomial n 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
        Finsupp.prod, ← Finset.prod_pow_eq_pow_sum, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_pow, ← map_pow, ← pow_mul, smul_eq_mul, mul_comm (n v)]
    rw [e, algebraMap_eq, ← mul_assoc, ← C_mul, coeff_C_mul, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hp, hq, mul_add]

omit [Fintype σ] in
/-- **Homogeneity from scaling by `2`** (characteristic `0`). -/
theorem isWH_of_scale [CharZero K] (w : σ → ℕ) {P : MvPolynomial σ K} {N : ℕ}
    (h : aeval (fun v => C ((2 : K) ^ w v) * X v) P = C ((2 : K) ^ N) * P) :
    P.IsWeightedHomogeneous w N := by
  intro d hd
  have := congrArg (fun p : MvPolynomial σ K => p.coeff d) h
  rw [coeff_scale, coeff_C_mul] at this
  have h2 : (2 : K) ^ Finsupp.weight w d = 2 ^ N := mul_right_cancel₀ hd this
  have h2' : ((2 ^ Finsupp.weight w d : ℕ) : K) = ((2 ^ N : ℕ) : K) := by push_cast; exact h2
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2')

end General

/-! ### Elliptic weights and homogeneity -/

/-- The weight of the `k`-th elliptic block. -/
def wk (k : Fin m) : Var d₀ d₁ m → ℕ
  | .e j _ => if j = k then 1 else 0
  | _ => 0

@[simp] theorem wk_x (k : Fin m) (i : Fin d₀) : wk k (.x i : Var d₀ d₁ m) = 0 := rfl
@[simp] theorem wk_y (k : Fin m) (j : Fin d₁) : wk k (.y j : Var d₀ d₁ m) = 0 := rfl
@[simp] theorem wk_z (k : Fin m) (j : Fin d₁) : wk k (.z j : Var d₀ d₁ m) = 0 := rfl
@[simp] theorem wk_e (k j : Fin m) (c : Fin 3) :
    wk k (.e j c : Var d₀ d₁ m) = if j = k then 1 else 0 := rfl

/-- `P` is homogeneous of degree `d k` in the `k`-th elliptic block, for every `k`. -/
def IsHomE (P : MvPolynomial (Var d₀ d₁ m) K) (d : Fin m → ℕ) : Prop :=
  ∀ k, P.IsWeightedHomogeneous (wk k) (d k)

/-- **Euler's identity** in the `k`-th elliptic block. -/
theorem euler {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d) (k : Fin m) :
    ∑ v, wk k v • (X v * pderiv v P) = d k • P :=
  (hP k).sum_weight_X_mul_pderiv

/-! ### Homogenized derivations -/

/-- The product of the chart forms. -/
noncomputable def Lc (d₀ d₁ : ℕ) (ch : Fin m → Fin 3) : MvPolynomial (Var d₀ d₁ m) K :=
  ∏ j, X (.e j (ch j))

/-- The product of the chart forms other than the `k`-th. -/
noncomputable def Lo (d₀ d₁ : ℕ) (ch : Fin m → Fin 3) (k : Fin m) : MvPolynomial (Var d₀ d₁ m) K :=
  ∏ j ∈ Finset.univ.erase k, X (.e j (ch j))

theorem Lc_eq (ch : Fin m → Fin 3) (k : Fin m) :
    (Lc d₀ d₁ ch : MvPolynomial (Var d₀ d₁ m) K) = X (.e k (ch k)) * Lo d₀ d₁ ch k :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm

/-- The multiplier of `dval` in `Dh`: `Lo k` on block `k`, `Lc` on the other variables. -/
noncomputable def mult (ch : Fin m → Fin 3) : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) K
  | .e k _ => Lo d₀ d₁ ch k
  | _ => Lc d₀ d₁ ch

variable (g₂ g₃ : Fin m → K)

/-- The values of `Dh` on the variables. -/
noncomputable def dvalh (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    MvPolynomial (Var d₀ d₁ m) K :=
  mult ch v * dval g₂ g₃ ch w v

/-- **The homogenized derivation** `Dh ch w = Lc · D_lin + Σₖ ζₖ Loₖ δₖ`. -/
noncomputable def Dh (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) :
    Derivation K (MvPolynomial (Var d₀ d₁ m) K) (MvPolynomial (Var d₀ d₁ m) K) :=
  mkDerivation K (dvalh g₂ g₃ ch w)

variable {g₂ g₃}

@[simp] theorem Dh_X (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    Dh g₂ g₃ ch w (X v) = dvalh g₂ g₃ ch w v := mkDerivation_X _ _ _

@[simp] theorem Dh_C (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (a : K) :
    Dh g₂ g₃ ch w (C a) = 0 := by
  rw [← algebraMap_eq]; exact Derivation.map_algebraMap _ _

theorem Dh_eq_sum (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) K) :
    Dh g₂ g₃ ch w P = ∑ v, dvalh g₂ g₃ ch w v * pderiv v P := mkDerivation_eq_sum _ _

/-! #### Block degrees -/

theorem sum_single_e : (∑ j, Pi.single (Blk.e j) 1 : Blk m → ℕ) = ellOnes := by
  funext b
  cases b <;> simp [ellOnes, Finset.sum_apply, Pi.single_apply]

theorem Lc_mem_FLE (ch : Fin m → Fin 3) :
    (Lc d₀ d₁ ch : MvPolynomial (Var d₀ d₁ m) K) ∈ FLE K blk ellOnes := by
  rw [← sum_single_e]
  exact prod_mem_FLE' _ _ _ fun j _ => fle_X (K := K) (Var.e j (ch j) : Var d₀ d₁ m)

theorem Lo_mem_FLE (ch : Fin m → Fin 3) (k : Fin m) :
    (Lo d₀ d₁ ch k : MvPolynomial (Var d₀ d₁ m) K) ∈
      FLE K blk (∑ j ∈ Finset.univ.erase k, Pi.single (Blk.e j) 1) :=
  prod_mem_FLE' _ _ _ fun j _ => fle_X (K := K) (Var.e j (ch j) : Var d₀ d₁ m)

theorem dvalh_mem (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    dvalh g₂ g₃ ch w v ∈ FLE K blk (Pi.single (blk v) 1 + ellOnes) := by
  classical
  cases v with
  | e k c =>
    refine fle_le (mul_mem_FLE K (Lo_mem_FLE ch k)
      (mul_mem_FLE K (fle_C (D := 0) _) (chartPoly_mem (ch k) k c))) ?_
    intro b
    have h := Finset.add_sum_erase Finset.univ (fun j => (Pi.single (Blk.e j) 1 : Blk m → ℕ))
      (Finset.mem_univ k)
    rw [sum_single_e] at h
    have hb := congrFun h b
    simp only [Pi.add_apply, Finset.sum_apply] at hb ⊢
    cases b with
    | e k' => by_cases hk : k' = k <;> simp_all [Pi.single_apply, ellOnes]
    | _ => simp_all [ellOnes]
  | x i =>
    exact fle_le (mul_mem_FLE K (Lc_mem_FLE ch) (fle_C (D := 0) _)) (by simp)
  | y j =>
    refine fle_le (mul_mem_FLE K (Lc_mem_FLE ch) (mul_mem_FLE K (fle_C (D := 0) _)
      (fle_X (Var.y j)))) ?_
    simp [add_comm]
  | z j =>
    refine fle_le (mul_mem_FLE K (Lc_mem_FLE ch) (fle_neg (mul_mem_FLE K (fle_C (D := 0) _)
      (fle_X (Var.z j))))) ?_
    simp [add_comm]

/-- **`Dh` raises elliptic block degrees by at most `1`** and does not raise the others. -/
theorem Dh_mem_FLE (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) :
    Dh g₂ g₃ ch w P ∈ FLE K blk (D + ellOnes) :=
  mkDerivation_mem_FLE (dvalh_mem ch w) hP

theorem DLh_mem_FLE (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m)) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) :
    DL (Dh g₂ g₃ ch) l P ∈ FLE K blk (D + l.length • ellOnes) := by
  induction l generalizing D P with
  | nil => simpa using hP
  | cons w l ih =>
    rw [DL_cons]
    have := ih (Dh_mem_FLE (g₂ := g₂) (g₃ := g₃) ch w hP)
    rwa [List.length_cons, add_smul, one_smul, add_comm (l.length • ellOnes), ← add_assoc]

/-! #### `I_G` -/

theorem Dh_Fk (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (k : Fin m) :
    Dh g₂ g₃ ch w (Fk g₂ g₃ d₀ d₁ k) = Lo d₀ d₁ ch k * Dw g₂ g₃ ch w (Fk g₂ g₃ d₀ d₁ k) := by
  simp only [Fk, F, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, Dh_X, Dw_X,
    Dh_C, Dw_C, D_ofNat, smul_eq_mul, nsmul_eq_mul, dvalh, mult]
  ring

theorem Dh_YZ (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (j : Fin d₁) :
    Dh g₂ g₃ ch w (YZ K d₀ m j) = 0 := by
  simp only [YZ, map_sub, Derivation.leibniz, Dh_X, dvalh, mult, dval, smul_eq_mul,
    Derivation.map_one_eq_zero]
  ring

/-- **`Dh` maps `I_G` into `I_G`.** -/
theorem Dh_IG (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m)
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) :
    Dh g₂ g₃ ch w P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  rw [IG, Ideal.ofList] at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · rw [Dh_YZ]; exact Ideal.zero_mem _
    · rw [Dh_Fk, Dw_Fk h2]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Fk_mem_IG g₂ g₃ k))
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx')

theorem DLh_IG (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m))
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) :
    DL (Dh g₂ g₃ ch) l P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  induction l generalizing P with
  | nil => simpa using hP
  | cons w l ih => rw [DL_cons]; exact ih (Dh_IG h2 ch w hP)

/-! #### Homogeneity -/

theorem isWH_mul' {σ : Type*} {w : σ → ℕ} {a b : MvPolynomial σ K} {i j N : ℕ}
    (ha : a.IsWeightedHomogeneous w i) (hb : b.IsWeightedHomogeneous w j) (h : i + j = N) :
    (a * b).IsWeightedHomogeneous w N := h ▸ ha.mul hb

theorem Lc_isWH (ch : Fin m → Fin 3) (k : Fin m) :
    (Lc d₀ d₁ ch : MvPolynomial (Var d₀ d₁ m) K).IsWeightedHomogeneous (wk k) 1 := by
  have := IsWeightedHomogeneous.prod (R := K) (w := wk k) Finset.univ
    (fun j => (X (.e j (ch j)) : MvPolynomial (Var d₀ d₁ m) K)) (fun j => wk k (.e j (ch j)))
    fun j _ => isWeightedHomogeneous_X _ _ _
  rw [Lc]; simpa [Finset.sum_ite_eq'] using this

theorem Lo_isWH (ch : Fin m → Fin 3) (k k' : Fin m) :
    (Lo d₀ d₁ ch k' : MvPolynomial (Var d₀ d₁ m) K).IsWeightedHomogeneous (wk k)
      (if k' = k then 0 else 1) := by
  have := IsWeightedHomogeneous.prod (R := K) (w := wk k) (Finset.univ.erase k')
    (fun j => (X (.e j (ch j)) : MvPolynomial (Var d₀ d₁ m) K)) (fun j => wk k (.e j (ch j)))
    fun j _ => isWeightedHomogeneous_X _ _ _
  rw [Lo]
  convert this using 1
  simp only [wk_e, Finset.sum_ite_eq', Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
  rcases eq_or_ne k' k with rfl | h
  · simp
  · simp [h, Ne.symm h]

section CharZero

variable [CharZero K]

theorem chartPoly_isWH (a : Fin 3) (k k' : Fin m) (c : Fin 3) :
    (chartPoly g₂ g₃ d₀ d₁ a k' c).IsWeightedHomogeneous (wk k) (if k' = k then 2 else 0) := by
  apply isWH_of_scale
  by_cases hk : k' = k
  · subst hk
    fin_cases a <;> fin_cases c <;>
      simp [chartPoly, chartU, chartV, chartW, map_ofNat] <;> ring
  · fin_cases a <;> fin_cases c <;>
      simp [chartPoly, chartU, chartV, chartW, map_ofNat, hk]

theorem dvalh_isWH (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) (k : Fin m) :
    (dvalh g₂ g₃ ch w v).IsWeightedHomogeneous (wk k) (wk k v + 1) := by
  cases v with
  | x i => exact isWH_mul' (Lc_isWH ch k) (isWeightedHomogeneous_C _ _) (by simp)
  | y j => exact isWH_mul' (Lc_isWH ch k) (isWH_mul' (isWeightedHomogeneous_C _ _)
      (isWeightedHomogeneous_X _ _ _) rfl) (by simp)
  | z j => exact isWH_mul' (Lc_isWH ch k) (isWH_mul' (isWeightedHomogeneous_C _ _)
      (isWeightedHomogeneous_X _ _ _) rfl).neg (by simp)
  | e k' c =>
    refine isWH_mul' (Lo_isWH ch k k') (isWH_mul' (isWeightedHomogeneous_C _ _)
      (chartPoly_isWH (ch k') k k' c) rfl) ?_
    by_cases h : k' = k <;> simp [h]

/-- **`Dh` raises every elliptic degree by `1`.** -/
theorem isHomE_Dh {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d)
    (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) : IsHomE (Dh g₂ g₃ ch w P) (d + 1) :=
  fun k => isWH_mkDerivation (fun v => dvalh_isWH ch w v k) (hP k)

theorem isHomE_DL {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d)
    (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m)) :
    IsHomE (DL (Dh g₂ g₃ ch) l P) (d + l.length) := by
  induction l generalizing P d with
  | nil => simpa using hP
  | cons w l ih =>
    rw [DL_cons]
    have := ih (isHomE_Dh (g₂ := g₂) (g₃ := g₃) hP ch w)
    rwa [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm (l.length : Fin m → ℕ),
      ← add_assoc]

end CharZero

/-! ### Vanishing to order `> n` modulo an ideal, along words -/

section VOg

variable {R ι : Type*} [CommRing R] [Algebra K R] (Dv : ι → Derivation K R R) (W : Set ι)
  (J : Ideal R)

theorem VOg_mul : ∀ (n : ℕ) (a x : R), (∀ l : List ι, (∀ w ∈ l, w ∈ W) → l.length ≤ n →
      DL Dv l x ∈ J) →
    ∀ l : List ι, (∀ w ∈ l, w ∈ W) → l.length ≤ n → DL Dv l (a * x) ∈ J := by
  intro n
  induction n with
  | zero =>
    intro a x hx l _ hl
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact J.mul_mem_left a (hx [] (by simp) le_rfl)
  | succ n ih =>
    intro a x hx l hlW hl
    cases l with
    | nil => exact J.mul_mem_left a (hx [] (by simp) (Nat.zero_le _))
    | cons w l =>
      have hw : w ∈ W := hlW w List.mem_cons_self
      have hlW' : ∀ w ∈ l, w ∈ W := fun v hv => hlW v (List.mem_cons_of_mem _ hv)
      have hl' : l.length ≤ n := by simpa using hl
      rw [DL_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add]
      have hA : DL Dv l (a * Dv w x) ∈ J := by
        refine ih a (Dv w x) (fun l' hl'W hl'n => ?_) l hlW' hl'
        rw [← DL_cons]
        exact hx _ (fun v hv => (List.mem_cons.mp hv).elim (· ▸ hw) (hl'W v))
          (by simp only [List.length_cons]; omega)
      have hB : DL Dv l (Dv w a * x) ∈ J :=
        ih (Dv w a) x (fun l' hl'W hl'n => hx l' hl'W (by omega)) l hlW' hl'
      rw [mul_comm x]
      exact J.add_mem hA hB

/-- `{x | D_l x ∈ J for all words l in W of length ≤ n}`. -/
def VOg (n : ℕ) : Ideal R where
  carrier := {x | ∀ l : List ι, (∀ w ∈ l, w ∈ W) → l.length ≤ n → DL Dv l x ∈ J}
  add_mem' hx hy l hlW hl := by rw [map_add]; exact J.add_mem (hx l hlW hl) (hy l hlW hl)
  zero_mem' l _ _ := by rw [map_zero]; exact J.zero_mem
  smul_mem' a x hx := VOg_mul Dv W J _ a x hx

variable {Dv W J}

theorem mem_VOg {n : ℕ} {x : R} : x ∈ VOg Dv W J n ↔
    ∀ l : List ι, (∀ w ∈ l, w ∈ W) → l.length ≤ n → DL Dv l x ∈ J := Iff.rfl

theorem mem_VOg_zero {x : R} : x ∈ VOg Dv W J 0 ↔ x ∈ J := by
  refine ⟨fun h => h [] (by simp) le_rfl, fun h l _ hl => ?_⟩
  rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]; exact h

theorem mem_VOg_succ {n : ℕ} {x : R} :
    x ∈ VOg Dv W J (n + 1) ↔ x ∈ J ∧ ∀ w ∈ W, Dv w x ∈ VOg Dv W J n := by
  constructor
  · intro h
    exact ⟨h [] (by simp) (Nat.zero_le _), fun w hw l hlW hl =>
      h (w :: l) (fun v hv => (List.mem_cons.mp hv).elim (· ▸ hw) (hlW v)) (by simp; omega)⟩
  · rintro ⟨h0, h⟩ l hlW hl
    cases l with
    | nil => exact h0
    | cons w l =>
      exact h w (hlW w List.mem_cons_self) l (fun v hv => hlW v (List.mem_cons_of_mem _ hv))
        (by simpa using hl)

theorem VOg_succ_le (n : ℕ) : VOg Dv W J (n + 1) ≤ VOg Dv W J n :=
  fun _ hx l hlW hl => hx l hlW (by omega)

theorem VOg_anti {n n' : ℕ} (h : n ≤ n') : VOg Dv W J n' ≤ VOg Dv W J n :=
  fun _ hx l hlW hl => hx l hlW (by omega)

theorem VOg_le (n : ℕ) : VOg Dv W J n ≤ J := fun _ hx => hx [] (by simp) (Nat.zero_le _)

theorem VOg_mono {n : ℕ} {J' : Ideal R} (h : J ≤ J') : VOg Dv W J n ≤ VOg Dv W J' n :=
  fun _ hx l hlW hl => h (hx l hlW hl)

/-- Words of length `≤ a` map order `> a + b` to order `> b`. -/
theorem DL_mem_VOg {a b : ℕ} {x : R} (hx : x ∈ VOg Dv W J (a + b)) (l : List ι)
    (hlW : ∀ w ∈ l, w ∈ W) (hl : l.length ≤ a) : DL Dv l x ∈ VOg Dv W J b := by
  induction l generalizing a x with
  | nil => exact VOg_anti (by omega) hx
  | cons w l ih =>
    rw [DL_cons]
    have hw := hlW w List.mem_cons_self
    have hl' : l.length ≤ a - 1 := by simp at hl; omega
    refine ih ?_ (fun v hv => hlW v (List.mem_cons_of_mem _ hv)) hl'
    have : a + b = (a - 1 + b) + 1 := by simp at hl; omega
    rw [this] at hx
    exact (mem_VOg_succ.mp hx).2 w hw

end VOg

variable (g₂ g₃) in
/-- `VO1 ch W n J`: order `> n` along `W` modulo `J`, in the chart `ch`. -/
noncomputable abbrev VO1 (ch : Fin m → Fin 3) (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ)
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  VOg (Dh g₂ g₃ ch) (W : Set (LieE K d₀ d₁ m)) J n

theorem IG_le_VO1 (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (W : Submodule K (LieE K d₀ d₁ m))
    (n : ℕ) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ VO1 g₂ g₃ ch W n (vanish E) :=
  fun _ hx l _ _ => IG_le_vanish h2 E (DLh_IG h2 ch l hx)

theorem mem_vanish_singleton {g : GPt K d₀ d₁ g₂ g₃} {P : MvPolynomial (Var d₀ d₁ m) K} :
    P ∈ vanish {g} ↔ ∀ lam, eval (coords g lam) P = 0 := by
  rw [mem_vanish]; simp

/-- **Saturation**: a factor that does not vanish at the cone representatives of `g` can be
cancelled. -/
theorem sat (ch : Fin m → Fin 3) (W : Submodule K (LieE K d₀ d₁ m)) {g : GPt K d₀ d₁ g₂ g₃}
    {u : MvPolynomial (Var d₀ d₁ m) K} (hu : ∀ lam, eval (coords g lam) u ≠ 0) :
    ∀ (n : ℕ) (y : MvPolynomial (Var d₀ d₁ m) K), u * y ∈ VO1 g₂ g₃ ch W n (vanish {g}) →
      y ∈ VO1 g₂ g₃ ch W n (vanish {g}) := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [mem_VOg_zero, mem_vanish_singleton] at hy ⊢
    intro lam
    have := hy lam
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).resolve_left (hu lam)
  | succ n ih =>
    intro y hy
    have hy' : y ∈ VO1 g₂ g₃ ch W n (vanish {g}) := ih y (VOg_succ_le n hy)
    rw [mem_VOg_succ] at hy ⊢
    refine ⟨VOg_le n hy', fun w hw => ih _ ?_⟩
    have h1 := hy.2 w hw
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := Ideal.mul_mem_left _ (Dh g₂ g₃ ch w u) hy'
    have := Ideal.sub_mem _ h1 h2
    rwa [mul_comm y, add_sub_cancel_right] at this

theorem eval_Lc (ch : Fin m → Fin 3) (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) :
    eval (coords g lam) (Lc d₀ d₁ ch) = ∏ j, (lam j : K) * rep (g.2.2 j) (ch j) := by
  simp [Lc, coords]

theorem eval_Lc_chartAt_ne (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) :
    eval (coords g lam) (Lc d₀ d₁ (chartAt g)) ≠ 0 := by
  rw [eval_Lc]
  simp [rep_chartAt, Finset.prod_ne_zero_iff]

/-! ### Chart change -/

/-- `2 · chartPoly = c2` (`c2` has integral coefficients). -/
theorem c2_eq (h2 : (2 : K) ≠ 0) (a : Fin 3) (k : Fin m) (c : Fin 3) :
    c2 a (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) c = 2 * chartPoly g₂ g₃ d₀ d₁ a k c := by
  have hh := two_mul_C_half (d₀ := d₀) (d₁ := d₁) (m := m) h2
  fin_cases a <;> fin_cases c <;>
    simp only [c2, chartPoly, chartU, chartV, chartW, bvars, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_zero]
  · ring
  · linear_combination (-(3 * X (Var.e k 1) ^ 2 + 3 * X (Var.e k 2) ^ 2 * C (g₃ k))) * hh
  · linear_combination (X (Var.e k 1) ^ 2 + 3 * X (Var.e k 2) ^ 2 * C (g₃ k)) * hh
  · linear_combination (-(X (Var.e k 2) ^ 2 * C (g₂ k))) * hh
  · ring
  · linear_combination (X (Var.e k 2) ^ 2 * C (g₂ k)) * hh

theorem chartPoly_eq_half (h2 : (2 : K) ≠ 0) (a : Fin 3) (k : Fin m) (c : Fin 3) :
    chartPoly g₂ g₃ d₀ d₁ a k c = C (1 / 2) * c2 a (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) c := by
  rw [c2_eq h2, ← mul_assoc, mul_comm (C (1 / 2)), two_mul_C_half h2, one_mul]

theorem Fv_bvars (k : Fin m) :
    Fv (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) =
      (Fk g₂ g₃ d₀ d₁ k : MvPolynomial (Var d₀ d₁ m) K) := by
  simp [Fv, Fk, bvars]

variable (g₂ g₃) in
/-- The Euler coefficient of the chart change `ch₀ → ch` in block `k`. -/
noncomputable def ae (ch₀ ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (k : Fin m) :
    MvPolynomial (Var d₀ d₁ m) K :=
  C (w.2.2 k) * Lo d₀ d₁ ch k * Lo d₀ d₁ ch₀ k * C (1 / 2) *
    ccE (ch₀ k) (ch k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)

theorem chg_var (h2 : (2 : K) ≠ 0) (ch₀ ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m)
    (v : Var d₀ d₁ m) : ∃ G ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃,
      Lc d₀ d₁ ch₀ * dvalh g₂ g₃ ch w v - Lc d₀ d₁ ch * dvalh g₂ g₃ ch₀ w v =
        ∑ k, wk k v • (ae g₂ g₃ ch₀ ch w k * X v) + G := by
  cases v with
  | e k c =>
    obtain ⟨f, hf⟩ := cc_eq (ch₀ k) (ch k) c (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)
    rw [Fv_bvars] at hf
    refine ⟨C (w.2.2 k) * Lo d₀ d₁ ch k * Lo d₀ d₁ ch₀ k * C (1 / 2) * f * Fk g₂ g₃ d₀ d₁ k,
      Ideal.mul_mem_left _ _ (Fk_mem_IG g₂ g₃ k), ?_⟩
    simp only [wk_e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [bvars] at hf
    rw [Lc_eq ch₀ k, Lc_eq ch k]
    simp only [dvalh, mult, dval, chartPoly_eq_half h2, ae]
    linear_combination (C (w.2.2 k) * Lo d₀ d₁ ch k * Lo d₀ d₁ ch₀ k * C (1 / 2)) * hf
  | x i => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval]; ring⟩
  | y j => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval]; ring⟩
  | z j => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval]; ring⟩

/-- **Chart change identity**: `Lc₀ · Dh_ch − Lc · Dh_{ch₀} = Σₖ aeₖ · Eulerₖ` modulo `I_G`. -/
theorem chg (h2 : (2 : K) ≠ 0) (ch₀ ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m)
    {x : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hx : IsHomE x d) :
    Lc d₀ d₁ ch₀ * Dh g₂ g₃ ch w x - Lc d₀ d₁ ch * Dh g₂ g₃ ch₀ w x -
      ∑ k, ae g₂ g₃ ch₀ ch w k * (d k • x) ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  choose G hG hGe using chg_var (g₂ := g₂) (g₃ := g₃) h2 ch₀ ch w
  have e1 : Lc d₀ d₁ ch₀ * Dh g₂ g₃ ch w x - Lc d₀ d₁ ch * Dh g₂ g₃ ch₀ w x =
      ∑ v, (Lc d₀ d₁ ch₀ * dvalh g₂ g₃ ch w v - Lc d₀ d₁ ch * dvalh g₂ g₃ ch₀ w v) *
        pderiv v x := by
    rw [Dh_eq_sum, Dh_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e3 : ∑ v, (∑ k, wk k v • (ae g₂ g₃ ch₀ ch w k * X v)) * pderiv v x =
      ∑ k, ae g₂ g₃ ch₀ ch w k * (d k • x) := by
    calc ∑ v, (∑ k, wk k v • (ae g₂ g₃ ch₀ ch w k * X v)) * pderiv v x
        = ∑ v, ∑ k, ae g₂ g₃ ch₀ ch w k * (wk k v • (X v * pderiv v x)) :=
          Finset.sum_congr rfl fun v _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by
              rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = ∑ k, ∑ v, ae g₂ g₃ ch₀ ch w k * (wk k v • (X v * pderiv v x)) := Finset.sum_comm
      _ = ∑ k, ae g₂ g₃ ch₀ ch w k * (d k • x) :=
          Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum, euler hx k]
  have e2 : Lc d₀ d₁ ch₀ * Dh g₂ g₃ ch w x - Lc d₀ d₁ ch * Dh g₂ g₃ ch₀ w x -
      ∑ k, ae g₂ g₃ ch₀ ch w k * (d k • x) = ∑ v, G v * pderiv v x := by
    rw [e1, ← e3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hGe v]; ring
  rw [e2]
  exact Ideal.sum_mem _ fun v _ => Ideal.mul_mem_right _ _ (hG v)

/-- **Chart change** (key step): derivatives in any chart lower the canonical order by one. -/
theorem Dh_mem_VO1_chartAt (h2 : (2 : K) ≠ 0) (W : Submodule K (LieE K d₀ d₁ m))
    {g : GPt K d₀ d₁ g₂ g₃} {n : ℕ} {x : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hx : IsHomE x d) (hxv : x ∈ VO1 g₂ g₃ (chartAt g) W (n + 1) (vanish {g}))
    (ch : Fin m → Fin 3) {w : LieE K d₀ d₁ m} (hw : w ∈ W) :
    Dh g₂ g₃ ch w x ∈ VO1 g₂ g₃ (chartAt g) W n (vanish {g}) := by
  refine sat (chartAt g) W (eval_Lc_chartAt_ne g) n _ ?_
  have hG := IG_le_VO1 h2 (chartAt g) W n {g} (chg h2 (chartAt g) ch w hx)
  have h1 := Ideal.mul_mem_left _ (Lc d₀ d₁ ch) ((mem_VOg_succ.mp hxv).2 w hw)
  have h3 : ∑ k, ae g₂ g₃ (chartAt g) ch w k * (d k • x) ∈
      VO1 g₂ g₃ (chartAt g) W n (vanish {g}) :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (by
      rw [nsmul_eq_mul]; exact Ideal.mul_mem_left _ _ (VOg_succ_le n hxv))
  have := Ideal.add_mem _ (Ideal.add_mem _ hG h1) h3
  convert this using 1
  ring

section CharZero

variable [CharZero K]

/-- Mixed words: words of length `≤ a` in arbitrary charts lower the canonical order by `a`. -/
theorem DL_mem_VO1_chartAt (h2 : (2 : K) ≠ 0) (W : Submodule K (LieE K d₀ d₁ m))
    {g : GPt K d₀ d₁ g₂ g₃} (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m))
    (hlW : ∀ w ∈ l, w ∈ W) : ∀ {b : ℕ} {x : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ},
      IsHomE x d → x ∈ VO1 g₂ g₃ (chartAt g) W (l.length + b) (vanish {g}) →
      DL (Dh g₂ g₃ ch) l x ∈ VO1 g₂ g₃ (chartAt g) W b (vanish {g}) := by
  induction l with
  | nil => intro b x d _ hxv; simpa using hxv
  | cons w l ih =>
    intro b x d hx hxv
    rw [DL_cons]
    refine ih (fun v hv => hlW v (List.mem_cons_of_mem _ hv)) (isHomE_Dh hx ch w) ?_
    refine Dh_mem_VO1_chartAt h2 W hx ?_ ch (hlW w List.mem_cons_self)
    simpa [List.length_cons, add_assoc, add_comm 1] using hxv

end CharZero

/-! ### The chart-free order of vanishing -/

variable (g₂ g₃) in
/-- **`P` vanishes to order `> n` along `W` at `g`**: all words of length `≤ n` in `W`, in all
charts, vanish at all cone representatives of `g`. -/
def VanAll (W : Submodule K (LieE K d₀ d₁ m)) (P : MvPolynomial (Var d₀ d₁ m) K) (n : ℕ)
    (g : GPt K d₀ d₁ g₂ g₃) : Prop :=
  ∀ ch, P ∈ VO1 g₂ g₃ ch W n (vanish {g})

variable (g₂ g₃) in
/-- The same with the canonical charts at `g` only. -/
def VanCan (W : Submodule K (LieE K d₀ d₁ m)) (P : MvPolynomial (Var d₀ d₁ m) K) (n : ℕ)
    (g : GPt K d₀ d₁ g₂ g₃) : Prop :=
  P ∈ VO1 g₂ g₃ (chartAt g) W n (vanish {g})

/-- **The order of vanishing is chart-free** (homogeneous `P`). -/
theorem vanAll_iff_vanCan [CharZero K] (h2 : (2 : K) ≠ 0) (W : Submodule K (LieE K d₀ d₁ m))
    {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d) (n : ℕ)
    (g : GPt K d₀ d₁ g₂ g₃) : VanAll g₂ g₃ W P n g ↔ VanCan g₂ g₃ W P n g := by
  refine ⟨fun h => h _, fun h ch l hlW hl => ?_⟩
  have := DL_mem_VO1_chartAt h2 W ch l hlW hP (b := 0) (VOg_anti (by omega) h)
  exact mem_VOg_zero.mp this

end LSG.ME
