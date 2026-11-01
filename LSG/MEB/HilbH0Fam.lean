/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.HilbH0Aux

/-!
# The independent family for `H(I(H⁰); t)` (α′; STAGE_A4 §7.3 (6), step 2)

Pure algebra: the family, its block degrees, its evaluation on the lift, and its count. The analytic input
(independence) is in `HilbH0.lean`.

Data: `t₀` linear forms `lp l` (coordinates on `h₀`), `κ` torus coordinates `jj : κ → Fin d₁` (independent modulo
`U`), a pivot set `J` of blocks, and a degree `T = tD₂`. On block `k` put `pivG B J k = g_k` if `k ∈ J`, else `0`,
and `pivM B J T k = T/(pivG+1) + 1`.
* `HIdx`: exponents `(a, b, c, d)` with `a l < M0`, `b k < M1`, `c k < pivM k`, `d k j < pivM k` (`j < pivG k`);
* **`hPoly lp jj (a, b, c, d) = ∏ lp_l^{a_l} · ∏ Y_{jj k}^{b_k} · ∏_k X_{k,i₀}^{c_k} ∏_j X_{k,is j}^{d_kj}`**;
* `HCrd`: target coordinates (`h₀`-coordinates, torus coordinates, and per block `ν_k` and the ratios `r_kj`);
  `hExp`: the exponent of `hPoly` as a monomial in `(·, ·, ν, r)` (`X_{k,i₀} = ν_k`, `X_{k,is j} = ν_k r_kj`);
* **`eval_hPoly`**: the evaluation identity; **`hExp_injective`**; **`hPoly_mem_FLE`**; **`card_HIdx`**;
* **`count_le`**: `(T+1)^{s+m} ≤ cHB B · ∏_k pivM_k^{pivG_k+1}` for `s ≤ Σ_k pivG_k`, `cHB B = ∏_k (g_k+1)^{g_k+1}`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Linear forms on the additive part -/

/-- The polynomial `Σ_j L(e_j) x_j` of a linear form `L`. -/
noncomputable def linPoly (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ j, C (L (Pi.single j 1)) * X (Var.x j)

theorem linPoly_mem_FLE (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) :
    linPoly (d₁ := d₁) (B := B) L ∈ FLE ℂ blk (Pi.single Blk.x 1) := by
  refine Submodule.sum_mem _ fun j _ => ?_
  have := StrongSix.M2.mul_mem_FLE ℂ (C_mem_FLE0 blk (L (Pi.single j 1)))
    (X_mem_FLE (blk (m := m)) (Var.x j : Var d₀ d₁ B))
  rwa [zero_add] at this

theorem eval_linPoly (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    eval (liftZ u μ) (linPoly L) = L u.1 := by
  simp only [linPoly, map_sum, map_mul, eval_C, eval_X, liftZ]
  rw [LinearMap.pi_apply_eq_sum_univ L u.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext i'
  simp [Pi.single_apply, eq_comm]

/-! ### The pivot sizes -/

variable (B) in
/-- `g_k` on pivot blocks, `0` on the others. -/
def pivG (J : Finset (Fin m)) (k : Fin m) : ℕ := if k ∈ J then (B k).g else 0

theorem pivG_le (J : Finset (Fin m)) (k : Fin m) : pivG B J k ≤ (B k).g := by
  unfold pivG; split_ifs <;> omega

theorem pivG_of_mem {J : Finset (Fin m)} {k : Fin m} (hk : k ∈ J) : pivG B J k = (B k).g := if_pos hk

variable (B) in
/-- The exponent range `T/(pivG+1) + 1` on block `k`. -/
def pivM (J : Finset (Fin m)) (T : ℕ) (k : Fin m) : ℕ := T / (pivG B J k + 1) + 1

variable (B) in
/-- The exponents of the family. -/
abbrev HIdx (t₀ M0 : ℕ) (κ : Type) (M1 : ℕ) (J : Finset (Fin m)) (T : ℕ) : Type :=
  (Fin t₀ → Fin M0) × (κ → Fin M1) × (∀ k, Fin (pivM B J T k)) ×
    (∀ k, Fin (pivG B J k) → Fin (pivM B J T k))

variable (B) in
/-- The target coordinates: `h₀`-coordinates, torus coordinates, and per block `ν_k` (`none`) and the ratios. -/
abbrev HCrd (t₀ : ℕ) (κ : Type) (J : Finset (Fin m)) : Type :=
  Fin t₀ ⊕ κ ⊕ (Σ k : Fin m, Option (Fin (pivG B J k)))

variable {t₀ M0 M1 T : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {J : Finset (Fin m)}

/-- **The family.** -/
noncomputable def hPoly (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ) (jj : κ → Fin d₁)
    (i : HIdx B t₀ M0 κ M1 J T) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  (∏ l, lp l ^ (i.1 l : ℕ)) * (∏ k, X (Var.y (jj k)) ^ (i.2.1 k : ℕ)) *
    ∏ k, (X (Var.e k (B k).i₀) ^ (i.2.2.1 k : ℕ) *
      ∏ j, X (Var.e k ((B k).is (Fin.castLE (pivG_le J k) j))) ^ (i.2.2.2 k j : ℕ))

/-- The exponent of `hPoly i` as a monomial in the target coordinates. -/
def hExp (i : HIdx B t₀ M0 κ M1 J T) : HCrd B t₀ κ J → ℕ
  | .inl l => i.1 l
  | .inr (.inl k) => i.2.1 k
  | .inr (.inr ⟨k, none⟩) => i.2.2.1 k + ∑ j, (i.2.2.2 k j : ℕ)
  | .inr (.inr ⟨k, some j⟩) => i.2.2.2 k j

/-- **The evaluation identity**: on a lift whose coordinates are `w` (`X_{k,is j} = ν_k r_kj`), `hPoly i` is the
monomial `w^{hExp i}`. -/
theorem eval_hPoly (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ) (jj : κ → Fin d₁) (u : Tan d₀ d₁ B)
    (μ : Fin m → ℂ) (w : HCrd B t₀ κ J → ℂ)
    (h1 : ∀ l, eval (liftZ u μ) (lp l) = w (.inl l))
    (h2 : ∀ k, Complex.exp (u.2.1 (jj k)) = w (.inr (.inl k)))
    (h3 : ∀ k, μ k * (B k).θ (u.2.2 k) (B k).i₀ = w (.inr (.inr ⟨k, none⟩)))
    (h4 : ∀ k j, μ k * (B k).θ (u.2.2 k) ((B k).is (Fin.castLE (pivG_le J k) j)) =
      w (.inr (.inr ⟨k, none⟩)) * w (.inr (.inr ⟨k, some j⟩)))
    (i : HIdx B t₀ M0 κ M1 J T) :
    eval (liftZ u μ) (hPoly lp jj i) = ∏ s, w s ^ hExp i s := by
  simp only [hPoly, map_mul, map_prod, map_pow, eval_X, h1]
  simp only [liftZ, h2, h3, h4]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [Fintype.prod_option, hExp]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
  ring

theorem hExp_injective : Function.Injective (hExp (B := B) (t₀ := t₀) (M0 := M0) (κ := κ) (M1 := M1)
    (J := J) (T := T)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  have ha : a = a' := funext fun l => Fin.ext (congrFun h (.inl l))
  have hb : b = b' := funext fun k => Fin.ext (congrFun h (.inr (.inl k)))
  have hd : d = d' := funext fun k => funext fun j => Fin.ext (congrFun h (.inr (.inr ⟨k, some j⟩)))
  subst ha hb hd
  have hc : c = c' := funext fun k => Fin.ext (by
    have := congrFun h (.inr (.inr ⟨k, none⟩))
    simp only [hExp] at this
    omega)
  subst hc
  rfl

/-! ### Block degrees -/

theorem sum_fin_le {ι : Type*} [Fintype ι] {M : ℕ} (f : ι → Fin M) :
    ∑ i, (f i : ℕ) ≤ Fintype.card ι * (M - 1) := by
  calc ∑ i, (f i : ℕ) ≤ ∑ _i : ι, (M - 1) := Finset.sum_le_sum fun i _ => by have := (f i).2; omega
    _ = Fintype.card ι * (M - 1) := by simp

theorem div_bound (T n : ℕ) : (n + 1) * (T / (n + 1)) ≤ T := Nat.mul_div_le T (n + 1)

theorem succ_le_div_bound (T n : ℕ) : T + 1 ≤ (n + 1) * (T / (n + 1) + 1) := by
  have h1 := Nat.div_add_mod T (n + 1)
  have h2 := Nat.mod_lt T (by omega : 0 < n + 1)
  rw [Nat.mul_succ]
  generalize (n + 1) * (T / (n + 1)) = P at *
  omega

/-- **Block degrees of the family.** -/
theorem hPoly_mem_FLE (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ)
    (hlp : ∀ l, lp l ∈ FLE ℂ blk (Pi.single Blk.x 1)) (jj : κ → Fin d₁) {D₀ D₁ D₂ t : ℕ}
    (hM0 : t₀ * (M0 - 1) ≤ t * D₀) (hM1 : Fintype.card κ * (M1 - 1) ≤ t * D₁) (hT : T = t * D₂)
    (i : HIdx B t₀ M0 κ M1 J T) :
    hPoly lp jj i ∈ FLE ℂ blk (t • DfunB D₀ D₁ D₂) := by
  obtain ⟨a, b, c, d⟩ := i
  have hA := prod_mem_FLE blk Finset.univ (fun l => lp l ^ (a l : ℕ))
    (fun l => (a l : ℕ) • Pi.single Blk.x 1) fun l _ => pow_mem_FLE blk (hlp l) _
  have hB := prod_mem_FLE blk Finset.univ (fun k => (X (Var.y (jj k)) : MvPolynomial (Var d₀ d₁ B) ℂ) ^
    (b k : ℕ)) (fun k => (b k : ℕ) • Pi.single (Blk.yz : Blk m) 1)
    fun k _ => pow_mem_FLE blk (X_mem_FLE blk (Var.y (jj k) : Var d₀ d₁ B)) _
  have hC := prod_mem_FLE blk Finset.univ (fun k => (X (Var.e k (B k).i₀) : MvPolynomial (Var d₀ d₁ B) ℂ) ^
      (c k : ℕ) * ∏ j, X (Var.e k ((B k).is (Fin.castLE (pivG_le J k) j))) ^ (d k j : ℕ))
    (fun k => (c k : ℕ) • Pi.single (Blk.e k) 1 + ∑ j, (d k j : ℕ) • Pi.single (Blk.e k) 1)
    fun k _ => StrongSix.M2.mul_mem_FLE ℂ
      (pow_mem_FLE blk (X_mem_FLE blk (Var.e k (B k).i₀ : Var d₀ d₁ B)) _)
      (prod_mem_FLE blk Finset.univ _ _ fun j _ =>
        pow_mem_FLE blk (X_mem_FLE blk (Var.e k ((B k).is (Fin.castLE (pivG_le J k) j)) :
          Var d₀ d₁ B)) _)
  refine StrongSix.M2.FLE_mono ℂ blk ?_ (StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ hA hB) hC)
  intro bl
  cases bl with
  | x =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, if_true, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero, DfunB]
    exact (sum_fin_le a).trans (by simpa using hM0)
  | yz =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, if_true, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero, zero_add,
      DfunB]
    exact (sum_fin_le b).trans (by simpa using hM1)
  | e k =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add, Blk.e.injEq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, DfunB, smul_eq_mul]
    rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true]
    have h1 : (c k : ℕ) ≤ pivM B J T k - 1 := by have := (c k).2; omega
    have h2 := sum_fin_le (d k)
    simp only [Fintype.card_fin] at h2
    have h3 := div_bound T (pivG B J k)
    simp only [pivM, Nat.add_sub_cancel] at h1 h2
    rw [← hT]
    nlinarith

theorem card_HIdx : Fintype.card (HIdx B t₀ M0 κ M1 J T) =
    M0 ^ t₀ * M1 ^ Fintype.card κ * ∏ k, pivM B J T k ^ (pivG B J k + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_pi, pow_succ,
    Finset.prod_mul_distrib]
  ring

variable (B) in
/-- The constant `∏_k (g_k+1)^{g_k+1}`. -/
def cHB : ℕ := ∏ k, ((B k).g + 1) ^ ((B k).g + 1)

theorem one_le_cHB : 1 ≤ cHB B :=
  Finset.one_le_prod' fun k _ => Nat.one_le_pow _ _ (Nat.succ_pos _)

/-- **The count**: `(T+1)^{s+m} ≤ cHB B · ∏_k pivM_k^{pivG_k+1}` for `s ≤ Σ_k pivG_k`. -/
theorem count_le {s : ℕ} (hs : s ≤ ∑ k, pivG B J k) :
    (T + 1) ^ (s + m) ≤ cHB B * ∏ k, pivM B J T k ^ (pivG B J k + 1) := by
  calc (T + 1) ^ (s + m) ≤ (T + 1) ^ (∑ k, pivG B J k + m) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    _ = ∏ k : Fin m, (T + 1) ^ (pivG B J k + 1) := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
        simp
    _ ≤ ∏ k, (((B k).g + 1) ^ ((B k).g + 1) * pivM B J T k ^ (pivG B J k + 1)) := by
        refine Finset.prod_le_prod fun k _ => ?_
        have hk := pivG_le J k (B := B)
        calc (T + 1) ^ (pivG B J k + 1)
            ≤ ((pivG B J k + 1) * pivM B J T k) ^ (pivG B J k + 1) :=
              Nat.pow_le_pow_left (succ_le_div_bound T _) _
          _ = (pivG B J k + 1) ^ (pivG B J k + 1) * pivM B J T k ^ (pivG B J k + 1) := mul_pow _ _ _
          _ ≤ ((B k).g + 1) ^ ((B k).g + 1) * pivM B J T k ^ (pivG B J k + 1) := by
              refine Nat.mul_le_mul_right _ ?_
              calc (pivG B J k + 1) ^ (pivG B J k + 1) ≤ ((B k).g + 1) ^ (pivG B J k + 1) :=
                    Nat.pow_le_pow_left (by omega) _
                _ ≤ ((B k).g + 1) ^ ((B k).g + 1) :=
                    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    _ = cHB B * ∏ k, pivM B J T k ^ (pivG B J k + 1) := by rw [Finset.prod_mul_distrib, cHB]

end LSG.MEB
