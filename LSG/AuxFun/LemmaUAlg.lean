/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.TaylorK
import LSG.AuxFun.LawSize

/-!
# Lemma U, algebraic side: sizes of the Taylor coefficients of `F_t` (Stage 3, D3b)

`F_t(s) = Σ_l p_l Π_f g_f(s)^{n_{l,f}}` with basic factors `g_f` of base `B`:

* `KS.prod_pow`: a product of powers of basic factors has base `2B` and constant
  `2^{Σ n} Π A_f^{n_f}`;
* **`KS.poly`**: the polynomial `Σ_l p_l Π_f g_f^{n_{l,f}}` with `n_{l,f} ≤ N_f` is
  `KS ((Σ |p_l|) 2^{Σ N} Π A_f^{N_f}) (2B) (Π e_f^{N_f}) δ`;
* basic factors: `ks_lin` (`x + y s`, the `G_a` coordinates), `ks_expm` (`x e^{y s}`, the `G_m`
  coordinates), `ks_quad` (a quadratic form in three series, the elliptic coordinates
  `law(X', ξ(s))`).
-/

open Finset

noncomputable section

namespace LSG.Aux

variable {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}

namespace KS

lemma zero {B : ℝ} {e δ : ℕ} (hB : 0 ≤ B) : KS ι 0 B e δ (fun _ => 0) := const (Sz.zero e) hB

lemma sum {α : Type*} (s : Finset α) {A : α → ℝ} {B : ℝ} {e δ : ℕ} {g : α → ℂ → ℂ} (hB : 0 ≤ B)
    (hg : ∀ a ∈ s, KS ι (A a) B e δ (g a)) :
    KS ι (∑ a ∈ s, A a) B e δ (fun x => ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (ι := ι) (e := e) (δ := δ) hB
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hg a (mem_insert_self a s)).add (ih fun b hb => hg b (mem_insert_of_mem hb))

lemma prod_pow {α : Type*} (s : Finset α) {B : ℝ} (hB : 0 ≤ B) {δ : ℕ} {g : α → ℂ → ℂ}
    {A : α → ℝ} {e : α → ℕ} (hg : ∀ f ∈ s, KS ι (A f) B (e f) δ (g f)) (n : α → ℕ) :
    KS ι (2 ^ (∑ f ∈ s, n f) * ∏ f ∈ s, A f ^ n f) (2 * B) (∏ f ∈ s, e f ^ n f) δ
      (fun x => ∏ f ∈ s, g f x ^ n f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (ι := ι) (δ := δ) (by positivity : (0 : ℝ) ≤ 2 * B)
  | insert a s ha ih =>
    have h := (ih fun f hf => hg f (mem_insert_of_mem hf)).mul_pow_basic hB
      (hg a (mem_insert_self a s)) (n a)
    simp only [sum_insert ha, prod_insert ha]
    convert h using 1
    · rw [pow_add]; ring
    · ring
    · funext x; ring

/-- **The polynomial in the basic factors.** -/
lemma poly {α : Type*} [Fintype α] {B : ℝ} (hB : 0 ≤ B) {δ : ℕ} {g : α → ℂ → ℂ} {A : α → ℝ}
    {e : α → ℕ} (hg : ∀ f, KS ι (A f) B (e f) δ (g f)) (hA : ∀ f, 1 ≤ A f) {L : ℕ}
    (p : Fin L → ℤ) (n : Fin L → α → ℕ) (N : α → ℕ) (hn : ∀ l f, n l f ≤ N f) :
    KS ι ((∑ l, |(p l : ℝ)|) * (2 ^ (∑ f, N f) * ∏ f, A f ^ N f)) (2 * B) (∏ f, e f ^ N f) δ
      (fun x => ∑ l, (p l : ℂ) * ∏ f, g f x ^ n l f) := by
  rw [sum_mul]
  refine sum (ι := ι) _ (by positivity) fun l _ => ?_
  have hm := prod_pow (ι := ι) univ hB (fun f _ => hg f) (n l)
  have hm' : KS ι (2 ^ (∑ f, N f) * ∏ f, A f ^ N f) (2 * B) (∏ f, e f ^ N f) δ
      (fun x => ∏ f, g f x ^ n l f) := by
    refine hm.mono ?_ (by positivity) le_rfl ?_ dvd_rfl
    · have hA0 : ∀ f, 0 ≤ A f := fun f => zero_le_one.trans (hA f)
      have h1 : (2 : ℝ) ^ (∑ f, n l f) ≤ 2 ^ (∑ f, N f) :=
        pow_le_pow_right₀ one_le_two (sum_le_sum fun f _ => hn l f)
      have h2 : ∏ f, A f ^ n l f ≤ ∏ f, A f ^ N f :=
        Finset.prod_le_prod₀ (fun f _ => pow_nonneg (hA0 f) _)
          (fun f _ => pow_le_pow_right₀ (hA f) (hn l f))
      exact mul_le_mul h1 h2 (prod_nonneg fun f _ => pow_nonneg (hA0 f) _) (by positivity)
    · exact prod_dvd_prod_of_dvd _ _ fun f _ => pow_dvd_pow _ (hn l f)
  simpa using hm'.const_mul (Sz.intCast (ι := ι) (p l))

end KS

/-! ### Basic factors -/

/-- `x + y s`. -/
lemma ks_lin {a B : ℝ} {d δ : ℕ} {x y : ℂ} (hx : Sz ι a d x) (hy : Sz ι (a * B) d y)
    (hB : 0 ≤ B) : KS ι a B d δ (fun s => x + y * s) := by
  refine ⟨analyticAt_const.add (analyticAt_const.mul analyticAt_id), fun j => ?_⟩
  rw [tco_lin]
  rcases j with _ | _ | j
  · simpa using hx
  · simpa using hy.mono le_rfl (Dvd.intro δ rfl)
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, add_eq_right]
    exact (Sz.zero _).mono_le (mul_nonneg hx.nonneg (pow_nonneg hB _))

/-- `x e^{y s}`. -/
lemma ks_expm {a b : ℝ} {d d' : ℕ} {x y : ℂ} (hx : Sz ι a d x) (hy : Sz ι b d' y) :
    KS ι a b d d' (fun s => x * Complex.exp (y * s)) := by
  refine ⟨analyticAt_const.mul (analyticAt_const.mul analyticAt_id).cexp, fun j => ?_⟩
  rw [tco_const_mul, tco_cexp]
  have h := (hx.mul (hy.pow j)).div_nat (Nat.factorial_ne_zero j)
  refine (by simpa [mul_div_assoc] using h : Sz ι (a * b ^ j / j.factorial)
    (d * d' ^ j * j.factorial) (x * (y ^ j / j.factorial))).mono_le ?_
  have hab : 0 ≤ a * b ^ j := by
    have hb : 0 ≤ b := hy.nonneg
    exact mul_nonneg hx.nonneg (pow_nonneg hb j)
  exact div_le_self hab (by exact_mod_cast j.factorial_pos)

/-- A quadratic form in three basic series (the elliptic factors `law(X', ξ(s))`). -/
lemma ks_quad {A B : ℝ} {E δ : ℕ} {ξ : Fin 3 → ℂ → ℂ} (hB : 0 ≤ B)
    (hξ : ∀ a, KS ι A B E δ (ξ a)) {q : Fin 3 → ℂ} {r : Fin 3 → Fin 3 → ℂ} {H : ℝ} {dq : ℕ}
    (hq : ∀ a, Sz ι H dq (q a)) (hr : ∀ a b, Sz ι H dq (r a b)) :
    KS ι (24 * H * A ^ 2) (2 * B) (dq * (E * E)) δ (fun s =>
      ∑ a : Fin 3, q a * ξ a s ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3, (if a < b then r a b * ξ a s * ξ b s else 0)) := by
  have hA : 0 ≤ A := by have := ((hξ 0).2 0).nonneg; simpa using this
  have hH : 0 ≤ H := (hq 0).nonneg
  have hprod : ∀ a b, KS ι (2 * A * A) (2 * B) (E * E) δ (fun s => ξ a s * ξ b s) := by
    intro a b
    exact ((hξ a).mono le_rfl hB (by linarith) dvd_rfl dvd_rfl).mul_basic hB (hξ b)
  have hsq : ∀ a, KS ι (H * (2 * A * A)) (2 * B) (dq * (E * E)) δ (fun s => q a * ξ a s ^ 2) := by
    intro a
    have := (hprod a a).const_mul (hq a)
    simpa [sq] using this
  have h1 := KS.sum (ι := ι) univ (by positivity) fun a (_ : a ∈ univ) => hsq a
  have hcross : ∀ a b, KS ι (H * (2 * A * A)) (2 * B) (dq * (E * E)) δ
      (fun s => if a < b then r a b * ξ a s * ξ b s else 0) := by
    intro a b
    split_ifs
    · have := (hprod a b).const_mul (hr a b)
      simpa [mul_assoc] using this
    · exact KS.zero (by positivity) |>.mono (by positivity) (by positivity) le_rfl dvd_rfl dvd_rfl
  have h2 := KS.sum (ι := ι) univ (by positivity) fun a (_ : a ∈ univ) =>
    KS.sum (ι := ι) univ (by positivity) fun b (_ : b ∈ univ) => hcross a b
  refine (h1.add h2).mono ?_ (by positivity) le_rfl dvd_rfl dvd_rfl
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  nlinarith [mul_nonneg hH (sq_nonneg A)]

end LSG.Aux
