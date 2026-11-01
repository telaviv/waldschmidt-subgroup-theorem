/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.Mono

/-!
# M2.6.3b: growth and nonvanishing of the monomials `MonoAV`

* **`sum_norm_evalAV_le`**: `Σ_l ‖M_l(u)‖ ≤ exp (log L + A₀ log (1 + R) + A₁ R + (D + F) c_V (1 + R)²)` on
  `‖u‖ ≤ R` (`c_V = cVg An M`; the fibre forms are linear in `s` and of order 2 in `z`).
* **`exists_PsiAV_ne_zero`**: distinct exponent vectors (`MonoAV.rexp`, in the dehomogenised variables `a`, `e^b`,
  the base ratios and the fibre ratios `s_i + Σ_j M_ij τ_j(z_j)`) and `p ≠ 0` give `PsiAV ≢ 0`. On `θ_{i₀} ≠ 0` a
  monomial is `Π_k θ_{k,i₀}^{D+F}` times a monomial in those variables (`MonoAV.eval_eq`); the base ratios fill a ball
  (`exists_ratio_ball`) and, for fixed `z`, the fibre ratios take every value (choose `s`).
-/

open Complex Finset Filter Topology

noncomputable section

namespace LSG.AuxAV

open LSG.MEBV LSG.AuxA
open LSG.MEB (AbBlock)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {D F : ℕ}

/-! ### Growth -/

/-- The growth constant of the monomials. -/
def cVg (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : ℝ :=
  (m + 1) * (cWU (fun k => (An k).an) + ∑ k, (An k).cT) + 1 + Real.log (1 + ∑ i, ∑ j, ‖M i j‖)

lemma cVg_nonneg (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : 0 ≤ cVg An M := by
  have h1 := cWU_nonneg (fun k => (An k).an)
  have h2 : 0 ≤ ∑ k, (An k).cT := sum_nonneg fun k _ => (An k).cT_nonneg
  have hs : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := sum_nonneg fun i _ => sum_nonneg fun j _ => norm_nonneg _
  have h3 : 0 ≤ Real.log (1 + ∑ i, ∑ j, ‖M i j‖) := Real.log_nonneg (by linarith)
  unfold cVg; positivity

/-- **Growth of the monomials.** -/
theorem sum_norm_evalAV_le (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) {L A₀ A₁ : ℕ}
    (νs : Fin L → MonoAV d₀ d₁ r B D F) (hα : ∀ l, ∑ i, (νs l).μ.α i ≤ A₀)
    (hβ : ∀ l, ∑ j, (νs l).μ.β j ≤ A₁) {R U : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L)
    (hU : Real.log L + A₀ * Real.log (1 + R) + A₁ * R + (D + F) * cVg An M * (1 + R) ^ 2 ≤ U)
    (u : TanAV d₀ d₁ r B) (hu : ‖u‖ ≤ R) : ∑ l, ‖(νs l).eval M u‖ ≤ Real.exp U := by
  set c : ℝ := cWU (fun k => (An k).an) + ∑ k, (An k).cT with hc
  have hcW0 := cWU_nonneg (fun k => (An k).an)
  have hcT0 : 0 ≤ ∑ k, (An k).cT := sum_nonneg fun k _ => (An k).cT_nonneg
  have hc0 : 0 ≤ c := by positivity
  set Mn : ℝ := ∑ i, ∑ j, ‖M i j‖ with hMn
  have hMn0 : 0 ≤ Mn := sum_nonneg fun i _ => sum_nonneg fun j _ => norm_nonneg _
  set E : ℝ := Real.exp (c * (1 + R) ^ 2) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hz : ∀ k, ‖u.2.2.1 k‖ ≤ R := fun k => (norm_zV_le u k).trans hu
  have hsq : ∀ k, (1 + ‖u.2.2.1 k‖) ^ 2 ≤ (1 + R) ^ 2 := fun k =>
    pow_le_pow_left₀ (by positivity) (by linarith [hz k]) 2
  have hθ : ∀ k, ‖thI B u.2.2.1 k‖ ≤ E := by
    intro k
    refine (norm_le_pi_norm ((B k).base.θ (u.2.2.1 k)) _).trans
      (((An k).an.growth _).trans (Real.exp_le_exp.mpr ?_))
    have : (An k).an.cW ≤ c := (cW_le (fun k => (An k).an) k).trans (le_add_of_nonneg_right hcT0)
    exact mul_le_mul this (hsq k) (by positivity) hc0
  have hT : ∀ k, ‖(B k).T (u.2.2.1 k) 0 (B k).t₀‖ ≤ E := by
    intro k
    refine ((An k).growthT _ 0 _).trans ?_
    rw [norm_zero, add_zero, one_mul]
    refine Real.exp_le_exp.mpr ?_
    have : (An k).cT ≤ c := by
      have h1 : (An k).cT ≤ ∑ k, (An k).cT :=
        single_le_sum (f := fun k => (An k).cT) (fun k _ => (An k).cT_nonneg) (mem_univ k)
      linarith
    exact mul_le_mul this (hsq k) (by positivity) hc0
  have hPθ : ∀ s : Finset (Fin m), ‖∏ k ∈ s, thI B u.2.2.1 k‖ ≤ E ^ m := by
    intro s
    rw [norm_prod]
    calc ∏ k ∈ s, ‖thI B u.2.2.1 k‖ ≤ ∏ _k ∈ s, E := prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hθ k
      _ = E ^ s.card := prod_const _
      _ ≤ E ^ m := pow_le_pow_right₀ hE1 (by simpa using card_le_univ s)
  set Q : ℝ := (1 + R) * (1 + Mn) with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hfib : ∀ i, ‖fibF M i u.2.2.1 u.2.2.2‖ ≤ Q * E ^ (m + 1) := by
    intro i
    unfold fibF
    have hs : ‖u.2.2.2 i‖ ≤ R := (norm_sV_le u i).trans hu
    have h1 : ‖u.2.2.2 i * ∏ k, thI B u.2.2.1 k‖ ≤ R * E ^ (m + 1) := by
      rw [norm_mul]
      exact mul_le_mul hs ((hPθ univ).trans (pow_le_pow_right₀ hE1 (Nat.le_succ m))) (norm_nonneg _) hR
    have h2 : ‖∑ j, M i j * ((B j).T (u.2.2.1 j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B u.2.2.1 l)‖ ≤
        Mn * E ^ (m + 1) := by
      refine (norm_sum_le _ _).trans ?_
      have hMi : ∑ j, ‖M i j‖ ≤ Mn :=
        single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun i _ => sum_nonneg fun j _ => norm_nonneg _) (mem_univ i)
      calc ∑ j, ‖M i j * ((B j).T (u.2.2.1 j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B u.2.2.1 l)‖
          ≤ ∑ j, ‖M i j‖ * E ^ (m + 1) := sum_le_sum fun j _ => by
            rw [norm_mul, norm_mul, pow_succ, mul_comm (E ^ m) E]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hT j) (hPθ _) (norm_nonneg _) (by positivity))
              (norm_nonneg _)
        _ = (∑ j, ‖M i j‖) * E ^ (m + 1) := by rw [sum_mul]
        _ ≤ Mn * E ^ (m + 1) := mul_le_mul_of_nonneg_right hMi (by positivity)
    calc _ ≤ R * E ^ (m + 1) + Mn * E ^ (m + 1) := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ Q * E ^ (m + 1) := by
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hQ]; nlinarith
  have hone : ∀ l, ‖(νs l).eval M u‖ ≤
      Real.exp (A₀ * Real.log (1 + R) + A₁ * R + (D + F) * cVg An M * (1 + R) ^ 2) := by
    intro l
    have hφ := (νs l).hφ
    have hA := sum_norm_eval_le (fun k => (An k).an) (fun _ : Fin 1 => (νs l).μ) (fun _ => hα l)
      (fun _ => hβ l) hR le_rfl le_rfl (piA u) ((norm_piA_le u).trans hu)
    simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, Real.log_one, zero_add] at hA
    have hpad : ‖(∏ k, thI B u.2.2.1 k) ^ (F - ∑ i, (νs l).φ i)‖ ≤ (E ^ (m + 1)) ^ (F - ∑ i, (νs l).φ i) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hPθ univ).trans (pow_le_pow_right₀ hE1 (Nat.le_succ m))) _
    have hfibs : ‖∏ i, fibF M i u.2.2.1 u.2.2.2 ^ (νs l).φ i‖ ≤
        Q ^ F * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i) := by
      rw [norm_prod]
      calc ∏ i, ‖fibF M i u.2.2.1 u.2.2.2 ^ (νs l).φ i‖ ≤ ∏ i, (Q * E ^ (m + 1)) ^ (νs l).φ i :=
            prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
              rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hfib i) _
        _ = Q ^ (∑ i, (νs l).φ i) * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i) := by
            rw [prod_pow_eq_pow_sum, mul_pow]
        _ ≤ Q ^ F * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ1 hφ) (by positivity)
    have hEF : (E ^ (m + 1)) ^ (F - ∑ i, (νs l).φ i) * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i) =
        Real.exp ((m + 1) * F * c * (1 + R) ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hφ, ← pow_mul, hE, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hQF : Q ^ F ≤ Real.exp (F * (Real.log (1 + R) + Real.log (1 + Mn))) := by
      rw [← Real.log_mul (by linarith) (by linarith), ← hQ, ← Real.log_pow, Real.exp_log (by positivity)]
    unfold MonoAV.eval
    rw [norm_mul, norm_mul]
    calc ‖(νs l).μ.eval (piA u)‖ * ‖(∏ k, thI B u.2.2.1 k) ^ (F - ∑ i, (νs l).φ i)‖ *
          ‖∏ i, fibF M i u.2.2.1 u.2.2.2 ^ (νs l).φ i‖
        ≤ Real.exp (A₀ * Real.log (1 + R) + A₁ * R + m * D * cWU (fun k => (An k).an) * (1 + R) ^ 2) *
            (E ^ (m + 1)) ^ (F - ∑ i, (νs l).φ i) * (Q ^ F * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i)) :=
          mul_le_mul (mul_le_mul hA hpad (norm_nonneg _) (Real.exp_pos _).le) hfibs (norm_nonneg _)
            (by positivity)
      _ = Real.exp (A₀ * Real.log (1 + R) + A₁ * R + m * D * cWU (fun k => (An k).an) * (1 + R) ^ 2) *
            Q ^ F * ((E ^ (m + 1)) ^ (F - ∑ i, (νs l).φ i) * (E ^ (m + 1)) ^ (∑ i, (νs l).φ i)) := by ring
      _ ≤ Real.exp (A₀ * Real.log (1 + R) + A₁ * R + m * D * cWU (fun k => (An k).an) * (1 + R) ^ 2) *
            Real.exp (F * (Real.log (1 + R) + Real.log (1 + Mn))) *
            Real.exp ((m + 1) * F * c * (1 + R) ^ 2) := by
          rw [hEF]; gcongr
      _ = Real.exp (A₀ * Real.log (1 + R) + A₁ * R + (m * D * cWU (fun k => (An k).an) * (1 + R) ^ 2 +
            F * (Real.log (1 + R) + Real.log (1 + Mn)) + (m + 1) * F * c * (1 + R) ^ 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          set sR : ℝ := (1 + R) ^ 2 with hsR
          have hl1 : Real.log (1 + R) ≤ sR := by
            calc Real.log (1 + R) ≤ 1 + R - 1 := Real.log_le_sub_one_of_pos (by linarith)
              _ ≤ sR := by rw [hsR]; nlinarith
          have hlM : 0 ≤ Real.log (1 + Mn) := Real.log_nonneg (by linarith)
          have hsq1 : 1 ≤ sR := one_le_pow₀ (by linarith)
          have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg F
          have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have hcWc : cWU (fun k => (An k).an) ≤ c := le_add_of_nonneg_right hcT0
          have f1 : (m : ℝ) * D * cWU (fun k => (An k).an) * sR ≤ (m + 1) * D * c * sR := by
            have : (m : ℝ) * D * cWU (fun k => (An k).an) ≤ (m + 1) * D * c :=
              mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hD0) hcWc hcW0 (by positivity)
            exact mul_le_mul_of_nonneg_right this (by positivity)
          have g1 : (F : ℝ) * Real.log (1 + R) ≤ (D + F) * sR :=
            (mul_le_mul_of_nonneg_left hl1 hF0).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
          have g2 : (F : ℝ) * Real.log (1 + Mn) ≤ (D + F) * Real.log (1 + Mn) * sR := by
            have : (F : ℝ) * Real.log (1 + Mn) ≤ (D + F) * Real.log (1 + Mn) :=
              mul_le_mul_of_nonneg_right (by linarith) hlM
            exact this.trans (le_mul_of_one_le_right (by positivity) hsq1)
          have hcv : cVg An M = (m + 1) * c + 1 + Real.log (1 + Mn) := rfl
          rw [hcv]
          nlinarith [f1, g1, g2]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  calc ∑ l, ‖(νs l).eval M u‖
      ≤ ∑ _l : Fin L, Real.exp (A₀ * Real.log (1 + R) + A₁ * R + (D + F) * cVg An M * (1 + R) ^ 2) :=
        sum_le_sum fun l _ => hone l
    _ = Real.exp (Real.log L) *
          Real.exp (A₀ * Real.log (1 + R) + A₁ * R + (D + F) * cVg An M * (1 + R) ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.exp_log hL0]
    _ = Real.exp (Real.log L + A₀ * Real.log (1 + R) + A₁ * R + (D + F) * cVg An M * (1 + R) ^ 2) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hU

/-! ### Nonvanishing -/

variable (d₀ d₁ r B) in
/-- The dehomogenised variables: `a`, `e^b`, the base ratios, the fibre ratios. -/
abbrev RVarAV := RVarA d₀ d₁ (Bb B) ⊕ Fin r

/-- The exponent vector in the dehomogenised variables. -/
def MonoAV.rexp (ν : MonoAV d₀ d₁ r B D F) : RVarAV d₀ d₁ r B → ℕ
  | .inl v => ν.μ.rexp v
  | .inr i => ν.φ i

/-- The fibre ratio `s_i + Σ_j M_ij τ_j(z_j)`. -/
def fibR (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (z : ∀ k, Fin (B k).g → ℂ) (s : Fin r → ℂ) : ℂ :=
  s i + ∑ j, M i j * tauV (B j) (z j)

/-- The values of the dehomogenised variables at a point. -/
def rval (M : Matrix (Fin r) (Fin m) ℂ) (u : TanAV d₀ d₁ r B) : RVarAV d₀ d₁ r B → ℂ
  | .inl (.inl i) => u.1 i
  | .inl (.inr (.inl j)) => Complex.exp (u.2.1 j)
  | .inl (.inr (.inr ⟨k, j⟩)) => ratioMap (B k).base (u.2.2.1 k) j
  | .inr i => fibR M i u.2.2.1 u.2.2.2

/-- **On `θ_{i₀} ≠ 0` a monomial is `Π_k θ_{k,i₀}^{D+F}` times a monomial in the dehomogenised variables.** -/
theorem MonoAV.eval_eq (M : Matrix (Fin r) (Fin m) ℂ) (ν : MonoAV d₀ d₁ r B D F) (u : TanAV d₀ d₁ r B)
    (hz : ∀ k, thI B u.2.2.1 k ≠ 0) :
    ν.eval M u = (∏ k, thI B u.2.2.1 k) ^ (D + F) * ∏ v, rval M u v ^ ν.rexp v := by
  have hA : ν.μ.eval (piA u) = (∏ k, thI B u.2.2.1 k) ^ D *
      ∏ v : RVarA d₀ d₁ (Bb B), rval M u (.inl v) ^ ν.rexp (.inl v) := by
    unfold MonoA.eval
    simp only [piA_apply]
    rw [Finset.prod_congr rfl fun k _ => ν.μ.block_eq k (u.2.2.1 k) (hz k)]
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
    simp only [rval, MonoAV.rexp, MonoA.rexp, prod_mul_distrib, thI, ← prod_pow]
    ring
  have hfib : ∏ i, fibF M i u.2.2.1 u.2.2.2 ^ ν.φ i =
      (∏ k, thI B u.2.2.1 k) ^ (∑ i, ν.φ i) * ∏ i, rval M u (.inr i) ^ ν.rexp (.inr i) := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [fibF_eq M i _ _ hz, mul_pow]; rfl
  unfold MonoAV.eval
  rw [hA, hfib, Fintype.prod_sum_type (fun x => rval M u x ^ ν.rexp x)]
  have hφ := ν.hφ
  have e : (∏ k, thI B u.2.2.1 k) ^ (D + F) = (∏ k, thI B u.2.2.1 k) ^ D *
      (∏ k, thI B u.2.2.1 k) ^ (F - ∑ i, ν.φ i) * (∏ k, thI B u.2.2.1 k) ^ (∑ i, ν.φ i) := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hφ, ← pow_add]
  rw [e]
  ring

/-- **`Ψ ≢ 0` for distinct monomials and `p ≠ 0`**, at a point where every `θ_{k,i₀} ≠ 0`. -/
theorem exists_PsiAV_ne_zero (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (hinj : Function.Injective fun l => (νs l).rexp) (p : Fin L → ℤ) (hp : p ≠ 0) :
    ∃ u, PsiAV M νs p u ≠ 0 ∧ ∀ k, thI B u.2.2.1 k ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  let ex : Fin L → (RVarAV d₀ d₁ r B →₀ ℕ) := fun l => Finsupp.equivFunOnFinite.symm (νs l).rexp
  have hex : Function.Injective ex := fun a b h => hinj (by
    have := congrArg Finsupp.equivFunOnFinite h; simpa [ex] using this)
  let Q : MvPolynomial (RVarAV d₀ d₁ r B) ℂ := ∑ l, MvPolynomial.monomial (ex l) (p l : ℂ)
  set N : ℕ := ∑ l, ∑ v, (νs l).rexp v
  have hdeg : ∀ v, MvPolynomial.degreeOf v Q ≤ N := by
    intro v
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun l _ => ?_)
    have hm : MvPolynomial.degreeOf v (MvPolynomial.monomial (ex l) (p l : ℂ)) ≤ (νs l).rexp v := by
      by_cases h0 : (p l : ℂ) = 0
      · rw [h0, map_zero]; simp
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ h0]; simp [ex]
    refine hm.trans ?_
    exact (single_le_sum (f := fun v => (νs l).rexp v) (fun _ _ => Nat.zero_le _)
      (mem_univ v)).trans (single_le_sum (f := fun l => ∑ v, (νs l).rexp v)
        (fun _ _ => Nat.zero_le _) (mem_univ l))
  choose ε hε hball using fun k => exists_ratio_ball (B k).base
  let ptR : ∀ k, Fin (B k).g → ℕ → ℂ := fun k j n =>
    ratioMap (B k).base 0 j + (ε k / (2 * (N + 2)) : ℝ) * n
  have hptR_inj : ∀ k j, Function.Injective (ptR k j) := fun k j a b h => by
    have h1 : ((ε k / (2 * (N + 2)) : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ε k / (2 * (N + 2)) := by have := hε k; positivity
      exact_mod_cast this.ne'
    have h2 := mul_left_cancel₀ h1 (add_left_cancel h)
    exact_mod_cast h2
  have hptR_near : ∀ k j n, n < N + 1 → ‖ptR k j n - ratioMap (B k).base 0 j‖ < ε k := fun k j n hn => by
    simp only [ptR, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_natCast]
    have hεk := hε k
    have hn' : (n : ℝ) < N + 2 := by
      have : (n : ℝ) < N + 1 := by exact_mod_cast hn
      linarith
    rw [Real.norm_of_nonneg (by positivity)]
    calc ε k / (2 * (N + 2)) * n ≤ ε k / (2 * (N + 2)) * (N + 2) := by gcongr
      _ = ε k / 2 := by field_simp
      _ < ε k := by linarith
  let Sv : RVarAV d₀ d₁ r B → Finset ℂ := fun v => match v with
    | .inl (.inl _) => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
    | .inl (.inr (.inl _)) => (range (N + 1)).image (fun n : ℕ => ((n + 1 : ℕ) : ℂ))
    | .inl (.inr (.inr ⟨k, j⟩)) => (range (N + 1)).image (ptR k j)
    | .inr _ => (range (N + 1)).image (fun n : ℕ => (n : ℂ))
  have hcard : ∀ v, MvPolynomial.degreeOf v Q < (Sv v).card := by
    intro v
    have h1 := hdeg v
    rcases v with (i | i | ⟨k, j⟩) | i
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
    · simp only [Sv]
      rw [card_image_of_injective _ (fun a b h => by
        have := Nat.cast_injective (R := ℂ) h; omega), card_range]; omega
    · simp only [Sv]; rw [card_image_of_injective _ (hptR_inj k j), card_range]; omega
    · simp only [Sv]; rw [card_image_of_injective _ Nat.cast_injective, card_range]; omega
  have hQ0 : Q = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q Sv hcard fun x hx => ?_
    have hz : ∀ k, ∃ z, (B k).base.θ z (B k).base.i₀ ≠ 0 ∧
        ratioMap (B k).base z = fun j => x (.inl (.inr (.inr ⟨k, j⟩))) := by
      intro k
      refine hball k _ ?_
      rw [dist_pi_lt_iff (hε k)]
      intro j
      obtain ⟨n, hn, hnx⟩ := mem_image.mp (hx (.inl (.inr (.inr ⟨k, j⟩))))
      rw [dist_eq_norm, ← hnx]
      exact hptR_near k j n (mem_range.mp hn)
    choose z hz0 hzx using hz
    have hb : ∀ i, x (.inl (.inr (.inl i))) ≠ 0 := by
      intro i
      obtain ⟨n, -, hn⟩ := mem_image.mp (hx (.inl (.inr (.inl i))))
      rw [← hn]; exact_mod_cast Nat.succ_ne_zero n
    let pt : TanAV d₀ d₁ r B := (fun i => x (.inl (.inl i)),
      fun i => Complex.log (x (.inl (.inr (.inl i)))), z,
      fun i => x (.inr i) - ∑ j, M i j * tauV (B j) (z j))
    have hzt : ∀ k, thI B pt.2.2.1 k ≠ 0 := hz0
    have hrv : rval M pt = x := by
      funext v
      rcases v with (i | i | ⟨k, j⟩) | i
      · rfl
      · exact Complex.exp_log (hb i)
      · change ratioMap (B k).base (z k) j = _
        rw [hzx k]
      · change x (.inr i) - ∑ j, M i j * tauV (B j) (z j) + ∑ j, M i j * tauV (B j) (z j) = _
        ring
    have hpt : PsiAV M νs p pt = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ := hall pt hne
      exact hzt k hk
    unfold PsiAV at hpt
    have hθ : (∏ k, thI B pt.2.2.1 k) ^ (D + F) ≠ 0 :=
      pow_ne_zero _ (prod_ne_zero_iff.mpr fun k _ => hzt k)
    have hpt' : (∏ k, thI B pt.2.2.1 k) ^ (D + F) * MvPolynomial.eval x Q = 0 := by
      rw [← hpt]
      simp only [Q, map_sum, MvPolynomial.eval_monomial, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), (νs l).eval_eq M pt hzt, hrv]
      simp only [ex, Finsupp.coe_equivFunOnFinite_symm]
      ring
    exact (mul_eq_zero.mp hpt').resolve_left hθ
  apply hp
  funext l
  have hc := congrArg (fun q : MvPolynomial (RVarAV d₀ d₁ r B) ℂ => q.coeff (ex l)) hQ0
  simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [sum_eq_single l (fun b _ hb => if_neg (fun h => hb (hex h))) (by simp)] at hc
  simp only [↓reduceIte] at hc
  simpa using hc

end LSG.AuxAV
