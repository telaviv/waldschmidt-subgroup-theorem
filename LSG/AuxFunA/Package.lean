/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.Mono
import LSG.W88.AbVarPer

/-!
# A5.2: the analytic package of a block (`STAGE_A5.md` D1)

What the consumer needs from a block beyond the frozen `AbBlock` fields:

* `lat ≤ per` with `per ⊆ ℚ · lat` (`IsNsmulIn`): the periods W88 counts;
* order-2 growth `‖θ z‖ ≤ exp (c_W (1 + ‖z‖)²)`;
* quasi-periodicity on `lat` in exponential-affine form: `θ (z + ω) = (κ_ω e^{L_ω z}) • θ z` with
  `‖κ_ω‖^{±1} ≤ exp (c_Q ‖ω‖²)` and `‖L_ω z‖ ≤ c_Q ‖ω‖ ‖z‖`.

For the `A`-block all three are proved in `LSG/JacAn3` (`latBasis`/`isNsmulIn_latt_kerE`, `thetaN_order2`,
`norm_facN`/`fac_affine`); the instance is A5.8.

Consequences for the monomials of `LSG/AuxFunA/Mono.lean`:
* `MonoA.differentiable_eval`;
* **`exists_qp_monoA`**: a common multiplier `mu` of all monomials of block degree `D` under `ω ∈ PerL`, with
  `‖mu‖ ≤ exp (m D c_Q (‖u‖ + ‖ω‖)²)`;
* **`sum_norm_eval_le`**: `Σ_l ‖M_l(u)‖ ≤ exp (log L + D₀ log (1 + R) + D₁ R + m D c_W (1 + R)²)` on `‖u‖ ≤ R`.
-/

open Complex Finset Module LSG.W88

noncomputable section

namespace LSG.AuxA

open LSG.MEB

/-- **The analytic package of a block.** -/
structure AbBlockAn (b : AbBlock) where
  /-- the periods counted by W88 -/
  lat : AddSubgroup (Fin b.g → ℂ)
  lat_le : lat ≤ b.per
  lat_nsmul : IsNsmulIn lat b.per
  /-- growth constant -/
  cW : ℝ
  cW_nonneg : 0 ≤ cW
  growth : ∀ z, ‖b.θ z‖ ≤ Real.exp (cW * (1 + ‖z‖) ^ 2)
  /-- quasi-periodicity constant -/
  cQ : ℝ
  cQ_nonneg : 0 ≤ cQ
  qp : ∀ ω ∈ lat, ∃ (κ : ℂ) (L : (Fin b.g → ℂ) →ₗ[ℂ] ℂ), κ ≠ 0 ∧ ‖κ‖ ≤ Real.exp (cQ * ‖ω‖ ^ 2) ∧
    ‖κ‖⁻¹ ≤ Real.exp (cQ * ‖ω‖ ^ 2) ∧ (∀ z, ‖L z‖ ≤ cQ * ‖ω‖ * ‖z‖) ∧
    ∀ z, b.θ (z + ω) = (κ * Complex.exp (L z)) • b.θ z

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {D : ℕ}

/-- The sublattice family of a package family. -/
def latF (An : ∀ k, AbBlockAn (B k)) : ∀ k, AddSubgroup (Fin (B k).g → ℂ) := fun k => (An k).lat

/-- A uniform growth constant. -/
def cWU (An : ∀ k, AbBlockAn (B k)) : ℝ := ∑ k, (An k).cW

/-- A uniform quasi-periodicity constant. -/
def cQU (An : ∀ k, AbBlockAn (B k)) : ℝ := ∑ k, (An k).cQ

lemma cWU_nonneg (An : ∀ k, AbBlockAn (B k)) : 0 ≤ cWU An := sum_nonneg fun k _ => (An k).cW_nonneg
lemma cQU_nonneg (An : ∀ k, AbBlockAn (B k)) : 0 ≤ cQU An := sum_nonneg fun k _ => (An k).cQ_nonneg
lemma cW_le (An : ∀ k, AbBlockAn (B k)) (k : Fin m) : (An k).cW ≤ cWU An :=
  single_le_sum (f := fun k => (An k).cW) (fun k _ => (An k).cW_nonneg) (mem_univ k)
lemma cQ_le (An : ∀ k, AbBlockAn (B k)) (k : Fin m) : (An k).cQ ≤ cQU An :=
  single_le_sum (f := fun k => (An k).cQ) (fun k _ => (An k).cQ_nonneg) (mem_univ k)

lemma norm_x_le (u : Tan d₀ d₁ B) (i : Fin d₀) : ‖u.1 i‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.1 i).trans (norm_fst_le u)
lemma norm_b_le (u : Tan d₀ d₁ B) (j : Fin d₁) : ‖u.2.1 j‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.2.1 j).trans ((norm_fst_le u.2).trans (norm_snd_le u))
lemma norm_z_le (u : Tan d₀ d₁ B) (k : Fin m) : ‖u.2.2 k‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.2.2 k).trans ((norm_snd_le u.2).trans (norm_snd_le u))

lemma differentiable_θ (b : AbBlock) : Differentiable ℂ b.θ := fun z => (b.θ_analytic z).differentiableAt

lemma differentiable_fprodA {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (u : Finset ι) (g : ι → E → ℂ) (h : ∀ i ∈ u, Differentiable ℂ (g i)) :
    Differentiable ℂ (fun x => ∏ i ∈ u, g i x) := fun x => by
  classical
  exact (HasFDerivAt.finsetProd fun i hi => (h i hi x).hasFDerivAt).differentiableAt

theorem MonoA.differentiable_eval (μ : MonoA d₀ d₁ B D) : Differentiable ℂ μ.eval := by
  have hx : ∀ i, Differentiable ℂ fun u : Tan d₀ d₁ B => u.1 i := fun i => by fun_prop
  have hb : ∀ j, Differentiable ℂ fun u : Tan d₀ d₁ B => Complex.exp (u.2.1 j) := fun j => by
    fun_prop
  have hθ : ∀ k c, Differentiable ℂ fun u : Tan d₀ d₁ B => (B k).θ (u.2.2 k) c := fun k c =>
    (differentiable_pi.mp (differentiable_θ (B k)) c).comp (by fun_prop)
  have h1 := differentiable_fprodA Finset.univ (fun i (u : Tan d₀ d₁ B) => u.1 i ^ μ.α i)
    fun i _ => (hx i).pow _
  have h2 := differentiable_fprodA Finset.univ
    (fun j (u : Tan d₀ d₁ B) => Complex.exp (u.2.1 j) ^ μ.β j) fun j _ => (hb j).pow _
  have h3 := differentiable_fprodA Finset.univ
    (fun k (u : Tan d₀ d₁ B) => ∏ c, (B k).θ (u.2.2 k) (fidx (B k) c) ^ μ.γ k c)
    fun k _ => differentiable_fprodA Finset.univ
      (fun c (u : Tan d₀ d₁ B) => (B k).θ (u.2.2 k) (fidx (B k) c) ^ μ.γ k c) fun c _ => (hθ k _).pow _
  unfold MonoA.eval
  exact (h1.mul h2).mul h3

/-- **Common multiplier of the monomials under a period.** -/
theorem exists_qp_monoA (An : ∀ k, AbBlockAn (B k)) {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D)
    {ω : Tan d₀ d₁ B} (hω : ω ∈ PerL d₀ d₁ B (latF An)) (u : Tan d₀ d₁ B) :
    ∃ mu : ℂ, ‖mu‖ ≤ Real.exp (m * D * cQU An * (‖u‖ + ‖ω‖) ^ 2) ∧
      ∀ l, (μs l).eval (u + ω) = mu * (μs l).eval u := by
  choose κ Lf hκ0 hκ hκi hL hθ using fun k => (An k).qp (ω.2.2 k) (hω.2.2 k)
  set f : Fin m → ℂ := fun k => κ k * Complex.exp (Lf k (u.2.2 k)) with hf
  refine ⟨∏ k, f k ^ D, ?_, fun l => ?_⟩
  · rw [norm_prod]
    have hk : ∀ k ∈ univ, ‖f k ^ D‖ ≤ Real.exp (D * cQU An * (‖u‖ + ‖ω‖) ^ 2) := by
      intro k _
      rw [norm_pow, hf, norm_mul, Complex.norm_exp]
      have hc0 := cQU_nonneg An
      have h1 : (Lf k (u.2.2 k)).re ≤ cQU An * ‖ω‖ * ‖u‖ :=
        (Complex.re_le_norm _).trans ((hL k _).trans
          (mul_le_mul (mul_le_mul (cQ_le An k) (norm_z_le ω k) (norm_nonneg _) hc0) (norm_z_le u k)
            (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))))
      have h2 : ‖κ k‖ ≤ Real.exp (cQU An * ‖ω‖ ^ 2) :=
        (hκ k).trans (Real.exp_le_exp.mpr (mul_le_mul (cQ_le An k)
          (pow_le_pow_left₀ (norm_nonneg _) (norm_z_le ω k) 2) (by positivity) hc0))
      calc (‖κ k‖ * Real.exp (Lf k (u.2.2 k)).re) ^ D
          ≤ (Real.exp (cQU An * ‖ω‖ ^ 2) * Real.exp (cQU An * ‖ω‖ * ‖u‖)) ^ D := by gcongr
        _ = Real.exp (D * (cQU An * ‖ω‖ ^ 2 + cQU An * ‖ω‖ * ‖u‖)) := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
        _ ≤ Real.exp (D * cQU An * (‖u‖ + ‖ω‖) ^ 2) := by
          apply Real.exp_le_exp.mpr
          have := cQU_nonneg An
          have hu := norm_nonneg u
          have hw := norm_nonneg ω
          have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
          nlinarith [mul_nonneg (mul_nonneg hD this) (mul_nonneg hu hu),
            mul_nonneg (mul_nonneg hD this) (mul_nonneg hu hw)]
    calc ∏ k, ‖f k ^ D‖ ≤ ∏ _k : Fin m, Real.exp (D * cQU An * (‖u‖ + ‖ω‖) ^ 2) :=
          Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) hk
      _ = Real.exp (m * D * cQU An * (‖u‖ + ‖ω‖) ^ 2) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf
  · have hb : ∀ j, Complex.exp ((u + ω).2.1 j) = Complex.exp (u.2.1 j) := fun j => by
      obtain ⟨a, ha⟩ := hω.2.1 j
      change Complex.exp (u.2.1 j + ω.2.1 j) = _
      rw [ha, Complex.exp_add]
      have e : Complex.exp (2 * Real.pi * I * a) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I a
      rw [e, mul_one]
    have hx : ∀ i, (u + ω).1 i = u.1 i := fun i => by
      change u.1 i + ω.1 i = u.1 i; rw [hω.1]; simp
    have hz : ∀ k c, (B k).θ ((u + ω).2.2 k) c = f k * (B k).θ (u.2.2 k) c := fun k c => by
      change (B k).θ (u.2.2 k + ω.2.2 k) c = _
      rw [hθ k]; rfl
    unfold MonoA.eval
    simp only [hx, hb, hz, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, (μs l).hγ]
    ring

/-- **Growth of the monomials.** -/
theorem sum_norm_eval_le (An : ∀ k, AbBlockAn (B k)) {L D₀ D₁ : ℕ} (μs : Fin L → MonoA d₀ d₁ B D)
    (hα : ∀ l, ∑ i, (μs l).α i ≤ D₀) (hβ : ∀ l, ∑ j, (μs l).β j ≤ D₁) {R U : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L)
    (hU : Real.log L + D₀ * Real.log (1 + R) + D₁ * R + m * D * cWU An * (1 + R) ^ 2 ≤ U)
    (u : Tan d₀ d₁ B) (hu : ‖u‖ ≤ R) : ∑ l, ‖(μs l).eval u‖ ≤ Real.exp U := by
  have h1R : 1 ≤ 1 + R := by linarith
  have hone : ∀ l, ‖(μs l).eval u‖ ≤
      (1 + R) ^ D₀ * Real.exp R ^ D₁ * Real.exp (cWU An * (1 + R) ^ 2) ^ (m * D) := by
    intro l
    unfold MonoA.eval
    rw [norm_mul, norm_mul, norm_prod, norm_prod, norm_prod]
    have ha : ∏ i, ‖u.1 i ^ (μs l).α i‖ ≤ (1 + R) ^ D₀ := by
      calc ∏ i, ‖u.1 i ^ (μs l).α i‖ ≤ ∏ i, (1 + R) ^ (μs l).α i :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
              rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((norm_x_le u i).trans (by linarith)) _
        _ = (1 + R) ^ ∑ i, (μs l).α i := prod_pow_eq_pow_sum _ _ _
        _ ≤ (1 + R) ^ D₀ := pow_le_pow_right₀ h1R (hα l)
    have hb : ∏ j, ‖Complex.exp (u.2.1 j) ^ (μs l).β j‖ ≤ Real.exp R ^ D₁ := by
      calc ∏ j, ‖Complex.exp (u.2.1 j) ^ (μs l).β j‖ ≤ ∏ j, Real.exp R ^ (μs l).β j :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
              rw [norm_pow, Complex.norm_exp]
              exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr
                (((Complex.re_le_norm _)).trans ((norm_b_le u j).trans hu))) _
        _ = Real.exp R ^ ∑ j, (μs l).β j := prod_pow_eq_pow_sum _ _ _
        _ ≤ Real.exp R ^ D₁ := pow_le_pow_right₀ (Real.one_le_exp hR) (hβ l)
    have he : ∏ k, ‖∏ c, (B k).θ (u.2.2 k) (fidx (B k) c) ^ (μs l).γ k c‖ ≤
        Real.exp (cWU An * (1 + R) ^ 2) ^ (m * D) := by
      have hk : ∀ k ∈ univ, ‖∏ c, (B k).θ (u.2.2 k) (fidx (B k) c) ^ (μs l).γ k c‖ ≤
          Real.exp (cWU An * (1 + R) ^ 2) ^ D := by
        intro k _
        rw [norm_prod]
        have hθ : ‖(B k).θ (u.2.2 k)‖ ≤ Real.exp (cWU An * (1 + R) ^ 2) :=
          ((An k).growth _).trans (Real.exp_le_exp.mpr (by
            have hz : ‖u.2.2 k‖ ≤ R := (norm_z_le u k).trans hu
            exact mul_le_mul (cW_le An k) (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity)
              (cWU_nonneg An)))
        calc ∏ c, ‖(B k).θ (u.2.2 k) (fidx (B k) c) ^ (μs l).γ k c‖
            ≤ ∏ c, Real.exp (cWU An * (1 + R) ^ 2) ^ (μs l).γ k c :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun c _ => by
                rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm _ _).trans hθ) _
          _ = Real.exp (cWU An * (1 + R) ^ 2) ^ D := by rw [prod_pow_eq_pow_sum, (μs l).hγ k]
      calc _ ≤ ∏ _k : Fin m, Real.exp (cWU An * (1 + R) ^ 2) ^ D :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hk
        _ = _ := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm D m]
    exact mul_le_mul (mul_le_mul ha hb (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)) he
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  calc ∑ l, ‖(μs l).eval u‖
      ≤ ∑ _l : Fin L, (1 + R) ^ D₀ * Real.exp R ^ D₁ * Real.exp (cWU An * (1 + R) ^ 2) ^ (m * D) :=
        sum_le_sum fun l _ => hone l
    _ = Real.exp (Real.log L + D₀ * Real.log (1 + R) + D₁ * R + m * D * cWU An * (1 + R) ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log hL0, ← Real.log_rpow (by linarith), Real.exp_log (by positivity), ← Real.exp_nat_mul,
          ← Real.exp_nat_mul]
        push_cast
        rw [Real.rpow_natCast]
        ring_nf
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hU

end LSG.AuxA
