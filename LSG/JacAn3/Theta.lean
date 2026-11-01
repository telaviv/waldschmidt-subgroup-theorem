/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn.PeriodKer

/-!
# A3.1: the entire lift `θ` of `E` and its doubling equation (STAGE_A3 §1.1)

With `d(v) = dup(germ v)₄` (nonzero on the germ ball) and `ℓ = log d = Σ pₙ` near `0`, put
`G := Σ_{n ≠ 2} pₙ / (4 − 2ⁿ)` and `Φ_k(z) := 4ᵏ G(z/2ᵏ) + (k/4) p₂(z)`. Then `Φ_{k+1} − Φ_k = 4ᵏ ℓ(z/2^{k+1})`, so

  `θ(z) := exp(−Φ_k(z)) • Ẽ_k(z)`

does not depend on `k` (no limits). Results:
* `ThetaData.theta_eq`: `θ = θ_k` for every admissible `k`;
* `ThetaData.analyticAt_theta`, `theta_ne_zero`, `theta_onQ`, `expP_eq_theta` (`[θ z] = E z`);
* **`ThetaData.theta_two_smul`**: `θ(2z) = e^{−p₂(z)} • dup(θ z)` (only the resonant quadratic term survives).
-/

noncomputable section

open Polynomial Metric Set Filter Topology
open scoped LinearAlgebra.Projectivization

namespace LSG.JacAn

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  (G : GermRad A hp hx)

/-- `d(v) = dup(germ v)₄`. -/
def GermRad.d (_G : GermRad A hp hx) (v : Fin 2 → ℂ) : ℂ := A.dup (germ A hp hx v) 4

/-- **Explicit consecutive lifts**: `Ẽ_{k+1}(z) = d(z/2^{k+1})^{4ᵏ} • Ẽ_k(z)`. -/
theorem expLift_succ_eq {k : ℕ} {z : Fin 2 → ℂ}
    (h : ((2 : ℂ) ^ (k + 1))⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε) :
    expLift A hp hx (k + 1) z = (G.d (((2 : ℂ) ^ (k + 1))⁻¹ • z)) ^ (4 ^ k) • expLift A hp hx k z := by
  set v := ((2 : ℂ) ^ (k + 1))⁻¹ • z
  obtain ⟨-, -, -, hd4, heq⟩ := G.good v h
  have h2v : (2 : ℂ) • v = ((2 : ℂ) ^ k)⁻¹ • z := by
    simp only [v, smul_smul, pow_succ, mul_inv]
    congr 1; field_simp
  set d := A.dup (germ A hp hx v) 4 with hd
  have hdup : A.dup (germ A hp hx v) = d • germ A hp hx ((2 : ℂ) • v) := by
    rw [← heq, normalize, smul_smul, ← hd, mul_inv_cancel₀ hd4, one_smul]
  have hGd : G.d v = d := rfl
  simp only [expLift]
  rw [Function.iterate_succ_apply, hdup, A.dup_iter_smul, h2v, hGd]

/-- The data for `θ`: a power series `P` of a logarithm of `d` on a ball `ball 0 ρ ⊆ ball 0 ε`. -/
structure ThetaData (G : GermRad A hp hx) where
  P : FormalMultilinearSeries ℂ (Fin 2 → ℂ) ℂ
  ρ : ℝ
  pos : 0 < ρ
  le_ε : ρ ≤ G.ε
  ball_sub : ball (0 : Fin 2 → ℂ) ρ ⊆ Metric.eball 0 P.radius
  exp_sum : ∀ v ∈ ball (0 : Fin 2 → ℂ) ρ, Complex.exp (P.sum v) = G.d v

/-- `θ`-data exist. -/
theorem exists_thetaData : Nonempty (ThetaData G) := by
  have hd0 : G.d 0 ≠ 0 := (G.good 0 (mem_ball_self G.pos)).2.2.2.1
  have hdan : ∀ v ∈ ball (0 : Fin 2 → ℂ) G.ε, AnalyticAt ℂ G.d v := fun v hv =>
    (analyticAt_pi_iff.mp ((A.dup_analytic _ (mem_univ _)).comp (G.good v hv).2.2.1)) 4
  set ℓ : (Fin 2 → ℂ) → ℂ := fun v => Complex.log (G.d 0) + Complex.log (G.d v / G.d 0)
  have hℓ : AnalyticAt ℂ ℓ 0 := analyticAt_const.add
    (((hdan 0 (mem_ball_self G.pos)).div analyticAt_const hd0).clog
      (by show G.d 0 / G.d 0 ∈ _; rw [div_self hd0]; exact Complex.one_mem_slitPlane))
  obtain ⟨P, r, hP⟩ := hℓ
  obtain ⟨ρ₁, hρ₁, hsub⟩ := Metric.mem_nhds_iff.mp (Metric.eball_mem_nhds (0 : Fin 2 → ℂ) hP.r_pos)
  refine ⟨⟨P, min ρ₁ G.ε, lt_min hρ₁ G.pos, min_le_right _ _, fun v hv => ?_, fun v hv => ?_⟩⟩
  · exact Metric.eball_subset_eball hP.r_le (hsub (ball_subset_ball (min_le_left _ _) hv))
  · have hvε : v ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball (min_le_right _ _) hv
    have hdv : G.d v ≠ 0 := (G.good v hvε).2.2.2.1
    have hs := hP.sum (hsub (ball_subset_ball (min_le_left _ _) hv))
    rw [zero_add] at hs
    rw [← hs]
    simp only [ℓ, Complex.exp_add, Complex.exp_log hd0, Complex.exp_log (div_ne_zero hdv hd0)]
    field_simp

variable {G} (D : ThetaData G)

/-- `|4 − 2ⁿ| ≥ 1` for `n ≠ 2`. -/
lemma one_le_norm_four_sub {n : ℕ} (hn : n ≠ 2) : 1 ≤ ‖(4 : ℂ) - 2 ^ n‖ := by
  have hc : (4 : ℂ) - 2 ^ n = (((4 : ℝ) - 2 ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n
    · norm_num
    · norm_num
    · exact absurd rfl hn
  · have : (8 : ℝ) ≤ 2 ^ n := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    rw [abs_of_neg (by linarith)]; linarith

/-- The series `G = Σ_{n ≠ 2} pₙ / (4 − 2ⁿ)`. -/
def ThetaData.Q : FormalMultilinearSeries ℂ (Fin 2 → ℂ) ℂ :=
  fun n => if n = 2 then 0 else ((4 : ℂ) - 2 ^ n)⁻¹ • D.P n

lemma ThetaData.norm_Q_le (n : ℕ) : ‖D.Q n‖ ≤ ‖D.P n‖ := by
  unfold ThetaData.Q
  split_ifs with hn
  · simp
  · rw [norm_smul, norm_inv]
    have h1 := one_le_norm_four_sub hn
    calc ‖(4 : ℂ) - 2 ^ n‖⁻¹ * ‖D.P n‖ ≤ 1 * ‖D.P n‖ := by
          gcongr; exact inv_le_one_of_one_le₀ h1
      _ = ‖D.P n‖ := one_mul _

lemma ThetaData.ball_sub_Q : ball (0 : Fin 2 → ℂ) D.ρ ⊆ Metric.eball 0 D.Q.radius :=
  D.ball_sub.trans (Metric.eball_subset_eball (FormalMultilinearSeries.radius_le_of_le D.norm_Q_le))

/-- `G`. -/
def ThetaData.Gs (v : Fin 2 → ℂ) : ℂ := D.Q.sum v

/-- The quadratic Taylor term `p₂(z)`. -/
def ThetaData.p2 (z : Fin 2 → ℂ) : ℂ := D.P 2 (fun _ => z)

lemma ThetaData.P_smul (n : ℕ) (c : ℂ) (w : Fin 2 → ℂ) :
    D.P n (fun _ => c • w) = c ^ n * D.P n (fun _ => w) := by
  have := (D.P n).map_smul_univ (fun _ => c) (fun _ => w)
  simpa [Finset.prod_const] using this

lemma ThetaData.Q_smul (n : ℕ) (c : ℂ) (w : Fin 2 → ℂ) :
    D.Q n (fun _ => c • w) = c ^ n * D.Q n (fun _ => w) := by
  have := (D.Q n).map_smul_univ (fun _ => c) (fun _ => w)
  simpa [Finset.prod_const] using this

lemma ThetaData.p2_smul (c : ℂ) (z : Fin 2 → ℂ) : D.p2 (c • z) = c ^ 2 * D.p2 z := D.P_smul 2 c z

/-- **The coefficient identity** `4 G(w) − G(2w) = ℓ(w) − p₂(w)`. -/
lemma ThetaData.Gs_identity {w : Fin 2 → ℂ} (hw : w ∈ ball (0 : Fin 2 → ℂ) D.ρ)
    (h2w : (2 : ℂ) • w ∈ ball (0 : Fin 2 → ℂ) D.ρ) :
    4 * D.Gs w - D.Gs ((2 : ℂ) • w) = D.P.sum w - D.p2 w := by
  have h1 := D.Q.hasSum (D.ball_sub_Q hw)
  have h2 := D.Q.hasSum (D.ball_sub_Q h2w)
  have h3 := D.P.hasSum (D.ball_sub hw)
  have h4 : HasSum (fun n => if n = 2 then D.P 2 (fun _ => w) else 0) (D.p2 w) :=
    hasSum_ite_eq 2 (D.P 2 (fun _ => w))
  have hL := (h1.mul_left 4).sub h2
  have hR := h3.sub h4
  refine hL.unique (hR.congr_fun fun n => ?_)
  simp only [D.Q_smul n 2 w]
  unfold ThetaData.Q
  split_ifs with hn
  · subst hn; simp
  · have hne : (4 : ℂ) - 2 ^ n ≠ 0 := by
      intro h0; have := one_le_norm_four_sub hn; rw [h0, norm_zero] at this; linarith
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, sub_zero]
    field_simp

/-- `Φ_k(z) = 4ᵏ G(z/2ᵏ) + (k/4) p₂(z)`. -/
def ThetaData.Phi (k : ℕ) (z : Fin 2 → ℂ) : ℂ :=
  4 ^ k * D.Gs (((2 : ℂ) ^ k)⁻¹ • z) + ((k : ℂ) / 4) * D.p2 z

/-- `θ_k = exp(−Φ_k) • Ẽ_k`. -/
def ThetaData.thetaK (k : ℕ) (z : Fin 2 → ℂ) : P9 := Complex.exp (-D.Phi k z) • expLift A hp hx k z

/-- Admissibility of `k` at `z`. -/
def ThetaData.Adm (k : ℕ) (z : Fin 2 → ℂ) : Prop := ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) D.ρ

lemma half_mem_ball {ρ : ℝ} {v : Fin 2 → ℂ} (h : v ∈ ball (0 : Fin 2 → ℂ) ρ) :
    (2 : ℂ)⁻¹ • v ∈ ball (0 : Fin 2 → ℂ) ρ := by
  rw [mem_ball_zero_iff] at h ⊢
  rw [norm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  rw [h2]; linarith [norm_nonneg v]

lemma two_pow_succ_inv_smul (k : ℕ) (z : Fin 2 → ℂ) :
    ((2 : ℂ) ^ (k + 1))⁻¹ • z = (2 : ℂ)⁻¹ • (((2 : ℂ) ^ k)⁻¹ • z) := by
  rw [smul_smul, pow_succ, mul_inv, mul_comm]

variable {D} in
lemma ThetaData.Adm.succ {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) : D.Adm (k + 1) z := by
  unfold ThetaData.Adm at h ⊢
  rw [two_pow_succ_inv_smul]; exact half_mem_ball h

variable {D} in
lemma ThetaData.Adm.mono {k k' : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) (hk : k ≤ k') : D.Adm k' z := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

variable {D} in
lemma ThetaData.Adm.memε {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) :
    ((2 : ℂ) ^ k)⁻¹ • z ∈ ball (0 : Fin 2 → ℂ) G.ε := ball_subset_ball D.le_ε h

/-- **Independence of `k`.** -/
theorem ThetaData.thetaK_succ {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) :
    D.thetaK (k + 1) z = D.thetaK k z := by
  set w := ((2 : ℂ) ^ k)⁻¹ • z with hw
  set w' := ((2 : ℂ) ^ (k + 1))⁻¹ • z with hw'
  have hw'w : w' = (2 : ℂ)⁻¹ • w := two_pow_succ_inv_smul k z
  have hwρ : w ∈ ball (0 : Fin 2 → ℂ) D.ρ := h
  have hw'ρ : w' ∈ ball (0 : Fin 2 → ℂ) D.ρ := h.succ
  have h2w' : (2 : ℂ) • w' = w := by rw [hw'w, smul_smul]; norm_num
  have hz : z = (2 : ℂ) ^ (k + 1) • w' := by
    rw [hw', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]
  have hid := D.Gs_identity hw'ρ (h2w' ▸ hwρ)
  rw [h2w'] at hid
  have hp2 : D.p2 z = 4 ^ (k + 1) * D.p2 w' := by
    rw [hz, D.p2_smul, ← pow_mul, mul_comm (k + 1) 2, pow_mul]; norm_num
  have hkey : D.Phi (k + 1) z = D.Phi k z + 4 ^ k * D.P.sum w' := by
    simp only [ThetaData.Phi, ← hw, ← hw']
    rw [hp2]
    push_cast
    linear_combination (4 : ℂ) ^ k * hid
  have hsucc := expLift_succ_eq G h.succ.memε
  have hexp : (G.d w') ^ (4 ^ k) = Complex.exp (4 ^ k * D.P.sum w') := by
    rw [← D.exp_sum w' hw'ρ, ← Complex.exp_nat_mul]; push_cast; ring_nf
  unfold ThetaData.thetaK
  rw [hsucc, hexp, smul_smul, ← Complex.exp_add, hkey]
  congr 2; ring

theorem ThetaData.thetaK_eq_of_le {k k' : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) (hk : k ≤ k') :
    D.thetaK k' z = D.thetaK k z := by
  induction hk with
  | refl => rfl
  | @step m hm ih => rw [D.thetaK_succ (h.mono hm), ih]

lemma ThetaData.exists_adm (z : Fin 2 → ℂ) : ∃ k : ℕ, D.Adm k z := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖z‖ / D.ρ) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_⟩
  unfold ThetaData.Adm
  rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_pow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, inv_mul_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ D.pos] at hk
  linarith

open scoped Classical in
/-- **The theta lift** `θ : ℂ² → ℂ⁹`. -/
def ThetaData.theta (z : Fin 2 → ℂ) : P9 := D.thetaK (Nat.find (D.exists_adm z)) z

open scoped Classical in
theorem ThetaData.theta_eq {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) : D.theta z = D.thetaK k z :=
  (D.thetaK_eq_of_le (Nat.find_spec (D.exists_adm z)) (Nat.find_min' _ h)).symm

lemma ThetaData.thetaK_ne_zero {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) : D.thetaK k z ≠ 0 :=
  smul_ne_zero (Complex.exp_ne_zero _) (expLift_ne_zero G h.memε)

theorem ThetaData.theta_ne_zero (z : Fin 2 → ℂ) : D.theta z ≠ 0 := by
  obtain ⟨k, hk⟩ := D.exists_adm z
  rw [D.theta_eq hk]; exact D.thetaK_ne_zero hk

theorem ThetaData.theta_onQ (z : Fin 2 → ℂ) : A.OnQ (D.theta z) := by
  obtain ⟨k, hk⟩ := D.exists_adm z
  rw [D.theta_eq hk]; exact A.onQ_smul _ _ (expLift_onQ G hk.memε)

/-- **`[θ z] = E z`.** -/
theorem ThetaData.expP_eq_theta (z : Fin 2 → ℂ) :
    expP G z = Projectivization.mk ℂ (D.theta z) (D.theta_ne_zero z) := by
  obtain ⟨k, hk⟩ := D.exists_adm z
  rw [expP_eq G hk.memε, Projectivization.mk_eq_mk_iff']
  refine ⟨Complex.exp (D.Phi k z), ?_⟩
  rw [D.theta_eq hk, ThetaData.thetaK, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    one_smul]

lemma ThetaData.analyticAt_p2 (z : Fin 2 → ℂ) : AnalyticAt ℂ D.p2 z :=
  (D.P 2).analyticAt.comp (analyticAt_pi_iff.mpr fun _ => analyticAt_id)

lemma ThetaData.analyticAt_thetaK {k : ℕ} {z : Fin 2 → ℂ} (h : D.Adm k z) :
    AnalyticAt ℂ (D.thetaK k) z := by
  have hQ : 0 < D.Q.radius := by
    have := D.ball_sub_Q (mem_ball_self D.pos)
    simpa using this
  have hG : AnalyticAt ℂ D.Gs (((2 : ℂ) ^ k)⁻¹ • z) :=
    (D.Q.hasFPowerSeriesOnBall hQ).analyticAt_of_mem (D.ball_sub_Q h)
  have hl : AnalyticAt ℂ (fun z : Fin 2 → ℂ => ((2 : ℂ) ^ k)⁻¹ • z) z := by fun_prop
  have hΦ : AnalyticAt ℂ (D.Phi k) z :=
    (analyticAt_const.mul (hG.comp hl)).add (analyticAt_const.mul (D.analyticAt_p2 z))
  exact (hΦ.neg.cexp).smul (analyticAt_expLift G h.memε)

/-- **`θ` is entire.** -/
theorem ThetaData.analyticAt_theta (z : Fin 2 → ℂ) : AnalyticAt ℂ D.theta z := by
  obtain ⟨k, hk⟩ := D.exists_adm z
  have hopen : IsOpen {z' : Fin 2 → ℂ | D.Adm k z'} :=
    isOpen_ball.preimage (continuous_const_smul _)
  refine (D.analyticAt_thetaK hk).congr ?_
  filter_upwards [hopen.mem_nhds hk] with z' hz' using (D.theta_eq hz').symm

/-- `Ẽ_{k+1}(2z) = dup(Ẽ_k(z))`. -/
lemma expLift_two_smul (k : ℕ) (z : Fin 2 → ℂ) :
    expLift A hp hx (k + 1) ((2 : ℂ) • z) = A.dup (expLift A hp hx k z) := by
  have h : ((2 : ℂ) ^ (k + 1))⁻¹ • ((2 : ℂ) • z) = ((2 : ℂ) ^ k)⁻¹ • z := by
    rw [smul_smul, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]
  simp only [expLift, h, Function.iterate_succ_apply']

/-- **The doubling equation** `θ(2z) = e^{−p₂(z)} • dup(θ z)`. -/
theorem ThetaData.theta_two_smul (z : Fin 2 → ℂ) :
    D.theta ((2 : ℂ) • z) = Complex.exp (-D.p2 z) • A.dup (D.theta z) := by
  obtain ⟨k, hk⟩ := D.exists_adm z
  have hk' : D.Adm (k + 1) ((2 : ℂ) • z) := by
    unfold ThetaData.Adm at hk ⊢
    rw [smul_smul, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]; exact hk
  rw [D.theta_eq hk', D.theta_eq hk]
  unfold ThetaData.thetaK
  rw [expLift_two_smul, A.dup_smul, smul_smul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  have hw : ((2 : ℂ) ^ (k + 1))⁻¹ • ((2 : ℂ) • z) = ((2 : ℂ) ^ k)⁻¹ • z := by
    rw [smul_smul, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]
  simp only [ThetaData.Phi, hw, D.p2_smul]
  push_cast
  ring

end LSG.JacAn
