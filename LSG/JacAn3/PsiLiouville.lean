/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.PsiPrep

/-!
# A3.6: ψ-Liouville; correctness and completeness of the 81 laws on `E(ℂ²)` (STAGE_A3 §2)

With `Θ = θ_N` and `N_km(u, v) = lawK k m (Θ u) (Θ v)`:
* column 0 is `∥ Θ(u + v)` (`hom_untrans`), row 0 is `∥ Θ(u − v)` (`law_S1` + `[−1]`);
* `rank_one` gives `N₀₀ · (N_km Θ_k′Θ_m′ − N_k′m′ Θ_kΘ_m) = 0`, and `N₀₀ ≢ 0` (`θ₀ ≢ 0`), so the cross identity holds
  everywhere (identity theorem); `ψ = N_{k₀m₀} / (Θ_{k₀}(u+v) Θ_{m₀}(u−v))` is entire on `ℂ² × ℂ²`;
* `|ψ|` is `Λ × Λ`-periodic (`norm_facN`), hence bounded (fundamental domain of `latBasis`), hence constant
  (Liouville);
* **`laws_eq`**: `lawK k m (Θ u) (Θ v) = κ Θ_k(u + v) Θ_m(u − v)`, `κ ≠ 0`;
* **`law_correct`**: law `m` at `(Θ u, Θ v)` is `∥ Θ(u + v)`; **`laws_complete`**: some law is nonzero.
-/

noncomputable section

open Metric Set Filter Topology Bornology

namespace LSG.JacAn

open Beta

lemma par_exists_smul {X Y : P9} (h : Par X Y) (hY : Y ≠ 0) : ∃ a : ℂ, X = a • Y := by
  have hm := nzIdx_spec hY
  refine ⟨X (nzIdx Y) / Y (nzIdx Y), funext fun i => ?_⟩
  have := h i (nzIdx Y)
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

lemma eq_zero_of_mul_eq_zero_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} (hf : ∀ x, AnalyticAt ℂ f x) (hg : ∀ x, AnalyticAt ℂ g x) (h : ∀ x, f x * g x = 0)
    {x₀ : E} (hx₀ : f x₀ ≠ 0) (x : E) : g x = 0 := by
  have hev : g =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [(hf x₀).continuousAt.eventually_ne hx₀] with y hy
    exact (mul_eq_zero.mp (h y)).resolve_left hy
  have hg' : AnalyticOnNhd ℂ g univ := fun y _ => hg y
  exact hg'.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ x₀) hev (mem_univ x)

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

local notation "E2" => (Fin 2 → ℂ) × (Fin 2 → ℂ)

lemma ThetaData.hom_N (u v : Fin 2 → ℂ) : Par (A.law0 (D.thetaN u) (D.thetaN v)) (D.thetaN (u + v)) := by
  simp only [ThetaData.thetaN, A.law0_smul_left, A.law0_smul_right]
  exact ((D.hom_untrans u v).smul_left _).smul_left _ |>.smul_right _

lemma ThetaData.neg_N (v : Fin 2 → ℂ) : Par (A.negP (D.thetaN v)) (D.thetaN (-v)) := by
  simp only [ThetaData.thetaN, ← negL_apply A, map_smul]
  rw [negL_apply A]
  exact ((D.theta_neg_par v).smul_left _).smul_right _

lemma ThetaData.col0 (u v : Fin 2 → ℂ) : ∃ a : ℂ, ∀ k, A.lawK k 0 (D.thetaN u) (D.thetaN v) =
    a * D.thetaN (u + v) k := by
  obtain ⟨a, ha⟩ := par_exists_smul (D.hom_N u v) (D.thetaN_ne_zero _)
  exact ⟨a, fun k => by rw [← A.law0_lawK, ha]; rfl⟩

lemma ThetaData.row0 (u v : Fin 2 → ℂ) : ∃ b : ℂ, ∀ m, A.lawK 0 m (D.thetaN u) (D.thetaN v) =
    b * D.thetaN (u - v) m := by
  obtain ⟨c, hc⟩ := par_exists_smul (D.neg_N v) (D.thetaN_ne_zero _)
  obtain ⟨a, ha⟩ := par_exists_smul (D.hom_N u (-v)) (D.thetaN_ne_zero _)
  refine ⟨c ^ 2 * a, fun m => ?_⟩
  rw [← A.lawK_S1, ← A.law0_lawK, hc, A.law0_smul_right, ha, ← sub_eq_add_neg]
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- `N_km(u, v)`. -/
def ThetaData.NK (k m : Fin 9) (x : E2) : ℂ := A.lawK k m (D.thetaN x.1) (D.thetaN x.2)

lemma ThetaData.analyticAt_NK (k m : Fin 9) (x : E2) : AnalyticAt ℂ (D.NK k m) x := by
  have hpr : AnalyticAt ℂ (fun x : E2 => (D.thetaN x.1, D.thetaN x.2)) x :=
    ((D.analyticAt_thetaN x.1).comp analyticAt_fst).prod ((D.analyticAt_thetaN x.2).comp analyticAt_snd)
  exact AnalyticAt.comp (g := fun XY : P9 × P9 => A.lawK k m XY.1 XY.2) (A.lawK_analytic k m _ (mem_univ _)) hpr

lemma ThetaData.analyticAt_plus (k : Fin 9) (x : E2) : AnalyticAt ℂ (fun x : E2 => D.thetaN (x.1 + x.2) k) x :=
  (analyticAt_pi_iff.mp (AnalyticAt.comp (g := D.thetaN) (f := fun x : E2 => x.1 + x.2)
    (D.analyticAt_thetaN _) (analyticAt_fst.add analyticAt_snd))) k

lemma ThetaData.analyticAt_minus (k : Fin 9) (x : E2) : AnalyticAt ℂ (fun x : E2 => D.thetaN (x.1 - x.2) k) x :=
  (analyticAt_pi_iff.mp (AnalyticAt.comp (g := D.thetaN) (f := fun x : E2 => x.1 - x.2)
    (D.analyticAt_thetaN _) (analyticAt_fst.sub analyticAt_snd))) k

/-- `N₀₀ ≢ 0`. -/
lemma ThetaData.exists_N00_ne : ∃ x₀ : E2, D.NK 0 0 x₀ ≠ 0 := by
  obtain ⟨w₁, hw₁⟩ := D.exists_theta0_ne
  obtain ⟨a, ha, h0⟩ := D.theta_zero
  refine ⟨(w₁, 0), ?_⟩
  have hN0 : D.thetaN w₁ 0 ≠ 0 := by
    simp only [ThetaData.thetaN, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Complex.exp_ne_zero _) hw₁
  simp only [ThetaData.NK]
  rw [show D.thetaN 0 = (Complex.exp (-D.lamN 0) * a) • origin9 by
    rw [ThetaData.thetaN, h0, smul_smul], A.lawK_smul_right, ← A.law0_lawK, A.law0_origin]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Complex.exp_ne_zero _) ha))
    (mul_ne_zero (mul_ne_zero (by norm_num) hN0) hN0)

/-- **The cross identity.** -/
theorem ThetaData.cross (k m k' m' : Fin 9) (x : E2) :
    D.NK k m x * D.thetaN (x.1 + x.2) k' * D.thetaN (x.1 - x.2) m' =
      D.NK k' m' x * D.thetaN (x.1 + x.2) k * D.thetaN (x.1 - x.2) m := by
  obtain ⟨x₀, hx₀⟩ := D.exists_N00_ne
  have hmul : ∀ x : E2, D.NK 0 0 x * (D.NK k m x * D.thetaN (x.1 + x.2) k' * D.thetaN (x.1 - x.2) m' -
      D.NK k' m' x * D.thetaN (x.1 + x.2) k * D.thetaN (x.1 - x.2) m) = 0 := by
    intro x
    obtain ⟨a, ha⟩ := D.col0 x.1 x.2
    obtain ⟨b, hb⟩ := D.row0 x.1 x.2
    have r1 := A.rank_one k m _ _ (D.thetaN_onQ x.1) (D.thetaN_onQ x.2)
    have r2 := A.rank_one k' m' _ _ (D.thetaN_onQ x.1) (D.thetaN_onQ x.2)
    simp only [ThetaData.NK]
    rw [ha k, hb m] at r1
    rw [ha k', hb m'] at r2
    linear_combination (D.thetaN (x.1 + x.2) k' * D.thetaN (x.1 - x.2) m') * r1 -
      (D.thetaN (x.1 + x.2) k * D.thetaN (x.1 - x.2) m) * r2
  have := eq_zero_of_mul_eq_zero_analytic (D.analyticAt_NK 0 0)
    (fun x => (((D.analyticAt_NK k m x).mul (D.analyticAt_plus k' x)).mul (D.analyticAt_minus m' x)).sub
      (((D.analyticAt_NK k' m' x).mul (D.analyticAt_plus k x)).mul (D.analyticAt_minus m x))) hmul hx₀ x
  exact sub_eq_zero.mp this

/-- **ψ.** -/
def ThetaData.psi (x : E2) : ℂ :=
  D.NK (nzIdx (D.thetaN (x.1 + x.2))) (nzIdx (D.thetaN (x.1 - x.2))) x /
    (D.thetaN (x.1 + x.2) (nzIdx (D.thetaN (x.1 + x.2))) * D.thetaN (x.1 - x.2) (nzIdx (D.thetaN (x.1 - x.2))))

theorem ThetaData.psi_spec (k m : Fin 9) (x : E2) :
    D.NK k m x = D.psi x * D.thetaN (x.1 + x.2) k * D.thetaN (x.1 - x.2) m := by
  have h1 := nzIdx_spec (D.thetaN_ne_zero (x.1 + x.2))
  have h2 := nzIdx_spec (D.thetaN_ne_zero (x.1 - x.2))
  have := D.cross k m (nzIdx (D.thetaN (x.1 + x.2))) (nzIdx (D.thetaN (x.1 - x.2))) x
  unfold ThetaData.psi
  field_simp
  linear_combination this

theorem ThetaData.analyticAt_psi (x₀ : E2) : AnalyticAt ℂ D.psi x₀ := by
  set k := nzIdx (D.thetaN (x₀.1 + x₀.2))
  set m := nzIdx (D.thetaN (x₀.1 - x₀.2))
  have h1 := nzIdx_spec (D.thetaN_ne_zero (x₀.1 + x₀.2))
  have h2 := nzIdx_spec (D.thetaN_ne_zero (x₀.1 - x₀.2))
  have hden : D.thetaN (x₀.1 + x₀.2) k * D.thetaN (x₀.1 - x₀.2) m ≠ 0 := mul_ne_zero h1 h2
  have han := (D.analyticAt_plus k x₀).mul (D.analyticAt_minus m x₀)
  refine ((D.analyticAt_NK k m x₀).div han hden).congr ?_
  filter_upwards [han.continuousAt.eventually_ne hden] with x hxx
  simp only [Pi.mul_apply] at hxx
  change D.NK k m x / (D.thetaN (x.1 + x.2) k * D.thetaN (x.1 - x.2) m) = D.psi x
  rw [D.psi_spec k m x, mul_assoc, mul_div_assoc, div_self hxx, mul_one]

lemma ThetaData.norm_facN_mul {c : Fin 2 → ℂ} (hc : c ∈ latt) (u v : Fin 2 → ℂ) :
    ‖D.facN c (u + v)‖ * ‖D.facN c (u - v)‖ = ‖D.facN c u‖ ^ 2 := by
  rw [D.norm_facN hc, D.norm_facN hc, D.norm_facN hc, ← Real.exp_add, sq, ← Real.exp_add]
  congr 1
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re]; ring

lemma ThetaData.norm_facN_mul' {c : Fin 2 → ℂ} (hc : c ∈ latt) (u v : Fin 2 → ℂ) :
    ‖D.facN c (u + v)‖ * ‖D.facN (-c) (u - v)‖ = ‖D.facN c v‖ ^ 2 := by
  have pc := isPer_of_mem_latt (G := G) hc
  have pnc := isPer_of_mem_latt (G := G) (neg_mem hc)
  rw [D.norm_facN hc, D.norm_facN (neg_mem hc), D.norm_facN hc, D.Lf_neg pc pnc, ← Real.exp_add, sq,
    ← Real.exp_add]
  congr 1
  simp only [ContinuousLinearMap.neg_apply, map_add, map_sub, map_neg, Complex.add_re, Complex.sub_re,
    Complex.neg_re]
  ring

/-- `|ψ|` is periodic in the first variable. -/
theorem ThetaData.psi_per1 {c : Fin 2 → ℂ} (hc : c ∈ latt) (u v : Fin 2 → ℂ) :
    ‖D.psi (u + c, v)‖ = ‖D.psi (u, v)‖ := by
  have pc := isPer_of_mem_latt (G := G) hc
  set k := nzIdx (D.thetaN (u + v))
  set m := nzIdx (D.thetaN (u - v))
  have h1 := nzIdx_spec (D.thetaN_ne_zero (u + v))
  have h2 := nzIdx_spec (D.thetaN_ne_zero (u - v))
  have e1 := D.psi_spec k m (u + c, v)
  have e2 := D.psi_spec k m (u, v)
  simp only [ThetaData.NK] at e1 e2
  rw [D.thetaN_add pc u, A.lawK_smul_left, e2, show u + c + v = (u + v) + c by abel,
    show u + c - v = (u - v) + c by abel, D.thetaN_add pc, D.thetaN_add pc] at e1
  simp only [Pi.smul_apply, smul_eq_mul] at e1
  have hne : D.thetaN (u + v) k * D.thetaN (u - v) m ≠ 0 := mul_ne_zero h1 h2
  have e3 : D.facN c u ^ 2 * D.psi (u, v) = D.psi (u + c, v) * (D.facN c (u + v) * D.facN c (u - v)) := by
    apply mul_right_cancel₀ hne; linear_combination e1
  have hn := congrArg norm e3
  rw [norm_mul, norm_mul, norm_mul, norm_pow, ← D.norm_facN_mul hc u v] at hn
  have hf1 := norm_pos_iff.mpr (D.fac_ne_zero pc (u + v))
  have hp1 : 0 < ‖D.facN c (u + v)‖ := by
    rw [ThetaData.facN, norm_mul]; exact mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hf1
  have hf2 := norm_pos_iff.mpr (D.fac_ne_zero pc (u - v))
  have hp2 : 0 < ‖D.facN c (u - v)‖ := by
    rw [ThetaData.facN, norm_mul]; exact mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hf2
  have hpos := mul_pos hp1 hp2
  nlinarith [mul_pos hpos hpos]

/-- `|ψ|` is periodic in the second variable. -/
theorem ThetaData.psi_per2 {c : Fin 2 → ℂ} (hc : c ∈ latt) (u v : Fin 2 → ℂ) :
    ‖D.psi (u, v + c)‖ = ‖D.psi (u, v)‖ := by
  have pc := isPer_of_mem_latt (G := G) hc
  have pnc := isPer_of_mem_latt (G := G) (neg_mem hc)
  set k := nzIdx (D.thetaN (u + v))
  set m := nzIdx (D.thetaN (u - v))
  have h1 := nzIdx_spec (D.thetaN_ne_zero (u + v))
  have h2 := nzIdx_spec (D.thetaN_ne_zero (u - v))
  have e1 := D.psi_spec k m (u, v + c)
  have e2 := D.psi_spec k m (u, v)
  simp only [ThetaData.NK] at e1 e2
  rw [D.thetaN_add pc v, A.lawK_smul_right, e2, show u + (v + c) = (u + v) + c by abel,
    show u - (v + c) = (u - v) + -c by abel, D.thetaN_add pc, D.thetaN_add pnc] at e1
  simp only [Pi.smul_apply, smul_eq_mul] at e1
  have hne : D.thetaN (u + v) k * D.thetaN (u - v) m ≠ 0 := mul_ne_zero h1 h2
  have e3 : D.facN c v ^ 2 * D.psi (u, v) =
      D.psi (u, v + c) * (D.facN c (u + v) * D.facN (-c) (u - v)) := by
    apply mul_right_cancel₀ hne; linear_combination e1
  have hn := congrArg norm e3
  rw [norm_mul, norm_mul, norm_mul, norm_pow, ← D.norm_facN_mul' hc u v] at hn
  have hp1 : 0 < ‖D.facN c (u + v)‖ := by
    rw [ThetaData.facN, norm_mul]
    exact mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) (norm_pos_iff.mpr (D.fac_ne_zero pc _))
  have hp2 : 0 < ‖D.facN (-c) (u - v)‖ := by
    rw [ThetaData.facN, norm_mul]
    exact mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) (norm_pos_iff.mpr (D.fac_ne_zero pnc _))
  have hpos := mul_pos hp1 hp2
  nlinarith [mul_pos hpos hpos]

/-- The fundamental parallelepiped. -/
def fundDom : Set (Fin 2 → ℂ) := (fun t : Fin 4 → ℝ => ∑ i, t i • latBasis i) '' Icc 0 1

lemma isCompact_fundDom : IsCompact fundDom :=
  isCompact_Icc.image (continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const)

lemma exists_fund (z : Fin 2 → ℂ) : ∃ f ∈ fundDom, ∃ c ∈ latt, z = f + c := by
  set r := latBasis.repr z
  refine ⟨∑ i, Int.fract (r i) • latBasis i, ⟨fun i => Int.fract (r i),
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, rfl⟩,
    ∑ i, (⌊r i⌋ : ℤ) • latBasis i, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _
    exact ⟨i, (latBasis_apply i).symm⟩
  · conv_lhs => rw [← latBasis.sum_repr z]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, ← add_smul, Int.fract_add_floor]

/-- **ψ is constant** (Liouville on `ℂ² × ℂ²`). -/
theorem ThetaData.psi_const (x y : E2) : D.psi x = D.psi y := by
  have hcont : Continuous D.psi := continuous_iff_continuousAt.mpr fun x => (D.analyticAt_psi x).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_fundDom.prod isCompact_fundDom).exists_bound_of_continuousOn hcont.continuousOn
  have hb : IsBounded (range D.psi) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨u, v⟩, rfl⟩
    obtain ⟨f, hf, c, hc, rfl⟩ := exists_fund u
    obtain ⟨f', hf', c', hc', rfl⟩ := exists_fund v
    rw [D.psi_per1 hc, D.psi_per2 hc']
    exact hM (f, f') ⟨hf, hf'⟩
  have hdiff : Differentiable ℂ D.psi := fun x => (D.analyticAt_psi x).differentiableAt
  exact hdiff.apply_eq_apply_of_bounded hb x y

/-- **The 81 laws on `E(ℂ²)`**: `lawK k m (Θ u) (Θ v) = κ Θ_k(u + v) Θ_m(u − v)` with `κ ≠ 0`. -/
theorem ThetaData.laws_eq : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (u v : Fin 2 → ℂ) (k m : Fin 9),
    A.lawK k m (D.thetaN u) (D.thetaN v) = κ * D.thetaN (u + v) k * D.thetaN (u - v) m := by
  refine ⟨D.psi (0, 0), ?_, fun u v k m => ?_⟩
  · intro h0
    obtain ⟨x₀, hx₀⟩ := D.exists_N00_ne
    apply hx₀
    rw [D.psi_spec, D.psi_const x₀ (0, 0), h0]; ring
  · have := D.psi_spec k m (u, v)
    rw [D.psi_const (u, v) (0, 0)] at this
    exact this

/-- **Completeness on the image**: at every pair of points of `E(ℂ²)` some law is nonzero. -/
theorem ThetaData.laws_complete (u v : Fin 2 → ℂ) : ∃ k m : Fin 9, A.lawK k m (D.thetaN u) (D.thetaN v) ≠ 0 := by
  obtain ⟨κ, hκ, h⟩ := D.laws_eq
  refine ⟨nzIdx (D.thetaN (u + v)), nzIdx (D.thetaN (u - v)), ?_⟩
  rw [h]
  exact mul_ne_zero (mul_ne_zero hκ (nzIdx_spec (D.thetaN_ne_zero _))) (nzIdx_spec (D.thetaN_ne_zero _))

/-- **Correctness**: law `m` at `(Θ u, Θ v)` is a multiple of `Θ (u + v)`. -/
theorem ThetaData.law_correct (u v : Fin 2 → ℂ) (m : Fin 9) :
    ∃ a : ℂ, (fun k => A.lawK k m (D.thetaN u) (D.thetaN v)) = a • D.thetaN (u + v) := by
  obtain ⟨κ, -, h⟩ := D.laws_eq
  exact ⟨κ * D.thetaN (u - v) m, funext fun k => by rw [h]; simp only [Pi.smul_apply, smul_eq_mul]; ring⟩

/-- **Every law computes addition on `E(ℂ²)` wherever it is nonzero**: `[law_m(Θ u, Θ v)] = E (u + v)`. -/
theorem ThetaData.law_computes_add (u v : Fin 2 → ℂ) (m : Fin 9)
    (hne : (fun k => A.lawK k m (D.thetaN u) (D.thetaN v)) ≠ 0) :
    Projectivization.mk ℂ _ hne = expP G (u + v) := by
  obtain ⟨a, ha⟩ := D.law_correct u v m
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hne ha
  rw [D.expP_eq_thetaN, Projectivization.mk_eq_mk_iff']
  exact ⟨a, ha.symm⟩

end LSG.JacAn
