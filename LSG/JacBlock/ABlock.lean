/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlock.SurjFactsInst
import LSG.JacBlock.Hilb
import LSG.JacBlock.WMv
import LSG.JacBlock.LawMv
import LSG.JacBlock.Simple
import LSG.JacAn4.Surj
import LSG.JacAn3.TaylorCharts

/-!
# A4.6: the A-block `AbBlock` instance

`aBlockOf D lci…` builds `LSG.MEB.AbBlock` from a `θ`-datum `D : ThetaData G` over A1's `a1Facts` and the B5
data (`lci_*`, supplied by A1, passed as arguments until they land). Field sources:
* model: `gens = gensMv` (9 quadrics + 3 cubics); `θ = D.thetaN`, `θ_model` from `thetaN_onQ` + `onQ_iff_gens`;
* periods: `per = kerE G`; `discreteTopology_kerE`; `per_span` from `latBasis ⊆ latt ≤ kerE`; `θ_per` and `θ_ker` from
  `expP_eq_thetaN` (for `θ_ker`: the laws, `θ w ∥ θ z ⇒ θ (w − z) ∥ θ 0`);
* `surj`: `ThetaData.surjA surjFacts`;
* laws: `law m k = spMv (Data.law k m)` (column `m` of `A32`), `law_eq`/`law_complete` from `ThetaData.laws_eq`;
* charts `{0, 4, 8}` (`quadA_cover`), `W = Wmv` (`flowW`, `W4C`, `W8C`, speed 1), `θ_flow` from `theta_PF0`,
  `theta_PF4`, `theta_PF_of_rel` (chart 8, with a point where `θ₈ ≠ 0` found through `surjA`);
* `i₀ = 4`, `is = (1, 8)`, `coords_locInv` with `germDerEquiv` (`W4_origin_indep`);
* `simple = simple_kerE`; `hilb` = `hilbA` (`y = (X₀, X₄, X₈)`, degree 14).

A5 constraints (STAGE_A4 §7.3): `g = 2`, `N = 9` by `rfl`, `θ = D.thetaN`, `per = kerE G`, `i₀ = 4`.
-/

noncomputable section

open MvPolynomial Filter Topology LSG.JacAn LSG.Jac

namespace LSG.JacBlock

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

/-! ### Periods -/

theorem per_span_kerE : Submodule.span ℝ (kerE G : Set (Fin 2 → ℂ)) = ⊤ := by
  rw [eq_top_iff, ← latBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨e, rfl⟩
  rw [latBasis_apply]
  exact LSG.W88.latt_le_kerE G (AddSubgroup.subset_closure ⟨e, rfl⟩)

lemma mk_thetaN_eq (z w : Fin 2 → ℂ) : expP G z = expP G w ↔ ∃ c : ℂ, D.thetaN z = c • D.thetaN w := by
  rw [D.expP_eq_thetaN, D.expP_eq_thetaN, Projectivization.mk_eq_mk_iff']
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

theorem theta_per : ∀ ω ∈ kerE G, ∀ z, ∃ c : ℂ, c ≠ 0 ∧ D.thetaN (z + ω) = c • D.thetaN z := by
  intro ω hω z
  have h := expP_periodic_of_ker G hω z
  obtain ⟨c, hc⟩ := (mk_thetaN_eq D _ _).mp h
  refine ⟨c, ?_, hc⟩
  rintro rfl
  rw [zero_smul] at hc
  exact D.thetaN_ne_zero _ hc

theorem theta_ker : ∀ z w, (∃ c : ℂ, D.thetaN w = c • D.thetaN z) → w - z ∈ kerE G := by
  rintro z w ⟨c, hc⟩
  obtain ⟨κ, hκ, hlaw⟩ := D.laws_eq
  -- `θ(w + z)_k θ(w − z)_m = c² θ(2z)_k θ(0)_m`
  have key : ∀ k m : Fin 9, κ * D.thetaN (w + z) k * D.thetaN (w - z) m =
      c ^ 2 * (κ * D.thetaN (z + z) k * D.thetaN (z - z) m) := by
    intro k m
    rw [← hlaw, ← hlaw, hc, a1Facts.lawK_smul_left]
  set k := nzIdx (D.thetaN (w + z))
  have hk : D.thetaN (w + z) k ≠ 0 := nzIdx_spec (D.thetaN_ne_zero _)
  change expP G (w - z) = expP G 0
  refine (mk_thetaN_eq D _ _).mpr ⟨c ^ 2 * D.thetaN (z + z) k / D.thetaN (w + z) k, ?_⟩
  funext m
  have := key k m
  rw [sub_self] at this
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk]
  apply mul_left_cancel₀ hκ
  linear_combination this

/-! ### Laws -/

lemma evalLaw_law (m : Fin 9) (X Y : Fin 9 → ℂ) :
    LSG.MEB.evalLaw (fun k => spMv (Data.law k m)) X Y = fun k => a1Facts.lawK k m X Y := by
  funext k
  simp only [LSG.MEB.evalLaw, eval_spMv]
  rfl

/-! ### Chart flows -/

lemma W8G_smul (j : Fin 2) (a : ℂ) (X : P9) : W8G j (a • X) = a ^ 2 • W8G j X := by
  funext i
  fin_cases j <;> fin_cases i <;> simp [W8G, W8n] <;> ring

lemma pf_thetaN {W : Fin 2 → P9 → P9} (hW : ∀ j (a : ℂ) X, W j (a • X) = a ^ 2 • W j X) {c : Fin 9}
    {z : Fin 2 → ℂ} (h : PFAt W 1 c D.theta z) : PFAt W 1 c D.thetaN z :=
  h.of_eventually_smul hW (D.analyticAt_theta z) (D.analyticAt_thetaN z) (nzIdx_spec (D.theta_ne_zero z))
    (Eventually.of_forall fun _ => ⟨_, rfl⟩)

/-- A point of the image with `θ₈ ≠ 0` (`(0, …, 0, 2, 1) ∈ V(Q)`, then `surjA`). -/
lemma exists_theta8_ne : ∃ w, D.theta w 8 ≠ 0 := by
  set P : P9 := ![0, 0, 0, 0, 0, 0, 0, 2, 1]
  have hP : OnQ P := by
    rw [onQ_iff]; intro j; fin_cases j <;> simp [quad, P] <;> norm_num
  have hP0 : P ≠ 0 := fun h => by simpa [P] using congrFun h 8
  obtain ⟨z, c, hz⟩ := ThetaData.surjA surjFacts D P hP0 hP
  refine ⟨z, fun h0 => ?_⟩
  have := congrFun hz 8
  simp only [Pi.smul_apply, smul_eq_mul, ThetaData.thetaN, h0, mul_zero] at this
  simp [P] at this

theorem theta_flow : ∀ c ∈ ({0, 4, 8} : Finset (Fin 9)), ∀ (j : Fin 2) (l : Fin 9) (z : Fin 2 → ℂ),
    D.thetaN z c * fderiv ℂ D.thetaN z (Pi.single j 1) l - D.thetaN z l * fderiv ℂ D.thetaN z (Pi.single j 1) c =
      eval (D.thetaN z) (Wmv c j l) := by
  intro c hc j l z
  have hj : ∀ (W : Fin 2 → P9 → P9) (Y : P9),
      (Pi.single j (1 : ℂ) : Fin 2 → ℂ) 0 * W 0 Y l + (Pi.single j (1 : ℂ) : Fin 2 → ℂ) 1 * W 1 Y l = W j Y l := by
    intro W Y; fin_cases j <;> simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · have h := pf_thetaN D flowW_smul (D.theta_PF0 z) (Pi.single j 1) l
    rw [h, one_mul, hj, Wmv, if_pos rfl, eval_Wc0]
  · have h := pf_thetaN D a1Facts.W4_smul (D.theta_PF4 z) (Pi.single j 1) l
    rw [h, one_mul, hj, Wmv, if_neg (by decide), if_pos rfl, eval_Wc4]
    try rfl
  · obtain ⟨w₂, hw₂⟩ := exists_theta8_ne D
    have h8 := D.theta_PF_of_rel a1Facts.W8 8 (fun j l a b => (a1Facts.W8num j l a b : ℂ) / a1Facts.W8den)
      a1Facts.W8_table a1Facts.W8rel a1Facts.W8_eight hw₂ z
    have h := pf_thetaN D (fun j a X => W8G_smul j a X) h8 (Pi.single j 1) l
    rw [h, one_mul, hj, Wmv, if_neg (by decide), if_neg (by decide), if_pos rfl, eval_Wc8]
    try rfl

/-! ### Coordinates at the origin -/

lemma thetaN_zero : ∃ μ : ℂ, μ ≠ 0 ∧ D.thetaN 0 = μ • origin9 := by
  obtain ⟨a, ha, h0⟩ := D.theta_zero
  exact ⟨Complex.exp (-D.lamN 0) * a, mul_ne_zero (Complex.exp_ne_zero _) ha, by
    rw [ThetaData.thetaN, h0, smul_smul]⟩

theorem coords_locInv : ∃ f' : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ),
    HasFDerivAt (fun z (j : Fin 2) => D.thetaN z (![1, 8] j) / D.thetaN z 4)
      (f' : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) 0 := by
  obtain ⟨μ, hμ, h0⟩ := thetaN_zero D
  set F' := fderiv ℂ D.thetaN 0
  have hF : HasFDerivAt D.thetaN F' 0 := (D.analyticAt_thetaN 0).differentiableAt.hasFDerivAt
  have h4 : D.thetaN 0 4 = μ := by rw [h0]; simp [origin9]
  have hl0 : ∀ l : Fin 9, l ≠ 4 → D.thetaN 0 l = 0 := fun l hl => by
    rw [h0]; simp [origin9, Pi.single_apply, hl]
  -- the derivative of each coordinate quotient
  have hq : ∀ l : Fin 9, l ≠ 4 → HasFDerivAt (fun z => D.thetaN z l / D.thetaN z 4)
      (μ⁻¹ • (prj l).comp F') 0 := by
    intro l hl
    have hc : HasFDerivAt (fun z => D.thetaN z l) ((prj l).comp F') 0 := (prj l).hasFDerivAt.comp 0 hF
    have hd : HasFDerivAt (fun z => D.thetaN z 4) ((prj 4).comp F') 0 := (prj 4).hasFDerivAt.comp 0 hF
    have hinv : HasFDerivAt (fun z => (D.thetaN z 4)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℂ (-(D.thetaN 0 4 ^ 2)⁻¹)).comp ((prj 4).comp F')) 0 :=
      (hasFDerivAt_inv (by rw [h4]; exact hμ)).comp 0 hd
    have := hc.mul hinv
    simp only [div_eq_mul_inv]
    convert this using 1
    simp [hl0 l hl, h4]
    try (ext; simp)
  have hpi : HasFDerivAt (fun z (j : Fin 2) => D.thetaN z (![1, 8] j) / D.thetaN z 4)
      (ContinuousLinearMap.pi fun j : Fin 2 => μ⁻¹ • (prj (![1, 8] j)).comp F') 0 := by
    refine hasFDerivAt_pi.mpr fun j => ?_
    fin_cases j
    · exact hq 1 (by decide)
    · exact hq 8 (by decide)
  refine ⟨germDerEquiv a1Facts, ?_⟩
  convert hpi using 1
  -- identify the derivative through the chart-4 flow at `0`
  ext v j
  have hPF := pf_thetaN D a1Facts.W4_smul (D.theta_PF4 0) v
  have hW : ∀ k : Fin 2, a1Facts.W4 k (D.thetaN 0) = μ ^ 2 • a1Facts.W4 k origin9 := fun k => by
    rw [h0, a1Facts.W4_smul]
  fin_cases j
  · have h := hPF 1
    rw [h4, hl0 1 (by decide), zero_mul, sub_zero, one_mul, hW, hW] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp [germDerEquiv, germDer, pr0, pr1, F']
    field_simp
    apply mul_left_cancel₀ hμ
    linear_combination -h
  · have h := hPF 8
    rw [h4, hl0 8 (by decide), zero_mul, sub_zero, one_mul, hW, hW] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp [germDerEquiv, germDer, pr0, pr1, F']
    field_simp
    apply mul_left_cancel₀ hμ
    linear_combination -h

/-! ### The instance -/

/-- **The A-block**, from a `θ`-datum over `a1Facts` and B5 data. -/
def aBlockOf (lci_s : ℕ) (lci_S : Fin lci_s → MvPolynomial (Fin 9) ℂ)
    (lci_F : Fin lci_s → List (MvPolynomial (Fin 9) ℂ)) (lci_len : ∀ i, (lci_F i).length + 2 + 1 = 9)
    (lci_F_le : ∀ i, Ideal.ofList (lci_F i) ≤ Ideal.span {Q | Q ∈ gensMv})
    (lci_mem : ∀ i, ∀ Q ∈ gensMv, lci_S i * Q ∈ Ideal.ofList (lci_F i))
    (lci_cover : ∀ v : Fin 9, ∃ e : ℕ,
      (X v : MvPolynomial (Fin 9) ℂ) ^ e ∈ Ideal.span {Q | Q ∈ gensMv} ⊔ Ideal.span (Set.range lci_S)) :
    LSG.MEB.AbBlock where
  g := 2
  N := 9
  gens := gensMv
  gens_hom := gensMv_hom
  θ := D.thetaN
  θ_analytic := D.analyticAt_thetaN
  θ_ne := D.thetaN_ne_zero
  θ_model z := (gensMv_eval_iff _).mpr ((onQ_iff_gens _).mp (D.thetaN_onQ z))
  per := kerE G
  per_discrete := LSG.W88.discreteTopology_kerE G
  per_span := per_span_kerE
  θ_per := theta_per D
  θ_ker := theta_ker D
  surj X hX h := ThetaData.surjA surjFacts D X hX ((onQ_iff_gens X).mpr ((gensMv_eval_iff X).mp h))
  nL := 9
  law m k := spMv (Data.law k m)
  law_hom m k := spMv_isWeightedHomogeneous _ (law_deg k m)
  law_eq m u v := by
    obtain ⟨κ, -, h⟩ := D.laws_eq
    refine ⟨κ * D.thetaN (u - v) m, ?_⟩
    rw [evalLaw_law]
    funext k
    rw [h, Pi.smul_apply, smul_eq_mul]
    ring
  law_complete u v := by
    obtain ⟨k, m, h⟩ := D.laws_complete u v
    refine ⟨m, fun h0 => h ?_⟩
    rw [evalLaw_law] at h0
    exact congrFun h0 k
  charts := {0, 4, 8}
  chart_cover X hX h := by
    have hQ := (onQ_iff_gens X).mpr ((gensMv_eval_iff X).mp h)
    rcases quadA_cover (a1Facts.onQ_quad X hQ) hX with h0 | h4 | h8
    · exact ⟨0, by simp, h0⟩
    · exact ⟨4, by simp, h4⟩
    · exact ⟨8, by simp, h8⟩
  W := Wmv
  W_hom := Wmv_hom
  W_chart := Wmv_chart
  θ_flow := theta_flow D
  i₀ := 4
  is := ![1, 8]
  θ_i₀ := by
    obtain ⟨μ, hμ, h0⟩ := thetaN_zero D
    rw [h0]; simpa [origin9] using hμ
  coords_locInv := coords_locInv D
  simple := simple_kerE G
  hilb_y := yA
  hilb_deg := 14
  hilb := hilbA
  lci_s := lci_s
  lci_S := lci_S
  lci_F := lci_F
  lci_len := lci_len
  lci_F_le := lci_F_le
  lci_mem := lci_mem
  lci_cover := lci_cover

section Checks

variable (s : ℕ) (S : Fin s → MvPolynomial (Fin 9) ℂ) (F : Fin s → List (MvPolynomial (Fin 9) ℂ))
  (h1 : ∀ i, (F i).length + 2 + 1 = 9) (h2 : ∀ i, Ideal.ofList (F i) ≤ Ideal.span {Q | Q ∈ gensMv})
  (h3 : ∀ i, ∀ Q ∈ gensMv, S i * Q ∈ Ideal.ofList (F i))
  (h4 : ∀ v : Fin 9, ∃ e : ℕ,
    (X v : MvPolynomial (Fin 9) ℂ) ^ e ∈ Ideal.span {Q | Q ∈ gensMv} ⊔ Ideal.span (Set.range S))

/-! The A5 constraints hold by `rfl`. -/
example : (aBlockOf D s S F h1 h2 h3 h4).g = 2 := rfl
example : (aBlockOf D s S F h1 h2 h3 h4).N = 9 := rfl
example : (aBlockOf D s S F h1 h2 h3 h4).θ = D.thetaN := rfl
example : (aBlockOf D s S F h1 h2 h3 h4).per = kerE G := rfl
example : (aBlockOf D s S F h1 h2 h3 h4).i₀ = (4 : Fin 9) := rfl

end Checks

/-- A base, a germ radius and a `θ`-datum over `a1Facts`, bundled. -/
structure ThetaPkg where
  B₁ : LocalBranch f₅ 2
  B₂ : LocalBranch f₅ 2
  p : ℂ × ℂ
  hp : p ∈ dom2 B₁ B₂
  hx : p.1 ≠ p.2
  G : GermRad a1Facts hp hx
  D : ThetaData G

theorem thetaPkg_nonempty : Nonempty ThetaPkg := by
  obtain ⟨B₁, B₂, p, hp, hx, G, -⟩ := exists_anchored_base surjFacts
  exact ⟨⟨B₁, B₂, p, hp, hx, G, Classical.choice (exists_thetaData G)⟩⟩

/-- A fixed choice of `θ`-datum (any choice works; `aBlockOf` takes an arbitrary one). -/
def stdPkg : ThetaPkg := Classical.choice thetaPkg_nonempty

end LSG.JacBlock
