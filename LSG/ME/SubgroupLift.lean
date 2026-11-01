import Mathlib
import LSG.ME.SubgroupLie
import LSG.ME.Deriv
import LSG.Weierstrass.Basic

/-!
# `V`-normalised lifts of `expE` and the chain rule (STAGE2 §5, item 4, analytic part)

* `chartVf a b P`: the `V`-chart derivation of `LSG.ME.Deriv` on a cone vector `P`
  (`eval_chartPoly_one`).
* **`exists_VLift`**: near every `z₀` with `z₀ ∈ Λ` or `℘'(z₀) ≠ 0` (i.e. `V ≠ 0` at `expE z₀`) there is
  an analytic lift `F` of `expE` to the cone with `V`-coordinate `1`, and `F' = chartVf (F)`:
  off the lattice `F = (℘/℘', 1, 1/℘')` (using `℘'' = 6℘² − g₂/2` and `℘'² = 4℘³ − g₂℘ − g₃`), near a
  lattice point `F = G / G_V` with `G = (z − l)³ · (℘, ℘', 1)` (the derivative at `l` by continuity).
* **`hasDerivAt_eval`**: the chain rule for evaluating a polynomial along a differentiable curve.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set

namespace LSG.ME

/-- The `V`-chart derivation on a cone vector `P = (U, V, W)`. -/
noncomputable def chartVf (a b : ℂ) (P : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![-(1 / 2 * P 1 ^ 2) - a * P 0 * P 2 - 3 * (1 / 2) * b * P 2 ^ 2, 0,
    -(6 * P 0 ^ 2) + 1 / 2 * a * P 2 ^ 2]

theorem eval_chartPoly_one {d₀ d₁ m : ℕ} (g₂ g₃ : Fin m → ℂ) (k : Fin m) (c : Fin 3)
    (x : Var d₀ d₁ m → ℂ) :
    eval x (chartPoly g₂ g₃ d₀ d₁ 1 k c) = chartVf (g₂ k) (g₃ k) (fun i => x (.e k i)) c := by
  fin_cases c <;> simp [chartPoly, chartV, chartVf]

/-- The affine `V`-normalised lift `(℘/℘', 1, 1/℘')`. -/
noncomputable def Faff (L : PeriodPair) (z : ℂ) : Fin 3 → ℂ :=
  ![L.weierstrassP z / L.derivWeierstrassP z, 1, 1 / L.derivWeierstrassP z]

theorem hasDerivAt_Faff (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice)
    (hp : L.derivWeierstrassP z ≠ 0) (i : Fin 3) :
    HasDerivAt (fun z => Faff L z i) (chartVf L.g₂ L.g₃ (Faff L z) i) z := by
  have h1 := hasDerivAt_weierstrassP L hz
  have h2 := hasDerivAt_derivWeierstrassP L hz
  have hsq := L.derivWeierstrassP_sq z hz
  fin_cases i
  · show HasDerivAt (fun z => L.weierstrassP z / L.derivWeierstrassP z) _ z
    refine (h1.div h2 hp).congr_deriv ?_
    simp [chartVf, Faff]
    field_simp
    linear_combination (3 : ℂ) * hsq
  · simpa [Faff, chartVf] using hasDerivAt_const z (1 : ℂ)
  · show HasDerivAt (fun z => 1 / L.derivWeierstrassP z) _ z
    refine ((hasDerivAt_const z (1 : ℂ)).div h2 hp).congr_deriv ?_
    simp [chartVf, Faff]
    field_simp
    ring

/-- The cone lift near a lattice point `z₀`: `(z − z₀)³ · (℘, ℘', 1)`, extended analytically. -/
noncomputable def Glat (L : PeriodPair) (z₀ z : ℂ) : Fin 3 → ℂ :=
  ![(z - z₀) + (z - z₀) ^ 3 * (L.weierstrassPExcept z₀ z - 1 / z₀ ^ 2),
    (z - z₀) ^ 3 * L.derivWeierstrassPExcept z₀ z - 2, (z - z₀) ^ 3]

theorem analyticOnNhd_Glat (L : PeriodPair) (z₀ : ℂ) (i : Fin 3) :
    AnalyticOnNhd ℂ (fun z => Glat L z₀ z i) (L.lattice \ {z₀})ᶜ := by
  have h1 := L.analyticOnNhd_weierstrassPExcept z₀
  have h2 := L.analyticOnNhd_derivWeierstrassPExcept z₀
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z - z₀) (L.lattice \ {z₀})ᶜ :=
    fun z _ => analyticAt_id.sub analyticAt_const
  fin_cases i
  · exact hid.add ((hid.pow 3).mul (h1.sub fun _ _ => analyticAt_const))
  · exact ((hid.pow 3).mul h2).sub fun _ _ => analyticAt_const
  · exact hid.pow 3

theorem Glat_eq (L : PeriodPair) {z₀ z : ℂ} (h₀ : z₀ ∈ L.lattice) (hzL : z ∉ L.lattice) :
    Glat L z₀ z = (z - z₀) ^ 3 • ![L.weierstrassP z, L.derivWeierstrassP z, 1] := by
  have hw : z - z₀ ≠ 0 := sub_ne_zero.mpr fun h => hzL (h ▸ h₀)
  have e1 := L.weierstrassPExcept_def ⟨z₀, h₀⟩ z
  have e2 := L.derivWeierstrassPExcept_def ⟨z₀, h₀⟩ z
  simp only at e1 e2
  funext i
  fin_cases i
  · simp only [Glat, e1]; simp; field_simp; ring
  · simp only [Glat, e2]; simp; field_simp; ring
  · simp [Glat]

theorem rep_expE_of_notMem (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z) =
      ![L.weierstrassP z, L.derivWeierstrassP z, 1] := by
  rw [expE_of_notMem L hz]
  funext i
  fin_cases i <;> simp [rep, mul_div_cancel₀]

/-- **`V`-normalised analytic lifts** near points where `V ≠ 0`. -/
theorem exists_VLift (L : PeriodPair) (z₀ : ℂ) (h : z₀ ∈ L.lattice ∨ L.derivWeierstrassP z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ F : ℂ → Fin 3 → ℂ,
      (∀ i, AnalyticOnNhd ℂ (fun z => F z i) U) ∧ ∀ z ∈ U, F z 1 = 1 ∧
        (∃ c : ℂ, c ≠ 0 ∧ F z = c • rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z)) ∧
        ∀ i, HasDerivAt (fun z => F z i) (chartVf L.g₂ L.g₃ (F z) i) z := by
  have hp'cont : ContinuousOn L.derivWeierstrassP (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP.continuousOn
  have hpcont : ContinuousOn L.weierstrassP (L.lattice : Set ℂ)ᶜ :=
    (L.differentiableOn_weierstrassP).continuousOn
  -- the affine part: on `Λᶜ ∩ {℘' ≠ 0}`
  set Ω := (L.lattice : Set ℂ)ᶜ ∩ L.derivWeierstrassP ⁻¹' {0}ᶜ with hΩ
  have hΩo : IsOpen Ω := hp'cont.isOpen_inter_preimage L.isClosed_lattice.isOpen_compl
    isOpen_compl_singleton
  have hFaffan : ∀ i, AnalyticOnNhd ℂ (fun z => Faff L z i) Ω := by
    intro i z hz
    have hp : AnalyticAt ℂ L.derivWeierstrassP z := L.analyticOnNhd_derivWeierstrassP z hz.1
    have hP : AnalyticAt ℂ L.weierstrassP z :=
      L.differentiableOn_weierstrassP.analyticOnNhd L.isClosed_lattice.isOpen_compl z hz.1
    fin_cases i
    · exact hP.div hp hz.2
    · exact analyticAt_const
    · exact analyticAt_const.div hp hz.2
  have hFaffrep : ∀ z ∈ Ω, Faff L z = (1 / L.derivWeierstrassP z) •
      rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z) := by
    intro z hz
    rw [rep_expE_of_notMem L hz.1]
    funext i
    have hp : L.derivWeierstrassP z ≠ 0 := hz.2
    fin_cases i <;> simp [Faff, hp, div_eq_inv_mul]
  rcases em (z₀ ∈ L.lattice) with h₀ | h₀
  · -- near a lattice point: `F = G / G_V`
    have hGc : ContinuousOn (fun z => Glat L z₀ z 1) (L.lattice \ {z₀})ᶜ :=
      (analyticOnNhd_Glat L z₀ 1).continuousOn
    set U := ((L.lattice : Set ℂ) \ {z₀})ᶜ ∩ (fun z => Glat L z₀ z 1) ⁻¹' {0}ᶜ
    have hUo : IsOpen U := hGc.isOpen_inter_preimage L.isOpen_compl_lattice_sdiff
      isOpen_compl_singleton
    have hz₀U : z₀ ∈ U := ⟨by simp, by simp [Glat]⟩
    let F : ℂ → Fin 3 → ℂ := fun z i => Glat L z₀ z i / Glat L z₀ z 1
    have hFan : ∀ i, AnalyticOnNhd ℂ (fun z => F z i) U := fun i z hz =>
      (analyticOnNhd_Glat L z₀ i z hz.1).div (analyticOnNhd_Glat L z₀ 1 z hz.1) hz.2
    -- off `z₀`, `F = Faff`
    have hFΩ : ∀ z ∈ U, z ≠ z₀ → z ∈ Ω ∧ F z = Faff L z := by
      intro z hz hzz
      have hzL : z ∉ L.lattice := fun h => hz.1 ⟨h, hzz⟩
      have hw : (z - z₀) ^ 3 ≠ 0 := pow_ne_zero 3 (sub_ne_zero.mpr hzz)
      have hG := Glat_eq L h₀ hzL
      have hG1 : Glat L z₀ z 1 = (z - z₀) ^ 3 * L.derivWeierstrassP z := by
        rw [hG]; simp
      have hp : L.derivWeierstrassP z ≠ 0 := by
        intro h0; exact hz.2 (by simp [hG1, h0])
      refine ⟨⟨hzL, hp⟩, funext fun i => ?_⟩
      simp only [F, hG1]
      rw [hG]
      have hw' : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
      fin_cases i <;> simp [Faff, hw', hp] <;> field_simp
    have hderiv_ne : ∀ z ∈ U, z ≠ z₀ → ∀ i,
        HasDerivAt (fun z => F z i) (chartVf L.g₂ L.g₃ (F z) i) z := by
      intro z hz hzz i
      obtain ⟨hzΩ, hFz⟩ := hFΩ z hz hzz
      rw [hFz]
      refine (hasDerivAt_Faff L hzΩ.1 hzΩ.2 i).congr_of_eventuallyEq ?_
      filter_upwards [(hUo.inter isOpen_compl_singleton).mem_nhds ⟨hz, hzz⟩] with y hy
      rw [(hFΩ y hy.1 hy.2).2]
    refine ⟨U, hUo, hz₀U, F, hFan, fun z hz => ⟨?_, ?_, ?_⟩⟩
    · exact div_self hz.2
    · by_cases hzz : z = z₀
      · subst hzz
        refine ⟨1, one_ne_zero, ?_⟩
        rw [expE_of_mem L h₀, one_smul]
        funext i
        fin_cases i <;> simp [F, Glat, rep, O]
      · obtain ⟨hzΩ, hFz⟩ := hFΩ z hz hzz
        exact ⟨_, one_div_ne_zero hzΩ.2, hFz.trans (hFaffrep z hzΩ)⟩
    · intro i
      by_cases hzz : z = z₀
      · subst hzz
        -- by continuity of both sides at `z₀`
        have han := hFan i z hz
        have hcd : ContinuousAt (deriv fun z => F z i) z := han.deriv.continuousAt
        have hcv : ContinuousAt (fun y => chartVf L.g₂ L.g₃ (F y) i) z := by
          have hc : ∀ j, ContinuousAt (fun y => F y j) z := fun j => (hFan j z hz).continuousAt
          fin_cases i <;> simp only [chartVf] <;> simp <;> fun_prop
        have heq : (deriv fun z => F z i) =ᶠ[𝓝[≠] z] fun y => chartVf L.g₂ L.g₃ (F y) i := by
          filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hz), self_mem_nhdsWithin] with y hy hyz
          exact (hderiv_ne y hy hyz i).deriv
        have hval : deriv (fun z => F z i) z = chartVf L.g₂ L.g₃ (F z) i :=
          tendsto_nhds_unique (hcd.tendsto.mono_left nhdsWithin_le_nhds)
            ((hcv.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
        rw [← hval]
        exact han.differentiableAt.hasDerivAt
      · exact hderiv_ne z hz hzz i
  · -- off the lattice
    have hp : L.derivWeierstrassP z₀ ≠ 0 := h.resolve_left h₀
    refine ⟨Ω, hΩo, ⟨h₀, hp⟩, Faff L, hFaffan, fun z hz => ⟨by simp [Faff], ?_, ?_⟩⟩
    · exact ⟨_, one_div_ne_zero hz.2, hFaffrep z hz⟩
    · exact fun i => hasDerivAt_Faff L hz.1 hz.2 i

/-! ### The chain rule -/

/-- **Chain rule** for polynomial evaluation along a curve. -/
theorem hasDerivAt_eval {σ : Type*} [Fintype σ] [DecidableEq σ] {Y : ℂ → σ → ℂ} {Y' : σ → ℂ}
    {c₀ : ℂ} (h : ∀ v, HasDerivAt (fun c => Y c v) (Y' v) c₀) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun c => eval (Y c) P) (∑ v, eval (Y c₀) (pderiv v P) * Y' v) c₀ := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const c₀ a
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, eval_X]
    have e : ∀ u, pderiv u (p * X v) = pderiv u p * X v + p * (Pi.single u (1 : MvPolynomial σ ℂ) : σ → MvPolynomial σ ℂ) v := by
      intro u; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]; ring
    have hs : (∑ u, eval (Y c₀) (pderiv u (p * X v)) * Y' u) =
        (∑ u, eval (Y c₀) (pderiv u p) * Y' u) * Y c₀ v + eval (Y c₀) p * Y' v := by
      simp_rw [e, map_add, map_mul, eval_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun u _ => by ring
      · rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb.symm])
          (by simp)]
        simp
    rw [hs]
    exact hp.mul (h v)

end LSG.ME
