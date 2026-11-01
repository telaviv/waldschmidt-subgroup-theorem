/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21LatT
import LSG.W88.Prop61V2

/-!
# W83 Prop. 2.1 for the class `𝒞` on `V` with `dim (V ∩ fibre) ≤ 1` (`STAGE6_MXP.md` §2.1)

If `V ∩ fibre = ℂu` is a line, `π` (forget `s`) has kernel `ℂu` on `V`. Coordinates on `V`:
`v = ℓ_x(x) + t u`, `x` = `n − 1` non-fibre coordinate forms of `π(V)` (`exists_coordsVT`). Then
* `MonoV.eval (p + t u)` is a polynomial of degree `≤ D` in `t` (`eval_add_fibre_poly`: the fibre
  forms are affine in `s`);
* a period `ω ∈ V` is `ℓ_x(x_ω) + τ_ω u`, `x_ω` in the product of lattices (`per_coord`), and the
  multiplier `expMult(πω, πp)` does not see `t`;
so `prop21LatT` applies. **`prop21_GVT_one`** (the line case) and **`prop21GVT_of_le_one`**
(`dim (V ∩ fibre) ≤ 1`, with `prop21_GV_deg` when `V ∩ fibre = 0`) give `Prop21DegV`.
-/

open Complex Finset Module Polynomial LSG.W88 LSG.W88.Vec
open LSG.Aux (Coord tcoord exists_coordsV latA latB latD per_coord perVec Idx exists_minor_ne_zero
  perVec_sum prop21LatT)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m q : ℕ}

/-! ### Monomials along a fibre direction -/

lemma fibF_add_smul (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ) (i : Fin q)
    (z : Fin m → ℂ) (s su : Fin q → ℂ) (t : ℂ) :
    fibF Ls M i z (s + t • su) =
      (su i * ∏ l, LSG.Aux.ellW (Ls l) 0 (z l)) * t + fibF Ls M i z s := by
  unfold fibF
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`MonoV.eval` is a polynomial of degree `≤ D` along a fibre direction.** -/
theorem eval_add_fibre_poly (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ) {D : ℕ}
    (μ : MonoV d0 d1 m q D) (p : TanV d0 d1 m q) {u : TanV d0 d1 m q} (hu : u ∈ fibreV) :
    ∃ Q : ℂ[X], Q.natDegree ≤ D ∧ ∀ t : ℂ, μ.eval Ls M (p + t • u) = Q.eval t := by
  classical
  obtain ⟨su, rfl⟩ := hu
  set A : ℂ := (∏ i, p.1 i ^ μ.α i) * (∏ i, Complex.exp (p.2.1 i) ^ μ.β i) *
    ∏ j, ∏ t, LSG.Aux.ellW (Ls j) t (p.2.2.1 j) ^ μ.γ j t with hA
  set cc : Fin q → ℂ := fun i => su i * ∏ l, LSG.Aux.ellW (Ls l) 0 (p.2.2.1 l) with hcc
  set bb : Fin q → ℂ := fun i => fibF Ls M i p.2.2.1 p.2.2.2 with hbb
  refine ⟨C A * ∏ i, (C (cc i) * X + C (bb i)) ^ μ.φ i, ?_, fun t => ?_⟩
  · refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    calc ∑ i, ((C (cc i) * X + C (bb i)) ^ μ.φ i).natDegree ≤ ∑ i, μ.φ i * 1 := by
          refine sum_le_sum fun i _ => (natDegree_pow_le).trans ?_
          exact Nat.mul_le_mul_left _ (natDegree_linear_le)
      _ ≤ D := by simpa using μ.hφ
  · have hu' : (LinearMap.comp vecIncl (LinearMap.inr ℂ (Fin d0 → ℂ) (Fin q → ℂ))) su =
        ((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), (0 : Fin m → ℂ), su) := rfl
    rw [hu']
    simp only [MonoV.eval, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero,
      add_zero, eval_mul, eval_C, eval_prod, eval_pow, eval_add, eval_X]
    rw [hA]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [fibF_add_smul]

/-! ### Coordinates on `V` when `V ∩ fibre` is a line -/

lemma piT_eq_zero_of_mem_fibreV {v : TanV d0 d1 m q} (hv : v ∈ fibreV) : piT v = 0 := by
  obtain ⟨s, rfl⟩ := hv
  rfl

lemma eq_zero_of_per_fibre (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ)
    {w : TanV d0 d1 m q} (hw : w ∈ PerV Ls M) (hwF : w ∈ fibreV) : w = 0 := by
  obtain ⟨s, rfl⟩ := hwF
  have h4 := hw.2.2.2
  change s = M.mulVec (etaV Ls 0) at h4
  have he : etaV Ls (0 : Fin m → ℂ) = 0 := funext fun j => LSG.Weierstrass.eta_zero (Ls j)
  rw [he, Matrix.mulVec_zero] at h4
  rw [h4]; rfl

/-- **Coordinates `v = ℓ_x(x) + t u` on `V`** when `V ∩ fibre = ℂu`. -/
theorem exists_coordsVT (V : Submodule ℂ (TanV d0 d1 m q)) (hV1 : finrank ℂ ↥(V ⊓ fibreV) = 1)
    {n' : ℕ} (hn : finrank ℂ V = n' + 1) :
    ∃ (u : TanV d0 d1 m q) (J : Fin n' → Coord d0 d1 m) (ℓx : (Fin n' → ℂ) →L[ℂ] TanV d0 d1 m q)
      (cx : V →L[ℂ] (Fin n' → ℂ)) (ct : V →L[ℂ] ℂ),
      u ∈ fibreV ∧ (∀ x, ℓx x ∈ V) ∧ (∀ v : V, (v : TanV d0 d1 m q) = ℓx (cx v) + ct v • u) ∧
      (∀ v : V, ∀ k, cx v k = tcoord (J k) (piT (v : TanV d0 d1 m q))) := by
  classical
  -- the line `V ∩ fibre = ℂu`
  have hne : V ⊓ fibreV ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hV1; exact zero_ne_one hV1
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hline : ∀ w ∈ V ⊓ fibreV, ∃ c : ℂ, w = c • u := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u, hu⟩ : ↥(V ⊓ fibreV))
      (fun h => hu0 (congrArg Subtype.val h))).mp hV1 ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  -- a coordinate form not vanishing at `u`
  obtain ⟨su, hsu⟩ := hu.2
  have hsu0 : su ≠ 0 := by
    rintro rfl; apply hu0; rw [← hsu, map_zero]
  obtain ⟨i₀, hi₀⟩ : ∃ i, su i ≠ 0 := by
    by_contra h; push Not at h; exact hsu0 (funext h)
  let f₀ : TanV d0 d1 m q →ₗ[ℂ] ℂ :=
    (LinearMap.proj i₀).comp ((LinearMap.snd ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp
      (LinearMap.snd ℂ _ _)))
  have hf₀u : f₀ u = su i₀ := by rw [← hsu]; rfl
  -- the projection on `V`
  let f : V →ₗ[ℂ] Tan d0 d1 m := piTL.comp V.subtype
  have hker : ∀ v : V, f v = 0 → (v : TanV d0 d1 m q) ∈ V ⊓ fibreV := fun v hv =>
    ⟨v.2, mem_fibreV_of_piT_eq_zero hv⟩
  have hkerf : finrank ℂ (LinearMap.ker f) = 1 := by
    have e : LinearMap.ker f = (V ⊓ fibreV).comap V.subtype := by
      ext v; constructor
      · intro hv; exact hker v hv
      · intro hv; exact piT_eq_zero_of_mem_fibreV hv.2
    rw [e, (Submodule.comapSubtypeEquivOfLe (inf_le_left : V ⊓ fibreV ≤ V)).finrank_eq, hV1]
  have hrank : finrank ℂ (LinearMap.range f) = n' := by
    have := LinearMap.finrank_range_add_finrank_ker f
    omega
  obtain ⟨J, ψ', hψ'⟩ := exists_coordsV (LinearMap.range f) hrank
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  have hfg : ∀ p : LinearMap.range f, f (g p) = p := fun p => by
    have := congrArg Subtype.val (LinearMap.congr_fun hg p)
    simpa using this
  let ℓxL : (Fin n' → ℂ) →ₗ[ℂ] TanV d0 d1 m q := V.subtype ∘ₗ g ∘ₗ ψ'.symm.toLinearMap
  let cxL : V →ₗ[ℂ] (Fin n' → ℂ) := ψ'.toLinearMap ∘ₗ f.rangeRestrict
  have hdec0 : ∀ v : V, (v : TanV d0 d1 m q) - ℓxL (cxL v) ∈ V ⊓ fibreV := by
    intro v
    have hgv : g (ψ'.symm (ψ' (f.rangeRestrict v))) = g (f.rangeRestrict v) := by
      rw [LinearEquiv.symm_apply_apply]
    refine ⟨V.sub_mem v.2 (g _).2, mem_fibreV_of_piT_eq_zero ?_⟩
    change piTL ((v : TanV d0 d1 m q) - (g (ψ'.symm (ψ' (f.rangeRestrict v))) : TanV d0 d1 m q)) = 0
    rw [hgv, map_sub]
    have h1 : piTL ((g (f.rangeRestrict v)) : TanV d0 d1 m q) = f (g (f.rangeRestrict v)) := rfl
    rw [h1, hfg]
    simp [f]
  let ctL : V →ₗ[ℂ] ℂ := (su i₀)⁻¹ • (f₀ ∘ₗ (V.subtype - ℓxL ∘ₗ cxL))
  refine ⟨u, J, LinearMap.toContinuousLinearMap ℓxL, LinearMap.toContinuousLinearMap cxL,
    LinearMap.toContinuousLinearMap ctL, hu.2, fun x => (g _).2, fun v => ?_, fun v k => ?_⟩
  · obtain ⟨c, hc⟩ := hline _ (hdec0 v)
    have hct : ctL v = c := by
      change (su i₀)⁻¹ * f₀ ((v : TanV d0 d1 m q) - ℓxL (cxL v)) = c
      rw [hc, map_smul, hf₀u, smul_eq_mul]
      field_simp
    change (v : TanV d0 d1 m q) = ℓxL (cxL v) + ctL v • u
    rw [hct, ← hc]; abel
  · change ψ' (f.rangeRestrict v) k = _
    rw [hψ']
    rfl

/-! ### Prop. 2.1 when `V ∩ fibre` is a line -/

set_option maxHeartbeats 1000000 in -- many norm estimates
/-- **W83 Prop. 2.1 on `V` with `dim (V ∩ fibre) = 1`.** -/
theorem prop21_GVT_one (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ)
    (V : Submodule ℂ (TanV d0 d1 m q)) (hV1 : finrank ℂ ↥(V ⊓ fibreV) = 1) {κ : ℕ}
    (ω : Fin κ → TanV d0 d1 m q) (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ PerV Ls M)
    (hω : LinearIndependent ℤ ω) : Prop21DegV Ls M V (finrank ℂ V) ω := by
  classical
  obtain ⟨n', hn'⟩ : ∃ n', finrank ℂ V = n' + 1 :=
    ⟨finrank ℂ V - 1, by have := Submodule.finrank_mono (inf_le_left : V ⊓ fibreV ≤ V); omega⟩
  obtain ⟨u, J, ℓx, cx, ct, huF, hℓV, hdec, hcx⟩ := exists_coordsVT V hV1 hn'
  set α : Fin n' → ℂ := fun k => latA Ls (J k)
  set β : Fin n' → ℂ := fun k => latB Ls (J k)
  have hD : ∀ k, ((starRingEnd ℂ) (α k) * β k).im ≠ 0 := fun k => latD Ls (J k)
  choose pc hpc using fun i c => per_coord Ls (piT_mem_per Ls M (hωP i)) c
  set P : Fin κ → Idx n' → ℤ := fun i c => if c.2 = 0 then (pc i (J c.1)).1 else (pc i (J c.1)).2
  set ωt : Fin κ → (Fin n' → ℂ) := fun i => cx ⟨ω i, hωV i⟩
  set τ : Fin κ → ℂ := fun i => ct ⟨ω i, hωV i⟩
  have hωt : ∀ i, perVec α β (P i) = ωt i := by
    intro i; funext k
    simp only [perVec, P, ωt, hcx, α, β]
    simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
    exact (hpc i (J k)).symm
  have hωdec : ∀ i, ω i = ℓx (ωt i) + τ i • u := fun i => hdec ⟨ω i, hωV i⟩
  have hPind : LinearIndependent ℤ P := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∑ i, (g i : ℂ) • ωt i = 0 := by
      have := congrArg (perVec α β) hg
      rw [perVec_sum] at this
      simp only [hωt] at this
      rw [this]; funext k; simp [perVec]
    have hw : ∑ i, g i • ω i = (∑ i, (g i : ℂ) * τ i) • u := by
      have e1 : ∑ i, g i • ω i = ∑ i, (g i : ℂ) • ω i :=
        sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
      rw [e1]
      simp only [hωdec, smul_add, sum_add_distrib, ← map_smul, ← map_sum, hsum, map_zero,
        zero_add, smul_smul, ← sum_smul]
    have hwP : ∑ i, g i • ω i ∈ PerV Ls M :=
      AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hωP i) _
    have hwF : ∑ i, g i • ω i ∈ fibreV := by rw [hw]; exact Submodule.smul_mem _ _ huF
    exact (Fintype.linearIndependent_iff.mp hω) g (eq_zero_of_per_fibre Ls M hwP hwF)
  obtain ⟨I, hI, hdet⟩ := exists_minor_ne_zero P hPind
  choose Ce hCe0 hCe using fun j => LSG.Aux.exists_eta_bound (Ls j)
  set Cq := ∑ j, Ce j with hCq
  have hCq0 : 0 ≤ Cq := sum_nonneg fun j _ => hCe0 j
  set α' : ℝ := max (‖ℓx‖ + ‖u‖) 1 with hα'
  set β' : ℝ := max (max ‖cx‖ ‖ct‖) 1 with hβ'
  have hα1 : 1 ≤ α' := le_max_right _ _
  have hβ1 : 1 ≤ β' := le_max_right _ _
  set a : ℝ := 3 * Cq * ‖ℓx‖ ^ 2 * β' ^ 2 + β' ^ 2 with ha
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21LatT n' κ a (by positivity) α β hD P I hI hdet τ
  obtain ⟨cW, K, hcW0, hK1, hcW⟩ := exists_sum_monoV_le_exp (d0 := d0) (d1 := d1) Ls M
  set γ : ℝ := α' * β' with hγ
  have hγ1 : 1 ≤ γ := one_le_mul_of_one_le_of_one_le hα1 hβ1
  set c₀ : ℝ := max c₁ (Real.exp 1) with hc₀
  have hc₀1 : 1 ≤ c₀ := le_trans (Real.one_le_exp (by norm_num)) (le_max_right _ _)
  refine ⟨c₀ * γ ^ 2, c₂ * 2 ^ (n' + 1), cW, K, by positivity, by positivity, hcW0, hK1, ?_⟩
  intro L D D₀ D₁ Δ U R ρ μs hα hβ hL hΔ hΔU hRr hr hU hDU hG hc
  rw [hn'] at hc
  have hρ1 : 1 ≤ ρ := le_trans (one_le_mul_of_one_le_of_one_le hc₀1 (one_le_pow₀ hγ1)) hr
  have hρ0 : 0 < ρ := by linarith
  have hRρ0 : 0 < R / ρ := lt_of_lt_of_le (by positivity) hRr
  have hR0 : 0 ≤ R := ((div_pos_iff_of_pos_right hρ0).mp hRρ0).le
  have hγR : γ ^ 2 ≤ R / ρ := le_trans (le_mul_of_one_le_left (by positivity) hc₀1) hRr
  have hexp1 : Real.exp 1 ≤ R / ρ :=
    le_trans (le_trans (le_max_right _ _) (le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ hγ1))) hRr
  have hlog1 : 1 ≤ Real.log (R / ρ) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hexp1
  -- the new parameters
  set r' : ℝ := β' * ρ with hr'
  set R' : ℝ := R / α' with hR'
  have hratio : R' / r' = (R / ρ) / γ := by simp only [R', r', hγ]; field_simp
  have hlog : Real.log (R / ρ) / 2 ≤ Real.log (R' / r') := by
    rw [hratio, Real.log_div hRρ0.ne' (by positivity)]
    have h1 : Real.log γ ≤ Real.log (R / ρ) / 2 := by
      have := Real.log_le_log (by positivity) hγR
      rw [Real.log_pow] at this; push_cast at this; linarith
    linarith
  have hlog' : Real.log (R' / r') ≤ Real.log (R / ρ) := by
    rw [hratio]
    exact Real.log_le_log (by positivity) (div_le_self hRρ0.le hγ1)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  -- `(D + 1) log(R/ρ) ≤ 2U`
  have hDlog : ((D : ℝ) + 1) * Real.log (R / ρ) ≤ 2 * U := by
    have hL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
    have hK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
    have h1R : Real.log (R / ρ) ≤ Real.log (1 + R) := by
      refine Real.log_le_log hRρ0 ?_
      calc R / ρ ≤ R := div_le_self hR0 hρ1
        _ ≤ 1 + R := by linarith
    have hDR : (D : ℝ) * Real.log (1 + R) ≤ U := by
      have h0 : 0 ≤ (D₀ : ℝ) * Real.log (1 + R) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
      have h2 : 0 ≤ (D : ℝ) * Real.log K := mul_nonneg hD0 hK0
      have h3 : 0 ≤ (D₁ : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR0
      have h4 : 0 ≤ (m : ℝ) * D * cW * (1 + R) ^ 2 := by positivity
      nlinarith
    have hlU : Real.log (R / ρ) ≤ U := by
      have h1 : 1 ≤ c₀ * γ ^ 2 * ρ ^ 2 :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc₀1 (one_le_pow₀ hγ1))
          (one_le_pow₀ hρ1)
      have h2 : 0 ≤ Real.log (R / ρ) := by linarith
      nlinarith
    nlinarith
  obtain ⟨p, hp0, hpΔ, hpz⟩ := h L D (3 * D * Cq * ‖ℓx‖ ^ 2) Δ U R' r'
    (fun l x t => (μs l).eval Ls M (ℓx x + t • u)) hL hΔ hΔU
    (by rw [hratio, le_div_iff₀ (by positivity)]
        calc c₁ * γ ≤ c₀ * γ ^ 2 := by
              gcongr
              · exact le_max_left _ _
              · exact le_self_pow₀ hγ1 two_ne_zero
          _ ≤ R / ρ := hRr)
    (by calc c₁ ≤ c₀ := le_max_left _ _
          _ ≤ c₀ * γ ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hγ1)
          _ ≤ ρ := hr
          _ ≤ r' := le_mul_of_one_le_left hρ0.le hβ1)
    (by have hl0 : 0 ≤ Real.log (R / ρ) := by linarith
        calc r' ^ 2 * Real.log (R' / r') ≤ r' ^ 2 * Real.log (R / ρ) := by gcongr
          _ = β' ^ 2 * (ρ ^ 2 * Real.log (R / ρ)) := by ring
          _ ≤ (c₀ * γ ^ 2) * (ρ ^ 2 * Real.log (R / ρ)) := by
              gcongr
              calc β' ^ 2 ≤ γ ^ 2 := by
                    simp only [hγ]; rw [mul_pow]
                    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hα1)
                _ ≤ c₀ * γ ^ 2 := le_mul_of_one_le_left (by positivity) hc₀1
          _ = c₀ * γ ^ 2 * ρ ^ 2 * Real.log (R / ρ) := by ring
          _ ≤ U := hU)
    (by positivity)
    (by calc 3 * D * Cq * ‖ℓx‖ ^ 2 * r' ^ 2 = 3 * Cq * ‖ℓx‖ ^ 2 * β' ^ 2 * (D * ρ ^ 2) := by ring
          _ ≤ 3 * Cq * ‖ℓx‖ ^ 2 * β' ^ 2 * U := by gcongr
          _ ≤ a * U := by
              have hU0 : 0 ≤ U := le_trans (by positivity) hDU
              have : 0 ≤ β' ^ 2 * U := by positivity
              rw [ha]; linarith)
    (by calc (D : ℝ) * r' ^ 2 = β' ^ 2 * (D * ρ ^ 2) := by ring
          _ ≤ β' ^ 2 * U := by gcongr
          _ ≤ a * U := by
              have hU0 : 0 ≤ U := le_trans (by positivity) hDU
              have : 0 ≤ 3 * Cq * ‖ℓx‖ ^ 2 * β' ^ 2 * U := by positivity
              rw [ha]; linarith)
    (fun l t => (differentiable_evalV Ls M (μs l)).comp (ℓx.differentiable.add_const _))
    (fun l x => eval_add_fibre_poly Ls M (μs l) (ℓx x) huF)
    (fun x t hx ht => hcW L D D₀ D₁ μs R U hα hβ hR0 hL hG _ (by
      calc ‖ℓx x + t • u‖ ≤ ‖ℓx x‖ + ‖t • u‖ := norm_add_le _ _
        _ ≤ ‖ℓx‖ * ‖x‖ + ‖t‖ * ‖u‖ := by
            rw [norm_smul]; exact add_le_add (ℓx.le_opNorm x) le_rfl
        _ ≤ ‖ℓx‖ * R' + R' * ‖u‖ := by gcongr
        _ = (‖ℓx‖ + ‖u‖) * R' := by ring
        _ ≤ α' * R' := by
            have : 0 ≤ R' := by positivity
            gcongr; exact le_max_left _ _
        _ = R := by simp only [R']; field_simp))
    (by
      intro k x t
      set w : TanV d0 d1 m q := ∑ i, k i • ω i with hw
      have hwP : w ∈ PerV Ls M :=
        AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hωP i) _
      set p0 : TanV d0 d1 m q := ℓx x + t • u with hp0
      have hpt : ℓx (x + ∑ i, (k i : ℂ) • perVec α β (P i)) + (t + ∑ i, (k i : ℂ) * τ i) • u =
          p0 + w := by
        have e : ∀ i, k i • ω i = (k i : ℂ) • ℓx (ωt i) + ((k i : ℂ) * τ i) • u := by
          intro i; rw [hωdec i, ← Int.cast_smul_eq_zsmul ℂ, smul_add, smul_smul]
        rw [hp0, hw]
        simp only [hωt, e, map_add, map_sum, map_smul, add_smul, Finset.sum_smul,
          Finset.sum_add_distrib]
        abel
      refine ⟨LSG.Aux.expMult Ls D (piT w) (piT p0), ?_, fun l => ?_⟩
      · refine (LSG.Aux.norm_expMult_le Ls hCe0 hCe (piT_mem_per Ls M hwP) _).trans
          (Real.exp_le_exp.mpr ?_)
        have hπp : ‖piT p0‖ ≤ ‖ℓx‖ * ‖x‖ := by
          rw [hp0, map_add, map_smul, piT_eq_zero_of_mem_fibreV huF, smul_zero, add_zero]
          exact (norm_piT_le _).trans (ℓx.le_opNorm x)
        have hπw : ‖piT w‖ ≤ ‖ℓx‖ * ‖∑ i, (k i : ℂ) • perVec α β (P i)‖ := by
          have : w = ℓx (∑ i, (k i : ℂ) • perVec α β (P i)) +
              (∑ i, (k i : ℂ) * τ i) • u := by
            have h1 : w = (p0 + w) - p0 := by abel
            rw [h1, ← hpt, hp0, map_add, add_smul]; abel
          rw [this, map_add, map_smul, piT_eq_zero_of_mem_fibreV huF, smul_zero, add_zero]
          exact (norm_piT_le _).trans (ℓx.le_opNorm _)
        have h0 : 0 ≤ ‖piT p0‖ + ‖piT w‖ := by positivity
        calc 3 * D * Cq * (‖piT p0‖ + ‖piT w‖) ^ 2
            ≤ 3 * D * Cq * (‖ℓx‖ * (‖x‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖)) ^ 2 := by
              gcongr; rw [mul_add]; exact add_le_add hπp hπw
          _ = 3 * D * Cq * ‖ℓx‖ ^ 2 * (‖x‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2 := by
              ring
      · change (μs l).eval Ls M (ℓx (x + ∑ i, (k i : ℂ) • perVec α β (P i)) +
          (t + ∑ i, (k i : ℂ) * τ i) • u) = _ * (μs l).eval Ls M (ℓx x + t • u)
        rw [hpt]
        exact (μs l).eval_add_per Ls M hwP p0)
    (by
      have hrr : ρ ^ κ ≤ r' ^ κ := pow_le_pow_left₀ hρ0.le (le_mul_of_one_le_left hρ0.le hβ1) κ
      have hll : (Real.log (R / ρ) / 2) ^ n' ≤ Real.log (R' / r') ^ n' :=
        pow_le_pow_left₀ (by linarith) hlog n'
      have hlpos : 0 < Real.log (R / ρ) := by linarith
      have hU0 : 0 ≤ U := by linarith
      have key : c₂ * ((D : ℝ) + 1) * U ^ (n' + 1) * Real.log (R / ρ) ≤
          L * Δ * r' ^ κ * Real.log (R' / r') ^ n' * Real.log (R / ρ) := by
        calc c₂ * ((D : ℝ) + 1) * U ^ (n' + 1) * Real.log (R / ρ)
            = c₂ * U ^ (n' + 1) * (((D : ℝ) + 1) * Real.log (R / ρ)) := by ring
          _ ≤ c₂ * U ^ (n' + 1) * (2 * U) := by gcongr
          _ = c₂ * 2 ^ (n' + 1) * U ^ (n' + 1 + 1) / 2 ^ n' := by
              field_simp; ring
          _ ≤ L * Δ * ρ ^ κ * Real.log (R / ρ) ^ (n' + 1) / 2 ^ n' := by gcongr
          _ = L * Δ * ρ ^ κ * (Real.log (R / ρ) / 2) ^ n' * Real.log (R / ρ) := by
              rw [div_pow, pow_succ]; field_simp
          _ ≤ L * Δ * r' ^ κ * Real.log (R' / r') ^ n' * Real.log (R / ρ) := by gcongr
      exact le_of_mul_le_mul_right key hlpos)
  refine ⟨p, hp0, hpΔ, fun z hzV hz => ?_⟩
  set v : V := ⟨z, hzV⟩
  have hvz : ‖v‖ = ‖z‖ := rfl
  have hx : ‖cx v‖ ≤ r' := by
    calc ‖cx v‖ ≤ ‖cx‖ * ‖v‖ := cx.le_opNorm v
      _ ≤ β' * ρ := by
          rw [hvz]; gcongr
          exact le_trans (le_max_left _ _) (le_max_left _ _)
  have ht : ‖ct v‖ ≤ r' := by
    calc ‖ct v‖ ≤ ‖ct‖ * ‖v‖ := ct.le_opNorm v
      _ ≤ β' * ρ := by
          rw [hvz]; gcongr
          exact le_trans (le_max_right _ _) (le_max_left _ _)
  have := hpz (cx v) (ct v) hx ht
  rwa [← hdec v] at this

/-- **W83 Prop. 2.1 on `V` with `dim (V ∩ fibre) ≤ 1`.** -/
theorem prop21GVT_of_le_one (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ)
    (V : Submodule ℂ (TanV d0 d1 m q)) (hV : finrank ℂ ↥(V ⊓ fibreV) ≤ 1) {κ : ℕ}
    (ω : Fin κ → TanV d0 d1 m q) (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ PerV Ls M)
    (hω : LinearIndependent ℤ ω) : Prop21DegV Ls M V (finrank ℂ V) ω := by
  rcases Nat.lt_or_ge (finrank ℂ ↥(V ⊓ fibreV)) 1 with h0 | h1
  · exact prop21DegV_of_inf Ls M V (Submodule.finrank_eq_zero.mp (by omega)) ω hωV hωP hω
  · exact prop21_GVT_one Ls M V (by omega) ω hωV hωP hω

end LSG.AuxV
