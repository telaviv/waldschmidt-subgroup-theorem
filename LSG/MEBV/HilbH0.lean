/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.HilbH0Fam
import LSG.MEB.HilbH0

/-!
# The unsliced Hilbert lower bound for `H⁰` (M2.5 β′; template `LSG.MEB.HilbH0`)

**`h0LowerBoundV O : H0LowerBoundV O (cHV B)`** for every `O : ObstrDataGV`, with W88's projection exponents:
`(tD₀/t₀+1)^{t₀} (tD₁/t₁+1)^{t₁} (tD₂+1)^{t₂+m} ≤ cHV B · H(I(O.grp); t)`, `t₀ = ex0 T′`, `t₁ = d₁ − dim U`,
`t₂ = ex2 T′`.

Proof. `I(O.grp) = I(exp T′)`, `T′ = tanOfV Γ U t`. The target coordinates are: linear coordinates on
`pr_A(T′) = pr₁(Γ)`, torus coordinates independent modulo `U`, per block `ν_k = μ_k θ_{i₀}` and the chart ratios on
the base pivot set `J` of `t`, and the fibre ratios `T_{t₀}/X_{i₀}` on a coordinate pivot `ιF` of
`F = {f | (0, 0, 0, f) ∈ T′}`. **`eventually_liftV`**: every target point near `hBaseV` is attained by
`u = vecIncl γ + torIncl β + g2Incl π + vecIncl (0, f)` (the fibre ratio is affine in `w`, so the last step is exact).
**`ex2_le`**: `ex2 T′ ≤ dim t + dim F`.
-/

open MvPolynomial Module Filter Topology Set
open StrongSix.M2 (FLE hfun)

namespace LSG.MEBV

open LSG.MEB (Blk DfunB IsRatSub perAb pivG pivG_le)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The tangent space `tanOfV` -/

theorem mem_tanOfV_iff {gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))} {U : Submodule ℚ (Fin d₁ → ℚ)}
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {u : Tan d₀ d₁ B} :
    u ∈ tanOfV d₀ d₁ B gam U t ↔ ∃ γ ∈ gam, ∃ β ∈ LSG.W88.torusLie U, ∃ π ∈ perTanId B t,
      u = vecIncl γ + torIncl β + g2Incl π := by
  constructor
  · intro hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy₁
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy₂
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hz
    exact ⟨a, ha, b, hb, p, hp, rfl⟩
  · rintro ⟨γ, hγ, β, hβ, π, hπ, rfl⟩
    exact Submodule.add_mem_sup (Submodule.add_mem_sup (Submodule.mem_map_of_mem hγ)
      (Submodule.mem_map_of_mem hβ)) (Submodule.mem_map_of_mem hπ)

theorem perTanId_fst_mem {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {p : _} (hp : p ∈ perTanId B t) :
    p.1 ∈ t := by
  have : perTanId B t ≤ t.comap (LinearMap.fst ℂ _ _) := by
    rw [perTanId, Submodule.span_le]
    rintro q ⟨hq, -⟩
    exact hq
  exact this hp

theorem tanOfV_map_prA (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    (tanOfV d₀ d₁ B gam U t).map prA = gam.map (LinearMap.fst ℂ _ _) := by
  ext a
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨γ, hγ, β, -, π, -, rfl⟩ := mem_tanOfV_iff.mp hu
    exact ⟨γ, hγ, by simp [vecIncl, torIncl, g2Incl]⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨vecIncl γ, Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_map_of_mem hγ)),
      by simp [vecIncl]⟩

theorem base_mem_of_tanOfV {gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))} {U : Submodule ℚ (Fin d₁ → ℚ)}
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {u : Tan d₀ d₁ B} (hu : u ∈ tanOfV d₀ d₁ B gam U t) :
    u.2.2.1 ∈ t := by
  obtain ⟨γ, -, β, -, π, hπ, rfl⟩ := mem_tanOfV_iff.mp hu
  simpa [vecIncl, torIncl, g2Incl] using perTanId_fst_mem hπ

/-- The pure-fibre part `F = {f | (0, 0, 0, f) ∈ T′}`. -/
def fibSub (T : Submodule ℂ (Tan d₀ d₁ B)) : Submodule ℂ (Fin m → ℂ) :=
  T.comap ((vecIncl : _ →ₗ[ℂ] Tan d₀ d₁ B).comp (LinearMap.inr ℂ _ _))

theorem mem_fibSub {T : Submodule ℂ (Tan d₀ d₁ B)} {f : Fin m → ℂ} :
    f ∈ fibSub T ↔ ((0, 0, 0, f) : Tan d₀ d₁ B) ∈ T := Iff.rfl

/-- **`ex2 T′ ≤ dim t + dim F`.** -/
theorem ex2_le (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) {r : ℕ} {ιF : Fin r → Fin m}
    (hr : finrank ℂ (fibSub (tanOfV d₀ d₁ B gam U t)) = r)
    (hsurj : ∀ y : Fin r → ℂ, ∃ f ∈ fibSub (tanOfV d₀ d₁ B gam U t), ∀ l, f (ιF l) = y l) :
    ex2 (tanOfV d₀ d₁ B gam U t) ≤ finrank ℂ t + r := by
  classical
  set T := tanOfV d₀ d₁ B gam U t
  set F := fibSub T
  -- the restriction `F → ℂ^r` is injective
  let ρ : F →ₗ[ℂ] (Fin r → ℂ) := (LinearMap.pi fun l => LinearMap.proj (ιF l)).comp F.subtype
  have hρs : Function.Surjective ρ := fun y => by
    obtain ⟨f, hf, hfy⟩ := hsurj y
    exact ⟨⟨f, hf⟩, funext hfy⟩
  have hρi : Function.Injective ρ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hr, Module.finrank_fin_fun])).mpr hρs
  set K := T ⊓ (LinearMap.ker (prA : Tan d₀ d₁ B →ₗ[ℂ] _) ⊓ LinearMap.ker prB)
  let φ : K →ₗ[ℂ] ↥(t.prod (⊤ : Submodule ℂ (Fin r → ℂ))) :=
    LinearMap.codRestrict _ ((LinearMap.prod ((piB (d₀ := d₀) (d₁ := d₁)) ∘ₗ K.subtype)
      ((LinearMap.pi fun l => (LinearMap.proj (ιF l) : (Fin m → ℂ) →ₗ[ℂ] ℂ)) ∘ₗ
        ((LinearMap.snd ℂ _ _) ∘ₗ (LinearMap.snd ℂ _ _) ∘ₗ (LinearMap.snd ℂ _ _)) ∘ₗ K.subtype)))
      fun u => ⟨base_mem_of_tanOfV u.2.1, Submodule.mem_top⟩
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hz : (u : Tan d₀ d₁ B).2.2.1 = 0 := by
      have := congrArg (fun p : ↥(t.prod (⊤ : Submodule ℂ (Fin r → ℂ))) => p.1.1) hu
      exact this
    have hw : ∀ l, (u : Tan d₀ d₁ B).2.2.2 (ιF l) = 0 := fun l => by
      have := congrArg (fun p : ↥(t.prod (⊤ : Submodule ℂ (Fin r → ℂ))) => p.1.2 l) hu
      exact this
    have hu1 : (u : Tan d₀ d₁ B).1 = 0 := u.2.2.1
    have hu2 : (u : Tan d₀ d₁ B).2.1 = 0 := u.2.2.2
    have hfib : (u : Tan d₀ d₁ B).2.2.2 ∈ F := by
      have e : ((0, 0, 0, (u : Tan d₀ d₁ B).2.2.2) : Tan d₀ d₁ B) = (u : Tan d₀ d₁ B) := by
        ext <;> simp [hu1, hu2, hz]
      rw [mem_fibSub, e]
      exact u.2.1
    have h0 : ρ ⟨_, hfib⟩ = 0 := funext fun l => by simpa [ρ] using hw l
    have hw0 : (u : Tan d₀ d₁ B).2.2.2 = 0 := by
      have := hρi (h0.trans (map_zero ρ).symm)
      simpa using congrArg Subtype.val this
    exact Subtype.ext (Prod.ext hu1 (Prod.ext hu2 (Prod.ext hz hw0)))
  have h := LinearMap.finrank_le_finrank_of_injective hφ
  rw [LSG.MEB.finrank_submodule_prod, finrank_top, Module.finrank_fin_fun] at h
  exact h

/-! ### The target base point and the lift -/

variable (B) in
/-- The base point of the target coordinates. -/
noncomputable def hBaseV (t₀ : ℕ) (κ : Type) (J : Finset (Fin m)) (r : ℕ) : HCrdV B t₀ κ J r → ℂ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl ⟨_, none⟩)) => 0
  | .inr (.inr (.inl ⟨k, some j⟩)) => (B k).base.chartRatio 0 (Fin.castLE (pivG_le J k) j)
  | .inr (.inr (.inr _)) => 0

/-- **Every target point near `hBaseV` is attained by a lift of a point of `exp T′`.** -/
theorem eventually_liftV (O : ObstrDataGV d₀ d₁ B) {J : Finset (Fin m)}
    (hsurj : ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ O.t, ∀ k ∈ J, z k = y k)
    {κ : Type} [Fintype κ] (jj : κ → Fin d₁)
    (hind : LinearIndependent ℚ fun k => O.U.mkQ (Pi.single (jj k) 1))
    (L : Fin (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) → (Fin d₀ → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ l l', L l (Module.finBasis ℂ (O.gam.map (LinearMap.fst ℂ _ _)) l' : Fin d₀ → ℂ) =
      if l' = l then 1 else 0)
    {r : ℕ} {ιF : Fin r → Fin m} (hF : ∀ y : Fin r → ℂ, ∃ f ∈ fibSub O.tan, ∀ l, f (ιF l) = y l) :
    ∀ᶠ w in 𝓝 (hBaseV B (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) κ J r), ∃ u ∈ O.tan, ∃ μ : Fin m → ℂ,
      (∀ l, L l u.1 = w (.inl l)) ∧
      (∀ k, liftZ u μ (Var.y (jj k)) = w (.inr (.inl k))) ∧
      (∀ k, liftZ u μ (Var.eX k (B k).base.i₀) = w (.inr (.inr (.inl ⟨k, none⟩)))) ∧
      (∀ k j, liftZ u μ (Var.eX k ((B k).base.is (Fin.castLE (pivG_le J k) j))) =
        w (.inr (.inr (.inl ⟨k, none⟩))) * w (.inr (.inr (.inl ⟨k, some j⟩)))) ∧
      (∀ l, liftZ u μ (Var.eT (ιF l) (B (ιF l)).t₀) =
        w (.inr (.inr (.inl ⟨ιF l, none⟩))) * w (.inr (.inr (.inr l)))) := by
  classical
  obtain ⟨σ, hσt, hσJ⟩ := LSG.MEB.exists_pivot_section (B := fun k => (B k).base) hsurj
  have hV : ∀ᶠ y in 𝓝 (0 : ∀ k, Fin (B k).g → ℂ), ∀ k, (B k).base.θ (σ y k) (B k).base.i₀ ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    have hc : ContinuousAt (fun y : (∀ k, Fin (B k).g → ℂ) => (B k).base.θ (σ y k) (B k).base.i₀) 0 :=
      (((B k).base.continuous_θ_apply (B k).base.i₀).comp
        ((continuous_apply k).comp σ.continuous)).continuousAt
    have h0' : (B k).base.θ (σ 0 k) (B k).base.i₀ ≠ 0 := by simpa using (B k).base.θ_i₀
    exact hc.eventually_ne h0'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hV
  let Tk : ∀ k, k ∈ J → (HCrdV B (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) κ J r → ℂ) → (Fin (B k).g → ℂ) :=
    fun k hk w j' => w (.inr (.inr (.inl ⟨k, some ⟨j', by
      rw [LSG.MEB.pivG_of_mem hk]; exact j'.2⟩⟩)))
  have hT0 : ∀ k (hk : k ∈ J), Tk k hk (hBaseV B (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) κ J r) = (B k).base.chartRatio 0 :=
    fun k hk => funext fun j' => rfl
  have hTc : ∀ k (hk : k ∈ J), Continuous (Tk k hk) := fun k hk =>
    continuous_pi fun j' => continuous_apply _
  have hG : ∀ᶠ w in 𝓝 (hBaseV B (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) κ J r), (∀ k, w (.inr (.inl k)) ≠ 0) ∧
      ∀ k (hk : k ∈ J), Tk k hk w ∈ (B k).base.chartRatio '' Metric.ball 0 ε := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro k
      exact (continuous_apply _).continuousAt.eventually_ne (by simp [hBaseV])
    · rw [Filter.eventually_all]
      intro k
      by_cases hk : k ∈ J
      · have := (hTc k hk).continuousAt.preimage_mem_nhds (x := hBaseV B (finrank ℂ (O.gam.map (LinearMap.fst ℂ _ _))) κ J r)
          (by rw [hT0 k hk]; exact (B k).base.chartRatio_image_mem_nhds (Metric.ball_mem_nhds 0 hε))
        filter_upwards [this] with w hw
        exact fun _ => hw
      · exact Filter.Eventually.of_forall fun w hk' => absurd hk' hk
  filter_upwards [hG] with w ⟨hw1, hw2⟩
  choose yk hyk hyr using hw2
  let y : ∀ k, Fin (B k).g → ℂ := fun k => if hk : k ∈ J then yk k hk else 0
  have hyball : y ∈ Metric.ball 0 ε := by
    rw [ball_pi _ hε]
    intro k _
    by_cases hk : k ∈ J
    · simp only [y, dif_pos hk]; exact hyk k hk
    · simp only [y, dif_neg hk]; exact Metric.mem_ball_self hε
  have hne := hball y hyball
  -- the additive part
  let v0 := Module.finBasis ℂ (O.gam.map (LinearMap.fst ℂ _ _))
  let x : Fin d₀ → ℂ := ∑ l, w (.inl l) • (v0 l : Fin d₀ → ℂ)
  have hx : x ∈ O.gam.map (LinearMap.fst ℂ _ _) := Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (v0 l).2
  have hLx : ∀ l, L l x = w (.inl l) := by
    intro l
    simp only [x, map_sum, map_smul, v0, hL, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨γ, hγ, hγx⟩ := Submodule.mem_map.mp hx
  -- the torus part
  obtain ⟨v, hv, hvj⟩ := LSG.MEB.exists_mem_torusLie O.U jj hind fun k => Complex.log (w (.inr (.inl k)))
  -- the base part
  obtain ⟨wπ, hwπ⟩ := exists_perTanId O.t_rat (hσt y)
  set u₀ : Tan d₀ d₁ B := vecIncl γ + torIncl v + g2Incl (σ y, wπ)
  have hu₀ : u₀ ∈ O.tan := mem_tanOfV_iff.mpr ⟨γ, hγ, v, hv, _, hwπ, rfl⟩
  -- the fibre adjustment
  obtain ⟨f, hf, hfl⟩ := hF fun l => w (.inr (.inr (.inr l))) - u₀.2.2.2 (ιF l) +
    (B (ιF l)).Φ (σ y (ιF l)) (B (ιF l)).t₀ / (B (ιF l)).base.θ (σ y (ιF l)) (B (ιF l)).base.i₀
  set u := u₀ + ((0, 0, 0, f) : Tan d₀ d₁ B)
  have hu : u ∈ O.tan := O.tan.add_mem hu₀ (mem_fibSub.mp hf)
  have hu1 : u.1 = x := by simp [u, u₀, vecIncl, torIncl, g2Incl, ← hγx]
  have hu2 : u.2.1 = v := by simp [u, u₀, vecIncl, torIncl, g2Incl]
  have hu3 : u.2.2.1 = σ y := by simp [u, u₀, vecIncl, torIncl, g2Incl]
  have hu4 : ∀ k, u.2.2.2 k = u₀.2.2.2 k + f k := fun k => by simp [u]
  refine ⟨u, hu, fun k => w (.inr (.inr (.inl ⟨k, none⟩))) / (B k).base.θ (σ y k) (B k).base.i₀,
    fun l => by rw [hu1]; exact hLx l, fun k => ?_, fun k => ?_, fun k j => ?_, fun l => ?_⟩
  · simp only [liftZ, hu2]
    rw [hvj k, Complex.exp_log (hw1 k)]
  · simp only [liftZ, VBlock.lift_inl, Tan.blkV, hu3]
    rw [div_mul_cancel₀ _ (hne k)]
  · have hk : k ∈ J := by
      by_contra hk
      have := j.2
      have h0' : pivG (fun k => (B k).base) J k = 0 := if_neg hk
      omega
    have hzk : σ y k = yk k hk := by rw [hσJ y k hk]; simp [y, dif_pos hk]
    have hr := congrFun (hyr k hk) (Fin.castLE (pivG_le J k) j)
    change (B k).base.θ (yk k hk) ((B k).base.is (Fin.castLE (pivG_le J k) j)) /
      (B k).base.θ (yk k hk) (B k).base.i₀ = w (.inr (.inr (.inl ⟨k, some j⟩))) at hr
    simp only [liftZ, VBlock.lift_inl, Tan.blkV, hu3]
    have hne' := hne k
    rw [hzk] at hne' ⊢
    rw [← hr]
    field_simp
  · simp only [liftZ, VBlock.lift_inr, Tan.blkV, hu3, hu4, (B (ιF l)).fc_t₀, hfl l]
    have hne' := hne (ιF l)
    field_simp
    ring

/-! ### The lower bound -/

/-- **The unsliced Hilbert lower bound for `H⁰ = O.grp`.** -/
def H0LowerBoundV (O : ObstrDataGV d₀ d₁ B) (cH : ℕ) : Prop :=
  ∀ D₀ D₁ D₂ t : ℕ,
    (t * D₀ / ex0 O.tan + 1) ^ ex0 O.tan *
        (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
        (t * D₂ + 1) ^ (ex2 O.tan + m) ≤
      cH * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t

theorem eval_monomial_funV {S : Type*} [Fintype S] (e : S → ℕ) (w : S → ℂ) :
    eval w (monomial (Finsupp.equivFunOnFinite.symm e) (1 : ℂ)) = ∏ s, w s ^ e s :=
  LSG.MEB.eval_monomial_fun e w

/-- **The unsliced Hilbert lower bound for `H⁰`**, constant `cHV B`. -/
theorem h0LowerBoundV (O : ObstrDataGV d₀ d₁ B) : H0LowerBoundV O (cHV B) := by
  classical
  intro D₀ D₁ D₂ t
  obtain ⟨J, hinj, hsurj⟩ := LSG.MEB.pivot (B := fun k => (B k).base) O.t_rat
  obtain ⟨κ, _, jj, -, hκ, hind⟩ := StrongSix.M2.exists_indep_quot O.U
  obtain ⟨ιF, hιF, hF⟩ := LSG.ME.exists_coord_surj (fibSub O.tan)
  set h0 := O.gam.map (LinearMap.fst ℂ _ _)
  set t₀ := finrank ℂ h0 with ht₀
  have hex0 : ex0 O.tan = t₀ := by rw [ex0, ObstrDataGV.tan, tanOfV_map_prA]
  let v0 := Module.finBasis ℂ h0
  have hL : ∀ l : Fin t₀, ∃ L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ, L.comp h0.subtype = v0.coord l :=
    fun l => LinearMap.exists_extend _
  choose L hLv using hL
  have hLk : ∀ l l', L l (v0 l' : Fin d₀ → ℂ) = if l' = l then 1 else 0 := by
    intro l l'
    have := congrArg (fun f => f (v0 l')) (hLv l)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  set M0 := t * D₀ / t₀ + 1
  set M1 := t * D₁ / (d₁ - finrank ℚ O.U) + 1
  set T := t * D₂
  let P : HIdxV B t₀ M0 κ M1 J ιF T → MvPolynomial (Var d₀ d₁ B) ℂ :=
    hPolyV (fun l => linPolyV (L l)) jj
  have hM0 : t₀ * (M0 - 1) ≤ t * D₀ := by simp only [M0, Nat.add_sub_cancel]; exact Nat.mul_div_le _ _
  have hM1 : Fintype.card κ * (M1 - 1) ≤ t * D₁ := by
    simp only [M1, Nat.add_sub_cancel, hκ]; exact Nat.mul_div_le _ _
  have hind' : ∀ c : HIdxV B t₀ M0 κ M1 J ιF T → ℂ, ∑ i, c i • P i ∈ vanish O.grp → ∀ i, c i = 0 := by
    intro c hc
    rw [O.grp_eq, vanish_zcl, mem_vanish_expG_iff] at hc
    let Q : MvPolynomial (HCrdV B t₀ κ J (finrank ℂ (fibSub O.tan))) ℂ :=
      ∑ i, c i • monomial (Finsupp.equivFunOnFinite.symm (hExpV i)) 1
    have hQ : Q = 0 := by
      refine LSG.MEB.eq_zero_of_eventually_eval Q (hBaseV B t₀ κ J _) ?_
      filter_upwards [eventually_liftV O hsurj jj hind L hLk hF] with w ⟨u, hu, μ, h1, h2, h3, h4, h5⟩
      have := hc u hu μ
      rw [map_sum] at this
      rw [← this]
      simp only [Q, map_sum, smul_eval, eval_monomial_funV]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact (eval_hPolyV _ jj (liftZ u μ) w (fun l => by rw [eval_linPolyV]; exact h1 l) h2 h3 h4 h5 i).symm
    intro i
    have := congrArg (fun p : MvPolynomial (HCrdV B t₀ κ J (finrank ℂ (fibSub O.tan))) ℂ =>
      p.coeff (Finsupp.equivFunOnFinite.symm (hExpV i))) hQ
    simp only [Q, coeff_sum, coeff_smul, coeff_monomial, MvPolynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by
        rw [if_neg]; · simp
        intro h
        exact hi' (hExpV_injective (Finsupp.equivFunOnFinite.symm.injective h)))
      (by simp)] at this
    simpa using this
  have hcard := card_le_hfun_vanishV (DfunB D₀ D₁ D₂) t O.grp P
    (fun i => hPolyV_mem_FLE _ (fun l => linPolyV_mem_FLE _) jj hM0 hM1 rfl i) hind'
  rw [card_HIdxV, hκ] at hcard
  have hs : ex2 O.tan ≤ ∑ k, pvV B J ιF k := by
    have h1 : ex2 O.tan ≤ finrank ℂ O.t + finrank ℂ (fibSub O.tan) :=
      ex2_le (B := B) O.gam O.U O.t (ιF := ιF) rfl hF
    have h2 : finrank ℂ O.t ≤ ∑ k, pivG (fun k => (B k).base) J k :=
      LSG.MEB.finrank_le_pivot (B := fun k => (B k).base) hinj
    have h3 := sum_fibG ιF
    simp only [pvV, Finset.sum_add_distrib, h3]
    omega
  have hcount := count_leV (B := B) (J := J) (T := T) hιF hs
  rw [hex0]
  calc M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * (T + 1) ^ (ex2 O.tan + m)
      ≤ M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * (cHV B * ∏ k, pivMV B J ιF T k ^ (pvV B J ιF k + 1)) :=
        Nat.mul_le_mul_left _ hcount
    _ = cHV B * (M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * ∏ k, pivMV B J ιF T k ^ (pvV B J ιF k + 1)) := by
        ring
    _ ≤ cHV B * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t := Nat.mul_le_mul_left _ hcard

end LSG.MEBV
