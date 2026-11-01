/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.CosetGe
import LSG.MEB.Rational

/-!
# Tools for the unsliced Hilbert lower bound of `H⁰` (α′; STAGE_A4 §7.3 (6), step 2)

Generic lemmas used by `HilbH0Fam.lean` and `HilbH0.lean`:
* `C_mem_FLE0`, `X_mem_FLE`, `pow_mem_FLE`, `prod_mem_FLE`: block degrees of products;
* **`card_le_hfun_vanish`**: a family in `FLE(tD)` independent modulo `I(E)` has at most `H(I(E); t)` members;
* **`eq_zero_of_eventually_eval`**: a polynomial vanishing near a point of `ℂ^S` is `0` (`funext_set` on a box);
* **`AbBlock.chartRatio`**, **`AbBlock.chartRatio_image_mem_nhds`**: the ratios `θ_{is j}/θ_{i₀}` are a local
  diffeomorphism at `0` (`coords_locInv` + the inverse function theorem), so they map neighbourhoods of `0` onto
  neighbourhoods;
* **`exists_mem_torusLie`**: prescribed values on coordinates independent modulo `U` are attained in `U^⊥`;
* **`exists_pivot_section`**, **`finrank_le_pivot`**: a continuous linear section `ℂ^{g} → t` of the pivot
  projection, and `dim t ≤ Σ_{k ∈ J} g_k`.
-/

open MvPolynomial Module Filter Topology Set
open StrongSix.M2 (FLE hfun)

namespace LSG.MEB

/-! ### Block degrees of products -/

section FLEaux

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq ι] (β : σ → ι)

theorem C_mem_FLE0 (a : ℂ) : (C a : MvPolynomial σ ℂ) ∈ FLE ℂ β 0 := by
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff, C_apply]
  intro m hm
  have hm0 : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst hm0
  intro i
  simp

theorem X_mem_FLE (v : σ) : (X v : MvPolynomial σ ℂ) ∈ FLE ℂ β (Pi.single (β v) 1) := by
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff, X]
  intro m hm
  have hm0 : m = Finsupp.single v 1 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst hm0
  intro i
  rw [StrongSix.M2.bdeg_single]
  by_cases h : β v = i
  · subst h; simp
  · simp [h, Pi.single_apply, Ne.symm h]

theorem pow_mem_FLE {P : MvPolynomial σ ℂ} {D : ι → ℕ} (hP : P ∈ FLE ℂ β D) (n : ℕ) :
    P ^ n ∈ FLE ℂ β (n • D) := by
  induction n with
  | zero => simpa using C_mem_FLE0 β 1
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact StrongSix.M2.mul_mem_FLE ℂ ih hP

theorem prod_mem_FLE {α : Type*} (s : Finset α) (f : α → MvPolynomial σ ℂ) (D : α → ι → ℕ)
    (h : ∀ a ∈ s, f a ∈ FLE ℂ β (D a)) : ∏ a ∈ s, f a ∈ FLE ℂ β (∑ a ∈ s, D a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C_mem_FLE0 β 1
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    exact StrongSix.M2.mul_mem_FLE ℂ (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

end FLEaux

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Counting independent elements -/

/-- **A family of `FLE(tD)` independent modulo `I(E)` has at most `H(I(E); t)` members.** -/
theorem card_le_hfun_vanish {ι : Type*} [Fintype ι] (D : Blk m → ℕ) (t : ℕ) (E : Set (GPt d₀ d₁ B))
    (P : ι → MvPolynomial (Var d₀ d₁ B) ℂ) (hP : ∀ i, P i ∈ FLE ℂ blk (t • D))
    (hind : ∀ c : ι → ℂ, ∑ i, c i • P i ∈ vanish E → ∀ i, c i = 0) :
    Fintype.card ι ≤ hfun blk D ℂ (vanish E) t := by
  classical
  have e : vanish E = StrongSix.M2.vanish' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2)
      (E ×ˢ Set.univ) := rfl
  rw [e, StrongSix.M2.hfun_vanish_eq' blk D (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2)
    (E ×ˢ Set.univ) t]
  set R := (FLE ℂ blk (t • D)).map
    (StrongSix.M2.restrE' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2) (E ×ˢ Set.univ))
  let f : ι → R := fun i => ⟨_, ⟨P i, hP i, rfl⟩⟩
  have hf : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply hind c
    rw [e, StrongSix.M2.mem_vanish']
    rintro ⟨g, lam⟩ ⟨hg, -⟩
    have := congrArg (fun x : R => (x : GPt d₀ d₁ B × (Fin m → ℂˣ) → ℂ) (g, lam)) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply, f, StrongSix.M2.restrE'_apply] at this
    rw [map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (Set.mk_mem_prod hg (Set.mem_univ _)), smul_eval, smul_eq_mul, mul_comm]
  exact hf.fintype_card_le_finrank

/-! ### Polynomials vanishing near a point -/

/-- **A polynomial vanishing on a neighbourhood of a point of `ℂ^S` is `0`.** -/
theorem eq_zero_of_eventually_eval {S : Type*} [Fintype S] (Q : MvPolynomial S ℂ) (x₀ : S → ℂ)
    (h : ∀ᶠ w in 𝓝 x₀, eval w Q = 0) : Q = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine MvPolynomial.funext_set (fun s => Metric.ball (x₀ s) r)
    (fun s => infinite_of_mem_nhds (x₀ s) (Metric.ball_mem_nhds _ hr)) fun w hw => ?_
  rw [map_zero]
  apply hball
  rw [ball_pi _ hr]
  exact hw

/-! ### The chart ratios of a block -/

namespace AbBlock

variable (b : AbBlock)

/-- The ratios `θ_{is j} / θ_{i₀}`. -/
noncomputable def chartRatio (z : Fin b.g → ℂ) : Fin b.g → ℂ := fun j => b.θ z (b.is j) / b.θ z b.i₀

theorem continuous_θ_apply (c : Fin b.N) : Continuous fun z => b.θ z c :=
  continuous_iff_continuousAt.mpr fun z => (b.analyticAt_θ_apply z c).continuousAt

/-- **The chart ratios map neighbourhoods of `0` onto neighbourhoods** (`coords_locInv` and the inverse
function theorem). -/
theorem chartRatio_image_mem_nhds {V : Set (Fin b.g → ℂ)} (hV : V ∈ 𝓝 0) :
    b.chartRatio '' V ∈ 𝓝 (b.chartRatio 0) := by
  obtain ⟨f', hf'⟩ := b.coords_locInv
  have hf'' : HasFDerivAt b.chartRatio (f' : (Fin b.g → ℂ) →L[ℂ] (Fin b.g → ℂ)) 0 := hf'
  have han : AnalyticAt ℂ b.chartRatio 0 := by
    rw [analyticAt_pi_iff]
    intro j
    exact (b.analyticAt_θ_apply 0 (b.is j)).div (b.analyticAt_θ_apply 0 b.i₀) b.θ_i₀
  have hs : HasStrictFDerivAt b.chartRatio (f' : (Fin b.g → ℂ) →L[ℂ] (Fin b.g → ℂ)) 0 := by
    have := han.hasStrictFDerivAt
    rwa [hf''.fderiv] at this
  rw [← hs.map_nhds_eq_of_equiv]
  exact image_mem_map hV

end AbBlock

/-! ### The torus part -/

/-- **Prescribed values on coordinates independent modulo `U` are attained in `U^⊥`.** -/
theorem exists_mem_torusLie (U : Submodule ℚ (Fin d₁ → ℚ)) {κ : Type*} [Fintype κ] (jj : κ → Fin d₁)
    (hind : LinearIndependent ℚ fun k => U.mkQ (Pi.single (jj k) 1)) (w : κ → ℂ) :
    ∃ v ∈ LSG.W88.torusLie U, ∀ k, v (jj k) = w k := by
  classical
  set e : κ → (Fin d₁ → ℚ) ⧸ U := fun k => U.mkQ (Pi.single (jj k) 1) with he
  let bs := Basis.span hind
  have hext : ∀ k, ∃ g : ((Fin d₁ → ℚ) ⧸ U) →ₗ[ℚ] ℚ,
      g.comp (Submodule.span ℚ (Set.range e)).subtype = bs.coord k :=
    fun k => LinearMap.exists_extend _
  choose g hg using hext
  have hge : ∀ k k', g k (e k') = if k' = k then 1 else 0 := by
    intro k k'
    have := congrArg (fun f => f ⟨e k', Submodule.subset_span ⟨k', rfl⟩⟩) (hg k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have hb : bs k' = ⟨e k', Submodule.subset_span ⟨k', rfl⟩⟩ := Basis.span_apply hind k'
    rw [← hb, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  let f : κ → (Fin d₁ → ℚ) →ₗ[ℚ] ℚ := fun k => (g k).comp U.mkQ
  have hfe : ∀ k k', f k (Pi.single (jj k') 1) = if k' = k then 1 else 0 := fun k k' => hge k k'
  have hsum : ∀ k (φ : Fin d₁ → ℚ), ∑ j, (φ j : ℂ) * (f k (Pi.single j 1) : ℂ) = (f k φ : ℂ) := by
    intro k φ
    have hφ : φ = ∑ j, φ j • (Pi.single j (1 : ℚ) : Fin d₁ → ℚ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hφ]
    simp only [map_sum, map_smul, smul_eq_mul]
    push_cast
    rfl
  refine ⟨fun j => ∑ k, w k * (f k (Pi.single j 1) : ℂ), fun φ hφ => ?_, fun k' => ?_⟩
  · have hfφ : ∀ k, f k φ = 0 := fun k => by
      simp only [f, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero U).mpr hφ, map_zero]
    calc ∑ j, (φ j : ℂ) * ∑ k, w k * (f k (Pi.single j 1) : ℂ)
        = ∑ k, w k * ∑ j, (φ j : ℂ) * (f k (Pi.single j 1) : ℂ) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [hsum, hfφ]
  · show ∑ k, w k * (f k (Pi.single (jj k') 1) : ℂ) = w k'
    simp only [hfe]
    rw [Finset.sum_eq_single k' (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp) (by simp)]
    simp

/-! ### The pivot section -/

/-- **A continuous linear section of the pivot projection**: for `J` as in `pivot`, a continuous linear map
`σ : ∏ ℂ^{g_k} → ∏ ℂ^{g_k}` with values in `t` that keeps the coordinates in `J`. -/
theorem exists_pivot_section {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {J : Finset (Fin m)}
    (hsurj : ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ t, ∀ k ∈ J, z k = y k) :
    ∃ σ : (∀ k, Fin (B k).g → ℂ) →L[ℂ] (∀ k, Fin (B k).g → ℂ),
      (∀ y, σ y ∈ t) ∧ ∀ y, ∀ k ∈ J, σ y k = y k := by
  classical
  let ρ : t →ₗ[ℂ] (∀ k : J, Fin (B k).g → ℂ) :=
    LinearMap.pi fun k : J => (LinearMap.proj (R := ℂ) (φ := fun k => Fin (B k).g → ℂ) (k : Fin m)).comp
      t.subtype
  have hρ : LinearMap.range ρ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y'
    obtain ⟨z, hz, hzJ⟩ := hsurj fun k => if h : k ∈ J then y' ⟨k, h⟩ else 0
    refine ⟨⟨z, hz⟩, funext fun k => ?_⟩
    simp only [ρ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply]
    rw [hzJ k k.2, dif_pos k.2]
  obtain ⟨s, hs⟩ := ρ.exists_rightInverse_of_surjective hρ
  let res : (∀ k, Fin (B k).g → ℂ) →ₗ[ℂ] (∀ k : J, Fin (B k).g → ℂ) :=
    LinearMap.pi fun k : J => LinearMap.proj (R := ℂ) (φ := fun k => Fin (B k).g → ℂ) (k : Fin m)
  let σl := t.subtype ∘ₗ s ∘ₗ res
  refine ⟨LinearMap.toContinuousLinearMap σl, fun y => (s (res y)).2, fun y k hk => ?_⟩
  have := congrFun (congrArg (fun f => f (res y)) hs) ⟨k, hk⟩
  simpa [ρ, res, σl] using this

/-- **`dim t ≤ Σ_{k ∈ J} g_k`** when the projection of `t` to the coordinates in `J` is injective. -/
theorem finrank_le_pivot {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {J : Finset (Fin m)}
    (hinj : ∀ z ∈ t, (∀ k ∈ J, z k = 0) → z = 0) :
    finrank ℂ t ≤ ∑ k, if k ∈ J then (B k).g else 0 := by
  classical
  let ρ : t →ₗ[ℂ] (∀ k : J, Fin (B k).g → ℂ) :=
    LinearMap.pi fun k : J => (LinearMap.proj (R := ℂ) (φ := fun k => Fin (B k).g → ℂ) (k : Fin m)).comp
      t.subtype
  have hρ : Function.Injective ρ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 := hinj z z.2 fun k hk => by
      have := congrFun hz ⟨k, hk⟩
      simpa [ρ] using this
    exact Subtype.ext h0
  have h1 := LinearMap.finrank_le_finrank_of_injective hρ
  rw [Module.finrank_pi_fintype] at h1
  simp only [Module.finrank_fin_fun] at h1
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_coe_sort J]
  exact h1

end LSG.MEB
