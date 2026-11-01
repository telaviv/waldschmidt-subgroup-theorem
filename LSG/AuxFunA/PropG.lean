/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.Package
import LSG.AuxFun.Prop21Lin
import LSG.W88.K5dModel

/-!
# A5.4: W83 Prop. 2.1 for the monomials on `V ⊂ T_G`, under toric injectivity (`STAGE_A5.md` D3)

`G = G_a^{d₀} × G_m^{d₁} × ∏ B_k` with analytic packages `An`. For a subspace `V` of dimension `n` and
`ℂ`-independent periods `ω_1, …, ω_κ ∈ V ∩ PerL` there are integers `p_l`, not all zero, `|p_l| ≤ e^Δ`, with
`|Σ p_l M_l| ≤ e^{−U}` on `V ∩ B(0, r)` (`prop21A`, `prop21A_deg`). This is Tier 1′ (`LSG.Aux.prop21Lin`): no
lattice-adapted coordinates.

`ℂ`-independence comes from **toric injectivity** (`TorInjB V`: an element of `V ∩ span_ℚ Per` with zero toric part
is `0`): `ℤ`-independent periods in `V` have `ℚ`-independent toric parts in `2πiℤ^{d₁}`, and `ℚ`-independent rational
vectors are `ℂ`-independent (`linIndep_of_torInj`; REVIEW_TORINJ §3b).
-/

open Complex Finset Module LSG.W88

noncomputable section

namespace LSG.AuxA

open LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- **Toric injectivity** of `V ⊂ T_G` (MEB form of `LSG.W88.TorInjA`). -/
def TorInjB (V : Submodule ℂ (Tan d₀ d₁ B)) : Prop :=
  ∀ v ∈ V, v ∈ Submodule.span ℚ (Per d₀ d₁ B : Set (Tan d₀ d₁ B)) → v.2.1 = 0 → v = 0

/-- **Toric injectivity makes `ℤ`-independent periods `ℂ`-independent.** -/
theorem linIndep_of_torInj {V : Submodule ℂ (Tan d₀ d₁ B)} (hV : TorInjB V) {κ : ℕ}
    (ω : Fin κ → Tan d₀ d₁ B) (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ Per d₀ d₁ B)
    (hω : LinearIndependent ℤ ω) : LinearIndependent ℂ ω := by
  classical
  choose n hn using fun i j => (hωP i).2.1 j
  set c : Fin κ → Fin d₁ → ℚ := fun i j => (n i j : ℚ)
  have hωQ : LinearIndependent ℚ ω := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hω
  have hc : LinearIndependent ℚ c := by
    rw [Fintype.linearIndependent_iff]
    intro q hq
    set v : Tan d₀ d₁ B := ∑ i, q i • ω i
    have hvV : v ∈ V := V.sum_mem fun i _ => by
      rw [← Rat.cast_smul_eq_qsmul ℂ]; exact V.smul_mem _ (hωV i)
    have hvP : v ∈ Submodule.span ℚ (Per d₀ d₁ B : Set (Tan d₀ d₁ B)) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hωP i))
    have hv1 : v.2.1 = 0 := by
      funext j
      have hj := congrFun hq j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, c] at hj
      change (∑ i, q i • ω i).2.1 j = 0
      have e : (∑ i, q i • ω i).2.1 j = ∑ i, q i • (ω i).2.1 j := by
        rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]; rfl
      rw [e]
      simp only [hn, ← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]
      have : ∑ i, (q i : ℂ) * (2 * Real.pi * I * (n i j : ℂ)) =
          2 * Real.pi * I * ((∑ i, q i * (n i j : ℚ) : ℚ) : ℂ) := by
        push_cast; rw [Finset.mul_sum]; refine sum_congr rfl fun i _ => by ring
      rw [this, hj]; simp
    have hv0 := hV v hvV hvP hv1
    exact Fintype.linearIndependent_iff.mp hωQ q hv0
  have hcC := LSG.W88.K5d.linIndep_cast (F := ℂ) c hc
  rw [Fintype.linearIndependent_iff]
  intro a ha
  refine Fintype.linearIndependent_iff.mp hcC a ?_
  funext j
  have h1 : (∑ i, a i • ω i).2.1 j = 0 := by rw [ha]; rfl
  have e : (∑ i, a i • ω i).2.1 j = ∑ i, a i * (ω i).2.1 j := by
    rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]; rfl
  rw [e] at h1
  simp only [hn] at h1
  have h2 : (2 * Real.pi * I : ℂ) * ∑ i, a i * ((c i j : ℚ) : ℂ) = 0 := by
    rw [← h1, Finset.mul_sum]; refine sum_congr rfl fun i _ => by simp only [c]; push_cast; ring
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have := (mul_eq_zero.mp h2).resolve_left h2pi
  simpa [Finset.sum_apply, smul_eq_mul] using this

/-- **W83 Prop. 2.1 (Tier 1′) for the monomials on `V`.** -/
theorem prop21A (An : ∀ k, AbBlockAn (B k)) (V : Submodule ℂ (Tan d₀ d₁ B)) {n : ℕ}
    (hn : finrank ℂ V = n) {κ : ℕ} (ω : Fin κ → Tan d₀ d₁ B) (hωV : ∀ i, ω i ∈ V)
    (hωP : ∀ i, ω i ∈ PerL d₀ d₁ B (latF An)) (hω : LinearIndependent ℂ ω) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L D : ℕ) (Δ U R r : ℝ) (μs : Fin L → MonoA d₀ d₁ B D),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → c₁ * r ^ 2 * Real.log (R / r) ≤ U →
      (D : ℝ) * r ^ 2 ≤ U →
      (∀ p ∈ V, ‖p‖ ≤ R → ∑ l, ‖(μs l).eval p‖ ≤ Real.exp U) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z ∈ V, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * (μs l).eval z‖ ≤ Real.exp (-U) := by
  classical
  -- coordinates on `V`
  let ψ : V ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasisOfFinrankEq ℂ V hn).equivFun
  set ωt : Fin κ → (Fin n → ℂ) := fun i => ψ ⟨ω i, hωV i⟩
  have hωV' : LinearIndependent ℂ (fun i => (⟨ω i, hωV i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hω
  have hωt : LinearIndependent ℂ ωt := hωV'.map' ψ.toLinearMap ψ.ker
  have hκ : κ ≤ n := by
    have := hωt.fintype_card_le_finrank
    simpa using this
  let ℓ : (Fin n → ℂ) →L[ℂ] Tan d₀ d₁ B :=
    LinearMap.toContinuousLinearMap (V.subtype ∘ₗ ψ.symm.toLinearMap)
  let ψL : V →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap ψ.toLinearMap
  have hℓV : ∀ z, ℓ z ∈ V := fun z => (ψ.symm z).2
  have hℓψ : ∀ v : V, ℓ (ψL v) = v := fun v => by simp [ℓ, ψL]
  have hℓω : ∀ i, ℓ (ωt i) = ω i := fun i => hℓψ ⟨ω i, hωV i⟩
  set α' : ℝ := max ‖ℓ‖ 1
  set β' : ℝ := max ‖ψL‖ 1
  have hα1 : 1 ≤ α' := le_max_right _ _
  have hβ1 : 1 ≤ β' := le_max_right _ _
  have hℓz : ∀ z, ‖ℓ z‖ ≤ α' * ‖z‖ := fun z =>
    (ℓ.le_opNorm z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hψz : ∀ v, ‖ψL v‖ ≤ β' * ‖v‖ := fun v =>
    (ψL.le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  set Cq := cQU An
  have hCq0 : 0 ≤ Cq := cQU_nonneg An
  set a : ℝ := m * Cq * ‖ℓ‖ ^ 2 * β' ^ 2
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := LSG.Aux.prop21Lin n κ hκ a (by positivity) ωt hωt
  set γ : ℝ := α' * β' with hγ
  have hγ1 : 1 ≤ γ := one_le_mul_of_one_le_of_one_le hα1 hβ1
  refine ⟨max c₁ 1 * γ ^ 2, c₂ * 2 ^ n, by positivity, by positivity, ?_⟩
  intro L D Δ U R r μs hL hΔ hΔU hRr hr hU hDU hψR hc
  have hm1 : 1 ≤ max c₁ 1 := le_max_right _ _
  have hr1 : 1 ≤ r := le_trans (one_le_mul_of_one_le_of_one_le hm1 (one_le_pow₀ hγ1)) hr
  have hr0 : 0 < r := by linarith
  have hRr0 : 0 < R / r := lt_of_lt_of_le (by positivity) hRr
  have hγR : γ ^ 2 ≤ R / r := le_trans (le_mul_of_one_le_left (by positivity) hm1) hRr
  have hβγ : β' ^ 2 ≤ max c₁ 1 * γ ^ 2 := by
    have : β' ^ 2 ≤ γ ^ 2 := by
      simp only [γ]; rw [mul_pow]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hα1)
    exact this.trans (le_mul_of_one_le_left (by positivity) hm1)
  set r' : ℝ := β' * r
  set R' : ℝ := R / α'
  have hratio : R' / r' = (R / r) / γ := by simp only [R', r', hγ]; field_simp
  have hlog : Real.log (R / r) / 2 ≤ Real.log (R' / r') := by
    rw [hratio, Real.log_div hRr0.ne' (by positivity)]
    have h1 : Real.log γ ≤ Real.log (R / r) / 2 := by
      have := Real.log_le_log (by positivity) hγR
      rw [Real.log_pow] at this; push_cast at this; linarith
    linarith
  have hlog' : Real.log (R' / r') ≤ Real.log (R / r) := by
    rw [hratio]
    exact Real.log_le_log (by positivity) (div_le_self hRr0.le hγ1)
  have hlog0 : 0 ≤ Real.log (R / r) := Real.log_nonneg (le_trans (one_le_pow₀ hγ1) hγR)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  obtain ⟨p, hp0, hpΔ, hpz⟩ := h L (m * D * Cq * ‖ℓ‖ ^ 2) Δ U R' r'
    (fun l z => (μs l).eval (ℓ z)) hL hΔ hΔU
    (by rw [hratio, le_div_iff₀ (by positivity)]
        calc c₁ * γ ≤ max c₁ 1 * γ ^ 2 := by
              gcongr
              · exact le_max_left _ _
              · exact le_self_pow₀ hγ1 two_ne_zero
          _ ≤ R / r := hRr)
    (by calc c₁ ≤ max c₁ 1 := le_max_left _ _
          _ ≤ max c₁ 1 * γ ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hγ1)
          _ ≤ r := hr
          _ ≤ r' := le_mul_of_one_le_left hr0.le hβ1)
    (by calc r' ^ 2 * Real.log (R' / r') ≤ r' ^ 2 * Real.log (R / r) := by gcongr
          _ = β' ^ 2 * (r ^ 2 * Real.log (R / r)) := by ring
          _ ≤ (max c₁ 1 * γ ^ 2) * (r ^ 2 * Real.log (R / r)) := by gcongr
          _ = max c₁ 1 * γ ^ 2 * r ^ 2 * Real.log (R / r) := by ring
          _ ≤ U := hU)
    (by positivity)
    (by calc m * D * Cq * ‖ℓ‖ ^ 2 * r' ^ 2 = m * Cq * ‖ℓ‖ ^ 2 * β' ^ 2 * (D * r ^ 2) := by ring
          _ ≤ m * Cq * ‖ℓ‖ ^ 2 * β' ^ 2 * U := by gcongr
          _ = a * U := rfl)
    (fun l => ((μs l).differentiable_eval).comp ℓ.differentiable)
    (fun z hz => hψR _ (hℓV z) (by
      calc ‖ℓ z‖ ≤ α' * ‖z‖ := hℓz z
        _ ≤ α' * R' := by gcongr
        _ = R := by simp only [R']; field_simp))
    (by
      intro k z
      set w : Fin n → ℂ := ∑ i, (k i : ℂ) • ωt i
      have hw : ℓ w ∈ PerL d₀ d₁ B (latF An) := by
        simp only [w, map_sum, map_smul, hℓω]
        refine AddSubgroup.sum_mem _ fun i _ => ?_
        rw [Int.cast_smul_eq_zsmul ℂ]
        exact AddSubgroup.zsmul_mem _ (hωP i) _
      obtain ⟨mu, hmu, hmuψ⟩ := exists_qp_monoA An μs hw (ℓ z)
      refine ⟨mu, hmu.trans (Real.exp_le_exp.mpr ?_), fun l => ?_⟩
      · have h1 : ‖ℓ z‖ + ‖ℓ w‖ ≤ ‖ℓ‖ * (‖z‖ + ‖w‖) := by
          rw [mul_add]; exact add_le_add (ℓ.le_opNorm z) (ℓ.le_opNorm w)
        have h0 : 0 ≤ ‖ℓ z‖ + ‖ℓ w‖ := by positivity
        calc m * D * Cq * (‖ℓ z‖ + ‖ℓ w‖) ^ 2
            ≤ m * D * Cq * (‖ℓ‖ * (‖z‖ + ‖w‖)) ^ 2 := by gcongr
          _ = m * D * Cq * ‖ℓ‖ ^ 2 * (‖z‖ + ‖w‖) ^ 2 := by ring
      · show (μs l).eval (ℓ (z + w)) = mu * (μs l).eval (ℓ z)
        rw [map_add]; exact hmuψ l)
    (by
      have hrr : r ^ κ ≤ r' ^ κ := pow_le_pow_left₀ hr0.le (le_mul_of_one_le_left hr0.le hβ1) κ
      have hll : (Real.log (R / r) / 2) ^ n ≤ Real.log (R' / r') ^ n :=
        pow_le_pow_left₀ (by positivity) hlog n
      have hΔ0 : (0 : ℝ) ≤ L * Δ := by positivity
      calc c₂ * U ^ (n + 1) = c₂ * 2 ^ n * U ^ (n + 1) / 2 ^ n := by field_simp
        _ ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n / 2 ^ n := by gcongr
        _ = L * Δ * r ^ κ * (Real.log (R / r) / 2) ^ n := by rw [div_pow]; ring
        _ ≤ L * Δ * r' ^ κ * Real.log (R' / r') ^ n := by gcongr)
  refine ⟨p, hp0, hpΔ, fun z hzV hz => ?_⟩
  have hv := hpz (ψL ⟨z, hzV⟩) ((hψz _).trans (mul_le_mul_of_nonneg_left hz (by positivity)))
  simpa only [hℓψ] using hv

/-- **`prop21A` with explicit degrees** (as `LSG.Aux.prop21_G_deg`). -/
theorem prop21A_deg (An : ∀ k, AbBlockAn (B k)) (V : Submodule ℂ (Tan d₀ d₁ B)) {n : ℕ}
    (hn : finrank ℂ V = n) {κ : ℕ} (ω : Fin κ → Tan d₀ d₁ B) (hωV : ∀ i, ω i ∈ V)
    (hωP : ∀ i, ω i ∈ PerL d₀ d₁ B (latF An)) (hω : LinearIndependent ℂ ω) :
    ∃ c₁ c₂ cW : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ cW ∧
      ∀ (L D D₀ D₁ : ℕ) (Δ U R r : ℝ) (μs : Fin L → MonoA d₀ d₁ B D),
      (∀ l, ∑ i, (μs l).α i ≤ D₀) → (∀ l, ∑ i, (μs l).β i ≤ D₁) →
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → c₁ * r ^ 2 * Real.log (R / r) ≤ U →
      (D : ℝ) * r ^ 2 ≤ U →
      Real.log L + D₀ * Real.log (1 + R) + D₁ * R + m * D * cW * (1 + R) ^ 2 ≤ U →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z ∈ V, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * (μs l).eval z‖ ≤ Real.exp (-U) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21A An V hn ω hωV hωP hω
  refine ⟨c₁, c₂, cWU An, hc₁, hc₂, cWU_nonneg An, fun L D D₀ D₁ Δ U R r μs hα hβ hL hΔ hΔU hRr hr hU
    hDU hG hc => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hc₁ hr
  have hR0 : 0 ≤ R := by
    have : 0 < R / r := lt_of_lt_of_le hc₁ hRr
    exact ((div_pos_iff_of_pos_right hr0).mp this).le
  exact h L D Δ U R r μs hL hΔ hΔU hRr hr hU hDU
    (fun p _ hp => sum_norm_eval_le An μs hα hβ hR0 hL hG p hp) hc

end LSG.AuxA
