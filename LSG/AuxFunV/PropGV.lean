/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.PropG
import LSG.AuxFunV.MonoV

/-!
# W83 Prop. 2.1 for the class `𝒞` on `V ⊂ T_G` with `V ∩ fibre = 0` (`prop21_GV`)

**The risk-3 workaround (`VECEXT.md` §3.3, §4 R3).** The fibre coordinate forms `s_i` send the
periods `(λ, M η(λ))` of `G₂` to `Σ_j M_ij η_j(Λ_j)`, which need not be discrete when `m ≥ 3`. Under
the premise `V ∩ fibre = 0` of `Theorem41VecLA`, the projection `π : T_G → T_{G/fibre}` (forget
`s`, `piT`) is injective on `V`, so `n = dim V` of the **non-fibre** coordinate forms
`(a, b, z)` restrict to a basis of `V*` (`exists_coordsVV`). They send a period `ω ∈ Ω(G)` to the
coordinates of `πω ∈ Ω(G/fibre) = Per Ls`, i.e. into `0`, `2πiℤ`, `Λ_j` (`per_coord`): discrete
groups, the setting of `LSG.Aux.prop21Lat` (Tier 2). The fibre forms are never used.

* `exists_coordsVV`: `ψ : V ≃ ℂⁿ` with `ψ v k = tcoord (J k) (πv)`.
* **`prop21_GV`**: W83 Prop. 2.1 with the κ-saving for the monomials `MonoV` of `G ∈ 𝒞` on `V`,
  periods `ω_i ∈ V ∩ Ω(G)` (`ℤ`-independent, possibly `ℂ`-dependent).
* **`prop21_GV_deg`**: the same with degree bounds in place of the growth hypothesis
  (`log L + (D₀ + D) log(1+R) + D log K + D₁ R + m D c (1+R)² ≤ U`).
-/

open Complex Finset Module LSG.W88 LSG.W88.Vec
open LSG.Aux (Coord tcoord exists_coordsV latA latB latD per_coord perVec Idx exists_minor_ne_zero
  prop21Lat perVec_sum)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m q : ℕ}

/-- **Coordinates on `V` from non-fibre forms** (needs `V ∩ fibre = 0`). -/
theorem exists_coordsVV (V : Submodule ℂ (TanV d0 d1 m q)) (hV : V ⊓ fibreV = ⊥) {n : ℕ}
    (hn : finrank ℂ V = n) :
    ∃ J : Fin n → Coord d0 d1 m, ∃ ψ : V ≃ₗ[ℂ] (Fin n → ℂ),
      ∀ v k, ψ v k = tcoord (J k) (piT (v : TanV d0 d1 m q)) := by
  let f : V →ₗ[ℂ] Tan d0 d1 m := piTL.comp V.subtype
  have hf : Function.Injective f := fun u v h =>
    Subtype.ext (piT_injOn hV u.2 v.2 h)
  let e : V ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hn' : finrank ℂ (LinearMap.range f) = n := by rw [← e.finrank_eq, hn]
  obtain ⟨J, ψ', hψ'⟩ := exists_coordsV (LinearMap.range f) hn'
  exact ⟨J, e.trans ψ', fun v k => by
    rw [LinearEquiv.trans_apply, hψ']
    rfl⟩

/-- **W83 Prop. 2.1 for the monomials of `exp_G`, `G ∈ 𝒞`, on `V` with `V ∩ fibre = 0`.** -/
theorem prop21_GV (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ)
    (V : Submodule ℂ (TanV d0 d1 m q)) (hV : V ⊓ fibreV = ⊥) {n : ℕ}
    (hn : finrank ℂ V = n) {κ : ℕ} (ω : Fin κ → TanV d0 d1 m q) (hωV : ∀ i, ω i ∈ V)
    (hωP : ∀ i, ω i ∈ PerV Ls M) (hω : LinearIndependent ℤ ω) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L D : ℕ) (Δ U R r : ℝ) (μs : Fin L → MonoV d0 d1 m q D),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → c₁ * r ^ 2 * Real.log (R / r) ≤ U →
      (D : ℝ) * r ^ 2 ≤ U →
      (∀ p ∈ V, ‖p‖ ≤ R → ∑ l, ‖(μs l).eval Ls M p‖ ≤ Real.exp U) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z ∈ V, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * (μs l).eval Ls M z‖ ≤ Real.exp (-U) := by
  classical
  -- coordinates (non-fibre forms) and lattice data
  obtain ⟨J, ψ, hψ⟩ := exists_coordsVV V hV hn
  set α : Fin n → ℂ := fun k => latA Ls (J k)
  set β : Fin n → ℂ := fun k => latB Ls (J k)
  have hD : ∀ k, ((starRingEnd ℂ) (α k) * β k).im ≠ 0 := fun k => latD Ls (J k)
  choose pc hpc using fun i c => per_coord Ls (piT_mem_per Ls M (hωP i)) c
  set P : Fin κ → Idx n → ℤ := fun i c => if c.2 = 0 then (pc i (J c.1)).1 else (pc i (J c.1)).2
  set ωt : Fin κ → (Fin n → ℂ) := fun i => ψ ⟨ω i, hωV i⟩
  have hωt : ∀ i, perVec α β (P i) = ωt i := by
    intro i; funext k
    simp only [perVec, P, ωt, hψ, α, β]
    simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
    exact (hpc i (J k)).symm
  have hPind : LinearIndependent ℤ P := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∑ i, (g i : ℂ) • ωt i = 0 := by
      have := congrArg (perVec α β) hg
      rw [perVec_sum] at this
      simp only [hωt] at this
      rw [this]; funext k; simp [perVec]
    let v : V := ⟨∑ i, (g i : ℂ) • ω i, V.sum_mem fun i _ => V.smul_mem _ (hωV i)⟩
    have hv : ψ v = 0 := by
      funext k
      rw [hψ]
      have e : ∀ i, tcoord (J k) (piT (ω i)) = ωt i k := fun i => (hψ ⟨ω i, hωV i⟩ k).symm
      have := congrFun hsum k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [v, map_sum, map_smul, smul_eq_mul, e, Pi.zero_apply]
      exact this
    have h2 : ∑ i, (g i : ℂ) • ω i = 0 := by
      have := congrArg Subtype.val (ψ.injective (hv.trans (map_zero ψ).symm))
      simpa [v] using this
    have h3 : ∑ i, g i • ω i = 0 := by
      rw [← h2]; exact sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    exact (Fintype.linearIndependent_iff.mp hω) g h3
  obtain ⟨I, hI, hdet⟩ := exists_minor_ne_zero P hPind
  -- the maps `ℓ : ℂⁿ → T_G` and `ψ : V → ℂⁿ`
  let ℓ : (Fin n → ℂ) →L[ℂ] TanV d0 d1 m q :=
    LinearMap.toContinuousLinearMap (V.subtype ∘ₗ ψ.symm.toLinearMap)
  let ψL : V →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap ψ.toLinearMap
  have hℓV : ∀ z, ℓ z ∈ V := fun z => (ψ.symm z).2
  have hℓψ : ∀ v : V, ℓ (ψL v) = v := fun v => by
    simp [ℓ, ψL]
  have hℓω : ∀ i, ℓ (ωt i) = ω i := fun i => hℓψ ⟨ω i, hωV i⟩
  set α' : ℝ := max ‖ℓ‖ 1
  set β' : ℝ := max ‖ψL‖ 1
  have hα1 : 1 ≤ α' := le_max_right _ _
  have hβ1 : 1 ≤ β' := le_max_right _ _
  have hℓz : ∀ z, ‖ℓ z‖ ≤ α' * ‖z‖ := fun z =>
    (ℓ.le_opNorm z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hψz : ∀ v, ‖ψL v‖ ≤ β' * ‖v‖ := fun v =>
    (ψL.le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  obtain ⟨Cq, hCq0, hqp⟩ := exists_qp_monoV (d0 := d0) (d1 := d1) Ls M
  set a : ℝ := 3 * Cq * ‖ℓ‖ ^ 2 * β' ^ 2
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21Lat n κ a (by positivity) α β hD P I hI hdet
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
  -- the new parameters
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
  obtain ⟨p, hp0, hpΔ, hpz⟩ := h L (3 * D * Cq * ‖ℓ‖ ^ 2) Δ U R' r'
    (fun l z => (μs l).eval Ls M (ℓ z)) hL hΔ hΔU
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
    (by calc 3 * D * Cq * ‖ℓ‖ ^ 2 * r' ^ 2 = 3 * Cq * ‖ℓ‖ ^ 2 * β' ^ 2 * (D * r ^ 2) := by ring
          _ ≤ 3 * Cq * ‖ℓ‖ ^ 2 * β' ^ 2 * U := by gcongr
          _ = a * U := rfl)
    (fun l => (differentiable_evalV Ls M (μs l)).comp ℓ.differentiable)
    (fun z hz => hψR _ (hℓV z) (by
      calc ‖ℓ z‖ ≤ α' * ‖z‖ := hℓz z
        _ ≤ α' * R' := by gcongr
        _ = R := by simp only [R']; field_simp))
    (by
      intro k z
      have hP : ∀ i, ℓ (ωt i) ∈ PerV Ls M := fun i => (hℓω i).symm ▸ hωP i
      obtain ⟨mu, hmu, hmuψ⟩ := hqp D n κ L ℓ ωt hP μs k z
      refine ⟨mu, ?_, fun l => ?_⟩
      · simpa only [hωt] using hmu
      · simpa only [hωt] using hmuψ l)
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

/-- **`prop21_GV` with explicit degrees** (growth hypothesis from `exists_sum_monoV_le_exp`). -/
theorem prop21_GV_deg (Ls : Fin m → PeriodPair) (M : Matrix (Fin q) (Fin m) ℂ)
    (V : Submodule ℂ (TanV d0 d1 m q)) (hV : V ⊓ fibreV = ⊥) {n : ℕ}
    (hn : finrank ℂ V = n) {κ : ℕ} (ω : Fin κ → TanV d0 d1 m q) (hωV : ∀ i, ω i ∈ V)
    (hωP : ∀ i, ω i ∈ PerV Ls M) (hω : LinearIndependent ℤ ω) :
    ∃ c₁ c₂ cW K : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ cW ∧ 1 ≤ K ∧
      ∀ (L D D₀ D₁ : ℕ) (Δ U R r : ℝ) (μs : Fin L → MonoV d0 d1 m q D),
      (∀ l, ∑ i, (μs l).α i ≤ D₀) → (∀ l, ∑ i, (μs l).β i ≤ D₁) →
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → c₁ * r ^ 2 * Real.log (R / r) ≤ U →
      (D : ℝ) * r ^ 2 ≤ U →
      Real.log L + (D₀ + D) * Real.log (1 + R) + D * Real.log K + D₁ * R +
        m * D * cW * (1 + R) ^ 2 ≤ U →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z ∈ V, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * (μs l).eval Ls M z‖ ≤ Real.exp (-U) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := prop21_GV Ls M V hV hn ω hωV hωP hω
  obtain ⟨cW, K, hcW0, hK1, hcW⟩ := exists_sum_monoV_le_exp (d0 := d0) (d1 := d1) Ls M
  refine ⟨c₁, c₂, cW, K, hc₁, hc₂, hcW0, hK1, fun L D D₀ D₁ Δ U R r μs hα hβ hL hΔ hΔU hRr hr hU
    hDU hG hc => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hc₁ hr
  have hR0 : 0 ≤ R := by
    have : 0 < R / r := lt_of_lt_of_le hc₁ hRr
    exact ((div_pos_iff_of_pos_right hr0).mp this).le
  exact h L D Δ U R r μs hL hΔ hΔU hRr hr hU hDU
    (fun p _ hp => hcW L D D₀ D₁ μs R U hα hβ hR0 hL hG p hp) hc

end LSG.AuxV
