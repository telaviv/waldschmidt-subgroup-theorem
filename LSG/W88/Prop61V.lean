/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Prop61
import LSG.W88.Prop61VData
import LSG.W88.Prop61VArith
import LSG.AuxFunV.LemmaUCoreV
import LSG.AuxFunV.MonoIndepV
import LSG.AuxFunV.PropGV

/-!
# W88 Prop. 6.1 for the class `𝒞` under (NR) and `V ∩ fibre = 0` (Stage 5, phase 2)

**`LSG.AuxV.prop61V`** / **`prop61V_b`**: `G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of
`(E₁ × ⋯ × E_m)^♮` along an algebraic `M : ℂ^m → ℂ^r`; `V ⊂ T_G` of dimension `n < d = d₀+d₁+m+r`
with `V ∩ fibre = 0`, `W ≤ V` rational over `ℚ̄`, `y_j ∈ V ∩ Λ(G)`, `ω_i ∈ V ∩ Ω(G)`
`ℤ`-independent,
(NR) `d₁ + 2d₀ + κ ≤ 2n`. There is `C > 0` such that for all large `S`, with
`Δ^{d−n} = C S^{d₁+2(m+r)−κ} (log S)^{b d₀}`, there is `P = Σ_l p_l M_l` (distinct monomials
`MonoV` of elliptic degree `D ≤ Δ/S²` counting the fibre forms, `G_a`-degree `≤ Δ/(log S)^b`,
`G_m`-degree `≤ Δ/S`) with `P ∘ exp_G ≢ 0` vanishing along `W` to order `≥ Δ/log S` at every
`Σ h_j y_j`, `0 ≤ h_j ≤ S`.

Proof as `LSG.W88.prop61_b`: `prop21_GV_deg` (risk-3 workaround), `lemmaU_coreV`,
`exists_PsiV_ne_zero`. The monomials (`monoFamV`) are
`aᵅ (e^b)^β Π_j (σ_j³)^{D−Φ−a_j}(σ_j³℘_j)^{a_j} Π_i S_i^{φ_i}`, `a_j, φ_i ≤ D₂`, `D = (r+1) D₂`,
so their number is `≍ D₂^{m+r}` (the `d₂ = m + r` of W88).
-/

open Complex Finset Module LSG.W88 LSG.W88.Vec

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}

/-- The monomial family of the class `𝒞`. -/
def monoFamV (d0 d1 m r a₀ a₁ D2 : ℕ)
    (x : (Fin d0 → Fin (a₀ + 1)) × (Fin d1 → Fin (a₁ + 1)) × (Fin m → Fin (D2 + 1)) ×
      (Fin r → Fin (D2 + 1))) :
    MonoV d0 d1 m r ((r + 1) * D2) where
  α := fun i => x.1 i
  β := fun i => x.2.1 i
  γ := fun j => ![(r + 1) * D2 - ∑ i, (x.2.2.2 i : ℕ) - x.2.2.1 j, x.2.2.1 j, 0]
  φ := fun i => x.2.2.2 i
  hγ := fun j => by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, add_zero]
    have h1 : ∑ i, (x.2.2.2 i : ℕ) ≤ r * D2 := by
      calc ∑ i, (x.2.2.2 i : ℕ) ≤ ∑ _i : Fin r, D2 :=
            sum_le_sum fun i _ => Nat.lt_succ_iff.mp (x.2.2.2 i).isLt
        _ = r * D2 := by simp
    have h2 := (x.2.2.1 j).isLt
    have : (r + 1) * D2 = r * D2 + D2 := by ring
    omega
  hφ := by
    have h1 : ∑ i, (x.2.2.2 i : ℕ) ≤ r * D2 := by
      calc ∑ i, (x.2.2.2 i : ℕ) ≤ ∑ _i : Fin r, D2 :=
            sum_le_sum fun i _ => Nat.lt_succ_iff.mp (x.2.2.2 i).isLt
        _ = r * D2 := by simp
    change ∑ i, (x.2.2.2 i : ℕ) ≤ (r + 1) * D2
    nlinarith

lemma monoFamV_rexp_injective (d0 d1 m r a₀ a₁ D2 : ℕ) :
    Function.Injective fun x => (monoFamV d0 d1 m r a₀ a₁ D2 x).rexp := by
  intro x x' h
  have h' := fun v => congrFun h v
  obtain ⟨α, β, a, φ⟩ := x
  obtain ⟨α', β', a', φ'⟩ := x'
  simp only [Prod.mk.injEq]
  refine ⟨funext fun i => Fin.ext ?_, funext fun i => Fin.ext ?_, funext fun j => Fin.ext ?_,
    funext fun i => Fin.ext ?_⟩
  · simpa [MonoV.rexp, monoFamV] using h' (.inl i)
  · simpa [MonoV.rexp, monoFamV] using h' (.inr (.inl i))
  · simpa [MonoV.rexp, monoFamV] using h' (.inr (.inr (.inl j)))
  · simpa [MonoV.rexp, monoFamV] using h' (.inr (.inr (.inr i)))

set_option maxHeartbeats 4000000 in -- large proof (many local constants)
/-- **W88 Prop. 6.1 for the class `𝒞` under (NR) and `V ∩ fibre = 0`**, with `a = 1` and any
`b ≥ 1`: `D₀ (log S)^b = Δ` and `Δ^{d−n} = C S^{d₁+2(m+r)−κ} (log S)^{b d₀}`. -/
theorem prop61V_b (b : ℕ) (hb : 1 ≤ b) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (hg : ∀ k, IsAlgebraic ℚ (Ls k).g₂ ∧ IsAlgebraic ℚ (Ls k).g₃) (hM : AlgMat M)
    (V W : Submodule ℂ (TanV d0 d1 m r)) (hWV : W ≤ V) (hW : RatSubV W) (hVf : V ⊓ fibreV = ⊥)
    (hn : finrank ℂ V < d0 + d1 + m + r) {μ : ℕ} (y : Fin μ → TanV d0 d1 m r)
    (hyV : ∀ j, y j ∈ V) (hyL : ∀ j, y j ∈ LamV Ls M) {κ : ℕ} (ω : Fin κ → TanV d0 d1 m r)
    (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ PerV Ls M) (hω : LinearIndependent ℤ ω)
    (hNR : d1 + 2 * d0 + κ ≤ 2 * finrank ℂ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ S₀ : ℕ, ∀ S : ℕ, S₀ ≤ S →
      ∃ (D L : ℕ) (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ),
        (∀ l, ((∑ i, (μs l).α i : ℕ) : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) (b * d0)
          (d0 + d1 + m + r - finrank ℂ V) S / Real.log S ^ b) ∧
        (∀ l, ((∑ i, (μs l).β i : ℕ) : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) (b * d0)
          (d0 + d1 + m + r - finrank ℂ V) S / S) ∧
        (D : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) (b * d0) (d0 + d1 + m + r - finrank ℂ V) S /
          (S : ℝ) ^ 2 ∧
        (∃ x, PsiV Ls M μs p x ≠ 0) ∧
        ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
          VanishAlong (PsiV Ls M μs p) W
            (delta61 C (d1 + 2 * (m + r) - κ) (b * d0) (d0 + d1 + m + r - finrank ℂ V) S /
              Real.log S)
            (∑ j, h j • y j) := by
  classical
  set n := finrank ℂ V with hndef
  set q := d0 + d1 + m + r - n with hqdef
  set e := d1 + 2 * (m + r) - κ with hedef
  have hq1 : 1 ≤ q := by omega
  have he : 2 * q ≤ e := by omega
  have heκ : e + κ = d1 + 2 * (m + r) := by omega
  have hdq : d0 + d1 + (m + r) = n + q := by omega
  -- data and constants
  obtain ⟨K, _, _, ι, τ, Dt, hDy, hDw⟩ := exists_LUDataV Ls M hg hM W hW y hyL
  have hwV : ∀ t, Dt.w t ∈ V := fun t => hWV (hDw ▸ Submodule.subset_span ⟨t, rfl⟩)
  have hyV' : ∀ j, Dt.y j ∈ V := by rw [hDy]; exact hyV
  obtain ⟨c₀, hc₀1, hLU⟩ := lemmaU_coreV Ls M ι V Dt hyV' hwV
  obtain ⟨c₁, c₂, cW, KK, hc₁, hc₂, hcW, hKK, hS21⟩ :=
    prop21_GV_deg Ls M V hVf hndef.symm ω hωV hωP hω
  have hlKK : 0 ≤ Real.log KK := Real.log_nonneg hKK
  -- the constant `ν` and the constant `C`
  set Ke : ℝ := ((e + b * d0 + 1 : ℕ) : ℝ) / q with hKedef
  have hKe : 0 ≤ Ke := by positivity
  set Kt : ℝ := 2 + Ke with hKtdef
  set ν : ℝ := 3 + c₁ + c₀ + 16 * m * cW + c₀ * (9 + 3 * Kt) + Real.log KK with hνdef
  have hν3 : 3 ≤ ν := by rw [hνdef]; nlinarith
  have hν1 : 1 ≤ ν := by linarith
  have hνc₁ : c₁ ≤ ν := by rw [hνdef]; nlinarith
  have hνc₀ : c₀ ≤ ν := by rw [hνdef]; nlinarith
  have hνcW : 16 * m * cW ≤ ν := by rw [hνdef]; nlinarith
  have hνbud : c₀ * (9 + 3 * Kt) ≤ ν := by rw [hνdef]; nlinarith
  have hνK : Real.log KK ≤ ν := by rw [hνdef]; nlinarith
  have hlogν : 0 < Real.log ν := Real.log_pos (by linarith)
  set Kν : ℝ := ν ^ (2 * κ) * Real.log ν ^ n /
    (((d0 : ℝ) + 1) ^ d0 * ((d1 : ℝ) + 1) ^ d1 * ν ^ (d0 + d1 + (m + r) + 1)) with hKνdef
  have hKν : 0 < Kν := by positivity
  set c₂' : ℝ := c₂ * ((r : ℝ) + 1) ^ (m + r) with hc₂'def
  have hc₂' : 0 ≤ c₂' := by positivity
  set C : ℝ := max 1 (c₂' * ν ^ (6 * (n + 1)) / Kν) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCK : c₂' * ν ^ (6 * (n + 1)) ≤ C * Kν := by
    have := le_max_right 1 (c₂' * ν ^ (6 * (n + 1)) / Kν)
    rw [div_le_iff₀ hKν] at this; exact this
  -- the threshold `S₀`
  set S₀ : ℕ := ⌈max (max 3 C) (max (2 * ν ^ 3) (((d0 + d1 + m + r + 1 : ℕ) : ℝ) * Kt))⌉₊
    with hS₀def
  refine ⟨C, by positivity, S₀, fun S hS => ?_⟩
  -- consequences of `S ≥ S₀`
  have hS₀S : max (max 3 C) (max (2 * ν ^ 3) (((d0 + d1 + m + r + 1 : ℕ) : ℝ) * Kt)) ≤
      (S : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hS)
  have hS3R : (3 : ℝ) ≤ S := (le_max_left _ _).trans ((le_max_left _ _).trans hS₀S)
  have hS3 : 3 ≤ S := by exact_mod_cast hS3R
  have hSC : C ≤ S := (le_max_right _ _).trans ((le_max_left _ _).trans hS₀S)
  have hSν : 2 * ν ^ 3 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans hS₀S)
  have hSK0 : ((d0 + d1 + m + r + 1 : ℕ) : ℝ) * Kt ≤ S :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hS₀S)
  have hSK : ((d0 : ℝ) + d1 + m + r + 1) * Kt ≤ S := by push_cast at hSK0; exact hSK0
  have hSR1 : (1 : ℝ) ≤ S := by linarith only [hS3R]
  have hS0 : (0 : ℝ) < S := by linarith only [hS3R]
  set lS := Real.log S with hlSdef
  have hlS : 1 ≤ lS := log_ge_one hS3
  have hlSS : lS ≤ (S : ℝ) ^ 2 := log_le_sq hS3
  have hlSS' : lS ≤ S := log_le_self' hS0
  have h2lS : 2 * lS ≤ (S : ℝ) ^ 2 := by nlinarith only [hlSS', hS3R]
  set lb := lS ^ b with hlbdef
  have hlb : lS ≤ lb := le_self_pow₀ hlS (by omega)
  have hlb1 : 1 ≤ lb := hlS.trans hlb
  set Δ := delta61 C e (b * d0) q S with hΔdef
  have hΔS : (S : ℝ) ^ 2 ≤ Δ := sq_le_delta hC1 hq1 he hS3
  have hΔ1 : 1 ≤ Δ := le_trans (by nlinarith only [hS3R]) hΔS
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  have hlΔ : Real.log Δ ≤ Ke * lS := log_delta_le hC1 hSC hq1 he hS3
  have hΔq : Δ ^ q = C * (S : ℝ) ^ e * lb ^ d0 := by
    rw [hlbdef, ← pow_mul]; exact delta_pow (by linarith only [hC1]) hq1
  -- the parameters
  set A₀ : ℕ := ⌊Δ / (ν * lb)⌋₊ with hA₀def
  set A₁ : ℕ := ⌊Δ / (ν * S)⌋₊ with hA₁def
  set D2 : ℕ := ⌊Δ / (((r : ℝ) + 1) * ν * (S : ℝ) ^ 2)⌋₊ with hD2def
  set D : ℕ := (r + 1) * D2 with hDdef
  set a₀ := A₀ / (d0 + 1) with ha₀def
  set a₁ := A₁ / (d1 + 1) with ha₁def
  set T : ℕ := ⌈Δ / lS⌉₊ with hTdef
  have hA₀lb : (A₀ : ℝ) ≤ Δ / (ν * lb) := Nat.floor_le (by positivity)
  have hA₀le : (A₀ : ℝ) ≤ Δ / (ν * lS) := hA₀lb.trans
    (div_le_div_of_nonneg_left hΔ0.le (by positivity) (by nlinarith only [hlb, hν1, hlS]))
  have hA₁le : (A₁ : ℝ) ≤ Δ / (ν * S) := Nat.floor_le (by positivity)
  have hD2le : (D2 : ℝ) ≤ Δ / (((r : ℝ) + 1) * ν * (S : ℝ) ^ 2) := Nat.floor_le (by positivity)
  have hDle : (D : ℝ) ≤ Δ / (ν * (S : ℝ) ^ 2) := by
    rw [hDdef]; push_cast
    calc ((r : ℝ) + 1) * D2 ≤ ((r : ℝ) + 1) * (Δ / (((r : ℝ) + 1) * ν * (S : ℝ) ^ 2)) := by
          gcongr
      _ = Δ / (ν * (S : ℝ) ^ 2) := by field_simp
  have hA₀lt : Δ / (ν * lb) < A₀ + 1 := Nat.lt_floor_add_one _
  have hA₁lt : Δ / (ν * S) < A₁ + 1 := Nat.lt_floor_add_one _
  have hD2lt : Δ / (((r : ℝ) + 1) * ν * (S : ℝ) ^ 2) < D2 + 1 := Nat.lt_floor_add_one _
  have hDlt : Δ / (ν * (S : ℝ) ^ 2) ≤ ((r : ℝ) + 1) * (D2 + 1) := by
    have h := hD2lt.le
    rw [div_le_iff₀ (by positivity)] at h ⊢
    nlinarith
  have ha₀A : A₀ + 1 ≤ (a₀ + 1) * (d0 + 1) := by
    have := Nat.lt_div_mul_add (a := A₀) (b := d0 + 1) (by omega); rw [ha₀def]; linarith
  have ha₁A : A₁ + 1 ≤ (a₁ + 1) * (d1 + 1) := by
    have := Nat.lt_div_mul_add (a := A₁) (b := d1 + 1) (by omega); rw [ha₁def]; linarith
  have ha₀le : d0 * a₀ ≤ A₀ := by
    have := Nat.div_mul_le_self A₀ (d0 + 1); rw [ha₀def]; nlinarith
  have ha₁le : d1 * a₁ ≤ A₁ := by
    have := Nat.div_mul_le_self A₁ (d1 + 1); rw [ha₁def]; nlinarith
  have ha₀A' : a₀ ≤ A₀ := Nat.div_le_self _ _
  have ha₁A' : a₁ ≤ A₁ := Nat.div_le_self _ _
  have hTle : (T : ℝ) < Δ / lS + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTge : Δ / lS ≤ T := Nat.le_ceil _
  -- the monomials
  let Ix := (Fin d0 → Fin (a₀ + 1)) × (Fin d1 → Fin (a₁ + 1)) × (Fin m → Fin (D2 + 1)) ×
    (Fin r → Fin (D2 + 1))
  set L := Fintype.card Ix with hLdef
  let eqv := Fintype.equivFin Ix
  set μs : Fin L → MonoV d0 d1 m r D := fun l => monoFamV d0 d1 m r a₀ a₁ D2 (eqv.symm l)
    with hμsdef
  have hLcard : L = (a₀ + 1) ^ d0 * (a₁ + 1) ^ d1 * (D2 + 1) ^ (m + r) := by
    simp only [hLdef, Ix, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]; ring
  have hL1 : 1 ≤ L := by rw [hLcard]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hαi : ∀ l i, (μs l).α i ≤ a₀ := fun l i => Nat.lt_succ_iff.mp ((eqv.symm l).1 i).isLt
  have hβi : ∀ l i, (μs l).β i ≤ a₁ := fun l i => Nat.lt_succ_iff.mp ((eqv.symm l).2.1 i).isLt
  have hαsum : ∀ l, ∑ i, (μs l).α i ≤ A₀ := fun l =>
    ((sum_le_sum fun i _ => hαi l i).trans (by simp)).trans ha₀le
  have hβsum : ∀ l, ∑ i, (μs l).β i ≤ A₁ := fun l =>
    ((sum_le_sum fun i _ => hβi l i).trans (by simp)).trans ha₁le
  -- `log (L + 1) ≤ Δ`
  have hfac : ∀ x : ℕ, (x : ℝ) ≤ Δ → ((x : ℝ) + 1) ≤ 2 * Δ := fun x hx => by
    linarith only [hx, hΔ1]
  have hA₀Δ : (A₀ : ℝ) ≤ Δ := hA₀le.trans (div_le_self hΔ0.le (by nlinarith only [hν1, hlS]))
  have hA₁Δ : (A₁ : ℝ) ≤ Δ := hA₁le.trans (div_le_self hΔ0.le (by nlinarith only [hν1, hSR1]))
  have hDΔ : (D : ℝ) ≤ Δ := hDle.trans (div_le_self hΔ0.le (by nlinarith only [hν1, hSR1]))
  have hD2Δ : (D2 : ℝ) ≤ Δ := by
    have : (D2 : ℝ) ≤ D := by rw [hDdef]; push_cast; nlinarith [(Nat.cast_nonneg D2 : (0 : ℝ) ≤ D2),
      (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    exact this.trans hDΔ
  have hL2 : ((L : ℝ) + 1) ≤ (2 * Δ) ^ (d0 + d1 + m + r + 1) := by
    have h1 : (L : ℝ) ≤ (2 * Δ) ^ (d0 + d1 + m + r) := by
      rw [hLcard]; push_cast
      have e0 : ((a₀ : ℝ) + 1) ≤ 2 * Δ :=
        hfac _ ((by exact_mod_cast ha₀A' : (a₀ : ℝ) ≤ A₀).trans hA₀Δ)
      have e1 : ((a₁ : ℝ) + 1) ≤ 2 * Δ :=
        hfac _ ((by exact_mod_cast ha₁A' : (a₁ : ℝ) ≤ A₁).trans hA₁Δ)
      have e2 : ((D2 : ℝ) + 1) ≤ 2 * Δ := hfac _ hD2Δ
      calc ((a₀ : ℝ) + 1) ^ d0 * ((a₁ : ℝ) + 1) ^ d1 * ((D2 : ℝ) + 1) ^ (m + r) ≤
            (2 * Δ) ^ d0 * (2 * Δ) ^ d1 * (2 * Δ) ^ (m + r) := by gcongr
        _ = (2 * Δ) ^ (d0 + d1 + m + r) := by rw [← pow_add, ← pow_add]; ring_nf
    have h2 : (1 : ℝ) ≤ (2 * Δ) ^ (d0 + d1 + m + r) := one_le_pow₀ (by linarith only [hΔ1])
    calc (L : ℝ) + 1 ≤ 2 * (2 * Δ) ^ (d0 + d1 + m + r) := by linarith only [h1, h2]
      _ ≤ (2 * Δ) * (2 * Δ) ^ (d0 + d1 + m + r) :=
          mul_le_mul_of_nonneg_right (by linarith only [hΔ1]) (by positivity)
      _ = (2 * Δ) ^ (d0 + d1 + m + r + 1) := by ring
  have hlL1 : Real.log ((L : ℝ) + 1) ≤ Δ := by
    have h1 := Real.log_le_log (by positivity) hL2
    rw [Real.log_pow, Real.log_mul (by norm_num) hΔ0.ne'] at h1
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith only [this]
    have h3 : Real.log 2 + Real.log Δ ≤ Kt * lS := by
      rw [hKtdef]; nlinarith only [hl2, hlΔ, hlS, hKe]
    have h4 : ((d0 + d1 + m + r + 1 : ℕ) : ℝ) * (Kt * lS) ≤ (S : ℝ) ^ 2 := by
      push_cast
      calc ((d0 : ℝ) + d1 + m + r + 1) * (Kt * lS) =
            (((d0 : ℝ) + d1 + m + r + 1) * Kt) * lS := by ring
        _ ≤ S * S := mul_le_mul hSK hlSS' (by linarith only [hlS]) hS0.le
        _ = (S : ℝ) ^ 2 := by ring
    calc Real.log ((L : ℝ) + 1) ≤ ((d0 + d1 + m + r + 1 : ℕ) : ℝ) *
          (Real.log 2 + Real.log Δ) := h1
      _ ≤ ((d0 + d1 + m + r + 1 : ℕ) : ℝ) * (Kt * lS) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ ≤ (S : ℝ) ^ 2 := h4
      _ ≤ Δ := hΔS
  -- W83 Prop. 2.1 (`prop21_GV_deg`)
  have hν0 : 0 < ν := by linarith only [hν1]
  have hRr : ν ^ 3 * S / (ν ^ 2 * S) = ν := by field_simp
  have hlog1R : Real.log (1 + ν ^ 3 * S) ≤ 2 * lS := by
    have h1 : 1 + ν ^ 3 * S ≤ (S : ℝ) ^ 2 := by
      have : ν ^ 3 * S ≥ 1 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hν1) hSR1
      nlinarith only [hSν, this, hS0]
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow, Nat.cast_ofNat] at h2
  have hlog1R0 : 0 ≤ Real.log (1 + ν ^ 3 * S) := Real.log_nonneg (by
    have : 0 ≤ ν ^ 3 * S := by positivity
    linarith only [this])
  have hlogL : Real.log (L : ℝ) ≤ Δ :=
    (Real.log_le_log (by exact_mod_cast hL1) (by linarith only)).trans hlL1
  obtain ⟨p, hp0, hpB, hsm⟩ := hS21 L D A₀ A₁ (Δ / ν) (ν ^ 6 * Δ) (ν ^ 3 * S) (ν ^ 2 * S) μs
    hαsum hβsum hL1 (by positivity)
    (by
      calc Δ / ν ≤ Δ := div_le_self hΔ0.le hν1
        _ = 1 * Δ := (one_mul _).symm
        _ ≤ ν ^ 6 * Δ := mul_le_mul_of_nonneg_right (one_le_pow₀ hν1) hΔ0.le)
    (by rw [hRr]; exact hνc₁)
    (by
      calc c₁ ≤ ν := hνc₁
        _ = ν * 1 * 1 := by ring
        _ ≤ ν * ν * S := by gcongr
        _ = ν ^ 2 * S := by ring)
    (by
      rw [hRr]
      have hl : c₁ * Real.log ν ≤ ν ^ 2 := by
        calc c₁ * Real.log ν ≤ ν * ν := mul_le_mul hνc₁ (log_le_self' hν0) hlogν.le hν0.le
          _ = ν ^ 2 := by ring
      calc c₁ * (ν ^ 2 * S) ^ 2 * Real.log ν = (c₁ * Real.log ν) * ν ^ 4 * (S : ℝ) ^ 2 := by ring
        _ ≤ ν ^ 2 * ν ^ 4 * Δ := by gcongr
        _ = ν ^ 6 * Δ := by ring)
    (by
      calc (D : ℝ) * (ν ^ 2 * S) ^ 2 ≤ Δ / (ν * (S : ℝ) ^ 2) * (ν ^ 2 * S) ^ 2 :=
            mul_le_mul_of_nonneg_right hDle (by positivity)
        _ = ν ^ 3 * Δ := by field_simp
        _ ≤ ν ^ 6 * Δ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hν1 (by norm_num))
            hΔ0.le)
    (growth61V hΔ0.le hν3 hSR1 hlS h2lS hcW hνcW hlKK hνK hlogL hA₀le hA₁le hDle hlog1R
      hlog1R0)
    (by
      rw [hRr, hLcard]
      push_cast
      have hr1 : (0 : ℝ) < ((r : ℝ) + 1) ^ (m + r) := by positivity
      rw [← mul_le_mul_iff_of_pos_left hr1]
      have hx₀ : Δ / (((d0 : ℝ) + 1) * ν * lb) ≤ (a₀ : ℝ) + 1 := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hA₀lt.le (by positivity : (0 : ℝ) ≤ ν * lb)
        have e1 : ((A₀ : ℝ) + 1) ≤ ((a₀ : ℝ) + 1) * ((d0 : ℝ) + 1) := by exact_mod_cast ha₀A
        rw [div_mul_cancel₀ _ (by positivity)] at this
        calc Δ ≤ ((A₀ : ℝ) + 1) * (ν * lb) := this
          _ ≤ ((a₀ : ℝ) + 1) * ((d0 : ℝ) + 1) * (ν * lb) := by gcongr
          _ = ((a₀ : ℝ) + 1) * ((d0 + 1) * ν * lb) := by ring
      have hx₁ : Δ / (((d1 : ℝ) + 1) * ν * S) ≤ (a₁ : ℝ) + 1 := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hA₁lt.le (by positivity : (0 : ℝ) ≤ ν * S)
        have e1 : ((A₁ : ℝ) + 1) ≤ ((a₁ : ℝ) + 1) * ((d1 : ℝ) + 1) := by exact_mod_cast ha₁A
        rw [div_mul_cancel₀ _ (by positivity)] at this
        calc Δ ≤ ((A₁ : ℝ) + 1) * (ν * S) := this
          _ ≤ ((a₁ : ℝ) + 1) * ((d1 : ℝ) + 1) * (ν * S) := by gcongr
          _ = ((a₁ : ℝ) + 1) * ((d1 + 1) * ν * S) := by ring
      have hsg := siegel61 (m := m + r) (x₀ := (a₀ : ℝ) + 1) (x₁ := (a₁ : ℝ) + 1)
        (x₂ := ((r : ℝ) + 1) * ((D2 : ℝ) + 1)) hΔ0 hν1 hSR1 hlb1 hlogν hc₂' hdq heκ hΔq
        hx₀ hx₁ hDlt hCK
      have hsg' : c₂' * (ν ^ 6 * Δ) ^ (n + 1) ≤ ((a₀ : ℝ) + 1) ^ d0 * ((a₁ : ℝ) + 1) ^ d1 *
          (((r : ℝ) + 1) ^ (m + r) * ((D2 : ℝ) + 1) ^ (m + r)) * (Δ / ν) * (ν ^ 2 * S) ^ κ *
            Real.log ν ^ n := by
        rw [← mul_pow]; exact hsg
      calc ((r : ℝ) + 1) ^ (m + r) * (c₂ * (ν ^ 6 * Δ) ^ (n + 1)) =
            c₂' * (ν ^ 6 * Δ) ^ (n + 1) := by rw [hc₂'def]; ring
        _ ≤ _ := hsg'
        _ = _ := by ring)
  -- Lemma U
  have hc₀ν : c₀ * (S : ℝ) ≤ ν ^ 2 * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0.le
    calc c₀ ≤ ν := hνc₀
      _ = ν * 1 := (mul_one _).symm
      _ ≤ ν * ν := mul_le_mul_of_nonneg_left hν1 hν0.le
      _ = ν ^ 2 := by ring
  have hlogT : Real.log ((T : ℝ) + 2) ≤ Kt * lS := by
    have h1 : (T : ℝ) + 2 ≤ 4 * Δ := by
      have : Δ / lS ≤ Δ := div_le_self hΔ0.le hlS
      linarith only [hTle, this, hΔ1]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hΔ0.ne'] at h2
    have hl4 : Real.log 4 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    rw [hKtdef]; nlinarith only [h2, hl4, hlΔ, hlS, hKe]
  have hbud := budget61 hΔ1 hν1 hS3R hlS h2lS hΔS (by linarith only [hc₀1])
    (by rw [hKtdef]; linarith only [hKe]) hνbud hlL1 hA₀le (log_succ_le_two_log hS3)
    (Real.log_nonneg (by linarith only [hSR1])) (Nat.cast_nonneg _) hA₁le hDle hTle.le
    (Nat.cast_nonneg _) hlogT (Real.log_nonneg (by
      linarith only [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]))
  have hVan := hLU D L μs p S T A₀ A₁ (Δ / ν) (ν ^ 6 * Δ) (by omega) (by positivity)
    (fun l i => (hαi l i).trans ha₀A') (fun l i => (hβi l i).trans ha₁A') hpB
    (fun z hz hzr => hsm z hz (hzr.trans hc₀ν)) (by
      have := hbud; linarith only [this])
  -- conclusions
  refine ⟨D, L, μs, p, fun l => ?_, fun l => ?_, ?_, ?_, fun h hh => ?_⟩
  · calc ((∑ i, (μs l).α i : ℕ) : ℝ) ≤ A₀ := by exact_mod_cast hαsum l
      _ ≤ Δ / (ν * lb) := hA₀lb
      _ ≤ Δ / lb := div_le_div_of_nonneg_left hΔ0.le (by positivity)
          (le_mul_of_one_le_left (by positivity) hν1)
  · calc ((∑ i, (μs l).β i : ℕ) : ℝ) ≤ A₁ := by exact_mod_cast hβsum l
      _ ≤ Δ / (ν * S) := hA₁le
      _ ≤ Δ / S := div_le_div_of_nonneg_left hΔ0.le hS0 (le_mul_of_one_le_left hS0.le hν1)
  · exact hDle.trans (div_le_div_of_nonneg_left hΔ0.le (by positivity)
      (le_mul_of_one_le_left (by positivity) hν1))
  · exact exists_PsiV_ne_zero Ls M μs (fun l j => rfl)
      ((monoFamV_rexp_injective d0 d1 m r a₀ a₁ D2).comp eqv.symm.injective) p hp0
  · have hv := hVan h hh
    rw [hDw, hDy] at hv
    intro w hw k hk
    exact hv w hw k (lt_of_lt_of_le hk hTge)

/-- **W88 Prop. 6.1 for the class `𝒞`** (with `a = b = 1`): `prop61V_b` with `b = 1`. -/
theorem prop61V (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (hg : ∀ k, IsAlgebraic ℚ (Ls k).g₂ ∧ IsAlgebraic ℚ (Ls k).g₃) (hM : AlgMat M)
    (V W : Submodule ℂ (TanV d0 d1 m r)) (hWV : W ≤ V) (hW : RatSubV W) (hVf : V ⊓ fibreV = ⊥)
    (hn : finrank ℂ V < d0 + d1 + m + r) {μ : ℕ} (y : Fin μ → TanV d0 d1 m r)
    (hyV : ∀ j, y j ∈ V) (hyL : ∀ j, y j ∈ LamV Ls M) {κ : ℕ} (ω : Fin κ → TanV d0 d1 m r)
    (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ PerV Ls M) (hω : LinearIndependent ℤ ω)
    (hNR : d1 + 2 * d0 + κ ≤ 2 * finrank ℂ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ S₀ : ℕ, ∀ S : ℕ, S₀ ≤ S →
      ∃ (D L : ℕ) (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ),
        (∀ l, ((∑ i, (μs l).α i : ℕ) : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) d0
          (d0 + d1 + m + r - finrank ℂ V) S / Real.log S) ∧
        (∀ l, ((∑ i, (μs l).β i : ℕ) : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) d0
          (d0 + d1 + m + r - finrank ℂ V) S / S) ∧
        (D : ℝ) ≤ delta61 C (d1 + 2 * (m + r) - κ) d0 (d0 + d1 + m + r - finrank ℂ V) S /
          (S : ℝ) ^ 2 ∧
        (∃ x, PsiV Ls M μs p x ≠ 0) ∧
        ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
          VanishAlong (PsiV Ls M μs p) W
            (delta61 C (d1 + 2 * (m + r) - κ) d0 (d0 + d1 + m + r - finrank ℂ V) S / Real.log S)
            (∑ j, h j • y j) := by
  simpa only [one_mul, pow_one] using
    prop61V_b 1 le_rfl Ls M hg hM V W hWV hW hVf hn y hyV hyL ω hωV hωP hω hNR

end LSG.AuxV
