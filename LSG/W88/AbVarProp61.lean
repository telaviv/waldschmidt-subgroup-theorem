/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.LemmaUMain
import LSG.AuxFunA.PropG
import LSG.W88.Prop61

/-!
# A5.6: W88 Prop. 6.1 under (NR) on `G_a^{d₀} × G_m^{d₁} × ∏ B_k` (`STAGE_A5.md` §3)

**`prop61A`** is `LSG.W88.prop61_b` for a family of abelian blocks with analytic packages `An` and Taylor packages
`Tay`. With `G = Σ g_k`, `n = dim V < d₀ + d₁ + G`, `q = d₀ + d₁ + G − n`, `e = d₁ + 2G − κ`, (NR)
`d₁ + 2d₀ + κ ≤ 2n` and `Δ^q = C S^e (log S)^{b d₀}` (`delta61`), there is `P = Σ_l p_l M_l` (distinct monomials,
`G_a`-degree `≤ Δ/log^b S`, `G_m`-degree `≤ Δ/S`, block degree `D ≤ Δ/S²`) with `Ψ ≢ 0`, vanishing along `W` to
order `≥ Δ/log S` at every `Σ h_j y_j`, `0 ≤ h_j ≤ S`.

Inputs (the arithmetic data and the periods are produced in A5.7):
* `Dt : LUDataA ι An μ τ` with `Dt.y` the generators and `span Dt.w = W`;
* `ℂ`-independent periods `ω_i ∈ V ∩ PerL` (under toric injectivity: `linIndep_of_torInj`).

Proof: the parameter chase of `prop61_b` with `prop21A_deg`, `lemmaU_A` and `exists_PsiA_ne_zero`. Monomials
(`monoFamA`): `a^α (e^b)^β Π_k θ_{k,i₀}^{D − Σ_j a_{kj}} Π_j θ_{k,is j}^{a_{kj}}` with `a_{kj} ≤ D'`, `D = (G + 1) D'`,
so there are `(D' + 1)^G` block parts.
-/

open Complex Finset Module LSG.Aux LSG.AuxA LSG.MEB

noncomputable section

namespace LSG.W88

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- The monomial family of Prop. 6.1. -/
def monoFamA (d₀ d₁ : ℕ) (B : Fin m → AbBlock) (a₀ a₁ D' : ℕ)
    (x : (Fin d₀ → Fin (a₀ + 1)) × (Fin d₁ → Fin (a₁ + 1)) × (∀ k, Fin (B k).g → Fin (D' + 1))) :
    MonoA d₀ d₁ B ((∑ k, (B k).g + 1) * D') where
  α := fun i => x.1 i
  β := fun i => x.2.1 i
  γ := fun k => Fin.cons ((∑ k, (B k).g + 1) * D' - ∑ j, (x.2.2 k j : ℕ)) fun j => (x.2.2 k j : ℕ)
  hγ := fun k => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have h1 : ∑ j, (x.2.2 k j : ℕ) ≤ (B k).g * D' := by
      calc ∑ j, (x.2.2 k j : ℕ) ≤ ∑ _j : Fin (B k).g, D' :=
            sum_le_sum fun j _ => Nat.lt_succ_iff.mp (x.2.2 k j).isLt
        _ = (B k).g * D' := by simp
    have h2 : (B k).g ≤ ∑ k, (B k).g := single_le_sum (f := fun k => (B k).g) (fun _ _ => Nat.zero_le _)
      (mem_univ k)
    have h3 : (B k).g * D' ≤ (∑ k, (B k).g + 1) * D' := Nat.mul_le_mul_right _ (by omega)
    omega

lemma monoFamA_rexp_injective (d₀ d₁ : ℕ) (B : Fin m → AbBlock) (a₀ a₁ D' : ℕ) :
    Function.Injective fun x => (monoFamA d₀ d₁ B a₀ a₁ D' x).rexp := by
  intro x x' h
  have h' := fun v => congrFun h v
  obtain ⟨α, β, a⟩ := x
  obtain ⟨α', β', a'⟩ := x'
  simp only [Prod.mk.injEq]
  refine ⟨funext fun i => Fin.ext ?_, funext fun i => Fin.ext ?_, funext fun k => funext fun j => Fin.ext ?_⟩
  · simpa [MonoA.rexp, monoFamA] using h' (.inl i)
  · simpa [MonoA.rexp, monoFamA] using h' (.inr (.inl i))
  · simpa [MonoA.rexp, monoFamA] using h' (.inr (.inr ⟨k, j⟩))

set_option maxHeartbeats 4000000 in
-- the parameter chase of `prop61_b`
/-- **W88 Prop. 6.1 under (NR)** for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`, with `a = 1` and any `b ≥ 1`. -/
theorem prop61A (b : ℕ) (hb : 1 ≤ b) {K : Type*} [Field K] [NumberField K] {ι : K →+* ℂ}
    (An : ∀ k, AbBlockAn (B k)) (Tay : ∀ k, AbBlockTay (B k) ι)
    (V W : Submodule ℂ (MEB.Tan d₀ d₁ B)) (hWV : W ≤ V) (hn : finrank ℂ V < d₀ + d₁ + ∑ k, (B k).g)
    {μ τ : ℕ} (Dt : LUDataA ι An μ τ) (hyV : ∀ j, Dt.y j ∈ V)
    (hW : Submodule.span ℂ (Set.range Dt.w) = W) {κ : ℕ} (ω : Fin κ → MEB.Tan d₀ d₁ B)
    (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ PerL d₀ d₁ B (latF An)) (hω : LinearIndependent ℂ ω)
    (hNR : d₁ + 2 * d₀ + κ ≤ 2 * finrank ℂ V) :
    ∃ C : ℝ, 0 < C ∧ ∃ S₀ : ℕ, ∀ S : ℕ, S₀ ≤ S →
      ∃ (D L : ℕ) (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ),
        (∀ l, ((∑ i, (μs l).α i : ℕ) : ℝ) ≤
          delta61 C (d₁ + 2 * ∑ k, (B k).g - κ) (b * d₀) (d₀ + d₁ + ∑ k, (B k).g - finrank ℂ V) S /
            Real.log S ^ b) ∧
        (∀ l, ((∑ i, (μs l).β i : ℕ) : ℝ) ≤
          delta61 C (d₁ + 2 * ∑ k, (B k).g - κ) (b * d₀) (d₀ + d₁ + ∑ k, (B k).g - finrank ℂ V) S / S) ∧
        (D : ℝ) ≤ delta61 C (d₁ + 2 * ∑ k, (B k).g - κ) (b * d₀) (d₀ + d₁ + ∑ k, (B k).g - finrank ℂ V) S /
          (S : ℝ) ^ 2 ∧
        (∃ x, PsiA μs p x ≠ 0) ∧
        ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
          VanishAlong (PsiA μs p) W
            (delta61 C (d₁ + 2 * ∑ k, (B k).g - κ) (b * d₀) (d₀ + d₁ + ∑ k, (B k).g - finrank ℂ V) S /
              Real.log S)
            (∑ j, h j • Dt.y j) := by
  classical
  set G := ∑ k, (B k).g with hGdef
  set n := finrank ℂ V with hndef
  set q := d₀ + d₁ + G - n with hqdef
  set e := d₁ + 2 * G - κ with hedef
  have hq1 : 1 ≤ q := by omega
  have he : 2 * q ≤ e := by omega
  have heκ : e + κ = d₁ + 2 * G := by omega
  have hdq : d₀ + d₁ + G = n + q := by omega
  -- data and constants
  have hwV : ∀ r, Dt.w r ∈ V := fun r => hWV (hW ▸ Submodule.subset_span ⟨r, rfl⟩)
  obtain ⟨c₀, hc₀1, hLU⟩ := lemmaU_A An Tay V Dt hyV hwV
  obtain ⟨c₁, c₂, cW, hc₁, hc₂, hcW, hS21⟩ := prop21A_deg An V hndef.symm ω hωV hωP hω
  set c₂' : ℝ := c₂ * ((G : ℝ) + 1) ^ G with hc₂'
  have hc₂'0 : 0 ≤ c₂' := by positivity
  set Ke : ℝ := ((e + b * d₀ + 1 : ℕ) : ℝ) / q with hKedef
  have hKe : 0 ≤ Ke := by positivity
  set Kt : ℝ := 2 + Ke with hKtdef
  set ν : ℝ := 3 + c₁ + c₀ + 16 * m * cW + c₀ * (9 + 3 * Kt) with hνdef
  have hν3 : 3 ≤ ν := by rw [hνdef]; nlinarith
  have hν1 : 1 ≤ ν := by linarith
  have hνc₁ : c₁ ≤ ν := by rw [hνdef]; nlinarith
  have hνc₀ : c₀ ≤ ν := by rw [hνdef]; nlinarith
  have hνcW : 16 * m * cW ≤ ν := by rw [hνdef]; nlinarith
  have hνbud : c₀ * (9 + 3 * Kt) ≤ ν := by rw [hνdef]; nlinarith
  have hlogν : 0 < Real.log ν := Real.log_pos (by linarith)
  set Kν : ℝ := ν ^ (2 * κ) * Real.log ν ^ n /
    (((d₀ : ℝ) + 1) ^ d₀ * ((d₁ : ℝ) + 1) ^ d₁ * ν ^ (d₀ + d₁ + G + 1)) with hKνdef
  have hKν : 0 < Kν := by positivity
  set C : ℝ := max 1 (c₂' * ν ^ (6 * (n + 1)) / Kν) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCK : c₂' * ν ^ (6 * (n + 1)) ≤ C * Kν := by
    have := le_max_right 1 (c₂' * ν ^ (6 * (n + 1)) / Kν)
    rw [div_le_iff₀ hKν] at this; exact this
  -- the threshold `S₀`
  set S₀ : ℕ := ⌈max (max 3 C) (max (2 * ν ^ 3) (((d₀ + d₁ + G + 1 : ℕ) : ℝ) * Kt))⌉₊ with hS₀def
  refine ⟨C, by positivity, S₀, fun S hS => ?_⟩
  have hS₀S : max (max 3 C) (max (2 * ν ^ 3) (((d₀ + d₁ + G + 1 : ℕ) : ℝ) * Kt)) ≤ (S : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hS)
  have hS3R : (3 : ℝ) ≤ S := (le_max_left _ _).trans ((le_max_left _ _).trans hS₀S)
  have hS3 : 3 ≤ S := by exact_mod_cast hS3R
  have hSC : C ≤ S := (le_max_right _ _).trans ((le_max_left _ _).trans hS₀S)
  have hSν : 2 * ν ^ 3 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans hS₀S)
  have hSK0 : ((d₀ + d₁ + G + 1 : ℕ) : ℝ) * Kt ≤ S :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hS₀S)
  have hSK : ((d₀ : ℝ) + d₁ + G + 1) * Kt ≤ S := by push_cast at hSK0; exact hSK0
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
  set Δ := delta61 C e (b * d₀) q S with hΔdef
  have hΔS : (S : ℝ) ^ 2 ≤ Δ := sq_le_delta hC1 hq1 he hS3
  have hΔ1 : 1 ≤ Δ := le_trans (by nlinarith only [hS3R]) hΔS
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  have hlΔ : Real.log Δ ≤ Ke * lS := log_delta_le hC1 hSC hq1 he hS3
  have hΔq : Δ ^ q = C * (S : ℝ) ^ e * lb ^ d₀ := by
    rw [hlbdef, ← pow_mul]; exact delta_pow (by linarith only [hC1]) hq1
  -- the parameters
  have hG1 : (1 : ℝ) ≤ (G : ℝ) + 1 := by linarith [(Nat.cast_nonneg G : (0 : ℝ) ≤ G)]
  set A₀ : ℕ := ⌊Δ / (ν * lb)⌋₊ with hA₀def
  set A₁ : ℕ := ⌊Δ / (ν * S)⌋₊ with hA₁def
  set D' : ℕ := ⌊Δ / (ν * ((G : ℝ) + 1) * (S : ℝ) ^ 2)⌋₊ with hD'def
  set D : ℕ := (G + 1) * D' with hDdef
  set a₀ := A₀ / (d₀ + 1) with ha₀def
  set a₁ := A₁ / (d₁ + 1) with ha₁def
  set T : ℕ := ⌈Δ / lS⌉₊ with hTdef
  have hA₀lb : (A₀ : ℝ) ≤ Δ / (ν * lb) := Nat.floor_le (by positivity)
  have hA₀le : (A₀ : ℝ) ≤ Δ / (ν * lS) := hA₀lb.trans
    (div_le_div_of_nonneg_left hΔ0.le (by positivity) (by nlinarith only [hlb, hν1, hlS]))
  have hA₁le : (A₁ : ℝ) ≤ Δ / (ν * S) := Nat.floor_le (by positivity)
  have hD'le : (D' : ℝ) ≤ Δ / (ν * ((G : ℝ) + 1) * (S : ℝ) ^ 2) := Nat.floor_le (by positivity)
  have hDle : (D : ℝ) ≤ Δ / (ν * (S : ℝ) ^ 2) := by
    rw [hDdef]; push_cast
    calc ((G : ℝ) + 1) * D' ≤ ((G : ℝ) + 1) * (Δ / (ν * ((G : ℝ) + 1) * (S : ℝ) ^ 2)) := by gcongr
      _ = Δ / (ν * (S : ℝ) ^ 2) := by field_simp
  have hA₀lt : Δ / (ν * lb) < A₀ + 1 := Nat.lt_floor_add_one _
  have hA₁lt : Δ / (ν * S) < A₁ + 1 := Nat.lt_floor_add_one _
  have hD'lt : Δ / (ν * ((G : ℝ) + 1) * (S : ℝ) ^ 2) < D' + 1 := Nat.lt_floor_add_one _
  have ha₀A : A₀ + 1 ≤ (a₀ + 1) * (d₀ + 1) := by
    have := Nat.lt_div_mul_add (a := A₀) (b := d₀ + 1) (by omega); rw [ha₀def]; linarith
  have ha₁A : A₁ + 1 ≤ (a₁ + 1) * (d₁ + 1) := by
    have := Nat.lt_div_mul_add (a := A₁) (b := d₁ + 1) (by omega); rw [ha₁def]; linarith
  have ha₀le : d₀ * a₀ ≤ A₀ := by
    have := Nat.div_mul_le_self A₀ (d₀ + 1); rw [ha₀def]; nlinarith
  have ha₁le : d₁ * a₁ ≤ A₁ := by
    have := Nat.div_mul_le_self A₁ (d₁ + 1); rw [ha₁def]; nlinarith
  have ha₀A' : a₀ ≤ A₀ := Nat.div_le_self _ _
  have ha₁A' : a₁ ≤ A₁ := Nat.div_le_self _ _
  have hTle : (T : ℝ) < Δ / lS + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTge : Δ / lS ≤ T := Nat.le_ceil _
  -- the monomials
  let Ix := (Fin d₀ → Fin (a₀ + 1)) × (Fin d₁ → Fin (a₁ + 1)) × (∀ k, Fin (B k).g → Fin (D' + 1))
  set L := Fintype.card Ix with hLdef
  let eqv := Fintype.equivFin Ix
  set μs : Fin L → MonoA d₀ d₁ B D := fun l => monoFamA d₀ d₁ B a₀ a₁ D' (eqv.symm l) with hμsdef
  have hLcard : L = (a₀ + 1) ^ d₀ * (a₁ + 1) ^ d₁ * (D' + 1) ^ G := by
    simp only [hLdef, Ix, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_pi]
    rw [prod_pow_eq_pow_sum, mul_assoc]
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
  have hD'Δ : (D' : ℝ) ≤ Δ := hD'le.trans (div_le_self hΔ0.le (by
    have : (1 : ℝ) ≤ ν * ((G : ℝ) + 1) := one_le_mul_of_one_le_of_one_le hν1 hG1
    nlinarith only [this, hSR1]))
  have hL2 : ((L : ℝ) + 1) ≤ (2 * Δ) ^ (d₀ + d₁ + G + 1) := by
    have h1 : (L : ℝ) ≤ (2 * Δ) ^ (d₀ + d₁ + G) := by
      rw [hLcard, pow_add, pow_add]; push_cast
      have e0 : ((a₀ : ℝ) + 1) ≤ 2 * Δ := hfac _ ((by exact_mod_cast ha₀A' : (a₀ : ℝ) ≤ A₀).trans hA₀Δ)
      have e1 : ((a₁ : ℝ) + 1) ≤ 2 * Δ := hfac _ ((by exact_mod_cast ha₁A' : (a₁ : ℝ) ≤ A₁).trans hA₁Δ)
      have e2 : ((D' : ℝ) + 1) ≤ 2 * Δ := hfac _ hD'Δ
      gcongr
    have h2 : (1 : ℝ) ≤ (2 * Δ) ^ (d₀ + d₁ + G) := one_le_pow₀ (by linarith only [hΔ1])
    calc (L : ℝ) + 1 ≤ 2 * (2 * Δ) ^ (d₀ + d₁ + G) := by linarith only [h1, h2]
      _ ≤ (2 * Δ) * (2 * Δ) ^ (d₀ + d₁ + G) :=
          mul_le_mul_of_nonneg_right (by linarith only [hΔ1]) (by positivity)
      _ = (2 * Δ) ^ (d₀ + d₁ + G + 1) := by ring
  have hlL1 : Real.log ((L : ℝ) + 1) ≤ Δ := by
    have h1 := Real.log_le_log (by positivity) hL2
    rw [Real.log_pow, Real.log_mul (by norm_num) hΔ0.ne'] at h1
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith only [this]
    have h3 : Real.log 2 + Real.log Δ ≤ Kt * lS := by
      rw [hKtdef]; nlinarith only [hl2, hlΔ, hlS, hKe]
    have h4 : ((d₀ + d₁ + G + 1 : ℕ) : ℝ) * (Kt * lS) ≤ (S : ℝ) ^ 2 := by
      push_cast
      calc ((d₀ : ℝ) + d₁ + G + 1) * (Kt * lS) = (((d₀ : ℝ) + d₁ + G + 1) * Kt) * lS := by ring
        _ ≤ S * S := mul_le_mul hSK hlSS' (by linarith only [hlS]) hS0.le
        _ = (S : ℝ) ^ 2 := by ring
    calc Real.log ((L : ℝ) + 1) ≤ ((d₀ + d₁ + G + 1 : ℕ) : ℝ) * (Real.log 2 + Real.log Δ) := h1
      _ ≤ ((d₀ + d₁ + G + 1 : ℕ) : ℝ) * (Kt * lS) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ ≤ (S : ℝ) ^ 2 := h4
      _ ≤ Δ := hΔS
  -- W83 Prop. 2.1 (`prop21A_deg`)
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
  have hsieg : c₂' * (ν ^ 6 * Δ) ^ (n + 1) ≤ ((a₀ : ℝ) + 1) ^ d₀ * ((a₁ : ℝ) + 1) ^ d₁ *
      (((G : ℝ) + 1) * ((D' : ℝ) + 1)) ^ G * (Δ / ν) * (ν ^ 2 * S) ^ κ * Real.log ν ^ n := by
    refine siegel61 hΔ0 hν1 hSR1 hlb1 hlogν hc₂'0 hdq heκ hΔq ?_ ?_ ?_ hCK
    · rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hA₀lt.le (by positivity : (0 : ℝ) ≤ ν * lb)
      have e1 : ((A₀ : ℝ) + 1) ≤ ((a₀ : ℝ) + 1) * ((d₀ : ℝ) + 1) := by exact_mod_cast ha₀A
      rw [div_mul_cancel₀ _ (by positivity)] at this
      calc Δ ≤ ((A₀ : ℝ) + 1) * (ν * lb) := this
        _ ≤ ((a₀ : ℝ) + 1) * ((d₀ : ℝ) + 1) * (ν * lb) := by gcongr
        _ = ((a₀ : ℝ) + 1) * ((d₀ + 1) * ν * lb) := by ring
    · rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hA₁lt.le (by positivity : (0 : ℝ) ≤ ν * S)
      have e1 : ((A₁ : ℝ) + 1) ≤ ((a₁ : ℝ) + 1) * ((d₁ : ℝ) + 1) := by exact_mod_cast ha₁A
      rw [div_mul_cancel₀ _ (by positivity)] at this
      calc Δ ≤ ((A₁ : ℝ) + 1) * (ν * S) := this
        _ ≤ ((a₁ : ℝ) + 1) * ((d₁ : ℝ) + 1) * (ν * S) := by gcongr
        _ = ((a₁ : ℝ) + 1) * ((d₁ + 1) * ν * S) := by ring
    · have h := hD'lt.le
      rw [div_le_iff₀ (by positivity)] at h ⊢
      calc Δ ≤ ((D' : ℝ) + 1) * (ν * ((G : ℝ) + 1) * (S : ℝ) ^ 2) := h
        _ = ((G : ℝ) + 1) * ((D' : ℝ) + 1) * (ν * (S : ℝ) ^ 2) := by ring
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
    (growth61 hΔ0.le hν3 hSR1 hlS hcW hνcW hlogL hA₀le (Nat.cast_nonneg _) hA₁le
      (Nat.cast_nonneg _) hDle (Nat.cast_nonneg _) hlog1R hlog1R0)
    (by
      rw [hRr, hLcard]
      push_cast
      have hGp : (0 : ℝ) < ((G : ℝ) + 1) ^ G := by positivity
      have e : c₂' * (ν ^ 6 * Δ) ^ (n + 1) = ((G : ℝ) + 1) ^ G * (c₂ * (ν ^ 6 * Δ) ^ (n + 1)) := by
        rw [hc₂']; ring
      rw [e, mul_pow ((G : ℝ) + 1) ((D' : ℝ) + 1) G] at hsieg
      have : ((G : ℝ) + 1) ^ G * (c₂ * (ν ^ 6 * Δ) ^ (n + 1)) ≤ ((G : ℝ) + 1) ^ G *
          (((a₀ : ℝ) + 1) ^ d₀ * ((a₁ : ℝ) + 1) ^ d₁ * ((D' : ℝ) + 1) ^ G * (Δ / ν) * (ν ^ 2 * S) ^ κ *
            Real.log ν ^ n) := by
        refine hsieg.trans (le_of_eq ?_); ring
      exact le_of_mul_le_mul_left this hGp)
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
    (Nat.cast_nonneg _) hlogT (Real.log_nonneg (by linarith only [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]))
  have hVan := hLU D L μs p S T A₀ A₁ (Δ / ν) (ν ^ 6 * Δ) (by omega) (by positivity)
    (fun l i => (hαi l i).trans ha₀A') (fun l i => (hβi l i).trans ha₁A') hpB
    (fun z hz hzr => hsm z hz (hzr.trans hc₀ν)) (by
      have := hbud; unfold budU; push_cast at this ⊢; linarith only [this])
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
  · exact exists_PsiA_ne_zero μs
      ((monoFamA_rexp_injective d₀ d₁ B a₀ a₁ D').comp eqv.symm.injective) p hp0
  · have hv := hVan h hh
    rw [hW] at hv
    intro w hw k hk
    exact hv w hw k (lt_of_lt_of_le hk hTge)

end LSG.W88
