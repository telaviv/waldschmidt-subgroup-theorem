/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.LemmaUFibC
import LSG.AuxFun.LemmaUMain

/-!
# Lemma U for the class `𝒞` at every point of `Y(S)` (Stage 5, phase 2)

**`LSG.AuxV.lemmaU_coreV`**: the statement of `LSG.Aux.lemmaU_core` for `G ∈ 𝒞` (monomials
`MonoV`, data `LUDataV`): if `Ψ = Σ_l p_l M_l` satisfies `|Ψ| ≤ e^{−U}` on `V ∩ B(0, c₀ S)` and
`c₀ (B + log(L+1) + (A₀+1) log(S+1) + (A₁+1) S + (D+1) S² + (T+1) log(T+2)) ≤ U`, then `Ψ` vanishes
to order `≥ T` along `W` at every `Σ h_j y_j`, `0 ≤ h_j ≤ S`.

Proof: the abelian set-up of `lemmaU_core` on the base; the fibre constants (`exists_fib_consts`)
and the fibre factors (`ks_fibFac`) of size `e^{c S²}`; `lemmaU_dirV` per direction, whose
Liouville hypothesis follows from `lemmaU_arith` applied with `U − E`, `E = c_E ((D+1)S² +
(T+1)log(T+2))` (`dominate`, `fib_extra_le`).
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 LSG.W88.Vec PeriodPair NumberField
open LSG.Aux (ellW ellV IsRep zh wpP wpQ xiV lawk Fct Afac efac Nfac AE eE KS Sz ks_wpSeries
  exists_alg_points_S exists_wden sz_lawk exists_lawk_bound exists_chart exists_xi_bound
  isRep_lawk isRep_half sz_natComb sz_expComb lemmaU_arith iteratedDeriv_line_eq_zero_of_span)
open scoped ContDiff

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}
variable {K : Type*} [Field K] [NumberField K]

/-- The extra fibre factor of the Liouville quantity is `≤ e^E`. -/
lemma fib_extra_le {deg r D NF k T : ℕ} {S CF cA cE' : ℝ} {e : ℕ} (hS : 1 ≤ S) (hk : k < T)
    (hcA : 0 ≤ cA) (hcE : 0 ≤ cE') (hCF : 0 ≤ CF) (he : (e : ℝ) ≤ Real.exp (cE' * S ^ 2))
    (he1 : 1 ≤ e) :
    ((((e ^ NF : ℕ) : ℝ)) ^ (r * D) * 2 ^ (r * D) *
        ((CF + 1) * (2 ^ NF * Real.exp (cA * S ^ 2) ^ NF)) ^ (r * D) * 2 ^ k) ^ deg ≤
      Real.exp (deg * (r * (NF * (cA + cE') + Real.log (CF + 1) + NF + 1) + 2) *
        ((D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2))) := by
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have he1' : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hlCF : 0 ≤ Real.log (CF + 1) := Real.log_nonneg (by linarith)
  set N := r * D
  have X1 : (((e ^ NF : ℕ) : ℝ)) ≤ Real.exp (NF * cE' * S ^ 2) := by
    push_cast
    calc (e : ℝ) ^ NF ≤ Real.exp (cE' * S ^ 2) ^ NF := pow_le_pow_left₀ (by positivity) he NF
      _ = Real.exp (NF * cE' * S ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have X2 : (CF + 1) * (2 ^ NF * Real.exp (cA * S ^ 2) ^ NF) ≤
      Real.exp (Real.log (CF + 1) + NF + NF * cA * S ^ 2) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by linarith)]
    have : (2 : ℝ) ^ NF * Real.exp (cA * S ^ 2) ^ NF ≤
        Real.exp NF * Real.exp (NF * cA * S ^ 2) := by
      rw [← mul_pow]
      calc (2 * Real.exp (cA * S ^ 2)) ^ NF ≤ (Real.exp 1 * Real.exp (cA * S ^ 2)) ^ NF := by
            gcongr
        _ = Real.exp NF * Real.exp (NF * cA * S ^ 2) := by
            rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    calc (CF + 1) * (2 ^ NF * Real.exp (cA * S ^ 2) ^ NF) ≤
        (CF + 1) * (Real.exp NF * Real.exp (NF * cA * S ^ 2)) := by gcongr
      _ = _ := by ring
  have X3 : (2 : ℝ) ^ k ≤ Real.exp T := by
    calc (2 : ℝ) ^ k ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ = Real.exp k := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp T := Real.exp_le_exp.mpr (by exact_mod_cast hk.le)
  have X4 : (2 : ℝ) ^ N ≤ Real.exp N := by
    calc (2 : ℝ) ^ N ≤ Real.exp 1 ^ N := pow_le_pow_left₀ (by norm_num) h2 N
      _ = Real.exp N := by rw [← Real.exp_nat_mul]; ring_nf
  set Z := N * (NF * cE' * S ^ 2) + N + N * (Real.log (CF + 1) + NF + NF * cA * S ^ 2) + T
  have hbase : (((e ^ NF : ℕ) : ℝ)) ^ N * 2 ^ N *
      ((CF + 1) * (2 ^ NF * Real.exp (cA * S ^ 2) ^ NF)) ^ N * 2 ^ k ≤ Real.exp Z := by
    have e1 : Real.exp Z = Real.exp (NF * cE' * S ^ 2) ^ N * Real.exp N *
        Real.exp (Real.log (CF + 1) + NF + NF * cA * S ^ 2) ^ N * Real.exp T := by
      simp only [Z]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add]
    rw [e1]
    have h0 : (0 : ℝ) ≤ (CF + 1) * (2 ^ NF * Real.exp (cA * S ^ 2) ^ NF) := by positivity
    gcongr
  have hZ : deg * Z ≤ deg * (r * (NF * (cA + cE') + Real.log (CF + 1) + NF + 1) + 2) *
      ((D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2)) := by
    have hdeg : (0 : ℝ) ≤ deg := Nat.cast_nonneg _
    have hT2 : 1 / 2 ≤ Real.log (T + 2) := by
      have h1 : Real.log 2 ≤ Real.log (T + 2) :=
        Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)])
      have h2' : 1 / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      linarith
    have hT : (T : ℝ) ≤ 2 * ((T + 1) * Real.log (T + 2)) := by
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      nlinarith
    have hN : (N : ℝ) = r * D := by simp [N]
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hNF : (0 : ℝ) ≤ NF := Nat.cast_nonneg NF
    have hlogT : 0 ≤ (T + 1) * Real.log (T + 2) := by positivity
    set c := (r : ℝ) * (NF * (cA + cE') + Real.log (CF + 1) + NF + 1)
    have hc : 0 ≤ c := by positivity
    set L2 := (T + 1) * Real.log (T + 2)
    have h1 : (r : ℝ) * D * (NF * cE' * S ^ 2) + r * D + r * D * (Real.log (CF + 1) + NF +
        NF * cA * S ^ 2) ≤ c * (D * S ^ 2) := by
      rw [← sub_nonneg]
      have e : c * (D * S ^ 2) - ((r : ℝ) * D * (NF * cE' * S ^ 2) + r * D + r * D *
          (Real.log (CF + 1) + NF + NF * cA * S ^ 2)) =
          (r * D * (Real.log (CF + 1) + NF + 1)) * (S ^ 2 - 1) := by simp only [c]; ring
      rw [e]
      exact mul_nonneg (by positivity) (by linarith)
    have hcD : c * (D * S ^ 2) ≤ c * ((D + 1) * S ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc
    have key : Z ≤ c * ((D + 1) * S ^ 2) + 2 * L2 := by
      have hZe : Z = (r : ℝ) * D * (NF * cE' * S ^ 2) + r * D + r * D * (Real.log (CF + 1) + NF +
          NF * cA * S ^ 2) + T := by simp only [Z, hN]
      rw [hZe]; linarith
    have hX0 : 0 ≤ (D + 1) * S ^ 2 := by positivity
    calc (deg : ℝ) * Z ≤ deg * (c * ((D + 1) * S ^ 2) + 2 * L2) :=
          mul_le_mul_of_nonneg_left key hdeg
      _ ≤ deg * (c + 2) * ((D + 1) * S ^ 2 + L2) := by
          rw [← sub_nonneg]
          have e : (deg : ℝ) * (c + 2) * ((D + 1) * S ^ 2 + L2) -
              deg * (c * ((D + 1) * S ^ 2) + 2 * L2) = deg * (c * L2 + 2 * ((D + 1) * S ^ 2)) := by
            ring
          rw [e]; positivity
  calc _ ≤ Real.exp Z ^ deg := pow_le_pow_left₀ (by positivity) hbase deg
    _ = Real.exp (deg * Z) := by rw [← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr hZ

/-- The constants of the fibre factors (index set). -/
abbrev FamF (m r : ℕ) := Fin r ⊕ (Fin r × Fin m) ⊕ Fin m ⊕ Fin m ⊕ Fin m ⊕ (Fin m × Fin 3)

set_option maxHeartbeats 8000000 in -- large proof (many local constants)
/-- **Lemma U for the class `𝒞` at every point of `Y(S)`.** -/
theorem lemmaU_coreV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (ι : K →+* ℂ)
    (V : Submodule ℂ (TanV d0 d1 m r)) {μ τ : ℕ}
    (Dt : LUDataV (d0 := d0) (d1 := d1) Ls M ι μ τ) (hyV : ∀ j, Dt.y j ∈ V)
    (hwV : ∀ q, Dt.w q ∈ V) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (D L : ℕ) (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ)
      (S T A₀ A₁ : ℕ) (B U : ℝ), 1 ≤ S → 0 ≤ B →
      (∀ l i, (μs l).α i ≤ A₀) → (∀ l i, (μs l).β i ≤ A₁) → (∀ l, |(p l : ℝ)| ≤ Real.exp B) →
      (∀ z ∈ V, ‖z‖ ≤ c₀ * S → ‖PsiV Ls M μs p z‖ ≤ Real.exp (-U)) →
      c₀ * (B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S +
        (D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2)) ≤ U →
      ∀ h : Fin μ → ℕ, (∀ j, h j ≤ S) →
        VanishAlong (PsiV Ls M μs p) (Submodule.span ℂ (Set.range Dt.w)) T
          (∑ j, h j • Dt.y j) := by
  classical
  set H := Dt.H with hHdef
  set d := Dt.d with hddef
  have hH : 1 ≤ H := Dt.hH
  have hd : 1 ≤ d := Dt.hd
  have hH0 : 0 < H := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdR
  -- algebraic points
  choose Ak hAk0 hAk using fun k => exists_alg_points_S (Ls k) (Dt.hγ₂ k) (Dt.hγ₃ k)
    (fun j => (Dt.y j).2.2.1 k) (fun j => Dt.X₀ j k) (fun j => Dt.hX₀ j k)
    (fun j => ⟨H, d, hd, Dt.hX₀s j k⟩)
  set Aa := ∑ k, Ak k with hAadef
  have hAa0 : 0 ≤ Aa := sum_nonneg fun k _ => hAk0 k
  have hAkAa : ∀ k, Ak k ≤ Aa := fun k => single_le_sum (fun j _ => hAk0 j) (mem_univ k)
  -- weighted denominators
  choose lk hlk1 hlk₂ hlk₃ using fun k => exists_wden (Dt.γ₂ k) (Dt.γ₃ k)
  set l := ∏ k, lk k with hldef
  have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by
    have := hlk1 k; omega)
  have hint : ∀ n : ℕ, IsIntegral ℤ (n : K) := fun n => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (n : ℤ))
  have hlint : ∀ k, IsIntegral ℤ ((l : K) ^ 4 * Dt.γ₂ k) ∧
      IsIntegral ℤ ((l : K) ^ 6 * Dt.γ₃ k) := by
    intro k
    have hsplit : l = lk k * ∏ j ∈ univ.erase k, lk j :=
      (mul_prod_erase univ lk (mem_univ k)).symm
    set r := ∏ j ∈ univ.erase k, lk j
    rw [hsplit]
    constructor
    · have e : ((lk k * r : ℕ) : K) ^ 4 * Dt.γ₂ k =
          ((r ^ 4 : ℕ) : K) * ((lk k : K) ^ 4 * Dt.γ₂ k) := by push_cast; ring
      rw [e]; exact (hint _).mul (hlk₂ k)
    · have e : ((lk k * r : ℕ) : K) ^ 6 * Dt.γ₃ k =
          ((r ^ 6 : ℕ) : K) * ((lk k : K) ^ 6 * Dt.γ₃ k) := by push_cast; ring
      rw [e]; exact (hint _).mul (hlk₃ k)
  -- sizes of the laws
  have hsz : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (C * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2)
          (lawk κ (Ls k).g₂ (Ls k).g₃ P Q i) := by
    intro k
    obtain ⟨C, hC0, hC⟩ := sz_lawk ι (le_max_left (house (Dt.γ₂ k)) (house (Dt.γ₃ k)))
      (le_max_right _ _) (hlint k).1 (hlint k).2
    exact ⟨C, hC0, fun κ P Q Hp Hq dp dq hP hQ i => by
      have := hC κ P Q Hp Hq dp dq hP hQ i; rwa [Dt.hγ₂ k, Dt.hγ₃ k] at this⟩
  choose Ck hCk0 hCk using hsz
  set Cl := 1 + ∑ k, Ck k with hCldef
  have hCl1 : 1 ≤ Cl := by have := sum_nonneg fun k (_ : k ∈ univ) => hCk0 k; linarith
  have hlaw : ∀ k (κ : Fin 2) (P Q : Fin 3 → ℂ) (Hp Hq : ℝ) (dp dq : ℕ),
      (∀ i, Sz ι Hp dp (P i)) → (∀ i, Sz ι Hq dq (Q i)) → ∀ i,
        Sz ι (Cl * Hp ^ 2 * Hq ^ 2) (l ^ 12 * dp ^ 2 * dq ^ 2)
          (lawk κ (Ls k).g₂ (Ls k).g₃ P Q i) := by
    intro k κ P Q Hp Hq dp dq hP hQ i
    refine (hCk k κ P Q Hp Hq dp dq hP hQ i).mono_le ?_
    have : Ck k ≤ Cl := by
      have := single_le_sum (f := Ck) (fun j _ => hCk0 j) (mem_univ k); linarith
    have h0 : 0 ≤ Hp ^ 2 * Hq ^ 2 := by positivity
    nlinarith
  -- archimedean bound for the laws
  choose C'k hC'k0 hC'k using fun k : Fin m => exists_lawk_bound (max ‖(Ls k).g₂‖ ‖(Ls k).g₃‖)
  set C'l := 1 + ∑ k, C'k k with hC'ldef
  have hC'l1 : 1 ≤ C'l := by have := sum_nonneg fun k (_ : k ∈ univ) => hC'k0 k; linarith
  have hC'kl : ∀ k, C'k k ≤ C'l := fun k => by
    have := single_le_sum (f := C'k) (fun j _ => hC'k0 j) (mem_univ k); linarith
  -- charts and discs
  choose ρ₀ cch hρ₀ hcch hchart using fun k => exists_chart (Ls k)
  choose ρx Mx hρx hρx1 hMx hxi using fun k => exists_xi_bound (Ls k)
  set ρ₁ : ℝ := 1 / (1 + ∑ k, (1 / ρ₀ k + 1 / ρx k)) with hρ₁def
  have hSig : 0 ≤ ∑ k, (1 / ρ₀ k + 1 / ρx k) := sum_nonneg fun k _ => by
    have := hρ₀ k; have := hρx k; positivity
  have hρ₁ : 0 < ρ₁ := by positivity
  have hρ₁le : ∀ k, ρ₁ ≤ ρ₀ k ∧ ρ₁ ≤ ρx k := by
    intro k
    have hk := single_le_sum (f := fun k => 1 / ρ₀ k + 1 / ρx k) (fun j _ => by
      have := hρ₀ j; have := hρx j; positivity) (mem_univ k)
    have h0 := hρ₀ k; have h1 := hρx k
    have i0 : 0 ≤ 1 / ρ₀ k := one_div_nonneg.mpr h0.le
    have i1 : 0 ≤ 1 / ρx k := one_div_nonneg.mpr h1.le
    constructor
    · calc ρ₁ ≤ 1 / (1 / ρ₀ k) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = ρ₀ k := one_div_one_div _
    · calc ρ₁ ≤ 1 / (1 / ρx k) := one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = ρx k := one_div_one_div _
  have hρ₁1 : ρ₁ ≤ 1 := by
    rw [hρ₁def, div_le_one (by positivity)]; linarith
  set Mξ := 1 + ∑ k, Mx k with hMξdef
  have hMξ1 : 1 ≤ Mξ := by
    have := sum_nonneg fun k (_ : k ∈ univ) => (zero_le_one.trans (hMx k)); linarith
  have hMxξ : ∀ k, Mx k ≤ Mξ := fun k => by
    have := single_le_sum (f := Mx) (fun j _ => zero_le_one.trans (hMx j)) (mem_univ k); linarith
  set cc := ∑ k, cch k with hccdef
  have hcc0 : 0 ≤ cc := sum_nonneg fun k _ => hcch k
  have hcchcc : ∀ k, cch k ≤ cc := fun k => single_le_sum (fun j _ => hcch j) (mem_univ k)
  set Y := ∑ j, ‖Dt.y j‖ with hYdef
  have hY0 : 0 ≤ Y := sum_nonneg fun j _ => norm_nonneg _
  set Wn := ∑ r, ‖Dt.w r‖ with hWndef
  have hWn0 : 0 ≤ Wn := sum_nonneg fun r _ => norm_nonneg _
  -- the exponent constants
  set KX : ℝ := Real.log Cl + 2 * Aa + 2 * Real.log H with hKXdef
  set KAE : ℝ := Real.log 144 + Real.log Cl + 2 * KX + 2 * Real.log H with hKAEdef
  set KR : ℝ := Real.log C'l + 2 * KX + 2 * Real.log Mξ + cc * (1 + Y) ^ 2 with hKRdef
  set KeE : ℝ := 36 * Real.log l + 4 * Aa + 6 * Real.log d with hKeEdef
  set cρ : ℝ := (1 + Wn) / ρ₁ with hcρdef
  set KB : ℝ := 1 + Real.log (4 * (1 + 7 * τ * H ^ 2)) / Real.log 2 with hKBdef
  set Kρ : ℝ := 1 + Real.log cρ / Real.log 2 with hKρdef
  set deg : ℕ := Module.finrank ℚ K with hdegdef
  set Ka : ℝ := 1 + Real.log ((μ + 1) * H) / Real.log 2 with hKadef
  set κ1 : ℝ := m * KR + deg * (3 * m * KeE + 3 * m * (1 + KAE)) with hκ1def
  set κ2 : ℝ := deg * (d0 * Real.log d / Real.log 2 + d0 + d0 * Ka) with hκ2def
  set κ3 : ℝ := deg * (d1 * μ * Real.log d + d1 + d1 * μ * Real.log H) with hκ3def
  set κ4 : ℝ := Kρ + deg * (2 * Real.log d / Real.log 2 + 1 + KB) with hκ4def
  set c₀ab : ℝ := 2 + Y + κ1 + κ2 + κ3 + κ4 + 2 * deg with hc₀abdef
  -- the fibre constants
  set cX : ℝ := Real.log Cl + 2 * Aa + 2 * Real.log H + 12 * Real.log l + 2 * Real.log d
    with hcXdef
  have hlogCl' : 0 ≤ Real.log Cl := Real.log_nonneg hCl1
  have hlogl' : 0 ≤ Real.log l := Real.log_nonneg (show (1 : ℝ) ≤ l by exact_mod_cast hl1)
  have hcX : 0 ≤ cX := by positivity
  obtain ⟨cF, hcF0, hcF⟩ := exists_fib_consts Ls M Dt hcX
  set cA : ℝ := cF + cX + (Real.log H + Real.log d) with hcAdef
  have hcA0 : 0 ≤ cA := by positivity
  set cE' : ℝ := Fintype.card (FamF m r) * cA + Real.log d with hcE'def
  have hcE'0 : 0 ≤ cE' := by positivity
  set cE : ℝ := deg * (r * (NF m * (cA + cE') + Real.log (CF m + 1) + NF m + 1) + 2)
    with hcEdef
  have hlogCF : 0 ≤ Real.log (CF m + 1) := Real.log_nonneg (by linarith [CF_nonneg m])
  have hcE0 : 0 ≤ cE := by positivity
  set c₀ : ℝ := c₀ab + cE with hc₀def
  -- nonnegativity of the constants
  have hlogCl : 0 ≤ Real.log Cl := Real.log_nonneg hCl1
  have hlogC'l : 0 ≤ Real.log C'l := Real.log_nonneg hC'l1
  have hlogMξ : 0 ≤ Real.log Mξ := Real.log_nonneg hMξ1
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg (show (1 : ℝ) ≤ l by exact_mod_cast hl1)
  have hKX : 0 ≤ KX := by positivity
  have hKAE : 0 ≤ KAE := by
    have : 0 ≤ Real.log 144 := Real.log_nonneg (by norm_num)
    positivity
  have hKR : 0 ≤ KR := by positivity
  have hKeE : 0 ≤ KeE := by positivity
  have hcρ1 : 1 ≤ cρ := by
    rw [hcρdef, le_div_iff₀ hρ₁]; linarith
  have hB4 : 1 ≤ 4 * (1 + 7 * (τ : ℝ) * H ^ 2) := by
    have : 0 ≤ 7 * (τ : ℝ) * H ^ 2 := by positivity
    linarith
  have hKB : 0 ≤ KB := by have := Real.log_nonneg hB4; positivity
  have hKρ : 0 ≤ Kρ := by have := Real.log_nonneg hcρ1; positivity
  have hμH : 1 ≤ ((μ : ℝ) + 1) * H :=
    one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)]) hH
  have hKa : 0 ≤ Ka := by have := Real.log_nonneg hμH; positivity
  have hκ1 : 0 ≤ κ1 := by positivity
  have hκ2 : 0 ≤ κ2 := by positivity
  have hκ3 : 0 ≤ κ3 := by positivity
  have hκ4 : 0 ≤ κ4 := by positivity
  have hdeg0 : (0 : ℝ) ≤ deg := Nat.cast_nonneg _
  refine ⟨c₀, by rw [hc₀def, hc₀abdef]; linarith, fun D L μs p S T A₀ A₁ B U hS hB hα hβ hp
    hsmall hbud h hh => ?_⟩
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  set t : TanV d0 d1 m r := ∑ j, h j • Dt.y j with htdef
  have ht0' : ∀ i, t.1 i = ∑ j, (h j : ℂ) * (Dt.y j).1 i := by
    intro i; simp [htdef, Prod.fst_sum, Finset.sum_apply, nsmul_eq_mul]
  have ht1' : ∀ i, t.2.1 i = ∑ j, (h j : ℂ) * (Dt.y j).2.1 i := by
    intro i; simp [htdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, nsmul_eq_mul]
  have ht2' : ∀ k, t.2.2.1 k = ∑ j, (h j : ℂ) * (Dt.y j).2.2.1 k := by
    intro k; simp [htdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, nsmul_eq_mul]
  have htn : ‖t‖ ≤ S * Y := by
    refine (norm_sum_le _ _).trans ?_
    rw [hYdef, mul_sum]
    refine sum_le_sum fun j _ => norm_nsmul_le.trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh j) (norm_nonneg _)
  have htk : ∀ k, ‖t.2.2.1 k‖ ≤ S * Y := fun k =>
    ((norm_le_pi_norm _ k).trans ((norm_fst_le _).trans ((norm_snd_le _).trans
      (norm_snd_le _)))).trans htn
  have htV : t ∈ V := V.sum_mem fun j _ => V.smul_of_tower_mem _ (hyV j)
  -- algebraic points `X_k` and their translates `X'_k`
  choose Xk dXk hXk hdXk hdXkle hXks using fun k => hAk k S hS h hh
  set dX := ∏ k, dXk k with hdXdef
  set HX := Real.exp (Aa * S ^ 2) with hHXdef
  have hHX1 : 1 ≤ HX := Real.one_le_exp (by positivity)
  have hdX1 : 1 ≤ dX := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by
    have := hdXk k; omega)
  have hdXle : (dX : ℝ) ≤ HX := by
    rw [hdXdef, hHXdef, Nat.cast_prod, hAadef, sum_mul, Real.exp_sum]
    exact prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) fun k _ => hdXkle k
  have hXs : ∀ k i, Sz ι HX dX (Xk k i) := fun k i =>
    (hXks k i).mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hAkAa k) (by positivity)))
      (dvd_prod_of_mem _ (mem_univ k))
  set E1 : Fin m → Fin 3 → ℂ := fun k => ![℘[Ls k] (zh (Ls k)), 0, 1] with hE1def
  have hE1s : ∀ k i, Sz ι H d (E1 k i) := by
    intro k i
    fin_cases i
    · exact Dt.he₁ k
    · exact (Sz.zero d).mono_le (zero_le_one.trans hH)
    · exact Sz.one.mono hH (one_dvd d)
  have hXrep : ∀ k, IsRep (Ls k) (t.2.2.1 k) (Xk k) := fun k => by rw [ht2']; exact hXk k
  choose κA hκA using fun k => isRep_lawk (Ls k) (hXrep k) (isRep_half (Ls k))
  set X' : Fin m → Fin 3 → ℂ := fun k => lawk (κA k) (Ls k).g₂ (Ls k).g₃ (Xk k) (E1 k)
    with hX'def
  have hX'rep : ∀ k, IsRep (Ls k) (t.2.2.1 k + zh (Ls k)) (X' k) := hκA
  set HX' := Cl * HX ^ 2 * H ^ 2 with hHX'def
  set dX' := l ^ 12 * dX ^ 2 * d ^ 2 with hdX'def
  have hHX'1 : 1 ≤ HX' :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCl1 (one_le_pow₀ hHX1))
      (one_le_pow₀ hH)
  have hdX'1 : 1 ≤ dX' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hX's : ∀ k i, Sz ι HX' dX' (X' k i) := fun k i =>
    hlaw k (κA k) (Xk k) (E1 k) HX H dX d (hXs k) (hE1s k) i
  choose κB hκB using fun k => isRep_lawk (Ls k) (hX'rep k) (isRep_half (Ls k))
  -- the fibre constants at `t`
  have hSR2 : (1 : ℝ) ≤ (S : ℝ) ^ 2 := one_le_pow₀ hSR
  have hHX'e : HX' ≤ Real.exp (cX * (S : ℝ) ^ 2) := by
    have e1 : HX' = Real.exp (Real.log Cl + 2 * Aa * (S : ℝ) ^ 2 + 2 * Real.log H) := by
      rw [hHX'def, hHXdef, Real.exp_add, Real.exp_add, Real.exp_log (by linarith),
        show 2 * Real.log H = Real.log (H ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity), ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [e1]; refine Real.exp_le_exp.mpr ?_
    have t1 : 0 ≤ (Real.log Cl + 2 * Real.log H) * ((S : ℝ) ^ 2 - 1) :=
      mul_nonneg (by linarith only [hlogCl', hlogH]) (by linarith only [hSR2])
    have t2 : 0 ≤ (12 * Real.log l + 2 * Real.log d) * (S : ℝ) ^ 2 :=
      mul_nonneg (by linarith only [hlogl', hlogd]) (by linarith only [hSR2])
    simp only [hcXdef]; nlinarith only [t1, t2]
  have hdX'e : (dX' : ℝ) ≤ Real.exp (cX * (S : ℝ) ^ 2) := by
    rw [hdX'def]; push_cast
    have e1 : (l : ℝ) ^ 12 * (d : ℝ) ^ 2 = Real.exp (12 * Real.log l + 2 * Real.log d) := by
      rw [Real.exp_add, show 12 * Real.log l = Real.log ((l : ℝ) ^ 12) by
        rw [Real.log_pow]; push_cast; ring, show 2 * Real.log d = Real.log ((d : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity),
        Real.exp_log (by positivity)]
    calc (l : ℝ) ^ 12 * (dX : ℝ) ^ 2 * (d : ℝ) ^ 2 =
          ((l : ℝ) ^ 12 * (d : ℝ) ^ 2) * (dX : ℝ) ^ 2 := by ring
      _ ≤ Real.exp (12 * Real.log l + 2 * Real.log d) * HX ^ 2 := by
          rw [e1]; gcongr
      _ = Real.exp (12 * Real.log l + 2 * Real.log d + 2 * Aa * (S : ℝ) ^ 2) := by
          rw [hHXdef, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ _ := Real.exp_le_exp.mpr (by
          have t1 : 0 ≤ (12 * Real.log l + 2 * Real.log d) * ((S : ℝ) ^ 2 - 1) :=
            mul_nonneg (by linarith only [hlogl', hlogd]) (by linarith only [hSR2])
          have t2 : 0 ≤ (Real.log Cl + 2 * Real.log H) * (S : ℝ) ^ 2 :=
            mul_nonneg (by linarith only [hlogCl', hlogH]) (by linarith only [hSR2])
          simp only [hcXdef]; nlinarith only [t1, t2])
  have hX'S : ∀ k a, SzS ι cX S (X' k a) := fun k a =>
    SzS.of_sz (hX's k a) hdX'1 hHX'e hdX'e
  obtain ⟨hcst, hqS⟩ := hcF S hS h hh X' hX'rep hX'S
  set cst : Fin r → ℂ := cstOf Ls M t with hcstdef
  let famV : FamF m r → ℂ := fun x => match x with
    | .inl i => cst i
    | .inr (.inl ij) => M ij.1 ij.2
    | .inr (.inr (.inl j)) => (2 * mult (lamIdx (X' j)) (X' j))⁻¹
    | .inr (.inr (.inr (.inl j))) => (Ls j).g₂
    | .inr (.inr (.inr (.inr (.inl j)))) => (Ls j).g₃
    | .inr (.inr (.inr (.inr (.inr ja)))) => X' ja.1 ja.2
  have hcHS : ∀ z : ℂ, Sz ι H d z → SzS ι cA S z := fun z hz =>
    (szS_of_sz hz hd hH hSR).mono (by simp only [hcAdef]; linarith only [hcF0, hcX]) hSR
  have hlH0 : 0 ≤ Real.log H := Real.log_nonneg hH
  have hld0 : 0 ≤ Real.log d := Real.log_nonneg hdR
  have hfam : ∀ x, SzS ι cA S (famV x) := by
    intro x
    rcases x with i | ij | j | j | j | ja
    · exact (hcst i).mono (by simp only [hcAdef]; linarith only [hcX, hlH0, hld0]) hSR
    · exact hcHS _ (Dt.hM ij.1 ij.2)
    · exact (hqS j).mono (by simp only [hcAdef]; linarith only [hcX, hlH0, hld0]) hSR
    · exact hcHS _ (Dt.hg₂' j)
    · exact hcHS _ (Dt.hg₃' j)
    · exact (hX'S ja.1 ja.2).mono (by simp only [hcAdef]; linarith only [hcF0, hlH0, hld0]) hSR
  obtain ⟨e₀, he₀1, he₀le, he₀s⟩ := SzS.common hfam
  set Afx : ℝ := Real.exp (cA * (S : ℝ) ^ 2) with hAfxdef
  have hAfx1 : 1 ≤ Afx := Real.one_le_exp (by positivity)
  have hHA : H ≤ Afx := by
    calc H = Real.exp (Real.log H) := (Real.exp_log (by linarith)).symm
      _ ≤ Afx := Real.exp_le_exp.mpr (by
          have : Real.log H ≤ cA := by simp only [hcAdef]; linarith only [hcF0, hcX, hld0]
          exact this.trans (le_mul_of_one_le_right hcA0 hSR2))
  set efx : ℕ := d * e₀ with hefxdef
  have hefx1 : 1 ≤ efx := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hefxle : (efx : ℝ) ≤ Real.exp (cE' * (S : ℝ) ^ 2) := by
    rw [hefxdef]; push_cast
    calc (d : ℝ) * e₀ ≤ Real.exp (Real.log d) * Real.exp (Fintype.card (FamF m r) * cA *
          (S : ℝ) ^ 2) := by
          rw [Real.exp_log (by linarith)]; gcongr
      _ ≤ Real.exp (cE' * (S : ℝ) ^ 2) := by
          rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
          have : Real.log d ≤ Real.log d * (S : ℝ) ^ 2 := le_mul_of_one_le_right hld0 hSR2
          simp only [hcE'def]; nlinarith only [this]
  have hfx : ∀ x, Sz ι Afx efx (famV x) := fun x =>
    (he₀s x).mono le_rfl (Dvd.intro_left d rfl)
  -- sizes of the coordinates of `t`
  set aT : ℝ := S * (μ + 1) * H with haTdef
  have haT1 : 1 ≤ aT :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hSR
      (by linarith only [(Nat.cast_nonneg μ : (0 : ℝ) ≤ μ)])) hH
  have ht0 : ∀ i, Sz ι aT d (t.1 i) := fun i => by
    rw [ht0']
    refine (sz_natComb hH0.le (fun j => Dt.ha j i) h hh).mono_le ?_
    rw [haTdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only)
      (by positivity)) hH0.le
  set hM : ℝ := H ^ (μ * S) with hhMdef
  set dM : ℕ := d ^ (μ * S) with hdMdef
  have ht1 : ∀ i, Sz ι hM dM (exp (t.2.1 i)) := fun i => by
    rw [ht1', Complex.exp_sum]
    have : ∀ j, exp ((h j : ℂ) * (Dt.y j).2.1 i) = exp ((Dt.y j).2.1 i) ^ h j := fun j => by
      rw [← Complex.exp_nat_mul]
    simp_rw [this]
    exact sz_expComb hH (fun j => Dt.hb j i) h hh
  -- the law bounds, discs and charts, uniformly in `k`
  have hlawB : ∀ k (κ' : Fin 2) (P Q : Fin 3 → ℂ) i,
      ‖lawk κ' (Ls k).g₂ (Ls k).g₃ P Q i‖ ≤ C'l * ‖P‖ ^ 2 * ‖Q‖ ^ 2 := by
    intro k κ' P Q i
    refine (hC'k k κ' i _ _ (le_max_left _ _) (le_max_right _ _) P Q).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC'kl k) (sq_nonneg _))
      (sq_nonneg _)
  have hxi' : ∀ k (u : ℂ), ‖u‖ ≤ ρ₁ → zh (Ls k) + u ∉ (Ls k).lattice ∧
      ‖℘[Ls k] (zh (Ls k) + u)‖ ≤ Mξ ∧ ‖℘'[Ls k] (zh (Ls k) + u)‖ ≤ Mξ := by
    intro k u hu
    obtain ⟨h1, h2, h3⟩ := hxi k u (hu.trans (hρ₁le k).2)
    exact ⟨h1, h2.trans (hMxξ k), h3.trans (hMxξ k)⟩
  have hchart' : ∀ k, ∃ j : Fin 3, ∀ z : ℂ, ‖z‖ ≤ ρ₁ →
      Real.exp (-(cc * (1 + S * Y) ^ 2)) ≤ ‖ellV (Ls k) (t.2.2.1 k + z) j‖ := by
    intro k
    obtain ⟨j, hj⟩ := hchart k (t.2.2.1 k)
    refine ⟨j, fun z hz => le_trans (Real.exp_le_exp.mpr ?_) (hj z (hz.trans (hρ₁le k).1))⟩
    have h1 : (1 + ‖t.2.2.1 k‖) ^ 2 ≤ (1 + S * Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [htk k]) 2
    have h2 : cch k * (1 + ‖t.2.2.1 k‖) ^ 2 ≤ cc * (1 + S * Y) ^ 2 :=
      mul_le_mul (hcchcc k) h1 (by positivity) hcc0
    linarith only [h2]
  -- one direction of the grid
  have key : ∀ c : Fin τ → ℕ, (∀ q, c q ≤ T) → ∀ k < T,
      iteratedDeriv k (fun s : ℂ => PsiV Ls M μs p (t + s • ∑ q, (c q : ℂ) • Dt.w q)) 0 = 0 := by
    intro c hc
    set v : TanV d0 d1 m r := ∑ q, (c q : ℂ) • Dt.w q with hvdef
    have hv0' : ∀ i, v.1 i = ∑ q, (c q : ℂ) * (Dt.w q).1 i := by
      intro i; simp [hvdef, Prod.fst_sum, Finset.sum_apply]
    have hv1' : ∀ i, v.2.1 i = ∑ q, (c q : ℂ) * (Dt.w q).2.1 i := by
      intro i; simp [hvdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    have hv2' : ∀ k, v.2.2.1 k = ∑ q, (c q : ℂ) * (Dt.w q).2.2.1 k := by
      intro k; simp [hvdef, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    have hv3' : ∀ i, v.2.2.2 i = ∑ q, (c q : ℂ) * (Dt.w q).2.2.2 i := by
      intro i; simp [hvdef, Prod.snd_sum, Finset.sum_apply]
    have hvn : ‖v‖ ≤ T * Wn := by
      refine (norm_sum_le _ _).trans ?_
      rw [hWndef, mul_sum]
      refine sum_le_sum fun q _ => ?_
      rw [norm_smul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc q) (norm_nonneg _)
    have hvV : v ∈ V := V.sum_mem fun q _ => V.smul_mem _ (hwV q)
    set aV : ℝ := T * τ * H with haVdef
    have haV : 0 ≤ aV := by positivity
    have hv0 : ∀ i, Sz ι aV d (v.1 i) := fun i => by
      rw [hv0']; exact sz_natComb hH0.le (fun q => Dt.hw0 q i) c hc
    have hv1 : ∀ i, Sz ι aV d (v.2.1 i) := fun i => by
      rw [hv1']; exact sz_natComb hH0.le (fun q => Dt.hw1 q i) c hc
    have hv2 : ∀ k, Sz ι aV d (v.2.2.1 k) := fun k => by
      rw [hv2']; exact sz_natComb hH0.le (fun q => Dt.hw2 q k) c hc
    have hv3 : ∀ i, Sz ι aV d (v.2.2.2 i) := fun i => by
      rw [hv3']; exact sz_natComb hH0.le (fun q => Dt.hw3 q i) c hc
    -- the fibre factors
    set Bξ : ℝ := 1 + 7 * aV * H with hBξdef
    have h7 : 0 ≤ 7 * aV * H := mul_nonneg (mul_nonneg (by norm_num) haV) hH0.le
    have hBξ1 : 1 ≤ Bξ := by simp only [hBξdef]; linarith only [h7]
    have hB₁ : 1 ≤ 2 * Bξ := by linarith
    have haVB : aV ≤ Bξ := by
      have : aV ≤ 7 * aV * H := by nlinarith only [haV, hH]
      simp only [hBξdef]; linarith only [this]
    have hξ : ∀ k, KS ι H Bξ d (d ^ 2) (wpP (Ls k) (v.2.2.1 k)) ∧
        KS ι H Bξ d (d ^ 2) (wpQ (Ls k) (v.2.2.1 k)) := fun k =>
      ks_wpSeries (Ls k) (hv2 k) (Dt.he₁ k) ((Dt.hg₂ k).mono le_rfl (Dvd.intro_left _ rfl |>.trans
        (by rw [sq]))) hH le_rfl hBξ1 (by
          have : aV * (6 * H + H) = 7 * aV * H := by ring
          simp only [hBξdef]; linarith only [this])
    have hval : ∀ i x, KS ι Afx (2 * Bξ) efx (d ^ 2) (fibVals Ls M X' cst v i x) := by
      intro i
      refine ks_fibVals Ls M X' cst v i hB₁ hAfx1 (hfx (.inl i)) ((hv3 i).mono ?_
        (Dvd.intro e₀ rfl)) (fun j => hfx (.inr (.inl (i, j))))
        (fun j => hfx (.inr (.inr (.inl j)))) (fun j => hfx (.inr (.inr (.inr (.inl j)))))
        (fun j => hfx (.inr (.inr (.inr (.inr (.inl j)))))) (fun j a =>
          hfx (.inr (.inr (.inr (.inr (.inr (j, a))))))) (fun j => ?_) (fun j => ?_) (fun j => ?_)
      · nlinarith only [haVB, hAfx1, hBξ1]
      · exact (hξ j).1.mono hHA (by linarith) (by linarith) (Dvd.intro e₀ rfl) dvd_rfl
      · exact (hξ j).2.mono hHA (by linarith) (by linarith) (Dvd.intro e₀ rfl) dvd_rfl
      · exact (ks_zS (Ls j) (hv2 j) (hξ j).1 haVB (by linarith)).mono hHA (by linarith)
          (by linarith) (one_dvd _) dvd_rfl
    have hfib : ∀ i, KS ι ((CF m + 1) * (2 ^ NF m * Afx ^ NF m)) (2 * (2 * Bξ)) (efx ^ NF m)
        (d ^ 2) (fibFac Ls M κB X' cst v i) := fun i =>
      (ks_fibFac Ls M κB X' cst v i (by linarith only [hBξ1]) hAfx1 (hval i)).mono
        (mul_le_mul_of_nonneg_right (by linarith only) (by positivity)) (by positivity) le_rfl
        dvd_rfl dvd_rfl
    have hsm : ∀ s : ℂ, ‖s‖ ≤ ρ₁ / (1 + ‖v‖) → ‖PsiV Ls M μs p (t + s • v)‖ ≤ Real.exp (-U) := by
      intro s hs
      refine hsmall _ (V.add_mem htV (V.smul_mem s hvV)) ?_
      have h1 : ‖s • v‖ ≤ ρ₁ := by
        rw [norm_smul]
        calc ‖s‖ * ‖v‖ ≤ ρ₁ / (1 + ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
          _ ≤ ρ₁ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith only [hρ₁, norm_nonneg v]
      have h2 : ‖t + s • v‖ ≤ S * Y + 1 :=
        (norm_add_le _ _).trans (by linarith only [htn, h1, hρ₁1])
      have h3 : S * Y + 1 ≤ c₀ * S := by
        have hc0 : 2 + Y ≤ c₀ := by
          rw [hc₀def, hc₀abdef]; linarith only [hκ1, hκ2, hκ3, hκ4, hdeg0, hcE0]
        nlinarith only [hc0, hSR, hY0]
      exact h2.trans h3
    -- the budget with `U − E`
    set E : ℝ := cE * ((D + 1) * (S : ℝ) ^ 2 + (T + 1) * Real.log (T + 2)) with hEdef
    have hbud' : c₀ab * (B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S +
        (D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2)) ≤ U - E := by
      have hL1 : 0 ≤ Real.log ((L : ℝ) + 1) := Real.log_nonneg (by
        linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
      have hS1 : 0 ≤ Real.log ((S : ℝ) + 1) := Real.log_nonneg (by linarith)
      have h1 : E ≤ cE * (B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S +
          (D + 1) * S ^ 2 + (T + 1) * Real.log (T + 2)) := by
        rw [hEdef]
        refine mul_le_mul_of_nonneg_left ?_ hcE0
        have : 0 ≤ B + Real.log (L + 1) + (A₀ + 1) * Real.log (S + 1) + (A₁ + 1) * S := by
          positivity
        linarith
      have h2 := hbud
      rw [hc₀def, add_mul] at h2
      linarith only [h1, h2]
    have hAfib1 : 1 ≤ (CF m + 1) * (2 ^ NF m * Afx ^ NF m) :=
      one_le_mul_of_one_le_of_one_le (by linarith only [CF_nonneg m])
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (one_le_pow₀ hAfx1))
    exact lemmaU_dirV Ls M ι μs p hα hβ hp hB t v κB X' hX'rep (fun k => (hκB k).1) cst
      (fun i => rfl) hH hd haT1 haV (one_le_pow₀ hH) (Nat.one_le_iff_ne_zero.mpr (by positivity))
      hHX'1 hdX'1 hl1 hCl1 hAfib1 (Nat.one_le_iff_ne_zero.mpr (by positivity)) hlaw
      ht0 hv0 ht1 hv1 hv2 hX's Dt.he₁ Dt.hg₂ hfib hρ₁ (zero_le_one.trans hC'l1) hMξ1 hlawB hxi'
      hchart' hsm (fun k hk => by
        have hab := lemmaU_arith (U := U - E) hS hk hH hd hCl1 hC'l1 hMξ1 hAa0 hcc0 hY0 hWn0 hρ₁
          hρ₁1 hl1 hB hdX1 hdXle (norm_nonneg v) hvn hbud'
        have hX := fib_extra_le (deg := deg) (r := r) (D := D) (NF := NF m) (k := k) (T := T)
          (CF := CF m) hSR hk hcA0 hcE'0 (CF_nonneg m) hefxle hefx1
        rw [prod_efacV, sum_NfacV, prod_AfacV]
        have hAf0 : ∀ f : Fct d0 d1 m, 0 ≤ Afac (S * (μ + 1) * H) (H ^ (μ * S)) Cl HX' H f := by
          intro f
          rcases f with i | i | ⟨k, c⟩
          · exact zero_le_one.trans haT1
          · exact zero_le_one.trans (one_le_pow₀ hH)
          · exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num)
              (zero_le_one.trans hCl1)) (sq_nonneg _))) (sq_nonneg _)
        exact dominate (by positivity) (by positivity) (by positivity)
          (prod_nonneg fun f _ => pow_nonneg (hAf0 f) _) (by positivity) hab hX)
  -- polarization
  intro w hw k hk
  have hkT : k < T := by exact_mod_cast hk
  exact iteratedDeriv_line_eq_zero_of_span (contDiff_PsiV Ls M μs p) t Dt.w k
    (fun c hc => key c (fun q => (hc q).trans hkT.le) k hkT) hw


end LSG.AuxV
