/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7Taylor
import LSG.W88.Prop61
import LSG.ME.MultEstStmt
import LSG.ME.SubgroupLift

/-!
# From the auxiliary function of Prop. 6.1 to a polynomial with formal multiplicity (W88 §7)

The auxiliary function `Psi Ls μs p = Σ_l p_l M_l ∘ exp_G` of `LSG.W88.prop61` becomes the
polynomial `Ppoly μs p = Σ_l p_l · monoPoly (μ_l)` on the multi-cone model of `LSG.ME`
(`(σ³, σ³℘, σ³℘′) ↦ (W, U, V)` in each elliptic block):

* `eval_Ppoly`: `Ppoly` evaluated at the cone representative `liftX ellV x` of `exp_G x` is
  `Psi x`; `isHomE_Ppoly` (degree `D` in every elliptic block), `Ppoly_mem_FLE`;
* `Ppoly_notMem_IG`: `Psi ≢ 0 ⇒ Ppoly ∉ I_G` (Nullstellensatz `vanish_univ`);
* **`ordGt_of_vanishAlong`**: analytic vanishing of `Psi` along `W` to order `> n` at `y`
  (`VanishAlong`) gives the formal order `OrdGt W (Ppoly μs p) n (exp_G y)`. The Taylor series of
  the analytic lift of `s ↦ exp_G(y + s w)` in the canonical charts is the formal flow `fexp`
  (`tps_eq_fflow`), and `Psi(y + s w)` is a unit times `Ppoly` at that lift (homogeneity).
-/

open MvPolynomial LSG.Aux LSG.ME LSG.Elliptic LSG.Weierstrass Filter Topology
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE prod_mem_FLE' pow_mem_FLE')

noncomputable section

namespace LSG.W88

variable {d0 d1 m : ℕ}

/-! ### The polynomial -/

/-- The cone monomial of `μ`. -/
def monoPoly {D : ℕ} (μ : Mono d0 d1 m D) : MvPolynomial (Var d0 d1 m) ℂ :=
  (∏ i, X (Var.x i) ^ μ.α i) * (∏ j, X (Var.y j) ^ μ.β j) *
    ∏ k, ∏ t : Fin 3, X (Var.e k (cidx t)) ^ μ.γ k t

/-- The polynomial of the auxiliary function. -/
def Ppoly {D L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) :
    MvPolynomial (Var d0 d1 m) ℂ :=
  ∑ l, C (p l : ℂ) * monoPoly (μs l)

/-- The `ellV` lifts. -/
def ellF (Ls : Fin m → PeriodPair) : Fin m → ℂ → Fin 3 → ℂ := fun k => ellV (Ls k)

theorem eval_monoPoly (Ls : Fin m → PeriodPair) {D : ℕ} (μ : Mono d0 d1 m D) (x : Tan d0 d1 m) :
    eval (liftX (ellF Ls) x) (monoPoly μ) = μ.eval Ls x := by
  simp only [monoPoly, Mono.eval, map_mul, map_prod, map_pow, eval_X, liftX, ellF, ellV_cidx]

theorem eval_Ppoly (Ls : Fin m → PeriodPair) {D L : ℕ} (μs : Fin L → Mono d0 d1 m D)
    (p : Fin L → ℤ) (x : Tan d0 d1 m) : eval (liftX (ellF Ls) x) (Ppoly μs p) = Psi Ls μs p x := by
  simp only [Ppoly, Psi, map_sum, map_mul, eval_C, eval_monoPoly]

theorem isHomE_monoPoly {D : ℕ} (μ : Mono d0 d1 m D) : IsHomE (monoPoly μ) (fun _ => D) := by
  intro k
  have hx := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (Var.x i) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.α i) (fun _ => 0)
    (fun i _ => by simpa using (isWeightedHomogeneous_X ℂ (wk k) (Var.x i : Var d0 d1 m)).pow (μ.α i))
  have hy := IsWeightedHomogeneous.prod Finset.univ
    (fun j => (X (Var.y j) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.β j) (fun _ => 0)
    (fun j _ => by simpa using (isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d0 d1 m)).pow (μ.β j))
  have he := IsWeightedHomogeneous.prod Finset.univ
    (fun k' => ∏ t : Fin 3, (X (Var.e k' (cidx t)) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.γ k' t)
    (fun k' => if k' = k then D else 0) (fun k' _ => by
      have := IsWeightedHomogeneous.prod Finset.univ
        (fun t : Fin 3 => (X (Var.e k' (cidx t)) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.γ k' t)
        (fun t => μ.γ k' t * if k' = k then 1 else 0)
        (fun t _ => by
          simpa [mul_comm] using
            (isWeightedHomogeneous_X ℂ (wk k) (Var.e k' (cidx t) : Var d0 d1 m)).pow (μ.γ k' t))
      convert this using 1
      split_ifs with h
      · simp [μ.hγ k']
      · simp)
  show IsWeightedHomogeneous (wk k) (monoPoly μ) D
  unfold monoPoly
  convert (hx.mul hy).mul he using 1
  simp

theorem isHomE_Ppoly {D L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) :
    IsHomE (Ppoly μs p) (fun _ => D) := by
  intro k
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [mem_weightedHomogeneousSubmodule]
  simpa using (isWeightedHomogeneous_C (wk k) (p l : ℂ)).mul (isHomE_monoPoly (μs l) k)

theorem monoPoly_mem_FLE {D A B : ℕ} (μ : Mono d0 d1 m D) (hA : ∑ i, μ.α i ≤ A)
    (hB : ∑ j, μ.β j ≤ B) : monoPoly μ ∈ FLE ℂ blk (Dfun A B D) := by
  have h1 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun i => (X (Var.x i) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.α i)
    (fun i => μ.α i • Pi.single (blk (Var.x i : Var d0 d1 m)) 1) (fun i _ => pow_mem_FLE' (fle_X _) _)
  have h2 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun j => (X (Var.y j) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.β j)
    (fun j => μ.β j • Pi.single (blk (Var.y j : Var d0 d1 m)) 1) (fun j _ => pow_mem_FLE' (fle_X _) _)
  have h3 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun k => ∏ t : Fin 3, (X (Var.e k (cidx t)) : MvPolynomial (Var d0 d1 m) ℂ) ^ μ.γ k t)
    (fun k => ∑ t : Fin 3, μ.γ k t • Pi.single (blk (Var.e k (cidx t) : Var d0 d1 m)) 1)
    (fun k _ => prod_mem_FLE' _ _ _ fun t _ => pow_mem_FLE' (fle_X _) _)
  refine FLE_mono ℂ blk (fun b => ?_) (mul_mem_FLE ℂ (mul_mem_FLE ℂ h1 h2) h3)
  cases b with
  | x => simpa [Dfun, Finset.sum_apply, Pi.single_apply] using hA
  | yz => simpa [Dfun, Finset.sum_apply, Pi.single_apply] using hB
  | e k =>
    simp only [Dfun, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blk_x, blk_y, blk_e,
      Pi.single_apply, smul_eq_mul, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero,
      zero_add, Blk.e.injEq, mul_ite, mul_one]
    rw [Finset.sum_comm]
    simp [μ.hγ k]

theorem Ppoly_mem_FLE {D L A B : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ)
    (hA : ∀ l, ∑ i, (μs l).α i ≤ A) (hB : ∀ l, ∑ j, (μs l).β j ≤ B) :
    Ppoly μs p ∈ FLE ℂ blk (Dfun A B D) := by
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (monoPoly_mem_FLE _ (hA l) (hB l))

/-! ### Nonvanishing on `G` -/

variable (Ls : Fin m → PeriodPair)

theorem ellV_eq_smul_rep (k : Fin m) (z : ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ellV (Ls k) z = c • rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) z) := by
  have hR := isRep_ellV (Ls k) z
  obtain ⟨c, hc, h⟩ := exists_smul_rep (two_ne_zero) (discr_g2L Ls k) hR.2.1 hR.1
  refine ⟨c, hc, ?_⟩
  rw [h]
  congr 2
  exact hR.2.2

theorem liftX_ellF_eq (x : Tan d0 d1 m) : ∃ lam, liftX (ellF Ls) x = coords (expG Ls x) lam :=
  liftX_eq Ls fun k => ellV_eq_smul_rep Ls k (x.2.2 k)

theorem Ppoly_notMem_IG {D L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ)
    (hne : ∃ x, Psi Ls μs p x ≠ 0) :
    Ppoly μs p ∉ IG (d₀ := d0) (d₁ := d1) (g2L Ls) (g3L Ls) := by
  intro hP
  rw [← vanish_univ (discr_g2L Ls) two_ne_zero] at hP
  obtain ⟨x, hx⟩ := hne
  obtain ⟨lam, hlam⟩ := liftX_ellF_eq Ls x
  apply hx
  rw [← eval_Ppoly, hlam]
  exact mem_vanish.mp hP _ (Set.mem_univ _) lam

/-- The product of the `W`-coordinates. -/
def Wprod (d0 d1 m : ℕ) : MvPolynomial (Var d0 d1 m) ℂ := ∏ k, X (Var.e k 2)

theorem Wprod_notMem_IG : Wprod d0 d1 m ∉ IG (d₀ := d0) (d₁ := d1) (g2L Ls) (g3L Ls) := by
  intro hP
  obtain ⟨k, -, hk⟩ := ((IG_isPrime (d₀ := d0) (d₁ := d1) (g2L Ls) (g3L Ls) two_ne_zero).prod_mem_iff).mp hP
  rw [← vanish_univ (discr_g2L Ls) two_ne_zero] at hk
  set x : Tan d0 d1 m := (0, 0, fun j => (Ls j).ω₁ / 2)
  have h := mem_vanish.mp hk (expG Ls x) (Set.mem_univ _) 1
  have hnot : x.2.2 k ∉ (Ls k).lattice := (Ls k).ω₁_div_two_notMem_lattice
  simp only [eval_X, coords, coordsZ_e, Pi.one_apply, Units.val_one, one_mul, expG] at h
  have key := congrFun (rep_expE_of_notMem (Ls k) hnot) 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at key
  exact one_ne_zero (key.symm.trans h)

theorem isHomE_Wprod : IsHomE (Wprod d0 d1 m) (fun _ => 1) := by
  intro k
  have := IsWeightedHomogeneous.prod Finset.univ
    (fun k' => (X (Var.e k' 2) : MvPolynomial (Var d0 d1 m) ℂ)) (fun k' => if k' = k then 1 else 0)
    (fun k' _ => by simpa using isWeightedHomogeneous_X ℂ (wk k) (Var.e k' 2 : Var d0 d1 m))
  simpa [Wprod] using this

theorem Wprod_mem_FLE :
    Wprod d0 d1 m ∈ FLE ℂ blk (∑ k : Fin m, Pi.single (Blk.e k : Blk m) 1) :=
  prod_mem_FLE' _ _ _ fun k _ => fle_X (Var.e k 2 : Var d0 d1 m)

/-! ### Charts and lifts -/

/-- The `W`-chart derivation on a cone vector. -/
def chartWf (a : ℂ) (P : Fin 3 → ℂ) : Fin 3 → ℂ := ![P 1 * P 2, 6 * P 0 ^ 2 - 1 / 2 * a * P 2 ^ 2, 0]

theorem eval_chartPoly_two (g₂ g₃ : Fin m → ℂ) (k : Fin m) (c : Fin 3) (x : Var d0 d1 m → ℂ) :
    eval x (chartPoly g₂ g₃ d0 d1 2 k c) = chartWf (g₂ k) (fun i => x (.e k i)) c := by
  fin_cases c <;> simp [chartPoly, chartW, chartWf]

open Classical in
/-- The chart index at a point of `ℂ`: `V` at lattice points, `W` elsewhere. -/
def chIdx (L : PeriodPair) (z : ℂ) : Fin 3 := if z ∈ L.lattice then 1 else 2

/-- The chart vector field. -/
def chF (ch : Fin 3) (a b : ℂ) (P : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if ch = 1 then chartVf a b P else chartWf a P

theorem chartAt_expG (y : Tan d0 d1 m) (k : Fin m) :
    ME.chartAt (expG Ls y) k = chIdx (Ls k) (y.2.2 k) := by
  by_cases h : y.2.2 k ∈ (Ls k).lattice
  · have h1 : chIdx (Ls k) (y.2.2 k) = 1 := by simp [chIdx, h]
    rw [h1]
    unfold ME.chartAt
    simp only [expG, expE_of_mem (Ls k) h]
  · have h2 : chIdx (Ls k) (y.2.2 k) = 2 := by simp [chIdx, h]
    rw [h2]
    unfold ME.chartAt
    simp only [expG, expE_of_notMem (Ls k) h]

theorem eval_chartPoly_chIdx (k : Fin m) (z : ℂ) (c : Fin 3) (x : Var d0 d1 m → ℂ) :
    eval x (chartPoly (g2L Ls) (g3L Ls) d0 d1 (chIdx (Ls k) z) k c) =
      chF (chIdx (Ls k) z) (Ls k).g₂ (Ls k).g₃ (fun i => x (.e k i)) c := by
  by_cases h : z ∈ (Ls k).lattice
  · have h1 : chIdx (Ls k) z = 1 := by simp [chIdx, h]
    rw [h1, eval_chartPoly_one]
    simp only [chF, ite_true]
    rfl
  · have h2 : chIdx (Ls k) z = 2 := by simp [chIdx, h]
    rw [h2, eval_chartPoly_two]
    simp only [chF, show (2 : Fin 3) ≠ 1 by decide, ite_false]
    rfl

theorem rep_chIdx (L : PeriodPair) (z : ℂ) :
    rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z) (chIdx L z) = 1 := by
  by_cases h : z ∈ L.lattice
  · have h1 : chIdx L z = 1 := by simp [chIdx, h]
    rw [h1, expE_of_mem L h]; simp [rep, O]
  · have h2 : chIdx L z = 2 := by simp [chIdx, h]
    rw [h2, rep_expE_of_notMem L h]; simp

/-- **Chart-normalised analytic lifts** of `expE` near `z₀`, in the canonical chart. -/
theorem exists_chartLift (L : PeriodPair) (z₀ : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ F : ℂ → Fin 3 → ℂ,
      (∀ i, AnalyticAt ℂ (fun z => F z i) z₀) ∧
      F z₀ = rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z₀) ∧
      ∀ z ∈ U, (∃ c : ℂ, c ≠ 0 ∧ F z = c • rep (g₂ := L.g₂) (g₃ := L.g₃) (expE L z)) ∧
        F z (chIdx L z₀) = 1 ∧
        ∀ i, HasDerivAt (fun z => F z i) (chF (chIdx L z₀) L.g₂ L.g₃ (F z) i) z := by
  by_cases h₀ : z₀ ∈ L.lattice
  · obtain ⟨U, hU, hz₀, F, hF, hFU⟩ := exists_VLift L z₀ (Or.inl h₀)
    have hch : chIdx L z₀ = 1 := by simp [chIdx, h₀]
    refine ⟨U, hU, hz₀, F, fun i => hF i z₀ hz₀, ?_, fun z hz => ⟨(hFU z hz).2.1, ?_, ?_⟩⟩
    · obtain ⟨c, hc, hFc⟩ := (hFU z₀ hz₀).2.1
      have h1 := congrFun hFc 1
      rw [(hFU z₀ hz₀).1, Pi.smul_apply, smul_eq_mul, expE_of_mem L h₀] at h1
      simp only [rep, O] at h1
      have hc1 : c = 1 := by simpa using h1.symm
      rw [hFc, hc1, one_smul]
    · rw [hch]; exact (hFU z hz).1
    · intro i; rw [hch]; simpa [chF] using (hFU z hz).2.2 i
  · have hch : chIdx L z₀ = 2 := by simp [chIdx, h₀]
    have hUo : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
    have hPan : AnalyticOnNhd ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ :=
      L.differentiableOn_weierstrassP.analyticOnNhd hUo
    refine ⟨(L.lattice : Set ℂ)ᶜ, hUo, h₀, fun z => ![L.weierstrassP z, L.derivWeierstrassP z, 1],
      fun i => ?_, ?_, fun z hz => ⟨⟨1, one_ne_zero, ?_⟩, ?_, fun i => ?_⟩⟩
    · fin_cases i
      · exact hPan z₀ h₀
      · exact L.analyticOnNhd_derivWeierstrassP z₀ h₀
      · exact analyticAt_const
    · rw [rep_expE_of_notMem L h₀]
    · rw [one_smul, rep_expE_of_notMem L hz]
    · rw [hch]; simp
    · rw [hch]
      fin_cases i
      · simpa [chF, chartWf] using hasDerivAt_weierstrassP L hz
      · have := hasDerivAt_derivWeierstrassP L hz
        refine this.congr_deriv ?_
        simp [chF, chartWf]; ring
      · simpa [chF, chartWf] using hasDerivAt_const z (1 : ℂ)

/-! ### Analytic vanishing gives formal order -/

theorem liftX_line (F : Fin m → ℂ → Fin 3 → ℂ) (y w : Tan d0 d1 m) (s : ℂ) :
    (∀ i, liftX F (y + s • w) (Var.x i) = y.1 i + s * w.1 i) ∧
    (∀ j, liftX F (y + s • w) (Var.y j) = Complex.exp (y.2.1 j + s * w.2.1 j)) ∧
    (∀ j, liftX F (y + s • w) (Var.z j) = Complex.exp (-(y.2.1 j + s * w.2.1 j))) ∧
    (∀ k c, liftX F (y + s • w) (Var.e k c) = F k (y.2.2 k + s * w.2.2 k) c) := by
  refine ⟨fun i => ?_, fun j => ?_, fun j => ?_, fun k c => ?_⟩ <;> simp [liftX]

/-- **Analytic vanishing along `W` ⇒ formal order along `W`.** -/
theorem ordGt_of_vanishAlong {D L : ℕ} (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ)
    (W : Submodule ℂ (Tan d0 d1 m)) {T : ℝ} {y : Tan d0 d1 m}
    (hv : VanishAlong (Psi Ls μs p) W T y) {n : ℕ} (hn : (n : ℝ) < T) :
    OrdGt (g2L Ls) (g3L Ls) W (Ppoly μs p) n (expG Ls y) := by
  intro w hw
  choose U hUo hzU F hFan hF0 hFU using fun k => exists_chartLift (Ls k) (y.2.2 k)
  set ch : Fin m → Fin 3 := fun k => chIdx (Ls k) (y.2.2 k) with hchdef
  have hch : ME.chartAt (expG Ls y) = ch := funext fun k => chartAt_expG Ls y k
  set Γ : Var d0 d1 m → ℂ → ℂ := fun v s => liftX F (y + s • w) v with hΓdef
  have hline := fun s => liftX_line F y w s
  -- near `0` the line stays in the lift domains
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ k, y.2.2 k + s * w.2.2 k ∈ U k := by
    refine eventually_all.mpr fun k => ?_
    have hc : ContinuousAt (fun s : ℂ => y.2.2 k + s * w.2.2 k) 0 := by fun_prop
    have := hc.preimage_mem_nhds ((hUo k).mem_nhds (by simpa using hzU k))
    exact this
  have hlinan : ∀ a b : ℂ, AnalyticAt ℂ (fun s : ℂ => a + s * b) 0 := fun a b => by fun_prop
  have hΓan : ∀ v, AnalyticAt ℂ (Γ v) 0 := by
    intro v
    cases v with
    | x i => simp only [Γ, (hline _).1]; exact hlinan _ _
    | y j => simp only [Γ, (hline _).2.1]; exact (hlinan _ _).cexp
    | z j => simp only [Γ, (hline _).2.2.1]; exact (hlinan _ _).neg.cexp
    | e k c =>
      simp only [Γ, (hline _).2.2.2]
      exact AnalyticAt.comp (g := fun z => F k z c) (f := fun s : ℂ => y.2.2 k + s * w.2.2 k)
        (by simpa using hFan k c) (hlinan _ _)
  have hder : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ v, HasDerivAt (Γ v)
      (eval (fun u => Γ u s) (dval (g2L Ls) (g3L Ls) (ME.chartAt (expG Ls y)) w v)) s := by
    filter_upwards [hev] with s hs
    intro v
    have hl : ∀ a b : ℂ, HasDerivAt (fun s : ℂ => a + s * b) b s := fun a b => by
      simpa using ((hasDerivAt_id s).mul_const b).const_add a
    cases v with
    | x i =>
      simp only [Γ, (hline _).1, dval, eval_C]
      exact hl _ _
    | y j =>
      simp only [Γ, (hline _).2.1, dval, map_mul, eval_C, eval_X]
      refine (hl _ _).cexp.congr_deriv ?_
      ring
    | z j =>
      simp only [Γ, (hline _).2.2.1, dval, map_neg, map_mul, eval_C, eval_X]
      have e : (fun t : ℂ => Complex.exp (-(y.2.1 j + t * w.2.1 j))) =
          fun t => Complex.exp (-y.2.1 j + t * -w.2.1 j) := by funext t; ring_nf
      rw [e]
      refine (hl _ _).cexp.congr_deriv ?_
      ring_nf
    | e k c =>
      simp only [Γ, (hline _).2.2.2, dval, map_mul, eval_C, hch]
      have h1 := (hFU k _ (hs k)).2.2 c
      refine (HasDerivAt.comp (h₂ := fun z => F k z c) s h1 (hl _ _)).congr_deriv ?_
      rw [eval_chartPoly_chIdx Ls k (y.2.2 k) c]
      simp only [hline, mul_comm]
  have h0 : (fun v => Γ v 0) = coords (expG Ls y) 1 := by
    funext v
    cases v with
    | x i => simp [Γ, hline, coords, expG]
    | y j => simp [Γ, hline, coords, expG, GPt.ym, expU]
    | z j => simp [Γ, hline, coords, expG, GPt.ym, expU, Complex.exp_neg]
    | e k c => simp [Γ, hline, coords, expG, hF0 k]; rfl
  have hfexp : fexp (g2L Ls) (g3L Ls) (expG Ls y) w = fun v => tps (Γ v) := by
    rw [tps_eq_fflow _ w Γ hΓan hder, h0]; rfl
  -- homogeneity: `Psi(y + s w) = u(s) · Ppoly(Γ(s))`
  set u : ℂ → ℂ := fun s => ∏ k, ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k) ^ D with hudef
  set f : ℂ → ℂ := fun s => eval (fun v => Γ v s) (Ppoly μs p) with hfdef
  have hfan : AnalyticAt ℂ f 0 := analyticAt_eval hΓan _
  have huan : AnalyticAt ℂ u 0 := by
    refine Finset.analyticAt_fun_prod _ fun k _ => (AnalyticAt.pow ?_ D)
    exact ((differentiable_ellV_apply (Ls k) (ch k)).analyticAt _).comp (hlinan _ _)
  have hu0 : u 0 ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
    obtain ⟨c, hc, hce⟩ := ellV_eq_smul_rep Ls k (y.2.2 k)
    simp only [zero_mul, add_zero]
    rw [hce, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc fun h0 => one_ne_zero ((rep_chIdx (Ls k) (y.2.2 k)).symm.trans h0)
  have hmul : (u * f) =ᶠ[𝓝 0] fun s => Psi Ls μs p (y + s • w) := by
    filter_upwards [hev] with s hs
    have hsc : liftX (ellF Ls) (y + s • w) =
        scl (fun k => ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k)) (liftX F (y + s • w)) := by
      funext v
      cases v with
      | x i => simp [liftX]
      | y j => simp [liftX]
      | z j => simp [liftX]
      | e k c =>
        rw [scl_e, (hline s).2.2.2]
        obtain ⟨c₁, hc₁, h₁⟩ := (hFU k _ (hs k)).1
        obtain ⟨c₂, -, h₂⟩ := ellV_eq_smul_rep Ls k (y.2.2 k + s * w.2.2 k)
        have hV : F k (y.2.2 k + s * w.2.2 k) (ch k) = 1 := (hFU k _ (hs k)).2.1
        have e₂ : ellV (Ls k) (y.2.2 k + s * w.2.2 k) = (c₂ / c₁) • F k (y.2.2 k + s * w.2.2 k) := by
          rw [h₂, h₁, smul_smul, div_mul_cancel₀ _ hc₁]; rfl
        have hcv : ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k) = c₂ / c₁ := by
          rw [e₂, Pi.smul_apply, hV, smul_eq_mul, mul_one]
        simp only [liftX, ellF, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        rw [hcv, e₂, Pi.smul_apply, smul_eq_mul]
    show u s * f s = Psi Ls μs p (y + s • w)
    have hs' := aeval_scl (K := ℂ) (S := ℂ) (isHomE_Ppoly μs p)
      (fun k => ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k)) (liftX F (y + s • w))
    have h3 : eval (scl (fun k => ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k))
        (liftX F (y + s • w))) (Ppoly μs p) = (∏ k, ellV (Ls k) (y.2.2 k + s * w.2.2 k) (ch k) ^ D) *
          eval (liftX F (y + s • w)) (Ppoly μs p) := by
      rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]; exact hs'
    rw [← eval_Ppoly, hsc, h3]
  have hzero : ∀ j < n + 1, iteratedDeriv j f 0 = 0 := by
    refine iteratedDeriv_eq_zero_of_mul huan hu0 hfan fun j hj => ?_
    rw [(hmul.iteratedDeriv j).eq_of_nhds]
    refine hv w hw j (lt_of_le_of_lt ?_ hn)
    exact_mod_cast Nat.lt_succ_iff.mp hj
  intro i hi
  rw [hfexp, ← tps_eval Γ hΓan, coeff_tps]
  show iteratedDeriv i f 0 / _ = 0
  rw [hzero i (Nat.lt_succ_of_le hi), zero_div]

end LSG.W88
