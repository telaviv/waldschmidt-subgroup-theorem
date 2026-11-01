/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Weierstrass.SigmaSign
import LSG.Weierstrass.OrderTwo
import LSG.W88.Statement

/-!
# The coordinate monomials of `exp_G` and their common multiplier (concrete (QP))

`G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, tangent space `LSG.W88.Tan d0 d1 m`. The entire
coordinates of `exp_G` are
* `a_i` (G_a), `exp (b_i)` (G_m), and
* for each elliptic factor the Weierstrass-embedding coordinates
  `W₀ = σ³`, `W₁ = σ(σ'² − σσ'') = σ³℘`, `W₂ = −(2σ'³ − 3σσ'σ'' + σ²σ''') = σ³℘'` (`ellW`).

A monomial (`Mono D`) is `Π a_i^{α_i} · Π exp(b_i)^{β_i} · Π_j Π_t W_{j,t}^{γ_{j,t}}` with
`Σ_t γ_{j,t} = D` for every `j` (multihomogeneous of degree `D` in each elliptic block, as in W83's
Prop. 2.4 with Serre's embedding of `E₁ × ⋯ × E_m`).

**Common multiplier.** For a period `ω ∈ Ω(G) = Per Ls`, every monomial satisfies
`M(p + ω) = mult(ω, p) · M(p)` with `mult(ω, p) = Π_j (ε_j(ω_j) e^{η_j(ω_j)(p_j + ω_j/2)})^{3D}`
(`sigma_add`; the `G_m` multiplier is `1`, `G_a` components of periods vanish), and
`‖mult(ω, p)‖ ≤ exp (3 D C (‖p‖ + ‖ω‖)²)` with `C` depending only on the lattices.

* `LSG.Aux.ellW`, `LSG.Aux.ellW_add`: quasi-periodicity of the elliptic coordinates.
* `LSG.Aux.exists_eta_bound`: `‖η(λ)‖ ≤ C ‖λ‖` on the lattice.
* `LSG.Aux.Mono`, `LSG.Aux.Mono.eval`, `LSG.Aux.Mono.eval_add_per`, `LSG.Aux.norm_expMult_le`.
* `LSG.Aux.exists_qp_mono`: (QP) in the form of `LSG.Aux.prop21Lin` for `ψ_l = M_l ∘ ℓ`, `ℓ` a
  linear map `ℂⁿ → T_G` (parametrising `V`), periods `ω_i` with `ℓ ω_i ∈ Ω(G)`.
-/

open Complex Finset LSG.Weierstrass LSG.W88 PeriodPair

noncomputable section

namespace LSG.Aux

/-! ### Elliptic coordinates -/

/-- The entire coordinates `(σ³, σ³℘, σ³℘')` of the Weierstrass embedding. -/
def ellW (L : PeriodPair) : Fin 3 → ℂ → ℂ :=
  ![fun z => sigma L z ^ 3,
    fun z => sigma L z * (deriv (sigma L) z ^ 2 - sigma L z * deriv (deriv (sigma L)) z),
    fun z => -(2 * deriv (sigma L) z ^ 3 -
      3 * sigma L z * deriv (sigma L) z * deriv (deriv (sigma L)) z +
      sigma L z ^ 2 * deriv (deriv (deriv (sigma L))) z)]

lemma differentiable_ellW (L : PeriodPair) (t : Fin 3) : Differentiable ℂ (ellW L t) := by
  have d0 := differentiable_sigma L
  have d1 := differentiable_deriv_sigma L
  have d2 := differentiable_deriv_deriv_sigma L
  have d3 := differentiable_deriv_deriv_deriv_sigma L
  fin_cases t
  · exact d0.pow 3
  · exact d0.mul ((d1.pow 2).sub (d0.mul d2))
  · exact ((((d1.pow 3).const_mul 2).sub (((d0.const_mul 3).mul d1).mul d2)).add
      ((d0.pow 2).mul d3)).neg

/-- The multiplier of `σ`: `σ(z + λ) = sigmaMult λ z · σ(z)`. -/
def sigmaMult (L : PeriodPair) (lam z : ℂ) : ℂ := sigmaSign L lam * exp (eta L lam * (z + lam / 2))

lemma ellW_eq_off (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ellW L 1 z = sigma L z ^ 3 * ℘[L] z ∧ ellW L 2 z = sigma L z ^ 3 * ℘'[L] z := by
  have hs : sigma L z ^ 3 ≠ 0 := pow_ne_zero _ (sigma_ne_zero L hz)
  constructor
  · rw [weierstrassP_eq_sigma_cube L hz, mul_div_cancel₀ _ hs]; rfl
  · rw [derivWeierstrassP_eq_sigma_cube L hz, mul_div_cancel₀ _ hs]; rfl

/-- **Quasi-periodicity of the elliptic coordinates.** -/
theorem ellW_add (L : PeriodPair) {lam : ℂ} (hlam : lam ∈ L.lattice) (t : Fin 3) (z : ℂ) :
    ellW L t (z + lam) = sigmaMult L lam z ^ 3 * ellW L t z := by
  have hcont : Continuous fun z => ellW L t (z + lam) :=
    (differentiable_ellW L t).continuous.comp (continuous_id.add continuous_const)
  have hcont' : Continuous fun z => sigmaMult L lam z ^ 3 * ellW L t z := by
    unfold sigmaMult
    exact ((continuous_const.mul ((continuous_const.mul
      (continuous_id.add continuous_const)).cexp)).pow 3).mul (differentiable_ellW L t).continuous
  have hd : Dense ((L.lattice : Set ℂ)ᶜ) := (countable_lattice L).dense_compl ℂ
  refine congrFun (hcont.ext_on hd hcont' fun w hw => ?_) z
  clear z
  have hz' : w ∉ L.lattice := hw
  set z := w
  have hzl : z + lam ∉ L.lattice := add_notMem_lattice L hz' hlam
  have hσ := sigma_add L hlam z
  simp only
  fin_cases t
  · change sigma L (z + lam) ^ 3 = sigmaMult L lam z ^ 3 * sigma L z ^ 3
    rw [hσ, sigmaMult]; ring
  · change ellW L 1 (z + lam) = sigmaMult L lam z ^ 3 * ellW L 1 z
    rw [(ellW_eq_off L hzl).1, (ellW_eq_off L hz').1, hσ,
      L.weierstrassP_add_coe z ⟨lam, hlam⟩, sigmaMult]; ring
  · change ellW L 2 (z + lam) = sigmaMult L lam z ^ 3 * ellW L 2 z
    rw [(ellW_eq_off L hzl).2, (ellW_eq_off L hz').2, hσ,
      L.derivWeierstrassP_add_coe z ⟨lam, hlam⟩, sigmaMult]; ring

/-- `η` grows linearly on the lattice. -/
theorem exists_eta_bound (L : PeriodPair) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ L.lattice, ‖eta L lam‖ ≤ C * ‖lam‖ := by
  let c : Fin 2 → (ℂ →L[ℝ] ℝ) := fun i ↦ LinearMap.toContinuousLinearMap (L.basis.coord i)
  refine ⟨‖c 0‖ * ‖eta L L.ω₁‖ + ‖c 1‖ * ‖eta L L.ω₂‖, by positivity, fun lam hlam => ?_⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hlam
  have hm1 : (m : ℂ) * L.ω₁ ∈ L.lattice := by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem m L.ω₁_mem_lattice
  have hn1 : (n : ℂ) * L.ω₂ ∈ L.lattice := by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem n L.ω₂_mem_lattice
  have hrepr : ∀ i, L.basis.repr ((m : ℂ) * L.ω₁ + n * L.ω₂) i = ![(m : ℝ), (n : ℝ)] i := by
    have : (m : ℂ) * L.ω₁ + n * L.ω₂ = ∑ i, ![(m : ℝ), (n : ℝ)] i • L.basis i := by
      simp [Fin.sum_univ_two, Complex.real_smul]
    intro i
    rw [this, L.basis.repr_sum_self]
  have hc : ∀ i, (c i) ((m : ℂ) * L.ω₁ + n * L.ω₂) = ![(m : ℝ), (n : ℝ)] i := fun i => by
    rw [← hrepr i]; rfl
  have ha : |(m : ℝ)| ≤ ‖c 0‖ * ‖(m : ℂ) * L.ω₁ + n * L.ω₂‖ := by
    have := (c 0).le_opNorm ((m : ℂ) * L.ω₁ + n * L.ω₂)
    rwa [hc 0, Real.norm_eq_abs] at this
  have hb : |(n : ℝ)| ≤ ‖c 1‖ * ‖(m : ℂ) * L.ω₁ + n * L.ω₂‖ := by
    have := (c 1).le_opNorm ((m : ℂ) * L.ω₁ + n * L.ω₂)
    rwa [hc 1, Real.norm_eq_abs] at this
  rw [eta_add L hm1 hn1, eta_zsmul L L.ω₁_mem_lattice, eta_zsmul L L.ω₂_mem_lattice]
  calc ‖(m : ℂ) * eta L L.ω₁ + n * eta L L.ω₂‖
      ≤ |(m : ℝ)| * ‖eta L L.ω₁‖ + |(n : ℝ)| * ‖eta L L.ω₂‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ ‖c 0‖ * ‖(m : ℂ) * L.ω₁ + n * L.ω₂‖ * ‖eta L L.ω₁‖ +
          ‖c 1‖ * ‖(m : ℂ) * L.ω₁ + n * L.ω₂‖ * ‖eta L L.ω₂‖ := by gcongr
    _ = _ := by ring

lemma norm_sigmaSign (L : PeriodPair) (lam : ℂ) : ‖sigmaSign L lam‖ = 1 := by
  unfold sigmaSign; split_ifs <;> simp

lemma norm_sigmaMult_le (L : PeriodPair) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ lam ∈ L.lattice, ‖eta L lam‖ ≤ C * ‖lam‖) {lam : ℂ} (hlam : lam ∈ L.lattice) (z : ℂ) :
    ‖sigmaMult L lam z‖ ≤ Real.exp (C * (‖z‖ + ‖lam‖) ^ 2) := by
  unfold sigmaMult
  rw [norm_mul, norm_sigmaSign, one_mul]
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_mul]
  have h1 : ‖z + lam / 2‖ ≤ ‖z‖ + ‖lam‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg lam]
  calc ‖eta L lam‖ * ‖z + lam / 2‖ ≤ (C * ‖lam‖) * (‖z‖ + ‖lam‖) := by
        gcongr; exact hC lam hlam
    _ ≤ C * (‖z‖ + ‖lam‖) ^ 2 := by
        have : ‖lam‖ ≤ ‖z‖ + ‖lam‖ := by linarith [norm_nonneg z]
        have h0 : 0 ≤ ‖z‖ + ‖lam‖ := by positivity
        calc C * ‖lam‖ * (‖z‖ + ‖lam‖) ≤ C * (‖z‖ + ‖lam‖) * (‖z‖ + ‖lam‖) := by gcongr
          _ = C * (‖z‖ + ‖lam‖) ^ 2 := by ring

/-! ### Monomials in the coordinates of `exp_G` -/

/-- A monomial in the coordinates of `exp_G`, multihomogeneous of degree `D` in each elliptic
block. -/
structure Mono (d0 d1 m D : ℕ) where
  /-- exponents of the `G_a` coordinates -/
  α : Fin d0 → ℕ
  /-- exponents of the `G_m` coordinates -/
  β : Fin d1 → ℕ
  /-- exponents of the elliptic coordinates `W_{j,0}, W_{j,1}, W_{j,2}` -/
  γ : Fin m → Fin 3 → ℕ
  hγ : ∀ j, ∑ t, γ j t = D

variable {d0 d1 m D : ℕ}

lemma differentiable_fprod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (u : Finset ι) (g : ι → E → ℂ) (h : ∀ i ∈ u, Differentiable ℂ (g i)) :
    Differentiable ℂ (fun x => ∏ i ∈ u, g i x) := fun x => by
  classical
  exact (HasFDerivAt.finsetProd fun i hi => (h i hi x).hasFDerivAt).differentiableAt

/-- Evaluation of a monomial at a point of the tangent space. -/
def Mono.eval (Ls : Fin m → PeriodPair) (μ : Mono d0 d1 m D) (p : Tan d0 d1 m) : ℂ :=
  (∏ i, p.1 i ^ μ.α i) * (∏ i, exp (p.2.1 i) ^ μ.β i) *
    ∏ j, ∏ t, ellW (Ls j) t (p.2.2 j) ^ μ.γ j t

/-- The common multiplier of the monomials of degree `D` under the period `ω`. -/
def expMult (Ls : Fin m → PeriodPair) (D : ℕ) (ω p : Tan d0 d1 m) : ℂ :=
  ∏ j, sigmaMult (Ls j) (ω.2.2 j) (p.2.2 j) ^ (3 * D)

lemma differentiable_eval (Ls : Fin m → PeriodPair) (μ : Mono d0 d1 m D) :
    Differentiable ℂ (μ.eval Ls) := by
  unfold Mono.eval
  refine (Differentiable.mul ?_ ?_).mul ?_
  · refine differentiable_fprod _ _ fun i _ => ?_
    fun_prop
  · refine differentiable_fprod _ _ fun i _ => ?_
    fun_prop
  · refine differentiable_fprod _ _ fun j _ => ?_
    refine differentiable_fprod _ _ fun t _ => ?_
    exact ((differentiable_ellW (Ls j) t).comp
      (by fun_prop : Differentiable ℂ fun p : Tan d0 d1 m => p.2.2 j)).pow _

/-- **Common multiplier under periods of `G`.** -/
theorem Mono.eval_add_per (Ls : Fin m → PeriodPair) (μ : Mono d0 d1 m D) {ω : Tan d0 d1 m}
    (hω : ω ∈ Per Ls) (p : Tan d0 d1 m) :
    μ.eval Ls (p + ω) = expMult Ls D ω p * μ.eval Ls p := by
  obtain ⟨h0, h1, h2⟩ := hω
  unfold Mono.eval expMult
  have hA : ∏ i, (p + ω).1 i ^ μ.α i = ∏ i, p.1 i ^ μ.α i := by
    simp [h0]
  have hB : ∏ i, exp ((p + ω).2.1 i) ^ μ.β i = ∏ i, exp (p.2.1 i) ^ μ.β i := by
    refine prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := h1 i
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hk, Complex.exp_add]
    rw [show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hC : ∏ j, ∏ t, ellW (Ls j) t ((p + ω).2.2 j) ^ μ.γ j t =
      (∏ j, sigmaMult (Ls j) (ω.2.2 j) (p.2.2 j) ^ (3 * D)) *
        ∏ j, ∏ t, ellW (Ls j) t (p.2.2 j) ^ μ.γ j t := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    simp only [Prod.snd_add, Pi.add_apply, ellW_add (Ls j) (h2 j), mul_pow, prod_mul_distrib,
      ← pow_mul, prod_pow_eq_pow_sum, ← mul_sum, μ.hγ j]
  rw [hA, hB, hC]; ring

/-- The multiplier bound. -/
theorem norm_expMult_le (Ls : Fin m → PeriodPair) {C : Fin m → ℝ} (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j, ∀ lam ∈ (Ls j).lattice, ‖eta (Ls j) lam‖ ≤ C j * ‖lam‖) {ω : Tan d0 d1 m}
    (hω : ω ∈ Per Ls) (p : Tan d0 d1 m) :
    ‖expMult Ls D ω p‖ ≤ Real.exp (3 * D * (∑ j, C j) * (‖p‖ + ‖ω‖) ^ 2) := by
  unfold expMult
  rw [norm_prod]
  have hj : ∀ j, ‖sigmaMult (Ls j) (ω.2.2 j) (p.2.2 j) ^ (3 * D)‖ ≤
      Real.exp (3 * D * C j * (‖p‖ + ‖ω‖) ^ 2) := by
    intro j
    rw [norm_pow]
    have h1 := norm_sigmaMult_le (Ls j) (hC0 j) (hC j) (hω.2.2 j) (p.2.2 j)
    have hpj : ‖p.2.2 j‖ ≤ ‖p‖ :=
      (norm_le_pi_norm _ j).trans ((norm_snd_le _).trans (norm_snd_le _))
    have hωj : ‖ω.2.2 j‖ ≤ ‖ω‖ :=
      (norm_le_pi_norm _ j).trans ((norm_snd_le _).trans (norm_snd_le _))
    have h2 : Real.exp (C j * (‖p.2.2 j‖ + ‖ω.2.2 j‖) ^ 2) ≤ Real.exp (C j * (‖p‖ + ‖ω‖) ^ 2) := by
      gcongr
      · exact hC0 j
    calc ‖sigmaMult (Ls j) (ω.2.2 j) (p.2.2 j)‖ ^ (3 * D)
        ≤ Real.exp (C j * (‖p‖ + ‖ω‖) ^ 2) ^ (3 * D) := by gcongr; exact h1.trans h2
      _ = Real.exp (3 * D * C j * (‖p‖ + ‖ω‖) ^ 2) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc ∏ j, ‖sigmaMult (Ls j) (ω.2.2 j) (p.2.2 j) ^ (3 * D)‖
      ≤ ∏ j, Real.exp (3 * D * C j * (‖p‖ + ‖ω‖) ^ 2) :=
        prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => hj j
    _ = Real.exp (3 * D * (∑ j, C j) * (‖p‖ + ‖ω‖) ^ 2) := by
        rw [← Real.exp_sum]; congr 1; rw [mul_sum, sum_mul]

/-- **Concrete (QP).** For `ℓ : ℂⁿ → T_G` linear and periods `ω_i` with `ℓ ω_i ∈ Ω(G)`, the
functions `ψ_l = M_l ∘ ℓ` (monomials of degree `D` in each elliptic block) have a common
multiplier under `Σ k_i ω_i`, bounded by `exp (b (‖z‖ + ‖Σ k_i ω_i‖)²)` with `b = 3 D C ‖ℓ‖²`,
`C` depending only on the lattices. This is the hypothesis of `LSG.Aux.prop21Lin`. -/
theorem exists_qp_mono (Ls : Fin m → PeriodPair) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n κ L : ℕ) (ℓ : (Fin n → ℂ) →L[ℂ] Tan d0 d1 m)
      (ω : Fin κ → (Fin n → ℂ)), (∀ i, ℓ (ω i) ∈ Per Ls) → ∀ (μs : Fin L → Mono d0 d1 m D),
      ∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ mu : ℂ,
        ‖mu‖ ≤ Real.exp (3 * D * C * ‖ℓ‖ ^ 2 * (‖z‖ + ‖∑ i, (k i : ℂ) • ω i‖) ^ 2) ∧
        ∀ l, (μs l).eval Ls (ℓ (z + ∑ i, (k i : ℂ) • ω i)) = mu * (μs l).eval Ls (ℓ z) := by
  choose C hC0 hC using fun j => exists_eta_bound (Ls j)
  refine ⟨∑ j, C j, sum_nonneg fun j _ => hC0 j, fun n κ L ℓ ω hω μs k z => ?_⟩
  set w : Fin n → ℂ := ∑ i, (k i : ℂ) • ω i
  have hw : ℓ w ∈ Per Ls := by
    simp only [w, map_sum, map_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have : (k i : ℂ) • ℓ (ω i) = (k i) • ℓ (ω i) := by
      rw [← Int.cast_smul_eq_zsmul ℂ]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (hω i) _
  refine ⟨expMult Ls D (ℓ w) (ℓ z), ?_, fun l => ?_⟩
  · refine (norm_expMult_le Ls hC0 hC hw (ℓ z)).trans (Real.exp_le_exp.mpr ?_)
    have h1 : ‖ℓ z‖ + ‖ℓ w‖ ≤ ‖ℓ‖ * (‖z‖ + ‖w‖) := by
      rw [mul_add]; exact add_le_add (ℓ.le_opNorm z) (ℓ.le_opNorm w)
    have h0 : 0 ≤ ‖ℓ z‖ + ‖ℓ w‖ := by positivity
    have hS : 0 ≤ 3 * (D : ℝ) * ∑ j, C j := by
      have := sum_nonneg fun j (_ : j ∈ univ) => hC0 j
      positivity
    calc 3 * D * (∑ j, C j) * (‖ℓ z‖ + ‖ℓ w‖) ^ 2
        ≤ 3 * D * (∑ j, C j) * (‖ℓ‖ * (‖z‖ + ‖w‖)) ^ 2 := by gcongr
      _ = 3 * D * (∑ j, C j) * ‖ℓ‖ ^ 2 * (‖z‖ + ‖w‖) ^ 2 := by ring
  · rw [map_add]
    exact (μs l).eval_add_per Ls hw (ℓ z)

end LSG.Aux
