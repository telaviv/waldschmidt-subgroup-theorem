/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.CM.Rot
import LSG.W88.MStarCopyMX

/-!
# The two CM lattices of Theorem MX: `ϖℤ[i]` and `Ω_ρℤ[ρ]` (lean_mstar's definitions)

For the verbatim copies `lemniscatic = (ϖ, iϖ)` and `equianharmonic = (Ω_ρ, ρΩ_ρ)` of
`LSG.W88.MStarCopy`:
* `cmLem : CMData lemniscatic I`, `cmRho : CMData equianharmonic rho`;
* quasi-periods (Legendre + rotation): `η(ϖ) = π/ϖ`, `η(iϖ) = −iπ/ϖ`, `η(Ω_ρ) = etaRho`,
  `η(ρΩ_ρ) = ρ̄ etaRho`, and `η(mω₁ + nω₂) = etaLem m n`, `= etaR m n` (`eta_lem`, `eta_rho`);
* `ext_zeta`: lean_mstar's copy `Ext.zeta` of `ζ` is LSG's `ζ` (definitionally);
* `sqrt3_I_mul_mem`: `√3 i · Ω_ρℤ[ρ] ⊆ Ω_ρℤ[ρ]` (`√3 i = 2ρ + 1`), used to split abelian
  subvarieties of `E_i^n × E_ρ^n`.
-/

open Complex LSG.Weierstrass PeriodPair LSG.W88.MStarCopy

namespace LSG.CM

/-! ### `ϖℤ[i]` -/

lemma varpi_ne_zero' : (varpi : ℂ) ≠ 0 := by exact_mod_cast varpi_ne_zero

lemma I_mul_mem_lem {x : ℂ} (hx : x ∈ lemniscatic.lattice) : I * x ∈ lemniscatic.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨-n, m, ?_⟩
  simp only [lemniscatic]; push_cast; ring_nf; rw [Complex.I_sq]; ring

lemma isAlgebraic_I : IsAlgebraic ℚ I :=
  ⟨Polynomial.X ^ 2 + Polynomial.C 1, (Polynomial.monic_X_pow_add_C 1 two_ne_zero).ne_zero,
    by simp⟩

lemma cmLem : CMData lemniscatic I where
  unit := ⟨I_ne_zero, fun x hx => I_mul_mem_lem hx, fun x hx => by
    rw [Complex.inv_I, neg_mul]; exact neg_mem (I_mul_mem_lem hx)⟩
  hω := rfl
  conj_eq := by rw [Complex.conj_I, Complex.inv_I]
  im_pos := by simp
  alg := isAlgebraic_I

/-- `η(ϖ) = π/ϖ` (Legendre). -/
theorem eta_varpi : eta lemniscatic lemniscatic.ω₁ = (Real.pi / varpi : ℝ) := by
  have h := cmLem.eta_one_mul
  rw [Complex.inv_I] at h
  have hv := varpi_ne_zero'
  change eta lemniscatic (varpi : ℂ) * (varpi : ℂ) * (I - -I) = _ at h
  change eta lemniscatic (varpi : ℂ) = _
  push_cast
  rw [eq_div_iff hv]
  linear_combination (-I / 2) * h + (eta lemniscatic (varpi : ℂ) * varpi - Real.pi) * I_sq

/-- `η(mϖ + n iϖ) = etaLem m n`. -/
theorem eta_lem (m n : ℤ) :
    eta lemniscatic (m * lemniscatic.ω₁ + n * lemniscatic.ω₂) = etaLem m n := by
  have hx : (m : ℂ) * lemniscatic.ω₁ + n * lemniscatic.ω₂ ∈ lemniscatic.lattice :=
    PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
  rw [cmLem.eta_eq_conj hx, eta_varpi]
  have hv := varpi_ne_zero'
  have : ((m : ℂ) * lemniscatic.ω₁ + n * lemniscatic.ω₂) / lemniscatic.ω₁ = m + n * I := by
    change ((m : ℂ) * varpi + n * (I * varpi)) / varpi = _
    field_simp
  rw [this, etaLem, map_add, map_mul, map_intCast, map_intCast, Complex.conj_I]
  push_cast
  ring

/-! ### `Ω_ρℤ[ρ]` -/

lemma omegaRho_ne_zero' : (omegaRho : ℂ) ≠ 0 := by exact_mod_cast omegaRho_pos.ne'

lemma r3_sq : r3 ^ 2 = 3 := by
  simp [r3, ← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma r3_ne_zero : r3 ≠ 0 := by
  intro h; have := r3_sq; rw [h] at this; norm_num at this

lemma rho_sq : rho ^ 2 = -1 - rho := by simp only [rho]; ring_nf; rw [Complex.I_sq, r3_sq]; ring

lemma rho_mul_mem {x : ℂ} (hx : x ∈ equianharmonic.lattice) : rho * x ∈ equianharmonic.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨-n, m - n, ?_⟩
  simp only [equianharmonic]; push_cast
  linear_combination (-(n : ℂ) * omegaRho) * rho_sq

lemma rho_ne_zero : rho ≠ 0 := by
  intro h; have := rho_sq; rw [h] at this; norm_num at this

lemma conj_r3 : starRingEnd ℂ r3 = r3 := by simp [r3, Complex.conj_ofReal]

lemma conj_rho : starRingEnd ℂ rho = rhoBar := by
  simp only [rho, rhoBar, map_div₀, map_add, map_neg, map_one, map_mul, Complex.conj_I,
    Complex.conj_ofNat, conj_r3]
  ring

lemma rho_inv : rho⁻¹ = rhoBar := by
  apply inv_eq_of_mul_eq_one_right
  simp only [rho, rhoBar]
  linear_combination (-(r3 ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * r3_sq

lemma rhoBar_eq : rhoBar = -1 - rho := by simp only [rho, rhoBar]; ring

lemma cmRho : CMData equianharmonic rho where
  unit := ⟨rho_ne_zero, fun x hx => rho_mul_mem hx, fun x hx => by
    rw [rho_inv, rhoBar_eq, sub_mul, neg_mul, one_mul]
    exact sub_mem (neg_mem hx) (rho_mul_mem hx)⟩
  hω := rfl
  conj_eq := by rw [conj_rho, rho_inv]
  im_pos := by
    simp [rho, r3]
  alg := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C 1, ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.eval 0) h
      simp at this
    · simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
      linear_combination rho_sq

/-- `η(Ω_ρ) = 2π/(√3 Ω_ρ)` (Legendre). -/
theorem eta_omegaRho : eta equianharmonic equianharmonic.ω₁ = etaRho := by
  have h := cmRho.eta_one_mul
  rw [rho_inv] at h
  have hO := omegaRho_ne_zero'
  have hr := r3_ne_zero
  change eta equianharmonic (omegaRho : ℂ) * (omegaRho : ℂ) * (rho - rhoBar) = _ at h
  change eta equianharmonic (omegaRho : ℂ) = _
  have hd : rho - rhoBar = I * r3 := by simp only [rho, rhoBar]; ring
  rw [hd] at h
  rw [etaRho, eq_div_iff (mul_ne_zero hr hO)]
  linear_combination (-I) * h +
    (eta equianharmonic (omegaRho : ℂ) * (r3 * omegaRho) - 2 * Real.pi) * I_sq

/-- `η(mΩ_ρ + nρΩ_ρ) = etaR m n`. -/
theorem eta_rho (m n : ℤ) :
    eta equianharmonic (m * equianharmonic.ω₁ + n * equianharmonic.ω₂) = etaR m n := by
  have hx : (m : ℂ) * equianharmonic.ω₁ + n * equianharmonic.ω₂ ∈ equianharmonic.lattice :=
    PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
  rw [cmRho.eta_eq_conj hx, eta_omegaRho]
  have hO := omegaRho_ne_zero'
  have : ((m : ℂ) * equianharmonic.ω₁ + n * equianharmonic.ω₂) / equianharmonic.ω₁ =
      m + n * rho := by
    change ((m : ℂ) * omegaRho + n * (rho * omegaRho)) / omegaRho = _
    field_simp
  rw [this, etaR, map_add, map_mul, map_intCast, map_intCast, conj_rho]

/-- `√3 i = 2ρ + 1` maps `Ω_ρℤ[ρ]` into itself. -/
lemma sqrt3_I_mul_mem {x : ℂ} (hx : x ∈ equianharmonic.lattice) :
    ((Real.sqrt 3 : ℝ) : ℂ) * I * x ∈ equianharmonic.lattice := by
  have : ((Real.sqrt 3 : ℝ) : ℂ) * I * x = rho * x + rho * x + x := by
    simp only [rho, r3]; ring
  rw [this]
  exact add_mem (add_mem (rho_mul_mem hx) (rho_mul_mem hx)) hx

/-! ### lean_mstar's `ζ` -/

/-- lean_mstar's copy of `ζ` is LSG's `ζ`. -/
lemma ext_zeta (L : PeriodPair) (z : ℂ) : Ext.zeta L z = LSG.Weierstrass.zeta L z := rfl

end LSG.CM
