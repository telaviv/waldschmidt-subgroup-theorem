/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopy

/-!
# Verbatim copy of `lean_mstar`'s model `gmXG` and its hypothesis `Thm11KappaMXG` (Theorem MX)

Sources (read 2026-10-31): `lean_mstar/CM4E/Defs.lean` (`varpi`, `omegaRho`), `CM4E/Lattice.lean`
(`lemniscatic`, `etaLem`), `CM4E/MX.lean` (`r3`, `rho`, `rhoBar`, `equianharmonic`, `etaRho`,
`etaR`,
`LogNat`), `CM4E/Ext/Weierstrass/ZetaDef.lean` (`zetaSummand`, `zeta`), `CM4E/Gen/Basis.lean`
(`theta`, `Kspan`,
`IsAdaptedFieldBasis`), `CM4E/Gen/Frame.lean` (`dotL`), `CM4E/Gen/MXGen.lean` (`TXG`, …, `gmXG`,
`Thm11KappaMXG`). The definition bodies are copied verbatim; only the namespace is
`LSG.W88.MStarCopy`
(with `CM4E.Ext.Weierstrass.zeta` copied as `MStarCopy.Ext.zeta`). Proofs of the `Prop` fields of
the period
pairs are copied too (they are irrelevant for definitional equality). `GroupModel`,
`HyperplaneKappa` are the
copies of `MStarCopy.lean`. Checked: `LSG.W88.MStarCopy.Thm11KappaMXG ↔ CM4E.Gen.Thm11KappaMXG` is
`Iff.rfl`
in the `lean_mstar` environment. Do not edit except to re-sync with the source.
-/

open Complex Module Real

namespace LSG.W88.MStarCopy

/-! ### `CM4E/Defs.lean` -/

noncomputable def varpi : ℝ := Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt (2 * π))

noncomputable def omegaRho : ℝ := Real.Gamma (1 / 3) ^ 3 / ((2 : ℝ) ^ ((4 : ℝ) / 3) * π)

/-! ### `CM4E/Lattice.lean` -/

lemma varpi_pos : 0 < varpi := by
  unfold varpi
  have h1 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma varpi_ne_zero : varpi ≠ 0 := varpi_pos.ne'

noncomputable def etaLem (m n : ℤ) : ℂ := ((m : ℂ) - n * I) * (Real.pi / varpi)

lemma linearIndependent_varpi : LinearIndependent ℝ ![(varpi : ℂ), I * varpi] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  exact ⟨by simpa [varpi_ne_zero] using hre, by simpa [varpi_ne_zero] using him⟩

noncomputable def lemniscatic : PeriodPair where
  ω₁ := varpi
  ω₂ := I * varpi
  indep := linearIndependent_varpi

/-! ### `CM4E/Ext/Weierstrass/ZetaDef.lean` -/

namespace Ext

noncomputable def zetaSummand (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2

noncomputable def zeta (L : PeriodPair) (z : ℂ) : ℂ := ∑' l : L.lattice, zetaSummand l z

end Ext

/-! ### `CM4E/MX.lean` -/

lemma omegaRho_pos : 0 < omegaRho := by
  unfold omegaRho
  have h1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ ((4 : ℝ) / 3) := by positivity
  have h3 := Real.pi_pos
  positivity

noncomputable def r3 : ℂ := (Real.sqrt 3 : ℂ)

noncomputable def rho : ℂ := (-1 + I * r3) / 2

noncomputable def rhoBar : ℂ := (-1 - I * r3) / 2

lemma linearIndependent_rho : LinearIndependent ℝ ![(omegaRho : ℂ), rho * omegaRho] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hO := omegaRho_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have e1 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).im = t * (Real.sqrt 3 / 2 * omegaRho) := by
    simp [rho, r3]
  have e2 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).re = s * omegaRho - t * (omegaRho / 2) := by
    simp [rho, r3]; ring
  rw [e1] at him; rw [e2] at hre
  simp only [Complex.zero_im, Complex.zero_re] at him hre
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exfalso; have : 0 < Real.sqrt 3 / 2 * omegaRho := by positivity
      linarith
  subst ht
  refine ⟨?_, rfl⟩
  rcases mul_eq_zero.mp (by linarith : s * omegaRho = 0) with h1 | h1
  · exact h1
  · linarith

noncomputable def equianharmonic : PeriodPair where
  ω₁ := omegaRho
  ω₂ := rho * omegaRho
  indep := linearIndependent_rho

noncomputable def etaRho : ℂ := 2 * Real.pi / (r3 * omegaRho)

noncomputable def etaR (m n : ℤ) : ℂ := ((m : ℂ) + n * rhoBar) * etaRho

def LogNat (L : PeriodPair) (eta : ℤ → ℤ → ℂ) (z w : ℂ) : Prop :=
  (∃ m n : ℤ, z = m * L.ω₁ + n * L.ω₂ ∧ IsAlgebraic ℚ (w - eta m n)) ∨
    (z ∉ L.lattice ∧ IsAlgebraic ℚ (L.weierstrassP z) ∧ IsAlgebraic ℚ (L.derivWeierstrassP z) ∧
      IsAlgebraic ℚ (w - Ext.zeta L z))

/-! ### `CM4E/Gen/Basis.lean` -/

def theta (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Fin r × Fin 2 → ℂ :=
  fun p => if p.2 = 0 then b p.1 else α * b p.1

noncomputable def Kspan (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (Set.range (theta α b))

structure IsAdaptedFieldBasis (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Prop where
  indep : LinearIndependent ℚ (theta α b)
  one_mem : (1 : ℂ) ∈ Kspan α b
  mul_mem : ∀ x ∈ Kspan α b, ∀ y ∈ Kspan α b, x * y ∈ Kspan α b
  inv_mem : ∀ x ∈ Kspan α b, x⁻¹ ∈ Kspan α b
  alg : ∀ j, IsAlgebraic ℚ (b j)

/-! ### `CM4E/Gen/Frame.lean` -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def dotL (θ : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ j, θ j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

end Frame

/-! ### `CM4E/Gen/MXGen.lean` -/

variable {r : ℕ}

abbrev TXG (r : ℕ) := ℂ × (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) × ℂ

variable (b : Fin r → ℂ)

noncomputable def psiX1 : TXG r →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ _ _ + dotL (theta I b) ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _) +
    dotL (theta I b) ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _)

noncomputable def psiX2 : TXG r →ₗ[ℂ] ℂ where
  toFun v := v.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def gXI (h : Fin r × Fin 2) (z w : ℂ) : TXG r :=
  (0, Pi.single h z, 0, theta I b h * w)
noncomputable def gXR (h : Fin r × Fin 2) (z w : ℂ) : TXG r :=
  (0, 0, Pi.single h z, theta I b h * w)
noncomputable def gXA (h : Fin r × Fin 2) (a t : ℂ) : TXG r :=
  (theta I b h * a, 0, 0, theta I b h * t)

def lamGenX : Set (TXG r) :=
  {v | ∃ h z w, LogNat lemniscatic etaLem z w ∧ v = gXI b h z w} ∪
    {v | ∃ h z w, LogNat equianharmonic etaR z w ∧ v = gXR b h z w} ∪
    {v | ∃ h a t, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ t ∧ v = gXA b h a t}

noncomputable def GX1 (j : Fin r × Fin 2) : TXG r := gXI b j varpi (Real.pi / varpi)
noncomputable def GX2 (j : Fin r × Fin 2) : TXG r := gXI b j (I * varpi) (-I * (Real.pi / varpi))
noncomputable def HX1 (j : Fin r × Fin 2) : TXG r := gXR b j omegaRho etaRho
noncomputable def HX2 (j : Fin r × Fin 2) : TXG r := gXR b j (rho * omegaRho) (rhoBar * etaRho)

noncomputable def perXG : Submodule ℚ (TXG r) :=
  Submodule.span ℚ (Set.range (GX1 b) ∪ Set.range (GX2 b) ∪ Set.range (HX1 b) ∪ Set.range (HX2 b))

def algXG (v : TXG r) : Prop :=
  IsAlgebraic ℚ v.1 ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.2.2.1 j)) ∧
    IsAlgebraic ℚ v.2.2.2

noncomputable def gmXG : GroupModel (TXG r) where
  d₁ := 0
  d₂ := 2 * Fintype.card (Fin r × Fin 2) + 1
  alg := algXG
  lam := (Submodule.span ℚ (lamGenX b) : Set (TXG r))
  per := perXG b
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algXG x ∧ (psiX1 b x ≠ 0 ∨ psiX2 (r := r) x ≠ 0)

def Thm11KappaMXG : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ →
    IsAlgebraic ℚ equianharmonic.g₂ → IsAlgebraic ℚ equianharmonic.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b → HyperplaneKappa (gmXG b)

end LSG.W88.MStarCopy
