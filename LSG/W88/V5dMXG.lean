/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dIso
import LSG.W88.MStarCopyMX

/-!
# Theorem MX's hypothesis `Thm11KappaMXG` from `Theorem41VecLA`: the instance, and the CM inputs

`G'' = G_a × G_ℓ` of `lean_mstar`'s `gmXG b` is directly in the class `𝒞`: `d₀ = 1`, `d₁ = 0`,
curves
`(E_i)^n ++ (E_ρ)^n` (`n = |Fin r × Fin 2|`, `mxLs`), `r = 1`, `M = (θᵀ, θᵀ)` (`mxM`). The
isomorphism
`mxIota : TanV 1 0 (n + n) 1 ≅ TXG r` reindexes the elliptic coordinates.

`thm11KappaMXG_of_cm`: `Theorem41VecLA` and five CM inputs give `MStarCopy.Thm11KappaMXG`. Proved
here: the
coordinates, `(i)` algebraicity, `(iv)` `d₁ = 0`, `d₂ = 2n + 1 = m + r`, algebraicity of `M`, the
invariants,
and the passage from generators to `span_ℚ lamGenX` (common denominators). The CM inputs
(hypotheses,
true by VECEXT.md §2.3/§2.6, not yet in Lean):
* `hLA`, `hPT`: `LiftAlg`, `PerTanRat` for `(E_i)^n × (E_ρ)^n`;
* `hΛ`: an additive subgroup of `Λ(G)` containing `ι⁻¹(lamGenX)` (`ζ` addition theorem and the
  quasi-period
  values `etaLem`, `etaR` for Lean's `ζ`);
* `hper`: the period generators `GX1, …, HX2` lie in `ι(span_ℚ Ω)` (quasi-period values);
* `hsub`: `ι(T_H) ∈ gmXG.sub` for nonzero members (splitting `B = B_i × B_ρ`, Lemma K).
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

/-- `n = |Fin r × Fin 2|`. -/
abbrev mxN (r : ℕ) : ℕ := Fintype.card (Fin r × Fin 2)

/-- An enumeration of `Fin r × Fin 2`. -/
noncomputable def mxE (r : ℕ) : Fin r × Fin 2 ≃ Fin (mxN r) := Fintype.equivFin _

/-- The curves `(E_i)^n ++ (E_ρ)^n`. -/
noncomputable def mxLs (r : ℕ) : Fin (mxN r + mxN r) → PeriodPair :=
  Fin.append (fun _ => lemniscatic) (fun _ => equianharmonic)

/-- `M = (θᵀ, θᵀ)`. -/
noncomputable def mxM {r : ℕ} (b : Fin r → ℂ) : Matrix (Fin 1) (Fin (mxN r + mxN r)) ℂ :=
  fun _ => Fin.append (fun i => theta I b ((mxE r).symm i)) (fun i => theta I b ((mxE r).symm i))

/-- `TanV 1 0 (n + n) 1 ≅ TXG r`. -/
noncomputable def mxIota (r : ℕ) : TanV 1 0 (mxN r + mxN r) 1 ≃ₗ[ℂ] TXG r where
  toFun x := (x.1 0, fun h => x.2.2.1 (Fin.castAdd _ (mxE r h)),
    fun h => x.2.2.1 (Fin.natAdd _ (mxE r h)), x.2.2.2 0)
  invFun v := (fun _ => v.1, 0, Fin.append (fun i => v.2.1 ((mxE r).symm i))
    (fun i => v.2.2.1 ((mxE r).symm i)), fun _ => v.2.2.2)
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i; fin_cases i; rfl
    · funext i; exact i.elim0
    · simp only [Equiv.apply_symm_apply]; exact Fin.append_castAdd_natAdd
    · funext i; fin_cases i; rfl
  right_inv v := by
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · funext h
      change Fin.append (fun i => v.2.1 ((mxE r).symm i)) (fun i => v.2.2.1 ((mxE r).symm i))
        (Fin.castAdd (mxN r) (mxE r h)) = v.2.1 h
      rw [Fin.append_left, Equiv.symm_apply_apply]
    · funext h
      change Fin.append (fun i => v.2.1 ((mxE r).symm i)) (fun i => v.2.2.1 ((mxE r).symm i))
        (Fin.natAdd (mxN r) (mxE r h)) = v.2.2.1 h
      rw [Fin.append_right, Equiv.symm_apply_apply]

lemma mxIota_symm_apply (r : ℕ) (v : TXG r) : (mxIota r).symm v = (fun _ => v.1, 0,
    Fin.append (fun i => v.2.1 ((mxE r).symm i)) (fun i => v.2.2.1 ((mxE r).symm i)),
    fun _ => v.2.2.2) := rfl

lemma theta_alg {r : ℕ} {b : Fin r → ℂ} (hb : ∀ j, IsAlgebraic ℚ (b j)) (p : Fin r × Fin 2) :
    IsAlgebraic ℚ (theta I b p) := by
  unfold theta
  split_ifs
  · exact hb p.1
  · have hI : IsAlgebraic ℚ I :=
      ⟨Polynomial.X ^ 2 + Polynomial.C 1, (Polynomial.monic_X_pow_add_C 1 two_ne_zero).ne_zero,
        by simp⟩
    rw [← K11.mem_Kq]
    exact K11.Kq.mul_mem (K11.mem_Kq.mpr hI) (K11.mem_Kq.mpr (hb p.1))

/-- **`Thm11KappaMXG` from `Theorem41VecLA` and the CM inputs** (see the module docstring). -/
theorem thm11KappaMXG_of_cm (h : Theorem41VecLA)
    (hLA : ∀ r, LiftAlg (mxLs r)) (hPT : ∀ r, PerTanRat (mxLs r))
    (hΛ : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      ∃ Λs : AddSubgroup (TanV 1 0 (mxN r + mxN r) 1), (∀ x ∈ Λs, x ∈ LamV (mxLs r) (mxM b)) ∧
        ∀ g ∈ lamGenX b, (mxIota r).symm g ∈ Λs)
    (hper : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      perXG b ≤ (OmV 1 0 (mxLs r) (mxM b)).map ((mxIota r).toLinearMap.restrictScalars ℚ))
    (hsub : ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b →
      ∀ H : SubgroupDataV (d0 := 1) (d1 := 0) (mxLs r) (mxM b), H.tan ≠ ⊥ →
        (gmXG b).sub (H.tan.map (mxIota r).toLinearMap)) :
    MStarCopy.Thm11KappaMXG := by
  intro hg₂ hg₃ hg₂' hg₃' r b hb
  obtain ⟨Λs, hΛs, hgen⟩ := hΛ r b hb
  have hLs : ∀ j, IsAlgebraic ℚ (mxLs r j).g₂ ∧ IsAlgebraic ℚ (mxLs r j).g₃ := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [mxLs, Fin.append_left]; exact ⟨hg₂, hg₃⟩
    · simp only [mxLs, Fin.append_right]; exact ⟨hg₂', hg₃'⟩
  have hM : AlgMat (mxM b) := by
    intro i j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simp only [mxM, Fin.append_left]; exact theta_alg hb.alg _
    · simp only [mxM, Fin.append_right]; exact theta_alg hb.alg _
  refine hyperplaneKappa_of_iso (hyperplaneKappaVec_of h) hLs hM le_rfl (hLA r) (hPT r) (gmXG b)
    (mxIota r) ?_ Λs hΛs ?_ (hper r b hb) rfl ?_ (hsub r b hb)
  · -- (i) algebraic vectors
    intro v hv
    rw [mxIota_symm_apply]
    refine ⟨fun _ => hv.1, fun i => i.elim0, fun k => ?_, fun _ => hv.2.2.2⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · change IsAlgebraic ℚ (Fin.append (fun i => v.2.1 ((mxE r).symm i))
        (fun i => v.2.2.1 ((mxE r).symm i)) (Fin.castAdd (mxN r) i))
      rw [Fin.append_left]; exact hv.2.1 _
    · change IsAlgebraic ℚ (Fin.append (fun i => v.2.1 ((mxE r).symm i))
        (fun i => v.2.2.1 ((mxE r).symm i)) (Fin.natAdd (mxN r) i))
      rw [Fin.append_right]; exact hv.2.2.1 _
  · -- (ii) common denominators
    intro y hy
    have hcl : y ∈ Submodule.span ℚ ((AddSubgroup.closure (lamGenX b) : AddSubgroup (TXG r)) :
        Set (TXG r)) := by
      rw [K11.span_closure_eq]; exact hy
    obtain ⟨N, hN, hNy⟩ := K11.exists_nsmul_mem_of_mem_span _ hcl
    refine ⟨N, hN, ?_⟩
    rw [← map_nsmul]
    have hle : AddSubgroup.closure (lamGenX b) ≤
        Λs.comap (mxIota r).symm.toLinearMap.toAddMonoidHom :=
      (AddSubgroup.closure_le _).mpr fun g hg => hgen g hg
    exact hle hNy
  · -- (iv) `d₂ = 2n + 1 = m + r`
    change 2 * Fintype.card (Fin r × Fin 2) + 1 =
      Fintype.card (Fin r × Fin 2) + Fintype.card (Fin r × Fin 2) + 1
    omega

end LSG.W88.V5d
