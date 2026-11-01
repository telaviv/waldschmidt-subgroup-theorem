/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Minor
import LSG.W88.Statement

/-!
# Coordinates on `V ⊂ T_G` adapted to the periods (bridge item (b))

`T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m` has `d₀ + d₁ + m` coordinate forms (`tcoord`). For a subspace `V` of
dimension `n`, `n` of them restrict to a basis of `V*` (`exists_coordsV`, via the nonzero minor of
`Minor.lean` applied to a basis of `V`), giving `ψ : V ≃ ℂⁿ`. Each coordinate form maps the period
group `Ω(G) = Per Ls` into a lattice of `ℂ`:
* `G_a`: `0 ⊂ ℤ·1 + ℤ·i`;   `G_m`: `2πiℤ ⊂ ℤ·1 + ℤ·2πi`;   `E_j`: `Λ_j = ℤω₁ + ℤω₂`
(`latA`, `latB`, `latD`, `per_coord`). So in the coordinates `ψ` the periods are `perVec` of integer
vectors, which is the setting of `LSG.Aux.prop21Lat`.
-/

open Complex Finset Module LSG.W88

noncomputable section

namespace LSG.Aux

variable {d0 d1 m : ℕ}

/-- Indices of the coordinate forms of `T_G`. -/
abbrev Coord (d0 d1 m : ℕ) := Fin d0 ⊕ Fin d1 ⊕ Fin m

/-- The coordinate forms of `T_G`. -/
def tcoord : Coord d0 d1 m → Tan d0 d1 m →ₗ[ℂ] ℂ
  | .inl i => (LinearMap.proj i).comp (LinearMap.fst ℂ _ _)
  | .inr (.inl i) => (LinearMap.proj i).comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))
  | .inr (.inr j) => (LinearMap.proj j).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))

lemma eq_zero_of_tcoord {p : Tan d0 d1 m} (h : ∀ c, tcoord c p = 0) : p = 0 := by
  obtain ⟨a, b, z⟩ := p
  have ha : a = 0 := funext fun i => h (.inl i)
  have hb : b = 0 := funext fun i => h (.inr (.inl i))
  have hz : z = 0 := funext fun j => h (.inr (.inr j))
  simp [ha, hb, hz]

/-- **Coordinates on `V`.** `n` coordinate forms of `T_G` restrict to an isomorphism `V ≃ ℂⁿ`. -/
theorem exists_coordsV (V : Submodule ℂ (Tan d0 d1 m)) {n : ℕ} (hn : finrank ℂ V = n) :
    ∃ J : Fin n → Coord d0 d1 m, ∃ ψ : V ≃ₗ[ℂ] (Fin n → ℂ), ∀ v k, ψ v k = tcoord (J k) v := by
  classical
  let b : Basis (Fin n) ℂ V := Module.finBasisOfFinrankEq ℂ V hn
  let Φ : V →ₗ[ℂ] (Coord d0 d1 m → ℂ) := LinearMap.pi fun c => (tcoord c).comp V.subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have : (v : Tan d0 d1 m) = 0 := eq_zero_of_tcoord fun c => congrFun hv c
    exact Subtype.ext this
  let Q : Fin n → Coord d0 d1 m → ℂ := fun k c => tcoord c (b k)
  have hQ : LinearIndependent ℂ Q := by
    have := b.linearIndependent.map' Φ (LinearMap.ker_eq_bot.mpr hΦ)
    convert this using 1
    funext k c; rfl
  obtain ⟨J, -, hunit⟩ := exists_minor_isUnit Q hQ
  set N : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun t k => Q k (J t)
  let ψ₀ : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi fun k => (tcoord (J k)).comp V.subtype
  have hψ₀ : ∀ v, ψ₀ v = N.mulVec (b.equivFun v) := by
    intro v
    funext t
    conv_lhs => rw [← b.sum_equivFun v]
    simp only [ψ₀, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      map_sum, map_smul, smul_eq_mul, Matrix.mulVec,
      dotProduct, N, Matrix.of_apply, Q]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hinj : Function.Injective ψ₀ := by
    intro v w h
    rw [hψ₀, hψ₀] at h
    exact b.equivFun.injective (Matrix.mulVec_injective_iff_isUnit.mpr hunit h)
  exact ⟨J, LinearMap.linearEquivOfInjective ψ₀ hinj (by rw [hn, finrank_fin_fun]),
    fun v k => rfl⟩

/-- First generator of the lattice containing the periods of coordinate `c`. -/
def latA (Ls : Fin m → PeriodPair) : Coord d0 d1 m → ℂ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr j) => (Ls j).ω₁

/-- Second generator. -/
def latB (Ls : Fin m → PeriodPair) : Coord d0 d1 m → ℂ
  | .inl _ => I
  | .inr (.inl _) => 2 * Real.pi * I
  | .inr (.inr j) => (Ls j).ω₂

lemma im_conj_mul_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h
  have h1 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hind := (LinearIndependent.pair_iff' h1).mp L.indep
  set w := (starRingEnd ℂ) L.ω₁ * L.ω₂
  have hw : (w.re : ℂ) = w := Complex.ext rfl (by simp [h])
  have hn : (0 : ℝ) < ‖L.ω₁‖ ^ 2 := by have := norm_pos_iff.mpr h1; positivity
  apply hind (w.re / ‖L.ω₁‖ ^ 2)
  have key : ((‖L.ω₁‖ ^ 2 : ℝ) : ℂ) * L.ω₂ = (w.re : ℂ) * L.ω₁ := by
    rw [hw]
    push_cast
    rw [← Complex.conj_mul']
    simp only [w]; ring
  have hn' : ((‖L.ω₁‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.real_smul, Complex.ofReal_div]
  field_simp
  rw [← key]

lemma latD (Ls : Fin m → PeriodPair) (c : Coord d0 d1 m) :
    ((starRingEnd ℂ) (latA Ls c) * latB Ls c).im ≠ 0 := by
  rcases c with i | i | j
  · simp [latA, latB]
  · simp [latA, latB, Real.pi_ne_zero]
  · exact im_conj_mul_ne_zero (Ls j)

/-- **Periods in coordinates.** Each coordinate of a period of `G` is an integer combination of
`latA c`, `latB c`. -/
lemma per_coord (Ls : Fin m → PeriodPair) {ω : Tan d0 d1 m} (hω : ω ∈ Per Ls)
    (c : Coord d0 d1 m) :
    ∃ q : ℤ × ℤ, tcoord c ω = (q.1 : ℂ) * latA Ls c + (q.2 : ℂ) * latB Ls c := by
  obtain ⟨h0, h1, h2⟩ := hω
  rcases c with i | i | j
  · refine ⟨(0, 0), ?_⟩
    simp [tcoord, h0]
  · obtain ⟨k, hk⟩ := h1 i
    refine ⟨(0, k), ?_⟩
    simp only [tcoord, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, latA, latB, hk]
    push_cast; ring
  · obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (h2 j)
    refine ⟨(a, b), ?_⟩
    simp only [tcoord, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.snd_apply, latA,
      latB]
    rw [← hab]

end LSG.Aux
