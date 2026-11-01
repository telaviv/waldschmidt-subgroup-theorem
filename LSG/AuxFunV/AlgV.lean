/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.MonoV

/-!
# Algebraic points of `E^♮` and `Λ(G)` as a group (Stage 5, phase 1, item 2)

* `NLaw_map`: the eight addition laws of `E^♮` commute with ring homomorphisms.
* `AlgPtN L z w`: all five coordinates of `exp_{E^♮}(z, w) = expN L z w` are algebraic.
* **`algPtN_add`**: algebraic points of `E^♮` are closed under the group law — uniformly in all
  configurations (doubling, opposite points, points over `O`), via a nonzero law
  (`NLaw_complete`) and its compatibility with the analytic group law (`NLaw_expN_all`).
* **`isAlgebraic_zeta_defect`**: if `z₁, z₂` are algebraic points of `E` (lattice points or
  `℘(zᵢ) ∈ ℚ̄`), then `ζ(z₁) + ζ(z₂) − ζ(z₁ + z₂) ∈ ℚ̄` and `z₁ + z₂` is again algebraic. (This is
  the fibre part of the group law of `E^♮`: the "eight laws" route of `VECEXT §3.1`.)
* **`lamVSub`**: for algebraic `g₂, g₃` and an algebraic matrix `M`, `Λ(G) = LamV Ls M` is an
  additive subgroup of `T_G` (`VECEXT.md` §3.1, "`LamV` is an `AddSubgroup`").
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic LSG.W88 LSG.W88.Vec PeriodPair

noncomputable section

namespace LSG.AuxV

/-! ### The laws commute with ring homomorphisms -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma map_law₁U (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₁U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₁U (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₁U, map_ofNat]

lemma map_law₁V (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₁V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₁V (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₁V, map_ofNat]

lemma map_law₁W (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₁W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₁W (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₁W, map_ofNat]

lemma map_law₂U (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₂U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₂U (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₂U, map_ofNat]

lemma map_law₂V (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₂V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₂V (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₂V, map_ofNat]

lemma map_law₂W (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (law₂W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₂W (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [law₂W, map_ofNat]

lemma map_kapW₁VV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₁VV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₁VV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₁VV, map_ofNat]

lemma map_kapV₁VV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₁VV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₁VV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₁VV, map_ofNat]

lemma map_kapW₁VW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₁VW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₁VW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₁VW, map_ofNat]

lemma map_kapV₁VW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₁VW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₁VW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₁VW, map_ofNat]

lemma map_kapW₁WV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₁WV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₁WV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₁WV, map_ofNat]

lemma map_kapV₁WV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₁WV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₁WV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₁WV, map_ofNat]

lemma map_kapW₁WW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₁WW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₁WW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₁WW, map_ofNat]

lemma map_kapV₁WW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₁WW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₁WW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₁WW, map_ofNat]

lemma map_kapW₂VV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₂VV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₂VV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₂VV, map_ofNat]

lemma map_kapV₂VV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₂VV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₂VV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₂VV, map_ofNat]

lemma map_kapW₂VW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₂VW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₂VW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₂VW, map_ofNat]

lemma map_kapV₂VW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₂VW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₂VW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₂VW, map_ofNat]

lemma map_kapW₂WV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₂WV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₂WV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₂WV, map_ofNat]

lemma map_kapV₂WV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₂WV g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₂WV (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₂WV, map_ofNat]

lemma map_kapW₂WW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapW₂WW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapW₂WW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapW₂WW, map_ofNat]

lemma map_kapV₂WW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    f (kapV₂WW g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      kapV₂WW (f g₂) (f g₃) (f U₁) (f V₁) (f W₁) (f U₂) (f V₂) (f W₂) := by
  simp [kapV₂WW, map_ofNat]

set_option maxHeartbeats 1000000 in -- large proof (many local constants)
/-- The eight laws are polynomials with integer coefficients. -/
theorem NLaw_map (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 5 → R) (c : Fin 5) :
    f (NLaw g₂ g₃ i j k P Q c) = NLaw (f g₂) (f g₃) i j k (f ∘ P) (f ∘ Q) c := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases c <;>
    simp [NLaw, lawSel, kapW, kapV, mult, LSG.Elliptic.tcoord, Pe, law₁, law₂, map_ofNat,
      map_law₁U, map_law₁V, map_law₁W, map_law₂U, map_law₂V, map_law₂W, map_kapW₁VV, map_kapV₁VV,
      map_kapW₁VW, map_kapV₁VW, map_kapW₁WV, map_kapV₁WV, map_kapW₁WW, map_kapV₁WW, map_kapW₂VV,
      map_kapV₂VV, map_kapW₂VW, map_kapV₂VW, map_kapW₂WV, map_kapV₂WV, map_kapW₂WW, map_kapV₂WW]

end Map

/-! ### Algebraic points of `E^♮` -/

/-- The subfield of algebraic numbers. -/
abbrev Qbar : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

lemma mem_Qbar {x : ℂ} : x ∈ Qbar ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

variable (L : PeriodPair)

/-- All coordinates of `exp_{E^♮}(z, w)` are algebraic. -/
def AlgPtN (z w : ℂ) : Prop := ∀ k, IsAlgebraic ℚ (expN L z w k)

/-- An algebraic point of `E`: a lattice point or `℘(z) ∈ ℚ̄`. -/
def AlgPtE (z : ℂ) : Prop := z ∈ L.lattice ∨ IsAlgebraic ℚ (℘[L] z)

lemma Pe_expN_ne_zero (z w : ℂ) : Pe (expN L z w) ≠ 0 := by
  unfold expN
  split_ifs
  · intro h; simpa [Pe, ptO] using congrFun h 1
  · intro h; simpa [Pe, ptAff] using congrFun h 2

lemma isAlgebraic_derivWeierstrassP (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {z : ℂ} (hz : z ∉ L.lattice) (hp : IsAlgebraic ℚ (℘[L] z)) : IsAlgebraic ℚ (℘'[L] z) := by
  refine IsAlgebraic.of_pow (n := 2) two_pos ?_
  rw [L.derivWeierstrassP_sq z hz]
  rw [← mem_Qbar] at hp hg₂ hg₃ ⊢
  exact Qbar.sub_mem (Qbar.sub_mem (Qbar.mul_mem (ofNat_mem Qbar 4) (Qbar.pow_mem hp 3))
    (Qbar.mul_mem hg₂ hp)) hg₃

/-- **Algebraic points of `E^♮` form a group** (closure under addition, all configurations). -/
theorem algPtN_add (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {z₁ w₁ z₂ w₂ : ℂ}
    (h₁ : AlgPtN L z₁ w₁) (h₂ : AlgPtN L z₂ w₂) : AlgPtN L (z₁ + z₂) (w₁ + w₂) := by
  set P := expN L z₁ w₁
  set Q := expN L z₂ w₂
  obtain ⟨i, j, k, -, -, -, hne⟩ := NLaw_complete (K := ℂ) two_ne_zero (discr_ne_zero L)
    (Fn_expN L z₁ w₁) (Fn_expN L z₂ w₂) (Pe_expN_ne_zero L z₁ w₁) (Pe_expN_ne_zero L z₂ w₂)
  obtain ⟨c, hc⟩ := NLaw_expN_all L z₁ w₁ z₂ w₂ i j k
  -- the law has algebraic entries
  let P' : Fin 5 → Qbar := fun e => ⟨P e, mem_Qbar.mpr (h₁ e)⟩
  let Q' : Fin 5 → Qbar := fun e => ⟨Q e, mem_Qbar.mpr (h₂ e)⟩
  let γ₂ : Qbar := ⟨L.g₂, mem_Qbar.mpr hg₂⟩
  let γ₃ : Qbar := ⟨L.g₃, mem_Qbar.mpr hg₃⟩
  have hmem : ∀ e, NLaw L.g₂ L.g₃ i j k P Q e ∈ Qbar := by
    intro e
    have := NLaw_map (Qbar.subtype) γ₂ γ₃ i j k P' Q' e
    rw [show (Qbar.subtype ∘ P') = P from rfl, show (Qbar.subtype ∘ Q') = Q from rfl] at this
    rw [show L.g₂ = Qbar.subtype γ₂ from rfl, show L.g₃ = Qbar.subtype γ₃ from rfl, ← this]
    exact SetLike.coe_mem _
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_smul] at hc; exact hne hc
  intro e
  rw [← mem_Qbar]
  by_cases hs : z₁ + z₂ ∈ L.lattice
  · have h1 : NLaw L.g₂ L.g₃ i j k P Q 1 = c := by
      rw [hc, expN_of_mem L hs]; simp [ptO]
    have he : expN L (z₁ + z₂) (w₁ + w₂) e = NLaw L.g₂ L.g₃ i j k P Q e / c := by
      rw [hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hc0]
    rw [he]
    exact Qbar.div_mem (hmem e) (h1 ▸ hmem 1)
  · have h2 : NLaw L.g₂ L.g₃ i j k P Q 2 = c := by
      rw [hc, expN_of_notMem L hs]; simp [ptAff]
    have he : expN L (z₁ + z₂) (w₁ + w₂) e = NLaw L.g₂ L.g₃ i j k P Q e / c := by
      rw [hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hc0]
    rw [he]
    exact Qbar.div_mem (hmem e) (h2 ▸ hmem 2)

/-- The point `(z, ζ(z))` (fibre coordinate `0`) over an algebraic point of `E` is algebraic. -/
lemma algPtN_zeta (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {z : ℂ}
    (h : AlgPtE L z) : AlgPtN L z (zeta L z) := by
  by_cases hz : z ∈ L.lattice
  · rw [AlgPtN, expN_of_mem L hz, sub_self]
    intro k
    fin_cases k <;> simp [ptO, isAlgebraic_zero, isAlgebraic_one]
  · have hp : IsAlgebraic ℚ (℘[L] z) := h.resolve_left hz
    have hp' := isAlgebraic_derivWeierstrassP L hg₂ hg₃ hz hp
    rw [AlgPtN, expN_of_notMem L hz, sub_self]
    intro k
    rw [← mem_Qbar] at hp hp' ⊢
    fin_cases k <;> simp only [ptAff, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact hp
    · exact hp'
    · exact Qbar.one_mem
    · exact Qbar.zero_mem
    · exact Qbar.sub_mem (Qbar.mul_mem hp' Qbar.zero_mem)
        (Qbar.mul_mem (ofNat_mem Qbar 2) (Qbar.pow_mem hp 2))

lemma algPtE_of_algPtN {z w : ℂ} (h : AlgPtN L z w) : AlgPtE L z := by
  by_cases hz : z ∈ L.lattice
  · exact Or.inl hz
  · right
    have := h 0
    rwa [expN_of_notMem L hz] at this

lemma fib_of_algPtN {z w : ℂ} (h : AlgPtN L z w) : IsAlgebraic ℚ (w - zeta L z) := by
  by_cases hz : z ∈ L.lattice
  · have := h 4
    rwa [expN_of_mem L hz] at this
  · have := h 3
    rwa [expN_of_notMem L hz] at this

/-- **The `ζ`-defect at algebraic points is algebraic** (all configurations). -/
theorem isAlgebraic_zeta_defect (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {z₁ z₂ : ℂ} (h₁ : AlgPtE L z₁) (h₂ : AlgPtE L z₂) :
    AlgPtE L (z₁ + z₂) ∧ IsAlgebraic ℚ (zeta L z₁ + zeta L z₂ - zeta L (z₁ + z₂)) := by
  have h := algPtN_add L hg₂ hg₃ (algPtN_zeta L hg₂ hg₃ h₁) (algPtN_zeta L hg₂ hg₃ h₂)
  exact ⟨algPtE_of_algPtN L h, fib_of_algPtN L h⟩

lemma algPtE_neg {z : ℂ} (h : AlgPtE L z) : AlgPtE L (-z) := by
  rcases h with h | h
  · exact Or.inl (L.lattice.neg_mem h)
  · right; rwa [L.weierstrassP_neg]

/-! ### `Λ(G)` is a group -/

variable {d0 d1 m r : ℕ}

lemma algVec_add {n : ℕ} {u v : Fin n → ℂ} (hu : AlgVec u) (hv : AlgVec v) : AlgVec (u + v) :=
  fun i => mem_Qbar.mp (Qbar.add_mem (mem_Qbar.mpr (hu i)) (mem_Qbar.mpr (hv i)))

lemma algVec_neg {n : ℕ} {u : Fin n → ℂ} (hu : AlgVec u) : AlgVec (-u) :=
  fun i => mem_Qbar.mp (Qbar.neg_mem (mem_Qbar.mpr (hu i)))

lemma algVec_mulVec {M : Matrix (Fin r) (Fin m) ℂ} (hM : AlgMat M) {u : Fin m → ℂ}
    (hu : AlgVec u) : AlgVec (M.mulVec u) := fun i => by
  rw [← mem_Qbar]
  simp only [Matrix.mulVec, dotProduct]
  exact Qbar.sum_mem fun j _ => Qbar.mul_mem (mem_Qbar.mpr (hM i j)) (mem_Qbar.mpr (hu j))

/-- **`Λ(G)` is an additive subgroup of `T_G`** (algebraic `g₂, g₃`, algebraic `M`). -/
def lamVSub (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (hg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) (hM : AlgMat M) :
    AddSubgroup (TanV d0 d1 m r) where
  carrier := LamV Ls M
  add_mem' {p q} hp hq := by
    obtain ⟨ha, hb, hz, hs⟩ := hp
    obtain ⟨ha', hb', hz', hs'⟩ := hq
    have hdef := fun j => isAlgebraic_zeta_defect (Ls j) (hg j).1 (hg j).2 (hz j) (hz' j)
    refine ⟨algVec_add ha ha', fun i => ?_, fun j => (hdef j).1, ?_⟩
    · change IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
      rw [Complex.exp_add, ← mem_Qbar]
      exact Qbar.mul_mem (mem_Qbar.mpr (hb i)) (mem_Qbar.mpr (hb' i))
    · have hd : AlgVec (zetaV Ls p.2.2.1 + zetaV Ls q.2.2.1 - zetaV Ls (p.2.2.1 + q.2.2.1)) :=
        fun j => (hdef j).2
      have he : (p + q).2.2.2 - M.mulVec (zetaV Ls (p + q).2.2.1) =
          (p.2.2.2 - M.mulVec (zetaV Ls p.2.2.1)) + (q.2.2.2 - M.mulVec (zetaV Ls q.2.2.1)) +
            M.mulVec (zetaV Ls p.2.2.1 + zetaV Ls q.2.2.1 - zetaV Ls (p.2.2.1 + q.2.2.1)) := by
        simp only [Prod.snd_add, Prod.fst_add, Matrix.mulVec_sub, Matrix.mulVec_add]
        abel
      rw [he]
      exact algVec_add (algVec_add hs hs') (algVec_mulVec hM hd)
  zero_mem' := by
    refine ⟨fun i => isAlgebraic_zero, fun i => ?_, fun j => Or.inl (Ls j).lattice.zero_mem, ?_⟩
    · change IsAlgebraic ℚ (Complex.exp 0); rw [Complex.exp_zero]; exact isAlgebraic_one
    · have hz : zetaV Ls (0 : TanV d0 d1 m r).2.2.1 = 0 := funext fun j => zeta_zero (Ls j)
      rw [hz, Matrix.mulVec_zero, sub_zero]
      exact fun i => isAlgebraic_zero
  neg_mem' {p} hp := by
    obtain ⟨ha, hb, hz, hs⟩ := hp
    refine ⟨algVec_neg ha, fun i => ?_, fun j => algPtE_neg (Ls j) (hz j), ?_⟩
    · change IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
      rw [Complex.exp_neg, ← mem_Qbar]
      exact Qbar.inv_mem (mem_Qbar.mpr (hb i))
    · have hz' : zetaV Ls (-p).2.2.1 = -zetaV Ls p.2.2.1 :=
        funext fun j => LSG.Weierstrass.zeta_neg (Ls j) (p.2.2.1 j)
      have he : (-p).2.2.2 - M.mulVec (zetaV Ls (-p).2.2.1) =
          -(p.2.2.2 - M.mulVec (zetaV Ls p.2.2.1)) := by
        rw [hz', Matrix.mulVec_neg]
        simp only [Prod.snd_neg]
        abel
      rw [he]
      exact algVec_neg hs

end LSG.AuxV
