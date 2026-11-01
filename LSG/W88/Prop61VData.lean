/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Prop61Data
import LSG.AuxFunV.LemmaUFibC

/-!
# The arithmetic data of Lemma U for the class `𝒞` (Stage 5, phase 2)

**`LSG.AuxV.exists_LUDataV`**: for algebraic `g₂, g₃` and `M`, `W` rational over `ℚ̄` and
`y_j ∈ Λ(G) = LamV Ls M`, there are a number field `K ⊂ ℂ`, a basis `w` of `W` with algebraic
coordinates and `LUDataV` with these `y`, `w` (the fibre values `s_j − Mζ(z_j)` are algebraic by
definition of `LamV`).
-/

open Complex Finset LSG.Elliptic LSG.Weierstrass LSG.W88 LSG.W88.Vec PeriodPair NumberField
open LSG.Aux (Sz conePt isRep_conePt isAlgebraic_conePt exists_den zh)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}

/-- **Construction of the data of Lemma U for the class `𝒞`.** -/
theorem exists_LUDataV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (hg : ∀ k, IsAlgebraic ℚ (Ls k).g₂ ∧ IsAlgebraic ℚ (Ls k).g₃) (hM : AlgMat M)
    (W : Submodule ℂ (TanV d0 d1 m r)) (hW : RatSubV W) {μ : ℕ}
    (y : Fin μ → TanV d0 d1 m r) (hyL : ∀ j, y j ∈ LamV Ls M) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ι : K →+* ℂ) (τ : ℕ)
      (Dt : LUDataV (d0 := d0) (d1 := d1) Ls M ι μ τ),
      Dt.y = y ∧ Submodule.span ℂ (Set.range Dt.w) = W := by
  classical
  -- a basis of `W` with algebraic coordinates
  set St : Set (TanV d0 d1 m r) := {w | w ∈ W ∧ AlgVecV w}
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ St
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨bF, hbF⟩ := hbfin.exists_finset_coe
  set τ := bF.card
  let w : Fin τ → TanV d0 d1 m r := fun q => (bF.equivFin.symm q : TanV d0 d1 m r)
  have hwb : ∀ q, w q ∈ b := fun q => by rw [← hbF]; exact (bF.equivFin.symm q).2
  have hrange : Set.range w = b := by
    ext x; constructor
    · rintro ⟨q, rfl⟩; exact hwb q
    · intro hx
      have hx' : x ∈ bF := by rw [← hbF] at hx; exact hx
      exact ⟨bF.equivFin ⟨x, hx'⟩, by simp [w]⟩
  have hspan : Submodule.span ℂ (Set.range w) = W := by
    rw [hrange, hbspan]; exact hW.symm
  have hwS : ∀ q, w q ∈ St := fun q => hbS (hwb q)
  -- the finite set of algebraic numbers
  let X₀ : Fin μ → Fin m → Fin 3 → ℂ := fun j k => conePt (Ls k) ((y j).2.2.1 k)
  let val : ((Fin μ × Fin d0) ⊕ (Fin μ × Fin d1) ⊕ (Fin μ × Fin m × Fin 3) ⊕ (Fin τ × Fin d0) ⊕
      (Fin τ × Fin d1) ⊕ (Fin τ × Fin m) ⊕ Fin m ⊕ Fin m ⊕ Fin m ⊕ Fin m ⊕
      ((Fin τ × Fin r) ⊕ (Fin μ × Fin r) ⊕ (Fin r × Fin m))) → ℂ := fun a =>
    match a with
    | .inl ji => (y ji.1).1 ji.2
    | .inr (.inl ji) => exp ((y ji.1).2.1 ji.2)
    | .inr (.inr (.inl jki)) => X₀ jki.1 jki.2.1 jki.2.2
    | .inr (.inr (.inr (.inl ri))) => (w ri.1).1 ri.2
    | .inr (.inr (.inr (.inr (.inl ri)))) => (w ri.1).2.1 ri.2
    | .inr (.inr (.inr (.inr (.inr (.inl rk))))) => (w rk.1).2.2.1 rk.2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))) => (Ls k).g₂
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))) => (Ls k).g₃
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))))) => ℘[Ls k] (zh (Ls k))
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))))) => (Ls k).g₂ / 2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ri)))))))))) =>
        (w ri.1).2.2.2 ri.2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ji))))))))))) =>
        (y ji.1).2.2.2 ji.2 - M.mulVec (zetaV Ls (y ji.1).2.2.1) ji.2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ij))))))))))) =>
        M ij.1 ij.2
  let Fs : Finset ℂ := univ.image val
  have hval : ∀ a, val a ∈ Fs := fun a => mem_image_of_mem _ (mem_univ a)
  have halg : ∀ x ∈ Fs, IsAlgebraic ℚ x := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    rcases a with ji | ji | jki | ri | ri | rk | k | k | k | k | ri | ji | ij
    · exact (hyL ji.1).1 ji.2
    · exact (hyL ji.1).2.1 ji.2
    · exact isAlgebraic_conePt (Ls jki.2.1) (hg jki.2.1) ((hyL jki.1).2.2.1 jki.2.1) jki.2.2
    · exact (hwS ri.1).2.1 ri.2
    · exact (hwS ri.1).2.2.1 ri.2
    · exact (hwS rk.1).2.2.2.1 rk.2
    · exact (hg k).1
    · exact (hg k).2
    · exact isAlgebraic_weierstrassP_half (Ls k) (hg k).1 (hg k).2 (Ls k).ω₁_mem_lattice
        (Ls k).ω₁_div_two_notMem_lattice
    · have h2 : IsAlgebraic ℚ ((2 : ℂ)⁻¹) := by
        simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2⁻¹ : ℚ)
      simpa [val, div_eq_mul_inv] using (hg k).1.mul h2
    · exact (hwS ri.1).2.2.2.2 ri.2
    · exact (hyL ji.1).2.2.2 ji.2
    · exact hM ij.1 ij.2
  -- the number field
  let F := IntermediateField.adjoin ℚ (Fs : Set ℂ)
  have : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  have : NumberField F := ⟨⟩
  let ι : F →+* ℂ := F.val.toRingHom
  have hmem : ∀ x ∈ Fs, x ∈ F := fun x hx => IntermediateField.subset_adjoin ℚ _ hx
  -- sizes
  choose dn hdn1 hdni using fun x : Fs => exists_den (⟨x.1, hmem x.1 x.2⟩ : F)
  set H : ℝ := 1 + ∑ x : Fs, house (⟨x.1, hmem x.1 x.2⟩ : F)
  set d : ℕ := ∏ x : Fs, dn x
  have hH : 1 ≤ H := by
    have := sum_nonneg fun x (_ : x ∈ (univ : Finset Fs)) => house_nonneg (⟨x.1, hmem x.1 x.2⟩ : F)
    simp only [H]; linarith
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun x _ => by
    have := hdn1 x; omega)
  have hsz : ∀ x ∈ Fs, Sz ι H d x := by
    intro x hx
    refine ⟨⟨x, hmem x hx⟩, rfl, ?_, ?_⟩
    · have := single_le_sum (f := fun x : Fs => house (⟨x.1, hmem x.1 x.2⟩ : F))
        (fun x _ => house_nonneg _) (mem_univ ⟨x, hx⟩)
      simp only [H]; linarith
    · have hdv : dn ⟨x, hx⟩ ∣ d := dvd_prod_of_mem _ (mem_univ _)
      obtain ⟨e, he⟩ := hdv
      have : ((d : ℕ) : F) * ⟨x, hmem x hx⟩ = (e : F) * ((dn ⟨x, hx⟩ : F) * ⟨x, hmem x hx⟩) := by
        rw [he]; push_cast; ring
      rw [this]
      have he' : IsIntegral ℤ (e : F) := by
        simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := (e : ℤ))
      exact he'.mul (hdni _)
  refine ⟨F, inferInstance, inferInstance, ι, τ,
    { y := y, w := w, X₀ := X₀,
      γ₂ := fun k => ⟨(Ls k).g₂, hmem _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))))⟩,
      γ₃ := fun k => ⟨(Ls k).g₃, hmem _
        (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))))))⟩,
      H := H, d := d, hH := hH, hd := hd,
      hγ₂ := fun k => rfl, hγ₃ := fun k => rfl,
      ha := fun j i => hsz _ (hval (.inl (j, i))),
      hb := fun j i => hsz _ (hval (.inr (.inl (j, i)))),
      hX₀ := fun j k => isRep_conePt (Ls k) _,
      hX₀s := fun j k i => hsz _ (hval (.inr (.inr (.inl (j, k, i))))),
      hw0 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inl (q, i)))))),
      hw1 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inr (.inl (q, i))))))),
      hw2 := fun q k => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inl (q, k)))))))),
      hw3 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inl (q, i))))))))))))),
      he₁ := fun k => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))))))),
      hg₂ := fun k => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl k))))))))))),
      hg₂' := fun k => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))))),
      hg₃' := fun k => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))))),
      hτ := fun j i => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inl (j, i)))))))))))))),
      hM := fun i j => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inr (.inr (i, j)))))))))))))) },
    rfl, hspan⟩

end LSG.AuxV
