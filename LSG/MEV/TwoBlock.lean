import Mathlib
import LSG.MEV.DerivV
import LSG.ME.PhOpTwo

/-!
# Two-parameter formal associativity (one block)

Over the base ring `R = ℂ⟦z⟧`: the inner canonical flow `ZB g s' β'` (variable `z'`, base-changed
to `R`) translated by the outer formal point `B = ZB y s β ∈ R⁵` is, for every law and both
orders, a multiple of an `R`-flow `Xt` of `(2s', β')` (chart `chartV (y + g)`) whose initial value
is `ZB (y + g) s β` (**`two_block`**). So `law(y + exp(z w), g + exp(z' w'))` is the flow of `w'`
through the flow of `w` through `y + g`.

* `isBFlow_map`: base change of flows along `algebraMap ℂ R`.
* `fixed_scale`: a normalized vector that is a multiple of a normalized vector equals it.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk c2)

namespace LSG.MEV

local notation "Rz" => PowerSeries ℂ

instance charZero_powerSeries_complex : CharZero (PowerSeries ℂ) :=
  charZero_of_injective_ringHom (f := (PowerSeries.C : ℂ →+* PowerSeries ℂ)) fun a b h => by
    simpa using congrArg (PowerSeries.coeff 0) h

theorem isBFlow_map {L : PeriodPair} {a : Fin 2} {s β : ℂ} {Y : Fin 5 → PowerSeries ℂ}
    (hY : IsBFlow (R := ℂ) L.g₂ L.g₃ a s β Y) :
    IsBFlow (R := Rz) L.g₂ L.g₃ a s β (fun l => PowerSeries.map (algebraMap ℂ Rz) (Y l)) := by
  refine ⟨by simp [hY.norm], fun l => ?_⟩
  rw [LSG.ME.derivative_map, hY.ode, dvalB_map]
  simp only [LSG.ME.map_algebraMap_alg]
  rfl

theorem Fn_map_series {L : PeriodPair} {Y : Fin 5 → PowerSeries ℂ}
    (hY : Fn (algebraMap ℂ (PowerSeries ℂ) L.g₂) (algebraMap ℂ (PowerSeries ℂ) L.g₃) Y = 0) :
    Fn (algebraMap ℂ (PowerSeries Rz) L.g₂) (algebraMap ℂ (PowerSeries Rz) L.g₃)
      (fun l => PowerSeries.map (algebraMap ℂ Rz) (Y l)) = 0 := by
  have := Fn_map (PowerSeries.map (algebraMap ℂ Rz)) (algebraMap ℂ (PowerSeries ℂ) L.g₂)
    (algebraMap ℂ (PowerSeries ℂ) L.g₃) Y
  rw [hY, map_zero, LSG.ME.map_algebraMap_alg, LSG.ME.map_algebraMap_alg] at this
  exact this.symm

theorem Gn_map_series {Y : Fin 5 → PowerSeries ℂ} (hY : Gn Y = 0) :
    Gn (fun l => PowerSeries.map (algebraMap ℂ Rz) (Y l)) = 0 := by
  have := Gn_map (PowerSeries.map (algebraMap ℂ Rz)) Y
  rw [hY, map_zero] at this
  exact this.symm

/-- **Two-parameter formal associativity** (one block). -/
theorem two_block {L : PeriodPair} (g y : EVL L) (s β s' β' : ℂ) :
    ∃ Xt : Fin 5 → PowerSeries Rz,
      IsBFlow (R := Rz) L.g₂ L.g₃ (chartV (y + g)) s' β' Xt ∧
      (∀ l, PowerSeries.constantCoeff (Xt l) = ZB (y + g) s β l) ∧
      ∀ A ∈ lawsAt (algebraMap ℂ (PowerSeries Rz) L.g₂) (algebraMap ℂ (PowerSeries Rz) L.g₃)
        (fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB g s' β' l))
        (fun l => PowerSeries.C (ZB y s β l)),
        A = A (bi (chartV (y + g))) • Xt := by
  obtain ⟨hg, hgF, hgG, hg0⟩ := ZB_spec g s' β'
  obtain ⟨hy, hyF, hyG, hy0⟩ := ZB_spec y s β
  set Ym : Fin 5 → PowerSeries Rz := fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB g s' β' l)
  set B : Fin 5 → Rz := ZB y s β
  have hYm := isBFlow_map hg
  have hYmF := Fn_map_series hgF
  have hYmG := Gn_map_series hgG
  have hB0 : Pe B ≠ 0 := fun h => by
    have := congrFun h (biE (chartV y))
    rw [← mult_eq _ (Pe B), mult_Pe, hy.norm] at this
    exact one_ne_zero this
  obtain ⟨i, j, k, hne⟩ := exists_NLaw_ne g y
  obtain ⟨μ, hμ0, hμ⟩ := NLaw_repV_ne g y i j k hne
  set b := chartV (y + g)
  set X := NLaw (algebraMap ℂ (PowerSeries Rz) L.g₂) (algebraMap ℂ (PowerSeries Rz) L.g₃) i j k Ym
    (fun l => PowerSeries.C (B l)) with hX
  -- the constant term in `z'`
  have hX0 : (fun l => PowerSeries.constantCoeff (X l)) =
      NLaw (algebraMap ℂ Rz L.g₂) (algebraMap ℂ Rz L.g₃) i j k
        (fun l => PowerSeries.C (repV g l)) B := by
    funext l
    rw [hX, NLaw_map]
    congr 1
    all_goals first
      | (simp [PowerSeries.algebraMap_apply]; done)
      | (funext l'; simp only [Ym, Function.comp_apply]
         rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
           PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]; rfl)
      | (funext l'; simp [Ym, hg0, PowerSeries.algebraMap_apply]; done)
  have hmem0 : NLaw (algebraMap ℂ Rz L.g₂) (algebraMap ℂ Rz L.g₃) i j k
      (fun l => PowerSeries.C (repV g l)) B ∈ lawsAt (algebraMap ℂ Rz L.g₂)
        (algebraMap ℂ Rz L.g₃) (ZB y s β) (fun l => PowerSeries.C (repV g l)) :=
    ⟨i, j, k, Or.inr rfl⟩
  have hlaw0 := laws_eq y g s β hmem0
  -- the constant term in `z` of the chart coordinate
  have hcc : PowerSeries.constantCoeff (NLaw (algebraMap ℂ Rz L.g₂) (algebraMap ℂ Rz L.g₃) i j k
      (fun l => PowerSeries.C (repV g l)) B (bi b)) = μ := by
    rw [NLaw_map]
    have h1 : (PowerSeries.constantCoeff ∘ fun l => PowerSeries.C (repV g l)) = repV g := by
      funext l; simp
    have h2 : (PowerSeries.constantCoeff ∘ B) = repV y := funext hy0
    rw [h1, h2]
    simp only [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, Algebra.algebraMap_self,
      RingHom.id_apply]
    have hc := congrFun hμ (bi b)
    rw [hc, add_comm g y]
    simp [repV_chart, b]
  have hU : IsUnit (X (bi b)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have := congrFun hX0 (bi b)
    rw [this, PowerSeries.isUnit_iff_constantCoeff, hcc]
    exact hμ0.isUnit
  have hBF : Fn (algebraMap ℂ Rz L.g₂) (algebraMap ℂ Rz L.g₃) B = 0 := hyF
  have hfl := curve_block hYm hYmF hYmG hBF hyG i j k hU
  refine ⟨_, hfl, fun l => ?_, fun A hA => curve_all hYm hYmF hYmG hBF hyG hB0 i j k hU hA⟩
  -- the initial value
  set Ui := Ring.inverse (X (bi b))
  have hUi : Ui * X (bi b) = 1 := Ring.inverse_mul_cancel _ hU
  have hcU := congrArg PowerSeries.constantCoeff hUi
  rw [map_mul, map_one] at hcU
  have e0 : ∀ l', PowerSeries.constantCoeff (X l') =
      NLaw (algebraMap ℂ Rz L.g₂) (algebraMap ℂ Rz L.g₃) i j k
        (fun l => PowerSeries.C (repV g l)) B (bi b) * ZB (y + g) s β l' := by
    intro l'
    have h1 := congrFun hX0 l'
    have h2 := congrFun hlaw0 l'
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h1, h2]
  rw [e0 (bi b), (ZB_spec (y + g) s β).1.norm, mul_one] at hcU
  show PowerSeries.constantCoeff (Ui * X l) = _
  rw [map_mul, e0 l, ← mul_assoc, hcU, one_mul]

end LSG.MEV
