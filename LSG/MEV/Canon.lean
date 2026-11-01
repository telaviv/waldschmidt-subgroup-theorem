import Mathlib
import LSG.MEV.Curve
import LSG.MEV.FormalExp
import LSG.MEV.Group

/-!
# Canonical flows through points of `E^♮` and formal associativity (one block, over `ℂ`)

* `ExpBlock_isBFlow`: the formal exponential `ExpBlock (2s) β` is the flow of `(2s, β)` normalized
  in chart `V` through the identity `ptO 0`.
* `chartV p`: the canonical chart at `p` (`V` over `O`, `W` otherwise); `repV p` is normalized
  there (`repV_chart`).
* **`ZB p s β`**: the flow of `(2s, β)` through `repV p`, normalized in `chartV p` (it exists by the
  curve lemma applied to `ExpBlock` and a good law; unique by `eq_of_isBFlow`), on `X`.
* **`laws_eq`** (formal associativity): for points `g, h`, every law value at `(ZB g, rep h)` or
  `(rep h, ZB g)` is (its chart coordinate) `•` `ZB (g + h)`.
* `ExpBlock_eq`: `ExpBlock (2s) β = ZB 0 s β`.
-/

open LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (c2)

namespace LSG.MEV

/-! ### The formal exponential is a flow -/

section Exp

variable {K : Type*} [Field K] [CharZero K]

local notation "dz" => (PowerSeries.derivative (R := K))

/-- The polynomial shape of `ExpBlock`. -/
noncomputable def EBpoly : Fin 5 → MvPolynomial (Fin 3) K :=
  ![MvPolynomial.X 0, 1, MvPolynomial.X 1, MvPolynomial.X 1 * MvPolynomial.X 2 +
    2 * MvPolynomial.X 0 ^ 2, MvPolynomial.X 2]

theorem ExpBlock_eq_aeval (g₂ g₃ a b : K) (l : Fin 5) :
    ExpBlock g₂ g₃ a b l = MvPolynomial.aeval (R := K) (stu g₂ g₃ a b) (EBpoly (K := K) l) := by
  fin_cases l <;> simp [ExpBlock, EBpoly]

theorem EB_identity (g₂ g₃ s b : K) (l : Fin 5) :
    ∑ v, MvPolynomial.pderiv v (EBpoly l) * vfV g₂ g₃ (2 * s) b v =
      dvalB 0 (MvPolynomial.C g₂) (MvPolynomial.C g₃) (MvPolynomial.C s) (MvPolynomial.C b)
        EBpoly l := by
  apply MvPolynomial.funext
  intro x
  fin_cases l <;>
    simp [Fin.sum_univ_three, EBpoly, vfV, dvalB, c2, rhoh, Pe, Derivation.leibniz,
      Derivation.leibniz_pow, MvPolynomial.pderiv_X, Pi.single_apply] <;> ring

/-- **The formal exponential is the flow through the identity**, chart `V`. -/
theorem ExpBlock_isBFlow (g₂ g₃ s b : K) :
    IsBFlow (R := K) g₂ g₃ 0 s b (ExpBlock g₂ g₃ (2 * s) b) := by
  refine ⟨rfl, fun l => ?_⟩
  rw [ExpBlock_eq_aeval, LSG.ME.derivative_aeval]
  simp only [stu_deriv, ← map_mul, ← map_sum, EB_identity]
  rw [← AlgHom.coe_toRingHom, dvalB_map]
  simp only [AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
  congr 1
  funext l'; exact (ExpBlock_eq_aeval g₂ g₃ (2 * s) b l').symm

end Exp

/-! ### Canonical flows over `ℂ` -/

section Canon

variable {L : PeriodPair}

local notation "dz" => (PowerSeries.derivative (R := ℂ))
local notation "alg" => algebraMap ℂ (PowerSeries ℂ)

open Classical in
/-- The canonical chart at a point of `E^♮`: `V` over `O`, `W` otherwise. -/
noncomputable def chartV (p : EVL L) : Fin 2 := if p.base = 0 then 0 else 1

theorem repV_chart (p : EVL L) : repV p (bi (chartV p)) = 1 := by
  obtain ⟨b, t⟩ := p
  cases b with
  | zero =>
    have h0 : (WeierstrassCurve.Affine.Point.zero : (curve L.g₂ L.g₃).toAffine.Point) = 0 := rfl
    simp [chartV, repV, h0, bi, ptO]
  | some x y h =>
    simp [chartV, repV, repB, bi, ptAff, WeierstrassCurve.Affine.Point.some_ne_zero]

theorem Pe_repV_ne (p : EVL L) : Pe (repV p) ≠ 0 := by rw [Pe_repV]; exact rep_ne_zero _

theorem constantCoeff_NLaw (i j k : Fin 2) (Y : Fin 5 → PowerSeries ℂ) (B : Fin 5 → ℂ) (l : Fin 5) :
    PowerSeries.constantCoeff (NLaw (alg L.g₂) (alg L.g₃) i j k Y (fun l => PowerSeries.C (B l)) l)
      = NLaw L.g₂ L.g₃ i j k (fun l => PowerSeries.constantCoeff (Y l)) B l := by
  rw [NLaw_map]
  congr 1 <;> first | simp [PowerSeries.algebraMap_apply] | (funext l'; simp)

/-- From a good law at `(g, h)` and a flow through `g`, the renormalized translate is a flow
through `g + h` (chart `chartV (g + h)`), on `X`. -/
theorem flow_through {g h : EVL L} {a : Fin 2} {s β : ℂ} {Y : Fin 5 → PowerSeries ℂ}
    (hY : IsBFlow L.g₂ L.g₃ a s β Y) (hYF : Fn (alg L.g₂) (alg L.g₃) Y = 0) (hYG : Gn Y = 0)
    (hY0 : ∀ l, PowerSeries.constantCoeff (Y l) = repV g l) (i j k : Fin 2)
    (hgood : NLaw L.g₂ L.g₃ i j k (repV g) (repV h) ≠ 0) :
    IsUnit (NLaw (alg L.g₂) (alg L.g₃) i j k Y (fun l => PowerSeries.C (repV h l))
        (bi (chartV (g + h)))) ∧
    let X := NLaw (alg L.g₂) (alg L.g₃) i j k Y (fun l => PowerSeries.C (repV h l))
    let Xt := Ring.inverse (X (bi (chartV (g + h)))) • X
    IsBFlow L.g₂ L.g₃ (chartV (g + h)) s β Xt ∧ Fn (alg L.g₂) (alg L.g₃) Xt = 0 ∧ Gn Xt = 0 ∧
      ∀ l, PowerSeries.constantCoeff (Xt l) = repV (g + h) l := by
  obtain ⟨μ, hμ0, hμ⟩ := NLaw_repV_ne g h i j k hgood
  set X := NLaw (alg L.g₂) (alg L.g₃) i j k Y (fun l => PowerSeries.C (repV h l)) with hX
  have hc : ∀ l, PowerSeries.constantCoeff (X l) = μ * repV (g + h) l := fun l => by
    rw [hX, constantCoeff_NLaw]
    have : (fun l => PowerSeries.constantCoeff (Y l)) = repV g := funext hY0
    rw [this, hμ]; rfl
  have hU : IsUnit (X (bi (chartV (g + h)))) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc, repV_chart, mul_one]
    exact hμ0.isUnit
  refine ⟨hU, ?_⟩
  intro X' Xt
  have hBF : Fn (algebraMap ℂ ℂ L.g₂) (algebraMap ℂ ℂ L.g₃) (repV h) = 0 := Fn_repV h
  have hfl := curve_block hY hYF hYG (B := repV h) hBF (Gn_repV h) i j k hU
  have hI : Inat (alg L.g₂) (alg L.g₃) Y (fun l => PowerSeries.C (repV h l)) = ⊥ := by
    have h1 : Fn (alg L.g₂) (alg L.g₃) (fun l => PowerSeries.C (repV h l)) = 0 := by
      have := Fn_map (PowerSeries.C : ℂ →+* PowerSeries ℂ) L.g₂ L.g₃ (repV h)
      rw [Fn_repV, map_zero] at this
      simpa [PowerSeries.algebraMap_apply, Function.comp_def] using this.symm
    have h2 : Gn (fun l => (PowerSeries.C (repV h l) : PowerSeries ℂ)) = 0 := by
      have := Gn_map (PowerSeries.C : ℂ →+* PowerSeries ℂ) (repV h)
      rw [Gn_repV, map_zero] at this
      simpa [Function.comp_def] using this.symm
    rw [Inat, hYF, hYG, h1, h2]; simp
  obtain ⟨hXF, hXG⟩ := NLaw_mem (alg L.g₂) (alg L.g₃) i j k Y (fun l => PowerSeries.C (repV h l))
  rw [hI, Submodule.mem_bot] at hXF hXG
  refine ⟨hfl, ?_, ?_, ?_⟩
  · show Fn _ _ (Ring.inverse (X (bi (chartV (g + h)))) • X) = 0
    have : ∀ (u : PowerSeries ℂ) (P : Fin 5 → PowerSeries ℂ),
        Fn (alg L.g₂) (alg L.g₃) (u • P) = u ^ 3 * Fn (alg L.g₂) (alg L.g₃) P := fun u P => by
      simp only [Fn, F, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hXF, mul_zero]
  · show Gn (Ring.inverse (X (bi (chartV (g + h)))) • X) = 0
    have : Gn (Ring.inverse (X (bi (chartV (g + h)))) • X) =
        Ring.inverse (X (bi (chartV (g + h)))) ^ 2 * Gn X := by
      simp only [Gn, Gfib, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hXG, mul_zero]
  · intro l
    have hn := congrArg PowerSeries.constantCoeff hfl.norm
    have hUi : Ring.inverse (X (bi (chartV (g + h)))) * X (bi (chartV (g + h))) = 1 :=
      Ring.inverse_mul_cancel _ hU
    have h1 := congrArg PowerSeries.constantCoeff hUi
    rw [map_mul, map_one, hc, repV_chart, mul_one] at h1
    show PowerSeries.constantCoeff (Ring.inverse (X (bi (chartV (g + h)))) * X l) = _
    rw [map_mul, hc, ← mul_assoc, h1, one_mul]

theorem exists_flow (p : EVL L) (s β : ℂ) :
    ∃ Z : Fin 5 → PowerSeries ℂ, IsBFlow L.g₂ L.g₃ (chartV p) s β Z ∧
      Fn (alg L.g₂) (alg L.g₃) Z = 0 ∧ Gn Z = 0 ∧
      ∀ l, PowerSeries.constantCoeff (Z l) = repV p l := by
  obtain ⟨i, j, k, hne⟩ := exists_NLaw_ne (0 : EVL L) p
  have hE := ExpBlock_isBFlow L.g₂ L.g₃ s β
  have hE0 : ∀ l, PowerSeries.constantCoeff (ExpBlock L.g₂ L.g₃ (2 * s) β l) =
      repV (0 : EVL L) l := fun l => by
    rw [constantCoeff_ExpBlock]; rfl
  obtain ⟨-, hfl, hF, hG, h0⟩ := flow_through hE (Fn_ExpBlock _ _ _ _) (Gn_ExpBlock _ _ _ _) hE0
    i j k hne
  rw [zero_add] at hfl hF hG h0
  exact ⟨_, hfl, hF, hG, h0⟩

/-- **The canonical flow** of `(2s, β)` through `p`. -/
noncomputable def ZB (p : EVL L) (s β : ℂ) : Fin 5 → PowerSeries ℂ :=
  (exists_flow p s β).choose

theorem ZB_spec (p : EVL L) (s β : ℂ) :
    IsBFlow L.g₂ L.g₃ (chartV p) s β (ZB p s β) ∧ Fn (alg L.g₂) (alg L.g₃) (ZB p s β) = 0 ∧
      Gn (ZB p s β) = 0 ∧ ∀ l, PowerSeries.constantCoeff (ZB p s β l) = repV p l :=
  (exists_flow p s β).choose_spec

theorem eq_ZB {p : EVL L} {s β : ℂ} {Z : Fin 5 → PowerSeries ℂ}
    (hZ : IsBFlow L.g₂ L.g₃ (chartV p) s β Z) (h0 : ∀ l, PowerSeries.constantCoeff (Z l) = repV p l) :
    Z = ZB p s β :=
  eq_of_isBFlow hZ (ZB_spec p s β).1 fun l => by rw [h0, (ZB_spec p s β).2.2.2]

theorem ExpBlock_eq (s β : ℂ) : ExpBlock L.g₂ L.g₃ (2 * s) β = ZB (0 : EVL L) s β :=
  eq_ZB (ExpBlock_isBFlow L.g₂ L.g₃ s β) fun l => by rw [constantCoeff_ExpBlock]; rfl

/-- **Formal associativity.** Every law value at `(ZB g, rep h)` or `(rep h, ZB g)` is its chart
coordinate times `ZB (g + h)`. -/
theorem laws_eq (g h : EVL L) (s β : ℂ) {A : Fin 5 → PowerSeries ℂ}
    (hA : A ∈ lawsAt (alg L.g₂) (alg L.g₃) (ZB g s β) (fun l => PowerSeries.C (repV h l))) :
    A = A (bi (chartV (g + h))) • ZB (g + h) s β := by
  obtain ⟨hZ, hZF, hZG, hZ0⟩ := ZB_spec g s β
  obtain ⟨i, j, k, hne⟩ := exists_NLaw_ne g h
  obtain ⟨hU, hfl, -, -, h0⟩ := flow_through hZ hZF hZG hZ0 i j k hne
  have hXt := eq_ZB hfl h0
  have := curve_all hZ hZF hZG (B := repV h) (Fn_repV h) (Gn_repV h) (Pe_repV_ne h) i j k hU hA
  rw [hXt] at this
  exact this

end Canon

end LSG.MEV
