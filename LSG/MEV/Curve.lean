import Mathlib
import LSG.MEV.FibreId
import LSG.MEV.Flow
import LSG.MEV.Prop
import LSG.ME.PhOpCurve

/-!
# The `E^♮` curve lemma (one block)

**`curve_block`**: let `Y` be a flow of `(2s, β)` normalized in chart `a`, on `X = V(F, G)`, and `B`
a point of `X` with coordinates in the base ring `R`. For a law `c₀ = (i, j, k)` whose `T_b`-chart
coordinate `U` at `(Y, B)` is a unit, the renormalized translate `U⁻¹ · NLaw_{c₀}(Y, B)` is again a
flow of `(2s, β)`, normalized in chart `b`. Ingredients:
* base coordinates: the abelian translation identity `LSG.ME.tr_eq` and `LSG.ME.renorm_deriv`
  (the base part of `NLaw` is `2λμ · law_i`);
* fibre coordinate: `starA` (the `T_μ(B)`-terms cancel and the `T_λ(Y)`-terms give
  `4μ²L²(λ D T_λ − T_λ D λ)`), `psi_flow` (that bracket along the flow), and the generated identity
  `fib_eq`; the other fibre coordinate from `G = 0`.

**`curve_all`**: over a domain `R` of characteristic `0`, every law at `(Y, B)` and at `(B, Y)` is
`(its T_b-chart coordinate) •` the renormalized flow (`nlaw_cross`).
-/

open LSG.Elliptic
open LSG.ME (c2 D_ofNat)

namespace LSG.MEV

section Struct

variable {T : Type*} [CommRing T] (g₂ g₃ : T) (i j k : Fin 2) (P Q : Fin 5 → T)

theorem Pe_NLaw : Pe (NLaw g₂ g₃ i j k P Q) =
    fun l => 2 * (mult j (Pe P) * mult k (Pe Q)) * lawSel g₂ g₃ i (Pe P) (Pe Q) l := by
  funext l; fin_cases l <;> rfl

theorem mult_NLaw (b : Fin 2) : mult b (Pe (NLaw g₂ g₃ i j k P Q)) =
    2 * (mult j (Pe P) * mult k (Pe Q)) * lawSel g₂ g₃ i (Pe P) (Pe Q) (biE b) := by
  fin_cases b <;> rfl

theorem tcoord_NLaw (b : Fin 2) : tcoord b (NLaw g₂ g₃ i j k P Q) =
    2 * mult k (Pe Q) * lawSel g₂ g₃ i (Pe P) (Pe Q) (biE b) * tcoord j P +
      2 * mult j (Pe P) * lawSel g₂ g₃ i (Pe P) (Pe Q) (biE b) * tcoord k Q -
      kapB b g₂ g₃ i j k (Pe P) (Pe Q) := by
  fin_cases b <;> rfl

theorem lawSel_eq_lawc (i : Fin 2) (P Q : Fin 3 → T) :
    lawSel g₂ g₃ i P Q = LSG.ME.lawc i g₂ g₃ P Q := by
  fin_cases i <;> simp [lawSel, LSG.ME.lawc]

end Struct

/-- The derivative bracket of a law value (the `T_μ(B)`-terms cancel). -/
theorem starA {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (D : Derivation S T T)
    (lam mu L t t' κ : T) (hmu : D mu = 0) (ht' : D t' = 0) :
    (2 * (lam * mu) * L) * D (2 * mu * L * t + 2 * lam * L * t' - κ) -
      (2 * mu * L * t + 2 * lam * L * t' - κ) * D (2 * (lam * mu) * L) =
    4 * mu ^ 2 * L ^ 2 * (lam * D t - t * D lam) -
      ((2 * (lam * mu) * L) * D κ - κ * D (2 * (lam * mu) * L)) := by
  simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul, D_ofNat, hmu, ht']
  ring

section Curve

variable {K : Type*} [Field K] [CharZero K] {R : Type*} [CommRing R] [Algebra K R]
  {g₂ g₃ : K}

local notation "dz" => (PowerSeries.derivative (R := R))
local notation "alg" => algebraMap K (PowerSeries R)

theorem dz_alg (x : K) : dz (alg x) = 0 := by
  rw [PowerSeries.algebraMap_apply]; exact PowerSeries.derivative_C

section Psi

variable {s β : K} {Y : Fin 5 → PowerSeries R}

theorem psi_diag {a : Fin 2} (hY : IsBFlow g₂ g₃ a s β Y) :
    mult a (Pe Y) * dz (tcoord a Y) - tcoord a Y * dz (mult a (Pe Y)) =
      mult a (Pe Y) ^ 2 * alg β +
        (mult a (Pe Y) ^ 2 * (2 * alg s * rhoh a (alg g₂) (alg g₃) (Pe Y)) + epsT dz a a (Pe Y)) := by
  have he : epsT dz a a (Pe Y) = 0 := by fin_cases a <;> rfl
  rw [hY.fib, he, mult_Pe, hY.norm, Derivation.map_one_eq_zero]
  ring

theorem psi_10 (hY : IsBFlow g₂ g₃ 1 s β Y) (hG : Gn Y = 0) :
    mult 0 (Pe Y) * dz (tcoord 0 Y) - tcoord 0 Y * dz (mult 0 (Pe Y)) =
      mult 0 (Pe Y) ^ 2 * alg β +
        (mult 0 (Pe Y) ^ 2 * (2 * alg s * rhoh 1 (alg g₂) (alg g₃) (Pe Y)) + epsT dz 1 0 (Pe Y)) := by
  have h2 : Y 2 = 1 := hY.norm
  have hG' : Y 2 * Y 4 - Y 1 * Y 3 + 2 * Y 0 ^ 2 = 0 := hG
  simp only [mult, tcoord, epsT, rhoh, Pe, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [hY.ode 4, hY.ode 1, hY.ode 0]
  simp only [dvalB, c2, rhoh, Pe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, h2] at hG' ⊢
  linear_combination (-(alg s * (12 * Y 0 ^ 2 - 1 ^ 2 * alg g₂))) * hG'

theorem psi_01 (hY : IsBFlow g₂ g₃ 0 s β Y) (hG : Gn Y = 0) :
    mult 1 (Pe Y) * dz (tcoord 1 Y) - tcoord 1 Y * dz (mult 1 (Pe Y)) =
      mult 1 (Pe Y) ^ 2 * alg β +
        (mult 1 (Pe Y) ^ 2 * (2 * alg s * rhoh 0 (alg g₂) (alg g₃) (Pe Y)) + epsT dz 0 1 (Pe Y)) := by
  have h1 : Y 1 = 1 := hY.norm
  have hG' : Y 2 * Y 4 - Y 1 * Y 3 + 2 * Y 0 ^ 2 = 0 := hG
  simp only [mult, tcoord, epsT, rhoh, Pe, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [hY.ode 3, hY.ode 2, hY.ode 0]
  simp only [dvalB, c2, rhoh, Pe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, h1] at hG' ⊢
  linear_combination (alg s * (-12 * Y 0 ^ 2 + Y 2 ^ 2 * alg g₂)) * hG'

/-- `λ D(T_λ) − T_λ D(λ)` along a normalized flow on `G = 0`. -/
theorem psi_flow {a : Fin 2} (hY : IsBFlow g₂ g₃ a s β Y) (hG : Gn Y = 0) (j : Fin 2) :
    mult j (Pe Y) * dz (tcoord j Y) - tcoord j Y * dz (mult j (Pe Y)) =
      mult j (Pe Y) ^ 2 * alg β +
        (mult j (Pe Y) ^ 2 * (2 * alg s * rhoh a (alg g₂) (alg g₃) (Pe Y)) + epsT dz a j (Pe Y)) := by
  fin_cases a <;> fin_cases j
  · exact psi_diag hY
  · exact psi_01 hY hG
  · exact psi_10 hY hG
  · exact psi_diag hY

end Psi

variable [IsDomain R]

/-- **The `E^♮` curve lemma.** -/
theorem curve_block {a b : Fin 2} {s β : K} {Y : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) (hYF : Fn (alg g₂) (alg g₃) Y = 0) (hYG : Gn Y = 0)
    {B : Fin 5 → R} (hBF : Fn (algebraMap K R g₂) (algebraMap K R g₃) B = 0) (hBG : Gn B = 0)
    (i j k : Fin 2)
    (hU : IsUnit (NLaw (alg g₂) (alg g₃) i j k Y (fun l => PowerSeries.C (B l)) (bi b))) :
    IsBFlow g₂ g₃ b s β (Ring.inverse (NLaw (alg g₂) (alg g₃) i j k Y
      (fun l => PowerSeries.C (B l)) (bi b)) • NLaw (alg g₂) (alg g₃) i j k Y
        (fun l => PowerSeries.C (B l))) := by
  set CB : Fin 5 → PowerSeries R := fun l => PowerSeries.C (B l) with hCB
  set X := NLaw (alg g₂) (alg g₃) i j k Y CB with hX
  set U := X (bi b) with hUdef
  set Ui := Ring.inverse U with hUidef
  have hUi : Ui * U = 1 := Ring.inverse_mul_cancel _ hU
  have halg : ∀ x : K, alg x = PowerSeries.C (algebraMap K R x) :=
    fun x => PowerSeries.algebraMap_apply
  have hCBF : Fn (alg g₂) (alg g₃) CB = 0 := by
    have := Fn_map (PowerSeries.C : R →+* PowerSeries R) (algebraMap K R g₂) (algebraMap K R g₃) B
    rw [hBF, map_zero] at this
    rw [halg, halg]; exact this.symm
  have hCBG : Gn CB = 0 := by
    have := Gn_map (PowerSeries.C : R →+* PowerSeries R) B
    rw [hBG, map_zero] at this; exact this.symm
  have hI : Inat (alg g₂) (alg g₃) Y CB = ⊥ := by rw [Inat, hYF, hYG, hCBF, hCBG]; simp
  obtain ⟨hXF, hXG⟩ := NLaw_mem (alg g₂) (alg g₃) i j k Y CB
  rw [hI, Submodule.mem_bot] at hXF hXG
  -- abbreviations
  set lam := mult j (Pe Y) with hlam
  set mu := mult k (Pe CB) with hmu
  set l := lawSel (alg g₂) (alg g₃) i (Pe Y) (Pe CB) with hl
  set L := l (biE b) with hL
  have hU_eq : U = 2 * (lam * mu) * L := by
    rw [hUdef, ← mult_Pe b X, hX, mult_NLaw]
  have hPeX : Pe X = fun l' => 2 * (lam * mu) * l l' := Pe_NLaw _ _ _ _ _ _ _
  have hdmu : dz mu = 0 := by
    rw [hmu, mult_Pe]; exact PowerSeries.derivative_C
  have hdt' : dz (tcoord k CB) = 0 := by rw [tcoord_eq]; exact PowerSeries.derivative_C
  have hQ : ∀ j, dz (Pe CB j) = 0 := fun j => by rw [Pe_apply]; exact PowerSeries.derivative_C
  have hPa : Pe Y (biE a) = 1 := by rw [← mult_eq a (Pe Y), mult_Pe]; exact hY.norm
  have hFv : Fv (alg g₂) (alg g₃) (Pe Y) = 0 := hYF
  have hFvQ : Fv (alg g₂) (alg g₃) (Pe CB) = 0 := hCBF
  -- the fibre identity
  obtain ⟨f₁, f₂, hfib⟩ := fib_eq dz i j k a b (alg g₂) (alg g₃) (alg s) (Pe Y) (Pe CB)
    (dz_alg g₂) (dz_alg g₃) hQ hY.base hPa
  rw [hFv, hFvQ, mul_zero, mul_zero, add_zero] at hfib
  have hstar : U * dz (X (ti b)) - X (ti b) * dz U =
      alg β * U ^ 2 + 2 * alg s * rhoh b (alg g₂) (alg g₃) (Pe X) := by
    rw [← tcoord_eq b X, hX, tcoord_NLaw, ← hX, hU_eq, ← hlam, ← hmu, ← hl, ← hL,
      starA dz lam mu L _ _ _ hdmu hdt', psi_flow hY hYG j, hPeX]
    unfold fibE at hfib
    linear_combination hfib
  -- the base translation identity
  have hbase : ∀ i' : Fin 3, L * dz (l i') = alg s * c2 (biE b) (alg g₂) (alg g₃) l i' +
      alg s * (LSG.ME.trE i (biE a) (biE b) (alg g₂) (alg g₃) (Pe Y) (Pe CB) * l i') := by
    intro i'
    have ha : biE a ≠ 0 := by fin_cases a <;> decide
    have hb : biE b ≠ 0 := by fin_cases b <;> decide
    obtain ⟨e₁, e₂, he⟩ := LSG.ME.tr_eq dz i ha hb (alg g₂) (alg g₃) (alg s) (Pe Y) (Pe CB)
      (dz_alg g₂) (dz_alg g₃) hQ hY.base i'
    rw [hFv, hFvQ, mul_zero, mul_zero, add_zero, mul_zero, hPa, one_mul] at he
    rw [hL, hl, lawSel_eq_lawc]
    linear_combination he
  set Li := Ui * (2 * (lam * mu)) with hLi
  have hLiL : Li * L = 1 := by rw [hLi, mul_assoc, ← hU_eq]; exact hUi
  have hXt : ∀ i' : Fin 3, (Ui • X) i'.castSucc.castSucc = Li * l i' := fun i' => by
    have := congrFun hPeX i'
    rw [Pe_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, this, hLi]; ring
  have hPeXt : Pe (Ui • X) = Li • l := by
    funext i'; rw [Pe_apply, hXt]; rfl
  have hrenorm : ∀ i' : Fin 3, dz (Li * l i') = alg s * c2 (biE b) (alg g₂) (alg g₃) (Li • l) i' :=
    fun i' => LSG.ME.renorm_deriv (by fin_cases b <;> decide) hbase hLiL i'
  have hnorm : (Ui • X) (bi b) = 1 := by simp only [Pi.smul_apply, smul_eq_mul]; exact hUi
  -- derivative of `Ui`
  have hdUi : dz Ui = -Ui ^ 2 * dz U := by
    have h := congrArg dz hUi
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination Ui * h - dz Ui * hUi
  have hfibt : dz ((Ui • X) (ti b)) = alg β + 2 * alg s * rhoh b (alg g₂) (alg g₃) (Pe (Ui • X)) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdUi, Pe_smul, rhoh_smul]
    linear_combination Ui ^ 2 * hstar - (Ui * dz (X (ti b)) - alg β * (1 + Ui * U)) * hUi
  have hGt : Gn (Ui • X) = 0 := by
    have : Gn (Ui • X) = Ui ^ 2 * Gn X := by simp only [Gn, Gfib, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hXG, mul_zero]
  have hbase' : ∀ i' : Fin 3, dz ((Ui • X) i'.castSucc.castSucc) =
      (Ui • X) (bi b) * (alg s * c2 (biE b) (alg g₂) (alg g₃) (Pe (Ui • X)) i') := by
    intro i'; rw [hnorm, one_mul, hXt, hrenorm, hPeXt]
  refine ⟨hnorm, ?_⟩
  set Xt := Ui • X with hXtdef
  simp only [Gn, Gfib] at hGt
  fin_cases b
  · -- chart `V`
    have h1 : Xt 1 = 1 := hnorm
    have e0 : dz (Xt 0) = Xt 1 * (alg s * c2 1 (alg g₂) (alg g₃) (Pe Xt) 0) := hbase' 0
    have e1 : dz (Xt 1) = Xt 1 * (alg s * c2 1 (alg g₂) (alg g₃) (Pe Xt) 1) := hbase' 1
    have e2 : dz (Xt 2) = Xt 1 * (alg s * c2 1 (alg g₂) (alg g₃) (Pe Xt) 2) := hbase' 2
    have e4 : dz (Xt 4) = alg β + 2 * alg s * rhoh 0 (alg g₂) (alg g₃) (Pe Xt) := hfibt
    have hT : Xt 3 = Xt 2 * Xt 4 + 2 * Xt 0 ^ 2 := by rw [h1] at hGt; linear_combination -hGt
    have e3 : dz (Xt 3) = alg s * c2 1 (alg g₂) (alg g₃) (Pe Xt) 2 * Xt 4 +
        Xt 2 * (alg β * Xt 1 ^ 2 + 2 * alg s * rhoh 0 (alg g₂) (alg g₃) (Pe Xt)) +
        4 * Xt 0 * (alg s * c2 1 (alg g₂) (alg g₃) (Pe Xt) 0) := by
      rw [hT]
      simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, D_ofNat, e2, e4,
        e0, h1, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero]
      ring
    intro l'
    fin_cases l'
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · show dz (Xt 4) = Xt 1 * (alg β * Xt 1 ^ 2 + 2 * alg s * rhoh 0 (alg g₂) (alg g₃) (Pe Xt))
      rw [e4, h1]; ring
  · -- chart `W`
    have h2 : Xt 2 = 1 := hnorm
    have e0 : dz (Xt 0) = Xt 2 * (alg s * c2 2 (alg g₂) (alg g₃) (Pe Xt) 0) := hbase' 0
    have e1 : dz (Xt 1) = Xt 2 * (alg s * c2 2 (alg g₂) (alg g₃) (Pe Xt) 1) := hbase' 1
    have e2 : dz (Xt 2) = Xt 2 * (alg s * c2 2 (alg g₂) (alg g₃) (Pe Xt) 2) := hbase' 2
    have e3 : dz (Xt 3) = alg β + 2 * alg s * rhoh 1 (alg g₂) (alg g₃) (Pe Xt) := hfibt
    have hT : Xt 4 = Xt 1 * Xt 3 - 2 * Xt 0 ^ 2 := by rw [h2] at hGt; linear_combination hGt
    intro l'
    fin_cases l'
    · exact e0
    · exact e1
    · exact e2
    · show dz (Xt 3) = Xt 2 * (alg β * Xt 2 ^ 2 + 2 * alg s * rhoh 1 (alg g₂) (alg g₃) (Pe Xt))
      rw [e3, h2]; ring
    · show dz (Xt 4) = alg s * c2 2 (alg g₂) (alg g₃) (Pe Xt) 1 * Xt 3 +
        Xt 1 * (alg β * Xt 2 ^ 2 + 2 * alg s * rhoh 1 (alg g₂) (alg g₃) (Pe Xt)) -
        4 * Xt 0 * (alg s * c2 2 (alg g₂) (alg g₃) (Pe Xt) 0)
      rw [hT]
      simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, D_ofNat, e1, e3,
        e0, h2, nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero]
      ring

/-- **Every law is a multiple of the renormalized flow** (cross identity over the domain `R⟦z⟧`). -/
theorem curve_all [CharZero R] {a b : Fin 2} {s β : K} {Y : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) (hYF : Fn (alg g₂) (alg g₃) Y = 0) (hYG : Gn Y = 0)
    {B : Fin 5 → R} (hBF : Fn (algebraMap K R g₂) (algebraMap K R g₃) B = 0) (hBG : Gn B = 0)
    (hB0 : Pe B ≠ 0) (i j k : Fin 2)
    (hU : IsUnit (NLaw (alg g₂) (alg g₃) i j k Y (fun l => PowerSeries.C (B l)) (bi b)))
    {A : Fin 5 → PowerSeries R}
    (hA : A ∈ lawsAt (alg g₂) (alg g₃) Y (fun l => PowerSeries.C (B l))) :
    A = A (bi b) • (Ring.inverse (NLaw (alg g₂) (alg g₃) i j k Y
      (fun l => PowerSeries.C (B l)) (bi b)) • NLaw (alg g₂) (alg g₃) i j k Y
        (fun l => PowerSeries.C (B l))) := by
  set CB : Fin 5 → PowerSeries R := fun l => PowerSeries.C (B l) with hCB
  set X := NLaw (alg g₂) (alg g₃) i j k Y CB with hX
  have hCinj : Function.Injective (PowerSeries.C : R → PowerSeries R) := fun x y h => by
    simpa using congrArg (PowerSeries.coeff 0) h
  have : CharZero (PowerSeries R) := charZero_of_injective_ringHom hCinj
  have halg : ∀ x : K, alg x = PowerSeries.C (algebraMap K R x) :=
    fun x => PowerSeries.algebraMap_apply
  have hCBF : Fn (alg g₂) (alg g₃) CB = 0 := by
    have := Fn_map (PowerSeries.C : R →+* PowerSeries R) (algebraMap K R g₂) (algebraMap K R g₃) B
    rw [hBF, map_zero] at this
    rw [halg, halg]; exact this.symm
  have hCBG : Gn CB = 0 := by
    have := Gn_map (PowerSeries.C : R →+* PowerSeries R) B
    rw [hBG, map_zero] at this; exact this.symm
  have hY0 : Pe Y ≠ 0 := fun h => by
    have := congrFun h (biE a)
    rw [← mult_eq a (Pe Y), mult_Pe, hY.norm] at this
    exact one_ne_zero this
  have hCB0 : Pe CB ≠ 0 := fun h => hB0 (by
    funext l; have := congrFun h l
    simp only [Pe_apply, Pi.zero_apply, CB] at this ⊢
    exact hCinj (by rw [this, map_zero]))
  have hXmem : X ∈ lawsAt (alg g₂) (alg g₃) Y CB := ⟨i, j, k, Or.inl rfl⟩
  have hUi : Ring.inverse (X (bi b)) * X (bi b) = 1 := Ring.inverse_mul_cancel _ hU
  funext l
  have hc := nlaw_cross hYF hYG hY0 hCBF hCBG hCB0 hA hXmem l (bi b)
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (Ring.inverse (X (bi b))) * hc - A l * hUi

end Curve

end LSG.MEV
