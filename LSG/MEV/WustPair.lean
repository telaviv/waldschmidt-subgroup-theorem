import Mathlib
import LSG.MEV.HomWords
import LSG.MEV.SubgroupCompV

/-!
# The Wüstholz pairing at the cosets of `H⁰` (vector-extension class)

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)`, `H⁰ = H0 Ls hH` and a point `a`, the pairing
`π_a(w, P) = (Dv_{chartsV a} w P)(coords a 1)` on `Lie G̃ × I(a + H⁰)` (canonical charts at `a`;
at `coords a 1` this is also the homogenised `Dhc`, `eval_DL_Dhc_chartsV`).

* `toTan`: the coordinate change `LieV → TanG` (`(ζ, β)` per block to the two `Fin m` vectors);
  `lieAlgL hH = (lieAlg hH).comap toTan`.
* `coords_zero_eq_FV`, `chartsV_zero`, **`eval_Dv_zero`**: at the identity, `π_0` is the pairing of
  the subgroup layer (`(D̂_{toTan w} P)(FV 0)`, `TZ`).
* **`coeff_one_sclV_ZG`** (first order along a rescaled canonical flow): for `P ∈ I(E)`, `g ∈ E`
  and `U_k(0) ≠ 0`, `[z¹] P(sclV U (ZG g w)) = π_g(w, scl U(0) P)` (the `U′(0)`-terms are block
  Euler terms, which vanish on cone points of `E`).
* `transl_mem_vanish_gtransl`: `τ_{−σ}` maps `I(V)` into `I(σ + V)`.
* **`mem_lieAlgL_of_ker`**: the left kernel of `π_a` on `I(a + H⁰)` lies in `lieAlg H`, for every
  `a`. Proof: translate `Q ∈ I(H⁰)` to `τ_{−a} Q ∈ I(a + H⁰)`, use `transl_phPt_eq` (formal
  associativity) to compare `[z¹]` of `(τ_{−a} Q)(phPt a w)` and `Q(ZG 0 w)` up to rescalings, and
  conclude with `TZ_eq_lieAlg`. (No translation identity for derivations is needed.)
* `eval_Dv_zero_of_mem`: `lieAlg H` is in the left kernel of `π_0` on `I(H⁰)`.
* `pairV`: `π` as a bilinear map.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk c2)
open StrongSix.M2 (DL DL_cons)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Coordinates -/

/-- Lie-algebra coordinates: `LieV` (pairs per block) to `TanG`. -/
def toTan : LieV ℂ d₀ d₁ m →ₗ[ℂ] TanG d₀ d₁ m where
  toFun w := (w.1, w.2.1, fun k => (w.2.2 k).1, fun k => (w.2.2 k).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (Ls) in
/-- The Lie algebra of `H` in `LieV` coordinates. -/
def lieAlgL {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) : Submodule ℂ (LieV ℂ d₀ d₁ m) :=
  (lieAlg Ls hH).comap toTan

theorem mem_lieAlgL {H : Set (GPtV d₀ d₁ Ls)} {hH : IsSubgroupG H} {w : LieV ℂ d₀ d₁ m} :
    w ∈ lieAlgL Ls hH ↔ toTan w ∈ lieAlg Ls hH := Iff.rfl

theorem coords_zero_eq_FV : coords (0 : GPtV d₀ d₁ Ls) 1 = FV Ls 0 := by
  funext v
  cases v with
  | x i => rw [a0_x]; rfl
  | y j => rw [a0_y]; simp [coords]
  | z j => rw [a0_z]; simp [coords]
  | e k c => rw [a0_e]; simp [coords, repV]

theorem chartsV_zero : chartsV (0 : GPtV d₀ d₁ Ls) = fun _ => 0 := by
  funext k; simp [chartsV, chartV]

theorem dvalB_zero_eq_bField (g₂ g₃ a b : ℂ) (P : Fin 5 → ℂ) (c : Fin 5) :
    dvalB 0 g₂ g₃ (a / 2) b P c = bField g₂ g₃ a b P c := by
  fin_cases c <;> simp [dvalB, bField, c2, rhoh, Pe] <;> first | ring1 | exact Or.inl (Or.inl (by ring))

theorem eval_dvV_e (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (k : Fin m)
    (c : Fin 5) : eval y (dvV Ls ch w (.e k c)) =
      dvalB (ch k) (g2L Ls k) (g3L Ls k) ((w.2.2 k).1 / 2) (w.2.2 k).2 (fun i => y (.e k i)) c := by
  simp only [dvV]
  rw [dvalB_map (eval y)]
  simp [bvars, Function.comp_def]

/-- **At the identity, `π_0` is the pairing of the subgroup layer.** -/
theorem eval_Dv_zero (w : LieV ℂ d₀ d₁ m) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (coords (0 : GPtV d₀ d₁ Ls) 1) (Dv Ls (chartsV (0 : GPtV d₀ d₁ Ls)) w Q) =
      eval (FV Ls 0) (Dh Ls (toTan w) Q) := by
  rw [Dv_eq_sum, eval_Dh, coords_zero_eq_FV, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, mul_comm, DV_of_V Ls (fun k => FV_V goodV_zero k)]
  congr 1
  cases v with
  | x i => simp [dvV, dvalE, toTan]
  | y j => simp [dvV, dvalE, toTan]
  | z j => simp [dvV, dvalE, toTan]
  | e k c =>
    rw [eval_dvV_e, chartsV_zero]
    simp only [dvalE, toTan, LinearMap.coe_mk, AddHom.coe_mk]
    exact dvalB_zero_eq_bField _ _ _ _ _ c

theorem dvalB_zero_eq_bField' {R : Type*} [CommRing R] [Algebra ℂ R] (g₂ g₃ a b : R)
    (P : Fin 5 → R) (c : Fin 5) :
    dvalB 0 g₂ g₃ (algebraMap ℂ R (1 / 2) * a) b P c = bField g₂ g₃ a b P c := by
  have h2 : algebraMap ℂ R 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ R) 2, ← map_mul, inv_mul_cancel₀ (two_ne_zero' ℂ), map_one]
  fin_cases c
  · simp [dvalB, bField, c2, rhoh, Pe]
    linear_combination (-(a * P 1 * g₂ * P 0 * P 2)) * h2
  · simp [dvalB, bField, c2, rhoh, Pe]
  · simp [dvalB, bField, c2, rhoh, Pe]
    linear_combination (-(6 * a * P 1 * P 0 ^ 2)) * h2
  · simp [dvalB, bField, c2, rhoh, Pe]
    linear_combination (-(6 * a * P 0 ^ 2 * P 4) + a * P 2 * (2 * g₂ * P 0 ^ 2 +
      3 * g₃ * P 0 * P 2) - 4 * a * P 0 ^ 2 * P 2 * g₂) * h2
  · simp [dvalB, bField, c2, rhoh, Pe]
    linear_combination (P 1 * a * (2 * g₂ * P 0 ^ 2 + 3 * g₃ * P 0 * P 2)) * h2

/-- **The merge**: in the `V`-chart, `Dhc` is the subgroup layer's `D̂` (`ChartDerivV.Dh`). -/
theorem Dhc_V_eq_Dh (w : LieV ℂ d₀ d₁ m) : Dhc Ls (fun _ => 0) w = Dh Ls (toTan w) := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Dhc_X, Dh, mkDerivation_X, dvh]
  cases v with
  | x i => simp [facV, Lcv, Vfac, dvV, dvalV, toTan, bi]
  | y j => simp [facV, Lcv, Vfac, dvV, dvalV, toTan, bi]
  | z j => simp [facV, Lcv, Vfac, dvV, dvalV, toTan, bi]
  | e k c =>
    simp only [facV, Lov, Vfac, dvV, dvalV, toTan, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    rw [← dvalB_zero_eq_bField']
    congr 1
    rw [MvPolynomial.algebraMap_eq, ← C_mul]
    congr 1; ring

/-! ### First order along rescaled canonical flows -/

theorem constCoeff_aeval_eval (Γ : Var d₀ d₁ m → PowerSeries ℂ)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    PowerSeries.constantCoeff (aeval Γ Q) = eval (fun v => PowerSeries.constantCoeff (Γ v)) Q := by
  rw [LSG.ME.constantCoeff_aeval (K := ℂ)]; rfl

theorem const_sclV_ZG (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (U : Fin m → PowerSeries ℂ) :
    (fun v => PowerSeries.constantCoeff (sclV U (ZG Ls g w) v)) =
      scaleV (fun k => PowerSeries.constantCoeff (U k)) (coords g 1) := by
  funext v
  have h := congrFun (const_ZG g w) v
  cases v with
  | e k c => simp only [sclV, scaleV_e, map_mul]; rw [h]
  | x i => simp only [sclV, scaleV_x]; exact h
  | y j => simp only [sclV, scaleV_y]; exact h
  | z j => simp only [sclV, scaleV_z]; exact h

theorem const_deriv_ZG (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    PowerSeries.constantCoeff (PowerSeries.derivative (ZG Ls g w v)) =
      eval (coords g 1) (dvV Ls (chartsV g) w v) := by
  rw [ZG_isVFlow g w v, LSG.ME.constantCoeff_aeval (K := ℂ), const_ZG]; rfl

theorem blockPart_coords (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂˣ) (k : Fin m) (v : Var d₀ d₁ m) :
    blockPart k (coords g ν) v = (ν k : ℂ) * blockPart k (coords g 1) v := by
  cases v with
  | e k' c => by_cases hk : k' = k <;> simp [blockPart, hk, coords]
  | x i => simp [blockPart]
  | y j => simp [blockPart]
  | z j => simp [blockPart]

/-- **First order along a rescaled canonical flow.** -/
theorem coeff_one_sclV_ZG {E : Set (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ vanish E) {g : GPtV d₀ d₁ Ls} (hg : g ∈ E) (w : LieV ℂ d₀ d₁ m)
    (U : Fin m → PowerSeries ℂ) (hU : ∀ k, PowerSeries.constantCoeff (U k) ≠ 0) :
    PowerSeries.coeff 1 (aeval (sclV U (ZG Ls g w)) P) =
      eval (coords g 1) (Dv Ls (chartsV g) w (scl (fun k => PowerSeries.constantCoeff (U k)) P)) := by
  classical
  set U₀ : Fin m → ℂ := fun k => PowerSeries.constantCoeff (U k)
  set y₁ := coords g 1
  set u : Var d₀ d₁ m → ℂ := fun v => eval y₁ (dvV Ls (chartsV g) w v)
  set cU : Fin m → ℂ := fun k => PowerSeries.constantCoeff (PowerSeries.derivative (U k))
  set ν : Fin m → ℂˣ := fun k => Units.mk0 (U₀ k) (hU k)
  have hy : scaleV U₀ y₁ = coords g ν := by
    have := scaleV_coords ν g 1
    simp only [Pi.one_apply, mul_one] at this
    exact this
  have hd : ∀ v, PowerSeries.constantCoeff (PowerSeries.derivative (sclV U (ZG Ls g w) v)) =
      scaleV U₀ u v + ∑ k, cU k * blockPart k y₁ v := by
    intro v
    cases v with
    | e k c =>
      simp only [sclV, scaleV_e]
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        const_deriv_ZG, Finset.sum_eq_single k (fun b _ hb => by simp [blockPart, Ne.symm hb])
          (by simp)]
      have := congrFun (const_ZG g w) (.e k c)
      simp only [blockPart, ite_true]
      rw [this]
      ring
    | x i => simp [sclV, blockPart, const_deriv_ZG, u, y₁]
    | y j => simp [sclV, blockPart, const_deriv_ZG, u, y₁]
    | z j => simp [sclV, blockPart, const_deriv_ZG, u, y₁]
  have heuler : ∀ k, ∑ v, eval (scaleV U₀ y₁) (pderiv v P) * blockPart k y₁ v = 0 := by
    intro k
    have h := euler_eq_zero hP hg ν k
    simp only [blockPart_coords g ν k] at h
    rw [← hy] at h
    simp only [mul_left_comm _ ((ν k : ℂ)), ← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left (ν k).ne_zero
  have hkey : PowerSeries.coeff 1 (aeval (sclV U (ZG Ls g w)) P) =
      PowerSeries.constantCoeff (PowerSeries.derivative (aeval (sclV U (ZG Ls g w)) P)) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  rw [hkey, LSG.ME.derivative_aeval, map_sum]
  simp only [map_mul, constCoeff_aeval_eval, const_sclV_ZG, hd]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  have h0 : ∀ k ∈ Finset.univ, ∑ v, eval (scaleV U₀ y₁) (pderiv v P) * (cU k * blockPart k y₁ v)
      = 0 := fun k _ => by
    simp only [mul_left_comm _ (cU k), ← Finset.mul_sum, heuler k, mul_zero]
  rw [Finset.sum_eq_zero h0, add_zero, Dv_eq_sum, map_sum]
  have := dir_scl U₀ y₁ u P
  rw [← this]
  exact Finset.sum_congr rfl fun v _ => by rw [map_mul]; ring

/-! ### Translations -/

theorem transl_mem_vanish_gtransl (σ : GPtV d₀ d₁ Ls) (c : Fin m → LC) {V : Set (GPtV d₀ d₁ Ls)}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ vanish V) :
    τ Ls (-σ) c P ∈ vanish (gtransl σ V) := by
  refine mem_vanish.mpr fun h hh lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl (-σ) h c lam
  rw [hν]
  refine eval_coordsZ_eq_zero (fun lam' => mem_vanish.mp hP _ ?_ lam') ν
  rw [← sub_eq_add_neg]; exact mem_gtransl.mp hh

/-! ### The left kernel of the pairing -/

section Kernel

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **The left kernel of `π_a` on `I(a + H⁰)` lies in `lieAlg H`.** -/
theorem mem_lieAlgL_of_ker (a : GPtV d₀ d₁ Ls) {w : LieV ℂ d₀ d₁ m}
    (hw : ∀ P ∈ vanish (gtransl a (H0 Ls hH)), eval (coords a 1) (Dv Ls (chartsV a) w P) = 0) :
    w ∈ lieAlgL Ls hH := by
  classical
  obtain ⟨c, hcg⟩ := exists_good a (-a)
  obtain ⟨c', hc'⟩ := exists_goodLaw a 0
  set u' : Fin m → PowerSeries ℂ := fun k => phPt Ls a w c' (.e k (bi (chartV (a.2.2 k))))
  have hu' : ∀ k, PowerSeries.constantCoeff (u' k) ≠ 0 := fun k => by
    have := phPt_unit a w hc' k
    rw [PowerSeries.isUnit_iff_constantCoeff] at this
    exact this.ne_zero
  set ν' : Fin m → ℂˣ := fun k => Units.mk0 _ (hu' k)
  have htr := transl_phPt_eq a (-a) w c c'
  rw [add_neg_cancel] at htr
  set u : Fin m → PowerSeries ℂ := fun k => aeval (phPt Ls a w c')
    (translVar Ls (-a) c (.e k (bi (chartV ((0 : GPtV d₀ d₁ Ls).2.2 k))))) with hudef
  have hconst : (fun v => PowerSeries.constantCoeff (phPt Ls a w c' v)) = coords a ν' := by
    rw [phPt_eq a w c', const_sclV_ZG]
    have := scaleV_coords ν' a 1
    simp only [Pi.one_apply, mul_one] at this
    exact this
  have hu : ∀ k, PowerSeries.constantCoeff (u k) ≠ 0 := by
    intro k
    obtain ⟨μ, hμ⟩ := eval_transl_good hcg
    have e1 : PowerSeries.constantCoeff (u k) = eval (coords a ν')
        (τ Ls (-a) c (X (.e k (bi (chartV ((0 : GPtV d₀ d₁ Ls).2.2 k)))))) := by
      rw [hudef, LSG.ME.constantCoeff_aeval (K := ℂ), hconst, τ, aeval_X]; rfl
    rw [e1, hμ, add_neg_cancel]
    simp only [coords, coordsZ_e, eval_X, repV_chart, mul_one]
    exact (ν' k ^ 3 * μ k).ne_zero
  set U₀ : Fin m → ℂ := fun k => PowerSeries.constantCoeff (u k)
  -- the kernel condition at the identity, rescaled
  have hmain : ∀ Q ∈ vanish (H0 Ls hH),
      eval (coords (0 : GPtV d₀ d₁ Ls) 1) (Dv Ls (chartsV (0 : GPtV d₀ d₁ Ls)) w (scl U₀ Q)) = 0 := by
    intro Q hQ
    have e : aeval (phPt Ls a w c') (τ Ls (-a) c Q) = aeval (sclV u (ZG Ls 0 w)) Q := by
      rw [τ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, htr]
    rw [phPt_eq a w c'] at e
    have hτ := transl_mem_vanish_gtransl a c hQ
    have h1 := coeff_one_sclV_ZG hτ (show a ∈ gtransl a (H0 Ls hH) from
      ⟨0, (H0_isSubgroup hH).zero_mem, zero_add a⟩) w u' hu'
    have h2 := coeff_one_sclV_ZG hQ (H0_isSubgroup hH).zero_mem w u hu
    rw [e, h2] at h1
    rw [h1]
    exact hw _ (scl_mem_vanish ν' hτ)
  -- conclude with `TZ = lieAlg`
  have hTZ : toTan w ∈ TZ Ls (H0 Ls hH) := by
    intro Q hQ
    have hU0 : ∀ k, U₀ k ≠ 0 := hu
    have hQ' : scl (fun k => (U₀ k)⁻¹) Q ∈ vanish (H0 Ls hH) :=
      scl_mem_vanish (fun k => (Units.mk0 _ (hU0 k))⁻¹) hQ
    have := hmain _ hQ'
    rw [scl_scl_inv hU0, eval_Dv_zero] at this
    exact this
  rw [TZ_eq_lieAlg (H0_isSubgroup hH) (isZClosed_H0 hH), lieAlg_H0 hH hc] at hTZ
  exact hTZ

/-- `lieAlg H` lies in the left kernel of `π_0` on `I(H⁰)`. -/
theorem eval_Dv_zero_of_mem {w : LieV ℂ d₀ d₁ m} (hw : w ∈ lieAlgL Ls hH)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ vanish (H0 Ls hH)) :
    eval (coords (0 : GPtV d₀ d₁ Ls) 1) (Dv Ls (chartsV (0 : GPtV d₀ d₁ Ls)) w Q) = 0 := by
  rw [eval_Dv_zero]
  have : toTan w ∈ TZ Ls (H0 Ls hH) :=
    lieAlg_subset_TZ (H0_isSubgroup hH) (by rw [lieAlg_H0 hH hc]; exact hw)
  exact this Q hQ

end Kernel

/-! ### The pairing as a bilinear map -/

variable (Ls) in
/-- The pairing `(w, P) ↦ (Dv_{ch} w P)(y)` on `Lie G̃ × J`. -/
def pairV (ch : Fin m → Fin 2) (y : Var d₀ d₁ m → ℂ) (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    LieV ℂ d₀ d₁ m →ₗ[ℂ] ↥(J.restrictScalars ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun w P => eval y (Dv Ls ch w P))
    (fun w w' P => by rw [Dv_add, Derivation.add_apply, map_add])
    (fun a w P => by rw [Dv_smul, Derivation.smul_apply, smul_eval, smul_eq_mul])
    (fun w P P' => by rw [Submodule.coe_add, map_add, map_add])
    (fun a w P => by rw [Submodule.coe_smul, Derivation.map_smul, smul_eval, smul_eq_mul])

theorem pairV_apply (ch : Fin m → Fin 2) (y : Var d₀ d₁ m → ℂ)
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (w : LieV ℂ d₀ d₁ m) (P : ↥(J.restrictScalars ℂ)) :
    pairV Ls ch y J w P = eval y (Dv Ls ch w P) := rfl

end

end LSG.MEV
