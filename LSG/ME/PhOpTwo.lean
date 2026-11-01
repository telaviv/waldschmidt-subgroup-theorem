import Mathlib
import LSG.ME.PhOpBridge

/-!
# Two-parameter families and translations of the formal order (STAGE2 §10)

The inputs for Roy's vanishing claim with Philippon's operators (`LSG.ME.Chain2`):

* `aeval_phOp`: `phOp` evaluated at a point with coordinates in any `K`-algebra.
* `ordGt_transl`: translation invariance of the formal order, for every law choice:
  `Q` of formal order `> n` at `y + v` ⇒ `τ v c Q` of formal order `> n` at `y` (homogeneous `Q`).
* **`ordGt_phOp`** (the two-parameter lemma, Philippon's `δ^k_g ∘ δ^{k'}_{g'}`): if all
  `Dh`-words of length `≤ N` in `W` kill `P` at `q = y + σ` (normalized representative), then for
  `κ + T ≤ N` and `w' ∈ W` the polynomial `phOp σ w' κ P` has formal order `> T` along `W` at
  `y` — and so does every translate `τ v c (phOp σ w' κ P)` at `y − v`
  (`ordGt_transl_phOp`). Proof: the double series `P(y + exp(z w) + σ + exp(z' w'))` is, by the
  curve lemma over the base ring `K⟦z⟧`, a rescaling of `P` along the flow of `D_{w'}` started on
  the flow of `D_w` through `q`; its coefficient of `z^i z'^κ` is `(Dh_w^i Dh_{w'}^κ P)(q)/(i! κ!)`
  (Taylor twice).
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (DL DL_cons)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Generalities -/

theorem DL_append {R ι : Type*} [CommRing R] [Algebra K R] (Dv : ι → Derivation K R R)
    (l₁ l₂ : List ι) (x : R) : DL Dv (l₁ ++ l₂) x = DL Dv l₂ (DL Dv l₁ x) := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons i l ih => rw [List.cons_append, DL_cons, DL_cons, ih]

theorem scl_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') (u : Fin m → S)
    (A : Var d₀ d₁ m → S) :
    (fun v => f (scl u A v)) = scl (fun k => f (u k)) (fun v => f (A v)) := by
  funext v; cases v <;> simp [map_mul]

theorem derivative_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (F : PowerSeries R) :
    PowerSeries.derivative (R := R') (PowerSeries.map f F) =
      PowerSeries.map f (PowerSeries.derivative (R := R) F) := by
  ext n; simp [PowerSeries.coeff_derivative, map_mul]

section Map

variable {R : Type*} [CommRing R] [Algebra K R]

theorem map_algebraMap_alg (a : K) :
    PowerSeries.map (algebraMap K R) (algebraMap K (PowerSeries K) a) =
      algebraMap K (PowerSeries R) a := by
  simp [PowerSeries.algebraMap_apply]

/-- Base change of flows. -/
theorem IsGFlow.map {a : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Y : Var d₀ d₁ m → PowerSeries K}
    (hY : IsGFlow g₂ g₃ a w Y) :
    IsGFlow g₂ g₃ a w (fun v => PowerSeries.map (algebraMap K R) (Y v)) where
  flow v := by
    rw [derivative_map, hY.flow v, ringHom_aeval _ map_algebraMap_alg]
  chart := hY.chart
  norm k := by rw [hY.norm k, map_one]
  cubic k := by
    have := Fv_map (PowerSeries.map (algebraMap K R)) (algebraMap K (PowerSeries K) (g₂ k))
      (algebraMap K (PowerSeries K) (g₃ k)) (fun i => Y (.e k i))
    rw [hY.cubic k, map_zero, map_algebraMap_alg, map_algebraMap_alg] at this
    exact this.symm

end Map

/-! ### Evaluations of `phOp` -/

section Eval

/-- `phOp` evaluated at a point with coordinates in a `K`-algebra `R`. -/
theorem aeval_phOp {R : Type*} [CommRing R] [Algebra K R] (x₀ : Var d₀ d₁ m → R)
    (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) K) :
    aeval x₀ (phOp g₂ g₃ g w c c' κ Q) = PowerSeries.coeff κ
      (aeval (addPt g₂ g₃ c (fun v => PowerSeries.C (x₀ v))
        (fun v => PowerSeries.map (algebraMap K R) (phPt g₂ g₃ g w c' v))) Q) := by
  set φ : MvPolynomial (Var d₀ d₁ m) K →+* R := (aeval x₀).toRingHom
  have hφ : ∀ p, φ p = aeval x₀ p := fun _ => rfl
  rw [phOp, ← hφ, ← PowerSeries.coeff_map, ringHom_aeval (PowerSeries.map φ)
    (fun a => by simp [PowerSeries.algebraMap_apply, hφ])]
  have hid : φ.comp (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) = algebraMap K R := by
    ext a; simp [hφ]
  have e : (fun v => PowerSeries.map φ (phSub g₂ g₃ g w c c' v)) =
      addPt g₂ g₃ c (fun v => PowerSeries.C (x₀ v))
        (fun v => PowerSeries.map (algebraMap K R) (phPt g₂ g₃ g w c' v)) := by
    funext v
    rw [phSub, addPt_map _ (fun a => by simp [PowerSeries.algebraMap_apply, hφ])]
    have hmm : ∀ F : PowerSeries K, PowerSeries.map φ (PowerSeries.map C F) =
        PowerSeries.map (algebraMap K R) F :=
      fun F => by rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hid]
    simp only [PowerSeries.map_C, hφ, aeval_X, hmm]
  rw [e]

/-- Evaluating a translate at a formal point: the translated point. -/
theorem aeval_transl {S : Type*} [CommRing S] [Algebra K S] (x₀ : Var d₀ d₁ m → S)
    (v : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    aeval x₀ (τ g₂ g₃ v c Q) =
      aeval (addPt g₂ g₃ c x₀ (fun u => algebraMap K S (coords v 1 u))) Q := by
  rw [τ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have e : (fun i => aeval x₀ (translVar g₂ g₃ v c i)) =
      addPt g₂ g₃ c x₀ (fun u => algebraMap K S (coords v 1 u)) := by
    funext u
    cases u with
    | x i => simp [translVar, addPt, coords]
    | y j => simp [translVar, addPt, coords, mul_comm]
    | z j => simp [translVar, addPt, coords, mul_comm]
    | e k i =>
      simp only [translVar, addPt, lawPoly, coords, coordsZ_e]
      rw [← AlgHom.coe_toRingHom, lawc_map]
      simp [bvars, Function.comp_def]
  rw [e]

end Eval

/-! ### Translation invariance of the formal order -/

section Transl

variable [CharZero K] [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- `y + exp(z w)` translated by `v` (any law choice) is a rescaling of `(y + v) + exp(z w)`. -/
theorem addPt_fexp_alg (y v : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c : Fin m → Fin 2) :
    ∃ U : Fin m → PowerSeries K, addPt g₂ g₃ c (fexp g₂ g₃ y w)
      (fun u => algebraMap K (PowerSeries K) (coords v 1 u)) = scl U (fexp g₂ g₃ (y + v) w) := by
  have := addPt_fexp hΔ y v w c
  simp only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact ⟨_, this⟩

/-- **Translation invariance of the formal order**, any law choice (homogeneous `Q`). -/
theorem ordGt_transl (W : Submodule K (LieE K d₀ d₁ m)) {Q : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hQ : IsHomE Q d) {n : ℕ} {y v : GPt K d₀ d₁ g₂ g₃}
    (h : OrdGt g₂ g₃ W Q n (y + v)) (c : Fin m → Fin 2) : OrdGt g₂ g₃ W (τ g₂ g₃ v c Q) n y := by
  intro w hw
  obtain ⟨U, hU⟩ := addPt_fexp_alg hΔ y v w c
  rw [aeval_transl, hU, aeval_scl hQ]
  exact (h w hw).mul_left _

end Transl

/-! ### The two-parameter lemma -/

section Two

variable [CharZero K]

/-- Vanishing of the coefficients `[z^i z'^κ]` with `i + κ ≤ N`. -/
def Tri (N : ℕ) (H : PowerSeries (PowerSeries K)) : Prop :=
  ∀ κ i, κ + i ≤ N → PowerSeries.coeff i (PowerSeries.coeff κ H) = 0

omit [CharZero K] in
theorem Tri.mul_left {N : ℕ} {H : PowerSeries (PowerSeries K)} (hH : Tri N H)
    (G : PowerSeries (PowerSeries K)) : Tri N (G * H) := by
  intro κ i hi
  rw [PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  rw [hH p.2 q.2 (by omega), mul_zero]

variable [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- **The two-parameter lemma.** -/
theorem lowZero_phOp {W : Submodule K (LieE K d₀ d₁ m)} {P : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hP : IsHomE P d) {y σ : GPt K d₀ d₁ g₂ g₃} {N : ℕ}
    (hvan : P ∈ VOg (Dh g₂ g₃ (chartAt (y + σ))) (W : Set (LieE K d₀ d₁ m))
      (RingHom.ker (eval (coords (y + σ) 1))) N)
    {w w' : LieE K d₀ d₁ m} (hw : w ∈ W) (hw' : w' ∈ W) (c₁ c₂ : Fin m → Fin 2) {κ T : ℕ}
    (hκ : κ + T ≤ N) (U : Fin m → PowerSeries K) :
    LowZero T (PowerSeries.coeff κ (aeval (addPt g₂ g₃ c₁
      (fun v => PowerSeries.C (scl U (fexp g₂ g₃ y w) v))
      (fun v => PowerSeries.map (algebraMap K (PowerSeries K)) (phPt g₂ g₃ σ w' c₂ v))) P)) := by
  set q := y + σ
  set Y := fexp g₂ g₃ y w
  set F' : Var d₀ d₁ m → PowerSeries (PowerSeries K) :=
    fun v => PowerSeries.map (algebraMap K (PowerSeries K)) (fexp g₂ g₃ σ w' v)
  -- the flow of `D_{w'}` started on the flow of `D_w` through `q`
  set Z : Var d₀ d₁ m → PowerSeries (PowerSeries K) := fflow g₂ g₃ (chartAt q) w' (fexp g₂ g₃ q w)
  have hZ : IsNFlow g₂ g₃ (chartAt q) w' Z :=
    fflow_isNFlow (chartAt_ne q) w' (fexp_isNFlow q w).norm
  -- the curve lemma over `R = K⟦z⟧`
  obtain ⟨c₀, hc₀⟩ := exists_good two_ne_zero hΔ y σ
  obtain ⟨μ, hμ, hμ0⟩ := addPt_coords hΔ y σ c₀
  have hU0 := addPt_fexp hΔ y σ w c₀
  have hcurve := curve_eq (R := PowerSeries K)
    (IsGFlow.map (R := PowerSeries K) (fexp_isGFlow σ w')) hZ (B := Y)
    (fexp_isGFlow y w).cubic c₀
    (fun k => lsgn (c₀ k) * addPt g₂ g₃ c₀ Y (fun v => PowerSeries.C (coords σ 1 v))
      (.e k (chartAt q k))) (fun k => ?_) ?_ c₁
  rotate_left
  · refine IsUnit.mul ?_ ?_
    · unfold lsgn; split_ifs
      · exact isUnit_one.neg
      · exact isUnit_one
    · rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_addPt]
      simp only [Y, fexp_const, PowerSeries.constantCoeff_C]
      rw [hμ, scl_e, coords_chartAt, mul_one]
      exact (hμ0 hc₀ k).isUnit
  · have hcm : ∀ F : PowerSeries K,
        PowerSeries.constantCoeff (PowerSeries.map (algebraMap K (PowerSeries K)) F) =
        PowerSeries.C (PowerSeries.constantCoeff F) := fun F => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.algebraMap_apply]
      rfl
    have hA :
        (fun v => PowerSeries.constantCoeff (addPt g₂ g₃ c₀ F' (fun v => PowerSeries.C (Y v)) v))
        = addPt g₂ g₃ c₀ (fun v => PowerSeries.C (coords σ 1 v)) Y := by
      funext v
      rw [addPt_map _ (fun a => by simp [PowerSeries.algebraMap_apply])]
      simp only [F', hcm, fexp_const, PowerSeries.constantCoeff_C]
    have hB : (fun v => PowerSeries.constantCoeff (Z v)) = fexp g₂ g₃ q w :=
      funext (fflow_const _ _ _)
    rw [hA, hB, addPt_swap]
    conv_lhs => rw [hU0]
    rw [scl_scl]
    rfl
  -- assemble the rescalings
  obtain ⟨V, hV⟩ : ∃ V, phPt g₂ g₃ σ w' c₂ = scl V (fexp g₂ g₃ σ w') := ⟨_, addPt_Exp hΔ σ w' c₂⟩
  obtain ⟨M, hpt⟩ : ∃ M, addPt g₂ g₃ c₁ (fun v => PowerSeries.C (scl U Y v))
      (fun v => PowerSeries.map (algebraMap K (PowerSeries K)) (phPt g₂ g₃ σ w' c₂ v)) = scl M Z :=
    ⟨_, by
      rw [hV, scl_map (PowerSeries.C : PowerSeries K →+* PowerSeries (PowerSeries K)),
        scl_map (PowerSeries.map (algebraMap K (PowerSeries K))), addPt_scl_left, addPt_scl_right,
        addPt_swap]
      conv_lhs => rw [hcurve]
      simp only [scl_scl]
      rfl⟩
  rw [hpt, aeval_scl hP]
  -- the double Taylor expansion
  have htri : Tri N (aeval Z P) := by
    intro κ' i hi
    have h1 := taylor hZ κ' P
    simp only [Z, fflow_const] at h1
    have h2 := congrArg (PowerSeries.coeff i) h1
    rw [← map_natCast (PowerSeries.C : K →+* PowerSeries K), PowerSeries.coeff_C_mul] at h2
    have h3 := taylor_fexp q w i (DL (Dh g₂ g₃ (chartAt q)) (List.replicate κ' w') P)
    rw [← DL_append, ← h2] at h3
    have h4 : eval (coords q 1) (DL (Dh g₂ g₃ (chartAt q)) (List.replicate κ' w' ++
        List.replicate i w) P) = 0 :=
      hvan _ (fun u hu => by
        rcases List.mem_append.mp hu with hu | hu
        · exact (List.eq_of_mem_replicate hu) ▸ hw'
        · exact (List.eq_of_mem_replicate hu) ▸ hw) (by simpa using hi)
    rw [h4] at h3
    have hf : ∀ n : ℕ, (n.factorial : K) ≠ 0 :=
      fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (hf i))).resolve_left (hf κ')
  intro i hi
  exact htri.mul_left _ κ i (by omega)

/-- **Translates of Philippon operators**: under the hypotheses of `lowZero_phOp`, the polynomial
`τ v c (phOp σ w' κ P)` has formal order `> T` along `W` at `y` whenever `P` is killed at
`(y + v) + σ` by all words of length `≤ N` and `κ + T ≤ N`. -/
theorem ordGt_transl_phOp {W : Submodule K (LieE K d₀ d₁ m)} {P : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hP : IsHomE P d) {y v σ : GPt K d₀ d₁ g₂ g₃} {N : ℕ}
    (hvan : P ∈ VOg (Dh g₂ g₃ (chartAt (y + v + σ))) (W : Set (LieE K d₀ d₁ m))
      (RingHom.ker (eval (coords (y + v + σ) 1))) N)
    {w' : LieE K d₀ d₁ m} (hw' : w' ∈ W) (c c₁ c₂ : Fin m → Fin 2) {κ T : ℕ} (hκ : κ + T ≤ N) :
    OrdGt g₂ g₃ W (τ g₂ g₃ v c (phOp g₂ g₃ σ w' c₁ c₂ κ P)) T y := by
  intro w hw
  obtain ⟨U, hU⟩ := addPt_fexp_alg hΔ y v w c
  rw [aeval_transl, hU, aeval_phOp]
  exact lowZero_phOp hΔ hP hvan hw hw' c₁ c₂ hκ U

end Two

end LSG.ME
