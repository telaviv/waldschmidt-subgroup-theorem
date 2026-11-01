import Mathlib
import LSG.ME.FormalExp
import LSG.ME.OrderTransl

/-!
# Translating formal points by addition laws (STAGE2 §10)

* `addPt c A B`: the point `A + B` computed with the addition laws `c` (blockwise; `A`, `B` are
  points with coordinates in a commutative `K`-algebra `S`); `scl u A` rescales the elliptic blocks.
  Swapping (`addPt_swap`), rescaling (`addPt_scl_left/right`), base change (`addPt_map`) and
  homogeneous evaluation (`aeval_scl`).
* **`curve_eq`** (the curve lemma): if `Y` is a normalized flow of `D_w` on `G` and `B` is a point
  of the cubics, then for **every** law choice `c`, `addPt c Y B = scl u Z` where `Z` is the
  normalized flow (other charts) through the point represented by `addPt c₀ Y(0) B` for one
  choice `c₀` with nonvanishing chart coordinates, and `u k` is the chart coordinate of
  `addPt c Y B` (a unit iff its constant term is). Proof: the translation identity
  (`LSG.ME.tr_eq`) with `D = d/dz` shows that `addPt c₀ Y B`, renormalized, is a flow; uniqueness
  of flows; the two laws are proportional on `E × E` (`law₁_cross_law₂`).
-/

universe u

open MvPolynomial LSG.Elliptic

namespace LSG.ME

/-! ### Laws on formal points -/

section Pt

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K} {S : Type*} [CommRing S]
  [Algebra K S]

variable (g₂ g₃) in
/-- The point `A + B`, computed with the addition laws `c`. -/
def addPt (c : Fin m → Fin 2) (A B : Var d₀ d₁ m → S) : Var d₀ d₁ m → S
  | .x i => A (.x i) + B (.x i)
  | .y j => A (.y j) * B (.y j)
  | .z j => A (.z j) * B (.z j)
  | .e k i => lawc (c k) (algebraMap K S (g₂ k)) (algebraMap K S (g₃ k)) (fun i => A (.e k i))
      (fun i => B (.e k i)) i

/-- Rescaling the elliptic blocks. -/
def scl (u : Fin m → S) (A : Var d₀ d₁ m → S) : Var d₀ d₁ m → S := fun v => A v * sc u v

@[simp] theorem scl_x (u : Fin m → S) (A : Var d₀ d₁ m → S) (i : Fin d₀) :
    scl u A (.x i) = A (.x i) := by simp [scl, sc]
@[simp] theorem scl_y (u : Fin m → S) (A : Var d₀ d₁ m → S) (j : Fin d₁) :
    scl u A (.y j) = A (.y j) := by simp [scl, sc]
@[simp] theorem scl_z (u : Fin m → S) (A : Var d₀ d₁ m → S) (j : Fin d₁) :
    scl u A (.z j) = A (.z j) := by simp [scl, sc]
@[simp] theorem scl_e (u : Fin m → S) (A : Var d₀ d₁ m → S) (k : Fin m) (i : Fin 3) :
    scl u A (.e k i) = u k * A (.e k i) := by simp [scl, sc, mul_comm]

theorem scl_blk (u : Fin m → S) (A : Var d₀ d₁ m → S) (k : Fin m) :
    (fun i => scl u A (.e k i)) = u k • fun i => A (.e k i) := by
  funext i; simp

theorem scl_scl (u u' : Fin m → S) (A : Var d₀ d₁ m → S) :
    scl u (scl u' A) = scl (u * u') A := by
  funext v; cases v <;> simp [mul_assoc]

theorem scl_one (A : Var d₀ d₁ m → S) : scl 1 A = A := by
  funext v; cases v <;> simp

omit [Algebra K S] in
/-- Evaluation of a homogeneous polynomial at a rescaled point. -/
theorem aeval_scl [Algebra K S] {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hQ : IsHomE Q d) (u : Fin m → S) (A : Var d₀ d₁ m → S) :
    aeval (scl u A) Q = (∏ k, u k ^ d k) * aeval A Q :=
  aeval_sc (K := K) hQ A u

theorem addPt_scl_left (c : Fin m → Fin 2) (u : Fin m → S) (A B : Var d₀ d₁ m → S) :
    addPt g₂ g₃ c (scl u A) B = scl (u ^ 2) (addPt g₂ g₃ c A B) := by
  funext v
  cases v with
  | e k i =>
    rw [scl_e]
    change lawc (c k) _ _ (fun i => scl u A (.e k i)) (fun i => B (.e k i)) i = _
    rw [scl_blk, lawc_one_smul]
    simp [addPt]
  | _ => simp [addPt]

theorem addPt_scl_right (c : Fin m → Fin 2) (u : Fin m → S) (A B : Var d₀ d₁ m → S) :
    addPt g₂ g₃ c A (scl u B) = scl (u ^ 2) (addPt g₂ g₃ c A B) := by
  funext v
  cases v with
  | e k i =>
    have := lawc_smul (c k) (algebraMap K S (g₂ k)) (algebraMap K S (g₃ k))
      (fun i => A (.e k i)) (fun i => B (.e k i)) 1 (u k)
    simp only [one_smul, one_mul] at this
    rw [scl_e]
    change lawc (c k) _ _ (fun i => A (.e k i)) (fun i => scl u B (.e k i)) i = _
    rw [scl_blk, this]
    simp [addPt]
  | _ => simp [addPt]

/-- The sign relating `lawc c P Q` and `lawc c Q P`. -/
def lsgn (c : Fin 2) : S := if c = 0 then -1 else 1

theorem lawc_swap (c : Fin 2) (g₂ g₃ : S) (P Q : Fin 3 → S) :
    lawc c g₂ g₃ P Q = (lsgn c : S) • lawc c g₂ g₃ Q P := by
  unfold lawc lsgn
  split_ifs
  · rw [law₁_swap g₂ g₃ P Q, neg_one_smul, neg_neg]
  · rw [law₂_swap, one_smul]

theorem addPt_swap (c : Fin m → Fin 2) (A B : Var d₀ d₁ m → S) :
    addPt g₂ g₃ c A B = scl (fun k => lsgn (c k)) (addPt g₂ g₃ c B A) := by
  funext v
  cases v with
  | x i => simp [addPt, add_comm]
  | y j => simp [addPt, mul_comm]
  | z j => simp [addPt, mul_comm]
  | e k i => simp only [addPt, scl_e, lawc_swap (c k) _ _ (fun i => A (.e k i)), Pi.smul_apply,
      smul_eq_mul]

theorem addPt_map {S' : Type*} [CommRing S'] [Algebra K S'] (f : S →+* S')
    (hf : ∀ a : K, f (algebraMap K S a) = algebraMap K S' a) (c : Fin m → Fin 2)
    (A B : Var d₀ d₁ m → S) (v : Var d₀ d₁ m) :
    f (addPt g₂ g₃ c A B v) = addPt g₂ g₃ c (fun v => f (A v)) (fun v => f (B v)) v := by
  cases v with
  | e k i => simp only [addPt, lawc_map, hf]; rfl
  | _ => simp [addPt]

theorem lawc_cross {P Q : Fin 3 → S} {a b : S} (hP : Fv a b P = 0) (hQ : Fv a b Q = 0)
    (c c' : Fin 2) (i j : Fin 3) :
    lawc c a b P Q i * lawc c' a b P Q j = lawc c a b P Q j * lawc c' a b P Q i := by
  fin_cases c <;> fin_cases c' <;> simp only [Fin.zero_eta, Fin.mk_one, lawc_zero, lawc_one]
  · ring
  · exact law₁_cross_law₂ hP hQ i j
  · linear_combination -(law₁_cross_law₂ hP hQ i j)
  · ring

/-- A law is a quadratic form in its second argument. -/
theorem lawc_quad {S : Type*} [CommRing S] (c : Fin 2) (a b : S) (P Q : Fin 3 → S) (i : Fin 3) :
    lawc c a b P Q i = Q 0 ^ 2 * lawc c a b P ![1, 0, 0] i + Q 1 ^ 2 * lawc c a b P ![0, 1, 0] i +
      Q 2 ^ 2 * lawc c a b P ![0, 0, 1] i +
      Q 0 * Q 1 * (lawc c a b P ![1, 1, 0] i - lawc c a b P ![1, 0, 0] i -
        lawc c a b P ![0, 1, 0] i) +
      Q 0 * Q 2 * (lawc c a b P ![1, 0, 1] i - lawc c a b P ![1, 0, 0] i -
        lawc c a b P ![0, 0, 1] i) +
      Q 1 * Q 2 * (lawc c a b P ![0, 1, 1] i - lawc c a b P ![0, 1, 0] i -
        lawc c a b P ![0, 0, 1] i) := by
  fin_cases c <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, lawc_zero, lawc_one, law₁, law₂, law₁U, law₁V, law₁W,
      law₂U, law₂V, law₂W, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    ring

end Pt

/-! ### The curve lemma -/

section Curve

variable {K : Type u} [Field K] [CharZero K] {R : Type*} [CommRing R] [Algebra K R]
  {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

local notation "dz" => (PowerSeries.derivative (R := R))

theorem c2_smul {S : Type*} [CommRing S] (a : Fin 3) (g₂ g₃ u : S) (P : Fin 3 → S) (i : Fin 3) :
    c2 a g₂ g₃ (u • P) i = u ^ 2 * c2 a g₂ g₃ P i := by
  fin_cases a <;> fin_cases i <;> simp [c2] <;> ring

theorem c2_self {S : Type*} [CommRing S] {a : Fin 3} (ha : a ≠ 0) (g₂ g₃ : S) (P : Fin 3 → S) :
    c2 a g₂ g₃ P a = 0 := by
  fin_cases a
  · exact absurd rfl ha
  · simp [c2]
  · simp [c2]

theorem aeval_chartPoly {S : Type*} [CommRing S] [Algebra K S] (Γ : Var d₀ d₁ m → S) (a : Fin 3)
    (k : Fin m) (i : Fin 3) :
    aeval Γ (chartPoly g₂ g₃ d₀ d₁ a k i) = algebraMap K S (1 / 2) *
      c2 a (algebraMap K S (g₂ k)) (algebraMap K S (g₃ k)) (fun i => Γ (.e k i)) i := by
  rw [chartPoly_eq_half (two_ne_zero' K), map_mul, aeval_C]
  congr 1
  rw [← AlgHom.coe_toRingHom, c2_map]
  simp only [AlgHom.coe_toRingHom, aeval_C]
  congr 1
  funext j; simp [bvars]

/-- The elliptic part of a flow, in `c2` form. -/
theorem flow_e {b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Y : Var d₀ d₁ m → PowerSeries R}
    (hY : IsFlow g₂ g₃ b w Y) (k : Fin m) (j : Fin 3) :
    dz (Y (.e k j)) = (algebraMap K _ (w.2.2 k) * algebraMap K _ (1 / 2)) *
      c2 (b k) (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k)) (fun i => Y (.e k i)) j := by
  rw [hY, dval, map_mul, aeval_C, aeval_chartPoly, mul_assoc]

/-- The renormalized translate of a flow solves the chart ODE (core computation). -/
theorem renorm_deriv {X : Fin 3 → PowerSeries R} {s t U' : PowerSeries R} {b : Fin 3} (hb : b ≠ 0)
    {g₂' g₃' : PowerSeries R}
    (hX : ∀ i, X b * dz (X i) = s * c2 b g₂' g₃' X i + s * (t * X i))
    (hU : U' * X b = 1) (i : Fin 3) :
    dz (U' * X i) = s * c2 b g₂' g₃' (U' • X) i := by
  have hb' := hX b
  rw [c2_self hb, mul_zero, zero_add] at hb'
  have h1 : dz (X b) = s * t := by
    linear_combination U' * hb' - (dz (X b) - s * t) * hU
  have hd : X b * dz U' + U' * dz (X b) = 0 := by
    have := congrArg dz hU
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have h2 : dz U' = -U' ^ 2 * (s * t) := by
    linear_combination U' * hd - dz U' * hU - U' ^ 2 * h1
  have h3 : dz (X i) = U' * (s * c2 b g₂' g₃' X i + s * (t * X i)) := by
    linear_combination U' * hX i - dz (X i) * hU
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h2, h3, c2_smul]
  ring

variable (g₂ g₃) in
/-- The hypotheses on the moving point `Y`: a normalized flow on the cubics. -/
structure IsGFlow (a : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (Y : Var d₀ d₁ m → PowerSeries R) :
    Prop extends IsNFlow g₂ g₃ a w Y where
  cubic : ∀ k, Fv (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k)) (fun i => Y (.e k i)) = 0

/-- **The curve lemma.** -/
theorem curve_eq {a b : Fin m → Fin 3} {w : LieE K d₀ d₁ m} {Y Z : Var d₀ d₁ m → PowerSeries R}
    (hY : IsGFlow g₂ g₃ a w Y) (hZ : IsNFlow g₂ g₃ b w Z) {B : Var d₀ d₁ m → R}
    (hB : ∀ k, Fv (algebraMap K R (g₂ k)) (algebraMap K R (g₃ k)) (fun i => B (.e k i)) = 0)
    (c₀ : Fin m → Fin 2) (u₀ : Fin m → R) (hu₀ : ∀ k, IsUnit (u₀ k))
    (h0 : (fun v => PowerSeries.constantCoeff (addPt g₂ g₃ c₀ Y (fun v => PowerSeries.C (B v)) v)) =
      scl u₀ fun v => PowerSeries.constantCoeff (Z v))
    (c : Fin m → Fin 2) :
    addPt g₂ g₃ c Y (fun v => PowerSeries.C (B v)) =
      scl (fun k => addPt g₂ g₃ c Y (fun v => PowerSeries.C (B v)) (.e k (b k))) Z := by
  set CB : Var d₀ d₁ m → PowerSeries R := fun v => PowerSeries.C (B v) with hCB
  set X := addPt g₂ g₃ c₀ Y CB with hX
  set U : Fin m → PowerSeries R := fun k => X (.e k (b k)) with hUdef
  have halg : ∀ x : K, algebraMap K (PowerSeries R) x = PowerSeries.C (algebraMap K R x) :=
    fun x => PowerSeries.algebraMap_apply
  -- the chart coordinates of `X` are units
  have hU : ∀ k, IsUnit (U k) := fun k => by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have := congrFun h0 (.e k (b k))
    simp only [scl_e] at this
    rw [show U k = X (.e k (b k)) from rfl, this, hZ.norm k, map_one, mul_one]
    exact hu₀ k
  set Ui : Fin m → PowerSeries R := fun k => Ring.inverse (U k) with hUi
  have hUiU : ∀ k, Ui k * U k = 1 := fun k => Ring.inverse_mul_cancel _ (hU k)
  have hCBF : ∀ k, Fv (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k)) (fun i => CB (.e k i)) = 0 :=
    fun k => by
      have := Fv_map (PowerSeries.C : R →+* PowerSeries R) (algebraMap K R (g₂ k))
        (algebraMap K R (g₃ k)) (fun i => B (.e k i))
      rw [hB k, map_zero] at this
      simpa only [halg, CB, Function.comp_def] using this.symm
  -- the translation identity, block by block
  have hstar : ∀ k i, U k * dz (X (.e k i)) =
      (algebraMap K _ (w.2.2 k) * algebraMap K _ (1 / 2)) *
        c2 (b k) (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k)) (fun i => X (.e k i)) i +
      (algebraMap K _ (w.2.2 k) * algebraMap K _ (1 / 2)) *
        (trE (c₀ k) (a k) (b k) (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k))
          (fun i => Y (.e k i)) (fun i => CB (.e k i)) * X (.e k i)) := by
    intro k i
    obtain ⟨f₁, f₂, hf⟩ := tr_eq (PowerSeries.derivative (R := R)) (c₀ k) (hY.chart k)
      (hZ.chart k) (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k))
      (algebraMap K _ (w.2.2 k) * algebraMap K _ (1 / 2)) (fun i => Y (.e k i))
      (fun i => CB (.e k i)) (by simp [halg]) (by simp [halg])
      (fun j => PowerSeries.derivative_C) (fun j => flow_e hY.flow k j) i
    rw [hY.cubic k, hCBF k, show Y (.e k (a k)) = 1 from hY.norm k] at hf
    rw [show U k = X (.e k (b k)) from rfl, hX]
    simp only [addPt]
    linear_combination hf
  set Xt := scl Ui X with hXt
  have hflow : IsFlow g₂ g₃ b w Xt := by
    intro v
    cases v with
    | x i => simp [Xt, X, addPt, hY.flow (.x i), dval, CB]
    | y j =>
      simp only [Xt, X, scl_y, addPt, Derivation.leibniz, CB, PowerSeries.derivative_C,
        smul_eq_mul, hY.flow (.y j), dval, map_mul, aeval_C, aeval_X]
      ring
    | z j =>
      simp only [Xt, X, scl_z, addPt, Derivation.leibniz, CB, PowerSeries.derivative_C,
        smul_eq_mul, hY.flow (.z j), dval, map_mul, map_neg, aeval_C,
        aeval_X]
      ring
    | e k i =>
      have := renorm_deriv (X := fun i => X (.e k i)) (hZ.chart k) (hstar k) (hUiU k) i
      rw [show Xt (.e k i) = Ui k * X (.e k i) from scl_e _ _ _ _, this, dval, map_mul, aeval_C,
        aeval_chartPoly, scl_blk Ui X k, mul_assoc]
  have hnorm : ∀ k, Xt (.e k (b k)) = 1 := fun k => by
    rw [show Xt (.e k (b k)) = Ui k * U k from scl_e _ _ _ _, hUiU k]
  have hinit : (fun v => PowerSeries.constantCoeff (Xt v)) =
      fun v => PowerSeries.constantCoeff (Z v) := by
    funext v
    have h0v := congrFun h0 v
    cases v with
    | x i => simpa [Xt] using h0v
    | y j => simpa [Xt] using h0v
    | z j => simpa [Xt] using h0v
    | e k i =>
      have hc : PowerSeries.constantCoeff (Ui k) * u₀ k = 1 := by
        have h1 := congrArg PowerSeries.constantCoeff (hUiU k)
        have h2 := congrFun h0 (.e k (b k))
        simp only [scl_e, hZ.norm k, map_one, mul_one] at h2
        rwa [map_mul, map_one, show U k = X (.e k (b k)) from rfl, h2] at h1
      simp only [scl_e] at h0v
      rw [show Xt (.e k i) = Ui k * X (.e k i) from scl_e _ _ _ _, map_mul, h0v, ← mul_assoc, hc,
        one_mul]
  have hXZ : Xt = Z := by
    rw [eq_fflow hflow, eq_fflow hZ.flow, hinit]
  have hX : X = scl U Z := by
    rw [← hXZ, hXt, scl_scl]
    funext v
    cases v with
    | e k i => simp [mul_comm (U k) (Ui k), hUiU k]
    | _ => simp
  funext v
  cases v with
  | x i =>
    have h := congrFun hX (.x i)
    simp only [scl, sc, mul_one] at h ⊢
    exact h
  | y j =>
    have h := congrFun hX (.y j)
    simp only [scl, sc, mul_one] at h ⊢
    exact h
  | z j =>
    have h := congrFun hX (.z j)
    simp only [scl, sc, mul_one] at h ⊢
    exact h
  | e k i =>
    have hcr := lawc_cross (hY.cubic k) (hCBF k) (c k) (c₀ k) i (b k)
    have hXi : X (.e k i) = U k * Z (.e k i) := by
      simpa using congrFun hX (.e k i)
    change lawc (c k) _ _ _ _ i * X (.e k (b k)) = lawc (c k) _ _ _ _ (b k) * X (.e k i) at hcr
    rw [scl_e]
    change lawc (c k) _ _ _ _ i = lawc (c k) _ _ _ _ (b k) * Z (.e k i)
    rw [hXi] at hcr
    have hUiU' : Ui k * X (.e k (b k)) = 1 := hUiU k
    set L := lawc (c k) (algebraMap K (PowerSeries R) (g₂ k)) (algebraMap K (PowerSeries R) (g₃ k))
      (fun i => Y (.e k i)) (fun i => CB (.e k i)) with hL
    linear_combination Ui k * hcr - (L i - L (b k) * Z (.e k i)) * hUiU'

end Curve

/-! ### Law curves through points of `G` -/

section LawCurves

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

theorem aeval_Fk {S : Type*} [CommRing S] [Algebra K S] (Γ : Var d₀ d₁ m → S) (k : Fin m) :
    aeval Γ (Fk g₂ g₃ d₀ d₁ k) =
      Fv (algebraMap K S (g₂ k)) (algebraMap K S (g₃ k)) (fun i => Γ (.e k i)) := by
  simp [Fk, Fv, F]

/-- A rescaling of a normalized point is determined by the chart coordinates. -/
theorem scl_norm {S : Type*} [CommRing S] {b : Fin m → Fin 3} {A Z : Var d₀ d₁ m → S}
    {u : Fin m → S} (hA : A = scl u Z) (hZ : ∀ k, Z (.e k (b k)) = 1) :
    A = scl (fun k => A (.e k (b k))) Z := by
  have : (fun k => A (.e k (b k))) = u := by funext k; rw [hA, scl_e, hZ k, mul_one]
  rw [this]; exact hA

theorem coords_eq_scl (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) :
    coords g lam = scl (fun k => (lam k : K)) (coords g 1) := by
  funext v; cases v <;> simp [coords]

theorem C_scl {S : Type*} [CommRing S] (u : Fin m → S) (A : Var d₀ d₁ m → S) :
    (fun v => PowerSeries.C (scl u A v)) =
      scl (fun k => PowerSeries.C (u k)) (fun v => PowerSeries.C (A v)) := by
  funext v; simp [scl, map_mul, sc]; cases v <;> simp

variable [CharZero K]

theorem fexp_isGFlow (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) :
    IsGFlow g₂ g₃ (chartAt p) w (fexp g₂ g₃ p w) :=
  { toIsNFlow := fexp_isNFlow p w
    cubic := fun k => by rw [← aeval_Fk]; exact fexp_Fk p w k }

omit [CharZero K] in
theorem constantCoeff_addPt {A B : Var d₀ d₁ m → PowerSeries K} (c : Fin m → Fin 2)
    (v : Var d₀ d₁ m) : PowerSeries.constantCoeff (addPt g₂ g₃ c A B v) =
      addPt g₂ g₃ c (fun v => PowerSeries.constantCoeff (A v))
        (fun v => PowerSeries.constantCoeff (B v)) v :=
  addPt_map _ (fun a => by simp) c A B v

variable [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- The constant terms: `addPt c (coords p 1) (coords q 1) = μ · coords (p + q) 1` blockwise. -/
theorem addPt_coords (p q : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) :
    ∃ μ : Fin m → K, addPt g₂ g₃ c (coords p 1) (coords q 1) = scl μ (coords (p + q) 1) ∧
      (Good p q c → ∀ k, μ k ≠ 0) := by
  choose μ hμ hμ0 using fun k => lawc_rep two_ne_zero (hΔ k) (c k) (p.2.2 k) (q.2.2 k)
  refine ⟨μ, ?_, fun hc k => hμ0 k (hc k)⟩
  funext v
  cases v with
  | x i => simp [addPt, coords]
  | y j => simp [addPt, coords]
  | z j => simp [addPt, coords, mul_comm]
  | e k i =>
    have := congrFun (hμ k) i
    simp only [addPt, scl_e, coords, coordsZ_e, Algebra.algebraMap_self, RingHom.id_apply]
    simpa using this

/-- **(L1)** `(p + exp(z w)) + q` is a rescaling of `(p + q) + exp(z w)`, for every law choice. -/
theorem addPt_fexp (p q : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c : Fin m → Fin 2) :
    addPt g₂ g₃ c (fexp g₂ g₃ p w) (fun v => PowerSeries.C (coords q 1 v)) =
      scl (fun k => addPt g₂ g₃ c (fexp g₂ g₃ p w) (fun v => PowerSeries.C (coords q 1 v))
        (.e k (chartAt (p + q) k))) (fexp g₂ g₃ (p + q) w) := by
  obtain ⟨c₀, hc₀⟩ := exists_good two_ne_zero hΔ p q
  obtain ⟨μ, hμ, hμ0⟩ := addPt_coords hΔ p q c₀
  refine curve_eq (fexp_isGFlow p w) (fexp_isNFlow (p + q) w) (B := coords q 1) (fun k => ?_) c₀ μ
    (fun k => (hμ0 hc₀ k).isUnit) ?_ c
  · have := Fv_rep (two_ne_zero (α := K)) (q.2.2 k)
    simpa [coords] using this
  · funext v
    rw [constantCoeff_addPt]
    simp only [fexp_const, PowerSeries.constantCoeff_C]
    rw [hμ]

omit [DecidableEq K] in
/-- **(L2)** `g + exp(z w)`, computed with any law choice, is a rescaling of `fexp g w`. -/
theorem addPt_Exp (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c : Fin m → Fin 2) :
    addPt g₂ g₃ c (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w) =
      scl (fun k => addPt g₂ g₃ c (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w)
        (.e k (chartAt g k))) (fexp g₂ g₃ g w) := by
  classical
  have h1 := addPt_fexp hΔ 0 g w c
  rw [zero_add] at h1
  obtain ⟨u, hu⟩ : ∃ u, addPt g₂ g₃ c (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w) =
      scl u (fexp g₂ g₃ g w) := ⟨_, by rw [addPt_swap, h1, scl_scl]⟩
  exact scl_norm hu (fexp_isNFlow g w).norm

variable (g₂ g₃) in
/-- The law-built point `h + (g + exp(z w))` (cone representative of `h` scaled by `λ`). -/
noncomputable def lawPt (h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (g : GPt K d₀ d₁ g₂ g₃)
    (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) : Var d₀ d₁ m → PowerSeries K :=
  addPt g₂ g₃ c (fun v => PowerSeries.C (coords h lam v))
    (addPt g₂ g₃ c' (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w))

/-- **(L3) Independence of the law choices**: the law-built point is a rescaling of the
intrinsic point `(h + g) + exp(z w)`. -/
theorem lawPt_eq (h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (g : GPt K d₀ d₁ g₂ g₃)
    (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) :
    lawPt g₂ g₃ h lam g w c c' =
      scl (fun k => lawPt g₂ g₃ h lam g w c c' (.e k (chartAt (h + g) k)))
      (fexp g₂ g₃ (h + g) w) := by
  have h1 := addPt_fexp hΔ g h w c
  rw [add_comm g h] at h1
  obtain ⟨u, hu⟩ : ∃ u, lawPt g₂ g₃ h lam g w c c' = scl u (fexp g₂ g₃ (h + g) w) :=
    ⟨_, by
      rw [lawPt, addPt_Exp hΔ g w c', coords_eq_scl h lam, C_scl, addPt_scl_left,
        addPt_scl_right, addPt_swap c (fun v => PowerSeries.C (coords h 1 v)), h1]
      simp only [scl_scl]; rfl⟩
  exact scl_norm hu (fexp_isNFlow (h + g) w).norm

/-- For good law choices the rescaling factors are units. -/
theorem lawPt_unit (h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (g : GPt K d₀ d₁ g₂ g₃)
    (w : LieE K d₀ d₁ m) {c c' : Fin m → Fin 2} (hc : Good h g c) (hc' : Good g 0 c') (k : Fin m) :
    IsUnit (lawPt g₂ g₃ h lam g w c c' (.e k (chartAt (h + g) k))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, lawPt, constantCoeff_addPt]
  obtain ⟨μ', hμ', hμ'0⟩ := addPt_coords hΔ g 0 c'
  obtain ⟨μ, hμ, hμ0⟩ := addPt_coords hΔ h g c
  have e1 : (fun v => PowerSeries.constantCoeff
      (addPt g₂ g₃ c' (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w) v)) =
      scl μ' (coords g 1) := by
    funext v
    rw [constantCoeff_addPt]
    simp only [fexp_const, PowerSeries.constantCoeff_C]
    rw [hμ', add_zero]
  simp only [PowerSeries.constantCoeff_C]
  rw [e1, coords_eq_scl h lam, addPt_scl_left, addPt_scl_right, hμ]
  simp only [scl_e, coords, coordsZ_e, Pi.one_apply, Units.val_one, rep_chartAt, mul_one,
    Pi.pow_apply]
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (mul_ne_zero (pow_ne_zero _ (hμ'0 hc' k))
    (hμ0 hc k))

end LawCurves

end LSG.ME
