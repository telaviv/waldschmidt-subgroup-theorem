import Mathlib
import LSG.MEV.SubgroupExp

/-!
# The homogenised invariant derivation `D̂_w` of `G̃` (`V`-chart; for the subgroup layer)

Written for the subgroup layer (STAGE5_MEV §6, gap G3), independently of the curve-lemma files
(`Flow.lean`'s `dvalB` is the same block field up to the parametrisation `ζ = 2s`, as a vector function).

**Block field** (`bField g₂ g₃ a b P`, direction `(a, b)` = base and fibre speed, `V`-chart, degree `+2`):
with `c_U = −V²/2 − g₂UW − (3/2)g₃W²`, `c_W = −6U² + (g₂/2)W²` (the abelian `V`-chart field) and
`R = bV² + a(2g₂U² + 3g₃UW)`:
`U ↦ aV c_U`, `V ↦ 0`, `W ↦ aV c_W`, `T₁ ↦ a(c_W T₃ + 4U c_U) + W R`, `T₃ ↦ V R`.
It preserves `G = WT₃ − VT₁ + 2U²` exactly; at `V = 1` it is the derivative of the `V`-normalised
lift of `exp_{E^♮}` (`LSG.MEV.SubgroupLiftV`).

**`Dh Ls w`** (a derivation of `ℂ[Var]`): `X_v ↦ Vfac_v · dval_v`, `dval` = `(a, b·y, −b·z, bField)`,
`Vfac = ∏_k V_k²` on linear variables and `∏_{k' ≠ k} V_{k'}²` on block `k`.
* `eval_Dh`: `eval y (Dh w Q) = Σ_v ∂_vQ(y) · DV w y v` (`DV` the evaluated field);
* `DV_add`, `DV_smul` (linear in `w`); `DV_of_V` (at `V = 1` the factors are `1`);
* **`DV_scale`**: `DV w (r · y) = (∏ r_k²) · r · DV w y` (block rescaling);
* **`DV_eq_zero_of_V`**: `DV w y = 0` if some block of `y` is a nonzero multiple of `repV p` with
  `V = 0` (`bField` vanishes there, by `F = G = 0`).
-/

open MvPolynomial LSG.Elliptic

namespace LSG.MEV

noncomputable section

/-! ### The block field -/

/-- The block field on a vector, over a `ℂ`-algebra. -/
def bField {R : Type*} [CommRing R] [Algebra ℂ R] (g₂ g₃ a b : R) (P : Fin 5 → R) : Fin 5 → R :=
  let h : R := algebraMap ℂ R (1 / 2)
  let cU := -(h * P 1 ^ 2) - g₂ * P 0 * P 2 - 3 * h * g₃ * P 2 ^ 2
  let cW := -(6 * P 0 ^ 2) + h * g₂ * P 2 ^ 2
  let Rr := b * P 1 ^ 2 + a * (2 * g₂ * P 0 ^ 2 + 3 * g₃ * P 0 * P 2)
  ![a * P 1 * cU, 0, a * P 1 * cW, a * (cW * P 4 + 4 * P 0 * cU) + P 2 * Rr, P 1 * Rr]

theorem bField_map {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (f : R →ₐ[ℂ] S) (g₂ g₃ a b : R) (P : Fin 5 → R) (i : Fin 5) :
    f (bField g₂ g₃ a b P i) = bField (f g₂) (f g₃) (f a) (f b) (f ∘ P) i := by
  fin_cases i <;> simp [bField, AlgHom.commutes, map_ofNat]

theorem bField_smul (g₂ g₃ a b r : ℂ) (P : Fin 5 → ℂ) (i : Fin 5) :
    bField g₂ g₃ a b (r • P) i = r ^ 3 * bField g₂ g₃ a b P i := by
  fin_cases i <;> simp [bField] <;> ring

theorem bField_add (g₂ g₃ a b a' b' : ℂ) (P : Fin 5 → ℂ) (i : Fin 5) :
    bField g₂ g₃ (a + a') (b + b') P i = bField g₂ g₃ a b P i + bField g₂ g₃ a' b' P i := by
  fin_cases i <;> simp [bField] <;> ring

theorem bField_smul_dir (g₂ g₃ a b c : ℂ) (P : Fin 5 → ℂ) (i : Fin 5) :
    bField g₂ g₃ (c * a) (c * b) P i = c * bField g₂ g₃ a b P i := by
  fin_cases i <;> simp [bField] <;> ring

/-- `bField` preserves `G`. -/
theorem bField_G (g₂ g₃ a b : ℂ) (P : Fin 5 → ℂ) :
    P 2 * bField g₂ g₃ a b P 4 + bField g₂ g₃ a b P 2 * P 4 - P 1 * bField g₂ g₃ a b P 3 -
      bField g₂ g₃ a b P 1 * P 3 + 4 * P 0 * bField g₂ g₃ a b P 0 = 0 := by
  simp [bField]; ring

/-- **`bField` vanishes at the points of `X` with `V = 0`, `W ≠ 0`** (the `2`-torsion fibres). -/
theorem bField_eq_zero_of_V {g₂ g₃ : ℂ} (a b : ℂ) {P : Fin 5 → ℂ} (hF : Fn g₂ g₃ P = 0)
    (hG : Gn P = 0) (hV : P 1 = 0) (hW : P 2 ≠ 0) (i : Fin 5) : bField g₂ g₃ a b P i = 0 := by
  simp only [Fn, F, Gn, Gfib] at hF hG
  fin_cases i
  · simp [bField, hV]
  · simp [bField]
  · simp [bField, hV]
  · have e3 : bField g₂ g₃ a b P 3 = a * ((-(6 * P 0 ^ 2) + 1 / 2 * g₂ * P 2 ^ 2) * P 4 +
        4 * P 0 * (-(1 / 2 * P 1 ^ 2) - g₂ * P 0 * P 2 - 3 * (1 / 2) * g₃ * P 2 ^ 2)) +
        P 2 * (b * P 1 ^ 2 + a * (2 * g₂ * P 0 ^ 2 + 3 * g₃ * P 0 * P 2)) := by
      simp [bField]
    show bField g₂ g₃ a b P 3 = 0
    rw [e3]
    refine (mul_eq_zero.mp (?_ : P 2 * _ = 0)).resolve_left hW
    rw [hV] at hF hG ⊢
    linear_combination (a * (-(6 * P 0 ^ 2) + 1 / 2 * g₂ * P 2 ^ 2)) * hG - 3 * a * P 0 * hF
  · simp [bField, hV]

theorem repV_W_ne_of_V {L : PeriodPair} (p : EVL L) (h : repV p 1 = 0) : repV p 2 ≠ 0 := by
  obtain ⟨b, t⟩ := p
  cases b with
  | zero => exact absurd h (by simp [repV, repB, ptO])
  | some x y hxy => simp [repV, repB, ptAff]

/-! ### The derivation -/

variable {d₀ d₁ m : ℕ} (Ls : Fin m → PeriodPair)

/-- The `V`-factors homogenising the derivation. -/
def Vfac : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .e k _ => ∏ k' ∈ Finset.univ.erase k, X (.e k' 1) ^ 2
  | _ => ∏ k', X (.e k' 1) ^ 2

/-- The values of `D_w` on the variables (before homogenisation). -/
def dvalV (w : TanG d₀ d₁ m) : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .x i => C (w.1 i)
  | .y j => C (w.2.1 j) * X (.y j)
  | .z j => -(C (w.2.1 j) * X (.z j))
  | .e k c => bField (C (Ls k).g₂) (C (Ls k).g₃) (C (w.2.2.1 k)) (C (w.2.2.2 k))
      (fun i => X (.e k i)) c

/-- **The homogenised derivation `D̂_w`.** -/
def Dh (w : TanG d₀ d₁ m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  mkDerivation ℂ fun v => Vfac v * dvalV Ls w v

/-- `V`-factors at a point. -/
def vfacE (y : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ
  | .e k _ => ∏ k' ∈ Finset.univ.erase k, y (.e k' 1) ^ 2
  | _ => ∏ k', y (.e k' 1) ^ 2

/-- The evaluated field (before homogenisation). -/
def dvalE (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * y (.y j)
  | .z j => -(w.2.1 j * y (.z j))
  | .e k c => bField (Ls k).g₂ (Ls k).g₃ (w.2.2.1 k) (w.2.2.2 k) (fun i => y (.e k i)) c

/-- The evaluated homogenised field. -/
def DV (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) : ℂ :=
  vfacE y v * dvalE Ls w y v

theorem eval_Vfac (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) : eval y (Vfac v) = vfacE y v := by
  cases v <;> simp [Vfac, vfacE]

theorem eval_dvalV (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) :
    eval y (dvalV Ls w v) = dvalE Ls w y v := by
  cases v with
  | x i => simp [dvalV, dvalE]
  | y j => simp [dvalV, dvalE]
  | z j => simp [dvalV, dvalE]
  | e k c =>
    simp only [dvalV, dvalE]
    rw [← coe_aeval_eq_eval]
    exact (bField_map (aeval y) _ _ _ _ _ c).trans (by simp [Function.comp_def])

/-- A derivation of `K[σ]` is `Σ_v (D X_v) ∂_v`. -/
theorem mkDerivation_eq_sum {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → MvPolynomial σ ℂ) (P : MvPolynomial σ ℂ) :
    mkDerivation ℂ f P = ∑ v, f v * pderiv v P := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [← algebraMap_eq, Derivation.map_algebraMap]; simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e : ∀ x, pderiv x (p * X v) =
        p * (Pi.single x (1 : MvPolynomial σ ℂ) : σ → _) v + X v * pderiv x p := by
      intro x; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp_rw [e]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, mkDerivation_X]
    have e1 : ∑ x, f x * (p * (Pi.single x (1 : MvPolynomial σ ℂ) : σ → _) v) = p * f v := by
      rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb)]; ring)
        (by simp)]
      simp only [Pi.single_eq_same]; ring
    have e2 : ∑ x, f x * (X v * pderiv x p) = X v * ∑ x, f x * pderiv x p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
    simp only [mul_add, Finset.sum_add_distrib, e1, e2]

/-- **Evaluation of `D̂_w`.** -/
theorem eval_Dh (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval y (Dh Ls w Q) = ∑ v, eval y (pderiv v Q) * DV Ls w y v := by
  classical
  rw [Dh, mkDerivation_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, map_mul, eval_Vfac, eval_dvalV, DV]; ring

theorem DV_add (w w' : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) :
    DV Ls (w + w') y v = DV Ls w y v + DV Ls w' y v := by
  unfold DV
  rw [← mul_add]
  congr 1
  cases v with
  | x i => simp [dvalE]
  | y j => simp [dvalE]; ring
  | z j => simp [dvalE]; ring
  | e k c => simp only [dvalE, Prod.snd_add, Prod.fst_add, Pi.add_apply, bField_add]

theorem DV_smul (c : ℂ) (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) :
    DV Ls (c • w) y v = c * DV Ls w y v := by
  unfold DV
  rw [mul_left_comm]
  congr 1
  cases v with
  | x i => simp [dvalE]
  | y j => simp [dvalE]; ring
  | z j => simp [dvalE]; ring
  | e k c' => simp only [dvalE, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
      bField_smul_dir]

theorem Dh_add (w w' : TanG d₀ d₁ m) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) (y : Var d₀ d₁ m → ℂ) :
    eval y (Dh Ls (w + w') Q) = eval y (Dh Ls w Q) + eval y (Dh Ls w' Q) := by
  simp only [eval_Dh, DV_add, mul_add, Finset.sum_add_distrib]

theorem Dh_smul (c : ℂ) (w : TanG d₀ d₁ m) (Q : MvPolynomial (Var d₀ d₁ m) ℂ)
    (y : Var d₀ d₁ m → ℂ) : eval y (Dh Ls (c • w) Q) = c * eval y (Dh Ls w Q) := by
  simp only [eval_Dh, DV_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- At a point with all `V`-coordinates `1`, the `V`-factors are `1`. -/
theorem DV_of_V {y : Var d₀ d₁ m → ℂ} (hy : ∀ k, y (.e k 1) = 1) (w : TanG d₀ d₁ m)
    (v : Var d₀ d₁ m) : DV Ls w y v = dvalE Ls w y v := by
  unfold DV
  cases v <;> simp [vfacE, hy]

/-! ### Rescaling -/

/-- Rescaling the `E^♮` blocks of a cone vector. -/
def scaleV (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ
  | .e k c => r k * y (.e k c)
  | v => y v

@[simp] theorem scaleV_e (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (k : Fin m) (c : Fin 5) :
    scaleV r y (.e k c) = r k * y (.e k c) := rfl
@[simp] theorem scaleV_x (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (i : Fin d₀) :
    scaleV r y (.x i) = y (.x i) := rfl
@[simp] theorem scaleV_y (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (j : Fin d₁) :
    scaleV r y (.y j) = y (.y j) := rfl
@[simp] theorem scaleV_z (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (j : Fin d₁) :
    scaleV r y (.z j) = y (.z j) := rfl

theorem prod_erase_sq (r : Fin m → ℂ) (k : Fin m) :
    (∏ k' ∈ Finset.univ.erase k, r k' ^ 2) * r k ^ 2 = ∏ k', r k' ^ 2 :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ k)

/-- **`D̂_w` is equivariant under block rescaling** (up to the uniform factor `∏ r_k²`). -/
theorem DV_scale (r : Fin m → ℂ) (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) :
    DV Ls w (scaleV r y) v = (∏ k, r k ^ 2) * scaleV r (DV Ls w y) v := by
  unfold DV
  cases v with
  | x i => simp [vfacE, dvalE, mul_pow, Finset.prod_mul_distrib]; ring
  | y j => simp [vfacE, dvalE, mul_pow, Finset.prod_mul_distrib]; ring
  | z j => simp [vfacE, dvalE, mul_pow, Finset.prod_mul_distrib]; ring
  | e k c =>
    simp only [vfacE, dvalE, scaleV_e, mul_pow, Finset.prod_mul_distrib]
    have hb : (fun i => r k * y (.e k i)) = r k • fun i => y (.e k i) := by funext i; simp
    rw [hb, bField_smul, ← prod_erase_sq r k]
    ring

/-- **`D̂_w` vanishes at cone points with a `2`-torsion fibre block.** -/
theorem DV_eq_zero_of_V {y : Var d₀ d₁ m → ℂ} {k : Fin m} {p : EVL (Ls k)} {u : ℂ}
    (hy : (fun c => y (.e k c)) = u • repV p) (hV : repV p 1 = 0) (w : TanG d₀ d₁ m)
    (v : Var d₀ d₁ m) : DV Ls w y v = 0 := by
  have hyV : y (.e k 1) = 0 := by
    have := congrFun hy 1; simp only [Pi.smul_apply, smul_eq_mul, hV, mul_zero] at this
    exact this
  unfold DV
  cases v with
  | x i => simp only [vfacE]; rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hyV]), zero_mul]
  | y j => simp only [vfacE]; rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hyV]), zero_mul]
  | z j => simp only [vfacE]; rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hyV]), zero_mul]
  | e k' c =>
    by_cases hk : k' = k
    · subst hk
      simp only [dvalE]
      rw [hy, bField_smul, bField_eq_zero_of_V _ _ (Fn_repV p) (Gn_repV p) hV
        (repV_W_ne_of_V p hV) c, mul_zero, mul_zero]
    · simp only [vfacE]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hk, Finset.mem_univ k⟩)
        (by simp [hyV] : y (.e k 1) ^ 2 = 0), zero_mul]

end

end LSG.MEV
