/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.MEV.MultEstStmtV
import LSG.W88.Prop61V
import LSG.MEV.IGNull

/-!
# W88 §7 for the class `𝒞`: the polynomial of the auxiliary function

The auxiliary function `PsiV Ls M μs p` of `LSG.AuxV.prop61V_b` becomes a polynomial `PpolyV` on the
model `G̃_r = G_a^{d₀+r} × G_m^{d₁} × ∏ E_k^♮` of `G = G̃_r / K_M` (`LSG/MEV/MultEstStmtV.lean`):
the elliptic coordinates `(σ³, σ³℘, σ³℘′) ↦ (W, U, V)`, and the fibre forms
`fibF_i ↦ S_i = x_{d₀+i} Π_l W_l + Σ_j M_ij T₁^{(j)} Π_{l≠j} W_l`.

* `liftT (a, b, z, s) = ((a, s), b, z, 0)`, `pushT (x, b, z, w) = (x_{<d₀}, b, z, x_{≥d₀} + Mw)`;
  `pushT_liftT`, `pushT_kvec`, `ker_pushT` (`= K_M`).
* `ptV x`: the cone point `(a, s; e^b; e^{−b}; ellN(z_k, 0))`; **`eval_PpolyV`**:
  `PpolyV(ptV x) = PsiV x`
  (`fibF_eq_ellN` with `W = 0`); **`ptV_eq_coords`**: `ptV x` is a cone representative of
  `exp(liftT x)`.
* `isHomV_PpolyV`, `PpolyV_mem_FLE`, `trailDeg_PpolyV`, **`invarK_PpolyV`**, `PpolyV_notMem_IG`;
  `WprodV = Π_k W_k` with the same properties.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module LSG.MEV
open LSG.W88.Vec (TanV PerV LamV AlgMat fibreV etaV zetaV)
open LSG.AuxV (MonoV PsiV ellN fibF)
open LSG.Aux (ellW)
open LSG.ME (g2L g3L Dfun Blk)
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE prod_mem_FLE' pow_mem_FLE')

noncomputable section

namespace LSG.W88

variable {d0 d1 m r : ℕ}

/-! ### Lift and push-out of tangent vectors -/

/-- `(a, b, z, s) ↦ ((a, s), b, z, 0)`. -/
def liftT : TanV d0 d1 m r →ₗ[ℂ] TanG (d0 + r) d1 m where
  toFun x := (Fin.append x.1 x.2.2.2, x.2.1, x.2.2.1, 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (by simp)))
    funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (by simp)))
    funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

@[simp] theorem liftT_apply (x : TanV d0 d1 m r) :
    liftT x = ((Fin.append x.1 x.2.2.2, x.2.1, x.2.2.1, 0) : TanG (d0 + r) d1 m) := rfl

/-- `(x, b, z, w) ↦ (x_{<d₀}, b, z, x_{≥d₀} + Mw)`, the tangent map of `G̃_r → G`. -/
def pushT (M : Matrix (Fin r) (Fin m) ℂ) : TanG (d0 + r) d1 m →ₗ[ℂ] TanV d0 d1 m r where
  toFun p := (fun i => p.1 (Fin.castAdd r i), p.2.1, p.2.2.1,
    (fun i => p.1 (Fin.natAdd d0 i)) + M.mulVec p.2.2.2)
  map_add' p q := by
    refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
    funext i; simp [Matrix.mulVec_add]; ring
  map_smul' c p := by
    refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
    funext i; simp [Matrix.mulVec_smul]

@[simp] theorem pushT_apply (M : Matrix (Fin r) (Fin m) ℂ) (p : TanG (d0 + r) d1 m) :
    pushT M p = (fun i => p.1 (Fin.castAdd r i), p.2.1, p.2.2.1,
      (fun i => p.1 (Fin.natAdd d0 i)) + M.mulVec p.2.2.2) := rfl

theorem pushT_liftT (M : Matrix (Fin r) (Fin m) ℂ) (x : TanV d0 d1 m r) :
    pushT M (liftT x) = x := by
  refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
  funext i; simp

theorem pushT_kvec (M : Matrix (Fin r) (Fin m) ℂ) (v : Fin m → ℂ) :
    pushT M (kvec (d₀ := d0) (d₁ := d1) M v) = 0 := by
  refine Prod.ext (funext fun i => by simp [kvec]) (Prod.ext rfl (Prod.ext rfl ?_))
  funext i; simp [kvec]

/-- **`ker pushT = K_M`.** -/
theorem ker_pushT (M : Matrix (Fin r) (Fin m) ℂ) :
    LinearMap.ker (pushT (d0 := d0) (d1 := d1) M) = kerK (d₀ := d0) (d₁ := d1) M := by
  apply le_antisymm
  · intro p hp
    have h := LinearMap.mem_ker.mp hp
    simp only [pushT_apply, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨p.2.2.2, Prod.ext ?_ (Prod.ext h2.symm (Prod.ext h3.symm rfl))⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa [kvec] using (congrFun h1 i).symm
    · have := congrFun h4 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp [kvec]; linear_combination -this
  · rintro _ ⟨v, rfl⟩
    exact pushT_kvec M v

theorem liftT_injective : Function.Injective (liftT (d0 := d0) (d1 := d1) (m := m) (r := r)) :=
  fun x y h => by
    have := congrArg (pushT (d0 := d0) (d1 := d1) (0 : Matrix (Fin r) (Fin m) ℂ)) h
    rwa [pushT_liftT, pushT_liftT] at this

/-! ### The polynomial -/

/-- The cone index of the `ellW` index: `(σ³, σ³℘, σ³℘′) ↦ (W, U, V)`. -/
def cidx5 : Fin 3 → Fin 5 := ![2, 0, 1]

theorem ellN_cidx5 (L : PeriodPair) (z w : ℂ) (t : Fin 3) : ellN L z w (cidx5 t) = ellW L t z := by
  fin_cases t <;> rfl

/-- The fibre form `S_i = x_{d₀+i} Π_l W_l + Σ_j M_ij T₁^{(j)} Π_{l≠j} W_l`. -/
def fibPoly (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) : MvPolynomial (Var (d0 + r) d1 m) ℂ :=
  X (.x (Fin.natAdd d0 i)) * ∏ l, X (.e l 2) +
    ∑ j, C (M i j) * (X (.e j 3) * ∏ l ∈ Finset.univ.erase j, X (.e l 2))

/-- The cone monomial of `μ`. -/
def monoPolyV (M : Matrix (Fin r) (Fin m) ℂ) {D : ℕ} (μ : MonoV d0 d1 m r D) :
    MvPolynomial (Var (d0 + r) d1 m) ℂ :=
  (∏ i, X (.x (Fin.castAdd r i)) ^ μ.α i) * (∏ j, X (.y j) ^ μ.β j) *
    (∏ k, ∏ t : Fin 3, X (.e k (cidx5 t)) ^ μ.γ k t) *
      ∏ i, fibPoly (d0 := d0) (d1 := d1) M i ^ μ.φ i

/-- **The polynomial of the auxiliary function.** -/
def PpolyV (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ} (μs : Fin L → MonoV d0 d1 m r D)
    (p : Fin L → ℤ) : MvPolynomial (Var (d0 + r) d1 m) ℂ :=
  ∑ l, C (p l : ℂ) * monoPolyV M (μs l)

/-- The product of the `W`-coordinates. -/
def WprodV (d0 d1 m : ℕ) : MvPolynomial (Var d0 d1 m) ℂ := ∏ k, X (.e k 2)

/-! ### Evaluation -/

/-- The cone point `(a, s; e^b; e^{−b}; ellN(z_k, 0))` of `x`. -/
def ptV (Ls : Fin m → PeriodPair) (x : TanV d0 d1 m r) : Var (d0 + r) d1 m → ℂ
  | .x i => Fin.append x.1 x.2.2.2 i
  | .y j => Complex.exp (x.2.1 j)
  | .z j => Complex.exp (-x.2.1 j)
  | .e k c => ellN (Ls k) (x.2.2.1 k) 0 c

theorem eval_fibPoly (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r)
    (x : TanV d0 d1 m r) :
    eval (ptV Ls x) (fibPoly (d0 := d0) (d1 := d1) M i) = fibF Ls M i x.2.2.1 x.2.2.2 := by
  rw [LSG.AuxV.fibF_eq_ellN Ls M i x.2.2.1 x.2.2.2 0]
  simp only [fibPoly, map_add, map_mul, map_prod, map_sum, eval_X, eval_C, ptV, Fin.append_right]
  simp only [LSG.AuxV.ellN_two, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]

theorem eval_monoPolyV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {D : ℕ}
    (μ : MonoV d0 d1 m r D) (x : TanV d0 d1 m r) :
    eval (ptV Ls x) (monoPolyV M μ) = μ.eval Ls M x := by
  simp only [monoPolyV, MonoV.eval, map_mul, map_prod, map_pow, eval_X, eval_fibPoly]
  simp only [ptV, Fin.append_left, ellN_cidx5]

/-- **`PpolyV` evaluated at `ptV x` is `PsiV x`.** -/
theorem eval_PpolyV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (x : TanV d0 d1 m r) :
    eval (ptV Ls x) (PpolyV M μs p) = PsiV Ls M μs p x := by
  simp only [PpolyV, PsiV, map_sum, map_mul, eval_C, eval_monoPolyV]

/-- **`ptV x` is a cone representative of `exp(liftT x)`.** -/
theorem ptV_eq_coords (Ls : Fin m → PeriodPair) (x : TanV d0 d1 m r) :
    ∃ ν : Fin m → ℂˣ, ptV Ls x = coords (expGV Ls (liftT x)) ν := by
  choose c hc hce using fun k => LSG.AuxV.ellN_eq_smul_expN (Ls k) (x.2.2.1 k) 0
  refine ⟨fun k => Units.mk0 (c k) (hc k), ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => simp [ptV, coords, expGV, GPtV.ym, LSG.ME.expU]
  | z j => simp [ptV, coords, expGV, GPtV.ym, LSG.ME.expU, Complex.exp_neg]
  | e k c' =>
    simp only [ptV, coords, coordsZ_e, expGV, liftT_apply, Units.val_mk0]
    rw [repV_expV, hce k]; rfl

/-! ### Degrees -/

theorem isWH_X_e {n : ℕ} (k k' : Fin m) (c : Fin 5) :
    (X (.e k' c) : MvPolynomial (Var n d1 m) ℂ).IsWeightedHomogeneous (wb blk (Blk.e k))
      (if k' = k then 1 else 0) := by
  have := isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (Var.e k' c : Var n d1 m)
  convert this using 1
  simp [wb, blk]

theorem isWH_prod_W {n : ℕ} (k : Fin m) (s : Finset (Fin m)) :
    (∏ l ∈ s, (X (.e l 2) : MvPolynomial (Var n d1 m) ℂ)).IsWeightedHomogeneous
      (wb blk (Blk.e k)) (if k ∈ s then 1 else 0) := by
  have := IsWeightedHomogeneous.prod s (fun l => (X (.e l 2) : MvPolynomial (Var n d1 m) ℂ))
    (fun l => if l = k then 1 else 0) (fun l _ => isWH_X_e k l 2)
  convert this using 1
  rw [Finset.sum_ite_eq']

theorem isWH_fibPoly (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (k : Fin m) :
    (fibPoly (d0 := d0) (d1 := d1) M i).IsWeightedHomogeneous (wb blk (Blk.e k)) 1 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => ?_)
  · rw [mem_weightedHomogeneousSubmodule]
    have h1 := isWeightedHomogeneous_X ℂ (wb blk (Blk.e k))
      (Var.x (Fin.natAdd d0 i) : Var (d0 + r) d1 m)
    have h2 := isWH_prod_W (n := d0 + r) (d1 := d1) k Finset.univ
    convert h1.mul h2 using 1
    simp [wb, blk]
  · rw [mem_weightedHomogeneousSubmodule]
    have h1 := isWH_X_e (n := d0 + r) (d1 := d1) k j 3
    have h2 := isWH_prod_W (n := d0 + r) (d1 := d1) k (Finset.univ.erase j)
    convert (isWeightedHomogeneous_C (wb blk (Blk.e k)) (M i j)).mul (h1.mul h2) using 1
    by_cases hkj : j = k
    · subst hkj; simp
    · simp [hkj, Ne.symm hkj]

theorem isHomV_monoPolyV (M : Matrix (Fin r) (Fin m) ℂ) {D : ℕ} (μ : MonoV d0 d1 m r D) :
    IsHomV (monoPolyV M μ) (fun _ => D) := by
  intro k
  have hx := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.α i)
    (fun _ => 0) (fun i _ => by
      simpa [wb, blk] using (isWeightedHomogeneous_X ℂ (wb blk (Blk.e k))
        (Var.x (Fin.castAdd r i) : Var (d0 + r) d1 m)).pow (μ.α i))
  have hy := IsWeightedHomogeneous.prod Finset.univ
    (fun j => (X (.y j) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.β j)
    (fun _ => 0) (fun j _ => by
      simpa [wb, blk] using (isWeightedHomogeneous_X ℂ (wb blk (Blk.e k))
        (Var.y j : Var (d0 + r) d1 m)).pow (μ.β j))
  have he := IsWeightedHomogeneous.prod Finset.univ
    (fun k' => ∏ t : Fin 3, (X (.e k' (cidx5 t)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.γ k' t)
    (fun k' => if k' = k then ∑ t, μ.γ k' t else 0) (fun k' _ => by
      have := IsWeightedHomogeneous.prod Finset.univ
        (fun t : Fin 3 => (X (.e k' (cidx5 t)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.γ k' t)
        (fun t => μ.γ k' t * if k' = k then 1 else 0)
        (fun t _ => by simpa [mul_comm] using (isWH_X_e (n := d0 + r) (d1 := d1) k k'
          (cidx5 t)).pow (μ.γ k' t))
      convert this using 1
      split_ifs <;> simp)
  have hf := IsWeightedHomogeneous.prod Finset.univ
    (fun i => fibPoly (d0 := d0) (d1 := d1) M i ^ μ.φ i) (fun i => μ.φ i)
    (fun i _ => by simpa using (isWH_fibPoly (d0 := d0) (d1 := d1) M i k).pow (μ.φ i))
  change IsWeightedHomogeneous _ (monoPolyV M μ) D
  unfold monoPolyV
  convert ((hx.mul hy).mul he).mul hf using 1
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (μ.hγ k).symm

theorem isHomV_PpolyV (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ} (μs : Fin L → MonoV d0 d1 m r D)
    (p : Fin L → ℤ) : IsHomV (PpolyV M μs p) (fun _ => D) := by
  intro k
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [mem_weightedHomogeneousSubmodule]
  simpa using (isWeightedHomogeneous_C (wb blk (Blk.e k)) (p l : ℂ)).mul
    (isHomV_monoPolyV M (μs l) k)

theorem isHomV_WprodV : IsHomV (WprodV d0 d1 m) (fun _ => 1) := by
  intro k
  simpa [WprodV] using isWH_prod_W (n := d0) (d1 := d1) k Finset.univ

theorem isHomV_mul {P Q : MvPolynomial (Var d0 d1 m) ℂ} {d e : Fin m → ℕ} (hP : IsHomV P d)
    (hQ : IsHomV Q e) : IsHomV (P * Q) (d + e) := fun k => (hP k).mul (hQ k)

/-! ### Block degrees -/

/-- The block degrees of a fibre form: `1` in `x` and in every `E^♮` block. -/
def E1 (m : ℕ) : Blk m → ℕ := Pi.single Blk.x 1 + ∑ k : Fin m, Pi.single (Blk.e k) 1

theorem prodW_mem_FLE {n : ℕ} (s : Finset (Fin m)) :
    (∏ l ∈ s, (X (.e l 2) : MvPolynomial (Var n d1 m) ℂ)) ∈
      FLE ℂ blk (∑ l ∈ s, Pi.single (Blk.e l : Blk m) 1) :=
  prod_mem_FLE' _ _ _ fun l _ => LSG.ME.fle_X (Var.e l 2 : Var n d1 m)

theorem fibPoly_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    fibPoly (d0 := d0) (d1 := d1) M i ∈ FLE ℂ blk (E1 m) := by
  classical
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => ?_)
  · exact mul_mem_FLE ℂ (LSG.ME.fle_X (Var.x (Fin.natAdd d0 i) : Var (d0 + r) d1 m))
      (prodW_mem_FLE Finset.univ)
  · rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (FLE_mono ℂ blk ?_ (mul_mem_FLE ℂ
      (LSG.ME.fle_X (Var.e j 3 : Var (d0 + r) d1 m)) (prodW_mem_FLE (Finset.univ.erase j))))
    intro b
    simp only [E1, Pi.add_apply, Finset.sum_apply, blk_e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Pi.single_apply]
    omega

theorem monoPolyV_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) {D A B : ℕ} (μ : MonoV d0 d1 m r D)
    (hA : ∑ i, μ.α i + ∑ i, μ.φ i ≤ A) (hB : ∑ j, μ.β j ≤ B) :
    monoPolyV M μ ∈ FLE ℂ blk (Dfun A B D) := by
  classical
  have h1 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.α i)
    (fun i => μ.α i • Pi.single (blk (Var.x (Fin.castAdd r i) : Var (d0 + r) d1 m)) 1)
    (fun i _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h2 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun j => (X (.y j) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.β j)
    (fun j => μ.β j • Pi.single (blk (Var.y j : Var (d0 + r) d1 m)) 1)
    (fun j _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h3 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun k => ∏ t : Fin 3, (X (.e k (cidx5 t)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.γ k t)
    (fun k => ∑ t : Fin 3, μ.γ k t • Pi.single (blk (Var.e k (cidx5 t) : Var (d0 + r) d1 m)) 1)
    (fun k _ => prod_mem_FLE' _ _ _ fun t _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h4 := prod_mem_FLE' (K := ℂ) (β := blk) Finset.univ
    (fun i => fibPoly (d0 := d0) (d1 := d1) M i ^ μ.φ i) (fun i => μ.φ i • E1 m)
    (fun i _ => pow_mem_FLE' (fibPoly_mem_FLE M i) _)
  refine FLE_mono ℂ blk (fun b => ?_)
    (mul_mem_FLE ℂ (mul_mem_FLE ℂ (mul_mem_FLE ℂ h1 h2) h3) h4)
  cases b with
  | x =>
    simpa [Dfun, E1, Finset.sum_apply, Pi.single_apply] using hA
  | yz => simpa [Dfun, E1, Finset.sum_apply, Pi.single_apply] using hB
  | e k =>
    simp only [Dfun, E1, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blk_x, blk_y, blk_e,
      Pi.single_apply, smul_eq_mul, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero,
      zero_add, Blk.e.injEq, mul_ite, mul_one, add_zero]
    rw [Finset.sum_comm]
    simp [μ.hγ k]

theorem PpolyV_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) {D L A B : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ)
    (hA : ∀ l, ∑ i, (μs l).α i + ∑ i, (μs l).φ i ≤ A) (hB : ∀ l, ∑ j, (μs l).β j ≤ B) :
    PpolyV M μs p ∈ FLE ℂ blk (Dfun A B D) := by
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (monoPolyV_mem_FLE M _ (hA l) (hB l))

theorem WprodV_mem_FLE :
    WprodV d0 d1 m ∈ FLE ℂ blk (∑ k : Fin m, Pi.single (Blk.e k : Blk m) 1) :=
  prodW_mem_FLE Finset.univ

/-! ### Degree in the trailing additive variables -/

section Trail

variable {P Q : MvPolynomial (Var (d0 + r) d1 m) ℂ} {a b : ℕ}

theorem trailDeg_mono (h : a ≤ b) (hP : TrailDeg (d₀ := d0) a P) : TrailDeg (d₀ := d0) b P :=
  fun s hs => (hP s hs).trans h

theorem trailDeg_add (hP : TrailDeg (d₀ := d0) a P) (hQ : TrailDeg (d₀ := d0) a Q) :
    TrailDeg (d₀ := d0) a (P + Q) := by
  classical
  intro s hs
  rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
  · exact hP s h
  · exact hQ s h

theorem trailDeg_mul (hP : TrailDeg (d₀ := d0) a P) (hQ : TrailDeg (d₀ := d0) b Q) :
    TrailDeg (d₀ := d0) (a + b) (P * Q) := by
  classical
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  exact add_le_add (hP u hu) (hQ v hv)

theorem trailDeg_C_mul (c : ℂ) (hP : TrailDeg (d₀ := d0) a P) :
    TrailDeg (d₀ := d0) a (C c * P) :=
  fun s hs => hP s (MvPolynomial.support_smul (by rwa [smul_eq_C_mul]))

theorem trailDeg_one : TrailDeg (d₀ := d0) 0 (1 : MvPolynomial (Var (d0 + r) d1 m) ℂ) := by
  intro s hs
  rw [show (1 : MvPolynomial (Var (d0 + r) d1 m) ℂ) = monomial 0 1 from rfl] at hs
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hs
  simp [hs]

theorem trailDeg_pow (hP : TrailDeg (d₀ := d0) a P) (n : ℕ) :
    TrailDeg (d₀ := d0) (n * a) (P ^ n) := by
  induction n with
  | zero => simpa using trailDeg_one
  | succ n ih => rw [pow_succ, add_mul, one_mul]; exact trailDeg_mul ih hP

theorem trailDeg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Var (d0 + r) d1 m) ℂ)
    (e : ι → ℕ) (h : ∀ i ∈ s, TrailDeg (d₀ := d0) (e i) (f i)) :
    TrailDeg (d₀ := d0) (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using trailDeg_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact trailDeg_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem trailDeg_X (v : Var (d0 + r) d1 m) :
    TrailDeg (d₀ := d0) (∑ i : Fin r, Finsupp.single v 1 (.x (Fin.natAdd d0 i))) (X v) := by
  intro s hs
  rw [X] at hs
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hs
  rw [hs]

theorem trailDeg_X_lead {v : Var (d0 + r) d1 m} (hv : ∀ i : Fin r, v ≠ .x (Fin.natAdd d0 i)) :
    TrailDeg (d₀ := d0) 0 (X v) := by
  have h := trailDeg_X (d0 := d0) v
  have e : ∑ i : Fin r, Finsupp.single v 1 (.x (Fin.natAdd d0 i)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (hv i).symm
  rwa [e] at h

theorem trailDeg_prodW (s : Finset (Fin m)) :
    TrailDeg (d₀ := d0) 0 (∏ l ∈ s, (X (.e l 2) : MvPolynomial (Var (d0 + r) d1 m) ℂ)) := by
  simpa using trailDeg_prod (d0 := d0) s (fun l => X (.e l 2)) (fun _ => 0)
    fun l _ => trailDeg_X_lead fun i' => by simp

theorem trailDeg_fibPoly (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    TrailDeg (d₀ := d0) 1 (fibPoly (d0 := d0) (d1 := d1) M i) := by
  classical
  refine trailDeg_add ?_ ?_
  · have h1 : TrailDeg (d₀ := d0) 1
        (X (.x (Fin.natAdd d0 i)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) := by
      refine trailDeg_mono ?_ (trailDeg_X (d0 := d0) _)
      rw [Finset.sum_eq_single i (fun j _ hj => Finsupp.single_eq_of_ne
        (fun h => by
          have := congrArg Fin.val (Var.x.inj h); simp at this; exact hj (Fin.ext (by omega))))
        (by simp)]
      simp
    simpa using trailDeg_mul h1 (trailDeg_prodW Finset.univ)
  · intro s hs
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
    have h3 : TrailDeg (d₀ := d0) 0 (X (.e j 3) : MvPolynomial (Var (d0 + r) d1 m) ℂ) :=
      trailDeg_X_lead fun i' => by simp
    exact (trailDeg_C_mul _ (by simpa using trailDeg_mul h3 (trailDeg_prodW _)) s hj).trans
      (Nat.zero_le 1)

theorem trailDeg_monoPolyV (M : Matrix (Fin r) (Fin m) ℂ) {D : ℕ} (μ : MonoV d0 d1 m r D) :
    TrailDeg (d₀ := d0) D (monoPolyV M μ) := by
  have h1 := trailDeg_prod (d0 := d0) Finset.univ
    (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.α i)
    (fun _ => 0) fun i _ => by
      simpa using trailDeg_pow (trailDeg_X_lead (d0 := d0) (v := .x (Fin.castAdd r i))
        fun i' h => by
          have := congrArg Fin.val (Var.x.inj h); simp at this; omega) (μ.α i)
  have h2 := trailDeg_prod (d0 := d0) Finset.univ
    (fun j => (X (.y j) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.β j)
    (fun _ => 0) fun j _ => by
      simpa using trailDeg_pow (trailDeg_X_lead (d0 := d0) (v := .y j) fun i' => by simp) (μ.β j)
  have h3 := trailDeg_prod (d0 := d0) Finset.univ
    (fun k => ∏ t : Fin 3, (X (.e k (cidx5 t)) : MvPolynomial (Var (d0 + r) d1 m) ℂ) ^ μ.γ k t)
    (fun _ => 0) fun k _ => by
      simpa using trailDeg_prod (d0 := d0) Finset.univ _ (fun _ => 0) fun t _ => by
        simpa using trailDeg_pow (trailDeg_X_lead (d0 := d0) (v := .e k (cidx5 t))
          fun i' => by simp) (μ.γ k t)
  have h4 := trailDeg_prod (d0 := d0) Finset.univ
    (fun i => fibPoly (d0 := d0) (d1 := d1) M i ^ μ.φ i) (fun i => μ.φ i) fun i _ => by
      simpa using trailDeg_pow (trailDeg_fibPoly (d0 := d0) (d1 := d1) M i) (μ.φ i)
  refine trailDeg_mono ?_ (trailDeg_mul (trailDeg_mul (trailDeg_mul h1 h2) h3) h4)
  simpa using μ.hφ

theorem trailDeg_PpolyV (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) : TrailDeg (d₀ := d0) D (PpolyV M μs p) := by
  classical
  intro s hs
  obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
  exact trailDeg_C_mul _ (trailDeg_monoPolyV M (μs l)) s hl

theorem trailDeg_WprodV : TrailDeg (d₀ := d0) 0 (WprodV (d0 + r) d1 m) :=
  trailDeg_prodW Finset.univ

end Trail

/-! ### Invariance under `K_M` -/

section Invar

variable (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (g : GPtV (d0 + r) d1 Ls)
  (lam : Fin m → ℂˣ) (v : Fin m → ℂ)

theorem expU_zero : LSG.ME.expU 0 = 1 := Units.ext (by simp [LSG.ME.expU])

theorem coords_kvec_xl (i : Fin d0) :
    coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam (.x (Fin.castAdd r i)) =
      coords g lam (.x (Fin.castAdd r i)) := by
  simp [coords, expGV, kvec]

theorem coords_kvec_xt (i : Fin r) :
    coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam (.x (Fin.natAdd d0 i)) =
      coords g lam (.x (Fin.natAdd d0 i)) - M.mulVec v i := by
  simp [coords, expGV, kvec, sub_eq_add_neg]

theorem coords_kvec_y (j : Fin d1) :
    coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam (.y j) = coords g lam (.y j) := by
  simp [coords, expGV, kvec, GPtV.ym, expU_zero]

theorem coords_kvec_e (k : Fin m) (c : Fin 5) :
    coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam (.e k c) =
      coords g lam (.e k c) + v k * ((fibv fun i => coords g lam (.e k i)) c) := by
  have h : (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)).2.2 k = g.2.2 k + expV (Ls k) (0, v k) :=
    rfl
  simp only [coords, coordsZ_e, h, add_expV_fib, repV, repB_add_fib]
  fin_cases c <;> simp [fibv] <;> ring

theorem eval_fibPoly_kvec (i : Fin r) :
    eval (coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam) (fibPoly M i) =
      eval (coords g lam) (fibPoly (d0 := d0) (d1 := d1) M i) := by
  simp only [fibPoly, map_add, map_mul, map_prod, map_sum, eval_X, eval_C, coords_kvec_xt,
    coords_kvec_e]
  simp only [fibv, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
    mul_zero, add_zero]
  set c := coords g lam
  have hW : ∀ j, c (.e j 2) * ∏ l ∈ Finset.univ.erase j, c (.e l 2) = ∏ l, c (.e l 2) :=
    fun j => Finset.mul_prod_erase _ (fun l => c (.e l 2)) (Finset.mem_univ j)
  have hsum : ∑ j, M i j * ((c (.e j 3) + v j * c (.e j 2)) *
      ∏ l ∈ Finset.univ.erase j, c (.e l 2)) =
      ∑ j, M i j * (c (.e j 3) * ∏ l ∈ Finset.univ.erase j, c (.e l 2)) +
        M.mulVec v i * ∏ l, c (.e l 2) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hW j]; ring
  rw [hsum]; ring

theorem eval_monoPolyV_kvec {D : ℕ} (μ : MonoV d0 d1 m r D) :
    eval (coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam) (monoPolyV M μ) =
      eval (coords g lam) (monoPolyV M μ) := by
  have he : ∀ k t, coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam (.e k (cidx5 t)) =
      coords g lam (.e k (cidx5 t)) := fun k t => by
    rw [coords_kvec_e]; fin_cases t <;> simp [cidx5, fibv]
  simp only [monoPolyV, map_mul, map_prod, map_pow, eval_X, coords_kvec_xl, coords_kvec_y, he,
    eval_fibPoly_kvec]

theorem eval_WprodV_kvec :
    eval (coords (g + expGV Ls (kvec (d₀ := d0) (d₁ := d1) M v)) lam) (WprodV (d0 + r) d1 m) =
      eval (coords g lam) (WprodV (d0 + r) d1 m) := by
  simp only [WprodV, map_prod, eval_X, coords_kvec_e]
  simp [fibv]

/-- **The polynomial of the auxiliary function is a polynomial on `G`.** -/
theorem invarK_PpolyV {D L : ℕ} (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) :
    InvarK Ls M (PpolyV M μs p * WprodV (d0 + r) d1 m) := by
  intro g lam v
  rw [map_mul, map_mul, eval_WprodV_kvec]
  congr 1
  simp only [PpolyV, map_sum, map_mul, eval_C, eval_monoPolyV_kvec]

end Invar

/-! ### Nonvanishing on `G̃` -/

theorem PpolyV_notMem_IG (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (hne : ∃ x, PsiV Ls M μs p x ≠ 0) :
    PpolyV M μs p ∉ IG (d₀ := d0 + r) (d₁ := d1) (g2L Ls) (g3L Ls) := by
  intro hP
  rw [← vanish_univ] at hP
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ν, hν⟩ := ptV_eq_coords Ls x
  apply hx
  rw [← eval_PpolyV, hν]
  exact mem_vanish.mp hP _ (Set.mem_univ _) ν

theorem WprodV_notMem_IG {n : ℕ} (Ls : Fin m → PeriodPair) :
    WprodV n d1 m ∉ IG (d₀ := n) (d₁ := d1) (g2L Ls) (g3L Ls) := by
  intro hP
  obtain ⟨k, -, hk⟩ :=
    ((IG_isPrime (d₀ := n) (d₁ := d1) (g2L Ls) (g3L Ls) (two_ne_zero' ℂ)).prod_mem_iff).mp hP
  rw [← vanish_univ] at hk
  set x : TanG n d1 m := (0, 0, fun j => (Ls j).ω₁ / 2, 0)
  have h := mem_vanish.mp hk (expGV Ls x) (Set.mem_univ _) 1
  have hnot : (Ls k).ω₁ / 2 ∉ (Ls k).lattice := (Ls k).ω₁_div_two_notMem_lattice
  simp only [eval_X, coords, coordsZ_e, Pi.one_apply, Units.val_one, one_mul, expGV, x,
    repV_expV, expN_of_notMem _ hnot] at h
  simp [ptAff] at h

theorem PV_notMem_IG (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {D L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (hne : ∃ x, PsiV Ls M μs p x ≠ 0) :
    PpolyV M μs p * WprodV (d0 + r) d1 m ∉ IG (d₀ := d0 + r) (d₁ := d1) (g2L Ls) (g3L Ls) := by
  intro h
  rcases (IG_isPrime (d₀ := d0 + r) (d₁ := d1) (g2L Ls) (g3L Ls) (two_ne_zero' ℂ)).mem_or_mem h
    with h' | h'
  · exact PpolyV_notMem_IG Ls M μs p hne h'
  · exact WprodV_notMem_IG Ls h'

end LSG.W88
