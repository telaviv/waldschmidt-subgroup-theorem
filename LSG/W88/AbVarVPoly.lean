/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVProp61
import LSG.ME.Transl

/-!
# M2.6.8a: the polynomial fed to `MultEstV` (push-out model `G = G̃_r / K_M`)

`G̃_r = G_a^{d₀+r} × G_m^{d₁} × ∏ B_k^♮` (MEBV's `Tan (d₀ + r) d₁ B ∋ (x, b, z, w)`), `K_M = range kvec`.

* `liftTA (a, b, z, s) = ((a, s), b, z, 0)`, `pushTA M (x, b, z, w) = (x_{<d₀}, b, z, x_{≥d₀} + M w)`;
  `pushTA_liftTA`, `pushTA_kvec`, **`ker_pushTA`** (`= kerK M`), `liftTA_injective`.
* The cone polynomials (MEBV variables): `fibPolyA M i = x_{d₀+i} Π_k X_{k,i₀} + Σ_j M_ij T_{j,t₀} Π_{l≠j} X_{l,i₀}`,
  `monoPolyA M ν`, `PpolyAV M νs p`, `WprodA = Π_k X_{k,i₀}`.
* **`eval_PpolyAV`**: `eval (liftV U) (PpolyAV M νs p) = PsiAV M νs p (pushTA M U)` for every `U` (via `T_t₀_add`), so
  **`invarKV_PW`** (`InvarKV M`) holds because `pushTA ∘ kvec = 0`.
* `isHomV_PW` (block degree `D + F + 1`), `PW_mem_FLE`, `trailDeg_PW` (`≤ F`), `PW_notMem_IGsem`, **`ordGtV_PW`**.
-/

open MvPolynomial Module Finset LSG.AuxAV LSG.AuxA
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE prod_mem_FLE' pow_mem_FLE')

noncomputable section

namespace LSG.W88

open LSG.MEB (Blk DfunB)
open LSG.MEBV (VBlock Var liftV blk wk IsHomV InvarKV TrailDeg kvec kerK IGsem OrdGtV expG
  notMem_IGsem_of_eval_ne)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock}

/-! ### Lift and push-out of tangent vectors -/

/-- `(a, b, z, s) ↦ ((a, s), b, z, 0)`. -/
def liftTA : TanAV d₀ d₁ r B →ₗ[ℂ] LSG.MEBV.Tan (d₀ + r) d₁ B where
  toFun x := (Fin.append x.1 x.2.2.2, x.2.1, x.2.2.1, 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (by simp)))
    funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (by simp)))
    funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

@[simp] theorem liftTA_apply (x : TanAV d₀ d₁ r B) :
    liftTA x = ((Fin.append x.1 x.2.2.2, x.2.1, x.2.2.1, 0) : LSG.MEBV.Tan (d₀ + r) d₁ B) := rfl

/-- `(x, b, z, w) ↦ (x_{<d₀}, b, z, x_{≥d₀} + M w)`, the tangent map of `G̃_r → G`. -/
def pushTA (M : Matrix (Fin r) (Fin m) ℂ) : LSG.MEBV.Tan (d₀ + r) d₁ B →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun p := (fun i => p.1 (Fin.castAdd r i), p.2.1, p.2.2.1,
    (fun i => p.1 (Fin.natAdd d₀ i)) + M.mulVec p.2.2.2)
  map_add' p q := by
    refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
    funext i; simp [Matrix.mulVec_add]; ring
  map_smul' c p := by
    refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
    funext i; simp [Matrix.mulVec_smul]

@[simp] theorem pushTA_apply (M : Matrix (Fin r) (Fin m) ℂ) (p : LSG.MEBV.Tan (d₀ + r) d₁ B) :
    pushTA M p = (fun i => p.1 (Fin.castAdd r i), p.2.1, p.2.2.1,
      (fun i => p.1 (Fin.natAdd d₀ i)) + M.mulVec p.2.2.2) := rfl

theorem pushTA_liftTA (M : Matrix (Fin r) (Fin m) ℂ) (x : TanAV d₀ d₁ r B) : pushTA M (liftTA x) = x := by
  refine Prod.ext (funext fun i => by simp) (Prod.ext rfl (Prod.ext rfl ?_))
  funext i; simp

theorem pushTA_kvec (M : Matrix (Fin r) (Fin m) ℂ) (v : Fin m → ℂ) :
    pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M (kvec M v) = 0 := by
  refine Prod.ext (funext fun i => by simp [kvec]) (Prod.ext rfl (Prod.ext rfl ?_))
  funext i; simp [kvec]

/-- **`ker pushTA = K_M`.** -/
theorem ker_pushTA (M : Matrix (Fin r) (Fin m) ℂ) :
    LinearMap.ker (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M) = kerK d₀ d₁ B M := by
  apply le_antisymm
  · intro p hp
    have h := LinearMap.mem_ker.mp hp
    simp only [pushTA_apply, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨p.2.2.2, Prod.ext ?_ (Prod.ext h2.symm (Prod.ext h3.symm rfl))⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa [kvec] using (congrFun h1 i).symm
    · have := congrFun h4 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp [kvec]; linear_combination -this
  · rintro _ ⟨v, rfl⟩
    exact pushTA_kvec M v

theorem liftTA_injective : Function.Injective (liftTA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) :=
  fun x y h => by
    have := congrArg (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) (0 : Matrix (Fin r) (Fin m) ℂ)) h
    rwa [pushTA_liftTA, pushTA_liftTA] at this

/-! ### The polynomial -/

/-- `X_{k,i₀}`. -/
abbrev XI (k : Fin m) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ := X (.e k (Sum.inl (B k).base.i₀))

/-- `T_{k,t₀}`. -/
abbrev XT (k : Fin m) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ := X (.e k (Sum.inr (B k).t₀))

/-- **The fibre form** `x_{d₀+i} Π_k X_{k,i₀} + Σ_j M_ij T_{j,t₀} Π_{l≠j} X_{l,i₀}` (`K_M`-invariant). -/
def fibPolyA (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ :=
  X (.x (Fin.natAdd d₀ i)) * ∏ k, XI k + ∑ j, C (M i j) * (XT j * ∏ l ∈ univ.erase j, XI l)

/-- The cone monomial of `ν`. -/
def monoPolyA (M : Matrix (Fin r) (Fin m) ℂ) {D F : ℕ} (ν : MonoAV d₀ d₁ r B D F) :
    MvPolynomial (Var (d₀ + r) d₁ B) ℂ :=
  (∏ i, X (.x (Fin.castAdd r i)) ^ ν.μ.α i) * (∏ j, X (.y j) ^ ν.μ.β j) *
    (∏ k, ∏ c, X (.e k (Sum.inl (fidx (Bb B k) c))) ^ ν.μ.γ k c) *
      (∏ k, XI k) ^ (F - ∑ i, ν.φ i) * ∏ i, fibPolyA (d₀ := d₀) (d₁ := d₁) M i ^ ν.φ i

/-- **The polynomial of the auxiliary function.** -/
def PpolyAV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ :=
  ∑ l, C (p l : ℂ) * monoPolyA M (νs l)

/-- The product of the `X_{k,i₀}`. -/
def WprodA : MvPolynomial (Var (d₀ + r) d₁ B) ℂ := ∏ k, XI k

/-- **The polynomial fed to `MultEstV`.** -/
def PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ) :
    MvPolynomial (Var (d₀ + r) d₁ B) ℂ :=
  PpolyAV M νs p * WprodA

/-! ### Evaluation -/

theorem eval_XI (U : LSG.MEBV.Tan (d₀ + r) d₁ B) (k : Fin m) :
    eval (liftV U) (XI (d₀ := d₀) (r := r) (d₁ := d₁) k) = thI B U.2.2.1 k := by
  rw [XI, eval_X]; rfl

theorem eval_XT (U : LSG.MEBV.Tan (d₀ + r) d₁ B) (k : Fin m) :
    eval (liftV U) (XT (d₀ := d₀) (r := r) (d₁ := d₁) k) =
      thI B U.2.2.1 k * U.2.2.2 k + (B k).T (U.2.2.1 k) 0 (B k).t₀ := by
  rw [XT, eval_X]
  change (B k).T (U.2.2.1 k) (U.2.2.2 k) (B k).t₀ = _
  rw [T_t₀_add]; rfl

theorem eval_fibPolyA (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (U : LSG.MEBV.Tan (d₀ + r) d₁ B) :
    eval (liftV U) (fibPolyA (d₀ := d₀) (d₁ := d₁) M i) =
      fibF M i (pushTA M U).2.2.1 (pushTA M U).2.2.2 := by
  simp only [fibPolyA, map_add, map_mul, map_prod, map_sum, eval_C, eval_XI, eval_XT]
  simp only [fibF, pushTA_apply, Pi.add_apply, Matrix.mulVec, dotProduct]
  have hj : ∀ j, thI B U.2.2.1 j * ∏ l ∈ univ.erase j, thI B U.2.2.1 l = ∏ k, thI B U.2.2.1 k :=
    fun j => mul_prod_erase univ _ (mem_univ j)
  have e : ∀ j, M i j * ((thI B U.2.2.1 j * U.2.2.2 j + (B j).T (U.2.2.1 j) 0 (B j).t₀) *
      ∏ l ∈ univ.erase j, thI B U.2.2.1 l) = M i j * U.2.2.2 j * ∏ k, thI B U.2.2.1 k +
        M i j * ((B j).T (U.2.2.1 j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B U.2.2.1 l) := by
    intro j; rw [← hj j]; ring
  rw [eval_X, sum_congr rfl fun j _ => e j, sum_add_distrib, ← sum_mul]
  change U.1 (Fin.natAdd d₀ i) * _ + _ = _
  ring

theorem eval_monoPolyA (M : Matrix (Fin r) (Fin m) ℂ) {D F : ℕ} (ν : MonoAV d₀ d₁ r B D F)
    (U : LSG.MEBV.Tan (d₀ + r) d₁ B) : eval (liftV U) (monoPolyA M ν) = ν.eval M (pushTA M U) := by
  simp only [monoPolyA, MonoAV.eval, MonoA.eval, map_mul, map_prod, map_pow, eval_X, eval_fibPolyA, eval_XI]
  rfl

theorem eval_PpolyAV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (U : LSG.MEBV.Tan (d₀ + r) d₁ B) :
    eval (liftV U) (PpolyAV M νs p) = PsiAV M νs p (pushTA M U) := by
  simp only [PpolyAV, PsiAV, map_sum, map_mul, eval_C, eval_monoPolyA]

theorem eval_WprodA (U : LSG.MEBV.Tan (d₀ + r) d₁ B) :
    eval (liftV U) (WprodA (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) = ∏ k, thI B U.2.2.1 k := by
  simp only [WprodA, map_prod, eval_XI]

theorem eval_PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (U : LSG.MEBV.Tan (d₀ + r) d₁ B) :
    eval (liftV U) (PWV M νs p) = PsiAV M νs p (pushTA M U) * ∏ k, thI B U.2.2.1 k := by
  rw [PWV, map_mul, eval_PpolyAV, eval_WprodA]

/-- **`K_M`-invariance.** -/
theorem invarKV_PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) : InvarKV M (PWV M νs p) := by
  intro U v
  rw [eval_PWV, eval_PWV, map_add, pushTA_kvec, add_zero]
  change _ * ∏ k, thI B (U.2.2.1 + 0) k = _
  rw [add_zero]

theorem PWV_notMem_IGsem (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) {x : TanAV d₀ d₁ r B} (hx : PsiAV M νs p x ≠ 0) (hθ : ∀ k, thI B x.2.2.1 k ≠ 0) :
    PWV M νs p ∉ IGsem (d₀ + r) d₁ B := by
  refine notMem_IGsem_of_eval_ne (u := liftTA x) ?_
  rw [eval_PWV, pushTA_liftTA]
  exact mul_ne_zero hx (prod_ne_zero_iff.mpr fun k _ => hθ k)

/-- Leibniz: a product vanishes to the order of a factor. -/
theorem iteratedDeriv_mul_eq_zeroAV {u f : ℂ → ℂ} (hu : Differentiable ℂ u) (hf : Differentiable ℂ f)
    {n : ℕ} (h : ∀ j ≤ n, iteratedDeriv j f 0 = 0) : ∀ j ≤ n, iteratedDeriv j (fun s => f s * u s) 0 = 0 := by
  intro j hj
  change iteratedDeriv j (f * u) 0 = 0
  rw [iteratedDeriv_mul (hf.analyticAt 0).contDiffAt (hu.analyticAt 0).contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h i (le_trans (Finset.mem_range_succ_iff.mp hi) hj), mul_zero, zero_mul]

/-- **The analytic order at `exp(liftTA x)` along `W.map liftTA`.** -/
theorem ordGtV_PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (W : Submodule ℂ (TanAV d₀ d₁ r B)) {n : ℕ} (x : TanAV d₀ d₁ r B)
    (h : ∀ w ∈ W, ∀ k ≤ n, iteratedDeriv k (fun s : ℂ => PsiAV M νs p (x + s • w)) 0 = 0) :
    OrdGtV (W.map liftTA) (PWV M νs p) n (expG (d₀ + r) d₁ B (liftTA x)) := by
  refine ⟨liftTA x, rfl, fun w' hw' k hk => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hw'
  have e : (fun s : ℂ => eval (liftV (liftTA x + s • liftTA w)) (PWV M νs p)) =
      fun s => PsiAV M νs p (x + s • w) * ∏ k, thI B (x + s • w).2.2.1 k := by
    funext s
    rw [eval_PWV, ← map_smul, ← map_add, pushTA_liftTA]
    rfl
  have hline : Differentiable ℂ fun s : ℂ => x + s • w :=
    (differentiable_const _).add (differentiable_id.smul_const w)
  have hθ : Differentiable ℂ fun s : ℂ => ∏ k, thI B (x + s • w).2.2.1 k :=
    (differentiable_fprodA _ _ fun l _ => differentiable_thI l).comp
      ((by fun_prop : Differentiable ℂ fun u : TanAV d₀ d₁ r B => u.2.2.1).comp hline)
  rw [e]
  exact iteratedDeriv_mul_eq_zeroAV hθ
    (((contDiff_PsiAV M νs p).differentiable (by simp)).comp hline) (h w hw) k hk

end LSG.W88
