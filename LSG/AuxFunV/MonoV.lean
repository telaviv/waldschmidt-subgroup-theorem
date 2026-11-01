/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.ExpCoordsN
import LSG.W88.StatementVec

/-!
# Monomials in the coordinates of `exp_G` for the class `𝒞` (concrete (QP) and growth)

`G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of `(E₁ × ⋯ × E_m)^♮` along `M : ℂ^m → ℂ^r`;
tangent space `TanV d0 d1 m r ∋ (a, b, z, s)` (`LSG/W88/StatementVec.lean`), `s = M w`.

**Fibre forms.** On `G₂` the functions of fibre degree one used here are the `ker M`-invariant
forms `S_i = Σ_j M_ij T₁^{(j)} Π_{l≠j} W_l` (all-`W` choice; `VECEXT.md` §3.2), i.e. analytically
`fibF i (z, s) = s_i Π_l σ_l³(z_l) − Σ_j M_ij σ_j²σ_j'(z_j) Π_{l≠j} σ_l³(z_l)`
`= Π_l σ_l³ · (s_i − (M ζ(z))_i)` off the lattices. It depends on `s = M w` only, is entire, of
degree one in every elliptic block, and **quasi-periodic with the same multiplier as `ellW`**
under the periods `(λ, M η(λ))` (`fibF_add_per`; `ζ(z + λ) = ζ(z) + η(λ)` via `zetaS_add`).

**Monomials** (`MonoV D`): `Π a^α Π e^{bβ} Π_j Π_t W_{j,t}^{γ_{j,t}} Π_i S_i^{φ_i}` with
`Σ_t γ_{j,t} + Σ_i φ_i = D` for every block `j` and `Σ φ ≤ D`.

* `piT`: the projection `T_G → T_{G/fibre} = Tan d0 d1 m` (forgets `s`); `piT_mem_per`,
  `ker_piT`, `norm_piT_le`.
* **`MonoV.eval_add_per`**: `M(p + ω) = expMult(πω, πp) · M(p)` for `ω ∈ Ω(G) = PerV Ls M` —
  the multiplier of the abelian case (`LSG.Aux.expMult`) evaluated on the base.
* **`exists_qp_monoV`**: (QP) in the form of `prop21Lat` for `ψ_l = M_l ∘ ℓ`, `ℓ ω_i ∈ Ω(G)`.
* **`exists_monoV_growth`**, **`exists_sum_monoV_le_exp`**: order two in `(a, b, z)`, polynomial
  in `s`: `|M(p)| ≤ (1+|p|)^{D₀+D} e^{D₁|p|} K^D e^{m D c (1+|p|)²}`.
-/

open Complex Finset LSG.Weierstrass LSG.W88 LSG.W88.Vec PeriodPair
open LSG.Aux (ellW sigmaMult ellW_add differentiable_ellW expMult norm_expMult_le
  exists_eta_bound differentiable_fprod growthLE_ellW)

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r : ℕ}

/-! ### The projection to `T_{G/fibre}` -/

/-- `(a, b, z, s) ↦ (a, b, z)`. -/
def piTL : TanV d0 d1 m r →ₗ[ℂ] Tan d0 d1 m :=
  (LinearMap.fst ℂ _ _).prod (((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)).prod
    ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))))

/-- `piTL` as a continuous linear map. -/
def piT : TanV d0 d1 m r →L[ℂ] Tan d0 d1 m := LinearMap.toContinuousLinearMap piTL

@[simp] lemma piT_apply (p : TanV d0 d1 m r) : piT p = (p.1, p.2.1, p.2.2.1) := rfl

lemma norm_piT_le (p : TanV d0 d1 m r) : ‖piT p‖ ≤ ‖p‖ := by
  rw [piT_apply]
  refine norm_prod_le_iff.mpr ⟨norm_fst_le p, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · exact (norm_fst_le p.2).trans (norm_snd_le p)
  · exact (norm_fst_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p))

lemma piT_mem_per (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {ω : TanV d0 d1 m r}
    (hω : ω ∈ PerV Ls M) : piT ω ∈ Per Ls :=
  ⟨hω.1, hω.2.1, hω.2.2.1⟩

/-- The kernel of the projection is the fibre. -/
lemma mem_fibreV_of_piT_eq_zero {v : TanV d0 d1 m r} (h : piT v = 0) : v ∈ fibreV := by
  rw [piT_apply] at h
  obtain ⟨a, b, z, s⟩ := v
  simp only [Prod.mk_eq_zero] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨s, rfl⟩

/-- Under `V ∩ fibre = 0` the projection is injective on `V`. -/
lemma piT_injOn {V : Submodule ℂ (TanV d0 d1 m r)} (hV : V ⊓ fibreV = ⊥) {u v : TanV d0 d1 m r}
    (hu : u ∈ V) (hv : v ∈ V) (h : piT u = piT v) : u = v := by
  have h0 : piT (u - v) = 0 := by rw [map_sub, h, sub_self]
  have hmem : u - v ∈ V ⊓ fibreV := ⟨V.sub_mem hu hv, mem_fibreV_of_piT_eq_zero h0⟩
  rw [hV] at hmem
  exact sub_eq_zero.mp hmem

/-! ### Fibre forms -/

/-- **The fibre form** `S_i = s_i Π_l σ_l³ − Σ_j M_ij σ_j²σ_j' Π_{l≠j} σ_l³` (entire). -/
def fibF (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (z : Fin m → ℂ)
    (s : Fin r → ℂ) : ℂ :=
  s i * ∏ l, ellW (Ls l) 0 (z l) -
    ∑ j, M i j * (zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l))

/-- Off the lattices `S_i = Π_l σ_l³ · (s_i − (M ζ(z))_i)`. -/
lemma fibF_eq_off (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r)
    {z : Fin m → ℂ} (hz : ∀ j, z j ∉ (Ls j).lattice) (s : Fin r → ℂ) :
    fibF Ls M i z s = (∏ l, ellW (Ls l) 0 (z l)) * (s i - (M.mulVec (zetaV Ls z)) i) := by
  unfold fibF
  have hj : ∀ j, zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l) =
      zeta (Ls j) (z j) * ∏ l, ellW (Ls l) 0 (z l) := by
    intro j
    rw [zetaS_eq_off _ (hz j), ← mul_prod_erase univ (fun l => ellW (Ls l) 0 (z l)) (mem_univ j)]
    simp only [ellW, Matrix.cons_val_zero]
    ring
  simp only [hj, Matrix.mulVec, dotProduct, zetaV, mul_sub, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun j _ => by ring

/-- **Quasi-periodicity of the fibre forms** under the periods `(λ, M η(λ))` of `G₂`. -/
theorem fibF_add_per (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r)
    {lam : Fin m → ℂ} (hlam : ∀ j, lam j ∈ (Ls j).lattice) (z : Fin m → ℂ) (s : Fin r → ℂ) :
    fibF Ls M i (z + lam) (s + M.mulVec (etaV Ls lam)) =
      (∏ j, sigmaMult (Ls j) (lam j) (z j) ^ 3) * fibF Ls M i z s := by
  set mu : Fin m → ℂ := fun j => sigmaMult (Ls j) (lam j) (z j) ^ 3
  set Wz : Fin m → ℂ := fun l => ellW (Ls l) 0 (z l)
  have hW : ∀ l, ellW (Ls l) 0 (z l + lam l) = mu l * Wz l := fun l => ellW_add _ (hlam l) 0 _
  have hZ : ∀ j, zetaS (Ls j) (z j + lam j) =
      mu j * (zetaS (Ls j) (z j) + eta (Ls j) (lam j) * Wz j) := fun j => zetaS_add _ (hlam j) _
  have hP : ∏ l, ellW (Ls l) 0 (z l + lam l) = (∏ l, mu l) * ∏ l, Wz l := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun l _ => hW l
  have hPe : ∀ j, mu j * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l + lam l) =
      (∏ l, mu l) * ∏ l ∈ univ.erase j, Wz l := by
    intro j
    rw [prod_congr rfl fun l _ => hW l, prod_mul_distrib, ← mul_assoc,
      mul_prod_erase univ mu (mem_univ j)]
  have hWe : ∀ j, Wz j * ∏ l ∈ univ.erase j, Wz l = ∏ l, Wz l := fun j =>
    mul_prod_erase univ Wz (mem_univ j)
  have hterm : ∀ j, M i j * (zetaS (Ls j) (z j + lam j) *
      ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l + lam l)) =
      (∏ l, mu l) * (M i j * (zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, Wz l)) +
        (∏ l, mu l) * (M i j * eta (Ls j) (lam j)) * ∏ l, Wz l := by
    intro j
    rw [hZ j, ← hWe j]
    linear_combination (M i j * (zetaS (Ls j) (z j) + eta (Ls j) (lam j) * Wz j)) * hPe j
  unfold fibF
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, etaV]
  rw [hP, sum_congr rfl fun j _ => hterm j, sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
  ring

lemma differentiable_fibF (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    Differentiable ℂ (fun p : TanV d0 d1 m r => fibF Ls M i p.2.2.1 p.2.2.2) := by
  have hz : ∀ l, Differentiable ℂ (fun p : TanV d0 d1 m r => p.2.2.1 l) := fun l => by fun_prop
  have hW : ∀ l, Differentiable ℂ (fun p : TanV d0 d1 m r => ellW (Ls l) 0 (p.2.2.1 l)) :=
    fun l => (differentiable_ellW (Ls l) 0).comp (hz l)
  unfold fibF
  refine Differentiable.sub ?_ ?_
  · exact (by fun_prop : Differentiable ℂ (fun p : TanV d0 d1 m r => p.2.2.2 i)).mul
      (differentiable_fprod _ _ fun l _ => hW l)
  · refine Differentiable.fun_sum fun j _ => ?_
    exact (differentiable_const _).mul (((differentiable_zetaS (Ls j)).comp (hz j)).mul
      (differentiable_fprod _ _ fun l _ => hW l))

/-! ### Monomials -/

/-- A monomial in the coordinates of `exp_G` for the class `𝒞`, of degree `D` in each elliptic
block (counting the fibre forms, which have degree one in every block). -/
structure MonoV (d0 d1 m r D : ℕ) where
  /-- exponents of the `G_a` coordinates -/
  α : Fin d0 → ℕ
  /-- exponents of the `G_m` coordinates -/
  β : Fin d1 → ℕ
  /-- exponents of the elliptic coordinates `W_{j,0}, W_{j,1}, W_{j,2}` -/
  γ : Fin m → Fin 3 → ℕ
  /-- exponents of the fibre forms -/
  φ : Fin r → ℕ
  hγ : ∀ j, ∑ t, γ j t + ∑ i, φ i = D
  hφ : ∑ i, φ i ≤ D

variable {D : ℕ}

/-- Evaluation of a monomial on `T_G`. -/
def MonoV.eval (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (μ : MonoV d0 d1 m r D) (p : TanV d0 d1 m r) : ℂ :=
  (∏ i, p.1 i ^ μ.α i) * (∏ i, exp (p.2.1 i) ^ μ.β i) *
    (∏ j, ∏ t, ellW (Ls j) t (p.2.2.1 j) ^ μ.γ j t) * ∏ i, fibF Ls M i p.2.2.1 p.2.2.2 ^ μ.φ i

lemma differentiable_evalV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (μ : MonoV d0 d1 m r D) : Differentiable ℂ (μ.eval Ls M) := by
  unfold MonoV.eval
  refine ((Differentiable.mul ?_ ?_).mul ?_).mul ?_
  · refine differentiable_fprod _ _ fun i _ => ?_
    fun_prop
  · refine differentiable_fprod _ _ fun i _ => ?_
    fun_prop
  · refine differentiable_fprod _ _ fun j _ => ?_
    refine differentiable_fprod _ _ fun t _ => ?_
    exact ((differentiable_ellW (Ls j) t).comp
      (by fun_prop : Differentiable ℂ fun p : TanV d0 d1 m r => p.2.2.1 j)).pow _
  · exact differentiable_fprod _ _ fun i _ => (differentiable_fibF Ls M i).pow _

/-- **Common multiplier under the periods of `G`** (the multiplier of the abelian case on the
base `πω`, `πp`). -/
theorem MonoV.eval_add_per (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (μ : MonoV d0 d1 m r D) {ω : TanV d0 d1 m r} (hω : ω ∈ PerV Ls M) (p : TanV d0 d1 m r) :
    μ.eval Ls M (p + ω) = expMult Ls D (piT ω) (piT p) * μ.eval Ls M p := by
  obtain ⟨h0, h1, h2, h3⟩ := hω
  set mu : Fin m → ℂ := fun j => sigmaMult (Ls j) (ω.2.2.1 j) (p.2.2.1 j)
  unfold MonoV.eval
  have hA : ∏ i, (p + ω).1 i ^ μ.α i = ∏ i, p.1 i ^ μ.α i := by simp [h0]
  have hB : ∏ i, exp ((p + ω).2.1 i) ^ μ.β i = ∏ i, exp (p.2.1 i) ^ μ.β i := by
    refine prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := h1 i
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hk, Complex.exp_add]
    rw [show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hC : ∏ j, ∏ t, ellW (Ls j) t ((p + ω).2.2.1 j) ^ μ.γ j t =
      (∏ j, mu j ^ (3 * ∑ t, μ.γ j t)) * ∏ j, ∏ t, ellW (Ls j) t (p.2.2.1 j) ^ μ.γ j t := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, ellW_add (Ls j) (h2 j), mul_pow,
      prod_mul_distrib, ← pow_mul, prod_pow_eq_pow_sum, ← mul_sum, mu]
  have hF : ∏ i, fibF Ls M i ((p + ω).2.2.1) ((p + ω).2.2.2) ^ μ.φ i =
      (∏ j, mu j ^ (3 * ∑ i, μ.φ i)) * ∏ i, fibF Ls M i p.2.2.1 p.2.2.2 ^ μ.φ i := by
    simp only [Prod.snd_add, Prod.fst_add, h3, fibF_add_per Ls M _ h2, mul_pow, prod_mul_distrib,
      prod_pow_eq_pow_sum]
    congr 1
    rw [← prod_pow]
    exact prod_congr rfl fun j _ => by rw [pow_mul]
  have hM : expMult Ls D (piT ω) (piT p) =
      (∏ j, mu j ^ (3 * ∑ t, μ.γ j t)) * ∏ j, mu j ^ (3 * ∑ i, μ.φ i) := by
    unfold expMult
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_add, ← mul_add, μ.hγ j]
    rfl
  rw [hA, hB, hC, hF, hM]; ring

/-- **Concrete (QP) for the class `𝒞`.** For `ℓ : ℂⁿ → T_G` linear and periods `ω_i` with
`ℓ ω_i ∈ Ω(G)`, the functions `ψ_l = M_l ∘ ℓ` have a common multiplier under `Σ k_i ω_i`,
bounded by `exp (3 D C ‖ℓ‖² (‖z‖ + ‖Σ k_i ω_i‖)²)`, `C` depending only on the lattices. -/
theorem exists_qp_monoV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D n κ L : ℕ) (ℓ : (Fin n → ℂ) →L[ℂ] TanV d0 d1 m r)
      (ω : Fin κ → (Fin n → ℂ)), (∀ i, ℓ (ω i) ∈ PerV Ls M) →
      ∀ (μs : Fin L → MonoV d0 d1 m r D),
      ∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ mu : ℂ,
        ‖mu‖ ≤ Real.exp (3 * D * C * ‖ℓ‖ ^ 2 * (‖z‖ + ‖∑ i, (k i : ℂ) • ω i‖) ^ 2) ∧
        ∀ l, (μs l).eval Ls M (ℓ (z + ∑ i, (k i : ℂ) • ω i)) = mu * (μs l).eval Ls M (ℓ z) := by
  choose C hC0 hC using fun j => exists_eta_bound (Ls j)
  refine ⟨∑ j, C j, sum_nonneg fun j _ => hC0 j, fun D n κ L ℓ ω hω μs k z => ?_⟩
  set w : Fin n → ℂ := ∑ i, (k i : ℂ) • ω i
  have hw : ℓ w ∈ PerV Ls M := by
    simp only [w, map_sum, map_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have : (k i : ℂ) • ℓ (ω i) = (k i) • ℓ (ω i) := by
      rw [← Int.cast_smul_eq_zsmul ℂ]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (hω i) _
  refine ⟨expMult Ls D (piT (ℓ w)) (piT (ℓ z)), ?_, fun l => ?_⟩
  · refine (norm_expMult_le Ls hC0 hC (piT_mem_per Ls M hw) _).trans (Real.exp_le_exp.mpr ?_)
    have h1 : ‖piT (ℓ z)‖ + ‖piT (ℓ w)‖ ≤ ‖ℓ‖ * (‖z‖ + ‖w‖) := by
      rw [mul_add]
      exact add_le_add ((norm_piT_le _).trans (ℓ.le_opNorm z))
        ((norm_piT_le _).trans (ℓ.le_opNorm w))
    have h0 : 0 ≤ ‖piT (ℓ z)‖ + ‖piT (ℓ w)‖ := by positivity
    have hS : 0 ≤ 3 * (D : ℝ) * ∑ j, C j := by
      have := sum_nonneg fun j (_ : j ∈ univ) => hC0 j
      positivity
    calc 3 * D * (∑ j, C j) * (‖piT (ℓ z)‖ + ‖piT (ℓ w)‖) ^ 2
        ≤ 3 * D * (∑ j, C j) * (‖ℓ‖ * (‖z‖ + ‖w‖)) ^ 2 := by gcongr
      _ = 3 * D * (∑ j, C j) * ‖ℓ‖ ^ 2 * (‖z‖ + ‖w‖) ^ 2 := by ring
  · rw [map_add]
    exact (μs l).eval_add_per Ls M hw (ℓ z)

/-! ### Growth -/

/-- A common order-two constant for `σ³` and `σ²σ'` on all curves. -/
lemma exists_W0_zetaS_growth (Ls : Fin m → PeriodPair) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ j z, ‖ellW (Ls j) 0 z‖ ≤ Real.exp (c * (1 + ‖z‖) ^ 2) ∧
      ‖zetaS (Ls j) z‖ ≤ Real.exp (c * (1 + ‖z‖) ^ 2) := by
  choose a ha0 ha using fun j => growthLE_exists_nonneg (growthLE_ellW (Ls j) 0)
  choose b hb0 hb using fun j => growthLE_exists_nonneg (growthLE_zetaS (Ls j))
  refine ⟨∑ j, (a j + b j), sum_nonneg fun j _ => by linarith [ha0 j, hb0 j], fun j z => ?_⟩
  have hj : a j + b j ≤ ∑ j, (a j + b j) :=
    single_le_sum (f := fun j => a j + b j) (fun j _ => by linarith [ha0 j, hb0 j]) (mem_univ j)
  have hsq : 0 ≤ (1 + ‖z‖) ^ 2 := by positivity
  constructor
  · refine (ha j z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hsq))
    linarith [hb0 j]
  · refine (hb j z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hsq))
    linarith [ha0 j]

lemma prod_exp_le {m : ℕ} {c : ℝ} (hc : 0 ≤ c) (z : Fin m → ℂ) (x : ℝ) (hx : ‖z‖ ≤ x)
    (u : Finset (Fin m)) (f : Fin m → ℂ)
    (hf : ∀ l, ‖f l‖ ≤ Real.exp (c * (1 + ‖z l‖) ^ 2)) :
    ‖∏ l ∈ u, f l‖ ≤ Real.exp (c * (1 + x) ^ 2) ^ u.card := by
  rw [norm_prod, ← prod_const]
  refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => (hf l).trans ?_
  have : ‖z l‖ ≤ x := (norm_le_pi_norm z l).trans hx
  gcongr

/-- **Growth of the fibre forms**: `|S_i(z, s)| ≤ K (1 + |s|) e^{m c (1+|z|)²}`. -/
theorem exists_fibF_growth (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    ∃ c K : ℝ, 0 ≤ c ∧ 1 ≤ K ∧ (∀ j z, ‖ellW (Ls j) 0 z‖ ≤ Real.exp (c * (1 + ‖z‖) ^ 2)) ∧
      ∀ i (z : Fin m → ℂ) (s : Fin r → ℂ) (x : ℝ), ‖z‖ ≤ x → ‖s‖ ≤ x →
        ‖fibF Ls M i z s‖ ≤ K * (1 + x) * Real.exp (c * (1 + x) ^ 2) ^ m := by
  obtain ⟨c, hc0, hc⟩ := exists_W0_zetaS_growth Ls
  set K : ℝ := 1 + ∑ i, ∑ j, ‖M i j‖
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := sum_nonneg fun i _ => sum_nonneg fun j _ => norm_nonneg _
    linarith
  refine ⟨c, K, hc0, hK1, fun j z => (hc j z).1, fun i z s x hz hs => ?_⟩
  have hx0 : 0 ≤ x := (norm_nonneg _).trans hz
  set E : ℝ := Real.exp (c * (1 + x) ^ 2)
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hP : ‖∏ l, ellW (Ls l) 0 (z l)‖ ≤ E ^ m := by
    simpa using prod_exp_le hc0 z x hz univ _ fun l => (hc l (z l)).1
  have hPe : ∀ j, ‖zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l)‖ ≤ E ^ m := by
    intro j
    have h1 : ‖zetaS (Ls j) (z j)‖ ≤ E :=
      (hc j (z j)).2.trans (Real.exp_le_exp.mpr (by
        have := (norm_le_pi_norm z j).trans hz
        gcongr))
    have h2 := prod_exp_le hc0 z x hz (univ.erase j) _ fun l => (hc l (z l)).1
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin] at h2
    have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => (h ▸ j).elim0
    rw [norm_mul]
    calc ‖zetaS (Ls j) (z j)‖ * ‖∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l)‖
        ≤ E * E ^ (m - 1) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = E ^ m := by rw [← pow_succ', Nat.sub_add_cancel hm]
  have hsi : ‖s i‖ ≤ x := (norm_le_pi_norm s i).trans hs
  have hMi : ∑ j, ‖M i j‖ ≤ ∑ i, ∑ j, ‖M i j‖ :=
    single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun i _ => sum_nonneg fun j _ => norm_nonneg _)
      (mem_univ i)
  unfold fibF
  calc ‖s i * ∏ l, ellW (Ls l) 0 (z l) -
        ∑ j, M i j * (zetaS (Ls j) (z j) * ∏ l ∈ univ.erase j, ellW (Ls l) 0 (z l))‖
      ≤ ‖s i‖ * E ^ m + ∑ j, ‖M i j‖ * E ^ m := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hPe j) (norm_nonneg _)
    _ = (‖s i‖ + ∑ j, ‖M i j‖) * E ^ m := by rw [add_mul, sum_mul]
    _ ≤ K * (1 + x) * E ^ m := by
        gcongr
        nlinarith [sum_nonneg fun i (_ : i ∈ univ) => sum_nonneg fun j (_ : j ∈ univ) =>
          norm_nonneg (M i j)]

/-- **Growth of a monomial of the class `𝒞`.** -/
theorem exists_monoV_growth (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    ∃ c K : ℝ, 0 ≤ c ∧ 1 ≤ K ∧ ∀ (D D₀ D₁ : ℕ) (μ : MonoV d0 d1 m r D), ∑ i, μ.α i ≤ D₀ →
      ∑ i, μ.β i ≤ D₁ → ∀ p : TanV d0 d1 m r,
      ‖μ.eval Ls M p‖ ≤ (1 + ‖p‖) ^ (D₀ + D) * Real.exp (D₁ * ‖p‖) * K ^ D *
        Real.exp (m * D * c * (1 + ‖p‖) ^ 2) := by
  obtain ⟨cF, K, hcF0, hK1, -, hF⟩ := exists_fibF_growth Ls M
  choose ce hce0 hceG using fun j => LSG.Aux.exists_ellW_growth (Ls j)
  set c : ℝ := cF + ∑ j, ce j
  have hce : ∀ j, ce j ≤ c := fun j => by
    have := single_le_sum (f := ce) (fun j _ => hce0 j) (mem_univ j); simp only [c]; linarith
  have hc0 : 0 ≤ c := by
    have := sum_nonneg fun j (_ : j ∈ univ) => hce0 j; simp only [c]; linarith
  refine ⟨c, K, hc0, hK1, fun D D₀ D₁ μ hα hβ p => ?_⟩
  set x := ‖p‖
  have hx0 : 0 ≤ x := norm_nonneg p
  have hp1 : 1 ≤ 1 + x := by linarith
  set E : ℝ := Real.exp (c * (1 + x) ^ 2)
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hpa : ∀ i, ‖p.1 i‖ ≤ 1 + x := fun i => by
    have := (norm_le_pi_norm p.1 i).trans (norm_fst_le p); linarith
  have hpb : ∀ i, ‖p.2.1 i‖ ≤ x := fun i =>
    (norm_le_pi_norm p.2.1 i).trans ((norm_fst_le p.2).trans (norm_snd_le p))
  have hpz : ‖p.2.2.1‖ ≤ x := (norm_fst_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p))
  have hps : ‖p.2.2.2‖ ≤ x := (norm_snd_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p))
  have hA : ‖∏ i, p.1 i ^ μ.α i‖ ≤ (1 + x) ^ D₀ := by
    rw [norm_prod]
    calc ∏ i, ‖p.1 i ^ μ.α i‖ ≤ ∏ i, (1 + x) ^ μ.α i := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]; gcongr; exact hpa i
      _ = (1 + x) ^ (∑ i, μ.α i) := prod_pow_eq_pow_sum _ _ _
      _ ≤ (1 + x) ^ D₀ := pow_le_pow_right₀ hp1 hα
  have hB : ‖∏ i, exp (p.2.1 i) ^ μ.β i‖ ≤ Real.exp (D₁ * x) := by
    rw [norm_prod]
    calc ∏ i, ‖exp (p.2.1 i) ^ μ.β i‖ ≤ ∏ i, Real.exp x ^ μ.β i := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]; gcongr
          exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hpb i))
      _ = Real.exp x ^ (∑ i, μ.β i) := prod_pow_eq_pow_sum _ _ _
      _ ≤ Real.exp x ^ D₁ := pow_le_pow_right₀ (Real.one_le_exp hx0) hβ
      _ = Real.exp (D₁ * x) := by rw [← Real.exp_nat_mul]
  have hC : ‖∏ j, ∏ t, ellW (Ls j) t (p.2.2.1 j) ^ μ.γ j t‖ ≤ ∏ j, E ^ (∑ t, μ.γ j t) := by
    rw [norm_prod]
    refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [norm_prod, ← prod_pow_eq_pow_sum]
    refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun t _ => ?_
    rw [norm_pow]
    gcongr
    refine (hceG j t _).trans (Real.exp_le_exp.mpr ?_)
    have : (1 + ‖p.2.2.1 j‖) ^ 2 ≤ (1 + x) ^ 2 := by
      gcongr; exact (norm_le_pi_norm _ j).trans hpz
    exact mul_le_mul (hce j) this (by positivity) hc0
  have hFi : ∀ i, ‖fibF Ls M i p.2.2.1 p.2.2.2‖ ≤ K * (1 + x) * E ^ m := by
    intro i
    have hcF : cF ≤ c := by
      have := sum_nonneg fun j (_ : j ∈ univ) => hce0 j
      simp only [c]; linarith
    have hEF : Real.exp (cF * (1 + x) ^ 2) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcF (by positivity))
    refine (hF i _ _ x hpz hps).trans ?_
    gcongr
  have hFp : ‖∏ i, fibF Ls M i p.2.2.1 p.2.2.2 ^ μ.φ i‖ ≤
      (K * (1 + x)) ^ (∑ i, μ.φ i) * ∏ _j : Fin m, E ^ (∑ i, μ.φ i) := by
    rw [norm_prod, prod_const, card_univ, Fintype.card_fin, ← pow_mul]
    calc ∏ i, ‖fibF Ls M i p.2.2.1 p.2.2.2 ^ μ.φ i‖ ≤ ∏ i, (K * (1 + x) * E ^ m) ^ μ.φ i := by
          refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
          rw [norm_pow]; gcongr; exact hFi i
      _ = _ := by rw [prod_pow_eq_pow_sum, mul_pow, ← pow_mul, mul_comm m]
  have hEm : (∏ j, E ^ (∑ t, μ.γ j t)) * ∏ _j : Fin m, E ^ (∑ i, μ.φ i) =
      Real.exp (m * D * c * (1 + x) ^ 2) := by
    rw [← prod_mul_distrib]
    have hj : ∀ j, E ^ (∑ t, μ.γ j t) * E ^ (∑ i, μ.φ i) = E ^ D := fun j => by
      rw [← pow_add, μ.hγ j]
    rw [prod_congr rfl fun j _ => hj j, prod_const, card_univ, Fintype.card_fin, ← pow_mul]
    simp only [E]
    rw [← Real.exp_nat_mul]
    push_cast; ring_nf
  have hKx : (K * (1 + x)) ^ (∑ i, μ.φ i) ≤ (1 + x) ^ D * K ^ D := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul (pow_le_pow_right₀ hp1 μ.hφ) (pow_le_pow_right₀ hK1 μ.hφ) (by positivity)
      (by positivity)
  unfold MonoV.eval
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖∏ i, p.1 i ^ μ.α i‖ * ‖∏ i, exp (p.2.1 i) ^ μ.β i‖ *
        ‖∏ j, ∏ t, ellW (Ls j) t (p.2.2.1 j) ^ μ.γ j t‖ * ‖∏ i, fibF Ls M i p.2.2.1 p.2.2.2 ^ μ.φ i‖
      ≤ (1 + x) ^ D₀ * Real.exp (D₁ * x) * (∏ j, E ^ (∑ t, μ.γ j t)) *
        ((K * (1 + x)) ^ (∑ i, μ.φ i) * ∏ _j : Fin m, E ^ (∑ i, μ.φ i)) := by
        gcongr
    _ = (1 + x) ^ D₀ * Real.exp (D₁ * x) * (K * (1 + x)) ^ (∑ i, μ.φ i) *
        ((∏ j, E ^ (∑ t, μ.γ j t)) * ∏ _j : Fin m, E ^ (∑ i, μ.φ i)) := by ring
    _ ≤ (1 + x) ^ D₀ * Real.exp (D₁ * x) * ((1 + x) ^ D * K ^ D) *
        Real.exp (m * D * c * (1 + x) ^ 2) := by rw [hEm]; gcongr
    _ = (1 + x) ^ (D₀ + D) * Real.exp (D₁ * x) * K ^ D * Real.exp (m * D * c * (1 + x) ^ 2) := by
        rw [pow_add]; ring

/-- **W83's growth hypothesis for a family of monomials of the class `𝒞`.** -/
theorem exists_sum_monoV_le_exp (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    ∃ c K : ℝ, 0 ≤ c ∧ 1 ≤ K ∧ ∀ (L D D₀ D₁ : ℕ) (μs : Fin L → MonoV d0 d1 m r D) (R U : ℝ),
      (∀ l, ∑ i, (μs l).α i ≤ D₀) → (∀ l, ∑ i, (μs l).β i ≤ D₁) → 0 ≤ R → 1 ≤ L →
      Real.log L + (D₀ + D) * Real.log (1 + R) + D * Real.log K + D₁ * R +
        m * D * c * (1 + R) ^ 2 ≤ U →
      ∀ p : TanV d0 d1 m r, ‖p‖ ≤ R → ∑ l, ‖(μs l).eval Ls M p‖ ≤ Real.exp U := by
  obtain ⟨c, K, hc0, hK1, hG⟩ := exists_monoV_growth (d0 := d0) (d1 := d1) Ls M
  refine ⟨c, K, hc0, hK1, fun L D D₀ D₁ μs R U hα hβ hR hL hU p hp => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hR1 : 0 < 1 + R := by linarith
  have hK0 : 0 < K := by linarith
  have hterm : ∀ l, ‖(μs l).eval Ls M p‖ ≤
      (1 + R) ^ (D₀ + D) * Real.exp (D₁ * R) * K ^ D * Real.exp (m * D * c * (1 + R) ^ 2) := by
    intro l
    refine (hG D D₀ D₁ (μs l) (hα l) (hβ l) p).trans ?_
    have h1 : 1 + ‖p‖ ≤ 1 + R := by linarith
    gcongr
  calc ∑ l, ‖(μs l).eval Ls M p‖
      ≤ ∑ _l : Fin L, (1 + R) ^ (D₀ + D) * Real.exp (D₁ * R) * K ^ D *
          Real.exp (m * D * c * (1 + R) ^ 2) := sum_le_sum fun l _ => hterm l
    _ = Real.exp (Real.log L + (D₀ + D) * Real.log (1 + R) + D * Real.log K + D₁ * R +
          m * D * c * (1 + R) ^ 2) := by
        have e1 : Real.exp ((D₀ + D) * Real.log (1 + R)) = (1 + R) ^ (D₀ + D) := by
          rw [show ((D₀ : ℝ) + D) = ((D₀ + D : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
            Real.exp_log hR1]
        have e2 : Real.exp (D * Real.log K) = K ^ D := by
          rw [Real.exp_nat_mul, Real.exp_log hK0]
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.exp_add, Real.exp_add,
          Real.exp_add, Real.exp_add, Real.exp_log hL0, e1, e2]
        ring
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hU

end LSG.AuxV
