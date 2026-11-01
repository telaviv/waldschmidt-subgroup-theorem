/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.Taylor
import LSG.AuxFunA.Mono

/-!
# M2.6.3: the monomials of the auxiliary function on `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`

`B : Fin m → VBlock`, `M : ℂ^m → ℂ^r`. The tangent space of `G` is
**`TanAV d₀ d₁ r B = ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k} × ℂ^r ∋ (a, b, z, s)`**, `s = M w` (`w` the fibre coordinates of
`∏ B_k^♮`); `piA` forgets `s` and lands in MEB's `Tan d₀ d₁ (Bb B)` of the base blocks.

**Fibre forms** (MEV's "all-`W`" choice, with `θ_{i₀}` for `W`):
`fibF i (z, s) = s_i Π_k θ_{k,i₀}(z_k) + Σ_j M_ij T_{j,t₀}(z_j, 0) Π_{l≠j} θ_{l,i₀}(z_l)`. This is the value of the
`K_M`-invariant cone form `x_{d₀+i} Π_k X_{k,i₀} + Σ_j M_ij T_{j,t₀} Π_{l≠j} X_{l,i₀}` at the lift (`LSG/AuxFunAV/Poly`).
On `θ_{i₀} ≠ 0`: `fibF i = Π_k θ_{k,i₀} · (s_i + Σ_j M_ij τ_j(z_j))` (`fibF_eq`).

**Monomials** `MonoAV d₀ d₁ r B D F`: a monomial `μ` of MEB's abelian consumer (`MonoA`, block degree `D` in the free
coordinates of the bases) times `Π_k θ_{k,i₀}^{F − Σφ}` times `Π_i fibF_i^{φ_i}` (`Σ φ ≤ F`). Every monomial has block
degree `D + F`.

* `PerAVg B M Λ` (the periods `0 × 2πiℤ^{d₁} × {(λ, M η(λ)) : λ ∈ ∏ Λ_k}`), `PerAV An M` (counted, `Λ = lat`),
  `PerAVf B M` (full, `Λ = per`).
* **`fibF_add_per`**, **`MonoAV.eval_add_per`**, **`exists_qp_monoAV`**: a common multiplier `Π_k f_k^{D+F}` under the
  periods (from `AbBlockAn.qp` and `VBlockAn.T_qp`).
* `MonoAV.differentiable_eval`, **`sum_norm_evalAV_le`** (order-2 growth).
* **`exists_PsiAV_ne_zero`**: distinct exponent vectors and `p ≠ 0` give `PsiAV ≢ 0`.
-/

open Complex Finset Filter Topology

noncomputable section

namespace LSG.AuxAV

open LSG.MEBV LSG.AuxA
open LSG.MEB (AbBlock)

variable {m d₀ d₁ r : ℕ}

/-! ### Tangent space, base blocks, periods -/

/-- The base blocks. -/
abbrev Bb (B : Fin m → VBlock) : Fin m → AbBlock := fun k => (B k).base

variable (d₀ d₁ r) in
/-- **The tangent space** `ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k} × ℂ^r` of `G`. -/
abbrev TanAV (B : Fin m → VBlock) : Type :=
  (Fin d₀ → ℂ) × (Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ)

variable {B : Fin m → VBlock}

/-- `(a, b, z, s) ↦ (a, b, z)`. -/
def piAL : TanAV d₀ d₁ r B →ₗ[ℂ] LSG.MEB.Tan d₀ d₁ (Bb B) where
  toFun u := (u.1, u.2.1, u.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `piAL` as a continuous linear map. -/
def piA : TanAV d₀ d₁ r B →L[ℂ] LSG.MEB.Tan d₀ d₁ (Bb B) := LinearMap.toContinuousLinearMap piAL

@[simp] lemma piA_apply (u : TanAV d₀ d₁ r B) : piA u = (u.1, u.2.1, u.2.2.1) := rfl

lemma norm_piA_le (u : TanAV d₀ d₁ r B) : ‖piA u‖ ≤ ‖u‖ := by
  rw [piA_apply]
  refine norm_prod_le_iff.mpr ⟨norm_fst_le u, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · exact (norm_fst_le u.2).trans (norm_snd_le u)
  · exact (norm_fst_le u.2.2).trans ((norm_snd_le u.2).trans (norm_snd_le u))

lemma norm_zV_le (u : TanAV d₀ d₁ r B) (k : Fin m) : ‖u.2.2.1 k‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.2.2.1 k).trans ((norm_fst_le u.2.2).trans ((norm_snd_le u.2).trans (norm_snd_le u)))

lemma norm_sV_le (u : TanAV d₀ d₁ r B) (i : Fin r) : ‖u.2.2.2 i‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.2.2.2 i).trans ((norm_snd_le u.2.2).trans ((norm_snd_le u.2).trans (norm_snd_le u)))

variable (B) in
/-- `η` blockwise: `etaB B z k = (B k).η (z k)`.

Name clash (cosmetic): `LSG.JacAn.ThetaData.etaB` (`LSG/JacAnV/Fibre.lean`) is the fibre period `η̄` of one
`A^♮` block; for the instance `(aBlockV).η = stdPkg.D.etaB`, so this `LSG.AuxAV.etaB` is that map applied in each
block. The two are different declarations in different namespaces. -/
def etaB (z : ∀ k, Fin (B k).g → ℂ) : Fin m → ℂ := fun k => (B k).η (z k)

variable (d₀ d₁ B) in
/-- **The periods** `0 × 2πiℤ^{d₁} × {(λ, M η(λ)) : λ ∈ ∏ Λ_k}` (for `Λ_k ≤ per_k`). -/
def PerAVg (M : Matrix (Fin r) (Fin m) ℂ) (Λ : ∀ k, AddSubgroup (Fin (B k).g → ℂ))
    (hΛ : ∀ k, Λ k ≤ (B k).base.per) : AddSubgroup (TanAV d₀ d₁ r B) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * Complex.I * k) ∧
    (∀ k, p.2.2.1 k ∈ Λ k) ∧ p.2.2.2 = M.mulVec (etaB B p.2.2.1)}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun k => (Λ k).add_mem (hp.2.2.1 k) (hq.2.2.1 k), ?_⟩
    · obtain ⟨a, ha⟩ := hp.2.1 i
      obtain ⟨b, hb⟩ := hq.2.1 i
      exact ⟨a + b, by change p.2.1 i + q.2.1 i = _; rw [ha, hb]; push_cast; ring⟩
    · have he : etaB B (p.2.2.1 + q.2.2.1) = etaB B p.2.2.1 + etaB B q.2.2.1 := funext fun k =>
        (B k).η_add (hΛ k (hp.2.2.1 k)) (hΛ k (hq.2.2.1 k))
      change p.2.2.2 + q.2.2.2 = M.mulVec (etaB B (p.2.2.1 + q.2.2.1))
      rw [he, Matrix.mulVec_add, ← hp.2.2.2, ← hq.2.2.2]
  zero_mem' := by
    refine ⟨rfl, fun _ => ⟨0, by simp⟩, fun k => (Λ k).zero_mem, ?_⟩
    have he : etaB B (0 : ∀ k, Fin (B k).g → ℂ) = 0 := funext fun k => (B k).η_zero
    change (0 : Fin r → ℂ) = M.mulVec (etaB B 0)
    rw [he, Matrix.mulVec_zero]
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun k => (Λ k).neg_mem (hp.2.2.1 k), ?_⟩
    · obtain ⟨a, ha⟩ := hp.2.1 i
      exact ⟨-a, by change -p.2.1 i = _; rw [ha]; push_cast; ring⟩
    · have he : etaB B (-p.2.2.1) = -etaB B p.2.2.1 := funext fun k => (B k).η_neg (hΛ k (hp.2.2.1 k))
      change -p.2.2.2 = M.mulVec (etaB B (-p.2.2.1))
      rw [he, Matrix.mulVec_neg, ← hp.2.2.2]

variable (d₀ d₁) in
/-- **The counted periods** (`Λ = lat`). -/
def PerAV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : AddSubgroup (TanAV d₀ d₁ r B) :=
  PerAVg d₀ d₁ B M (fun k => (An k).an.lat) fun k => (An k).an.lat_le

variable (d₀ d₁ B) in
/-- **The full periods** (`Λ = per`). -/
def PerAVf (M : Matrix (Fin r) (Fin m) ℂ) : AddSubgroup (TanAV d₀ d₁ r B) :=
  PerAVg d₀ d₁ B M (fun k => (B k).base.per) fun _ => le_rfl

/-! ### Fibre forms -/

variable (B) in
/-- `θ_{k,i₀}(z_k)`. -/
def thI (z : ∀ k, Fin (B k).g → ℂ) (k : Fin m) : ℂ := (B k).base.θ (z k) (B k).base.i₀

/-- **The fibre form** `s_i Π_k θ_{k,i₀} + Σ_j M_ij T_{j,t₀}(z_j, 0) Π_{l≠j} θ_{l,i₀}`. -/
def fibF (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (z : ∀ k, Fin (B k).g → ℂ) (s : Fin r → ℂ) : ℂ :=
  s i * ∏ k, thI B z k + ∑ j, M i j * ((B j).T (z j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B z l)

/-- On `θ_{i₀} ≠ 0`: `fibF i = Π_k θ_{k,i₀} · (s_i + Σ_j M_ij τ_j(z_j))`. -/
theorem fibF_eq (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (z : ∀ k, Fin (B k).g → ℂ) (s : Fin r → ℂ)
    (hz : ∀ k, thI B z k ≠ 0) :
    fibF M i z s = (∏ k, thI B z k) * (s i + ∑ j, M i j * tauV (B j) (z j)) := by
  unfold fibF
  have hj : ∀ j, (B j).T (z j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B z l =
      tauV (B j) (z j) * ∏ k, thI B z k := by
    intro j
    rw [T_zero_eq (B j) (z j) (hz j), ← mul_prod_erase univ (thI B z) (mem_univ j)]
    simp only [thI]; ring
  simp only [hj, mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun j _ => by ring

/-- **Quasi-periodicity of the fibre forms**: if `θ_k(z_k + λ_k) = f_k θ_k(z_k)` and
`T_k(z_k + λ_k, η(λ_k)) = f_k T_k(z_k, 0)` for all `k`, then `fibF(z + λ, s + M η(λ)) = Π_k f_k · fibF(z, s)`. -/
theorem fibF_add_per (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) {z lam : ∀ k, Fin (B k).g → ℂ}
    (s : Fin r → ℂ) (f : Fin m → ℂ)
    (hθ : ∀ k, (B k).base.θ (z k + lam k) = f k • (B k).base.θ (z k))
    (hT : ∀ k, (B k).T (z k + lam k) ((B k).η (lam k)) = f k • (B k).T (z k) 0) :
    fibF M i (z + lam) (s + M.mulVec (etaB B lam)) = (∏ k, f k) * fibF M i z s := by
  set W : Fin m → ℂ := thI B z
  have hW : ∀ l, thI B (z + lam) l = f l * W l := fun l => by
    simp only [thI, W, Pi.add_apply, hθ l, Pi.smul_apply, smul_eq_mul]
  have hTj : ∀ j, (B j).T (z j + lam j) 0 (B j).t₀ =
      f j * (B j).T (z j) 0 (B j).t₀ - (B j).η (lam j) * (f j * W j) := by
    intro j
    have h1 := congrFun (hT j) (B j).t₀
    rw [T_t₀_add] at h1
    have h2 : (B j).base.θ (z j + lam j) (B j).base.i₀ = f j * W j := by
      have := hW j; simpa [thI] using this
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h2] at h1
    linear_combination h1
  have hP : ∏ l, thI B (z + lam) l = (∏ l, f l) * ∏ l, W l := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun l _ => hW l
  have hPe : ∀ j, f j * ∏ l ∈ univ.erase j, thI B (z + lam) l = (∏ l, f l) * ∏ l ∈ univ.erase j, W l := by
    intro j
    rw [prod_congr rfl fun l _ => hW l, prod_mul_distrib, ← mul_assoc, mul_prod_erase univ f (mem_univ j)]
  have hWe : ∀ j, W j * ∏ l ∈ univ.erase j, W l = ∏ l, W l := fun j => mul_prod_erase univ W (mem_univ j)
  have hterm : ∀ j, M i j * ((B j).T (z j + lam j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, thI B (z + lam) l) =
      (∏ l, f l) * (M i j * ((B j).T (z j) 0 (B j).t₀ * ∏ l ∈ univ.erase j, W l)) -
        (∏ l, f l) * (M i j * (B j).η (lam j)) * ∏ l, W l := by
    intro j
    rw [hTj j, ← hWe j]
    linear_combination (M i j * ((B j).T (z j) 0 (B j).t₀ - (B j).η (lam j) * W j)) * hPe j
  unfold fibF
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, etaB]
  rw [hP, sum_congr rfl fun j _ => hterm j, sum_sub_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
  ring

lemma differentiable_thI (k : Fin m) : Differentiable ℂ fun z : ∀ k, Fin (B k).g → ℂ => thI B z k :=
  (differentiable_pi.mp (differentiable_θ (B k).base) (B k).base.i₀).comp (differentiable_apply k)

lemma differentiable_fibF (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    Differentiable ℂ (fun u : TanAV d₀ d₁ r B => fibF M i u.2.2.1 u.2.2.2) := by
  have hz : Differentiable ℂ (fun u : TanAV d₀ d₁ r B => u.2.2.1) := by fun_prop
  have hW : ∀ l, Differentiable ℂ (fun u : TanAV d₀ d₁ r B => thI B u.2.2.1 l) := fun l =>
    (differentiable_thI l).comp hz
  have hT : ∀ j, Differentiable ℂ (fun u : TanAV d₀ d₁ r B => (B j).T (u.2.2.1 j) 0 (B j).t₀) := fun j =>
    (differentiable_T (B j) 0 (B j).t₀).comp (by fun_prop)
  unfold fibF
  refine Differentiable.add ((by fun_prop : Differentiable ℂ fun u : TanAV d₀ d₁ r B => u.2.2.2 i).mul
    (differentiable_fprodA _ _ fun l _ => hW l)) ?_
  exact Differentiable.fun_sum fun j _ => (differentiable_const _).mul
    ((hT j).mul (differentiable_fprodA _ _ fun l _ => hW l))

/-! ### Monomials -/

variable (d₀ d₁ B r) in
/-- **A monomial of block degree `D + F`**: an abelian monomial of block degree `D` in the free base coordinates, the
padding `Π θ_{i₀}^{F − Σφ}`, and the fibre forms `Π fibF_i^{φ_i}`. -/
structure MonoAV (D F : ℕ) where
  μ : MonoA d₀ d₁ (Bb B) D
  φ : Fin r → ℕ
  hφ : ∑ i, φ i ≤ F

variable {D F : ℕ}

/-- The monomial as a function on `TanAV`. -/
def MonoAV.eval (M : Matrix (Fin r) (Fin m) ℂ) (ν : MonoAV d₀ d₁ r B D F) (u : TanAV d₀ d₁ r B) : ℂ :=
  ν.μ.eval (piA u) * (∏ k, thI B u.2.2.1 k) ^ (F - ∑ i, ν.φ i) * ∏ i, fibF M i u.2.2.1 u.2.2.2 ^ ν.φ i

/-- **The auxiliary function.** -/
def PsiAV (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F) (p : Fin L → ℤ)
    (u : TanAV d₀ d₁ r B) : ℂ :=
  ∑ l, (p l : ℂ) * (νs l).eval M u

theorem MonoAV.differentiable_eval (M : Matrix (Fin r) (Fin m) ℂ) (ν : MonoAV d₀ d₁ r B D F) :
    Differentiable ℂ (ν.eval M) := by
  have hz : Differentiable ℂ (fun u : TanAV d₀ d₁ r B => u.2.2.1) := by fun_prop
  have h1 : Differentiable ℂ fun u : TanAV d₀ d₁ r B => ν.μ.eval (piA u) :=
    ν.μ.differentiable_eval.comp piA.differentiable
  have h2 : Differentiable ℂ fun u : TanAV d₀ d₁ r B => (∏ k, thI B u.2.2.1 k) ^ (F - ∑ i, ν.φ i) :=
    (differentiable_fprodA _ _ fun l _ => (differentiable_thI l).comp hz).pow _
  have h3 : Differentiable ℂ fun u : TanAV d₀ d₁ r B => ∏ i, fibF M i u.2.2.1 u.2.2.2 ^ ν.φ i :=
    differentiable_fprodA _ _ fun i _ => (differentiable_fibF M i).pow _
  exact (h1.mul h2).mul h3

lemma contDiff_thI (k : Fin m) :
    ContDiff ℂ (⊤ : ℕ∞) fun u : TanAV d₀ d₁ r B => thI B u.2.2.1 k :=
  (contDiff_iff_contDiffAt.mpr fun z =>
    ((analyticAt_pi_iff.mp ((B k).base.θ_analytic z)) (B k).base.i₀).contDiffAt).comp (by fun_prop)

lemma contDiff_fibF (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    ContDiff ℂ (⊤ : ℕ∞) (fun u : TanAV d₀ d₁ r B => fibF M i u.2.2.1 u.2.2.2) := by
  have hT : ∀ j, ContDiff ℂ (⊤ : ℕ∞) (fun u : TanAV d₀ d₁ r B => (B j).T (u.2.2.1 j) 0 (B j).t₀) := fun j =>
    (contDiff_iff_contDiffAt.mpr fun z => (analyticAt_T (B j) 0 (B j).t₀ z).contDiffAt).comp (by fun_prop)
  unfold fibF
  refine ContDiff.add ((by fun_prop : ContDiff ℂ (⊤ : ℕ∞) fun u : TanAV d₀ d₁ r B => u.2.2.2 i).mul
    (contDiff_prod fun l _ => contDiff_thI l)) ?_
  exact ContDiff.sum fun j _ => contDiff_const.mul ((hT j).mul (contDiff_prod fun l _ => contDiff_thI l))

lemma contDiff_monoA (μ : MonoA d₀ d₁ (Bb B) D) : ContDiff ℂ (⊤ : ℕ∞) μ.eval := by
  have hθ : ∀ k c, ContDiff ℂ (⊤ : ℕ∞) fun u : LSG.MEB.Tan d₀ d₁ (Bb B) => (B k).base.θ (u.2.2 k) c :=
    fun k c => (contDiff_iff_contDiffAt.mpr fun z =>
      ((analyticAt_pi_iff.mp ((B k).base.θ_analytic z)) c).contDiffAt).comp (by fun_prop)
  unfold MonoA.eval
  have h1 := contDiff_prod (t := univ) (f := fun i (u : LSG.MEB.Tan d₀ d₁ (Bb B)) => u.1 i ^ μ.α i)
    fun i _ => (by fun_prop : ContDiff ℂ (⊤ : ℕ∞) fun u : LSG.MEB.Tan d₀ d₁ (Bb B) => u.1 i).pow _
  have h2 := contDiff_prod (t := univ)
    (f := fun j (u : LSG.MEB.Tan d₀ d₁ (Bb B)) => Complex.exp (u.2.1 j) ^ μ.β j)
    fun j _ => (by fun_prop : ContDiff ℂ (⊤ : ℕ∞)
      fun u : LSG.MEB.Tan d₀ d₁ (Bb B) => Complex.exp (u.2.1 j)).pow _
  have h3 := contDiff_prod (t := univ)
    (f := fun k (u : LSG.MEB.Tan d₀ d₁ (Bb B)) => ∏ c, (Bb B k).θ (u.2.2 k) (fidx (Bb B k) c) ^ μ.γ k c)
    fun k _ => contDiff_prod (t := univ)
      (f := fun c (u : LSG.MEB.Tan d₀ d₁ (Bb B)) => (Bb B k).θ (u.2.2 k) (fidx (Bb B k) c) ^ μ.γ k c)
      fun c _ => (hθ k _).pow _
  exact (h1.mul h2).mul h3

theorem contDiff_PsiAV (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) : ContDiff ℂ (⊤ : ℕ∞) (PsiAV M νs p) := by
  unfold PsiAV
  refine ContDiff.sum fun l _ => contDiff_const.mul ?_
  have h1 : ContDiff ℂ (⊤ : ℕ∞) fun u : TanAV d₀ d₁ r B => (νs l).μ.eval (piA u) :=
    (contDiff_monoA (νs l).μ).comp piA.contDiff
  unfold MonoAV.eval
  exact (h1.mul ((contDiff_prod fun k _ => contDiff_thI k).pow _)).mul
    (contDiff_prod fun i _ => (contDiff_fibF M i).pow _)

/-! ### Quasi-periodicity -/

/-- The abelian part under a period: `μ(u + ω) = Π_k f_k^D μ(u)`. -/
theorem MonoA_eval_add_per (μ : MonoA d₀ d₁ (Bb B) D) {u ω : LSG.MEB.Tan d₀ d₁ (Bb B)} (f : Fin m → ℂ)
    (hx : ω.1 = 0) (hb : ∀ i, ∃ k : ℤ, ω.2.1 i = 2 * Real.pi * Complex.I * k)
    (hθ : ∀ k, (B k).base.θ (u.2.2 k + ω.2.2 k) = f k • (B k).base.θ (u.2.2 k)) :
    μ.eval (u + ω) = (∏ k, f k ^ D) * μ.eval u := by
  have hb' : ∀ j, Complex.exp ((u + ω).2.1 j) = Complex.exp (u.2.1 j) := fun j => by
    obtain ⟨a, ha⟩ := hb j
    change Complex.exp (u.2.1 j + ω.2.1 j) = _
    rw [ha, Complex.exp_add]
    have e : Complex.exp (2 * Real.pi * I * a) = 1 := by
      rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I a
    rw [e, mul_one]
  have hx' : ∀ i, (u + ω).1 i = u.1 i := fun i => by
    change u.1 i + ω.1 i = u.1 i; rw [hx]; simp
  have hz : ∀ k c, (Bb B k).θ ((u + ω).2.2 k) c = f k * (Bb B k).θ (u.2.2 k) c := fun k c => by
    change (B k).base.θ (u.2.2 k + ω.2.2 k) c = _
    rw [hθ k]; rfl
  unfold MonoA.eval
  simp only [hx', hb', hz, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, μ.hγ]
  ring

/-- **The multiplier of a monomial under a period** `ω ∈ PerAV`, given the block multipliers. -/
theorem MonoAV.eval_add_per (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ)
    (ν : MonoAV d₀ d₁ r B D F) {ω : TanAV d₀ d₁ r B} (hω : ω ∈ PerAV d₀ d₁ An M) (u : TanAV d₀ d₁ r B)
    (κ : Fin m → ℂ) (Lf : ∀ k, (Fin (B k).g → ℂ) →ₗ[ℂ] ℂ)
    (hθq : ∀ k z, (B k).base.θ (z + ω.2.2.1 k) = (κ k * Complex.exp (Lf k z)) • (B k).base.θ z) :
    ν.eval M (u + ω) = (∏ k, (κ k * Complex.exp (Lf k (u.2.2.1 k))) ^ (D + F)) * ν.eval M u := by
  set f : Fin m → ℂ := fun k => κ k * Complex.exp (Lf k (u.2.2.1 k)) with hf
  have hθ : ∀ k, (B k).base.θ (u.2.2.1 k + ω.2.2.1 k) = f k • (B k).base.θ (u.2.2.1 k) := fun k => hθq k _
  have hT : ∀ k, (B k).T (u.2.2.1 k + ω.2.2.1 k) ((B k).η (ω.2.2.1 k)) = f k • (B k).T (u.2.2.1 k) 0 := by
    intro k
    have := VBlockAn.T_qp (b := B k) ((An k).an.lat_le (hω.2.2.1 k)) (hθq k) (u.2.2.1 k) 0
    simpa using this
  have hA : ν.μ.eval (piA (u + ω)) = (∏ k, f k ^ D) * ν.μ.eval (piA u) := by
    rw [map_add]
    exact MonoA_eval_add_per ν.μ f hω.1 hω.2.1 hθ
  have hW : ∏ k, thI B (u + ω).2.2.1 k = (∏ k, f k) * ∏ k, thI B u.2.2.1 k := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    change (B k).base.θ (u.2.2.1 k + ω.2.2.1 k) _ = _
    rw [hθ k]; rfl
  have hS : ∀ i, fibF M i (u + ω).2.2.1 (u + ω).2.2.2 = (∏ k, f k) * fibF M i u.2.2.1 u.2.2.2 := by
    intro i
    have e : (u + ω).2.2.2 = u.2.2.2 + M.mulVec (etaB B ω.2.2.1) := by
      change u.2.2.2 + ω.2.2.2 = _; rw [hω.2.2.2]
    rw [e]
    exact fibF_add_per M i u.2.2.2 f hθ hT
  have hφ := ν.hφ
  have key : ∏ i, fibF M i (u + ω).2.2.1 (u + ω).2.2.2 ^ ν.φ i =
      (∏ k, f k) ^ (∑ i, ν.φ i) * ∏ i, fibF M i u.2.2.1 u.2.2.2 ^ ν.φ i := by
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => by rw [hS i, mul_pow]
  have hfD : ∏ k, f k ^ (D + F) =
      (∏ k, f k ^ D) * (∏ k, f k) ^ (F - ∑ i, ν.φ i) * (∏ k, f k) ^ (∑ i, ν.φ i) := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hφ, ← prod_pow, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => by rw [pow_add]
  change _ = (∏ k, f k ^ (D + F)) * _
  unfold MonoAV.eval
  rw [hA, hW, key, hfD, mul_pow]
  ring

/-- **Common multiplier of the monomials under a period.** -/
theorem exists_qp_monoAV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (νs : Fin L → MonoAV d₀ d₁ r B D F) {ω : TanAV d₀ d₁ r B} (hω : ω ∈ PerAV d₀ d₁ An M)
    (u : TanAV d₀ d₁ r B) :
    ∃ mu : ℂ, ‖mu‖ ≤ Real.exp (m * (D + F) * cQU (fun k => (An k).an) * (‖u‖ + ‖ω‖) ^ 2) ∧
      ∀ l, (νs l).eval M (u + ω) = mu * (νs l).eval M u := by
  set Cq := cQU (fun k => (An k).an)
  choose κ Lf hκ0 hκ hκi hL hθ using fun k => (An k).an.qp (ω.2.2.1 k) (hω.2.2.1 k)
  set f : Fin m → ℂ := fun k => κ k * Complex.exp (Lf k (u.2.2.1 k)) with hf
  refine ⟨∏ k, f k ^ (D + F), ?_, fun l => (νs l).eval_add_per An M hω u κ Lf hθ⟩
  rw [norm_prod]
  have hc0 : 0 ≤ Cq := cQU_nonneg _
  have hk : ∀ k ∈ univ, ‖f k ^ (D + F)‖ ≤ Real.exp ((D + F) * Cq * (‖u‖ + ‖ω‖) ^ 2) := by
    intro k _
    rw [norm_pow, hf, norm_mul, Complex.norm_exp]
    have hcq : (An k).an.cQ ≤ Cq := cQ_le (fun k => (An k).an) k
    have h1 : (Lf k (u.2.2.1 k)).re ≤ Cq * ‖ω‖ * ‖u‖ :=
      (Complex.re_le_norm _).trans ((hL k _).trans
        (mul_le_mul (mul_le_mul hcq (norm_zV_le ω k) (norm_nonneg _) hc0) (norm_zV_le u k)
          (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))))
    have h2 : ‖κ k‖ ≤ Real.exp (Cq * ‖ω‖ ^ 2) :=
      (hκ k).trans (Real.exp_le_exp.mpr (mul_le_mul hcq
        (pow_le_pow_left₀ (norm_nonneg _) (norm_zV_le ω k) 2) (by positivity) hc0))
    calc (‖κ k‖ * Real.exp (Lf k (u.2.2.1 k)).re) ^ (D + F)
        ≤ (Real.exp (Cq * ‖ω‖ ^ 2) * Real.exp (Cq * ‖ω‖ * ‖u‖)) ^ (D + F) := by gcongr
      _ = Real.exp ((D + F : ℕ) * (Cq * ‖ω‖ ^ 2 + Cq * ‖ω‖ * ‖u‖)) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]
      _ ≤ Real.exp ((D + F) * Cq * (‖u‖ + ‖ω‖) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hu := norm_nonneg u
        have hw := norm_nonneg ω
        have hD : (0 : ℝ) ≤ D + F := by positivity
        push_cast
        nlinarith [mul_nonneg (mul_nonneg hD hc0) (mul_nonneg hu hu),
          mul_nonneg (mul_nonneg hD hc0) (mul_nonneg hu hw)]
  calc ∏ k, ‖f k ^ (D + F)‖ ≤ ∏ _k : Fin m, Real.exp ((D + F) * Cq * (‖u‖ + ‖ω‖) ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) hk
    _ = Real.exp (m * (D + F) * Cq * (‖u‖ + ‖ω‖) ^ 2) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf

end LSG.AuxAV
