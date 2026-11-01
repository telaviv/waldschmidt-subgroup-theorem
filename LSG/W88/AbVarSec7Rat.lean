/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarSec7Defs
import LSG.MEB.ModelIG

/-!
# A5.7c: from `ObstrDataB` to `SubgroupDataB`, the grid, and the polynomial fed to `MultEstB` (`STAGE_A5.md` §6.3)

* **`exists_subgroupDataB`**: the `ℚ̄`-rational part of `O.h0` (`ratPart`) gives `SubgroupDataB` with the same
  `λ, δ₁, δ₂` and larger `δ − τ` (copy of `exists_subgroupData_rat`; `λ` is counted with any period group `Pe`
  whose elements have zero `G_a`-part, e.g. `PerL`).
* `finrank_*_leB`, **`obstr_delta_posB`**: a proper obstruction has codimension `≥ 1`.
* `gridPtsB`, `mem_gridPtsB`, **`sig_gridPtsB`**: the points `exp_G(Σ h_j y_j)`, `h_j ≤ M`.
* **`PW μs p = PpolyA μs p · Π_k X_{k,i₀}`** (block degree `D + 1 ≥ 1`, as `Wprod` in the elliptic case):
  `isHomB_PW`, `PW_mem_FLE`, `PW_notMem_IGsem` (via `IGsem_isPrime`), `ordGtB_PW` (Leibniz).
-/

open MvPolynomial Module LSG.AuxA
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE)

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock ObstrDataB PerL perAb IsRatSub tanOf IsHomB DfunB blk IGsem OrdGtB sigB liftB)

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### The `ℚ̄`-rational part -/

/-- **The `ℚ̄`-rational subgroup data** attached to `O`. -/
def ratDataB (O : ObstrDataB d₀ d₁ B) : SubgroupDataB d₀ d₁ B where
  h0 := ratPart O.h0
  U := O.U
  t := O.t
  h0_rat := rationalOverQbar_ratPart _
  t_rat := O.t_rat

theorem ratDataB_tan_le (O : ObstrDataB d₀ d₁ B) : (ratDataB O).tan ≤ O.tan :=
  fun _ hu => ⟨ratPart_le _ hu.1, hu.2⟩

theorem inf_tanPer_eqB (O : ObstrDataB d₀ d₁ B) (Pe : AddSubgroup (MEB.Tan d₀ d₁ B))
    (hPe : ∀ p ∈ Pe, p.1 = 0) (Y : AddSubgroup (MEB.Tan d₀ d₁ B)) (hY : ∀ y ∈ Y, AlgVec y.1) :
    Y ⊓ ((ratDataB O).tan.toAddSubgroup ⊔ Pe) = Y ⊓ (O.tan.toAddSubgroup ⊔ Pe) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (sup_le_sup_right (fun u hu => ratDataB_tan_le O hu) _)
  · rintro y ⟨hyY, hy⟩
    refine ⟨hyY, ?_⟩
    obtain ⟨a, ha, p, hp, rfl⟩ := AddSubgroup.mem_sup.mp hy
    refine AddSubgroup.mem_sup.mpr ⟨a, ?_, p, hp, rfl⟩
    have halg : AlgVec (a + p).1 := hY _ hyY
    rw [Prod.fst_add, hPe p hp, add_zero] at halg
    exact ⟨mem_ratPart ha.1 halg, ha.2⟩

theorem finrank_tan_addB (O : ObstrDataB d₀ d₁ B) :
    finrank ℂ O.tan + finrank ℂ (ratPart O.h0) = finrank ℂ (ratDataB O).tan + finrank ℂ O.h0 := by
  set f : MEB.Tan d₀ d₁ B →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.fst ℂ _ _
  have hmapO : O.tan.map f = O.h0 := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩; exact hu.1
    · intro a ha
      exact ⟨(a, 0, 0), ⟨ha, Submodule.zero_mem _, Submodule.zero_mem _⟩, rfl⟩
  have hmapH : (ratDataB O).tan.map f = ratPart O.h0 := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩; exact hu.1
    · intro a ha
      exact ⟨(a, 0, 0), ⟨ha, Submodule.zero_mem _, Submodule.zero_mem _⟩, rfl⟩
  have hker : (ratDataB O).tan ⊓ LinearMap.ker f = O.tan ⊓ LinearMap.ker f := by
    apply le_antisymm
    · exact inf_le_inf_right _ (ratDataB_tan_le O)
    · rintro u ⟨hu, hk⟩
      have hu1 : u.1 = 0 := hk
      refine ⟨⟨?_, hu.2⟩, hk⟩
      rw [hu1]; exact Submodule.zero_mem _
  have e1 := StrongSix.Roy.finrank_map_add_inf_ker f O.tan
  have e2 := StrongSix.Roy.finrank_map_add_inf_ker f (ratDataB O).tan
  rw [hmapO] at e1
  rw [hmapH, hker] at e2
  omega

lemma finrank_blocks : finrank ℂ (∀ k, Fin (B k).g → ℂ) = ∑ k, (B k).g := by
  simp [Module.finrank_pi_fintype]

theorem finrank_h0_leB (O : ObstrDataB d₀ d₁ B) : finrank ℂ O.h0 ≤ d₀ := by
  simpa using Submodule.finrank_le O.h0

theorem finrank_U_leB (O : ObstrDataB d₀ d₁ B) : finrank ℚ O.U ≤ d₁ := by
  simpa using Submodule.finrank_le O.U

theorem finrank_t_leB (O : ObstrDataB d₀ d₁ B) : finrank ℂ O.t ≤ ∑ k, (B k).g :=
  (Submodule.finrank_le O.t).trans finrank_blocks.le

/-- **The `ℚ̄`-rational subgroup data**: same `λ`, `δ₁`, `δ₂`, and `δ − τ` does not decrease. -/
theorem exists_subgroupDataB (O : ObstrDataB d₀ d₁ B) (W : Submodule ℂ (MEB.Tan d₀ d₁ B))
    (Pe : AddSubgroup (MEB.Tan d₀ d₁ B)) (hPe : ∀ p ∈ Pe, p.1 = 0)
    (Y : AddSubgroup (MEB.Tan d₀ d₁ B)) (hY : ∀ y ∈ Y, AlgVec y.1) :
    ∃ H : SubgroupDataB d₀ d₁ B,
      rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Pe)) = rk (Y ⊓ (O.tan.toAddSubgroup ⊔ Pe)) ∧
      H.δ1 = finrank ℚ O.U ∧ H.δ2 = (∑ k, (B k).g) - finrank ℂ O.t ∧
      ((d₀ - finrank ℂ O.h0 + finrank ℚ O.U + ((∑ k, (B k).g) - finrank ℂ O.t) : ℕ) : ℤ) -
          ((finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) : ℕ) : ℤ) ≤
        (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
  refine ⟨ratDataB O, by rw [inf_tanPer_eqB O Pe hPe Y hY], rfl, rfl, ?_⟩
  have hA := finrank_inf_add_le W O.tan (ratDataB O).tan (ratDataB_tan_le O)
  have hB := finrank_tan_addB O
  have hW1 : finrank ℂ ↥(W ⊓ O.tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hW2 : finrank ℂ ↥(W ⊓ (ratDataB O).tan) ≤ finrank ℂ W := Submodule.finrank_mono inf_le_left
  have hh0 := finrank_h0_leB O
  have hr0 : finrank ℂ (ratPart O.h0) ≤ finrank ℂ O.h0 := Submodule.finrank_mono (ratPart_le _)
  simp only [SubgroupDataB.δ, SubgroupDataB.δ0, SubgroupDataB.δ1, SubgroupDataB.δ2]
  change ((d₀ - finrank ℂ O.h0 + finrank ℚ O.U + ((∑ k, (B k).g) - finrank ℂ O.t) : ℕ) : ℤ) -
      ((finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan) : ℕ) : ℤ) ≤
    ((d₀ - finrank ℂ (ratPart O.h0) + finrank ℚ O.U + ((∑ k, (B k).g) - finrank ℂ O.t) : ℕ) : ℤ) -
      ((finrank ℂ W - finrank ℂ ↥(W ⊓ (ratDataB O).tan) : ℕ) : ℤ)
  push_cast [hW1, hW2, hh0, hr0.trans hh0]
  omega

/-- **A proper obstruction has codimension `≥ 1`.** -/
theorem obstr_delta_posB (O : ObstrDataB d₀ d₁ B) (hO : O.Proper) :
    1 ≤ d₀ - finrank ℂ O.h0 + finrank ℚ O.U + ((∑ k, (B k).g) - finrank ℂ O.t) := by
  by_contra hcon
  apply hO
  have h1 : finrank ℂ O.h0 = d₀ := by have := finrank_h0_leB O; omega
  have h2 : finrank ℚ O.U = 0 := by omega
  have h3 : finrank ℂ O.t = ∑ k, (B k).g := by have := finrank_t_leB O; omega
  have e1 : O.h0 = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h1)
  have e2 : O.U = ⊥ := Submodule.finrank_eq_zero.mp h2
  have e3 : O.t = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h3, finrank_blocks])
  have e4 : torusLie O.U = ⊤ := by
    rw [e2]
    refine eq_top_iff.mpr fun v _ φ hφ => ?_
    rw [Submodule.mem_bot] at hφ
    simp [hφ]
  change tanOf O.h0 O.U O.t = ⊤
  rw [tanOf, e1, e4, e3, Submodule.prod_top, Submodule.prod_top]

/-! ### The grid -/

open scoped Classical in
/-- The grid points `exp_G(Σ h_j y_j)`, `0 ≤ h_j ≤ M`. -/
def gridPtsB {μ : ℕ} (y : Fin μ → MEB.Tan d₀ d₁ B) (M : ℕ) : Finset (MEB.GPt d₀ d₁ B) :=
  Finset.univ.image fun h : Fin μ → Fin (M + 1) => MEB.expG d₀ d₁ B (∑ j, (h j : ℕ) • y j)

theorem mem_gridPtsB {μ : ℕ} {y : Fin μ → MEB.Tan d₀ d₁ B} {M : ℕ} {g : MEB.GPt d₀ d₁ B} :
    g ∈ gridPtsB y M ↔ ∃ h : Fin μ → ℕ, (∀ j, h j ≤ M) ∧ g = MEB.expG d₀ d₁ B (∑ j, h j • y j) := by
  classical
  unfold gridPtsB
  constructor
  · intro hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨fun j => h j, fun j => Nat.lt_succ_iff.mp (h j).isLt, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact Finset.mem_image.mpr ⟨fun j => ⟨h j, Nat.lt_succ_of_le (hh j)⟩, Finset.mem_univ _, rfl⟩

theorem sig_gridPtsB {μ : ℕ} {y : Fin μ → MEB.Tan d₀ d₁ B} {M r : ℕ} {σ : MEB.GPt d₀ d₁ B}
    (hσ : σ ∈ sigB (gridPtsB y M) r) :
    ∃ h : Fin μ → ℕ, (∀ j, h j ≤ r * M) ∧ σ = MEB.expG d₀ d₁ B (∑ j, h j • y j) := by
  obtain ⟨σs, hσs, rfl⟩ := hσ
  choose h hh hσh using fun i => mem_gridPtsB.mp (hσs i)
  refine ⟨fun j => ∑ i, h i j, fun j => ?_, ?_⟩
  · calc ∑ i, h i j ≤ ∑ _i : Fin r, M := Finset.sum_le_sum fun i _ => hh i j
      _ = r * M := by simp
  · rw [Finset.sum_congr rfl fun i _ => hσh i, ← map_sum, Finset.sum_comm]
    simp only [Finset.sum_smul]

/-! ### The polynomial `PpolyA · Π_k X_{k,i₀}` -/

variable (d₀ d₁ B) in
/-- The monomial `Π_k X_{k,i₀}` (block degree `1`). -/
def monoW : MonoA d₀ d₁ B 1 where
  α := 0
  β := 0
  γ := fun _ => Pi.single 0 1
  hγ := fun _ => by simp

theorem monoW_eval (u : MEB.Tan d₀ d₁ B) : (monoW d₀ d₁ B).eval u = ∏ k, (B k).θ (u.2.2 k) (B k).i₀ := by
  unfold MonoA.eval monoW
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero]

theorem monoW_eval_zero_ne : (monoW d₀ d₁ B).eval 0 ≠ 0 := by
  rw [monoW_eval]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => (B k).θ_i₀

/-- **The polynomial fed to `MultEstB`.** -/
def PW {D L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) : MvPolynomial (MEB.Var d₀ d₁ B) ℂ :=
  PpolyA μs p * (monoW d₀ d₁ B).poly

theorem isHomB_PW {D L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) :
    IsHomB (PW μs p) (fun _ => D + 1) := fun k =>
  (isHomB_PpolyA μs p k).mul ((monoW d₀ d₁ B).isHomB_poly k)

theorem PW_mem_FLE {D L A₀ A₁ : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ)
    (hA : ∀ l, ∑ i, (μs l).α i ≤ A₀) (hB : ∀ l, ∑ j, (μs l).β j ≤ A₁) :
    PW μs p ∈ FLE ℂ blk (DfunB A₀ A₁ (D + 1)) := by
  refine FLE_mono ℂ blk (fun b => ?_) (mul_mem_FLE ℂ (PpolyA_mem_FLE μs p hA hB)
    ((monoW d₀ d₁ B).poly_mem_FLE (A₀ := 0) (A₁ := 0) (by simp [monoW]) (by simp [monoW])))
  cases b <;> simp [DfunB]

theorem PW_notMem_IGsem {D L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ)
    {x : MEB.Tan d₀ d₁ B} (hx : PsiA μs p x ≠ 0) : PW μs p ∉ IGsem d₀ d₁ B := by
  intro h
  rcases (LSG.MEB.IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)).mem_or_mem h with h' | h'
  · exact LSG.MEB.notMem_IGsem_of_eval_ne (u := x) (by rw [eval_PpolyA]; exact hx) h'
  · exact LSG.MEB.notMem_IGsem_of_eval_ne (u := 0) (by rw [MonoA.eval_poly]; exact monoW_eval_zero_ne) h'

/-- Leibniz: a product vanishes to the order of a factor. -/
theorem iteratedDeriv_mul_eq_zeroB {u f : ℂ → ℂ} (hu : Differentiable ℂ u) (hf : Differentiable ℂ f)
    {n : ℕ} (h : ∀ j ≤ n, iteratedDeriv j f 0 = 0) : ∀ j ≤ n, iteratedDeriv j (fun s => u s * f s) 0 = 0 := by
  intro j hj
  change iteratedDeriv j (u * f) 0 = 0
  rw [iteratedDeriv_mul (hu.analyticAt 0).contDiffAt (hf.analyticAt 0).contDiffAt]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h (j - i) ((Nat.sub_le j i).trans hj), mul_zero]

theorem ordGtB_PW {D L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ)
    (W : Submodule ℂ (MEB.Tan d₀ d₁ B)) {n : ℕ} (u : MEB.Tan d₀ d₁ B)
    (h : ∀ w ∈ W, ∀ k ≤ n, iteratedDeriv k (fun s : ℂ => PsiA μs p (u + s • w)) 0 = 0) :
    OrdGtB W (PW μs p) n (MEB.expG d₀ d₁ B u) := by
  refine ⟨u, rfl, fun w hw k hk => ?_⟩
  have e : (fun s : ℂ => eval (liftB (u + s • w)) (PW μs p)) =
      fun s => (monoW d₀ d₁ B).eval (u + s • w) * PsiA μs p (u + s • w) := by
    funext s
    rw [PW, map_mul, eval_PpolyA, MonoA.eval_poly, mul_comm]
  have hline : Differentiable ℂ fun s : ℂ => u + s • w :=
    (differentiable_const _).add (differentiable_id.smul_const w)
  rw [e]
  refine iteratedDeriv_mul_eq_zeroB ((monoW d₀ d₁ B).differentiable_eval.comp hline)
    (((contDiff_PsiA μs p).differentiable (by simp)).comp hline) (h w hw) k hk

end LSG.W88
