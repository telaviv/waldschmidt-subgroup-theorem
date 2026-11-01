/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Model

/-!
# The ideals `IGsem` and `IGexp` of `G̃` (M2.5 α; template `LSG.MEB.ModelIG`)

* **`IGsem_isPrime`**: `IGsem` is prime, by the identity theorem on the connected space `Tan × ℂ^m` (with β's
  `liftZ`, `mem_IGsem_iff_liftZ`, `analyticAt_eval_liftZ` from `LSG.MEBV.Lift`).
* `VBlock.blockI k = (gens_k) ⊆ ℂ[X_c, T_t]`, `YZ j`, **`IGexp = (Y_j Z_j − 1)_j + Σ_k rename_k (blockI k)`**
  (the explicit ideal, in the shape of `StrongSix.M2.bezout_blocks`).
* `IGexp_le_vanish`: `IGexp ⊆ I(E)` for every `E` (`lift_model` and homogeneity of the generators).
* **`exists_coordsZ_of_IGexp`**: every zero of `IGexp` **whose nonzero blocks have nonzero `X`-part** is
  `coordsZ g ν` (the field `surjV`). There is no cone Nullstellensatz `rad_IGexp` (M2.md §M2.4a.2): the model is
  not saturated at `{X = 0}`, and the core slices with `X`-only forms, so it never needs it.
* `mem_IGsem_iff_coordsZ`.
-/

open MvPolynomial Filter Topology

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- **`IGsem` is prime** (identity theorem on the connected space `Tan × ℂ^m`). -/
theorem IGsem_isPrime : (IGsem d₀ d₁ B).IsPrime := by
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ IGsem d₀ d₁ B := htop ▸ Submodule.mem_top
    have := mem_IGsem_iff_liftZ.mp h1 0 0
    rw [map_one] at this
    exact one_ne_zero this
  have hfh : ∀ q : LZ d₀ d₁ B, eval (liftZ q.1 q.2) P * eval (liftZ q.1 q.2) Q = 0 := fun q => by
    have := mem_IGsem_iff_liftZ.mp hPQ q.1 q.2
    rwa [map_mul] at this
  by_cases hP : P ∈ IGsem d₀ d₁ B
  · exact Or.inl hP
  right
  have : ∃ q : LZ d₀ d₁ B, eval (liftZ q.1 q.2) P ≠ 0 := by
    by_contra hcon
    exact hP (mem_IGsem_iff_liftZ.mpr fun u μ => not_not.mp fun h => hcon ⟨(u, μ), h⟩)
  obtain ⟨q₀, hq₀⟩ := this
  have hev : (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) =ᶠ[𝓝 q₀] 0 := by
    filter_upwards [(analyticAt_eval_liftZ P q₀).continuousAt.eventually_ne hq₀] with q hq
    exact (mul_eq_zero.mp (hfh q)).resolve_left hq
  have han : AnalyticOnNhd ℂ (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) Set.univ :=
    fun q _ => analyticAt_eval_liftZ Q q
  have hpc : IsPreconnected (Set.univ : Set (LZ d₀ d₁ B)) := (convex_univ (𝕜 := ℝ)).isPreconnected
  have hzero : Set.EqOn (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) 0 Set.univ :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc (Set.mem_univ q₀) hev
  refine mem_IGsem_iff_liftZ.mpr fun u μ => ?_
  have := hzero (Set.mem_univ (u, μ))
  simpa using this

theorem IGsem_ne_top : IGsem d₀ d₁ B ≠ ⊤ := (IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)).ne_top

/-! ### The explicit ideal `IGexp` -/

/-- The explicit ideal of a block, in `ℂ[X_c, T_t]`. -/
noncomputable def VBlock.blockI (b : VBlock) : Ideal (MvPolynomial b.Idx ℂ) :=
  Ideal.span {Q | Q ∈ b.gens}

variable (d₀ B) in
/-- `Y_j Z_j − 1`. -/
noncomputable def YZ (j : Fin d₁) : MvPolynomial (Var d₀ d₁ B) ℂ := X (.y j) * X (.z j) - 1

variable (d₀ d₁ B) in
/-- The `G_m` relations as a list. -/
noncomputable def lYZ : List (MvPolynomial (Var d₀ d₁ B) ℂ) := List.ofFn (YZ d₀ B)

theorem lYZ_length : (lYZ d₀ d₁ B).length = d₁ := by simp [lYZ]

variable (d₀ d₁ B) in
/-- **The explicit ideal of `G̃`**: `(Y_j Z_j − 1)_j + Σ_k rename_k (gens_k)`. -/
noncomputable def IGexp : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Ideal.ofList (lYZ d₀ d₁ B) ⊔ ⨆ k, ((B k).blockI).map (rename (Var.e (d₀ := d₀) (d₁ := d₁) k))

theorem YZ_mem_IGexp (j : Fin d₁) : YZ d₀ B j ∈ IGexp d₀ d₁ B :=
  Ideal.mem_sup_left (Ideal.subset_span (by simp [lYZ]))

theorem rename_mem_IGexp (k : Fin m) {Q : MvPolynomial (B k).Idx ℂ} (hQ : Q ∈ (B k).gens) :
    rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q ∈ IGexp d₀ d₁ B :=
  Ideal.mem_sup_right (Ideal.mem_iSup_of_mem k (Ideal.mem_map_of_mem _ (Ideal.subset_span hQ)))

/-- `IGexp` as the span of its generators. -/
theorem IGexp_eq_span : IGexp d₀ d₁ B = Ideal.span (Set.range (YZ d₀ B) ∪
    {P | ∃ k, ∃ Q ∈ (B k).gens, P = rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q}) := by
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun k => ?_)
    · rw [Ideal.ofList, Ideal.span_le]
      intro P hP
      simp only [lYZ, List.mem_ofFn, Set.mem_setOf_eq] at hP
      obtain ⟨j, rfl⟩ := hP
      exact Ideal.subset_span (Or.inl ⟨j, rfl⟩)
    · rw [VBlock.blockI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨Q, hQ, rfl⟩
      exact Ideal.subset_span (Or.inr ⟨k, Q, hQ, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨k, Q, hQ, rfl⟩)
    · exact YZ_mem_IGexp j
    · exact rename_mem_IGexp k hQ

theorem eval_rename_e (k : Fin m) (x : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (B k).Idx ℂ) :
    eval x (rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q) = eval (fun c => x (.e k c)) Q := by
  rw [eval_rename]; rfl

/-- **`IGexp ⊆ I(E)`** for every set of points. -/
theorem IGexp_le_vanish (E : Set (GPt d₀ d₁ B)) : IGexp d₀ d₁ B ≤ vanish E := by
  rw [IGexp_eq_span, Ideal.span_le]
  rintro _ (⟨j, rfl⟩ | ⟨k, Q, hQ, rfl⟩) <;> refine mem_vanish.mpr fun g _ lam => ?_
  · simp [YZ]
  · rw [eval_rename_e]
    obtain ⟨d, -, hd⟩ := (B k).gens_hom Q hQ
    have : (fun c => coords g lam (.e k c)) = (lam k : ℂ) • (B k).rep (g.2.2 k) := by
      funext c; simp
    rw [this, LSG.MEB.eval_smul_of_isHomogeneous hd, VBlock.rep, (B k).lift_model _ Q hQ, mul_zero]

theorem IGexp_le_IGsem : IGexp d₀ d₁ B ≤ IGsem d₀ d₁ B := IGexp_le_vanish _

/-- **Every zero of `IGexp` whose nonzero blocks have nonzero `X`-part is a cone point** (the field
`surjV`). -/
theorem exists_coordsZ_of_IGexp {x : Var d₀ d₁ B → ℂ} (hx : ∀ P ∈ IGexp d₀ d₁ B, eval x P = 0)
    (hX : ∀ k, (fun c => x (.e k c)) ≠ 0 → (fun c : Fin (B k).N => x (.e k (Sum.inl c))) ≠ 0) :
    ∃ (g : GPt d₀ d₁ B) (ν : Fin m → ℂ), x = coordsZ g ν := by
  classical
  have hyz : ∀ j, x (.y j) * x (.z j) = 1 := fun j => by
    have := hx _ (YZ_mem_IGexp j)
    simpa [YZ, sub_eq_zero] using this
  have hblk : ∀ k, ∃ (p : (B k).Pt) (ν : ℂ), (fun c => x (.e k c)) = ν • (B k).rep p := by
    intro k
    by_cases h0 : (fun c => x (.e k c)) = 0
    · exact ⟨0, 0, by rw [h0, zero_smul]⟩
    have hz : ∀ Q ∈ gensOf (B k).base.gens (B k).gensT, eval (fun c => x (.e k c)) Q = 0 :=
      fun Q hQ => by
        rw [← eval_rename_e (d₀ := d₀) (d₁ := d₁)]; exact hx _ (rename_mem_IGexp k hQ)
    obtain ⟨z, c, hc⟩ := (B k).surjV _ (hX k h0) hz
    obtain ⟨c', hc', h'⟩ := (B k).rep_mk z
    refine ⟨QuotientAddGroup.mk z, c / c', ?_⟩
    change _ = _ • (B k).lift z at hc
    rw [hc, h', smul_smul, div_mul_cancel₀ _ hc']
  choose p ν hpν using hblk
  refine ⟨(fun i => x (.x i), Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j), p), ν, ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j =>
    simp only [coordsZ, GPt.ym]
    have : x (.z j) = (x (.y j))⁻¹ := (eq_inv_of_mul_eq_one_right (hyz j))
    rw [this]; simp
  | e k c => exact congrFun (hpν k) c

theorem IGexp_ne_top : IGexp d₀ d₁ B ≠ ⊤ :=
  ne_top_of_le_ne_top IGsem_ne_top IGexp_le_IGsem

/-- `IGsem` is the vanishing ideal of the cone points. -/
theorem mem_IGsem_iff_coordsZ {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ IGsem d₀ d₁ B ↔ ∀ g ν, eval (coordsZ g ν) P = 0 := by
  constructor
  · intro hP g ν
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP g (Set.mem_univ _) lam) ν
  · intro h
    exact mem_vanish.mpr fun g _ lam => by rw [coords_eq_coordsZ]; exact h g _

end LSG.MEBV
