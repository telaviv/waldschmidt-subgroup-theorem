/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement
import LSG.Weierstrass.ZetaQuasiPeriod

/-!
# W88 Theorem 4.1 for groups with vector-extension factors: the statement (design: `VECEXT.md`)

Statement file only (no proofs beyond trivial ones). Everything is in coordinates.

## The class `𝒞`

`G = G_a^{d₀} × G_m^{d₁} × G₂`, where `G₂` is the **push-out of the universal vector extension
`(E₁ × ⋯ × E_m)^♮` along a `ℚ̄`-linear map `M : ℂ^m → ℂ^r`** (an `r × m` matrix with algebraic entries;
`M` need not be onto, a non-onto `M` adds `G_a` factors to `G₂`). `E_j` is the curve of the period pair
`Ls j` (algebraic `g₂, g₃`). Special cases: `r = 0` is `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (the abelian
statement of `Statement.lean`); `M = id` is `(E₁ × ⋯ × E_m)^♮`; `M = θᵀ` gives the groups `G_ℓ`, `Q''` of
the M* paper.

## Coordinates

`T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r ∋ (a, b, z, s)`; on `(E^m)^♮` the coordinates are `(z, w)` (base,
and the fibre coordinate dual to `−x dx/y`), `exp(z, w) = ((℘_j(z_j), ℘_j'(z_j)), w − ζ(z))`, and
`s = M w`. So
* `Λ(G)` (`LamV`): `a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`, every `z_j ∈ Λ_j` or `℘_j(z_j) ∈ ℚ̄`, and
  `s − M ζ(z) ∈ ℚ̄^r` (`ζ` coordinatewise; Lean's `ζ` equals `η` on the lattice, `zeta_of_mem_lattice`);
* `Ω(G)` (`PerV`): `0 × 2πiℤ^{d₁} × {(λ, M η(λ)) : λ ∈ Λ₁ × ⋯ × Λ_m}`.

## Connected algebraic subgroups (`SubgroupDataV`)

`G' = T_U × (B̃ + Γ)`, with `U ⊂ ℚ^{d₁}` (subtorus with Lie algebra `U^⊥`), `B ⊂ E₁ × ⋯ × E_m` an abelian
subvariety (tangent `t`, `IsAbelianTangent`), `B̃` the image in `G₂` of its universal vector extension
`B^♮ ⊂ (E^m)^♮`, whose tangent space is `perTanId t = span_ℂ {(λ, η(λ)) : λ ∈ t ∩ Λ}` (pushed by `M`:
`perTan`), and `Γ ⊂ ℂ^{d₀} × ℂ^r` a `ℚ̄`-rational subspace of the vector group `G_a^{d₀} × (fibre of G₂)`.
Every such datum is a connected algebraic subgroup defined over `ℚ̄`, and every connected algebraic
subgroup is of this form (`Hom(B^♮, G_a) = 0`; `VECEXT.md` §2). W88's projection-based codimensions:
`δ₀ = d₀ − dim pr₀ Γ`, `δ₁ = dim U`, `δ = codim`, `δ₂ = δ − δ₀ − δ₁`.

## Statements
* `Theorem41Vec`: W88 Thm 4.1 under (NR) for the class `𝒞` (the eventual target).
* `Theorem41VecLA`: the same with three extra premises — `r ≤ 1`, `LiftAlg Ls` (lifts of algebraic
  points of `B` to algebraic points of `B^♮`; true for all curves over `ℚ̄`) and `V ∩ (fibre) = 0`.
  **Proved**: `LSG.W88.theorem41VecLA` (`MainVec.lean`), for every algebraic `M`. Also proved: its onto-`M`
  case `Theorem41VecLAOnto` (`LSG.W88.theorem41VecLA_onto`, `V5dOnto.lean`) and `Theorem41Vec2`
  (`d₀ = 0`, `r ≤ 2`, `dim (V ∩ fibre) ≤ 1`; `LSG.W88.theorem41Vec2`, `V5d2Stmt.lean`). The `r ≤ 1` forms
  cover every lean_mstar bridge except `Thm11KappaMXP` (MX′), which needs `Theorem41Vec2` (`r = 2`).
  `Theorem41Vec` itself is not proved.
* `HyperplaneKappaVec`: W88 §5d ((5.4) ⇒ `V` contains a nonzero subgroup tangent) for the class, under
  `r ≤ 1`, `LiftAlg`, `PerTanRat`; the generic engine behind the bridges.
-/

open Complex Module

namespace LSG.W88.Vec

/-- The tangent space `ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r` of `G_a^{d₀} × G_m^{d₁} × G₂`. -/
abbrev TanV (d0 d1 m r : ℕ) := (Fin d0 → ℂ) × (Fin d1 → ℂ) × (Fin m → ℂ) × (Fin r → ℂ)

variable {d0 d1 m r : ℕ}

/-- `ζ` coordinatewise. -/
noncomputable def zetaV (Ls : Fin m → PeriodPair) (z : Fin m → ℂ) : Fin m → ℂ :=
  fun j => LSG.Weierstrass.zeta (Ls j) (z j)

/-- `η` coordinatewise. -/
noncomputable def etaV (Ls : Fin m → PeriodPair) (z : Fin m → ℂ) : Fin m → ℂ :=
  fun j => LSG.Weierstrass.eta (Ls j) (z j)

/-- Lean's `ζ` vanishes at `0` (every summand of the series is `0` there). -/
lemma zeta_zero (L : PeriodPair) : LSG.Weierstrass.zeta L 0 = 0 := by
  simp [LSG.Weierstrass.zeta, LSG.Weierstrass.zetaSummand]

/-- On the lattice, Lean's `ζ` is the quasi-period: `ζ(λ) = η(λ)`. So `LamV` needs no case split. -/
lemma zeta_of_mem_lattice (L : PeriodPair) {l : ℂ} (hl : l ∈ L.lattice) :
    LSG.Weierstrass.zeta L l = LSG.Weierstrass.eta L l := by
  have h := LSG.Weierstrass.zeta_add L hl 0
  rwa [zero_add, zeta_zero, zero_add] at h

/-- A matrix with algebraic entries. -/
def AlgMat (M : Matrix (Fin r) (Fin m) ℂ) : Prop := ∀ i j, IsAlgebraic ℚ (M i j)

/-- A vector of `T_G` with algebraic coordinates. -/
def AlgVecV (p : TanV d0 d1 m r) : Prop :=
  AlgVec p.1 ∧ AlgVec p.2.1 ∧ AlgVec p.2.2.1 ∧ AlgVec p.2.2.2

/-- A vector of a product `ℂ^a × ℂ^b` with algebraic coordinates. -/
def AlgPair {a b : ℕ} (p : (Fin a → ℂ) × (Fin b → ℂ)) : Prop := AlgVec p.1 ∧ AlgVec p.2

/-- `ℚ̄`-rationality: spanned by its vectors with algebraic coordinates. -/
def RatSubV (W : Submodule ℂ (TanV d0 d1 m r)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgVecV w}

/-- `ℚ̄`-rationality for subspaces of `ℂ^a × ℂ^b`. -/
def RatPair {a b : ℕ} (W : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgPair w}

/-- **`Λ(G)`**, the logarithms of algebraic points. -/
def LamV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) : Set (TanV d0 d1 m r) :=
  {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧
    (∀ j, p.2.2.1 j ∈ (Ls j).lattice ∨ IsAlgebraic ℚ ((Ls j).weierstrassP (p.2.2.1 j))) ∧
    AlgVec (p.2.2.2 - M.mulVec (zetaV Ls p.2.2.1))}

/-- **`Ω(G)`**, the periods: `0 × 2πiℤ^{d₁} × {(λ, M η(λ))}`. -/
noncomputable def PerV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    AddSubgroup (TanV d0 d1 m r) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * I * k) ∧
    (∀ j, p.2.2.1 j ∈ (Ls j).lattice) ∧ p.2.2.2 = M.mulVec (etaV Ls p.2.2.1)}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun j => (Ls j).lattice.add_mem (hp.2.2.1 j) (hq.2.2.1 j), ?_⟩
    · obtain ⟨k, hk⟩ := hp.2.1 i
      obtain ⟨l, hl⟩ := hq.2.1 i
      exact ⟨k + l, by
        show p.2.1 i + q.2.1 i = _
        rw [hk, hl]; push_cast; ring⟩
    · have he : etaV Ls (p.2.2.1 + q.2.2.1) = etaV Ls p.2.2.1 + etaV Ls q.2.2.1 := by
        funext j
        exact LSG.Weierstrass.eta_add (Ls j) (hp.2.2.1 j) (hq.2.2.1 j)
      show p.2.2.2 + q.2.2.2 = M.mulVec (etaV Ls (p.2.2.1 + q.2.2.1))
      rw [he, Matrix.mulVec_add, ← hp.2.2.2, ← hq.2.2.2]
  zero_mem' := by
    refine ⟨rfl, fun _ => ⟨0, by simp⟩, fun j => (Ls j).lattice.zero_mem, ?_⟩
    have he : etaV Ls (0 : Fin m → ℂ) = 0 := by
      funext j; exact LSG.Weierstrass.eta_zero (Ls j)
    show (0 : Fin r → ℂ) = M.mulVec (etaV Ls 0)
    rw [he, Matrix.mulVec_zero]
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun j => (Ls j).lattice.neg_mem (hp.2.2.1 j), ?_⟩
    · obtain ⟨k, hk⟩ := hp.2.1 i
      exact ⟨-k, by
        show -p.2.1 i = _
        rw [hk]; push_cast; ring⟩
    · have he : etaV Ls (-p.2.2.1) = -etaV Ls p.2.2.1 := by
        funext j
        exact LSG.Weierstrass.eta_neg (Ls j) (hp.2.2.1 j)
      show -p.2.2.2 = M.mulVec (etaV Ls (-p.2.2.1))
      rw [he, Matrix.mulVec_neg, ← hp.2.2.2]

/-! ### Embeddings of the pieces of a subgroup tangent space -/

/-- `(a, s) ↦ (a, 0, 0, s)`: the vector group `G_a^{d₀} × (fibre of G₂)`. -/
def vecIncl : ((Fin d0 → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] TanV d0 d1 m r :=
  (LinearMap.fst ℂ _ _).prod ((0 : ((Fin d0 → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] (Fin d1 → ℂ)).prod
    ((0 : ((Fin d0 → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] (Fin m → ℂ)).prod (LinearMap.snd ℂ _ _)))

/-- `x ↦ (0, x, 0, 0)`: the torus. -/
def torIncl : (Fin d1 → ℂ) →ₗ[ℂ] TanV d0 d1 m r :=
  (0 : (Fin d1 → ℂ) →ₗ[ℂ] (Fin d0 → ℂ)).prod
    (LinearMap.id.prod (0 : (Fin d1 → ℂ) →ₗ[ℂ] ((Fin m → ℂ) × (Fin r → ℂ))))

/-- `(z, s) ↦ (0, 0, z, s)`: the factor `G₂`. -/
def g2Incl : ((Fin m → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] TanV d0 d1 m r :=
  (0 : ((Fin m → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] (Fin d0 → ℂ)).prod
    ((0 : ((Fin m → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] (Fin d1 → ℂ)).prod LinearMap.id)

/-- The fibre `0 × 0 × 0 × ℂ^r` of `G₂ → E₁ × ⋯ × E_m`. -/
def fibreV : Submodule ℂ (TanV d0 d1 m r) :=
  LinearMap.range ((vecIncl : _ →ₗ[ℂ] TanV d0 d1 m r) ∘ₗ LinearMap.inr ℂ (Fin d0 → ℂ) (Fin r → ℂ))

/-- **The tangent space of `B^♮ ⊂ (E^m)^♮`** for an abelian subvariety `B` with tangent `t`:
`span_ℂ {(λ, η(λ)) : λ ∈ t, λ_j ∈ Λ_j}` (dimension `2 dim t`). -/
noncomputable def perTanId (Ls : Fin m → PeriodPair) (t : Submodule ℂ (Fin m → ℂ)) :
    Submodule ℂ ((Fin m → ℂ) × (Fin m → ℂ)) :=
  Submodule.span ℂ {p | p.1 ∈ t ∧ (∀ j, p.1 j ∈ (Ls j).lattice) ∧ p.2 = etaV Ls p.1}

/-- Its image `T_{B̃}` in `T(G₂) = ℂ^m × ℂ^r` (push-out along `M`). -/
noncomputable def perTan (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (t : Submodule ℂ (Fin m → ℂ)) : Submodule ℂ ((Fin m → ℂ) × (Fin r → ℂ)) :=
  (perTanId Ls t).map (LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M))

/-- Data of a connected algebraic subgroup `G' = T_U × (B̃ + Γ)` of `G`. -/
structure SubgroupDataV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) where
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d1 → ℚ)
  /-- the tangent space of the abelian image `B` -/
  t : Submodule ℂ (Fin m → ℂ)
  /-- the vector part, inside `G_a^{d₀} × (fibre of G₂)`. The representation is not unique: the vector part
  of `G′` is `gam + ψ(H¹(B, O)^∨)`, so different `gam` can give the same subgroup. Only `tan` (and the
  quantities computed from it) enters the conclusion. -/
  gam : Submodule ℂ ((Fin d0 → ℂ) × (Fin r → ℂ))
  gam_rat : RatPair gam
  t_ab : IsAbelianTangent Ls t

namespace SubgroupDataV

variable {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}
variable (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M)

/-- `T_{G'} = Γ + U^⊥ + T_{B̃}`. -/
noncomputable def tan : Submodule ℂ (TanV d0 d1 m r) :=
  H.gam.map vecIncl ⊔ (torusLie H.U).map torIncl ⊔ (perTan Ls M H.t).map g2Incl

/-- `δ₀ = d₀ − dim π₀(G')`. -/
noncomputable def δ0 : ℕ := d0 - finrank ℂ (H.gam.map (LinearMap.fst ℂ _ _))
/-- `δ₁ = d₁ − dim π₁(G') = dim U`. -/
noncomputable def δ1 : ℕ := finrank ℚ H.U
/-- `δ = codim G'`. -/
noncomputable def δ : ℕ := (d0 + d1 + m + r) - finrank ℂ H.tan
/-- `δ₂ = δ − δ₀ − δ₁`. -/
noncomputable def δ2 : ℕ := H.δ - H.δ0 - H.δ1

/-- `G' ≠ G`. -/
def Proper : Prop := H.δ ≠ 0

end SubgroupDataV

/-- Every algebraic point of an abelian subvariety `B` lifts to an algebraic point of `B^♮`
(true for all curves over `ℚ̄`; proved for CM curves with `κ₁ = 0` in the bridge layer). -/
def LiftAlg (Ls : Fin m → PeriodPair) : Prop :=
  ∀ t : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls t → ∀ z ∈ t,
    (∀ j, z j ∈ (Ls j).lattice ∨ IsAlgebraic ℚ ((Ls j).weierstrassP (z j))) →
    ∃ w : Fin m → ℂ, (z, w) ∈ perTanId Ls t ∧ AlgVec (w - zetaV Ls z)

/-- `T(B^♮)` is `ℚ̄`-rational for every abelian subvariety `B` (true for all curves over `ℚ̄`). -/
def PerTanRat (Ls : Fin m → PeriodPair) : Prop :=
  ∀ t : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls t → RatPair (perTanId Ls t)

/-- The W88 conclusion for `(V, W, Y)`: some proper `G'` with `δ > τ` and the inequality. -/
def Concl41 (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)) : Prop :=
  ∃ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.Proper ∧
    finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
    (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV Ls M)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
        ((d0 + d1 + m + r : ℕ) - finrank ℂ V : ℤ) ≤
      ((H.δ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
        ((d1 + 2 * (m + r) : ℕ) - rk (Y ⊓ PerV Ls M) : ℤ))

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × ((E₁ × ⋯ × E_m)^♮ pushed out along M)`, under (NR).** -/
def Theorem41Vec : Prop :=
  ∀ (d0 d1 m r : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) → AlgMat M →
    ∀ (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)),
      finrank ℂ V < d0 + d1 + m + r → W ≤ V → RatSubV W →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) →
      -- (NR)
      d1 + 2 * d0 + rk (Y ⊓ PerV Ls M) ≤ 2 * finrank ℂ V →
      Concl41 Ls M V W Y

/-- `Theorem41Vec` with `r ≤ 1`, `LiftAlg Ls` and `V ∩ fibre = 0`. Proved: `LSG.W88.theorem41VecLA`
(`MainVec.lean`). -/
def Theorem41VecLA : Prop :=
  ∀ (d0 d1 m r : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) → AlgMat M →
    r ≤ 1 → LiftAlg Ls →
    ∀ (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)),
      finrank ℂ V < d0 + d1 + m + r → W ≤ V → RatSubV W → V ⊓ fibreV = ⊥ →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) →
      d1 + 2 * d0 + rk (Y ⊓ PerV Ls M) ≤ 2 * finrank ℂ V →
      Concl41 Ls M V W Y

/-- **W88 §5d for the class** ((5.4) with `d₂ = m + r`): a hyperplane `V` satisfying (5.4) contains the
tangent space of a nonzero connected algebraic subgroup. -/
def HyperplaneKappaVec : Prop :=
  ∀ (d0 d1 m r : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ),
    (∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) → AlgMat M →
    r ≤ 1 → LiftAlg Ls → PerTanRat Ls →
    ∀ (V W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r)),
      finrank ℂ V + 1 = d0 + d1 + m + r → W ≤ V → RatSubV W →
      Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M) →
      ((rk Y : ℤ) > ((d1 : ℤ) + 2 * (m + r) - rk (Y ⊓ PerV Ls M)) *
        ((d0 + d1 + m + r : ℤ) - 1 - finrank ℂ W)) →
      ∃ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≠ ⊥ ∧ H.tan ≤ V

/-- The first target is a special case of the full statement. -/
theorem theorem41VecLA_of (h : Theorem41Vec) : Theorem41VecLA :=
  fun d0 d1 m r Ls M hL hM _ _ V W Y hV hWV hW _ hY hYV hNR =>
    h d0 d1 m r Ls M hL hM V W Y hV hWV hW hY hYV hNR

end LSG.W88.Vec
