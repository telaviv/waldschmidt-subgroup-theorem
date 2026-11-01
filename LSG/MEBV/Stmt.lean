/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Geom
import LSG.MEB.Stmt
import StrongSix.M2.Filtered
import LSG.W88.Statement

/-!
# The statement `MultEstV` (M2.md §M2.4a; frozen)

Philippon's multiplicity estimate on `G = G_a^{d₀} × G_m^{d₁} × G₂`, where `G₂` is the push-out of
`B₁^♮ × ⋯ × B_m^♮` (vector-extension blocks, one `G_a` fibre each) along an **onto** `M : ℂ^m → ℂ^r`. As in
`LSG.MEV.MultEstVec`, `G` is modelled as the quotient `G̃_r / K_M` of

  `G̃_r = G_a^{d₀+r} × G_m^{d₁} × B₁^♮ × ⋯ × B_m^♮`

by the vector subgroup `K_M = {(0, −Mv; 0; 0, v) : v ∈ ℂ^m}` (`kerK M`): the last `r` additive coordinates are the
vector part of `G₂`. M2 uses `d₀ = 0`, `r = 1`, `M = bᵀ` (`b` an adapted basis), all blocks `A_σ̄^♮`.

The order of vanishing is analytic (MEB's `OrdGtB` form), so W88 §7 needs no bridge; polynomials on `G` are the
`K_M`-invariant ones, stated on the lift (`InvarKV`).

* `PerG d₀ d₁ B = 0 × 2πiℤ^{d₁} × ∏_k perV_k`: the periods of `G̃`.
* `perTanId B t = span_ℂ {(λ, η(λ)) : λ ∈ t ∩ ∏ per_k}`: the Lie algebra of `B̃ = B^♮`-image for an abelian
  subvariety `B ⊆ ∏ A_k` with tangent space `t`.
* `vecIncl`, `torIncl`, `g2Incl`; **`tanOfV Γ U t = Γ ⊕ U^⊥ ⊕ perTanId t`**: the tangent space of the member
  `T_U × (B̃ + Γ)` of the subgroup family (VECEXT §1.2, `LSG.MEV.SubgroupPreV.tan`).
* `wk k`, `IsHomV`, `sigB`, **`OrdGtV`** (analytic, at some lift), `prLead`, `prB`, `kvec`, `kerK`,
  **`InvarKV`**, `TrailDeg`.
* **`ObstrDataBV d₀ r d₁ B M`**: the obstruction `G̃′ ⊇ K_M`: the data `(U, t, Γ)` with `t` rational for the base
  periods (`t_rat`), the subgroup `grp = zcl (exp T̃′)`, `T̃′ = tanOfV Γ U t`, with Lie algebra `T̃′`, `K_M ⊆ T̃′`,
  and **`htil`** (`exp⁻¹(grp) ⊆ ℚ ⊗ (T̃′ + PerG)`, as `LSG.MEB.ObstrDataB.htil`). W88's projection exponents
  `t0 = dim pr_{G_a^{d₀}} T̃′`, `t2 = dim (T̃′ ∩ ker pr_{G_a^{d₀}} ∩ ker pr_{G_m})` (it counts `K_M`).
* **`MultEstV`**: the statement.
-/

open MvPolynomial Module LSG.W88

namespace LSG.MEBV

open LSG.MEB (Blk DfunB IsRatSub perAb)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock}

/-! ### Periods -/

variable (d₀ d₁ B) in
/-- **The periods** `Ω(G̃) = ker expG = 0 × 2πiℤ^{d₁} × ∏_k perV_k`. -/
def PerG : AddSubgroup (Tan d₀ d₁ B) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * Complex.I * k) ∧
    ∀ k, p.blkV k ∈ (B k).perV}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun k => (B k).perV.add_mem (hp.2.2 k) (hq.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    obtain ⟨b, hb⟩ := hq.2.1 i
    exact ⟨a + b, by change p.2.1 i + q.2.1 i = _; rw [ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨rfl, fun _ => ⟨0, by simp⟩, fun k => (B k).perV.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun k => (B k).perV.neg_mem (hp.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    exact ⟨-a, by change -p.2.1 i = _; rw [ha]; push_cast; ring⟩

variable (B) in
/-- The base periods `∏_k per_k` (MEB's `perAb` of the base blocks). -/
abbrev perBase : AddSubgroup (∀ k, Fin (B k).g → ℂ) := perAb fun k => (B k).base

variable (B) in
/-- **`perTanId t`**: the `ℂ`-span of the periods `(λ, η(λ))` of `∏ B_k^♮` with base part in `t`. -/
def perTanId (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    Submodule ℂ ((∀ k, Fin (B k).g → ℂ) × (Fin m → ℂ)) :=
  Submodule.span ℂ {p | p.1 ∈ t ∧ ∀ k, (p.1 k, p.2 k) ∈ (B k).perV}

/-! ### The tangent space of a member of the subgroup family -/

/-- `(a, w) ↦ (a, 0, 0, w)`: the vector group `G_a^{d₀} × (fibres)`. -/
def vecIncl : ((Fin d₀ → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] Tan d₀ d₁ B where
  toFun x := (x.1, 0, 0, x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- `b ↦ (0, b, 0, 0)`: the torus. -/
def torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] Tan d₀ d₁ B where
  toFun b := (0, b, 0, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- `(z, w) ↦ (0, 0, z, w)`: the product of the `B_k^♮`. -/
def g2Incl : ((∀ k, Fin (B k).g → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] Tan d₀ d₁ B where
  toFun x := (0, 0, x.1, x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

variable (d₀ d₁ B) in
/-- **`T_{G′} = Γ + U^⊥ + perTanId t`**, the tangent space of `T_U × (B̃ + Γ)`. -/
def tanOfV (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ))) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Submodule ℂ (Tan d₀ d₁ B) :=
  gam.map vecIncl ⊔ (torusLie U).map torIncl ⊔ (perTanId B t).map g2Incl

/-! ### Degrees, points, orders -/

/-- The weight of the `k`-th block. -/
def wk (k : Fin m) : Var d₀ d₁ B → ℕ
  | .e k' _ => if k' = k then 1 else 0
  | _ => 0

/-- `P` is homogeneous of degree `d k` in the `k`-th block (its `X`- and `T`-coordinates), for every `k`. -/
def IsHomV (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ) : Prop :=
  ∀ k, P.IsWeightedHomogeneous (wk k) (d k)

/-- Sums of `n` points of `S`. -/
def sigB (S : Finset (GPt d₀ d₁ B)) (n : ℕ) : Set (GPt d₀ d₁ B) :=
  {g | ∃ σ : Fin n → GPt d₀ d₁ B, (∀ i, σ i ∈ S) ∧ g = ∑ i, σ i}

/-- **Analytic order `> n` along `W` at `p`** (at some lift `u` of `p`): W88's `VanishAlong` for `P ∘ liftV`. -/
def OrdGtV (W : Submodule ℂ (Tan d₀ d₁ B)) (P : MvPolynomial (Var d₀ d₁ B) ℂ) (n : ℕ)
    (p : GPt d₀ d₁ B) : Prop :=
  ∃ u : Tan d₀ d₁ B, expG d₀ d₁ B u = p ∧ ∀ w ∈ W, ∀ k ≤ n,
    iteratedDeriv k (fun s : ℂ => eval (liftV (u + s • w)) P) 0 = 0

/-! ### The push-out -/

/-- The projection to `ℂ^{d₀}` (the leading additive coordinates of `G̃_r`). -/
def prLead : Tan (d₀ + r) d₁ B →ₗ[ℂ] (Fin d₀ → ℂ) where
  toFun p i := p.1 (Fin.castAdd r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection to the toric coordinates. -/
def prB : Tan d₀ d₁ B →ₗ[ℂ] (Fin d₁ → ℂ) where
  toFun p := p.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `v ↦ (0, −Mv; 0; 0, v)`. -/
def kvec (M : Matrix (Fin r) (Fin m) ℂ) : (Fin m → ℂ) →ₗ[ℂ] Tan (d₀ + r) d₁ B where
  toFun v := (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec v), 0, 0, v)
  map_add' v v' := by
    refine Prod.ext ?_ (Prod.ext (by simp) (Prod.ext (by simp) rfl))
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp
    · simp [Matrix.mulVec_add]; ring
  map_smul' c v := by
    refine Prod.ext ?_ (Prod.ext (by simp) (Prod.ext (by simp) rfl))
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Matrix.mulVec_smul]

variable (d₀ d₁ B) in
/-- `K_M`, the tangent space of the kernel of `G̃_r → G`. -/
def kerK (M : Matrix (Fin r) (Fin m) ℂ) : Submodule ℂ (Tan (d₀ + r) d₁ B) :=
  LinearMap.range (kvec (d₀ := d₀) (d₁ := d₁) (B := B) M)

/-- **Polynomials on `G`**: invariance of `P ∘ liftV` under translation by `K_M`. (The lift is exact, so for
multihomogeneous `P` this is invariance on all cone representatives.) -/
def InvarKV (M : Matrix (Fin r) (Fin m) ℂ) (P : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) : Prop :=
  ∀ (u : Tan (d₀ + r) d₁ B) (v : Fin m → ℂ), eval (liftV (u + kvec M v)) P = eval (liftV u) P

/-- Degree `≤ D` in the `r` trailing additive variables (the vector part of `G₂`, of degree `D₂`). -/
def TrailDeg (D : ℕ) (P : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) : Prop :=
  ∀ s ∈ P.support, ∑ i : Fin r, s (.x (Fin.natAdd d₀ i)) ≤ D

/-! ### The obstruction -/

/-- **Obstruction data** for `G = G̃_r / K_M`: a member `T_U × (B̃ + Γ)` of the subgroup family of `G̃_r`, with
`t` rational for the base periods, `grp = zcl (exp T̃′)` a Zariski-closed subgroup with Lie algebra
`T̃′ = tanOfV Γ U t ⊇ K_M`, and `exp⁻¹(grp) ⊆ ℚ ⊗ (T̃′ + Ω(G̃))`. -/
structure ObstrDataBV (d₀ r d₁ : ℕ) {m : ℕ} (B : Fin m → VBlock) (M : Matrix (Fin r) (Fin m) ℂ) where
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d₁ → ℚ)
  /-- the base tangent space of the abelian image `B ⊆ ∏ A_k` -/
  t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)
  t_rat : IsRatSub (perBase B) t
  /-- the vector part, inside `G_a^{d₀+r} × (fibres)` -/
  gam : Submodule ℂ ((Fin (d₀ + r) → ℂ) × (Fin m → ℂ))
  /-- the subgroup itself -/
  grp : Set (GPt (d₀ + r) d₁ B)
  grp_eq : grp = zcl (expG (d₀ + r) d₁ B '' (tanOfV (d₀ + r) d₁ B gam U t : Set (Tan (d₀ + r) d₁ B)))
  grp_sub : IsSubgroupG grp
  grp_closed : IsZClosed grp
  /-- `T̃′` is the Lie algebra of `grp` -/
  lie : ∀ v : Tan (d₀ + r) d₁ B,
    (∀ c : ℂ, expG (d₀ + r) d₁ B (c • v) ∈ grp) ↔ v ∈ tanOfV (d₀ + r) d₁ B gam U t
  /-- `G̃′ ⊇ K_M`, i.e. `G̃′` is the preimage of a subgroup of `G` -/
  ker_le : kerK d₀ d₁ B M ≤ tanOfV (d₀ + r) d₁ B gam U t
  /-- the analytic preimage of `grp` lies in `ℚ ⊗ (T̃′ + Ω(G̃))` (W88's `htil_le_span`) -/
  htil : ∀ u : Tan (d₀ + r) d₁ B, expG (d₀ + r) d₁ B u ∈ grp →
    ∃ N : ℕ, 0 < N ∧ N • u ∈ (tanOfV (d₀ + r) d₁ B gam U t).toAddSubgroup ⊔ PerG (d₀ + r) d₁ B

namespace ObstrDataBV

variable {M : Matrix (Fin r) (Fin m) ℂ} (O : ObstrDataBV d₀ r d₁ B M)

/-- The tangent space `T̃′ = Γ + U^⊥ + perTanId t`. -/
def tan : Submodule ℂ (Tan (d₀ + r) d₁ B) := tanOfV (d₀ + r) d₁ B O.gam O.U O.t

/-- `G′ ≠ G`. -/
def Proper : Prop := O.tan ≠ ⊤

/-- `t₀ = dim pr_{G_a^{d₀}} T̃′`. -/
noncomputable def t0 : ℕ := finrank ℂ (O.tan.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)))

/-- `t₂ = dim (T̃′ ∩ ker pr_{G_a^{d₀}} ∩ ker pr_{G_m})` (base, fibre and trailing additive directions; it
counts `K_M`, of dimension `m`). -/
noncomputable def t2 : ℕ := finrank ℂ ↥(O.tan ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) ⊓
  LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B))))

theorem expG_mem {u : Tan (d₀ + r) d₁ B} (hu : u ∈ O.tan) : expG (d₀ + r) d₁ B u ∈ O.grp := by
  simpa using (O.lie u).mpr hu 1

end ObstrDataBV

/-! ### The statement -/

/-- **The multiplicity estimate for `G = G_a^{d₀} × G_m^{d₁} × ((B₁^♮ × ⋯ × B_m^♮) pushed out along an onto M)`**
(Philippon 1986, Thm. 2.1, constants absorbed), in the model `G = G̃_r / K_M`. `P` is a polynomial on `G`
(`K_M`-invariant), homogeneous of degree `D₂` in each block `B_k^♮`, of degree `≤ D₀` in the additive variables and
`≤ D₂` in the `r` trailing ones, `≤ D₁` in the toric ones, `P ∉ IGsem`, and of analytic order `> n T` along `W`
at every point of `Σ(n)`, `n = dim G̃_r = d₀ + r + d₁ + Σ_k (g_k + 1)`. Then there is a proper obstruction
`G̃′ ⊇ K_M` with
`T^c · |F| · D₀^{t₀} D₁^{t₁} D₂^{t₂} ≤ C · D₀^{d₀} D₁^{d₁} D₂^{Σ_k (g_k + 1) + r}`
for every `F ⊆ S` of points pairwise inequivalent modulo `G̃′`, `c = dim W − dim (W ∩ T̃′)`, `t₁ = d₁ − dim U`.
(`t₂` counts `K_M`; dividing by `D₂^m` gives W88's `D₂^{d₂}`, `d₂ = Σ_k g_k + r`.) -/
def MultEstV : Prop :=
  ∀ (d₀ r d₁ m : ℕ) (B : Fin m → VBlock) (M : Matrix (Fin r) (Fin m) ℂ),
    Function.Surjective M.mulVec → ∃ C : ℕ,
    ∀ (W : Submodule ℂ (Tan (d₀ + r) d₁ B)) (S : Finset (GPt (d₀ + r) d₁ B))
      (P : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPt (d₀ + r) d₁ B) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ StrongSix.M2.FLE ℂ blk (DfunB D₀ D₁ D₂) → TrailDeg (d₀ := d₀) D₂ P → InvarKV M P →
      P ∉ IGsem (d₀ + r) d₁ B →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sigB S (dimG (d₀ + r) d₁ B), OrdGtV W P (dimG (d₀ + r) d₁ B * T) σ) →
      ∃ O : ObstrDataBV d₀ r d₁ B M, O.Proper ∧
        ∀ F : Finset (GPt (d₀ + r) d₁ B), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
              D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ O.t2 ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, ((B k).g + 1) + r)

end LSG.MEBV
