/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement
import LSG.W88.MStarCopy
import LSG.JacAn3.Normalize

/-!
# W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × A^r` with rational-period `A`-parts: the statement

`A = Jac(y² = 4x⁵ + 1)` is the abelian surface of A2/A3. Its tangent space is `ℂ²` in the eigen-coordinates
`(z₀, z₁)` dual to `dx/y`, `x dx/y`. The statements below see `A` only through `Λ = latt = ⟨perVec e : e < 4⟩`, an
`ℝ`-basis lattice (`latBasis`) of periods of these differentials. **`latt` is a finite-index sublattice of `ker E`**:
`latt ≤ kerE` (`lattice_le_ker`, `latt_le_kerE`) and `kerE ⊆ ℚ·latt` (`isNsmulIn_latt_kerE`, `AbVarPer.lean`).
Whether `latt` is the whole period lattice is not decided; every use below depends only on `ℚ·latt` (or on
`Y ∩ latt^r` for `Y` with `A`-parts already in `latt^r`), so the index does not matter (REVIEW_STATEMENT_ABVAR §1).

## The group, its logarithms and periods

`T_G = ℂ^{d₀} × ℂ^{d₁} × (ℂ²)^r` (`TanA`).
* **`LamA`** (logarithms of algebraic points, restricted to rational-period `A`-parts): `a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`,
  and every `A`-part in `Λ`. On these, `exp_A` is the origin (`latt_le_kerE`), so no algebraicity of points of `A` is
  needed. `LamA` is an additive subgroup.
* **`PerA`** (periods): `0 × 2πiℤ^{d₁} × Λ^r`, a finite-index subgroup of `Ω(G) = ker exp_G`, with the same
  `ℚ`-span.

**Why rational-period `A`-parts suffice** (`hyperplaneKappaOn_of_scale`). In `lean_mstar`, `lam = span_ℚ lamGen`
with generators logarithms of algebraic numbers in one toric slot and periods of `A^r`. A finite family in
`span_ℚ S`, `S ⊆ L` (a subgroup), has a common denominator `M` with `M y_i ∈ L` (`exists_nsmul_mem_closure`);
`M y_i ∈ V`, `span_ℚ (M y) = span_ℚ y` (so `rk` and `κ = dim (span_ℚ y ⊓ per)` are unchanged), and the conclusion
of `HyperplaneKappa` does not involve `y`. So the `§5d` hypothesis for `lam = span_ℚ LamA` follows from the one for
`lam = LamA`.

## Connected algebraic subgroups (`SubgroupDataA`)

`G' = H₀ × T_U × B` with `h₀ ⊂ ℂ^{d₀}` a `ℚ̄`-rational subspace, `T_U` the subtorus with Lie algebra `U^⊥`, and
`B ⊂ A^r` an abelian subvariety, given by its tangent `t ⊂ (ℂ²)^r` with `t ∩ Λ^r` spanning `t` over `ℝ`
(`IsAbelianTangentA`; complex subtori of `A^r` are abelian subvarieties and conversely).

## Toric injectivity

`TorInjA V`: every `v ∈ V ∩ span_ℚ Ω(G)` with zero toric part is `0` (`lean_mstar`'s `TorInj`, REVIEW_TORINJ.md,
PLAN.md "lean_mstar TorInj interface"). It is a premise of both forms below.

## The statements

* **`Theorem41AbVarPer`**: W88 Thm 4.1 (with (NR)) for `G`, as `Theorem41Abelian` (`Statement.lean`) with `d₂ = 2r`.
  Proved: `LSG.W88.theorem41AbVarPer` (`AbVarThm41.lean`, from the block-generic `theorem41B_of`).
* **`HyperplaneKappaAbVar`**: the W88 §5d form, `HyperplaneKappaOnLsg (gmLsgA d₀ d₁ r) TorInjA`, for the group model
  `gmLsgA` (`lean_mstar`'s `GroupModel`, copied in `MStarCopy.lean`). Proved: `LSG.W88.hyperplaneKappaAbVar`
  (`AbVar5dFinal.lean`).

**Scope.** Both forms are W88 for `G_a^{d₀} × G_m^{d₁} × A^r` restricted to toric-injective `V` and to subgroups `Y`
whose `A`-components are periods (by `hyperplaneKappaOn_spanLam`, rational periods, i.e. torsion points of `A^r`).
For `G = A^r` alone (`d₀ = d₁ = 0`) they are empty: `TorInjA` forces `V ∩ LamA = 0`, so no nonzero `y` exists and the
premise of (5.4) never holds. Likewise the `d₁ = 0` case says nothing about non-torsion points. Do not cite them as
"W88 for `A^r`" (REVIEW_STATEMENT_ABVAR m6).
-/

open Complex Module

namespace LSG.W88

open LSG.JacAn

/-- The tangent space `ℂ^{d₀} × ℂ^{d₁} × (ℂ²)^r` of `G_a^{d₀} × G_m^{d₁} × A^r`. -/
abbrev TanA (d0 d1 r : ℕ) := (Fin d0 → ℂ) × (Fin d1 → ℂ) × (Fin r → Fin 2 → ℂ)

variable {d0 d1 r : ℕ}

/-- `A`-parts with algebraic coordinates. -/
def AlgVecA (u : Fin r → Fin 2 → ℂ) : Prop := ∀ j k, IsAlgebraic ℚ (u j k)

/-- The `ℚ̄`-structure of `T_G`. -/
def AlgTanA (p : TanA d0 d1 r) : Prop := AlgVec p.1 ∧ AlgVec p.2.1 ∧ AlgVecA p.2.2

/-- `ℚ̄`-rational subspaces of `T_G`. -/
def RationalOverQbarA (W : Submodule ℂ (TanA d0 d1 r)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgTanA w}

/-- **The logarithms of algebraic points with `A`-parts in `Λ`** (an additive subgroup). -/
def LamA : AddSubgroup (TanA d0 d1 r) where
  carrier := {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧ ∀ j, p.2.2 j ∈ latt}
  add_mem' {p q} hp hq := by
    refine ⟨fun i => (hp.1 i).add (hq.1 i), fun i => ?_, fun j => latt.add_mem (hp.2.2 j) (hq.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
    rw [Complex.exp_add]; exact (hp.2.1 i).mul (hq.2.1 i)
  zero_mem' := ⟨fun _ => isAlgebraic_zero, fun _ => by simpa using isAlgebraic_one,
    fun _ => latt.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨fun i => (hp.1 i).neg, fun i => ?_, fun j => latt.neg_mem (hp.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
    rw [Complex.exp_neg]; exact (hp.2.1 i).inv

/-- **The period group** `Ω(G) = 0 × 2πiℤ^{d₁} × Λ^r`. -/
def PerA : AddSubgroup (TanA d0 d1 r) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * I * k) ∧ ∀ j, p.2.2 j ∈ latt}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun j => latt.add_mem (hp.2.2 j) (hq.2.2 j)⟩
    obtain ⟨k, hk⟩ := hp.2.1 i
    obtain ⟨l, hl⟩ := hq.2.1 i
    exact ⟨k + l, by show p.2.1 i + q.2.1 i = _; rw [hk, hl]; push_cast; ring⟩
  zero_mem' := ⟨rfl, fun _ => ⟨0, by simp⟩, fun _ => latt.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun j => latt.neg_mem (hp.2.2 j)⟩
    obtain ⟨k, hk⟩ := hp.2.1 i
    exact ⟨-k, by show -p.2.1 i = _; rw [hk]; push_cast; ring⟩

/-- **`exp_A` is the origin on `Λ`**, for every base and germ radius of A2 (`lattice_le_ker`). -/
theorem latt_le_kerE {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂}
    {hx : p.1 ≠ p.2} (G : GermRad A hp hx) : latt ≤ kerE G := (lattice_le_ker G).2.1

/-- `t ⊂ (ℂ²)^r` is the tangent space of an abelian subvariety of `A^r`: `t ∩ Λ^r` spans `t` over `ℝ`. -/
def IsAbelianTangentA (t : Submodule ℂ (Fin r → Fin 2 → ℂ)) : Prop :=
  (t.restrictScalars ℝ : Submodule ℝ (Fin r → Fin 2 → ℂ)) =
    Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ latt}

/-- Data of a connected algebraic subgroup `G' = H₀ × T_U × B` of `G_a^{d₀} × G_m^{d₁} × A^r`. -/
structure SubgroupDataA (d0 d1 r : ℕ) where
  h0 : Submodule ℂ (Fin d0 → ℂ)
  U : Submodule ℚ (Fin d1 → ℚ)
  t : Submodule ℂ (Fin r → Fin 2 → ℂ)
  h0_rat : RationalOverQbar h0
  t_ab : IsAbelianTangentA t

namespace SubgroupDataA

variable (H : SubgroupDataA d0 d1 r)

/-- The tangent space `T_{G'} = h₀ × U^⊥ × t`. -/
def tan : Submodule ℂ (TanA d0 d1 r) := H.h0.prod ((torusLie H.U).prod H.t)

/-- `δ₀ = codim h₀`. -/
noncomputable def δ0 : ℕ := d0 - finrank ℂ H.h0
/-- `δ₁ = dim U`. -/
noncomputable def δ1 : ℕ := finrank ℚ H.U
/-- `δ₂ = codim t = 2r − dim t`. -/
noncomputable def δ2 : ℕ := 2 * r - finrank ℂ H.t
/-- `δ = codim G'`. -/
noncomputable def δ : ℕ := H.δ0 + H.δ1 + H.δ2

/-- `G' ≠ G`. -/
def Proper : Prop := H.δ ≠ 0

end SubgroupDataA

/-- **Toric injectivity** of `V`: a vector of `V ∩ span_ℚ Ω(G)` with zero toric part is `0`. -/
def TorInjA (V : Submodule ℂ (TanA d0 d1 r)) : Prop :=
  ∀ v ∈ V, v ∈ Submodule.span ℚ ((PerA : AddSubgroup (TanA d0 d1 r)) : Set (TanA d0 d1 r)) → v.2.1 = 0 → v = 0

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × A^r`, rational-period `A`-parts, under (NR) and (TorInj).**
Proved as `LSG.W88.theorem41AbVarPer` (`AbVarThm41.lean`). -/
def Theorem41AbVarPer : Prop :=
  ∀ (d0 d1 r : ℕ) (V W : Submodule ℂ (TanA d0 d1 r)) (Y : AddSubgroup (TanA d0 d1 r)),
    finrank ℂ V < d0 + d1 + 2 * r → W ≤ V → RationalOverQbarA W →
    Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamA) → TorInjA V →
    -- (NR)
    d1 + 2 * d0 + rk (Y ⊓ PerA) ≤ 2 * finrank ℂ V →
    ∃ H : SubgroupDataA d0 d1 r, H.Proper ∧
      finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
      (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerA)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
          ((d0 + d1 + 2 * r : ℕ) - finrank ℂ V : ℤ) ≤
        ((H.δ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
          ((d1 + 2 * (2 * r) : ℕ) - rk (Y ⊓ PerA) : ℤ))

/-! ## The W88 §5d form -/

open MStarCopy

/-- `HyperplaneKappa` with an extra premise `good V` on the hyperplane. **Equivalent to `lean_mstar`'s
`HyperplaneKappaOn` (`MStarCopy.HyperplaneKappaOn`, `MStarCopyAbVar.lean`) up to premise order**, but not
definitionally equal: here `good V` comes after `G.Rational W`, in lean_mstar right after the binders.
`hkOn_transport` (`AbVarMStar.lean`) converts between the two orders. -/
def HyperplaneKappaOnLsg {Vt : Type*} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt] (G : GroupModel Vt)
    (good : Submodule ℂ Vt → Prop) : Prop :=
  ∀ (V W : Submodule ℂ Vt) (m : ℕ) (y : Fin m → Vt),
    finrank ℂ V + 1 = finrank ℂ Vt → W ≤ V → G.Rational W → good V →
    (∀ i, y i ∈ V ∧ y i ∈ G.lam) →
    ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
      ((G.d₁ : ℤ) + 2 * G.d₂ - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per)) *
        ((finrank ℂ Vt : ℤ) - 1 - finrank ℂ W)) →
    ∃ S : Submodule ℂ Vt, G.sub S ∧ S ≠ ⊥ ∧ S ≤ V

/-- **The group model of `G_a^{d₀} × G_m^{d₁} × A^r`** with `lam = LamA`. Sound by `latt_le_kerE` (`exp_A = 0` on
`Λ`), `per = span_ℚ Ω(G)`, and the classification of connected algebraic subgroups `H₀ × T_U × B`. -/
noncomputable def gmLsgA (d0 d1 r : ℕ) : GroupModel (TanA d0 d1 r) where
  d₁ := d1
  d₂ := 2 * r
  alg := AlgTanA
  lam := ((LamA : AddSubgroup (TanA d0 d1 r)) : Set (TanA d0 d1 r))
  per := Submodule.span ℚ ((PerA : AddSubgroup (TanA d0 d1 r)) : Set (TanA d0 d1 r))
  sub := fun S => ∃ H : SubgroupDataA d0 d1 r, S = H.tan

/-- **The W88 §5d hypothesis for `G_a^{d₀} × G_m^{d₁} × A^r`** (toric-injective hyperplanes), with `lam = LamA`:
the `A`-parts of the `y_i` lie in `Λ` (and, by `hyperplaneKappaOn_spanLam`, in `span_ℚ LamA`, i.e. are torsion
points of `A^r`). Empty for `d₀ = d₁ = 0` (module docstring). -/
def HyperplaneKappaAbVar : Prop := ∀ d0 d1 r : ℕ, HyperplaneKappaOnLsg (gmLsgA d0 d1 r) TorInjA

/-! ## The scaling reduction -/

/-- **Common denominators**: a vector of `span_ℚ S` has a positive multiple in the subgroup generated by `S`. -/
theorem exists_nsmul_mem_closure {E : Type*} [AddCommGroup E] [Module ℚ E] {S : Set E} {v : E}
    (hv : v ∈ Submodule.span ℚ S) : ∃ M : ℕ, 0 < M ∧ M • v ∈ AddSubgroup.closure S := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, hx⟩ := hx
    obtain ⟨M₂, h₂, hy⟩ := hy
    refine ⟨M₁ * M₂, Nat.mul_pos h₁ h₂, ?_⟩
    rw [smul_add, mul_comm M₁ M₂, mul_smul, mul_comm M₂ M₁, mul_smul]
    exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hx _) (AddSubgroup.nsmul_mem _ hy _)
  | smul q x _ hx =>
    obtain ⟨M, hM, hx⟩ := hx
    refine ⟨q.den * M, Nat.mul_pos q.den_pos hM, ?_⟩
    have : (q.den * M) • (q • x) = q.num • (M • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ M, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        smul_smul]
      congr 1
      push_cast
      rw [mul_comm (q.den : ℚ), mul_assoc, Rat.den_mul_eq_num]; ring
    rw [this]
    exact AddSubgroup.zsmul_mem _ hx _

/-- A finite family in `span_ℚ S` has a common positive multiple in the subgroup generated by `S`. -/
theorem exists_common_nsmul {E : Type*} [AddCommGroup E] [Module ℚ E] {S : Set E} {m : ℕ} {y : Fin m → E}
    (hy : ∀ i, y i ∈ Submodule.span ℚ S) : ∃ M : ℕ, 0 < M ∧ ∀ i, M • y i ∈ AddSubgroup.closure S := by
  choose M hM hMy using fun i => exists_nsmul_mem_closure (hy i)
  refine ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i, fun i => ?_⟩
  have hdvd : M i ∣ ∏ j, M j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hMy i) _

lemma span_range_nsmul {E : Type*} [AddCommGroup E] [Module ℚ E] {m M : ℕ} (hM : 0 < M) (y : Fin m → E) :
    Submodule.span ℚ (Set.range fun i => M • y i) = Submodule.span ℚ (Set.range y) := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show M • y i ∈ _
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : y i = (M : ℚ)⁻¹ • (M • y i) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hM', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The scaling reduction.** If `lam ⊆ span_ℚ S` with `S ⊆ L` (a subgroup), the `§5d` hypothesis for the model with
`lam := L` implies it for the original model (same `d₁, d₂, alg, per, sub`, and any premise `good`). -/
theorem hyperplaneKappaOn_of_scale {Vt : Type*} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt]
    (G : GroupModel Vt) (good : Submodule ℂ Vt → Prop) {S : Set Vt} {L : AddSubgroup Vt}
    (hlam : G.lam ⊆ Submodule.span ℚ S) (hS : S ⊆ L)
    (h : HyperplaneKappaOnLsg { G with lam := (L : Set Vt) } good) : HyperplaneKappaOnLsg G good := by
  intro V W m y hV hWV hW hgood hy hrk
  obtain ⟨M, hM, hMy⟩ := exists_common_nsmul (S := S) (fun i => hlam (hy i).2)
  have hcl : AddSubgroup.closure S ≤ L := (AddSubgroup.closure_le L).mpr hS
  have hspan := span_range_nsmul hM y
  refine h V W m (fun i => M • y i) hV hWV hW hgood (fun i => ⟨V.toAddSubgroup.nsmul_mem (hy i).1 M,
    hcl (hMy i)⟩) ?_
  rw [hspan]
  exact hrk

/-- **The `lean_mstar`-shaped model** (`lam = span_ℚ LamA`, which contains `span_ℚ lamGen`) reduces to `gmLsgA`. -/
theorem hyperplaneKappaOn_spanLam (d0 d1 r : ℕ)
    (h : HyperplaneKappaOnLsg (gmLsgA d0 d1 r) TorInjA) :
    HyperplaneKappaOnLsg { gmLsgA d0 d1 r with
      lam := (Submodule.span ℚ ((LamA : AddSubgroup (TanA d0 d1 r)) : Set (TanA d0 d1 r)) : Set (TanA d0 d1 r)) }
      TorInjA :=
  hyperplaneKappaOn_of_scale _ TorInjA (S := (LamA : AddSubgroup (TanA d0 d1 r))) (L := LamA) (fun _ hv => hv)
    (fun _ hv => hv) (by
      have e : ({ ({ gmLsgA d0 d1 r with lam := (Submodule.span ℚ ((LamA : AddSubgroup (TanA d0 d1 r)) :
          Set (TanA d0 d1 r)) : Set (TanA d0 d1 r)) } : GroupModel (TanA d0 d1 r)) with
          lam := ((LamA : AddSubgroup (TanA d0 d1 r)) : Set (TanA d0 d1 r)) } : GroupModel (TanA d0 d1 r)) =
          gmLsgA d0 d1 r := rfl
      rw [e]; exact h)

end LSG.W88
