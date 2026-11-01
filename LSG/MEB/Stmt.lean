/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Geom
import StrongSix.M2.Filtered
import LSG.W88.Statement

/-!
# The statement `MultEstB` (STAGE_A4 §1.2; frozen in A4.0)

Philippon's multiplicity estimate on `G = G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m` for a family of abelian blocks, in the
form W88 §7 consumes (`LSG.W88.theorem41Abelian_of` is the template for `MultEstAb`).

* `Per d₀ d₁ B = 0 × 2πiℤ^{d₁} × ∏_k per_k` and `perAb B = ∏_k per_k`.
* `wk k`, `IsHomB P d`: `P` is homogeneous of degree `d k` in the `k`-th block. `DfunB D₀ D₁ D₂`: block degrees.
* `sigB S r`: sums of `r` points of `S`.
* **`OrdGtB W P n p`**: *analytic* order `> n` along `W` at `p`. Along some lift `u` of `p` and every `w ∈ W`, the
  Taylor coefficients of degree `≤ n` of `s ↦ P(liftB (u + s w))` vanish. This is W88's `VanishAlong` for
  `Φ = P ∘ liftB` at `u`, with `k ≤ n` in place of `k < T`, so the consumer needs no bridge (compare
  `LSG.W88.ordGt_of_vanishAlong`).
* `tanOf h₀ U t = h₀ × U^⊥ × t`.
* **`ObstrDataB`**: the obstruction subgroup. Compared with `LSG.ME.ObstrData` it has `t ⊆ ∏ ℂ^{g_k}` with `IsRatSub`
  for `perAb`, and one extra field **`htil`**: `exp⁻¹(grp) ⊆ (1/N)(T_{G′} + Per)`. That is W88's `htil_le_span`,
  delivered by the core so that the §7 counting (`exists_inequiv_grid`) needs no subgroup layer.
* **`MultEstB`**: the statement. The hypothesis `P ∉ IGsem` follows from `P ∘ liftB ≢ 0` (`notMem_IGsem_of_eval_ne`).
-/

open MvPolynomial Module LSG.W88

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

variable (B) in
/-- The period lattice `∏_k per_k` of the abelian part. -/
def perAb : AddSubgroup (∀ k, Fin (B k).g → ℂ) := AddSubgroup.pi Set.univ fun k => (B k).per

variable (d₀ d₁ B) in
/-- **The periods** `Ω(G) = ker expG = 0 × 2πiℤ^{d₁} × ∏_k per_k`. -/
def Per : AddSubgroup (Tan d₀ d₁ B) where
  carrier := {p | p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * Complex.I * k) ∧ ∀ k, p.2.2 k ∈ (B k).per}
  add_mem' {p q} hp hq := by
    refine ⟨by simp [hp.1, hq.1], fun i => ?_, fun k => (B k).per.add_mem (hp.2.2 k) (hq.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    obtain ⟨b, hb⟩ := hq.2.1 i
    exact ⟨a + b, by change p.2.1 i + q.2.1 i = _; rw [ha, hb]; push_cast; ring⟩
  zero_mem' := ⟨rfl, fun _ => ⟨0, by simp⟩, fun k => (B k).per.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨by simp [hp.1], fun i => ?_, fun k => (B k).per.neg_mem (hp.2.2 k)⟩
    obtain ⟨a, ha⟩ := hp.2.1 i
    exact ⟨-a, by change -p.2.1 i = _; rw [ha]; push_cast; ring⟩

/-- The weight of the `k`-th block. -/
def wk (k : Fin m) : Var d₀ d₁ B → ℕ
  | .e k' _ => if k' = k then 1 else 0
  | _ => 0

/-- `P` is homogeneous of degree `d k` in the `k`-th block, for every `k`. -/
def IsHomB (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ) : Prop :=
  ∀ k, P.IsWeightedHomogeneous (wk k) (d k)

/-- The block degrees `(D₀, D₁, D₂, …, D₂)`. -/
def DfunB (D₀ D₁ D₂ : ℕ) : Blk m → ℕ
  | .x => D₀
  | .yz => D₁
  | .e _ => D₂

/-- Sums of `r` points of `S`. -/
def sigB (S : Finset (GPt d₀ d₁ B)) (r : ℕ) : Set (GPt d₀ d₁ B) :=
  {g | ∃ σ : Fin r → GPt d₀ d₁ B, (∀ i, σ i ∈ S) ∧ g = ∑ i, σ i}

/-- **Analytic order `> n` along `W` at `p`** (at some lift `u` of `p`): W88's `VanishAlong` for `P ∘ liftB`. -/
def OrdGtB (W : Submodule ℂ (Tan d₀ d₁ B)) (P : MvPolynomial (Var d₀ d₁ B) ℂ) (n : ℕ)
    (p : GPt d₀ d₁ B) : Prop :=
  ∃ u : Tan d₀ d₁ B, expG d₀ d₁ B u = p ∧ ∀ w ∈ W, ∀ k ≤ n,
    iteratedDeriv k (fun s : ℂ => eval (liftB (u + s • w)) P) 0 = 0

/-- The tangent space `h₀ × U^⊥ × t`. -/
def tanOf (h0 : Submodule ℂ (Fin d₀ → ℂ)) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Submodule ℂ (Tan d₀ d₁ B) :=
  h0.prod ((torusLie U).prod t)

variable (d₀ d₁ B) in
/-- **Obstruction data**: a connected algebraic subgroup `G′` with tangent space `h₀ × U^⊥ × t`, as a set
`grp = zcl (exp (h₀ × U^⊥ × t))`. -/
structure ObstrDataB where
  /-- the additive part -/
  h0 : Submodule ℂ (Fin d₀ → ℂ)
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d₁ → ℚ)
  /-- the tangent space of the abelian part -/
  t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)
  t_rat : IsRatSub (perAb B) t
  /-- the subgroup itself -/
  grp : Set (GPt d₀ d₁ B)
  grp_eq : grp = zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set (Tan d₀ d₁ B)))
  grp_sub : IsSubgroupG grp
  grp_closed : IsZClosed grp
  /-- `T_{G′}` is the Lie algebra of `grp` -/
  lie : ∀ v : Tan d₀ d₁ B, (∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ grp) ↔ v ∈ tanOf h0 U t
  /-- the analytic preimage of `grp` lies in `ℚ ⊗ (T_{G′} + Ω(G))` (W88's `htil_le_span`) -/
  htil : ∀ u : Tan d₀ d₁ B, expG d₀ d₁ B u ∈ grp →
    ∃ N : ℕ, 0 < N ∧ N • u ∈ (tanOf h0 U t).toAddSubgroup ⊔ Per d₀ d₁ B

namespace ObstrDataB

variable (O : ObstrDataB d₀ d₁ B)

/-- The tangent space `T_{G′} = h₀ × U^⊥ × t`. -/
def tan : Submodule ℂ (Tan d₀ d₁ B) := tanOf O.h0 O.U O.t

/-- `G′ ≠ G`. -/
def Proper : Prop := O.tan ≠ ⊤

theorem expG_mem {u : Tan d₀ d₁ B} (hu : u ∈ O.tan) : expG d₀ d₁ B u ∈ O.grp := by
  simpa using (O.lie u).mpr hu 1

end ObstrDataB

/-! ### The statement -/

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m`** (Philippon 1986, Thm. 2.1, constants
absorbed). `P` is homogeneous of degree `D₂` in each block, of block degrees `≤ (D₀, D₁, D₂)`, `P ∉ IGsem`, and of
analytic order `> n T` along `W` at every point of `Σ(n)`, `n = dim G = d₀ + d₁ + Σ g_k` (change request CR1,
STAGE_A4 §6.5). Then there is a proper obstruction
`G′` with `T^c · |F| · D₀^{t₀} D₁^{t₁} D₂^{t₂} ≤ C · D₀^{d₀} D₁^{d₁} D₂^{Σ g_k}` for every `F ⊆ S` of points pairwise
inequivalent modulo `G′`, `c = dim W − dim (W ∩ T_{G′})`, `t₀ = dim h₀`, `t₁ = d₁ − dim U`, `t₂ = dim t`. -/
def MultEstB : Prop :=
  ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ C : ℕ,
    ∀ (W : Submodule ℂ (Tan d₀ d₁ B)) (S : Finset (GPt d₀ d₁ B))
      (P : MvPolynomial (Var d₀ d₁ B) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPt d₀ d₁ B) ∈ S → IsHomB P (fun _ => D₂) →
      P ∈ StrongSix.M2.FLE ℂ blk (DfunB D₀ D₁ D₂) → P ∉ IGsem d₀ d₁ B →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sigB S (d₀ + d₁ + ∑ k, (B k).g), OrdGtB W P ((d₀ + d₁ + ∑ k, (B k).g) * T) σ) →
      ∃ O : ObstrDataB d₀ d₁ B, O.Proper ∧
        ∀ F : Finset (GPt d₀ d₁ B), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ finrank ℂ O.h0 *
              D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ finrank ℂ O.t ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, (B k).g)

end LSG.MEB
