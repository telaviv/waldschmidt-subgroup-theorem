/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOntoBridges
import LSG.W88.MStarCopyStd

/-!
# The standard model with a vector-extension factor

`G_a^{d₀} × G_m^{d₁} × ((∏E_j)^♮ pushed out along M)`.

`MStarCopy.gmStdVec d₀ d₁ Ls M` is the group model (lean_mstar's `GroupModel`, verbatim copy in
`MStarCopy.lean`) of `G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of `(E₁ × ⋯ × E_m)^♮`
along the `r × m` matrix `M`, in the coordinates `TanV d₀ d₁ m r` of `StatementVec.lean`:
* `alg = AlgVecV` (all four blocks of coordinates algebraic);
* `lam = LamV Ls M` (logarithms of algebraic points);
* `per = span_ℚ PerV Ls M` (periods `0 × 2πiℤ^{d₁} × {(λ, M η(λ))}`);
* `d₁ = d₁`, `d₂ = m + r` (`dim G₂`; the `G_a^{d₀}` factor does not enter (5.4));
* `sub` = the tangent spaces `T_U^⊥ + T_{B̃} + Γ` of all `SubgroupDataV`.
It mirrors `gmStd` (`MStarCopyStd.lean`): for `r = 0` the data are those of `gmStd` up to the
coordinate change `ℂ^0`. Soundness: as for the class `𝒞` of `StatementVec.lean` (`VECEXT.md` §2).

This file is **not** a copy of a lean_mstar definition (lean_mstar has none yet); lean_mstar should
copy `gmStdVec` verbatim into its namespace, with its own `GroupModel`; the two `HyperplaneKappa`
propositions then unfold to the same term (checked, see `INTERFACE.md`).

## Results
* `hyperplaneKappa_gmStdVec`: `HyperplaneKappa (gmStdVec d₀ d₁ Ls M)` for `r ≤ 1`, algebraic
  invariants, algebraic `M`, `LiftAlg Ls`, `PerTanRat Ls` — `hyperplaneKappaVec_uncond` transported
  along the identity (`hyperplaneKappa_of_iso`).
* `hypStdVecCM`: one CM lattice repeated (`CMLattice` with `KappaOneZero`, lean_mstar's premises of
  `Thm11KappaMGn`), every `M` with `r ≤ 1`; `LiftAlg`/`PerTanRat` from `LSG.CM.liftAlg_block`,
  `perTanRat_block`.
* `hypStdVecCM_eOne`: the case `G_a^{d₀} × G_m^{d₁} × E^♮ × E^m` (`M = eOne m`, the first unit row).

Not covered: `LiftAlg` for mixed families of non-isogenous CM curves (the block splitting
`K5d.mul_mem_of_blockConst` of `K5dNonIsog.lean` reduces it to the blocks, but `liftAlg_block` is
stated for a constant family on `Fin p`, and the reindexing was not done).
-/

open Complex Module

namespace LSG.W88.MStarCopy

open LSG.W88.Vec

/-- **The standard model of `G_a^{d₀} × G_m^{d₁} × ((E₁ × ⋯ × E_m)^♮ pushed out along `M`)`.** -/
noncomputable def gmStdVec (d0 d1 : ℕ) {m r : ℕ} (Ls : Fin m → PeriodPair)
    (M : Matrix (Fin r) (Fin m) ℂ) : GroupModel (LSG.W88.Vec.TanV d0 d1 m r) where
  d₁ := d1
  d₂ := m + r
  alg := LSG.W88.Vec.AlgVecV
  lam := LSG.W88.Vec.LamV Ls M
  per := Submodule.span ℚ
    (LSG.W88.Vec.PerV (d0 := d0) (d1 := d1) Ls M : Set (LSG.W88.Vec.TanV d0 d1 m r))
  sub := fun S => ∃ H : LSG.W88.Vec.SubgroupDataV (d0 := d0) (d1 := d1) Ls M, S = H.tan

end LSG.W88.MStarCopy

namespace LSG.W88

open LSG.W88.Vec LSG.W88.MStarCopy

variable {m r : ℕ}

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × ((∏E_j)^♮ pushed out along `M`)`**, `r ≤ 1`. -/
theorem hyperplaneKappa_gmStdVec {d0 d1 : ℕ} {Ls : Fin m → PeriodPair}
    {M : Matrix (Fin r) (Fin m) ℂ} (h : r ≤ 1)
    (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) (hM : AlgMat M)
    (hLA : LiftAlg Ls) (hPT : PerTanRat Ls) :
    MStarCopy.HyperplaneKappa (gmStdVec d0 d1 Ls M) := by
  refine V5d.hyperplaneKappa_of_iso V5d.hyperplaneKappaVec_uncond halg hM h hLA hPT
    (gmStdVec d0 d1 Ls M) (LinearEquiv.refl ℂ _) (fun v hv => hv)
    (LSG.AuxV.lamVSub Ls M halg hM) (fun _ hx => hx)
    (fun y hy => ⟨1, one_pos, by rw [one_nsmul]; exact hy⟩)
    (fun x hx => ⟨x, hx, rfl⟩) rfl rfl ?_
  rintro H -
  exact ⟨H, by simp⟩

/-- **One CM curve repeated** (`L` with `κ₁ = 0`, the premises of lean_mstar's `Thm11KappaMGn`):
W88 §5d for `G_a^{d₀} × G_m^{d₁} × ((E^m)^♮ pushed out along `M`)`, every algebraic `M`,
`r ≤ 1`. -/
theorem hypStdVecCM (L : MStarCopy.CMLattice) (hκ : MStarCopy.KappaOneZero L)
    (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃) (d0 d1 : ℕ)
    (M : Matrix (Fin r) (Fin m) ℂ) (hr : r ≤ 1) (hM : AlgMat M) :
    MStarCopy.HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin m => L.pp) M) :=
  have hd := V5d.CMLat.cmD L hκ
  hyperplaneKappa_gmStdVec hr (fun _ => ⟨hg₂, hg₃⟩) hM (LSG.CM.liftAlg_block hg₂ hg₃ hd)
    (LSG.CM.perTanRat_block hd)

/-- The push-out matrix of `E^♮ × E^m` inside `(E^{m+1})^♮`: the first unit row. -/
def StdVec.eOne (m : ℕ) : Matrix (Fin 1) (Fin (m + 1)) ℂ :=
  Matrix.of fun _ j => if j = 0 then 1 else 0

lemma StdVec.algMat_eOne (m : ℕ) : AlgMat (StdVec.eOne m) := by
  intro i j
  simp only [StdVec.eOne, Matrix.of_apply]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

/-- **`G_a^{d₀} × G_m^{d₁} × E^♮ × E^m`** (one fibre, over the first curve), `E` with CM and
`κ₁ = 0`. -/
theorem hypStdVecCM_eOne (L : MStarCopy.CMLattice) (hκ : MStarCopy.KappaOneZero L)
    (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃) (d0 d1 m : ℕ) :
    MStarCopy.HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin (m + 1) => L.pp) (StdVec.eOne m)) :=
  hypStdVecCM L hκ hg₂ hg₃ d0 d1 (StdVec.eOne m) le_rfl (StdVec.algMat_eOne m)

/-! ### Examples -/

example (L : MStarCopy.CMLattice) (hκ : MStarCopy.KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) :
    MStarCopy.HyperplaneKappa (gmStdVec 1 1 (fun _ : Fin 3 => L.pp) (StdVec.eOne 2)) :=
  hypStdVecCM_eOne L hκ hg₂ hg₃ 1 1 2

/-- `E^♮ × E` with the matrix written inline. -/
example (L : MStarCopy.CMLattice) (hκ : MStarCopy.KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) :
    MStarCopy.HyperplaneKappa (gmStdVec 0 2 (fun _ : Fin 2 => L.pp) !![1, 0]) :=
  hypStdVecCM L hκ hg₂ hg₃ 0 2 _ le_rfl (by
    intro i j; fin_cases i; fin_cases j <;> simp [isAlgebraic_one, isAlgebraic_zero])

end LSG.W88
