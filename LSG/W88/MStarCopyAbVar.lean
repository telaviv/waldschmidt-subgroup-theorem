/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.MStarCopyMGn

/-!
# Verbatim copy of `lean_mstar`'s AbVar hypotheses `Thm11KappaA`, `Thm11KappaAK` (A6 bridge)

Source: `lean_mstar` HEAD `9b8d03680726333fdf242a2ce955034ebe495a6d` (2026-10-31 16:25), read 2026-10-31:
* `CM4E/Waldschmidt.lean`: `HyperplaneKappaOn`;
* `CM4E/Gen/Frame.lean`: `TorInj`;
* `CM4E/AbVar/Basis.lean`: `thetaD`, `KspanD`, `IsAdaptedBasisD`;
* `CM4E/AbVar/Fermat7.lean`: `betaG`;
* `CM4E/AbVar/ThmA.lean`: `zetaN`, `thetaA`, `perAgen`, `algA`, `gmA`, `Thm11KappaA`, `perA5`;
* `CM4E/AbVar/MGAK.lean`: `twistA`, `lamAK`, `gmAK`, `Thm11KappaAK`.
The remaining dependencies (`GroupModel`, `GroupModel.Rational`, `TF`, `tor1`, `tor2`, `qv`, `perGen`, `gmF`, `gmF2`,
`dotL`, ...) are the existing copies in `MStarCopy`, `MStarCopyMX`, `MStarCopyMGn`; all were re-compared with this HEAD
(whitespace-normalised text, identical). Definition bodies, binders and `variable` contexts are copied verbatim; only
the namespace is `LSG.W88.MStarCopy`. The new definitions were checked against the unmodified sources by `rfl` in a
scratch file in `lean_mstar` (since deleted). Do not edit except to re-sync with the source.
-/

open Complex Module

namespace LSG.W88.MStarCopy

/-! ### `CM4E/Waldschmidt.lean` -/

section Waldschmidt

variable {Vt : Type*} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt]

/-- **`HyperplaneKappa` restricted to the hyperplanes `V` with `good V`.** Same premises and conclusion as
`HyperplaneKappa`, with the extra premise `good V`; so it is weaker than `HyperplaneKappa` (`HyperplaneKappa.on`). -/
def HyperplaneKappaOn (G : GroupModel Vt) (good : Submodule ℂ Vt → Prop) : Prop :=
  ∀ (V W : Submodule ℂ Vt) (m : ℕ) (y : Fin m → Vt), good V →
    finrank ℂ V + 1 = finrank ℂ Vt → W ≤ V → G.Rational W →
    (∀ i, y i ∈ V ∧ y i ∈ G.lam) →
    ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
      ((G.d₁ : ℤ) + 2 * G.d₂ - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per)) *
        ((finrank ℂ Vt : ℤ) - 1 - finrank ℂ W)) →
    ∃ S : Submodule ℂ Vt, G.sub S ∧ S ≠ ⊥ ∧ S ≤ V

end Waldschmidt

/-! ### `CM4E/Gen/Frame.lean` -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- **Toric injectivity of a hyperplane `V`** (for a group model on the frame space `TF ι Q`, toric part `v.1`): every
vector of `V` in the period group with zero toric part is `0`. It is natural because on the period group it says
exactly that no nonzero period with zero toric part (a period of `G₂` alone) lies in `V`. The sibling project
`lean_lsg` uses it to prove W83 Prop. 2.1 for these hyperplanes without Masser's Theorem A. -/
def TorInj (G : GroupModel (TF ι Q)) (V : Submodule ℂ (TF ι Q)) : Prop :=
  ∀ v ∈ V, v ∈ G.per → v.1 = 0 → v = 0

end Frame

/-! ### `CM4E/AbVar/Basis.lean` -/

/-- `θ(j, e) = α^e b j`. -/
def thetaD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Fin r × Fin d → ℂ :=
  fun p => α ^ (p.2 : ℕ) * b p.1

/-- `K = span_ℚ θ`. -/
noncomputable def KspanD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (Set.range (thetaD α d b))

/-- `θ` is a `ℚ`-basis of a subfield `K` of `ℂ` consisting of algebraic numbers. -/
structure IsAdaptedBasisD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Prop where
  indep : LinearIndependent ℚ (thetaD α d b)
  one_mem : (1 : ℂ) ∈ KspanD α d b
  mul_mem : ∀ x ∈ KspanD α d b, ∀ y ∈ KspanD α d b, x * y ∈ KspanD α d b
  inv_mem : ∀ x ∈ KspanD α d b, x⁻¹ ∈ KspanD α d b
  alg : ∀ j, IsAlgebraic ℚ (b j)

/-! ### `CM4E/AbVar/ThmA.lean` -/

section ThmA

/-- `ζ_N = e^{2πi/N}`. -/
noncomputable def zetaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

variable (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (s₀ : Fin g) {r : ℕ} (b : Fin r → ℂ)

/-- `θ'(s, j) = b_j` on the slot `s₀`, `0` elsewhere: `λ = θ'ᵀ`. -/
def thetaA : Fin g × Fin r → ℂ := fun p => if p.1 = s₀ then b p.2 else 0

/-- Generators of the periods of `A^r`: `[ζ^e]γ` in copy `j`. -/
noncomputable def perAgen : Set (Fin g × Fin r → ℂ) :=
  Set.range (fun je : Fin r × ℕ => fun p => if p.2 = je.1 then zetaN N ^ (κ p.1 * je.2) * P p.1 else 0)

/-- The `ℚ̄`-structure of `T(A^r)`. -/
def algA (q : Fin g × Fin r → ℂ) : Prop := ∀ p, IsAlgebraic ℚ (q p)

/-- **The model of `G_m^{2n} × A^r`.** -/
noncomputable def gmA : GroupModel (TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) :=
  gmF (algA g) (perAgen N g κ P) (dotL (thetaA g s₀ b))

/-- **The hypothesis for Theorem MG-A**: W88 §5d for `G_m^{2n} × A^r`, for every `F`-basis `b` of a number field,
restricted to the toric-injective hyperplanes (`TorInj`: no nonzero period of `A^r` alone lies in `V`). The restriction
only weakens the hypothesis (`HyperplaneKappa.on`); the proof uses it only at `V''`, which is toric-injective
(`perA_inj`). -/
def Thm11KappaA : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmA N g κ P s₀ b) (TorInj (gmA N g κ P s₀ b))

end ThmA

/-! ### `CM4E/AbVar/Fermat7.lean` -/

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
noncomputable def betaG (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

/-! ### `CM4E/AbVar/ThmA.lean` (instance) -/

/-- The eigen-periods `P s = (1 − ζ₅^{s+1}) B((s+1)/5, (s+1)/5)` of `Jac(y⁵ = x(1 − x))` (`s = 0, 1`). -/
noncomputable def perA5 (s : Fin 2) : ℂ :=
  (1 - zetaN 5 ^ ((s : ℕ) + 1)) * betaG ((((s : ℕ) + 1 : ℕ) : ℂ) / 5) ((((s : ℕ) + 1 : ℕ) : ℂ) / 5)

/-! ### `CM4E/AbVar/MGAK.lean` -/

section MGAK

variable (N g : ℕ) (κ : Fin g → ℕ) {r : ℕ}

/-- `[ζ^e]v` in copy `j` of `A^r`. -/
noncomputable def twistA (j : Fin r) (e : ℕ) (v : Fin g → ℂ) : Fin g × Fin r → ℂ :=
  fun p => if p.2 = j then zetaN N ^ (κ p.1 * e) * v p.1 else 0

section MGA

variable (P : Fin g → ℂ) (s₀ : Fin g) (b : Fin r → ℂ) (LA : Set (Fin g → ℂ))

/-- Generators of the logarithms of `G_m^{2n} × A^r`: toric logarithms and `[ζ^e]v` in copy `j`. -/
def lamAK : Set (TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) :=
  {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor1 i y} ∪
    {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor2 i y} ∪
    {x | ∃ (j : Fin r) (e : ℕ), ∃ v ∈ insert P LA, x = qv (twistA N g κ j e v)}

/-- The model of `G_m^{2n} × A^r` with logarithms of `A` (frame `gmF2`). -/
noncomputable def gmAK : GroupModel (TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) :=
  gmF2 (thetaD (zetaN N) N.totient b) (algA g) (lamAK N g κ P LA)
    (perGen (ι := Fin r × Fin N.totient) (perAgen N g κ P)) 0 (dotL (thetaA g s₀ b))
    (finrank ℂ (Fin g × Fin r → ℂ))

/-- **The hypothesis for the `K`-form of MG-A**: W88 §5d for `G_m^{2n} × A^r`, every `F`-basis `b`, restricted to the
toric-injective hyperplanes (`TorInj`: no nonzero period of `A^r` alone lies in `V`; this only weakens it, by
`HyperplaneKappa.on`, and the proof uses only `V''`, which is toric-injective by `perA_inj`). Claimed when `LA`
consists of eigen-coordinate tuples of logarithms of algebraic points of `A` (normalised as `P`). -/
def Thm11KappaAK : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmAK N g κ P s₀ b LA) (TorInj (gmAK N g κ P s₀ b LA))

end MGA

end MGAK

end LSG.W88.MStarCopy
