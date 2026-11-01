import Mathlib
import LSG.Elliptic.NaturalLaws
import LSG.ME.OrderId

/-!
# The fibre half of the `E^♮` translation identity: definitions

Charts of an `E^♮` block are indexed by `Fin 2` (`0 = V`, `1 = W`, as for `mult`/`tcoord` of the
spike): `biE a ∈ Fin 3` is the base coordinate (`V ↦ 1`, `W ↦ 2`).

* `rhoh a P`: the homogeneous fibre field of chart `a` (quadratic in the base coordinates):
  `ρ_V = 2g₂U² + 3g₃UW`, `ρ_W = UW`; along a flow normalized in chart `a`, the chart fibre
  coordinate `T_a` (`T_V = T₃`, `T_W = T₁`) moves by `T_a' = β + ζ ρ_a`.
* `kapB b`: the fibre correction `κ` of the law in the `T_b`-component.
* `epsT D a j P`: the chart-change term of `λ D(T_λ) − T_λ D(λ)` for `λ = j ≠ a`.
* **`fibE D i j k a b g₂ g₃ s P Q`**: the base expression
  `4μ²L²Ψ − (A_b D(κ) − κ D(A_b)) − 2s ρ_b(A_base)` (`L = law_i(P, Q)_b`, `A_b = 2λμL`,
  `Ψ = λ²·2s ρ_a(P) + ε_{a,λ}`), which lies in `(F(P), F(Q))` when `D P = s c2_a(P)`, `D Q = 0`,
  `P_a = 1` (generated identities `LSG.MEV.FibreId*`, script `scripts/mev_curve/fibre_ids.py`).
-/

open LSG.Elliptic

namespace LSG.MEV

variable {R : Type*} [CommRing R]

/-- The base coordinate of a chart: `V ↦ 1`, `W ↦ 2`. -/
def biE (a : Fin 2) : Fin 3 := ![1, 2] a

@[simp] theorem biE_zero : biE 0 = 1 := rfl
@[simp] theorem biE_one : biE 1 = 2 := rfl

theorem mult_eq (a : Fin 2) (P : Fin 3 → R) : mult a P = P (biE a) := by
  fin_cases a <;> rfl

/-- The homogeneous fibre field of chart `a`: `ρ_V = 2g₂U² + 3g₃UW`, `ρ_W = UW`. -/
def rhoh (a : Fin 2) (g₂ g₃ : R) (P : Fin 3 → R) : R :=
  ![2 * g₂ * P 0 ^ 2 + 3 * g₃ * P 0 * P 2, P 0 * P 2] a

theorem rhoh_smul (a : Fin 2) (g₂ g₃ u : R) (P : Fin 3 → R) :
    rhoh a g₂ g₃ (u • P) = u ^ 2 * rhoh a g₂ g₃ P := by
  fin_cases a <;> simp [rhoh] <;> ring

theorem rhoh_map {S : Type*} [CommRing S] (f : R →+* S) (a : Fin 2) (g₂ g₃ : R) (P : Fin 3 → R) :
    f (rhoh a g₂ g₃ P) = rhoh a (f g₂) (f g₃) (f ∘ P) := by
  fin_cases a <;> simp [rhoh, map_ofNat]

/-- The fibre correction of the `T_b`-component (`V ↦ κⱽ`, `W ↦ κᵂ`). -/
def kapB (b : Fin 2) (g₂ g₃ : R) (i j k : Fin 2) (P Q : Fin 3 → R) : R :=
  ![kapV g₂ g₃ i j k P Q, kapW g₂ g₃ i j k P Q] b

section D

variable {S : Type*} [CommRing S] [Algebra S R]

/-- The chart-change term of `λ D(T_λ) − T_λ D(λ)` (`λ = j`, moving point normalized in chart `a`). -/
def epsT (D : Derivation S R R) (a j : Fin 2) (P : Fin 3 → R) : R :=
  ![![0, 4 * P 0 * P 2 * D (P 0) - 2 * P 0 ^ 2 * D (P 2)],
    ![-(4 * P 0 * P 1 * D (P 0) - 2 * P 0 ^ 2 * D (P 1)), 0]] a j

/-- **The base expression of the fibre identity.** -/
def fibE (D : Derivation S R R) (i j k a b : Fin 2) (g₂ g₃ s : R) (P Q : Fin 3 → R) : R :=
  4 * mult k Q ^ 2 * lawSel g₂ g₃ i P Q (biE b) ^ 2 *
      (mult j P ^ 2 * (2 * s * rhoh a g₂ g₃ P) + epsT D a j P) -
    (2 * (mult j P * mult k Q) * lawSel g₂ g₃ i P Q (biE b) * D (kapB b g₂ g₃ i j k P Q) -
      kapB b g₂ g₃ i j k P Q * D (2 * (mult j P * mult k Q) * lawSel g₂ g₃ i P Q (biE b))) -
    2 * s * rhoh b g₂ g₃ (fun l => 2 * (mult j P * mult k Q) * lawSel g₂ g₃ i P Q l)

end D

end LSG.MEV
