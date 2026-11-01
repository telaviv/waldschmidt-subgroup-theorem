import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# A complete system of two addition laws: the polynomial layer

The Weierstrass cubic `E : V²W = 4U³ − g₂UW² − g₃W³` in `ℙ²`, with cone form
`F g₂ g₃ U V W = V²W − 4U³ + g₂UW² + g₃W³`, and two addition laws `law₁`, `law₂`, both
bihomogeneous of bidegree `(2, 2)` with coefficients in `ℤ[g₂, g₃]`.

* `law₁` is Mathlib's projective chord law `WeierstrassCurve.Projective.addXYZ` transported to
  our curve (times `4`); it vanishes exactly on the diagonal `P = Q` (see `AdditionLawsGroup`).
* `law₂` is the Bosma–Lenstra law attached to the line `V = 0` (in Mathlib coordinates this is
  the Renes–Costello–Batina "complete" formula, times `32`); on the diagonal it equals the
  doubling form `dbl` modulo `F`, and it is never zero there.

This file proves the polynomial identities, over an arbitrary commutative ring:
* `F_law₁`, `F_law₂` (and `Fv_law₁_mem`, `Fv_law₂_mem`): `F(A(P, Q)) ∈ (F(P), F(Q))`, with
  explicit cofactors (computed by division with respect to `U₁`, then `U₂`, in sympy);
* `law₁_smul`, `law₂_smul`: bihomogeneity of bidegree `(2, 2)`;
* `law₁_zero_right`, `law₂_zero_right`: `A(P, O) = c(P) • P` with `O = (0 : 1 : 0)`;
* `law₁_cross_law₂`: on `E × E` the two laws are proportional (all 2×2 minors vanish);
* `law₂_self`: on `E`, `law₂ P P = dbl P`.
The comparison with Mathlib's group law is in `LSG.Elliptic.AdditionLawsGroup`.
-/

namespace LSG.Elliptic

variable {R : Type*} [CommRing R]

/-- The cone form of `E : V²W = 4U³ − g₂UW² − g₃W³`. -/
def F (g₂ g₃ U V W : R) : R :=
  V ^ 2 * W - 4 * U ^ 3 + g₂ * U * W ^ 2 + g₃ * W ^ 3

/-! ### Components (bidegree `(2, 2)` in `(U₁, V₁, W₁; U₂, V₂, W₂)`) -/

/-- `U`-component of `law₁`. -/
def law₁U (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -U₁^2*W₂^2*g₂ - 2*U₁*V₁*V₂*W₂ - U₁*V₂^2*W₁ - 3*U₁*W₁*W₂^2*g₃ + U₂^2*W₁^2*g₂ + U₂*V₁^2*W₂
    + 2*U₂*V₁*V₂*W₁ + 3*U₂*W₁^2*W₂*g₃

/-- `V`-component of `law₁`. -/
def law₁V (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    12*U₁^2*U₂*V₂ - 12*U₁*U₂^2*V₁ + U₁*V₁*W₂^2*g₂ - 2*U₁*V₂*W₁*W₂*g₂ + 2*U₂*V₁*W₁*W₂*g₂
    - U₂*V₂*W₁^2*g₂ + V₁^2*V₂*W₂ - V₁*V₂^2*W₁ + 3*V₁*W₁*W₂^2*g₃ - 3*V₂*W₁^2*W₂*g₃

set_option linter.unusedVariables false in
/-- `W`-component of `law₁`. -/
def law₁W (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -12*U₁^2*U₂*W₂ + 12*U₁*U₂^2*W₁ + U₁*W₁*W₂^2*g₂ - U₂*W₁^2*W₂*g₂ + V₁^2*W₂^2 - V₂^2*W₁^2

/-- `U`-component of `law₂`. -/
def law₂U (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    4*U₁^2*V₂*W₂*g₂ + 8*U₁*U₂*V₁*W₂*g₂ + 8*U₁*U₂*V₂*W₁*g₂ + 4*U₁*V₁*V₂^2 + 12*U₁*V₁*W₂^2*g₃
    + 24*U₁*V₂*W₁*W₂*g₃ + 4*U₂^2*V₁*W₁*g₂ + 4*U₂*V₁^2*V₂ + 24*U₂*V₁*W₁*W₂*g₃ + 12*U₂*V₂*W₁^2*g₃
    + V₁*W₁*W₂^2*g₂^2 + V₂*W₁^2*W₂*g₂^2

/-- `V`-component of `law₂`. -/
def law₂V (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -48*U₁^2*U₂^2*g₂ - 144*U₁^2*U₂*W₂*g₃ - 4*U₁^2*W₂^2*g₂^2 - 144*U₁*U₂^2*W₁*g₃
    - 16*U₁*U₂*W₁*W₂*g₂^2 - 12*U₁*W₁*W₂^2*g₂*g₃ - 4*U₂^2*W₁^2*g₂^2 - 12*U₂*W₁^2*W₂*g₂*g₃
    + 4*V₁^2*V₂^2 + W₁^2*W₂^2*g₂^3 - 36*W₁^2*W₂^2*g₃^2

/-- `W`-component of `law₂`. -/
def law₂W (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    48*U₁^2*U₂*V₂ + 48*U₁*U₂^2*V₁ - 4*U₁*V₁*W₂^2*g₂ - 8*U₁*V₂*W₁*W₂*g₂ - 8*U₂*V₁*W₁*W₂*g₂
    - 4*U₂*V₂*W₁^2*g₂ + 4*V₁^2*V₂*W₂ + 4*V₁*V₂^2*W₁ - 12*V₁*W₁*W₂^2*g₃ - 12*V₂*W₁^2*W₂*g₃

/-- `U`-component of the doubling form (degree 4); `law₂ P P = dbl P` on `E`. -/
def dblU (g₂ g₃ U V W : R) : R :=
    24*U^2*V*W*g₂ + 8*U*V^3 + 72*U*V*W^2*g₃ + 2*V*W^3*g₂^2

/-- `V`-component of the doubling form. -/
def dblV (g₂ g₃ U V W : R) : R :=
    -432*U^3*W*g₃ - 36*U^2*W^2*g₂^2 - 12*U*V^2*W*g₂ + 4*V^4 + 36*V^2*W^2*g₃ + W^4*g₂^3

set_option linter.unusedVariables false in
/-- `W`-component of the doubling form. -/
def dblW (g₂ g₃ U V W : R) : R :=
    32*V^3*W

/-! ### Cofactors for `F(A(P, Q)) ∈ (F(P), F(Q))` -/

/-- Chunk 0 of `law₁Cof₁`. -/
def law₁Cof₁P0 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -1296*U₁^2*U₂^4*W₁*W₂^2*g₃ - 144*U₁^2*U₂^2*V₂^2*W₁*W₂^2*g₂ - 3*U₁^2*V₂^2*W₁*W₂^4*g₂^2
    - 108*U₁*U₂^3*V₁^2*W₂^3*g₂ - 108*U₁*U₂^2*V₁^2*W₂^4*g₃ - 108*U₁*U₂^2*V₂^2*W₁^2*W₂^2*g₃
    - 24*U₁*U₂*V₁*V₂*W₁*W₂^4*g₂^2 - 12*U₁*V₁^2*V₂^2*W₂^4*g₂ - 12*U₁*V₁*V₂^3*W₁*W₂^3*g₂
    - 36*U₁*V₁*V₂*W₁*W₂^5*g₂*g₃ - 3*U₁*V₂^4*W₁^2*W₂^2*g₂ - 18*U₁*V₂^2*W₁^2*W₂^4*g₂*g₃
    - 27*U₁*W₁^2*W₂^6*g₂*g₃^2 - 36*U₂^4*V₁^2*W₁*W₂^2*g₂ - 288*U₂^4*V₁*V₂*W₁^2*W₂*g₂
    - 324*U₂^4*W₁^3*W₂^2*g₂*g₃ - 18*U₂^3*W₁^3*W₂^3*g₂^3 - 30*U₂^2*V₂^2*W₁^3*W₂^2*g₂^2
    - 2*U₂*W₁^3*W₂^5*g₂^4 - 12*V₁^2*V₂^4*W₁*W₂^2 - 2*V₂^2*W₁^3*W₂^4*g₂^3
    - 27*V₂^2*W₁^3*W₂^4*g₃^2 - 2*W₁^3*W₂^6*g₂^3*g₃ - 27*W₁^3*W₂^6*g₃^3

/-- Chunk 1 of `law₁Cof₁`. -/
def law₁Cof₁P1 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -U₁^3*W₂^6*g₂^3 - 864*U₁^2*U₂^4*V₁*V₂*W₂ - 432*U₁^2*U₂^4*V₂^2*W₁ - 72*U₁^2*U₂^3*W₁*W₂^3*g₂^2
    - 6*U₁^2*U₂*W₁*W₂^5*g₂^3 - 6*U₁^2*V₁*V₂*W₂^5*g₂^2 - 9*U₁^2*W₁*W₂^6*g₂^2*g₃
    + 108*U₁*U₂^3*W₁^2*W₂^3*g₂*g₃ - 72*U₁*U₂^2*V₁*V₂^3*W₁*W₂ - 432*U₂^6*V₁^2*W₁
    - 432*U₂^6*W₁^3*g₃ + 108*U₂^3*V₁^2*V₂^2*W₁*W₂ + 108*U₂^3*V₁^2*W₁*W₂^3*g₃
    + 108*U₂^3*V₂^2*W₁^3*W₂*g₃ + 108*U₂^3*W₁^3*W₂^3*g₃^2 + 12*U₂*V₁^2*V₂^2*W₁*W₂^3*g₂
    - 6*U₂*V₂^4*W₁^3*W₂*g₂ - 8*V₁^3*V₂^3*W₂^3 - 36*V₁^2*V₂^2*W₁*W₂^4*g₃ - 6*V₁*V₂^5*W₁^2*W₂
    - 36*V₁*V₂^3*W₁^2*W₂^3*g₃ - 54*V₁*V₂*W₁^2*W₂^5*g₃^2 - V₂^6*W₁^3 - 9*V₂^4*W₁^3*W₂^2*g₃

/-- Chunk 2 of `law₁Cof₁`. -/
def law₁Cof₁P2 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    432*U₁^3*U₂^3*V₂^2*W₂ + 432*U₁^3*U₂^3*W₂^3*g₃ + 36*U₁^3*U₂^2*W₂^4*g₂^2
    + 144*U₁^2*U₂^2*V₁*V₂*W₂^3*g₂ + 432*U₁*U₂^5*V₁^2*W₂ + 864*U₁*U₂^5*V₁*V₂*W₁
    + 1296*U₁*U₂^5*W₁^2*W₂*g₃ + 72*U₁*U₂^3*V₁*V₂*W₁*W₂^2*g₂ + 144*U₁*U₂^3*V₂^2*W₁^2*W₂*g₂
    + 36*U₁*U₂^2*V₁^2*V₂^2*W₂^2 + 216*U₁*U₂^2*V₁*V₂*W₁*W₂^3*g₃ + 36*U₁*U₂^2*V₂^4*W₁^2
    + 24*U₁*U₂^2*W₁^2*W₂^4*g₂^3 + 24*U₁*U₂*V₂^2*W₁^2*W₂^3*g₂^2 + 72*U₂^5*W₁^3*W₂*g₂^2
    + 36*U₂^2*V₁^2*W₁*W₂^4*g₂^2 + 48*U₂^2*V₁*V₂*W₁^2*W₂^3*g₂^2 + 54*U₂^2*W₁^3*W₂^4*g₂^2*g₃
    + 36*U₂*V₁^2*W₁*W₂^5*g₂*g₃ + 48*U₂*V₁*V₂^3*W₁^2*W₂^2*g₂ + 72*U₂*V₂^2*W₁^3*W₂^3*g₂*g₃
    + 54*U₂*W₁^3*W₂^5*g₂*g₃^2

/-- Cofactor of `F(P)` in `F(law₁(P, Q))`. -/
def law₁Cof₁ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    law₁Cof₁P0 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₁Cof₁P1 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₁Cof₁P2 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂

/-- Chunk 0 of `law₁Cof₂`. -/
def law₁Cof₂P0 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -36*U₁^2*U₂^3*W₁^4*g₂^2 - 36*U₁^2*U₂*V₁^4*W₂^2 - 144*U₁^2*U₂*V₁^3*V₂*W₁*W₂
    - 144*U₁^2*U₂*V₁^2*V₂^2*W₁^2 - 216*U₁^2*U₂*V₁^2*W₁^2*W₂^2*g₃ - 432*U₁^2*U₂*V₁*V₂*W₁^3*W₂*g₃
    - 24*U₁^2*U₂*W₁^4*W₂^2*g₂^3 - 324*U₁^2*U₂*W₁^4*W₂^2*g₃^2 + 12*U₁^2*V₁^2*W₁^2*W₂^3*g₂^2
    - 108*U₁*U₂^3*V₁^2*W₁^3*g₂ - 108*U₁*U₂^3*W₁^5*g₂*g₃ + 108*U₁*U₂^2*V₁^4*W₁*W₂
    - 60*U₁*U₂*V₁^2*W₁^3*W₂^2*g₂^2 - 48*U₁*U₂*V₁*V₂*W₁^4*W₂*g₂^2 - 108*U₁*U₂*W₁^5*W₂^2*g₂^2*g₃
    - 108*U₂^3*V₁^4*W₁^2 - 216*U₂^3*V₁^2*W₁^4*g₃ - 108*U₂^3*W₁^6*g₃^2 - 33*U₂*V₁^4*W₁^2*W₂^2*g₂
    - 60*U₂*V₁^3*V₂*W₁^3*W₂*g₂ + 12*U₂*V₁^2*V₂^2*W₁^4*g₂ - 126*U₂*V₁^2*W₁^4*W₂^2*g₂*g₃
    - 36*U₂*V₁*V₂*W₁^5*W₂*g₂*g₃ - 81*U₂*W₁^6*W₂^2*g₂*g₃^2

/-- Chunk 1 of `law₁Cof₂`. -/
def law₁Cof₂P1 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    252*U₁^2*U₂^2*V₁^2*W₁^2*W₂*g₂ + 324*U₁^2*U₂^2*W₁^4*W₂*g₂*g₃ + 24*U₁^2*V₁*V₂*W₁^3*W₂^2*g₂^2
    + 36*U₁^2*W₁^4*W₂^3*g₂^2*g₃ + 216*U₁*U₂^2*V₁^3*V₂*W₁^2 + 432*U₁*U₂^2*V₁^2*W₁^3*W₂*g₃
    + 216*U₁*U₂^2*V₁*V₂*W₁^4*g₃ + 24*U₁*U₂^2*W₁^5*W₂*g₂^3 + 324*U₁*U₂^2*W₁^5*W₂*g₃^2
    + 24*U₁*V₁^3*V₂*W₁^2*W₂^2*g₂ + 24*U₁*V₁^2*V₂^2*W₁^3*W₂*g₂ + 36*U₁*V₁^2*W₁^3*W₂^3*g₂*g₃
    + 2*U₁*W₁^5*W₂^3*g₂^4 + 54*U₁*W₁^5*W₂^3*g₂*g₃^2 + 21*U₂^2*V₁^2*W₁^4*W₂*g₂^2
    + 27*U₂^2*W₁^6*W₂*g₂^2*g₃ + 12*V₁^4*V₂^2*W₁^2*W₂ + 36*V₁^3*V₂*W₁^3*W₂^2*g₃
    + 36*V₁^2*V₂^2*W₁^4*W₂*g₃ + 2*V₁^2*W₁^4*W₂^3*g₂^3 + 27*V₁^2*W₁^4*W₂^3*g₃^2
    + 54*V₁*V₂*W₁^5*W₂^2*g₃^2 + 2*W₁^6*W₂^3*g₂^3*g₃ + 27*W₁^6*W₂^3*g₃^3

/-- Chunk 2 of `law₁Cof₂`. -/
def law₁Cof₂P2 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    72*U₁^2*U₂^2*V₁*V₂*W₁^3*g₂ + 6*U₁*V₁^4*W₁*W₂^3*g₂ + 72*U₁*V₁*V₂*W₁^4*W₂^2*g₂*g₃
    + U₂^3*W₁^6*g₂^3 + 6*U₂^2*V₁*V₂*W₁^5*g₂^2 + V₁^6*W₂^3 + 6*V₁^5*V₂*W₁*W₂^2
    + 9*V₁^4*W₁^2*W₂^3*g₃ + 8*V₁^3*V₂^3*W₁^3

/-- Cofactor of `F(Q)` in `F(law₁(P, Q))`. -/
def law₁Cof₂ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    law₁Cof₂P0 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₁Cof₂P1 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₁Cof₂P2 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂

/-- Chunk 0 of `law₂Cof₁`. -/
def law₂Cof₁P0 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -165888*U₁^3*U₂^4*V₂*W₂*g₂*g₃ - 2304*U₁^3*U₂^2*V₂^3*W₂*g₂^2
    - 13824*U₁^3*U₂^2*V₂*W₂^3*g₂^2*g₃ - 192*U₁^3*U₂*V₂*W₂^4*g₂^4 - 165888*U₁^2*U₂^5*V₁*W₂*g₂*g₃
    - 165888*U₁^2*U₂^5*V₂*W₁*g₂*g₃ - 2304*U₁^2*U₂^4*V₁*W₂^2*g₂^3 - 248832*U₁^2*U₂^4*V₁*W₂^2*g₃^2
    - 13824*U₁^2*U₂^4*V₂*W₁*W₂*g₂^3 - 2304*U₁^2*U₂^2*V₁*V₂^4*g₂ - 165888*U₁*U₂^6*V₁*W₁*g₂*g₃
    - 13824*U₁*U₂^5*V₁*W₁*W₂*g₂^3 - 13824*U₁*U₂^4*V₁^2*V₂*W₂*g₂^2
    - 13824*U₁*U₂^4*V₁*V₂^2*W₁*g₂^2 - 2304*U₁*U₂^3*V₁^2*V₂^3*g₂
    - 13824*U₁*U₂^3*V₁^2*V₂*W₂^2*g₂*g₃ - 13824*U₁*U₂^3*V₁*V₂^2*W₁*W₂*g₂*g₃
    - 20736*U₁*U₂^2*V₁^2*V₂*W₂^3*g₃^2 - 11520*U₂^6*V₁*W₁^2*g₂^3 - 16128*U₂^5*V₁^2*V₂*W₁*g₂^2
    - 2304*U₂^4*V₁^3*V₂^2*g₂ - 192*U₂^2*V₁*V₂^4*W₁^2*g₂^2 - 112*U₂*V₁^2*V₂*W₁*W₂^4*g₂^4
    - 16*V₁^3*V₂^2*W₂^4*g₂^3

/-- Chunk 1 of `law₂Cof₁`. -/
def law₂Cof₁P1 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -27648*U₁^3*U₂^5*V₂*g₂^2 - 27648*U₁^3*U₂^3*V₂^3*g₃ - 4608*U₁^3*U₂^3*V₂*W₂^2*g₂^3
    - 248832*U₁^3*U₂^3*V₂*W₂^2*g₃^2 - 27648*U₁^2*U₂^6*V₁*g₂^2 - 497664*U₁^2*U₂^4*V₂*W₁*W₂*g₃^2
    - 4608*U₁^2*U₂^3*V₂^3*W₁*g₂^2 - 55296*U₁^2*U₂^3*V₂*W₁*W₂^2*g₂^2*g₃
    - 497664*U₁*U₂^5*V₁*W₁*W₂*g₃^2 - 248832*U₁*U₂^5*V₂*W₁^2*g₃^2
    - 34560*U₁*U₂^4*V₁*W₁*W₂^2*g₂^2*g₃ - 41472*U₁*U₂^3*V₂*W₁^2*W₂^2*g₂*g₃^2
    - 32*U₁*V₁^2*V₂*W₂^5*g₂^4 - 32*U₁*V₁*V₂^2*W₁*W₂^4*g₂^4 - 27648*U₂^6*V₁^3*g₃
    - 248832*U₂^6*V₁*W₁^2*g₃^2 - 4608*U₂^5*V₁^3*W₂*g₂^2 - 48384*U₂^5*V₂*W₁^3*g₂^2*g₃
    - 34560*U₂^4*V₁*V₂^2*W₁^2*g₂*g₃ - 41472*U₂^4*V₁*W₁^2*W₂^2*g₂*g₃^2
    - 2688*U₂^4*V₂*W₁^3*W₂*g₂^4 - 32*U₂*V₁^3*W₂^5*g₂^4 - 32*V₁^3*W₂^6*g₂^3*g₃
    - 4*V₁*W₁^2*W₂^6*g₂^6

/-- Chunk 2 of `law₂Cof₁`. -/
def law₂Cof₁P2 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -82944*U₁^2*U₂^4*V₁*V₂^2*g₃ - 9216*U₁^2*U₂^3*V₁*V₂^2*W₂*g₂^2 - 768*U₁^2*U₂^2*V₂*W₁*W₂^3*g₂^4
    + 1152*U₁^2*U₂*V₁*W₂^5*g₂^3*g₃ - 82944*U₁*U₂^5*V₁^2*V₂*g₃ - 9216*U₁*U₂^5*V₂*W₁^2*g₂^3
    - 76032*U₁*U₂^4*V₂*W₁^2*W₂*g₂^2*g₃ - 6912*U₁*U₂^3*V₂^3*W₁^2*g₂*g₃
    - 6912*U₁*U₂^2*V₁*V₂^4*W₁*g₃ + 10368*U₁*U₂^2*V₂*W₁^2*W₂^3*g₂^3*g₃
    - 62208*U₁*U₂^2*V₂*W₁^2*W₂^3*g₃^3 + 10368*U₁*U₂*V₁*V₂^2*W₁*W₂^3*g₂^2*g₃
    - 96768*U₂^5*V₁*W₁^2*W₂*g₂^2*g₃ - 55296*U₂^4*V₁^2*V₂*W₁*W₂*g₂*g₃
    - 82944*U₂^4*V₂*W₁^3*W₂*g₂*g₃^2 - 6912*U₂^3*V₁^2*V₂^3*W₁*g₃
    - 62208*U₂^3*V₁^2*V₂*W₁*W₂^2*g₃^2 - 6912*U₂^3*V₂^3*W₁^3*g₃^2 - 62208*U₂^3*V₂*W₁^3*W₂^2*g₃^3
    + 10944*U₂^2*V₂^3*W₁^3*W₂*g₂^2*g₃ + 1056*U₂*V₁*W₁^2*W₂^5*g₂^4*g₃
    - 96*V₁^2*V₂*W₁*W₂^5*g₂^3*g₃ + 10368*V₁^2*V₂*W₁*W₂^5*g₃^3 - 8*V₂*W₁^3*W₂^5*g₂^6

/-- Chunk 3 of `law₂Cof₁`. -/
def law₂Cof₁P3 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    1152*U₁^2*U₂*V₂^3*W₁*W₂^2*g₂^3 + 1152*U₁^2*U₂*V₂*W₁*W₂^4*g₂^3*g₃ + 16*U₁^2*V₁*W₂^6*g₂^5
    + 1152*U₁^2*V₂^3*W₁*W₂^3*g₂^2*g₃ + 1536*U₁*U₂^2*V₁^2*V₂*W₂^3*g₂^3
    + 1536*U₁*U₂^2*V₂^3*W₁^2*W₂*g₂^3 + 1344*U₁*U₂*V₁^2*V₂^3*W₂^2*g₂^2
    + 1728*U₁*U₂*V₁^2*V₂*W₂^4*g₂^2*g₃ + 1152*U₁*U₂*V₁*V₂^4*W₁*W₂*g₂^2
    + 160*U₁*U₂*V₁*W₁*W₂^5*g₂^5 + 1152*U₁*V₁^2*V₂^3*W₂^3*g₂*g₃ + 1728*U₁*V₁^2*V₂*W₂^5*g₂*g₃^2
    + 144*U₁*V₁*W₁*W₂^6*g₂^4*g₃ + 1280*U₂^3*V₁^3*W₂^3*g₂^3 + 128*U₂^3*V₂^3*W₁^3*g₂^3
    + 1152*U₂^2*V₁^3*V₂^2*W₂^2*g₂^2 + 12672*U₂^2*V₁^2*V₂*W₁*W₂^3*g₂^2*g₃
    + 11520*U₂*V₁^2*V₂^3*W₁*W₂^2*g₂*g₃ + 1392*U₂*V₂*W₁^3*W₂^4*g₂^4*g₃ + 1728*V₁^3*V₂^2*W₂^4*g₃^2
    + 1152*V₁^2*V₂^5*W₁*W₂*g₃ + 144*V₁*V₂^4*W₁^2*W₂^2*g₂^3 + 13824*V₂^3*W₁^3*W₂^3*g₃^3
    + 1152*V₂*W₁^3*W₂^5*g₂^3*g₃^2

/-- Chunk 4 of `law₂Cof₁`. -/
def law₂Cof₁P4 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    192*U₁^2*U₂^2*V₁*W₂^4*g₂^4 + 20736*U₁^2*U₂^2*V₁*W₂^4*g₂*g₃^2 + 192*U₁^2*V₁*V₂^4*W₂^2*g₂^2
    + 32*U₁^2*V₂*W₁*W₂^5*g₂^5 + 20736*U₁*U₂^2*V₂^3*W₁^2*W₂*g₃^2 + 320*U₁*U₂*V₂*W₁^2*W₂^4*g₂^5
    + 192*U₁*V₁^2*V₂^5*W₂*g₂ + 2304*U₁*V₁*V₂^4*W₁*W₂^2*g₂*g₃ + 240*U₁*V₂*W₁^2*W₂^5*g₂^4*g₃
    + 2304*U₂^3*V₁*V₂^2*W₁^2*W₂*g₂^3 + 23040*U₂^3*V₁*W₁^2*W₂^3*g₂^3*g₃
    + 2880*U₂^2*V₁^3*W₂^4*g₂^2*g₃ + 3264*U₂^2*V₁^2*V₂^3*W₁*W₂*g₂^2
    + 27648*U₂^2*V₁*V₂^2*W₁^2*W₂^2*g₂^2*g₃ + 24192*U₂^2*V₂*W₁^3*W₂^3*g₂^2*g₃^2
    + 2304*U₂*V₁^3*V₂^2*W₂^3*g₂*g₃ + 20736*U₂*V₁^2*V₂*W₁*W₂^4*g₂*g₃^2
    + 320*U₂*V₁*V₂^2*W₁^2*W₂^3*g₂^4 + 20736*U₂*V₁*W₁^2*W₂^5*g₂*g₃^3
    + 20736*U₂*V₂^3*W₁^3*W₂^2*g₂*g₃^2 + 20736*U₂*V₂*W₁^3*W₂^4*g₂*g₃^3 + 1728*V₁^3*W₂^6*g₃^3
    + 240*V₁*V₂^2*W₁^2*W₂^4*g₂^3*g₃ + 20736*V₁*V₂^2*W₁^2*W₂^4*g₃^3

/-- Chunk 5 of `law₂Cof₁`. -/
def law₂Cof₁P5 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    64*U₁^3*V₂^3*W₂^3*g₂^3 + 576*U₁^2*V₁*V₂^2*W₂^4*g₂^2*g₃ + 6912*U₁*U₂^2*V₁^2*V₂^3*W₂*g₃
    + 4608*U₁*U₂^2*V₁*V₂^2*W₁*W₂^2*g₂^3 + 62208*U₁*U₂^2*V₁*W₁*W₂^4*g₃^3
    + 6912*U₁*U₂*V₁*W₁*W₂^5*g₂^2*g₃^2 + 5184*U₁*U₂*V₂*W₁^2*W₂^4*g₂^2*g₃^2
    + 6912*U₁*V₁*V₂^2*W₁*W₂^4*g₂*g₃^2 + 6912*U₁*V₂^3*W₁^2*W₂^3*g₂*g₃^2
    + 576*U₂^4*V₁*W₁^2*W₂^2*g₂^4 + 3456*U₂^3*V₁^2*V₂*W₁*W₂^2*g₂^3 + 592*U₂^2*V₁*W₁^2*W₂^4*g₂^5
    + 38016*U₂^2*V₁*W₁^2*W₂^4*g₂^2*g₃^2 + 704*U₂^2*V₂*W₁^3*W₂^3*g₂^5 + 384*U₂*V₁^3*V₂^4*W₂*g₂
    + 3456*U₂*V₁^3*W₂^5*g₂*g₃^2 + 6912*U₂*V₁*V₂^4*W₁^2*W₂*g₂*g₃
    + 41472*U₂*V₁*V₂^2*W₁^2*W₂^3*g₂*g₃^2 + 480*U₂*V₂^3*W₁^3*W₂^2*g₂^4 + 64*V₁^3*V₂^6
    + 576*V₁^3*V₂^4*W₂^2*g₃ + 6912*V₁^2*V₂^3*W₁*W₂^3*g₃^2 + 6912*V₁*V₂^4*W₁^2*W₂^2*g₃^2
    + 432*V₂^3*W₁^3*W₂^3*g₂^3*g₃

/-- Chunk 6 of `law₂Cof₁`. -/
def law₂Cof₁P6 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    768*U₁^2*U₂*V₁*V₂^2*W₂^3*g₂^3 + 768*U₁*U₂^3*V₁*W₁*W₂^3*g₂^4
    + 82944*U₁*U₂^3*V₁*W₁*W₂^3*g₂*g₃^2 + 9216*U₁*U₂^2*V₁*W₁*W₂^4*g₂^3*g₃
    + 8640*U₁*U₂*V₂^3*W₁^2*W₂^2*g₂^2*g₃ + 8064*U₂^3*V₂*W₁^3*W₂^2*g₂^3*g₃
    + 80*V₁^2*V₂^3*W₁*W₂^3*g₂^3 + 720*V₁*W₁^2*W₂^6*g₂^3*g₃^2

/-- Cofactor of `F(P)` in `F(law₂(P, Q))`. -/
def law₂Cof₁ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    law₂Cof₁P0 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P1 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P2 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P3 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P4 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P5 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₁P6 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂

/-- Chunk 0 of `law₂Cof₂`. -/
def law₂Cof₂P0 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -13824*U₁^2*U₂*V₁^3*V₂^2*W₁*g₃ - 124416*U₁^2*U₂*V₁^2*V₂*W₁^2*W₂*g₃^2
    - 10944*U₁^2*U₂*V₁*W₁^3*W₂^2*g₂^3*g₃ - 124416*U₁^2*U₂*V₁*W₁^3*W₂^2*g₃^3
    - 13248*U₁^2*U₂*V₂*W₁^4*W₂*g₂^3*g₃ - 1152*U₁^2*V₁^3*W₁*W₂^3*g₂^2*g₃
    - 12096*U₁^2*V₂*W₁^4*W₂^2*g₂^2*g₃^2 - 103680*U₁*U₂^3*V₁*W₁^4*g₂*g₃^2
    - 124416*U₁*U₂^2*V₁^3*W₁^2*W₂*g₃^2 - 124416*U₁*U₂^2*V₁*W₁^4*W₂*g₃^3
    - 13248*U₁*U₂^2*V₂*W₁^5*g₂^3*g₃ - 12096*U₁*U₂*V₁^3*W₁^2*W₂^2*g₂^2*g₃
    - 10368*U₁*U₂*V₁*V₂^2*W₁^4*g₂^2*g₃ - 160*U₁*V₁^3*W₁^2*W₂^3*g₂^4
    - 15552*U₁*V₁*W₁^4*W₂^3*g₂*g₃^3 - 1152*U₂^2*V₁^5*W₁*W₂*g₂^2
    - 15552*U₂^2*V₁^2*V₂*W₁^4*g₂^2*g₃ - 12096*U₂^2*V₂*W₁^6*g₂^2*g₃^2
    - 11520*U₂*V₁^4*V₂*W₁^2*W₂*g₂*g₃ - 1152*V₁^4*V₂^3*W₁^2*g₃ - 10368*V₁^3*V₂^2*W₁^3*W₂*g₃^2
    - 10368*V₁^2*V₂*W₁^4*W₂^2*g₃^3 - 15552*V₁*W₁^5*W₂^3*g₃^4 - 15552*V₂*W₁^6*W₂^2*g₃^4

/-- Chunk 1 of `law₂Cof₂`. -/
def law₂Cof₂P1 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -2304*U₁^2*U₂^2*V₁^4*V₂*g₂ - 165888*U₁^2*U₂^2*V₁*W₁^3*W₂*g₂*g₃^2
    - 2112*U₁^2*U₂^2*V₂*W₁^4*g₂^4 - 2304*U₁^2*U₂*V₁^2*V₂*W₁^2*W₂*g₂^3
    - 1920*U₁^2*U₂*V₁*V₂^2*W₁^3*g₂^3 - 192*U₁^2*V₁^4*V₂*W₂^2*g₂^2 - 20736*U₁*U₂^2*V₁^4*V₂*W₁*g₃
    - 2304*U₁*U₂*V₁^4*V₂*W₁*W₂*g₂^2 - 25920*U₁*U₂*V₁^2*V₂*W₁^3*W₂*g₂^2*g₃
    - 256*U₁*U₂*V₁*W₁^4*W₂^2*g₂^5 - 192*U₁*V₁^4*V₂^3*W₁*g₂ - 1728*U₁*V₁^4*V₂*W₁*W₂^2*g₂*g₃
    - 1728*U₁*V₁^3*W₁^2*W₂^3*g₂*g₃^2 - 1728*U₁*V₁^2*V₂^3*W₁^3*g₂*g₃
    - 256*U₁*V₁*V₂^2*W₁^4*W₂*g₂^4 - 20736*U₁*V₂*W₁^5*W₂^2*g₂*g₃^3
    - 24192*U₂^2*V₁^3*W₁^3*W₂*g₂^2*g₃ - 24192*U₂^2*V₁*W₁^5*W₂*g₂^2*g₃^2
    - 1728*U₂*V₁^5*W₁*W₂^2*g₂*g₃ - 20736*U₂*V₁^3*W₁^3*W₂^2*g₂*g₃^2 - 20736*U₂*V₂*W₁^6*W₂*g₂*g₃^3
    - 1728*V₁^5*W₁*W₂^3*g₃^2 - 1728*V₁^2*V₂^3*W₁^4*g₃^2 - 240*V₁*V₂^2*W₁^5*W₂*g₂^3*g₃

/-- Chunk 2 of `law₂Cof₂`. -/
def law₂Cof₂P2 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -41472*U₁^2*U₂^2*V₁^3*W₁*W₂*g₂*g₃ - 4224*U₁^2*U₂^2*V₁*W₁^3*W₂*g₂^4
    - 41472*U₁^2*U₂*V₁^3*W₁*W₂^2*g₃^2 - 41472*U₁^2*U₂*V₁*V₂^2*W₁^3*g₃^2
    - 3072*U₁*U₂^3*V₁*W₁^4*g₂^4 - 3456*U₁*U₂^2*V₁^3*W₁^2*W₂*g₂^3
    - 26496*U₁*U₂^2*V₁*W₁^4*W₂*g₂^3*g₃ - 2688*U₁*U₂*V₁^3*V₂^2*W₁^2*g₂^2
    - 39744*U₁*U₂*V₁*W₁^4*W₂^2*g₂^2*g₃^2 - 32832*U₁*U₂*V₂*W₁^5*W₂*g₂^2*g₃^2
    - 4032*U₁*V₁^3*V₂^2*W₁^2*W₂*g₂*g₃ - 400*U₁*V₁^2*V₂*W₁^3*W₂^2*g₂^4
    - 288*U₁*V₁*W₁^4*W₂^3*g₂^4*g₃ - 2816*U₂^3*V₁^3*W₁^3*g₂^3 - 2880*U₂^3*V₁*W₁^5*g₂^3*g₃
    - 3840*U₂^2*V₁^4*V₂*W₁^2*g₂^2 - 384*U₂*V₁^5*V₂^2*W₁*g₂ - 27648*U₂*V₁^2*V₂*W₁^4*W₂*g₂*g₃^2
    - 32*U₂*V₁*V₂^2*W₁^5*g₂^4 - 336*U₂*V₁*W₁^5*W₂^2*g₂^4*g₃ - 25920*U₂*V₁*W₁^5*W₂^2*g₂*g₃^3
    - 3456*V₁^3*W₁^3*W₂^3*g₃^3 - 4*V₂*W₁^6*W₂^2*g₂^6 - 288*V₂*W₁^6*W₂^2*g₂^3*g₃^2

/-- Chunk 3 of `law₂Cof₂`. -/
def law₂Cof₂P3 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -62208*U₁^2*U₂^3*V₁*W₁^3*g₂^2*g₃ - 62208*U₁^2*U₂^2*V₁^2*V₂*W₁^2*g₂*g₃
    - 6912*U₁^2*U₂*V₁^4*V₂*W₂*g₃ - 768*U₁^2*U₂*V₁^3*W₁*W₂^2*g₂^3 - 62208*U₁^2*U₂*V₂*W₁^4*W₂*g₃^3
    - 576*U₁^2*V₁^2*V₂^3*W₁^2*g₂^2 - 5184*U₁^2*V₁^2*V₂*W₁^2*W₂^2*g₂^2*g₃
    - 5184*U₁^2*V₁*V₂^2*W₁^3*W₂*g₂^2*g₃ - 48384*U₁*U₂^3*V₁^3*W₁^2*g₂*g₃
    - 5568*U₁*U₂^2*V₁^2*V₂*W₁^3*g₂^3 - 62208*U₁*U₂^2*V₂*W₁^5*g₃^3 - 512*U₁*U₂*V₂*W₁^5*W₂*g₂^5
    - 528*U₁*V₂*W₁^5*W₂^2*g₂^4*g₃ - 6912*U₂^3*V₁^5*W₁*g₃ - 69120*U₂^3*V₁^3*W₁^3*g₃^2
    - 62208*U₂^3*V₁*W₁^5*g₃^3 - 576*U₂*V₁^3*W₁^3*W₂^2*g₂^4 - 704*U₂*V₁^2*V₂*W₁^4*W₂*g₂^4
    - 6912*U₂*V₁*V₂^2*W₁^5*g₂*g₃^2 - 528*U₂*V₂*W₁^6*W₂*g₂^4*g₃ - 576*V₁^5*V₂^2*W₁*W₂*g₃
    - 64*V₁^3*V₂^2*W₁^3*W₂*g₂^3 - 544*V₁^3*W₁^3*W₂^3*g₂^3*g₃ - 5184*V₁*V₂^2*W₁^5*W₂*g₃^3

/-- Chunk 4 of `law₂Cof₂`. -/
def law₂Cof₂P4 (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    -9216*U₁^2*U₂^3*V₁^3*W₁*g₂^2 - 82944*U₁^2*U₂^2*V₂*W₁^4*g₂*g₃^2
    - 768*U₁^2*V₁^3*V₂^2*W₁*W₂*g₂^2 + 32*U₁^2*V₁*W₁^3*W₂^3*g₂^5
    - 8640*U₁^2*V₁*W₁^3*W₂^3*g₂^2*g₃^2 + 16*U₁^2*V₂*W₁^4*W₂^2*g₂^5
    - 82944*U₁*U₂^2*V₁^2*V₂*W₁^3*g₃^2 - 8640*U₁*V₁^2*V₂*W₁^3*W₂^2*g₂*g₃^2
    - 8640*U₁*V₁*V₂^2*W₁^4*W₂*g₂*g₃^2 + 32*U₂^2*V₁*W₁^5*W₂*g₂^5 + 16*U₂^2*V₂*W₁^6*g₂^5
    - 8064*U₂*V₁^3*V₂^2*W₁^3*g₂*g₃ + 64*V₁^6*V₂^3 + 32*V₁^5*W₁*W₂^3*g₂^3
    - 8640*V₁^4*V₂*W₁^2*W₂^2*g₃^2 + 16*V₁^2*V₂^3*W₁^4*g₂^3 - 912*V₁^2*V₂*W₁^4*W₂^2*g₂^3*g₃
    - 8*V₁*W₁^5*W₂^3*g₂^6 + 144*V₁*W₁^5*W₂^3*g₂^3*g₃^2

/-- Cofactor of `F(Q)` in `F(law₂(P, Q))`. -/
def law₂Cof₂ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) : R :=
    law₂Cof₂P0 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₂P1 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₂P2 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₂P3 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ +
    law₂Cof₂P4 g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂

set_option maxHeartbeats 4000000 in
-- `ring` on a bidegree `(6, 6)` identity with several thousand monomials
set_option maxRecDepth 100000 in
/-- `F(law₁(P, Q)) = c₁ F(P) + c₂ F(Q)`, an identity in `ℤ[g₂, g₃][U₁, …, W₂]`. -/
theorem F_law₁ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    F g₂ g₃ (law₁U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂)
      (law₁V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂)
      (law₁W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₁Cof₁ g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * F g₂ g₃ U₁ V₁ W₁ +
        law₁Cof₂ g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * F g₂ g₃ U₂ V₂ W₂ := by
  simp only [F, law₁U, law₁V, law₁W, law₁Cof₁, law₁Cof₂,
    law₁Cof₁P0, law₁Cof₁P1, law₁Cof₁P2, law₁Cof₂P0, law₁Cof₂P1, law₁Cof₂P2]
  ring

set_option maxHeartbeats 4000000 in
-- `ring` on a bidegree `(6, 6)` identity with several thousand monomials
set_option maxRecDepth 100000 in
/-- `F(law₂(P, Q)) = c₁ F(P) + c₂ F(Q)`, an identity in `ℤ[g₂, g₃][U₁, …, W₂]`. -/
theorem F_law₂ (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R) :
    F g₂ g₃ (law₂U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂)
      (law₂V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂)
      (law₂W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂) =
      law₂Cof₁ g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * F g₂ g₃ U₁ V₁ W₁ +
        law₂Cof₂ g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * F g₂ g₃ U₂ V₂ W₂ := by
  simp only [F, law₂U, law₂V, law₂W, law₂Cof₁, law₂Cof₂,
    law₂Cof₁P0, law₂Cof₁P1, law₂Cof₁P2, law₂Cof₁P3, law₂Cof₁P4, law₂Cof₁P5, law₂Cof₁P6,
    law₂Cof₂P0, law₂Cof₂P1, law₂Cof₂P2, law₂Cof₂P3, law₂Cof₂P4]
  ring

/-! ### The two laws are proportional on `E × E` -/

theorem law₁_cross_law₂_VW (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R)
    (hP : F g₂ g₃ U₁ V₁ W₁ = 0) (hQ : F g₂ g₃ U₂ V₂ W₂ = 0) :
    law₁V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ =
      law₁W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ := by
  linear_combination (norm := (simp only [law₁V, law₁W, law₂V, law₂W, F]; ring))
    (144*U₁*U₂^3*W₂*g₂ - 144*U₁*U₂^2*V₂^2 + 432*U₁*U₂^2*W₂^2*g₃ + 12*U₁*U₂*W₂^3*g₂^2
      - 144*U₂^4*W₁*g₂ + 24*U₂^2*W₁*W₂^2*g₂^2 + 48*U₂*V₂^2*W₁*W₂*g₂ - W₁*W₂^4*g₂^3) * hP +
    (144*U₁^2*U₂*V₁^2 - 432*U₁^2*U₂*W₁^2*g₃ + 12*U₁^2*W₁^2*W₂*g₂^2 - 48*U₁*U₂*W₁^3*g₂^2
      - 12*U₁*V₁^2*W₁*W₂*g₂ + 36*U₁*W₁^3*W₂*g₂*g₃ - 36*U₂*V₁^2*W₁^2*g₂ - 36*U₂*W₁^4*g₂*g₃
      + W₁^4*W₂*g₂^3) * hQ

theorem law₁_cross_law₂_WU (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R)
    (hP : F g₂ g₃ U₁ V₁ W₁ = 0) (hQ : F g₂ g₃ U₂ V₂ W₂ = 0) :
    law₁W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ =
      law₁U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂W g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ := by
  linear_combination (norm := (simp only [law₁W, law₁U, law₂W, law₂U, F]; ring))
    (12*U₂^2*V₁*W₂^2*g₂ + 12*U₂^2*V₂*W₁*W₂*g₂ - 12*U₂*V₁*V₂^2*W₂ + 36*U₂*V₁*W₂^3*g₃
      - 12*U₂*V₂^3*W₁ + 36*U₂*V₂*W₁*W₂^2*g₃ + V₁*W₂^4*g₂^2 + V₂*W₁*W₂^3*g₂^2) * hP +
    (-12*U₁^2*V₁*W₁*W₂*g₂ - 12*U₁^2*V₂*W₁^2*g₂ + 12*U₁*V₁^3*W₂ + 12*U₁*V₁^2*V₂*W₁
      - 36*U₁*V₁*W₁^2*W₂*g₃ - 36*U₁*V₂*W₁^3*g₃ - V₁*W₁^3*W₂*g₂^2 - V₂*W₁^4*g₂^2) * hQ

theorem law₁_cross_law₂_UV (g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ : R)
    (hP : F g₂ g₃ U₁ V₁ W₁ = 0) (hQ : F g₂ g₃ U₂ V₂ W₂ = 0) :
    law₁U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ =
      law₁V g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ * law₂U g₂ g₃ U₁ V₁ W₁ U₂ V₂ W₂ := by
  linear_combination (norm := (simp only [law₁U, law₁V, law₂U, law₂V, F]; ring))
    (-12*U₁*U₂^2*W₂^2*g₂^2 + 12*U₁*U₂*V₂^2*W₂*g₂ - 36*U₁*U₂*W₂^3*g₂*g₃ - U₁*W₂^4*g₂^3
      - 12*U₂^2*V₁*V₂*W₂*g₂ + 12*U₂^2*V₂^2*W₁*g₂ - 72*U₂^2*W₁*W₂^2*g₂*g₃ + 12*U₂*V₁*V₂^3
      - 36*U₂*V₁*V₂*W₂^2*g₃ + 36*U₂*V₂^2*W₁*W₂*g₃ - 4*U₂*W₁*W₂^3*g₂^3 - 108*U₂*W₁*W₂^3*g₃^2
      - V₁*V₂*W₂^3*g₂^2 - 3*V₂^2*W₁*W₂^2*g₂^2 - 6*W₁*W₂^4*g₂^2*g₃) * hP +
    (12*U₁^2*U₂*W₁^2*g₂^2 - 12*U₁^2*V₁^2*W₂*g₂ + 12*U₁^2*V₁*V₂*W₁*g₂ + 72*U₁^2*W₁^2*W₂*g₂*g₃
      - 12*U₁*U₂*V₁^2*W₁*g₂ + 36*U₁*U₂*W₁^3*g₂*g₃ - 12*U₁*V₁^3*V₂ - 36*U₁*V₁^2*W₁*W₂*g₃
      + 36*U₁*V₁*V₂*W₁^2*g₃ + 4*U₁*W₁^3*W₂*g₂^3 + 108*U₁*W₁^3*W₂*g₃^2 + U₂*W₁^4*g₂^3
      + 3*V₁^2*W₁^2*W₂*g₂^2 + V₁*V₂*W₁^3*g₂^2 + 6*W₁^4*W₂*g₂^2*g₃) * hQ

/-! ### The diagonal -/

theorem law₂_self_U (g₂ g₃ U V W : R) :
    law₂U g₂ g₃ U V W U V W = dblU g₂ g₃ U V W := by
  simp only [law₂U, dblU]
  ring

theorem law₂_self_V (g₂ g₃ U V W : R) (h : F g₂ g₃ U V W = 0) :
    law₂V g₂ g₃ U V W U V W = dblV g₂ g₃ U V W := by
  linear_combination (norm := (simp only [law₂V, dblV, F]; ring)) (12*U*g₂ - 36*W*g₃) * h

theorem law₂_self_W (g₂ g₃ U V W : R) (h : F g₂ g₃ U V W = 0) :
    law₂W g₂ g₃ U V W U V W = dblW g₂ g₃ U V W := by
  linear_combination (norm := (simp only [law₂W, dblW, F]; ring)) (-24*V) * h

/-! ### Vector form

Points of the cone are vectors `P : Fin 3 → R` with `P 0 = U`, `P 1 = V`, `P 2 = W`
(Mathlib's convention for projective coordinates). -/

/-- `F` on a vector. -/
def Fv (g₂ g₃ : R) (P : Fin 3 → R) : R :=
  F g₂ g₃ (P 0) (P 1) (P 2)

/-- The first addition law (Mathlib's chord law, transported), bidegree `(2, 2)`. -/
def law₁ (g₂ g₃ : R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![law₁U g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
    law₁V g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
    law₁W g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]

/-- The second addition law (the Bosma–Lenstra law of the line `V = 0`), bidegree `(2, 2)`. -/
def law₂ (g₂ g₃ : R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![law₂U g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
    law₂V g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2),
    law₂W g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2)]

/-- The doubling form (degree `4`). -/
def dbl (g₂ g₃ : R) (P : Fin 3 → R) : Fin 3 → R :=
  ![dblU g₂ g₃ (P 0) (P 1) (P 2), dblV g₂ g₃ (P 0) (P 1) (P 2), dblW g₂ g₃ (P 0) (P 1) (P 2)]

/-- The identity element `O = (0 : 1 : 0)`. -/
def O : Fin 3 → R :=
  ![0, 1, 0]

/-- Negation `(U : V : W) ↦ (U : −V : W)`. -/
def negv (P : Fin 3 → R) : Fin 3 → R :=
  ![P 0, -P 1, P 2]

variable (g₂ g₃ : R) (P Q : Fin 3 → R)

theorem Fv_O : Fv g₂ g₃ (O : Fin 3 → R) = 0 := by
  simp [Fv, F, O]

theorem Fv_negv : Fv g₂ g₃ (negv P) = Fv g₂ g₃ P := by
  simp only [Fv, F, negv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **(a) for `law₁`**: `F(law₁(P, Q)) = c₁ F(P) + c₂ F(Q)`. -/
theorem Fv_law₁ : Fv g₂ g₃ (law₁ g₂ g₃ P Q) =
    law₁Cof₁ g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2) * Fv g₂ g₃ P +
      law₁Cof₂ g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2) * Fv g₂ g₃ Q :=
  F_law₁ ..

/-- **(a) for `law₂`**: `F(law₂(P, Q)) = c₁ F(P) + c₂ F(Q)`. -/
theorem Fv_law₂ : Fv g₂ g₃ (law₂ g₂ g₃ P Q) =
    law₂Cof₁ g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2) * Fv g₂ g₃ P +
      law₂Cof₂ g₂ g₃ (P 0) (P 1) (P 2) (Q 0) (Q 1) (Q 2) * Fv g₂ g₃ Q :=
  F_law₂ ..

/-- **(a)**, ideal form: `F(law₁(P, Q)) ∈ (F(P), F(Q))`. -/
theorem Fv_law₁_mem : Fv g₂ g₃ (law₁ g₂ g₃ P Q) ∈ Ideal.span {Fv g₂ g₃ P, Fv g₂ g₃ Q} :=
  Ideal.mem_span_pair.mpr ⟨_, _, (Fv_law₁ g₂ g₃ P Q).symm⟩

/-- **(a)**, ideal form: `F(law₂(P, Q)) ∈ (F(P), F(Q))`. -/
theorem Fv_law₂_mem : Fv g₂ g₃ (law₂ g₂ g₃ P Q) ∈ Ideal.span {Fv g₂ g₃ P, Fv g₂ g₃ Q} :=
  Ideal.mem_span_pair.mpr ⟨_, _, (Fv_law₂ g₂ g₃ P Q).symm⟩

/-- `law₁` is bihomogeneous of bidegree `(2, 2)`. -/
theorem law₁_smul (u v : R) : law₁ g₂ g₃ (u • P) (v • Q) = (u * v) ^ 2 • law₁ g₂ g₃ P Q := by
  funext i
  fin_cases i <;>
  · simp only [law₁, law₁U, law₁V, law₁W, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₂` is bihomogeneous of bidegree `(2, 2)`. -/
theorem law₂_smul (u v : R) : law₂ g₂ g₃ (u • P) (v • Q) = (u * v) ^ 2 • law₂ g₂ g₃ P Q := by
  funext i
  fin_cases i <;>
  · simp only [law₂, law₂U, law₂V, law₂W, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

theorem dbl_smul (u : R) : dbl g₂ g₃ (u • P) = u ^ 4 • dbl g₂ g₃ P := by
  funext i
  fin_cases i <;>
  · simp only [dbl, dblU, dblV, dblW, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₁` is antisymmetric. -/
theorem law₁_swap : law₁ g₂ g₃ Q P = -law₁ g₂ g₃ P Q := by
  funext i
  fin_cases i <;>
  · simp only [law₁, law₁U, law₁V, law₁W, Pi.neg_apply, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₂` is symmetric. -/
theorem law₂_swap : law₂ g₂ g₃ Q P = law₂ g₂ g₃ P Q := by
  funext i
  fin_cases i <;>
  · simp only [law₂, law₂U, law₂V, law₂W, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₁` vanishes on the diagonal. -/
theorem law₁_self : law₁ g₂ g₃ P P = 0 := by
  funext i
  fin_cases i <;>
  · simp only [law₁, law₁U, law₁V, law₁W, Pi.zero_apply, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₁(P, O) = −W(P) · P`. -/
theorem law₁_O_right : law₁ g₂ g₃ P O = (-P 2) • P := by
  funext i
  fin_cases i <;>
  · simp only [law₁, law₁U, law₁V, law₁W, O, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₂(P, O) = 4V(P) · P`. -/
theorem law₂_O_right : law₂ g₂ g₃ P O = (4 * P 1) • P := by
  funext i
  fin_cases i <;>
  · simp only [law₂, law₂U, law₂V, law₂W, O, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring

/-- `law₁(O, Q) = W(Q) · Q`. -/
theorem law₁_O_left : law₁ g₂ g₃ O Q = Q 2 • Q := by
  rw [law₁_swap, law₁_O_right]
  funext i
  simp

/-- `law₂(O, Q) = 4V(Q) · Q`. -/
theorem law₂_O_left : law₂ g₂ g₃ O Q = (4 * Q 1) • Q := by
  rw [law₂_swap, law₂_O_right]

variable {g₂ g₃ P Q}

/-- On `E × E` all `2 × 2` minors of `(law₁(P, Q), law₂(P, Q))` vanish. -/
theorem law₁_cross_law₂ (hP : Fv g₂ g₃ P = 0) (hQ : Fv g₂ g₃ Q = 0) (i j : Fin 3) :
    law₁ g₂ g₃ P Q i * law₂ g₂ g₃ P Q j = law₁ g₂ g₃ P Q j * law₂ g₂ g₃ P Q i := by
  simp only [Fv] at hP hQ
  have h1 := law₁_cross_law₂_VW g₂ g₃ _ _ _ _ _ _ hP hQ
  have h2 := law₁_cross_law₂_WU g₂ g₃ _ _ _ _ _ _ hP hQ
  have h3 := law₁_cross_law₂_UV g₂ g₃ _ _ _ _ _ _ hP hQ
  fin_cases i <;> fin_cases j <;>
  simp only [law₁, law₂, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
  first | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm

/-- On `E`, `law₂(P, P) = dbl(P)`. -/
theorem law₂_self (hP : Fv g₂ g₃ P = 0) : law₂ g₂ g₃ P P = dbl g₂ g₃ P := by
  simp only [Fv] at hP
  funext i
  fin_cases i
  · exact law₂_self_U ..
  · exact law₂_self_V _ _ _ _ _ hP
  · exact law₂_self_W _ _ _ _ _ hP

end LSG.Elliptic
