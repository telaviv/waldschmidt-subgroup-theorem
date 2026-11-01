import Mathlib
import LSG.MEV.FibreId00
import LSG.MEV.FibreId01
import LSG.MEV.FibreId10
import LSG.MEV.FibreId11

/-!
# The fibre identity for all eight laws and all chart pairs

`fib_eq`: for `D P = s c2_a(P)`, `D Q = 0`, `P_a = 1`, the base expression `fibE` of the fibre
half of the translation identity lies in `(F(P), F(Q))` (dispatch to the 32 generated identities
of `LSG.MEV.FibreId{i}{a}`).
-/

open LSG.Elliptic LSG.ME

namespace LSG.MEV

variable {R : Type*} [CommRing R]

theorem fib_eq {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (i j k a b : Fin 2)
    (g₂ g₃ s : R) (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0)
    (hQ : ∀ j, D (Q j) = 0) :
    (∀ j, D (P j) = s * c2 (biE a) g₂ g₃ P j) → P (biE a) = 1 →
    ∃ f₁ f₂ : R, fibE D i j k a b g₂ g₃ s P Q = f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q :=
  match i, j, k, a, b with
  | 0, 0, 0, 0, 0 => fibId_000_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 0, 0, 1 => fibId_000_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 0, 1, 0 => fibId_000_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 0, 1, 1 => fibId_000_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 1, 0, 0 => fibId_001_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 1, 0, 1 => fibId_001_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 1, 1, 0 => fibId_001_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 0, 1, 1, 1 => fibId_001_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 0, 0, 0 => fibId_010_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 0, 0, 1 => fibId_010_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 0, 1, 0 => fibId_010_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 0, 1, 1 => fibId_010_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 1, 0, 0 => fibId_011_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 1, 0, 1 => fibId_011_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 1, 1, 0 => fibId_011_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 0, 1, 1, 1, 1 => fibId_011_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 0, 0, 0 => fibId_100_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 0, 0, 1 => fibId_100_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 0, 1, 0 => fibId_100_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 0, 1, 1 => fibId_100_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 1, 0, 0 => fibId_101_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 1, 0, 1 => fibId_101_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 1, 1, 0 => fibId_101_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 0, 1, 1, 1 => fibId_101_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 0, 0, 0 => fibId_110_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 0, 0, 1 => fibId_110_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 0, 1, 0 => fibId_110_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 0, 1, 1 => fibId_110_11 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 1, 0, 0 => fibId_111_00 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 1, 0, 1 => fibId_111_01 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 1, 1, 0 => fibId_111_10 D g₂ g₃ s P Q hg₂ hg₃ hQ
  | 1, 1, 1, 1, 1 => fibId_111_11 D g₂ g₃ s P Q hg₂ hg₃ hQ

end LSG.MEV
