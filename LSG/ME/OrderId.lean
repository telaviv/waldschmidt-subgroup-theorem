import Mathlib
import LSG.Elliptic.AdditionLaws

/-!
# Polynomial identities for chart derivations and translations (generated)

Generated with sympy (division by the cone forms `F(P)`, `F(Q)` with respect to `U₁`, `U₂`).
Over an arbitrary commutative ring; `P` is the moving cone vector, `Q` the translating one.

* `c2 a`: the chart derivation of chart `a` (`0, 1, 2` = `U, V, W`), **doubled** so that the
  coefficients are integers (`c2 a = 2 · chartPoly a`).
* `cc_eq` (**chart change**): `P_a · c2_b(P) − P_b · c2_a(P) = ccE_{ab}(P) · P + f · F(P)`,
  i.e. `L_a δ_b − L_b δ_a` is a multiple of the Euler derivation modulo `F`.
* `tr_eq_cab` (**translation**): for a derivation `D` with `D P = s · c2_a(P)` (and `D Q = 0`) and
  `A = law_c(P, Q)`: `A_b · D(A_i) − s · P_a · c2_b(A)_i − s · trE_{cab} · A_i ∈ s · (F(P), F(Q))`,
  for charts `a, b ∈ {V, W}`. Analytically: the invariant derivation commutes with translation, up
  to the chart multipliers `L_a(P)`, `L_b(A)` and an Euler term.
-/

open LSG.Elliptic

-- generated polynomial identities: long lines are kept unbroken
set_option linter.style.longLine false

namespace LSG.ME

variable {R : Type*} [CommRing R]

@[simp] theorem D_ofNat {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (n : ℕ)
    [n.AtLeastTwo] : D (no_index (OfNat.ofNat n) : R) = 0 := by
  rw [← Nat.cast_ofNat]; exact D.map_natCast n

/-- The chart derivations, doubled (integral coefficients); chart `0, 1, 2` = `U, V, W`. -/
def c2 (a : Fin 3) (g₂ g₃ : R) (P : Fin 3 → R) : Fin 3 → R :=
  ![![2*(P 0)*(P 1), 2*(P 0)*(P 2)*(g₂) + 3*(P 1)^2 + 3*(P 2)^2*(g₃), 0],
    ![-2*(P 0)*(P 2)*(g₂) - (P 1)^2 - 3*(P 2)^2*(g₃), 0, -12*(P 0)^2 + (P 2)^2*(g₂)],
    ![2*(P 1)*(P 2), 12*(P 0)^2 - (P 2)^2*(g₂), 0]] a

/-- Euler coefficient of the chart change (doubled). -/
def ccE (a b : Fin 3) (g₂ g₃ : R) (P : Fin 3 → R) : R :=
  ![![0, -2*(P 0)*(P 2)*(g₂) - 3*(P 1)^2 - 3*(P 2)^2*(g₃), 0],
    ![2*(P 0)*(P 2)*(g₂) + 3*(P 1)^2 + 3*(P 2)^2*(g₃), 0, 12*(P 0)^2 - (P 2)^2*(g₂)],
    ![0, -12*(P 0)^2 + (P 2)^2*(g₂), 0]] a b

/-- **Chart change**: `L_a δ_b − L_b δ_a = e · Euler` modulo `F` (doubled). -/
theorem cc_eq (a b c : Fin 3) (g₂ g₃ : R) (P : Fin 3 → R) : ∃ f : R,
    P a * c2 b g₂ g₃ P c - P b * c2 a g₂ g₃ P c - ccE a b g₂ g₃ P * P c = f * Fv g₂ g₃ P := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only [c2, ccE, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨-3, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩
  · exact ⟨0, by ring⟩

/-- Euler coefficient of the translation identity (doubled), law 0, charts 1, 1. -/
def trE011 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  -24*(P 0)^2*(Q 0)*(P 1)*(Q 2)*(g₂) - 24*(P 0)^2*(Q 0)*(Q 1)*(P 2)*(g₂) + 12*(P 0)^2*(P 1)*(Q 1)^2 - 36*(P 0)^2*(P 1)*(Q 2)^2*(g₃) + 72*(P 0)^2*(Q 1)*(P 2)*(Q 2)*(g₃) + 24*(P 0)*(Q 0)^2*(P 1)*(P 2)*(g₂) - 24*(P 0)*(Q 0)*(P 1)^2*(Q 1) - 72*(P 0)*(Q 0)*(Q 1)*(P 2)^2*(g₃) - 2*(P 0)*(P 1)*(P 2)*(Q 2)^2*(g₂)^2 + 8*(P 0)*(Q 1)*(P 2)^2*(Q 2)*(g₂)^2 + 12*(Q 0)^2*(P 1)^3 + 36*(Q 0)^2*(P 1)*(P 2)^2*(g₃) + 2*(Q 0)*(P 1)*(P 2)^2*(Q 2)*(g₂)^2 - 2*(Q 0)*(Q 1)*(P 2)^3*(g₂)^2 - (P 1)^3*(Q 2)^2*(g₂) + 8*(P 1)^2*(Q 1)*(P 2)*(Q 2)*(g₂) - (P 1)*(Q 1)^2*(P 2)^2*(g₂) + 6*(Q 1)*(P 2)^3*(Q 2)*(g₂)*(g₃)

/-- Euler coefficient of the translation identity (doubled), law 0, charts 1, 2. -/
def trE012 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  72*(P 0)^2*(Q 0)*(P 2)*(Q 2)*(g₂) + 24*(P 0)^2*(Q 1)^2*(P 2) - 48*(P 0)*(Q 0)^2*(P 2)^2*(g₂) + 24*(P 0)*(Q 0)*(P 1)^2*(Q 2) + 72*(P 0)*(Q 0)*(P 2)^2*(Q 2)*(g₃) - 4*(P 0)*(P 2)^2*(Q 2)^2*(g₂)^2 - 48*(Q 0)^2*(P 1)^2*(P 2) - 72*(Q 0)^2*(P 2)^3*(g₃) - 2*(Q 0)*(P 2)^3*(Q 2)*(g₂)^2 - 4*(P 1)^2*(P 2)*(Q 2)^2*(g₂) - 2*(Q 1)^2*(P 2)^3*(g₂) - 6*(P 2)^3*(Q 2)^2*(g₂)*(g₃)

set_option linter.unusedVariables false in
/-- Euler coefficient of the translation identity (doubled), law 0, charts 2, 1. -/
def trE021 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  24*(P 0)^2*(Q 0)*(P 2)*(Q 2)*(g₂) + 24*(P 0)^2*(P 1)*(Q 1)*(Q 2) - 12*(P 0)^2*(Q 1)^2*(P 2) + 36*(P 0)^2*(P 2)*(Q 2)^2*(g₃) - 24*(P 0)*(Q 0)^2*(P 2)^2*(g₂) + 48*(P 0)*(Q 0)*(P 1)*(Q 1)*(P 2) + 2*(P 0)*(P 2)^2*(Q 2)^2*(g₂)^2 - 60*(Q 0)^2*(P 1)^2*(P 2) - 36*(Q 0)^2*(P 2)^3*(g₃) - 2*(Q 0)*(P 2)^3*(Q 2)*(g₂)^2 + 5*(P 1)^2*(P 2)*(Q 2)^2*(g₂) - 6*(P 1)*(Q 1)*(P 2)^2*(Q 2)*(g₂) + (Q 1)^2*(P 2)^3*(g₂)

/-- Euler coefficient of the translation identity (doubled), law 0, charts 2, 2. -/
def trE022 (_g₂ _g₃ : R) (P Q : Fin 3 → R) : R :=
  24*(P 0)^2*(P 1)*(Q 2)^2 - 48*(P 0)*(Q 0)*(P 1)*(P 2)*(Q 2) + 24*(Q 0)^2*(P 1)*(P 2)^2

/-- Euler coefficient of the translation identity (doubled), law 1, charts 1, 1. -/
def trE111 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  288*(P 0)^2*(Q 0)^2*(P 2)*(g₂)^2 + 864*(P 0)^2*(Q 0)*(P 2)*(Q 2)*(g₂)*(g₃) - 8*(P 0)^2*(P 2)*(Q 2)^2*(g₂)^3 + 864*(P 0)^2*(P 2)*(Q 2)^2*(g₃)^2 + 96*(P 0)*(Q 0)^2*(P 1)^2*(g₂) + 864*(P 0)*(Q 0)^2*(P 2)^2*(g₂)*(g₃) + 288*(P 0)*(Q 0)*(P 1)^2*(Q 2)*(g₃) + 64*(P 0)*(Q 0)*(P 2)^2*(Q 2)*(g₂)^3 + 864*(P 0)*(Q 0)*(P 2)^2*(Q 2)*(g₃)^2 + 8*(P 0)*(P 1)^2*(Q 2)^2*(g₂)^2 + 72*(P 0)*(P 2)^2*(Q 2)^2*(g₂)^2*(g₃) + 576*(Q 0)^2*(P 1)^2*(P 2)*(g₃) - 8*(Q 0)^2*(P 2)^3*(g₂)^3 + 864*(Q 0)^2*(P 2)^3*(g₃)^2 + 64*(Q 0)*(P 1)^2*(P 2)*(Q 2)*(g₂)^2 + 72*(Q 0)*(P 2)^3*(Q 2)*(g₂)^2*(g₃) + 48*(P 1)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) + 2*(P 2)^3*(Q 2)^2*(g₂)^4

/-- Euler coefficient of the translation identity (doubled), law 1, charts 1, 2. -/
def trE112 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  96*(P 0)^2*(Q 0)*(P 1)*(Q 2)*(g₂) - 96*(P 0)^2*(Q 0)*(Q 1)*(P 2)*(g₂) - 48*(P 0)^2*(P 1)*(Q 1)^2 + 144*(P 0)^2*(P 1)*(Q 2)^2*(g₃) + 288*(P 0)^2*(Q 1)*(P 2)*(Q 2)*(g₃) - 96*(P 0)*(Q 0)^2*(P 1)*(P 2)*(g₂) - 96*(P 0)*(Q 0)*(P 1)^2*(Q 1) - 288*(P 0)*(Q 0)*(Q 1)*(P 2)^2*(g₃) + 8*(P 0)*(P 1)*(P 2)*(Q 2)^2*(g₂)^2 + 32*(P 0)*(Q 1)*(P 2)^2*(Q 2)*(g₂)^2 - 48*(Q 0)^2*(P 1)^3 - 144*(Q 0)^2*(P 1)*(P 2)^2*(g₃) - 8*(Q 0)*(P 1)*(P 2)^2*(Q 2)*(g₂)^2 - 8*(Q 0)*(Q 1)*(P 2)^3*(g₂)^2 + 4*(P 1)^3*(Q 2)^2*(g₂) + 32*(P 1)^2*(Q 1)*(P 2)*(Q 2)*(g₂) + 4*(P 1)*(Q 1)^2*(P 2)^2*(g₂) + 24*(Q 1)*(P 2)^3*(Q 2)*(g₂)*(g₃)

/-- Euler coefficient of the translation identity (doubled), law 1, charts 2, 1. -/
def trE121 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  96*(P 0)^2*(P 1)*(Q 1)^2 - 192*(P 0)*(Q 0)^2*(P 1)*(P 2)*(g₂) - 576*(P 0)*(Q 0)*(P 1)*(P 2)*(Q 2)*(g₃) - 16*(P 0)*(P 1)*(P 2)*(Q 2)^2*(g₂)^2 - 288*(Q 0)^2*(P 1)*(P 2)^2*(g₃) - 32*(Q 0)*(P 1)*(P 2)^2*(Q 2)*(g₂)^2 - 8*(P 1)*(Q 1)^2*(P 2)^2*(g₂) - 24*(P 1)*(P 2)^2*(Q 2)^2*(g₂)*(g₃)

/-- Euler coefficient of the translation identity (doubled), law 1, charts 2, 2. -/
def trE122 (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  -96*(P 0)^2*(Q 0)*(P 2)*(Q 2)*(g₂) + 96*(P 0)^2*(P 1)*(Q 1)*(Q 2) + 48*(P 0)^2*(Q 1)^2*(P 2) - 144*(P 0)^2*(P 2)*(Q 2)^2*(g₃) + 96*(P 0)*(Q 0)^2*(P 2)^2*(g₂) + 192*(P 0)*(Q 0)*(P 1)*(Q 1)*(P 2) - 8*(P 0)*(P 2)^2*(Q 2)^2*(g₂)^2 + 240*(Q 0)^2*(P 1)^2*(P 2) + 144*(Q 0)^2*(P 2)^3*(g₃) + 8*(Q 0)*(P 2)^3*(Q 2)*(g₂)^2 - 20*(P 1)^2*(P 2)*(Q 2)^2*(g₂) - 24*(P 1)*(Q 1)*(P 2)^2*(Q 2)*(g₂) - 4*(Q 1)^2*(P 2)^3*(g₂)

/-- The Euler coefficient of the translation identity (doubled); `0` off `a, b ∈ {V, W}`. -/
def trE (c : Fin 2) (a b : Fin 3) (g₂ g₃ : R) (P Q : Fin 3 → R) : R :=
  match c, a, b with
  | 0, 1, 1 => trE011 g₂ g₃ P Q
  | 0, 1, 2 => trE012 g₂ g₃ P Q
  | 0, 2, 1 => trE021 g₂ g₃ P Q
  | 0, 2, 2 => trE022 g₂ g₃ P Q
  | 1, 1, 1 => trE111 g₂ g₃ P Q
  | 1, 1, 2 => trE112 g₂ g₃ P Q
  | 1, 2, 1 => trE121 g₂ g₃ P Q
  | 1, 2, 2 => trE122 g₂ g₃ P Q
  | _, _, _ => 0

theorem tr_eq_011 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 1 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₁ g₂ g₃ P Q 1 * D (law₁ g₂ g₃ P Q i) - s * (P 1 * c2 1 g₂ g₃ (law₁ g₂ g₃ P Q) i) -
      s * (trE011 g₂ g₃ P Q * law₁ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₁, law₁U, law₁V, law₁W, c2, trE011, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨-36*(P 0)^2*(Q 0)*(Q 1)^3 - 108*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₃) + 72*(P 0)*(Q 0)^3*(Q 1)*(P 2)*(g₂) + 72*(P 0)*(Q 0)^2*(P 1)*(Q 1)^2 + 216*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₃) - 6*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 - 6*(P 0)*(P 1)*(Q 1)^2*(Q 2)^2*(g₂) + 6*(P 0)*(Q 1)^3*(P 2)*(Q 2)*(g₂) - 72*(Q 0)^4*(P 1)*(P 2)*(g₂) + 18*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₂)^2 - 12*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₂)^2 - 6*(Q 0)*(P 1)*(Q 1)^2*(P 2)*(Q 2)*(g₂) + 18*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)*(g₃) - 3*(Q 0)*(Q 1)^3*(P 2)^2*(g₂) - 45*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)*(g₃) - 9*(P 1)^2*(Q 1)^3*(Q 2) + 9*(P 1)^2*(Q 1)*(Q 2)^3*(g₃) - 36*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₃) - 9*(Q 1)^3*(P 2)^2*(Q 2)*(g₃) - 27*(Q 1)*(P 2)^2*(Q 2)^3*(g₃)^2,
      -36*(P 0)^2*(Q 0)*(P 1)^3 - 108*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₃) + 12*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₂)^2 - 12*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₂)^2 + 12*(P 0)*(P 1)^3*(P 2)*(Q 2)*(g₂) + 12*(P 0)*(P 1)^2*(Q 1)*(P 2)^2*(g₂) + 36*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)*(g₃) - 15*(Q 0)*(P 1)^3*(P 2)^2*(g₂) - 9*(Q 0)*(P 1)*(P 2)^4*(g₂)*(g₃) + 3*(P 1)^5*(Q 2) + 6*(P 1)^4*(Q 1)*(P 2) + 18*(P 1)^3*(P 2)^2*(Q 2)*(g₃) + 18*(P 1)^2*(Q 1)*(P 2)^3*(g₃) + 27*(P 1)*(P 2)^4*(Q 2)*(g₃)^2, by ring⟩
  · exact ⟨-72*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2)*(g₂) + 72*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₂) - 6*(P 0)*(P 1)*(Q 1)*(Q 2)^3*(g₂)^2 + 12*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)^2 - 12*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 + 6*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂)^2 - 6*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₂) + 6*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₂) - 18*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂)*(g₃) + 18*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)*(g₃),
      0, by ring⟩
  · exact ⟨432*(P 0)^2*(Q 0)^3*(Q 1) + 36*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂) - 432*(P 0)*(Q 0)^4*(P 1) + 108*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂) - 216*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂) - 36*(P 0)*(Q 0)*(P 1)*(Q 1)^2*(Q 2) + 108*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₃) - 72*(P 0)*(Q 0)*(Q 1)^3*(P 2) - 216*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₃) - 6*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^2 + 72*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂) + 36*(Q 0)^3*(Q 1)*(P 2)^2*(g₂) + 36*(Q 0)^2*(P 1)^2*(Q 1)*(Q 2) + 72*(Q 0)^2*(P 1)*(Q 1)^2*(P 2) + 108*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃) - 18*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2 + 15*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2 - 9*(P 1)^2*(Q 1)*(Q 2)^3*(g₂) - 12*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) - 18*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃) + 12*(Q 1)^3*(P 2)^2*(Q 2)*(g₂) + 9*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)*(g₃),
      -36*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₂) + 36*(P 0)^2*(P 1)^3*(Q 2) + 72*(P 0)^2*(P 1)^2*(Q 1)*(P 2) + 108*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₃) - 108*(P 0)*(Q 0)*(P 1)^3*(P 2) - 108*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₃) + 12*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)^2 - 3*(Q 0)*(P 1)*(P 2)^4*(g₂)^2 + 15*(P 1)^3*(P 2)^2*(Q 2)*(g₂) - 6*(P 1)^2*(Q 1)*(P 2)^3*(g₂) + 9*(P 1)*(P 2)^4*(Q 2)*(g₂)*(g₃), by ring⟩

theorem tr_eq_012 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 1 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₁ g₂ g₃ P Q 2 * D (law₁ g₂ g₃ P Q i) - s * (P 1 * c2 2 g₂ g₃ (law₁ g₂ g₃ P Q) i) -
      s * (trE012 g₂ g₃ P Q * law₁ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₁, law₁U, law₁V, law₁W, c2, trE012, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨36*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2) + 108*(P 0)^2*(Q 0)*(Q 2)^3*(g₃) - 72*(P 0)*(Q 0)^3*(P 2)*(Q 2)*(g₂) - 144*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2) - 36*(P 0)*(Q 0)^2*(Q 1)^2*(P 2) - 324*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₃) - 6*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^2 - 9*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) - 9*(P 0)*(P 2)*(Q 2)^4*(g₂)*(g₃) + 72*(Q 0)^4*(P 2)^2*(g₂) + 72*(Q 0)^3*(P 1)^2*(Q 2) + 144*(Q 0)^3*(P 1)*(Q 1)*(P 2) + 216*(Q 0)^3*(P 2)^2*(Q 2)*(g₃) + 6*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^2 - 6*(Q 0)*(P 1)^2*(Q 2)^3*(g₂) - 3*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂) + 9*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)*(g₃) - 3*(P 1)^2*(Q 1)^2*(Q 2)^2 - 9*(P 1)^2*(Q 2)^4*(g₃) - 12*(P 1)*(Q 1)^3*(P 2)*(Q 2) - 3*(Q 1)^4*(P 2)^2 - 9*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₃),
      -72*(P 0)^2*(Q 0)*(P 1)^2*(P 2) + 12*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂) + 6*(Q 0)*(P 1)^2*(P 2)^3*(g₂) + 6*(P 1)^4*(P 2)*(Q 2) + 12*(P 1)^3*(Q 1)*(P 2)^2 + 18*(P 1)^2*(P 2)^3*(Q 2)*(g₃), by ring⟩
  · exact ⟨72*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂) - 108*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂) + 72*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂) + 36*(P 0)*(Q 0)*(P 1)*(Q 1)^2*(Q 2) - 108*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₃) + 72*(P 0)*(Q 0)*(Q 1)^3*(P 2) + 216*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₃) + 3*(P 0)*(P 1)*(Q 2)^4*(g₂)^2 - 6*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^2 - 72*(Q 0)^3*(Q 1)*(P 2)^2*(g₂) - 108*(Q 0)^2*(P 1)*(Q 1)^2*(P 2) + 108*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₃) - 216*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃) + 24*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2 - 12*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2 + 6*(P 1)^2*(Q 1)*(Q 2)^3*(g₂) + 9*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) + 27*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃) - 6*(Q 1)^3*(P 2)^2*(Q 2)*(g₂) - 18*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)*(g₃),
      36*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₂) - 36*(P 0)^2*(P 1)^3*(Q 2) - 72*(P 0)^2*(P 1)^2*(Q 1)*(P 2) - 108*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₃) + 108*(P 0)*(Q 0)*(P 1)^3*(P 2) + 108*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₃) - 12*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)^2 + 3*(Q 0)*(P 1)*(P 2)^4*(g₂)^2 - 15*(P 1)^3*(P 2)^2*(Q 2)*(g₂) + 6*(P 1)^2*(Q 1)*(P 2)^3*(g₂) - 9*(P 1)*(P 2)^4*(Q 2)*(g₂)*(g₃), by ring⟩
  · exact ⟨-432*(P 0)^2*(Q 0)^3*(Q 2) - 36*(P 0)^2*(Q 0)*(Q 2)^3*(g₂) + 432*(P 0)*(Q 0)^4*(P 2) + 72*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂) + 3*(P 0)*(P 2)*(Q 2)^4*(g₂)^2 - 36*(Q 0)^3*(P 2)^2*(Q 2)*(g₂) + 36*(Q 0)^2*(P 1)^2*(Q 2)^2 - 36*(Q 0)^2*(Q 1)^2*(P 2)^2 - 3*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2 + 3*(P 1)^2*(Q 2)^4*(g₂) - 3*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂),
      0, by ring⟩

theorem tr_eq_021 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 2 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₁ g₂ g₃ P Q 1 * D (law₁ g₂ g₃ P Q i) - s * (P 2 * c2 1 g₂ g₃ (law₁ g₂ g₃ P Q) i) -
      s * (trE021 g₂ g₃ P Q * law₁ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₁, law₁U, law₁V, law₁W, c2, trE021, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨72*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2) - 144*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2) - 108*(P 0)*(Q 0)^2*(Q 1)^2*(P 2) - 108*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₃) - 12*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^2 - 9*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) - 9*(P 0)*(P 2)*(Q 2)^4*(g₂)*(g₃) + 72*(Q 0)^3*(P 1)^2*(Q 2) + 144*(Q 0)^3*(P 1)*(Q 1)*(P 2) + 216*(Q 0)^3*(P 2)^2*(Q 2)*(g₃) + 12*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^2 - 6*(Q 0)*(P 1)^2*(Q 2)^3*(g₂) - 12*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂) + 18*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂) - 18*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)*(g₃) - 6*(P 1)^2*(Q 1)^2*(Q 2)^2 - 6*(P 1)*(Q 1)^3*(P 2)*(Q 2) - 18*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₃) + 3*(Q 1)^4*(P 2)^2 - 18*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₃) - 27*(P 2)^2*(Q 2)^4*(g₃)^2,
      -36*(P 0)^2*(Q 0)*(P 1)^2*(P 2) - 108*(P 0)^2*(Q 0)*(P 2)^3*(g₃) + 12*(P 0)^2*(P 2)^3*(Q 2)*(g₂)^2 - 12*(P 0)*(Q 0)*(P 2)^4*(g₂)^2 + 12*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂) + 12*(P 0)*(P 1)*(Q 1)*(P 2)^3*(g₂) + 36*(P 0)*(P 2)^4*(Q 2)*(g₂)*(g₃) - 15*(Q 0)*(P 1)^2*(P 2)^3*(g₂) - 9*(Q 0)*(P 2)^5*(g₂)*(g₃) + 3*(P 1)^4*(P 2)*(Q 2) + 6*(P 1)^3*(Q 1)*(P 2)^2 + 18*(P 1)^2*(P 2)^3*(Q 2)*(g₃) + 18*(P 1)*(Q 1)*(P 2)^4*(g₃) + 27*(P 2)^5*(Q 2)*(g₃)^2, by ring⟩
  · exact ⟨432*(P 0)^2*(Q 0)^3*(Q 1) - 36*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂) - 432*(P 0)*(Q 0)^4*(P 1) + 72*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂) - 72*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂) - 3*(P 0)*(P 1)*(Q 2)^4*(g₂)^2 + 6*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^2 + 72*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂) - 36*(Q 0)^3*(Q 1)*(P 2)^2*(g₂) + 36*(Q 0)^2*(P 1)^2*(Q 1)*(Q 2) - 36*(Q 0)^2*(P 1)*(Q 1)^2*(P 2) + 108*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₃) - 108*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃) - 6*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2 + 3*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2 - 3*(P 1)^2*(Q 1)*(Q 2)^3*(g₂) + 3*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) - 9*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃) + 9*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)*(g₃),
      0, by ring⟩
  · exact ⟨-36*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂) - 144*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2 + 36*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2) - 108*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₃) - 3*(P 0)*(P 2)*(Q 2)^4*(g₂)^2 + 72*(Q 0)^3*(P 2)^2*(Q 2)*(g₂) + 72*(Q 0)^2*(P 1)^2*(Q 2)^2 + 72*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2) - 36*(Q 0)^2*(Q 1)^2*(P 2)^2 + 108*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₃) - 6*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2 - 6*(P 1)^2*(Q 2)^4*(g₂) + 6*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂) - 9*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂) - 9*(P 2)^2*(Q 2)^4*(g₂)*(g₃),
      -36*(P 0)^2*(Q 0)*(P 2)^3*(g₂) + 36*(P 0)^2*(P 1)^2*(P 2)*(Q 2) + 72*(P 0)^2*(P 1)*(Q 1)*(P 2)^2 + 108*(P 0)^2*(P 2)^3*(Q 2)*(g₃) - 108*(P 0)*(Q 0)*(P 1)^2*(P 2)^2 - 108*(P 0)*(Q 0)*(P 2)^4*(g₃) + 12*(P 0)*(P 2)^4*(Q 2)*(g₂)^2 - 3*(Q 0)*(P 2)^5*(g₂)^2 + 15*(P 1)^2*(P 2)^3*(Q 2)*(g₂) - 6*(P 1)*(Q 1)*(P 2)^4*(g₂) + 9*(P 2)^5*(Q 2)*(g₂)*(g₃), by ring⟩

theorem tr_eq_022 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 2 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₁ g₂ g₃ P Q 2 * D (law₁ g₂ g₃ P Q i) - s * (P 2 * c2 2 g₂ g₃ (law₁ g₂ g₃ P Q) i) -
      s * (trE022 g₂ g₃ P Q * law₁ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₁, law₁U, law₁V, law₁W, c2, trE022, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨-72*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2 + 72*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2 + 72*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2) - 6*(P 0)*(P 1)*(Q 2)^4*(g₂) + 6*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂) - 12*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂) - 6*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂) - 6*(P 1)^2*(Q 1)*(Q 2)^3 - 6*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2 - 18*(P 1)*(P 2)*(Q 2)^4*(g₃) - 6*(Q 1)^3*(P 2)^2*(Q 2),
      -72*(P 0)^2*(Q 0)*(P 1)*(P 2)^2 + 12*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂) + 6*(Q 0)*(P 1)*(P 2)^4*(g₂) + 6*(P 1)^3*(P 2)^2*(Q 2) + 12*(P 1)^2*(Q 1)*(P 2)^3 + 18*(P 1)*(P 2)^4*(Q 2)*(g₃), by ring⟩
  · exact ⟨-432*(P 0)^2*(Q 0)^3*(Q 2) + 36*(P 0)^2*(Q 0)*(Q 2)^3*(g₂) + 432*(P 0)*(Q 0)^4*(P 2) + 36*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂) + 144*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2 - 36*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2) + 108*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₃) - 108*(Q 0)^3*(P 2)^2*(Q 2)*(g₂) - 36*(Q 0)^2*(P 1)^2*(Q 2)^2 - 72*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2) - 108*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₃) + 9*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2 + 3*(P 1)^2*(Q 2)^4*(g₂) - 6*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂) + 12*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂) + 9*(P 2)^2*(Q 2)^4*(g₂)*(g₃),
      36*(P 0)^2*(Q 0)*(P 2)^3*(g₂) - 36*(P 0)^2*(P 1)^2*(P 2)*(Q 2) - 72*(P 0)^2*(P 1)*(Q 1)*(P 2)^2 - 108*(P 0)^2*(P 2)^3*(Q 2)*(g₃) + 108*(P 0)*(Q 0)*(P 1)^2*(P 2)^2 + 108*(P 0)*(Q 0)*(P 2)^4*(g₃) - 12*(P 0)*(P 2)^4*(Q 2)*(g₂)^2 + 3*(Q 0)*(P 2)^5*(g₂)^2 - 15*(P 1)^2*(P 2)^3*(Q 2)*(g₂) + 6*(P 1)*(Q 1)*(P 2)^4*(g₂) - 9*(P 2)^5*(Q 2)*(g₂)*(g₃), by ring⟩
  · exact ⟨0,
      0, by ring⟩

set_option maxHeartbeats 8000000 in
-- large generated identity (law₂)
theorem tr_eq_111 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 1 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₂ g₂ g₃ P Q 1 * D (law₂ g₂ g₃ P Q i) - s * (P 1 * c2 1 g₂ g₃ (law₂ g₂ g₃ P Q) i) -
      s * (trE111 g₂ g₃ P Q * law₂ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₂, law₂U, law₂V, law₂W, c2, trE111, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨-1152*(P 0)^2*(Q 0)^3*(Q 1)*(g₂)^2 - 6912*(P 0)^2*(Q 0)^2*(Q 1)*(Q 2)*(g₂)*(g₃) - 96*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂)^3 - 10368*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₃)^2 - 288*(P 0)^2*(Q 1)*(Q 2)^3*(g₂)^2*(g₃) - 1152*(P 0)*(Q 0)^4*(P 1)*(g₂)^2 - 8640*(P 0)*(Q 0)^3*(P 1)*(Q 2)*(g₂)*(g₃) - 6912*(P 0)*(Q 0)^3*(Q 1)*(P 2)*(g₂)*(g₃) - 1728*(P 0)*(Q 0)^2*(P 1)*(Q 1)^2*(g₃) - 288*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂)^3 - 15552*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₃)^2 - 576*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂)^3 - 20736*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₃)^2 - 96*(P 0)*(Q 0)*(P 1)*(Q 1)^2*(Q 2)*(g₂)^2 - 1008*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₂)^2*(g₃) - 2304*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2*(g₃) - 16*(P 0)*(P 1)*(Q 2)^4*(g₂)^4 - 48*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^4 - 5184*(Q 0)^4*(P 1)*(P 2)*(g₂)*(g₃) - 3456*(Q 0)^3*(P 1)^2*(Q 1)*(g₃) - 192*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂)^3 - 20736*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₃)^2 + 96*(Q 0)^3*(Q 1)*(P 2)^2*(g₂)^3 - 10368*(Q 0)^3*(Q 1)*(P 2)^2*(g₃)^2 - 288*(Q 0)^2*(P 1)^2*(Q 1)*(Q 2)*(g₂)^2 - 1728*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₂)^2*(g₃) - 1440*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₂)^2*(g₃) + 576*(Q 0)*(P 1)*(Q 1)^2*(P 2)*(Q 2)*(g₂)*(g₃) - 112*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^4 + 1728*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)*(g₃)^2 - 120*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^4 + 864*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)*(g₃)^2 + 288*(P 1)^2*(Q 1)^3*(Q 2)*(g₃) + 8*(P 1)^2*(Q 1)*(Q 2)^3*(g₂)^3 + 864*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₃)^2 - 108*(P 1)*(P 2)*(Q 2)^4*(g₂)^3*(g₃) + 2592*(P 1)*(P 2)*(Q 2)^4*(g₃)^3 - 144*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)^3*(g₃) + 2592*(Q 1)*(P 2)^2*(Q 2)^3*(g₃)^3,
      -1728*(P 0)^2*(Q 0)*(P 1)^3*(g₃) - 96*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₂)^3 - 5184*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₃)^2 - 96*(P 0)^2*(P 1)^3*(Q 2)*(g₂)^2 - 192*(P 0)^2*(P 1)^2*(Q 1)*(P 2)*(g₂)^2 - 432*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₂)^2*(g₃) - 288*(P 0)*(Q 0)*(P 1)^3*(P 2)*(g₂)^2 - 864*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₂)^2*(g₃) - 432*(P 0)*(P 1)^3*(P 2)*(Q 2)*(g₂)*(g₃) - 576*(P 0)*(P 1)^2*(Q 1)*(P 2)^2*(g₂)*(g₃) - 32*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)^4 - 432*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)*(g₃)^2 - 720*(Q 0)*(P 1)^3*(P 2)^2*(g₂)*(g₃) - 8*(Q 0)*(P 1)*(P 2)^4*(g₂)^4 - 432*(Q 0)*(P 1)*(P 2)^4*(g₂)*(g₃)^2 - 288*(P 1)^4*(Q 1)*(P 2)*(g₃) + 24*(P 1)^3*(P 2)^2*(Q 2)*(g₂)^3 - 1728*(P 1)^3*(P 2)^2*(Q 2)*(g₃)^2 + 16*(P 1)^2*(Q 1)*(P 2)^3*(g₂)^3 - 864*(P 1)^2*(Q 1)*(P 2)^3*(g₃)^2 - 36*(P 1)*(P 2)^4*(Q 2)*(g₂)^3*(g₃), by ring⟩
  · exact ⟨20736*(P 0)^2*(Q 0)^4*(g₂)*(g₃) + 2304*(P 0)^2*(Q 0)^3*(Q 2)*(g₂)^3 + 62208*(P 0)^2*(Q 0)^3*(Q 2)*(g₃)^2 + 10368*(P 0)^2*(Q 0)^2*(Q 2)^2*(g₂)^2*(g₃) + 192*(P 0)^2*(Q 0)*(Q 2)^3*(g₂)^4 + 5184*(P 0)^2*(Q 0)*(Q 2)^3*(g₂)*(g₃)^2 + 144*(P 0)^2*(Q 2)^4*(g₂)^3*(g₃) + 62208*(P 0)*(Q 0)^4*(P 2)*(g₃)^2 + 13824*(P 0)*(Q 0)^3*(P 2)*(Q 2)*(g₂)^2*(g₃) + 768*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂)^4 + 10368*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂)*(g₃)^2 + 1152*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^3*(g₃) + 432*(P 0)*(P 2)*(Q 2)^4*(g₂)^2*(g₃)^2 + 1728*(Q 0)^4*(P 2)^2*(g₂)^2*(g₃) + 192*(Q 0)^3*(P 2)^2*(Q 2)*(g₂)^4 + 5184*(Q 0)^3*(P 2)^2*(Q 2)*(g₂)*(g₃)^2 - 1728*(Q 0)^2*(P 1)^2*(Q 1)^2*(g₃) + 288*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^3*(g₃) + 15552*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₃)^3 - 192*(Q 0)*(P 1)^2*(Q 1)^2*(Q 2)*(g₂)^2 - 48*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^5 + 2160*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2*(g₃)^2 - 144*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₂)*(g₃) - 36*(P 2)^2*(Q 2)^4*(g₂)^4*(g₃) + 1296*(P 2)^2*(Q 2)^4*(g₂)*(g₃)^3,
      0, by ring⟩
  · exact ⟨1152*(P 0)^2*(Q 0)^2*(Q 1)*(Q 2)*(g₂)^2 + 3456*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂)*(g₃) + 96*(P 0)^2*(Q 1)*(Q 2)^3*(g₂)^3 + 1152*(P 0)*(Q 0)^3*(P 1)*(Q 2)*(g₂)^2 + 2304*(P 0)*(Q 0)^3*(Q 1)*(P 2)*(g₂)^2 + 5184*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂)*(g₃) + 13824*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂)*(g₃) - 1728*(P 0)*(Q 0)*(P 1)*(Q 1)^2*(Q 2)*(g₃) + 96*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₂)^3 + 5184*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₃)^2 + 192*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^3 + 20736*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₃)^2 - 96*(P 0)*(P 1)*(Q 1)^2*(Q 2)^2*(g₂)^2 + 144*(P 0)*(P 1)*(Q 2)^4*(g₂)^2*(g₃) + 576*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^2*(g₃) + 2304*(Q 0)^4*(P 1)*(P 2)*(g₂)^2 + 1152*(Q 0)^3*(P 1)^2*(Q 1)*(g₂) + 10368*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂)*(g₃) + 3456*(Q 0)^3*(Q 1)*(P 2)^2*(g₂)*(g₃) - 1728*(Q 0)^2*(P 1)*(Q 1)^2*(P 2)*(g₃) + 15552*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₃)^2 + 288*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₂)^3 + 10368*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃)^2 - 288*(Q 0)*(P 1)^2*(Q 1)*(Q 2)^2*(g₂)^2 - 576*(Q 0)*(P 1)*(Q 1)^2*(P 2)*(Q 2)*(g₂)^2 + 288*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2*(g₃) + 1152*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2*(g₃) - 192*(P 1)^2*(Q 1)^3*(Q 2)*(g₂) - 288*(P 1)^2*(Q 1)*(Q 2)^3*(g₂)*(g₃) - 720*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) + 16*(P 1)*(P 2)*(Q 2)^4*(g₂)^4 - 432*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃)^2 + 24*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)^4,
      1152*(P 0)^2*(Q 0)*(P 1)^3*(g₂) + 5184*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₂)*(g₃) + 1728*(P 0)^2*(P 1)^3*(Q 2)*(g₃) + 3456*(P 0)^2*(P 1)^2*(Q 1)*(P 2)*(g₃) + 96*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₂)^3 + 5184*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₃)^2 + 5184*(P 0)*(Q 0)*(P 1)^3*(P 2)*(g₃) + 384*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₂)^3 + 5184*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₃)^2 + 288*(P 0)*(P 1)^3*(P 2)*(Q 2)*(g₂)^2 + 384*(P 0)*(P 1)^2*(Q 1)*(P 2)^2*(g₂)^2 + 864*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)^2*(g₃) + 480*(Q 0)*(P 1)^3*(P 2)^2*(g₂)^2 + 432*(Q 0)*(P 1)*(P 2)^4*(g₂)^2*(g₃) + 192*(P 1)^4*(Q 1)*(P 2)*(g₂) + 720*(P 1)^3*(P 2)^2*(Q 2)*(g₂)*(g₃) + 288*(P 1)^2*(Q 1)*(P 2)^3*(g₂)*(g₃) + 8*(P 1)*(P 2)^4*(Q 2)*(g₂)^4 + 432*(P 1)*(P 2)^4*(Q 2)*(g₂)*(g₃)^2, by ring⟩

set_option maxHeartbeats 8000000 in
-- large generated identity (law₂)
theorem tr_eq_112 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 1 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₂ g₂ g₃ P Q 2 * D (law₂ g₂ g₃ P Q i) - s * (P 1 * c2 2 g₂ g₃ (law₂ g₂ g₃ P Q) i) -
      s * (trE112 g₂ g₃ P Q * law₂ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₂, law₂U, law₂V, law₂W, c2, trE112, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨1152*(P 0)^2*(Q 0)^2*(Q 1)^2*(g₂) + 3456*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2)*(g₃) + 576*(P 0)*(Q 0)^3*(P 1)*(Q 1)*(g₂) + 3456*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₃) + 3456*(P 0)*(Q 0)^2*(Q 1)^2*(P 2)*(g₃) + 48*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2*(g₂)^2 + 192*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2)*(g₂)^2 - 48*(P 0)*(P 1)*(Q 1)^3*(Q 2)*(g₂) - 144*(P 0)*(P 1)*(Q 1)*(Q 2)^3*(g₂)*(g₃) - 288*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) - 576*(Q 0)^4*(P 1)^2*(g₂) + 288*(Q 0)^2*(P 1)^2*(Q 2)^2*(g₂)^2 + 96*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2)*(g₂)^2 + 96*(Q 0)^2*(Q 1)^2*(P 2)^2*(g₂)^2 + 96*(Q 0)*(P 1)^2*(Q 1)^2*(Q 2)*(g₂) + 576*(Q 0)*(P 1)^2*(Q 2)^3*(g₂)*(g₃) - 48*(P 1)^2*(Q 1)^4 + 288*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₃) - 4*(P 1)^2*(Q 2)^4*(g₂)^3 + 432*(P 1)^2*(Q 2)^4*(g₃)^2 + 288*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₃) - 40*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^3 + 864*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₃)^2 - 48*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)^3 + 864*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₃)^2,
      -3456*(P 0)^2*(Q 0)*(P 1)^2*(P 2)*(g₃) - 192*(P 0)^2*(P 1)^2*(P 2)*(Q 2)*(g₂)^2 - 144*(P 0)^2*(P 1)*(Q 1)*(P 2)^2*(g₂)^2 - 384*(P 0)*(Q 0)*(P 1)^2*(P 2)^2*(g₂)^2 - 48*(P 0)*(P 1)^3*(Q 1)*(P 2)*(g₂) - 576*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂)*(g₃) - 432*(P 0)*(P 1)*(Q 1)*(P 2)^3*(g₂)*(g₃) - 192*(Q 0)*(P 1)^4*(P 2)*(g₂) - 288*(Q 0)*(P 1)^2*(P 2)^3*(g₂)*(g₃) - 48*(P 1)^5*(Q 1) - 288*(P 1)^4*(P 2)*(Q 2)*(g₃) - 288*(P 1)^3*(Q 1)*(P 2)^2*(g₃) + 16*(P 1)^2*(P 2)^3*(Q 2)*(g₂)^3 - 864*(P 1)^2*(P 2)^3*(Q 2)*(g₃)^2 + 4*(P 1)*(Q 1)*(P 2)^4*(g₂)^3 - 432*(P 1)*(Q 1)*(P 2)^4*(g₃)^2, by ring⟩
  · exact ⟨-20736*(P 0)^2*(Q 0)^3*(Q 1)*(g₃) - 2304*(P 0)^2*(Q 0)^2*(Q 1)*(Q 2)*(g₂)^2 - 1728*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂)*(g₃) - 20736*(P 0)*(Q 0)^4*(P 1)*(g₃) - 3456*(P 0)*(Q 0)^3*(P 1)*(Q 2)*(g₂)^2 - 2304*(P 0)*(Q 0)^3*(Q 1)*(P 2)*(g₂)^2 - 5184*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂)*(g₃) - 6912*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂)*(g₃) + 1728*(P 0)*(Q 0)*(P 1)*(Q 1)^2*(Q 2)*(g₃) + 96*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₂)^3 - 5184*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₃)^2 + 576*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^3 - 20736*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₃)^2 + 96*(P 0)*(P 1)*(Q 1)^2*(Q 2)^2*(g₂)^2 - 2304*(Q 0)^4*(P 1)*(P 2)*(g₂)^2 - 1152*(Q 0)^3*(P 1)^2*(Q 1)*(g₂) - 6912*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂)*(g₃) - 1728*(Q 0)^3*(Q 1)*(P 2)^2*(g₂)*(g₃) - 1728*(Q 0)^2*(P 1)^2*(Q 1)*(Q 2)*(g₃) + 384*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₂)^3 - 10368*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₃)^2 - 5184*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃)^2 + 96*(Q 0)*(P 1)^2*(Q 1)*(Q 2)^2*(g₂)^2 + 384*(Q 0)*(P 1)*(Q 1)^2*(P 2)*(Q 2)*(g₂)^2 + 576*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2*(g₃) - 144*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2*(g₃) + 96*(P 1)^2*(Q 1)^3*(Q 2)*(g₂) + 144*(P 1)^2*(Q 1)*(Q 2)^3*(g₂)*(g₃) + 576*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) - 16*(P 1)*(P 2)*(Q 2)^4*(g₂)^4 + 864*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃)^2 - 48*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)^4 + 1296*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)*(g₃)^2,
      -1152*(P 0)^2*(Q 0)*(P 1)^3*(g₂) - 5184*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₂)*(g₃) - 1728*(P 0)^2*(P 1)^3*(Q 2)*(g₃) - 3456*(P 0)^2*(P 1)^2*(Q 1)*(P 2)*(g₃) - 96*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₂)^3 - 5184*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₃)^2 - 5184*(P 0)*(Q 0)*(P 1)^3*(P 2)*(g₃) - 384*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₂)^3 - 5184*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₃)^2 - 288*(P 0)*(P 1)^3*(P 2)*(Q 2)*(g₂)^2 - 384*(P 0)*(P 1)^2*(Q 1)*(P 2)^2*(g₂)^2 - 864*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)^2*(g₃) - 480*(Q 0)*(P 1)^3*(P 2)^2*(g₂)^2 - 432*(Q 0)*(P 1)*(P 2)^4*(g₂)^2*(g₃) - 192*(P 1)^4*(Q 1)*(P 2)*(g₂) - 720*(P 1)^3*(P 2)^2*(Q 2)*(g₂)*(g₃) - 288*(P 1)^2*(Q 1)*(P 2)^3*(g₂)*(g₃) - 8*(P 1)*(P 2)^4*(Q 2)*(g₂)^4 - 432*(P 1)*(P 2)^4*(Q 2)*(g₂)*(g₃)^2, by ring⟩
  · exact ⟨-1152*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2)*(g₂) - 1152*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₂) + 96*(P 0)*(P 1)*(Q 1)*(Q 2)^3*(g₂)^2 + 192*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)^2 + 192*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 + 96*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂)^2 - 96*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₂) - 96*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₂) + 288*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂)*(g₃) + 288*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)*(g₃),
      0, by ring⟩

set_option maxHeartbeats 8000000 in
-- large generated identity (law₂)
theorem tr_eq_121 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 2 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₂ g₂ g₃ P Q 1 * D (law₂ g₂ g₃ P Q i) - s * (P 2 * c2 1 g₂ g₃ (law₂ g₂ g₃ P Q) i) -
      s * (trE121 g₂ g₃ P Q * law₂ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₂, law₂U, law₂V, law₂W, c2, trE121, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨1152*(P 0)^2*(Q 0)^3*(Q 2)*(g₂)^2 + 576*(P 0)^2*(Q 0)^2*(Q 1)^2*(g₂) + 5184*(P 0)^2*(Q 0)^2*(Q 2)^2*(g₂)*(g₃) + 1728*(P 0)^2*(Q 0)*(Q 1)^2*(Q 2)*(g₃) + 96*(P 0)^2*(Q 0)*(Q 2)^3*(g₂)^3 + 5184*(P 0)^2*(Q 0)*(Q 2)^3*(g₃)^2 + 48*(P 0)^2*(Q 1)^2*(Q 2)^2*(g₂)^2 + 144*(P 0)^2*(Q 2)^4*(g₂)^2*(g₃) + 1152*(P 0)*(Q 0)^3*(P 1)*(Q 1)*(g₂) + 5184*(P 0)*(Q 0)^3*(P 2)*(Q 2)*(g₂)*(g₃) + 3456*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₃) + 480*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂)^3 + 10368*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₃)^2 + 96*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2*(g₂)^2 + 96*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2)*(g₂)^2 + 1296*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^2*(g₃) + 96*(P 0)*(P 1)*(Q 1)^3*(Q 2)*(g₂) + 144*(P 0)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) + 8*(P 0)*(P 2)*(Q 2)^4*(g₂)^4 + 432*(P 0)*(P 2)*(Q 2)^4*(g₂)*(g₃)^2 - 1728*(Q 0)^4*(P 2)^2*(g₂)*(g₃) + 96*(Q 0)^3*(P 2)^2*(Q 2)*(g₂)^3 + 96*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2)*(g₂)^2 - 48*(Q 0)^2*(Q 1)^2*(P 2)^2*(g₂)^2 + 1296*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^2*(g₃) + 96*(Q 0)*(P 1)^2*(Q 1)^2*(Q 2)*(g₂) + 96*(Q 0)*(P 1)*(Q 1)^3*(P 2)*(g₂) + 288*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂)*(g₃) + 432*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂)*(g₃) + 8*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^4 + 2160*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)*(g₃)^2 + 48*(P 1)^2*(Q 1)^4 + 144*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₃) + 576*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₃) + 8*(P 1)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^3 + 12*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)^3 + 432*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₃)^2 + 1296*(P 2)^2*(Q 2)^4*(g₃)^3,
      -1728*(P 0)^2*(Q 0)*(P 1)^2*(P 2)*(g₃) - 96*(P 0)^2*(Q 0)*(P 2)^3*(g₂)^3 - 5184*(P 0)^2*(Q 0)*(P 2)^3*(g₃)^2 - 96*(P 0)^2*(P 1)^2*(P 2)*(Q 2)*(g₂)^2 - 192*(P 0)^2*(P 1)*(Q 1)*(P 2)^2*(g₂)^2 - 432*(P 0)^2*(P 2)^3*(Q 2)*(g₂)^2*(g₃) - 288*(P 0)*(Q 0)*(P 1)^2*(P 2)^2*(g₂)^2 - 864*(P 0)*(Q 0)*(P 2)^4*(g₂)^2*(g₃) - 432*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂)*(g₃) - 576*(P 0)*(P 1)*(Q 1)*(P 2)^3*(g₂)*(g₃) - 32*(P 0)*(P 2)^4*(Q 2)*(g₂)^4 - 432*(P 0)*(P 2)^4*(Q 2)*(g₂)*(g₃)^2 - 720*(Q 0)*(P 1)^2*(P 2)^3*(g₂)*(g₃) - 8*(Q 0)*(P 2)^5*(g₂)^4 - 432*(Q 0)*(P 2)^5*(g₂)*(g₃)^2 - 288*(P 1)^3*(Q 1)*(P 2)^2*(g₃) + 24*(P 1)^2*(P 2)^3*(Q 2)*(g₂)^3 - 1728*(P 1)^2*(P 2)^3*(Q 2)*(g₃)^2 + 16*(P 1)*(Q 1)*(P 2)^4*(g₂)^3 - 864*(P 1)*(Q 1)*(P 2)^4*(g₃)^2 - 36*(P 2)^5*(Q 2)*(g₂)^3*(g₃), by ring⟩
  · exact ⟨0,
      0, by ring⟩
  · exact ⟨6912*(P 0)^2*(Q 0)^4*(g₂) + 20736*(P 0)^2*(Q 0)^3*(Q 2)*(g₃) - 1728*(P 0)^2*(Q 0)*(Q 2)^3*(g₂)*(g₃) - 48*(P 0)^2*(Q 2)^4*(g₂)^3 + 20736*(P 0)*(Q 0)^4*(P 2)*(g₃) + 1152*(P 0)*(Q 0)^3*(P 2)*(Q 2)*(g₂)^2 + 1152*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₂) + 1152*(P 0)*(Q 0)^2*(Q 1)^2*(P 2)*(g₂) - 5184*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) + 1152*(P 0)*(Q 0)*(P 1)*(Q 1)^3 + 3456*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2*(g₃) + 1728*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2)*(g₃) - 288*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^3 - 5184*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₃)^2 + 96*(P 0)*(P 1)*(Q 1)*(Q 2)^3*(g₂)^2 - 288*(P 0)*(P 2)*(Q 2)^4*(g₂)^2*(g₃) + 1728*(Q 0)^4*(P 2)^2*(g₂)^2 + 1152*(Q 0)^3*(P 1)*(Q 1)*(P 2)*(g₂) + 1728*(Q 0)^3*(P 2)^2*(Q 2)*(g₂)*(g₃) + 576*(Q 0)^2*(P 1)^2*(Q 1)^2 + 3456*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2)*(g₃) + 1728*(Q 0)^2*(Q 1)^2*(P 2)^2*(g₃) - 576*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^3 + 96*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 - 192*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂)^2 - 1296*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2*(g₃) - 48*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₂) - 288*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₂) - 432*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)*(g₃) + 4*(P 2)^2*(Q 2)^4*(g₂)^4 - 864*(P 2)^2*(Q 2)^4*(g₂)*(g₃)^2,
      1152*(P 0)^2*(Q 0)*(P 1)^2*(P 2)*(g₂) + 5184*(P 0)^2*(Q 0)*(P 2)^3*(g₂)*(g₃) + 1728*(P 0)^2*(P 1)^2*(P 2)*(Q 2)*(g₃) + 3456*(P 0)^2*(P 1)*(Q 1)*(P 2)^2*(g₃) + 96*(P 0)^2*(P 2)^3*(Q 2)*(g₂)^3 + 5184*(P 0)^2*(P 2)^3*(Q 2)*(g₃)^2 + 5184*(P 0)*(Q 0)*(P 1)^2*(P 2)^2*(g₃) + 384*(P 0)*(Q 0)*(P 2)^4*(g₂)^3 + 5184*(P 0)*(Q 0)*(P 2)^4*(g₃)^2 + 288*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂)^2 + 384*(P 0)*(P 1)*(Q 1)*(P 2)^3*(g₂)^2 + 864*(P 0)*(P 2)^4*(Q 2)*(g₂)^2*(g₃) + 480*(Q 0)*(P 1)^2*(P 2)^3*(g₂)^2 + 432*(Q 0)*(P 2)^5*(g₂)^2*(g₃) + 192*(P 1)^3*(Q 1)*(P 2)^2*(g₂) + 720*(P 1)^2*(P 2)^3*(Q 2)*(g₂)*(g₃) + 288*(P 1)*(Q 1)*(P 2)^4*(g₂)*(g₃) + 8*(P 2)^5*(Q 2)*(g₂)^4 + 432*(P 2)^5*(Q 2)*(g₂)*(g₃)^2, by ring⟩

set_option maxHeartbeats 8000000 in
-- large generated identity (law₂)
theorem tr_eq_122 {S : Type*} [CommRing S] [Algebra S R] (D : Derivation S R R) (g₂ g₃ s : R)
    (P Q : Fin 3 → R) (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 2 g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    law₂ g₂ g₃ P Q 2 * D (law₂ g₂ g₃ P Q i) - s * (P 2 * c2 2 g₂ g₃ (law₂ g₂ g₃ P Q) i) -
      s * (trE122 g₂ g₃ P Q * law₂ g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
  have q0 := hQ 0; have q1 := hQ 1; have q2 := hQ 2
  simp only [c2, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  fin_cases i <;> simp only [law₂, law₂U, law₂V, law₂W, c2, trE122, Fv, F, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul,
    nsmul_eq_mul, D_ofNat, h0, h1, h2, q0, q1, q2, hg₂, hg₃, Nat.cast_ofNat, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, Nat.reduceSub, pow_one]
  · exact ⟨-1152*(P 0)^2*(Q 0)^2*(Q 1)*(Q 2)*(g₂) - 576*(P 0)^2*(Q 0)*(Q 1)^3 - 1728*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₃) - 1152*(P 0)*(Q 0)^3*(P 1)*(Q 2)*(g₂) - 1728*(P 0)*(Q 0)^3*(Q 1)*(P 2)*(g₂) - 1728*(P 0)*(Q 0)^2*(P 1)*(Q 1)^2 - 1728*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₃) - 6912*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₃) + 96*(P 0)*(Q 0)*(P 1)*(Q 2)^3*(g₂)^2 - 144*(P 0)*(Q 0)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 + 144*(P 0)*(P 1)*(Q 1)^2*(Q 2)^2*(g₂) + 144*(P 0)*(P 1)*(Q 2)^4*(g₂)*(g₃) + 144*(P 0)*(Q 1)^3*(P 2)*(Q 2)*(g₂) + 144*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)*(g₃) - 1728*(Q 0)^4*(P 1)*(P 2)*(g₂) - 1152*(Q 0)^3*(P 1)^2*(Q 1) - 6912*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₃) - 3456*(Q 0)^3*(Q 1)*(P 2)^2*(g₃) - 96*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₂)^2 - 288*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₂)^2 + 192*(Q 0)*(P 1)^2*(Q 1)*(Q 2)^2*(g₂) + 384*(Q 0)*(P 1)*(Q 1)^2*(P 2)*(Q 2)*(g₂) + 576*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)*(g₃) + 48*(Q 0)*(Q 1)^3*(P 2)^2*(g₂) + 144*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)*(g₃) + 48*(P 1)^2*(Q 1)^3*(Q 2) + 144*(P 1)^2*(Q 1)*(Q 2)^3*(g₃) + 576*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₃) + 20*(P 1)*(P 2)*(Q 2)^4*(g₂)^3 + 432*(Q 1)^3*(P 2)^2*(Q 2)*(g₃) + 32*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)^3 - 432*(Q 1)*(P 2)^2*(Q 2)^3*(g₃)^2,
      -3456*(P 0)^2*(Q 0)*(P 1)*(P 2)^2*(g₃) - 192*(P 0)^2*(P 1)*(P 2)^2*(Q 2)*(g₂)^2 - 144*(P 0)^2*(Q 1)*(P 2)^3*(g₂)^2 - 384*(P 0)*(Q 0)*(P 1)*(P 2)^3*(g₂)^2 - 48*(P 0)*(P 1)^2*(Q 1)*(P 2)^2*(g₂) - 576*(P 0)*(P 1)*(P 2)^3*(Q 2)*(g₂)*(g₃) - 432*(P 0)*(Q 1)*(P 2)^4*(g₂)*(g₃) - 192*(Q 0)*(P 1)^3*(P 2)^2*(g₂) - 288*(Q 0)*(P 1)*(P 2)^4*(g₂)*(g₃) - 48*(P 1)^4*(Q 1)*(P 2) - 288*(P 1)^3*(P 2)^2*(Q 2)*(g₃) - 288*(P 1)^2*(Q 1)*(P 2)^3*(g₃) + 16*(P 1)*(P 2)^4*(Q 2)*(g₂)^3 - 864*(P 1)*(P 2)^4*(Q 2)*(g₃)^2 + 4*(Q 1)*(P 2)^5*(g₂)^3 - 432*(Q 1)*(P 2)^5*(g₃)^2, by ring⟩
  · exact ⟨1152*(P 0)*(Q 0)^3*(P 2)*(Q 2)*(g₂)^2 - 1152*(P 0)*(Q 0)^2*(P 1)*(Q 1)*(Q 2)*(g₂) - 1152*(P 0)*(Q 0)^2*(Q 1)^2*(P 2)*(g₂) + 5184*(P 0)*(Q 0)^2*(P 2)*(Q 2)^2*(g₂)*(g₃) - 1152*(P 0)*(Q 0)*(P 1)*(Q 1)^3 - 3456*(P 0)*(Q 0)*(P 1)*(Q 1)*(Q 2)^2*(g₃) - 1728*(P 0)*(Q 0)*(Q 1)^2*(P 2)*(Q 2)*(g₃) + 96*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₂)^3 + 5184*(P 0)*(Q 0)*(P 2)*(Q 2)^3*(g₃)^2 - 96*(P 0)*(P 1)*(Q 1)*(Q 2)^3*(g₂)^2 + 144*(P 0)*(P 2)*(Q 2)^4*(g₂)^2*(g₃) - 1152*(Q 0)^4*(P 2)^2*(g₂)^2 - 1152*(Q 0)^3*(P 1)*(Q 1)*(P 2)*(g₂) - 1152*(Q 0)^2*(P 1)^2*(Q 1)^2 - 3456*(Q 0)^2*(P 1)*(Q 1)*(P 2)*(Q 2)*(g₃) - 1728*(Q 0)^2*(Q 1)^2*(P 2)^2*(g₃) + 384*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₂)^3 + 5184*(Q 0)^2*(P 2)^2*(Q 2)^2*(g₃)^2 - 96*(Q 0)*(P 1)*(Q 1)*(P 2)*(Q 2)^2*(g₂)^2 + 192*(Q 0)*(Q 1)^2*(P 2)^2*(Q 2)*(g₂)^2 + 1152*(Q 0)*(P 2)^2*(Q 2)^3*(g₂)^2*(g₃) + 96*(P 1)^2*(Q 1)^2*(Q 2)^2*(g₂) + 288*(P 1)*(Q 1)^3*(P 2)*(Q 2)*(g₂) + 432*(Q 1)^2*(P 2)^2*(Q 2)^2*(g₂)*(g₃) + 8*(P 2)^2*(Q 2)^4*(g₂)^4 + 432*(P 2)^2*(Q 2)^4*(g₂)*(g₃)^2,
      -1152*(P 0)^2*(Q 0)*(P 1)^2*(P 2)*(g₂) - 5184*(P 0)^2*(Q 0)*(P 2)^3*(g₂)*(g₃) - 1728*(P 0)^2*(P 1)^2*(P 2)*(Q 2)*(g₃) - 3456*(P 0)^2*(P 1)*(Q 1)*(P 2)^2*(g₃) - 96*(P 0)^2*(P 2)^3*(Q 2)*(g₂)^3 - 5184*(P 0)^2*(P 2)^3*(Q 2)*(g₃)^2 - 5184*(P 0)*(Q 0)*(P 1)^2*(P 2)^2*(g₃) - 384*(P 0)*(Q 0)*(P 2)^4*(g₂)^3 - 5184*(P 0)*(Q 0)*(P 2)^4*(g₃)^2 - 288*(P 0)*(P 1)^2*(P 2)^2*(Q 2)*(g₂)^2 - 384*(P 0)*(P 1)*(Q 1)*(P 2)^3*(g₂)^2 - 864*(P 0)*(P 2)^4*(Q 2)*(g₂)^2*(g₃) - 480*(Q 0)*(P 1)^2*(P 2)^3*(g₂)^2 - 432*(Q 0)*(P 2)^5*(g₂)^2*(g₃) - 192*(P 1)^3*(Q 1)*(P 2)^2*(g₂) - 720*(P 1)^2*(P 2)^3*(Q 2)*(g₂)*(g₃) - 288*(P 1)*(Q 1)*(P 2)^4*(g₂)*(g₃) - 8*(P 2)^5*(Q 2)*(g₂)^4 - 432*(P 2)^5*(Q 2)*(g₂)*(g₃)^2, by ring⟩
  · exact ⟨-6912*(P 0)^2*(Q 0)^3*(Q 1) + 576*(P 0)^2*(Q 0)*(Q 1)*(Q 2)^2*(g₂) - 6912*(P 0)*(Q 0)^4*(P 1) + 1152*(P 0)*(Q 0)^2*(P 1)*(Q 2)^2*(g₂) + 1152*(P 0)*(Q 0)^2*(Q 1)*(P 2)*(Q 2)*(g₂) - 48*(P 0)*(P 1)*(Q 2)^4*(g₂)^2 - 96*(P 0)*(Q 1)*(P 2)*(Q 2)^3*(g₂)^2 + 1152*(Q 0)^3*(P 1)*(P 2)*(Q 2)*(g₂) + 576*(Q 0)^3*(Q 1)*(P 2)^2*(g₂) - 576*(Q 0)^2*(P 1)^2*(Q 1)*(Q 2) - 576*(Q 0)^2*(P 1)*(Q 1)^2*(P 2) + 1728*(Q 0)^2*(P 1)*(P 2)*(Q 2)^2*(g₃) + 1728*(Q 0)^2*(Q 1)*(P 2)^2*(Q 2)*(g₃) - 96*(Q 0)*(P 1)*(P 2)*(Q 2)^3*(g₂)^2 - 48*(Q 0)*(Q 1)*(P 2)^2*(Q 2)^2*(g₂)^2 + 48*(P 1)^2*(Q 1)*(Q 2)^3*(g₂) + 48*(P 1)*(Q 1)^2*(P 2)*(Q 2)^2*(g₂) - 144*(P 1)*(P 2)*(Q 2)^4*(g₂)*(g₃) - 144*(Q 1)*(P 2)^2*(Q 2)^3*(g₂)*(g₃),
      0, by ring⟩


end LSG.ME
