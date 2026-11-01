import Mathlib
import LSG.ME.SubgroupProj

/-!
# Multihomogeneous components of vanishing ideals (STAGE2 §5, item 5)

* **`multiComp_mem_vanish`**: `vanish E` is closed under multihomogeneous components (multigrading
  `wV` by elliptic blocks), by iterating the block components of `comp_mem_vanish`.
* `sum_multiComp`: a polynomial is the (finite) sum of its multihomogeneous components.

(Mathlib's graded primality criterion would apply with the lexicographic order on `Fin m → ℕ`, but
elaborating it times out on the `Pi.Lex` order instances; primality is proved directly instead.)
-/

universe u

open MvPolynomial

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- Iterated block components along a list of blocks. -/
noncomputable def compL (d : Fin m → ℕ) : List (Fin m) → MvPolynomial (Var d₀ d₁ m) K →
    MvPolynomial (Var d₀ d₁ m) K
  | [] => id
  | k :: l => fun P => weightedHomogeneousComponent (wE k) (d k) (compL d l P)

open Classical in
theorem coeff_compL (d : Fin m → ℕ) (l : List (Fin m)) (P : MvPolynomial (Var d₀ d₁ m) K)
    (t : Var d₀ d₁ m →₀ ℕ) :
    (compL d l P).coeff t =
      if ∀ k ∈ l, Finsupp.weight (wE k) t = d k then P.coeff t else 0 := by
  induction l with
  | nil => simp [compL]
  | cons k l ih =>
    simp only [compL, coeff_weightedHomogeneousComponent]
    rw [ih]
    by_cases h1 : Finsupp.weight (wE k) t = d k <;> by_cases h2 : ∀ k ∈ l, Finsupp.weight (wE k) t = d k
      <;> simp [h1, h2]

theorem compL_mem_vanish [Infinite K] {E : Set (GPt K d₀ d₁ g₂ g₃)} (d : Fin m → ℕ)
    (l : List (Fin m)) {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ vanish E) :
    compL d l P ∈ vanish E := by
  induction l with
  | nil => exact hP
  | cons k l ih => exact comp_mem_vanish ih k (d k)

theorem compL_univ (d : Fin m → ℕ) (P : MvPolynomial (Var d₀ d₁ m) K) :
    compL d (List.finRange m) P = weightedHomogeneousComponent wV d P := by
  classical
  ext t
  rw [coeff_compL, coeff_weightedHomogeneousComponent]
  congr 1
  apply propext
  constructor
  · intro h; funext k; rw [← weight_wE]; exact h k (List.mem_finRange k)
  · intro h k _; rw [weight_wE, h]

/-- **`vanish E` is closed under multihomogeneous components.** -/
theorem multiComp_mem_vanish [Infinite K] {E : Set (GPt K d₀ d₁ g₂ g₃)} (d : Fin m → ℕ)
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ vanish E) :
    weightedHomogeneousComponent wV d P ∈ vanish E := by
  rw [← compL_univ]; exact compL_mem_vanish d _ hP

theorem sum_multiComp (P : MvPolynomial (Var d₀ d₁ m) K) :
    ∃ s : Finset (Fin m → ℕ), P = ∑ d ∈ s, weightedHomogeneousComponent wV d P := by
  have hfin := weightedHomogeneousComponent_finsupp (w := (wV : Var d₀ d₁ m → Fin m → ℕ)) P
  refine ⟨hfin.toFinset, ?_⟩
  conv_lhs => rw [← finsum_weightedHomogeneousComponent wV P]
  exact finsum_eq_sum _ hfin

end LSG.ME
