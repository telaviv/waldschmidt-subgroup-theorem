import Mathlib
import LSG.MEV.IG

/-!
# The Nullstellensatz on `G̃`: `I(G̃) = I_G̃`

* `IG_le_vanish`: `I_G̃ ⊆ I(E)` for every set of points.
* `exists_coords_of_rel`: a zero of `Y Z − 1` all of whose `E^♮` blocks are nonzero multiples of
  representatives is a cone representative `coords g λ`.
* `blockPath`: every zero `v` of `(F, G)` in `ℂ⁵` is the value at `τ = 0` of a polynomial curve
  `τ ↦ φ(τ)` whose points for `τ ≠ 0` lie on `X` with nonzero base part. For `v` with nonzero base
  part, `φ` is constant; for `v = (0, 0, 0, a, b)` with `a ≠ 0`,
  `φ(τ) = τ · ptAff x₀ y₀ (a/τ) = (τx₀, τy₀, τ, a, y₀a − 2τx₀²)` with `y₀ = b/a` and `x₀` a root of
  `4x³ − g₂x − g₃ = y₀²`; for `v = (0, 0, 0, 0, b)`, `φ(τ) = τ · ptO (b/τ) = (0, τ, 0, 0, b)`.
  (So the boundary `U = V = W = 0` of the cone over `X` lies in the closure of `E^♮`.)
* **`vanish_univ`**: `I(G̃) = I_G̃` (Hilbert's Nullstellensatz, primality of `I_G̃`, `blockPath`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem eval_coords_Fk (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (k : Fin m) :
    eval (coordsZ g ν) (Fk (g2L Ls) (g3L Ls) d₀ d₁ k) = 0 := by
  have h := Fn_repV (g.2.2 k)
  simp only [Fn, F] at h
  simp only [g2L, g3L, Fk, F, map_add, map_sub, map_mul, map_pow, eval_C, eval_X, coordsZ_e, map_ofNat]
  linear_combination ν k ^ 3 * h

theorem eval_coords_Gk (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (k : Fin m) :
    eval (coordsZ g ν) (Gk ℂ d₀ d₁ k) = 0 := by
  have h := Gn_repV (g.2.2 k)
  simp only [Gn, Gfib] at h
  simp only [Gk, Gfib, map_add, map_sub, map_mul, map_pow, eval_X, coordsZ_e, map_ofNat]
  linear_combination ν k ^ 2 * h

theorem IG_le_vanish (E : Set (GPtV d₀ d₁ Ls)) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ vanish E := by
  rw [IG, Ideal.ofList, Ideal.span_le]
  intro P hP
  simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hP
  refine mem_vanish.mpr fun g _ lam => ?_
  rcases hP with (⟨j, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · simp [YZ, coords]
  · exact eval_coords_Fk g _ k
  · exact eval_coords_Gk g _ k

/-- **Relevant zeros are cone representatives.** -/
theorem exists_coords_of_rel {x : Var d₀ d₁ m → ℂ} (hyz : ∀ j, x (.y j) * x (.z j) = 1)
    (hb : ∀ k, ∃ (p : EVL (Ls k)) (u : ℂ), u ≠ 0 ∧ (fun c => x (.e k c)) = u • repV p) :
    ∃ (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ), x = coords g lam := by
  choose p u hu hpu using hb
  refine ⟨(fun i => x (.x i), Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j), p),
    fun k => Units.mk0 (u k) (hu k), ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j =>
    simp only [coords, coordsZ_z, GPtV.ym]
    have h1 := hyz j
    rw [show ((Additive.toMul (Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j)) j)⁻¹ : ℂˣ)
      = Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hyz j) from Units.ext (by
        simp only [toMul_ofMul, Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
        exact (eq_inv_of_mul_eq_one_right h1).symm)]
    simp
  | e k c =>
    have := congrFun (hpu k) c
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp [coords, this]

/-- **Polynomial curves to the zeros of `(F, G)`.** -/
theorem blockPath (L : PeriodPair) {v : Fin 5 → ℂ} (hF : Fn L.g₂ L.g₃ v = 0) (hG : Gn v = 0) :
    ∃ φ : Fin 5 → Polynomial ℂ, (∀ c, (φ c).eval 0 = v c) ∧
      ∀ τ : ℂ, τ ≠ 0 → Fn L.g₂ L.g₃ (fun c => (φ c).eval τ) = 0 ∧
        Gn (fun c => (φ c).eval τ) = 0 ∧ Pe (fun c => (φ c).eval τ) ≠ 0 := by
  by_cases hP : Pe v ≠ 0
  · exact ⟨fun c => Polynomial.C (v c), fun c => by simp, fun τ _ => by simpa using ⟨hF, hG, hP⟩⟩
  have h0 : v 0 = 0 := by simpa [Pe] using congrFun (not_not.mp hP) 0
  have h1 : v 1 = 0 := by simpa [Pe] using congrFun (not_not.mp hP) 1
  have h2 : v 2 = 0 := by simpa [Pe] using congrFun (not_not.mp hP) 2
  by_cases ha : v 3 = 0
  · refine ⟨![0, Polynomial.X, 0, 0, Polynomial.C (v 4)], fun c => ?_, fun τ hτ => ?_⟩
    · fin_cases c <;> simp [h0, h1, h2, ha]
    · refine ⟨by simp [Fn, F], by simp [Gn, Gfib], fun h => hτ ?_⟩
      simpa [Pe] using congrFun h 1
  · set y₀ := v 4 / v 3
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℂ, (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C L.g₂ *
        Polynomial.X - Polynomial.C (L.g₃ + y₀ ^ 2)).IsRoot x₀ := by
      apply Complex.exists_root
      have : (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C L.g₂ * Polynomial.X -
          Polynomial.C (L.g₃ + y₀ ^ 2) : Polynomial ℂ).degree = 3 := by
        compute_degree!
      rw [this]; norm_num
    have hE : y₀ ^ 2 = 4 * x₀ ^ 3 - L.g₂ * x₀ - L.g₃ := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X] at hx₀
      linear_combination -hx₀
    refine ⟨![Polynomial.C x₀ * Polynomial.X, Polynomial.C y₀ * Polynomial.X, Polynomial.X,
      Polynomial.C (v 3), Polynomial.C (y₀ * v 3) - Polynomial.C (2 * x₀ ^ 2) * Polynomial.X],
      fun c => ?_, fun τ hτ => ?_⟩
    · fin_cases c <;> simp [h0, h1, h2, y₀, div_mul_cancel₀ _ ha]
    · refine ⟨?_, ?_, fun h => hτ ?_⟩
      · simp only [Fn, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        linear_combination τ ^ 3 * hE
      · simp [Gn, Gfib]; ring
      · simpa [Pe] using congrFun h 2

/-- **Hilbert's Nullstellensatz on `G̃`**: `I(G̃) = I_G̃`. -/
theorem vanish_univ :
    vanish (Set.univ : Set (GPtV d₀ d₁ Ls)) = IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  classical
  apply le_antisymm _ (IG_le_vanish _)
  intro P hP
  have hprime := IG_isPrime (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) (two_ne_zero' ℂ)
  rw [← hprime.radical, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
  intro x hx
  rw [mem_zeroLocus_iff] at hx
  rw [show (aeval x) P = eval x P from rfl]
  have hev : ∀ Q ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls), eval x Q = 0 := fun Q hQ => hx Q hQ
  have hyz : ∀ j, x (.y j) * x (.z j) = 1 := fun j => by
    simpa [YZ, sub_eq_zero] using hev _ (YZ_mem_IG _ _ j)
  have hF : ∀ k, Fn (Ls k).g₂ (Ls k).g₃ (fun c => x (.e k c)) = 0 := fun k => by
    simpa [Fk, F, Fn, g2L, g3L] using hev _ (Fk_mem_IG (d₀ := d₀) (d₁ := d₁) _ _ k)
  have hG : ∀ k, Gn (fun c => x (.e k c)) = 0 := fun k => by
    simpa [Gk, Gfib, Gn] using hev _ (Gk_mem_IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) k)
  choose φ hφ0 hφ using fun k => blockPath (Ls k) (hF k) (hG k)
  let Φ : Var d₀ d₁ m → Polynomial ℂ := fun v => match v with
    | .x i => Polynomial.C (x (.x i))
    | .y j => Polynomial.C (x (.y j))
    | .z j => Polynomial.C (x (.z j))
    | .e k c => φ k c
  set Q := MvPolynomial.aeval Φ P
  have hevQ : ∀ t : ℂ, Q.eval t = eval (fun v => (Φ v).eval t) P := by
    intro t
    rw [show Q = MvPolynomial.aeval Φ P from rfl, MvPolynomial.aeval_def,
      MvPolynomial.polynomial_eval_eval₂]
    have : (Polynomial.evalRingHom t).comp (algebraMap ℂ (Polynomial ℂ)) = RingHom.id ℂ := by
      ext; simp
    rw [this]; rfl
  have hroot : ∀ t : ℂ, t ≠ 0 → Q.IsRoot t := by
    intro t ht
    rw [Polynomial.IsRoot, hevQ]
    obtain ⟨g, lam, hgl⟩ := exists_coords_of_rel (Ls := Ls) (x := fun v => (Φ v).eval t)
      (fun j => by simpa [Φ] using hyz j) (fun k => by
        obtain ⟨hF', hG', hP'⟩ := hφ k t ht
        obtain ⟨b, s, u, hu, he⟩ := exists_smul_repB (two_ne_zero' ℂ) (discr_ne_zero (Ls k)) hF'
          hG' hP'
        exact ⟨⟨b, s⟩, u, hu, he⟩)
    rw [hgl]
    exact mem_vanish.mp hP g (Set.mem_univ _) lam
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) (fun t ht => hroot t ht) ?_
    exact Set.Finite.infinite_compl (Set.finite_singleton 0)
  have := hevQ 0
  rw [hQ, Polynomial.eval_zero] at this
  rw [this]
  congr 2
  funext v
  cases v with
  | x i => simp [Φ]
  | y j => simp [Φ]
  | z j => simp [Φ]
  | e k c => exact (hφ0 k c).symm

end LSG.MEV
