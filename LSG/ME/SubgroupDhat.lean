import Mathlib
import LSG.ME.SubgroupProj
import LSG.ME.Deriv

/-!
# The homogenised invariant derivation `D̂_w` (STAGE2 §5, item 4, algebraic part)

The chart derivation `D_w` of `LSG.ME.Deriv` (here with the `V`-chart in every elliptic block) does
**not** preserve the multihomogeneous ideal `vanish H` of a subgroup: its linear part has
multidegree `0` and its `k`-th elliptic part has multidegree `e_k`, so `D_w P` is not
multihomogeneous (e.g. the diagonal of `E × E`, `P = U₁W₂ − U₂W₁`, `w = (1, 1)`). The fix is to
homogenise with the chart forms `V_k`:

  `D̂_w P = Σ_v V̂_v · (D_w X_v) · ∂P/∂X_v`, `V̂_v = ∏_k V_k` (linear `v`), `∏_{k' ≠ k} V_{k'}` (`v` in
  block `k`).

* **`isWeightedHomogeneous_Dhat`**: `D̂_w` maps multidegree `d` to `d + (1, …, 1)`.
* **`eval_Dhat_of_V`**: at a point with all `V_k = 1`, `D̂_w P` and `D_w P` (`V`-charts) agree.
* **`eval_Dhat_eq_zero_of_V`**: at a cone point with some `V_k = 0` (a `2`-torsion point in block
  `k`), `D̂_w P = 0` whenever `P` is multihomogeneous and vanishes there (Euler's identity: the
  `V`-chart derivation is proportional to the Euler field at such points).
* **`transl_mem_vanish`**: `vanish H` is stable under translations by elements of a subgroup `H`.
-/

universe u

open MvPolynomial LSG.Elliptic

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} (g₂ g₃ : Fin m → K)

/-- `∏_k V_k`. -/
noncomputable def Vprod : MvPolynomial (Var d₀ d₁ m) K := ∏ k, X (.e k 1)

/-- `∏_{k' ≠ k} V_{k'}`. -/
noncomputable def Vexc (k : Fin m) : MvPolynomial (Var d₀ d₁ m) K :=
  ∏ k' ∈ Finset.univ.erase k, X (.e k' 1)

/-- The homogenising factor of a variable. -/
noncomputable def Vfac : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) K
  | .e k _ => Vexc k
  | _ => Vprod

/-- The coefficients of `D̂_w`. -/
noncomputable def dhat (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) : MvPolynomial (Var d₀ d₁ m) K :=
  Vfac v * dval g₂ g₃ (fun _ => 1) w v

/-- **The homogenised derivation** `D̂_w P = Σ_v dhat_v · ∂P/∂X_v`. -/
noncomputable def Dhat (w : LieE K d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) K) :
    MvPolynomial (Var d₀ d₁ m) K :=
  ∑ v, dhat g₂ g₃ w v * pderiv v P

/-- The multidegree `(1, …, 1)`. -/
def ones : Fin m → ℕ := ∑ k, Pi.single k 1

/-! ### Evaluation -/

theorem eval_Vfac_of_V {x : Var d₀ d₁ m → K} (hx : ∀ k, x (.e k 1) = 1) (v : Var d₀ d₁ m) :
    eval x (Vfac v) = 1 := by
  cases v <;> simp [Vfac, Vprod, Vexc, hx]

/-- At a point with all `V_k = 1`, `D̂_w` and the `V`-chart `D_w` agree. -/
theorem eval_Dhat_of_V {x : Var d₀ d₁ m → K} (hx : ∀ k, x (.e k 1) = 1) (w : LieE K d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) K) :
    eval x (Dhat g₂ g₃ w P) = eval x (Dw g₂ g₃ (fun _ => 1) w P) := by
  rw [Dhat, Dw_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [dhat, map_mul, eval_Vfac_of_V hx, one_mul]

/-! ### Homogeneity -/

theorem homog_X_e (k : Fin m) (c : Fin 3) :
    IsWeightedHomogeneous wV (X (.e k c) : MvPolynomial (Var d₀ d₁ m) K) (Pi.single k 1) :=
  isWeightedHomogeneous_X K wV _

theorem homog_Vprod : IsWeightedHomogeneous wV (Vprod : MvPolynomial (Var d₀ d₁ m) K) ones := by
  have := IsWeightedHomogeneous.prod (R := K) (w := wV) Finset.univ
    (fun k => (X (.e k 1) : MvPolynomial (Var d₀ d₁ m) K)) (fun k => Pi.single k 1)
    (fun k _ => homog_X_e k 1)
  exact this

theorem homog_Vexc (k : Fin m) : IsWeightedHomogeneous wV (Vexc k : MvPolynomial (Var d₀ d₁ m) K)
    (∑ k' ∈ Finset.univ.erase k, Pi.single k' 1) :=
  IsWeightedHomogeneous.prod (R := K) (w := wV) _ _ _ fun k' _ => homog_X_e k' 1

theorem ones_eq (k : Fin m) :
    (ones : Fin m → ℕ) = Pi.single k 1 + ∑ k' ∈ Finset.univ.erase k, Pi.single k' 1 :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm

theorem homog_chartPoly_one (k : Fin m) (c : Fin 3) :
    IsWeightedHomogeneous wV (chartPoly g₂ g₃ d₀ d₁ 1 k c : MvPolynomial (Var d₀ d₁ m) K)
      (2 • Pi.single k 1) := by
  have hX := homog_X_e (K := K) (d₀ := d₀) (d₁ := d₁) k
  have hC : ∀ a : K, IsWeightedHomogeneous wV (C a : MvPolynomial (Var d₀ d₁ m) K) 0 :=
    fun a => isWeightedHomogeneous_C _ _
  have hn : ∀ n : ℕ, IsWeightedHomogeneous wV (n : MvPolynomial (Var d₀ d₁ m) K) 0 := fun n => by
    rw [← map_natCast C]; exact hC _
  have h2 : (2 • Pi.single k 1 : Fin m → ℕ) = Pi.single k 1 + Pi.single k 1 := two_nsmul _
  fin_cases c
  · simp only [chartPoly, chartV, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.isValue]
    refine IsWeightedHomogeneous.sub (IsWeightedHomogeneous.sub ?_ ?_) ?_
    · exact homog_of_eq ((hC _).mul ((hX 1).pow 2)).neg (by rw [zero_add])
    · exact homog_of_eq (((hC _).mul (hX 0)).mul (hX 2)) (by rw [zero_add, h2])
    · exact homog_of_eq ((((hn 3).mul (hC _)).mul (hC _)).mul ((hX 2).pow 2)) (by simp)
  · simpa [chartPoly, chartV] using isWeightedHomogeneous_zero K wV _
  · simp only [chartPoly, chartV, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Fin.isValue]
    refine IsWeightedHomogeneous.add ?_ ?_
    · exact homog_of_eq ((hn 6).mul ((hX 0).pow 2)).neg (by rw [zero_add])
    · exact homog_of_eq (((hC _).mul (hC _)).mul ((hX 2).pow 2)) (by simp)

theorem homog_dhat (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    IsWeightedHomogeneous wV (dhat g₂ g₃ w v) (wV v + ones) := by
  have hC : ∀ a : K, IsWeightedHomogeneous wV (C a : MvPolynomial (Var d₀ d₁ m) K) 0 :=
    fun a => isWeightedHomogeneous_C _ _
  cases v with
  | x i =>
    refine homog_of_eq (homog_Vprod.mul (hC _)) ?_
    simp [wV]
  | y j =>
    refine homog_of_eq (homog_Vprod.mul ((hC _).mul (isWeightedHomogeneous_X K wV _))) ?_
    simp [wV]
  | z j =>
    refine homog_of_eq (homog_Vprod.mul ((hC _).mul (isWeightedHomogeneous_X K wV _)).neg) ?_
    simp [wV]
  | e k c =>
    refine homog_of_eq ((homog_Vexc k).mul ((hC _).mul (homog_chartPoly_one g₂ g₃ k c))) ?_
    simp only [wV, zero_add, ones_eq k, two_nsmul]
    abel

theorem pderiv_eq_zero_of_homog {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hP : IsWeightedHomogeneous wV P d) {k : Fin m} (hk : d k = 0) (c : Fin 3) :
    pderiv (.e k c) P = 0 := by
  classical
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hw := hP (mem_support_iff.mp hs)
  have hle := Finsupp.le_weight (wE k) (s := (.e k c : Var d₀ d₁ m)) (by simp [wE, wV]) s
  rw [weight_wE, hw, hk] at hle
  rw [pderiv_monomial, Nat.le_zero.mp hle, Nat.cast_zero, mul_zero, monomial_zero]

theorem homog_pderiv {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hP : IsWeightedHomogeneous wV P d) (v : Var d₀ d₁ m) (w : LieE K d₀ d₁ m) :
    IsWeightedHomogeneous wV (dhat g₂ g₃ w v * pderiv v P) (d + ones) := by
  classical
  by_cases hv : ∃ k c, v = .e k c ∧ d k = 0
  · obtain ⟨k, c, rfl, hk⟩ := hv
    rw [pderiv_eq_zero_of_homog hP hk c, mul_zero]
    exact isWeightedHomogeneous_zero K wV _
  · push Not at hv
    have hn : d - wV v + wV v = d := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      cases v with
      | e k' c =>
        by_cases hkk : k = k'
        · subst hkk
          have := hv k c rfl
          simp only [wV, Pi.single_eq_same]
          omega
        · simp [wV, Pi.single_apply, hkk]
      | _ => simp [wV]
    refine homog_of_eq ((homog_dhat g₂ g₃ w v).mul (hP.pderiv hn)) ?_
    rw [add_right_comm, add_comm (wV v) (d - wV v), hn]

/-- **`D̂_w` is homogeneous of multidegree `(1, …, 1)`.** -/
theorem isWeightedHomogeneous_Dhat {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hP : IsWeightedHomogeneous wV P d) (w : LieE K d₀ d₁ m) :
    IsWeightedHomogeneous wV (Dhat g₂ g₃ w P) (d + ones) :=
  IsWeightedHomogeneous.sum _ _ _ fun v _ => homog_pderiv g₂ g₃ hP v w

/-! ### Points with `V_k = 0` -/

/-- **Euler.** At a cone point of `E_k` with `V_k = 0` (and `W_k ≠ 0`), `D̂_w P` vanishes for every
multihomogeneous `P` vanishing there. -/
theorem eval_Dhat_eq_zero_of_V [CharZero K] {x : Var d₀ d₁ m → K}
    {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsWeightedHomogeneous wV P d)
    (hPx : eval x P = 0) {k : Fin m} (hV : x (.e k 1) = 0) (hW : x (.e k 2) ≠ 0)
    (hF : Fv (g₂ k) (g₃ k) (fun c => x (.e k c)) = 0) (w : LieE K d₀ d₁ m) :
    eval x (Dhat g₂ g₃ w P) = 0 := by
  classical
  rw [Dhat, map_sum]
  -- the terms outside block `k` carry the factor `V_k`
  have hout : ∀ v, (∀ c, v ≠ .e k c) → eval x (dhat g₂ g₃ w v * pderiv v P) = 0 := by
    intro v hv
    have hfac : eval x (Vfac v) = 0 := by
      cases v with
      | e k' c =>
        have hk' : k' ≠ k := fun h => hv c (h ▸ rfl)
        simp only [Vfac, Vexc, map_prod, eval_X]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk'.symm, Finset.mem_univ k⟩) hV
      | _ =>
        simp only [Vfac, Vprod, map_prod, eval_X]
        exact Finset.prod_eq_zero (Finset.mem_univ k) hV
    simp [dhat, hfac]
  -- in block `k`, the `V`-chart derivation is `α · (U, V, W)`
  set U := x (.e k 0)
  set W := x (.e k 2)
  set α := (-(6 * U ^ 2) + 1 / 2 * g₂ k * W ^ 2) / W
  have hFk : -4 * U ^ 3 + g₂ k * U * W ^ 2 + g₃ k * W ^ 3 = 0 := by
    have := hF
    simp only [Fv, F, hV] at this
    linear_combination this
  have hch : ∀ c, eval x (chartPoly g₂ g₃ d₀ d₁ 1 k c) = α * x (.e k c) := by
    intro c
    fin_cases c
    · simp [chartPoly, chartV, hV, α]
      field_simp
      linear_combination (-3 : K) * hFk
    · simp [chartPoly, chartV, hV]
    · simp [chartPoly, chartV, α]
      field_simp
      simp only [U, W]
      ring
  -- Euler's identity in block `k`
  have hPk : IsWeightedHomogeneous (wE k) P (d k) := fun s hs => by rw [weight_wE, hP hs]
  have heul := hPk.sum_weight_X_mul_pderiv
  have heul' : ∑ c : Fin 3, x (.e k c) * eval x (pderiv (.e k c) P) = 0 := by
    have := congrArg (eval x) heul
    rw [map_nsmul, hPx, smul_zero, map_sum] at this
    rw [← this]
    rw [← (Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image fun c : Fin 3 => (Var.e k c : Var d₀ d₁ m))) ?_)]
    · rw [Finset.sum_image (fun a _ b _ h => by cases h; rfl)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [wE, wV]
    · intro v _ hv
      cases v with
      | e k' c =>
        have hk' : k' ≠ k := fun h => hv (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, h ▸ rfl⟩)
        simp [wE, wV, Pi.single_apply, hk']
      | _ => simp [wE, wV]
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image fun c : Fin 3 => (Var.e k c : Var d₀ d₁ m))) (fun v _ hv => hout v
      fun c h => hv (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, h.symm⟩))]
  rw [Finset.sum_image (fun a _ b _ h => by cases h; rfl)]
  calc ∑ c : Fin 3, eval x (dhat g₂ g₃ w (.e k c) * pderiv (.e k c) P)
      = eval x (Vexc k) * w.2.2 k * α * ∑ c : Fin 3, x (.e k c) * eval x (pderiv (.e k c) P) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [dhat, Vfac, dval, map_mul, eval_C, hch c]
        ring
    _ = 0 := by rw [heul', mul_zero]

/-! ### Translations preserve `vanish H` -/

theorem transl_mem_vanish [DecidableEq K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0) {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsSubgroupG H)
    {g : GPt K d₀ d₁ g₂ g₃} (hg : g ∈ H) (c : Fin m → Fin 2) {P : MvPolynomial (Var d₀ d₁ m) K}
    (hP : P ∈ vanish H) : τ g₂ g₃ g c P ∈ vanish H := by
  refine mem_vanish.mpr fun h hh lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl h2 hΔ g h c lam
  rw [hν]
  exact eval_coordsZ_eq_zero (mem_vanish.mp hP _ (hH.add_mem h hh g hg)) ν

end LSG.ME
