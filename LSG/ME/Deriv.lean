import Mathlib
import LSG.ME.Transl
import StrongSix.M2.Wustholz

/-!
# Invariant derivations on the multi-cone model (STAGE2 §3)

On `E : V²W = 4U³ − g₂UW² − g₃W³` with affine coordinates `u = U/W`, `v = V/W` (so that
`v² = 4u³ − g₂u − g₃`; in Mathlib's coordinates `x = u`, `y = v/2`, matching `rep = (x : 2y : 1)`)
the invariant derivation is `D u = v`, `D v = 6u² − g₂/2` (`u = ℘`, `v = ℘'`). It is induced on the
cone by three homogeneous derivations of degree `+1`, one per chart `L ∈ {U, V, W}`
(`chartPoly`, chart index `0, 1, 2` for `U, V, W`; re-verified here by `ring`):

* `W`-chart: `U ↦ VW`, `V ↦ 6U² − (g₂/2)W²`, `W ↦ 0`;
* `U`-chart: `U ↦ UV`, `V ↦ (3/2)V² + g₂UW + (3/2)g₃W²`, `W ↦ 0`;
* `V`-chart: `U ↦ −V²/2 − g₂UW − (3/2)g₃W²`, `V ↦ 0`, `W ↦ −6U² + (g₂/2)W²`.

* `Dw g₂ g₃ ch w` for `w = (ξ, η, ζ) ∈ K^{d₀} × K^{d₁} × K^m` and charts `ch : Fin m → Fin 3`:
  `Σ ξᵢ ∂/∂Xᵢ + Σ ηⱼ (Yⱼ ∂/∂Yⱼ − Zⱼ ∂/∂Zⱼ) + Σ ζₖ (chart derivation of block k)` (`Dw_apply`).
* **`Dw_mem_FLE`**: elliptic block degrees go up by at most `1`, the others do not go up.
* **`Dw_IG`**: `Dw` maps `I_G` into `I_G` (`δ_W F = δ_V F = 0`, `δ_U F = 3V F`).
* **`chart_affine`**: the analytic meaning. In each chart `L`,
  `W δU − U δW = L · V W + a F` and `W δV − V δW = L · (6U² − (g₂/2) W²) + b F` with constants
  `a, b`; so on `E` with `W ≠ 0`: `δ(u) = L · v`, `δ(v) = L · (6u² − g₂/2)`, i.e. `δ = L · D`.
* `chartAt g`: the canonical chart at `g` (`W` if `gₖ ≠ 0`, `V` if `gₖ = 0`), whose form is `1` at
  `rep gₖ`; **`VanishesAlong W P n g`**: all derivatives along words of length `< n` in `W` vanish
  at every cone representative of `g` (StrongSix's `DL`).
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE S bdeg bdeg_add bdeg_single mul_mem_FLE FLE_mono DL DL_cons)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ}

/-- The Lie algebra `K^{d₀} × K^{d₁} × K^m` of `G`. -/
abbrev LieE (K : Type u) (d₀ d₁ m : ℕ) : Type u := (Fin d₀ → K) × (Fin d₁ → K) × (Fin m → K)

variable (g₂ g₃ : Fin m → K)

section Charts

variable (d₀ d₁ : ℕ) (k : Fin m)

local notation "U" => (X (Var.e k 0) : MvPolynomial (Var d₀ d₁ m) K)
local notation "V" => (X (Var.e k 1) : MvPolynomial (Var d₀ d₁ m) K)
local notation "W" => (X (Var.e k 2) : MvPolynomial (Var d₀ d₁ m) K)
local notation "h" => (C (1 / 2 : K) : MvPolynomial (Var d₀ d₁ m) K)

/-- The `U`-chart derivation: `U ↦ UV`, `V ↦ (3/2)V² + g₂UW + (3/2)g₃W²`, `W ↦ 0`. -/
noncomputable def chartU : Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  ![U * V, 3 * h * V ^ 2 + C (g₂ k) * U * W + 3 * h * C (g₃ k) * W ^ 2, 0]

/-- The `V`-chart derivation: `U ↦ −V²/2 − g₂UW − (3/2)g₃W²`, `V ↦ 0`, `W ↦ −6U² + (g₂/2)W²`. -/
noncomputable def chartV : Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  ![-(h * V ^ 2) - C (g₂ k) * U * W - 3 * h * C (g₃ k) * W ^ 2, 0,
    -(6 * U ^ 2) + h * C (g₂ k) * W ^ 2]

/-- The `W`-chart derivation: `U ↦ VW`, `V ↦ 6U² − (g₂/2)W²`, `W ↦ 0`. -/
noncomputable def chartW : Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  ![V * W, 6 * U ^ 2 - h * C (g₂ k) * W ^ 2, 0]

end Charts

/-- The chart derivations of block `k` on `(U, V, W)`; chart `0, 1, 2` = `U, V, W`
(written with `h = C (1/2)`: `3h = 3/2`, `h g₂ = g₂/2`). -/
noncomputable def chartPoly (d₀ d₁ : ℕ) (ch : Fin 3) (k : Fin m) :
    Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  ![chartU g₂ g₃ d₀ d₁ k, chartV g₂ g₃ d₀ d₁ k, chartW g₂ d₀ d₁ k] ch

/-- The values of `D_w` on the variables. -/
noncomputable def dval (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) :
    Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) K
  | .x i => C (w.1 i)
  | .y j => C (w.2.1 j) * X (.y j)
  | .z j => -(C (w.2.1 j) * X (.z j))
  | .e k c => C (w.2.2 k) * chartPoly g₂ g₃ d₀ d₁ (ch k) k c

/-- **The derivation `D_w`** with charts `ch`. -/
noncomputable def Dw (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) :
    Derivation K (MvPolynomial (Var d₀ d₁ m) K) (MvPolynomial (Var d₀ d₁ m) K) :=
  mkDerivation K (dval g₂ g₃ ch w)

variable {g₂ g₃}

@[simp] theorem Dw_X (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    Dw g₂ g₃ ch w (X v) = dval g₂ g₃ ch w v := mkDerivation_X _ _ _

@[simp] theorem Dw_C (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (a : K) :
    Dw g₂ g₃ ch w (C a) = 0 := by
  rw [← algebraMap_eq]; exact Derivation.map_algebraMap _ _

@[simp] theorem Dw_ofNat (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (n : ℕ) [n.AtLeastTwo] :
    Dw g₂ g₃ ch w (OfNat.ofNat n) = 0 := by
  rw [← Nat.cast_ofNat]; exact Derivation.map_natCast _ n

/-- `D_w = Σ_v (D_w X_v) ∂/∂X_v`; with `dval` this is the formula of STAGE2 §3. -/
theorem Dw_apply (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) K) :
    Dw g₂ g₃ ch w P = ∑ v, dval g₂ g₃ ch w v * pderiv v P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e : ∀ x, pderiv x (p * X v) =
        p * (Pi.single x (1 : MvPolynomial (Var d₀ d₁ m) K) : Var d₀ d₁ m → _) v +
          X v * pderiv x p := by
      intro x; rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp_rw [e]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, Dw_X]
    have e1 : ∑ x, dval g₂ g₃ ch w x *
        (p * (Pi.single x (1 : MvPolynomial (Var d₀ d₁ m) K) : Var d₀ d₁ m → _) v) =
          p * dval g₂ g₃ ch w v := by
      rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb)]; ring)
        (by simp)]
      simp only [Pi.single_eq_same]; ring
    have e2 : ∑ x, dval g₂ g₃ ch w x * (X v * pderiv x p) =
        X v * ∑ x, dval g₂ g₃ ch w x * pderiv x p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
    simp only [mul_add, Finset.sum_add_distrib, e1, e2]

/-! ### Block degrees -/

section Degree

variable {σ ι : Type*} [Fintype σ] [DecidableEq ι] {β : σ → ι}

/-- A derivation raising each variable's block degree by at most `E` raises all block degrees by
at most `E`. -/
theorem mkDerivation_mem_FLE {f : σ → MvPolynomial σ K} {E : ι → ℕ}
    (hf : ∀ v, f v ∈ FLE K β (Pi.single (β v) 1 + E)) {D : ι → ℕ} {P : MvPolynomial σ K}
    (hP : P ∈ FLE K β D) : mkDerivation K f P ∈ FLE K β (D + E) := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hsS : s ∈ S β D := by rw [FLE, mem_restrictSupport_iff] at hP; exact hP hs
  rw [mkDerivation_monomial]
  refine Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun i hi => ?_)
  have hi1 : 1 ≤ s i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : Finsupp.single i 1 ≤ s := fun x => by
    rw [Finsupp.single_apply]; split_ifs with h
    · subst h; exact hi1
    · exact Nat.zero_le _
  have hb : ∀ b, bdeg β (s - Finsupp.single i 1) b + (if β i = b then 1 else 0) = bdeg β s b :=
    fun b => by rw [← bdeg_single, ← bdeg_add, tsub_add_cancel_of_le hle]
  have hmon : (monomial (s - Finsupp.single i 1) ((s i : ℕ) : K) : MvPolynomial σ K) ∈
      FLE K β (D - Pi.single (β i) 1) := by
    rw [FLE, monomial_mem_restrictSupport]
    refine Or.inl fun b => ?_
    have h1 := hb b
    have h2 := hsS b
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases h : b = β i
    · subst h; simp only [ite_true] at h1 ⊢; omega
    · simp only [h, Ne.symm h, ite_false] at h1 ⊢; omega
  dsimp only
  rw [smul_eq_mul]
  refine FLE_mono K β (fun b => ?_) (mul_mem_FLE K hmon (hf i))
  have h1 := hb b
  have h2 := hsS b
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h : b = β i
  · subst h; simp only [ite_true] at h1 ⊢; omega
  · simp only [h, Ne.symm h, ite_false] at h1 ⊢; omega

end Degree

/-- The degree shift of `D_w`: `1` on elliptic blocks, `0` otherwise. -/
def ellOnes : Blk m → ℕ
  | .e _ => 1
  | _ => 0

theorem chartPoly_mem (ch : Fin 3) (k : Fin m) (c : Fin 3) :
    chartPoly g₂ g₃ d₀ d₁ ch k c ∈ FLE K blk (Pi.single (Blk.e k) 2) := by
  unfold chartPoly chartU chartV chartW
  fin_cases ch <;> fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    first | exact Submodule.zero_mem _ | fle_tac

theorem dval_mem (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (v : Var d₀ d₁ m) :
    dval g₂ g₃ ch w v ∈ FLE K blk (Pi.single (blk v) 1 + ellOnes) := by
  cases v with
  | x i => exact fle_C _
  | y j =>
    refine fle_le (mul_mem_FLE K (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0) _)
      (fle_X (Var.y j))) ?_
    rw [Pi.le_def]; intro b; cases b <;> simp [ellOnes]
  | z j =>
    refine fle_neg (fle_le (mul_mem_FLE K (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m))
      (D := 0) _) (fle_X (Var.z j))) ?_)
    rw [Pi.le_def]; intro b; cases b <;> simp [ellOnes]
  | e k c =>
    refine fle_le (mul_mem_FLE K (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0) _)
      (chartPoly_mem (ch k) k c)) ?_
    rw [Pi.le_def]; intro b
    cases b with
    | e k' => by_cases h : k' = k <;> simp [ellOnes, h]
    | _ => simp [ellOnes]

/-- **`D_w` raises elliptic block degrees by at most `1`** and does not raise the others. -/
theorem Dw_mem_FLE (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) :
    Dw g₂ g₃ ch w P ∈ FLE K blk (D + ellOnes) :=
  mkDerivation_mem_FLE (dval_mem ch w) hP

/-! ### `I_G` -/

theorem Dw_YZ (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (j : Fin d₁) :
    Dw g₂ g₃ ch w (YZ K d₀ m j) = 0 := by
  simp only [YZ, map_sub, Derivation.leibniz, Dw_X, dval, smul_eq_mul, Derivation.map_one_eq_zero]
  ring

omit [Field K] in
theorem two_mul_C_half [Field K] (h2 : (2 : K) ≠ 0) :
    (2 : MvPolynomial (Var d₀ d₁ m) K) * C (1 / 2) = 1 := by
  rw [← map_ofNat C 2, ← C_mul, mul_one_div_cancel h2, C_1]

theorem Dw_Fk (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) (k : Fin m) :
    Dw g₂ g₃ ch w (Fk g₂ g₃ d₀ d₁ k) =
      (if ch k = 0 then C (w.2.2 k) * (3 * X (Var.e k 1)) else 0) * Fk g₂ g₃ d₀ d₁ k := by
  have hh := two_mul_C_half (d₀ := d₀) (d₁ := d₁) (m := m) h2
  have h4 : (4 : MvPolynomial (Var d₀ d₁ m) K) = C 4 := (map_ofNat C 4).symm
  simp only [Fk, F, h4, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, Dw_X, Dw_C,
    dval, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero]
  generalize ch k = c
  fin_cases c <;>
    simp only [chartPoly, chartU, chartV, chartW, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, ite_false, Nat.cast_ofNat,
      ← h4]
  · linear_combination (C (w.2.2 k) * (3 * X (Var.e k 1) ^ 3 * X (Var.e k 2) +
      3 * C (g₃ k) * X (Var.e k 1) * X (Var.e k 2) ^ 3)) * hh
  · linear_combination (C (w.2.2 k) * (C (g₂ k) ^ 2 * X (Var.e k 0) * X (Var.e k 2) ^ 3 +
      6 * X (Var.e k 0) ^ 2 * X (Var.e k 1) ^ 2 + 18 * C (g₃ k) * X (Var.e k 0) ^ 2 * X (Var.e k
          2) ^ 2)) * hh
  · linear_combination (-(C (w.2.2 k) * C (g₂ k) * X (Var.e k 1) * X (Var.e k 2) ^ 3)) * hh

/-- **`D_w` maps `I_G` into `I_G`.** -/
theorem Dw_IG (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) {P : MvPolynomial (Var
    d₀ d₁ m) K}
    (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) : Dw g₂ g₃ ch w P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃
        := by
  rw [IG, Ideal.ofList] at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · rw [Dw_YZ]; exact Ideal.zero_mem _
    · rw [Dw_Fk h2]; exact Ideal.mul_mem_left _ _ (Fk_mem_IG g₂ g₃ k)
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx')

/-! ### The analytic meaning -/

/-- **Chart identities.** For the chart derivation `δ` of chart `L = X (e k ch)` (the `ζ = 1`
part of `D_w` on block `k`): `W δU − U δW = L · VW + a F` and `W δV − V δW = L · (6U² − (g₂/2)W²)
    + b F`
for constants `a, b`. Hence on `E` with `W ≠ 0`, in `u = U/W`, `v = V/W`:
`δ u = L · v` and `δ v = L · (6u² − g₂/2)`: `δ` is `L` times the invariant derivation. -/
theorem chart_affine (h2 : (2 : K) ≠ 0) (ch : Fin 3) (k : Fin m) :
    ∃ a b : K,
      X (Var.e k 2) * chartPoly g₂ g₃ d₀ d₁ ch k 0 - X (Var.e k 0) * chartPoly g₂ g₃ d₀ d₁ ch k 2 =
        X (Var.e k ch) * (X (Var.e k 1) * X (Var.e k 2)) + C a * Fk g₂ g₃ d₀ d₁ k ∧
      X (Var.e k 2) * chartPoly g₂ g₃ d₀ d₁ ch k 1 - X (Var.e k 1) * chartPoly g₂ g₃ d₀ d₁ ch k 2 =
        X (Var.e k ch) * (6 * X (Var.e k 0) ^ 2 - C (g₂ k / 2) * X (Var.e k 2) ^ 2) +
          C b * Fk g₂ g₃ d₀ d₁ k := by
  have hh := two_mul_C_half (d₀ := d₀) (d₁ := d₁) (m := m) h2
  have hg : C (g₂ k / 2) = (C (1 / 2) * C (g₂ k) : MvPolynomial (Var d₀ d₁ m) K) := by
    rw [← C_mul, div_eq_mul_one_div, mul_comm]
  have h3 : C (3 * (1 / 2) : K) = (3 * C (1 / 2) : MvPolynomial (Var d₀ d₁ m) K) := by
    rw [C_mul, map_ofNat]
  fin_cases ch
  · refine ⟨0, 3 * (1 / 2), ?_, ?_⟩ <;>
      simp only [chartPoly, chartU, chartV, chartW, Fk, F, hg, h3, Fin.zero_eta,
          Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, C_0]
    · ring
    · linear_combination (6 * X (Var.e k 0) ^ 3 - C (g₂ k) * X (Var.e k 0) * X (Var.e k 2) ^ 2) * hh
  · refine ⟨-(3 * (1 / 2)), 0, ?_, ?_⟩ <;>
      simp only [chartPoly, chartU, chartV, chartW, Fk, F, hg, h3, C_neg, Fin.mk_one,
          Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, C_0]
    · linear_combination (X (Var.e k 1) ^ 2 * X (Var.e k 2) + C (g₂ k) * X (Var.e k 0) * X (Var.e
        k 2) ^ 2 -
        6 * X (Var.e k 0) ^ 3) * hh
    · ring
  · refine ⟨0, 0, ?_, ?_⟩ <;>
      simp only [chartPoly, chartU, chartV, chartW, Fk, F, hg, Fin.reduceFinMk,
          Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, C_0] <;>
      ring

/-! ### Vanishing along a subspace -/

/-- The canonical chart at `g`: the `W`-chart (`2`) if `gₖ ≠ 0`, the `V`-chart (`1`) if `gₖ = 0`. -/
def chartAt (g : GPt K d₀ d₁ g₂ g₃) : Fin m → Fin 3 := fun k =>
  match g.2.2 k with
  | 0 => 1
  | .some .. => 2

/-- The canonical chart form is `1` at `rep gₖ`. -/
theorem rep_chartAt (g : GPt K d₀ d₁ g₂ g₃) (k : Fin m) : rep (g.2.2 k) (chartAt g k) = 1 := by
  unfold chartAt
  cases g.2.2 k with
  | zero => simp [rep, O]
  | some x y h => simp [rep]

variable (g₂ g₃) in
/-- **`P` vanishes to order `≥ n` along `W` at `g`**: every derivative of `P` along a word of
length `< n` in `W` (canonical charts at `g`, first letter applied first) vanishes at every cone
representative of `g`. -/
def VanishesAlong (W : Submodule K (LieE K d₀ d₁ m)) (P : MvPolynomial (Var d₀ d₁ m) K) (n : ℕ)
    (g : GPt K d₀ d₁ g₂ g₃) : Prop :=
  ∀ l : List (LieE K d₀ d₁ m), (∀ w ∈ l, w ∈ W) → l.length < n →
    ∀ lam, eval (coords g lam) (DL (Dw g₂ g₃ (chartAt g)) l P) = 0

/-- Words of derivations preserve `I_G`. -/
theorem DL_IG (h2 : (2 : K) ≠ 0) (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m)) {P :
    MvPolynomial (Var d₀ d₁ m) K}
    (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) :
    DL (Dw g₂ g₃ ch) l P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  induction l generalizing P with
  | nil => simpa using hP
  | cons w l ih => rw [DL_cons]; exact ih (Dw_IG h2 ch w hP)

/-- Words of derivations raise elliptic block degrees by at most the word length. -/
theorem DL_mem_FLE (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m)) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) :
    DL (Dw g₂ g₃ ch) l P ∈ FLE K blk (D + l.length • ellOnes) := by
  induction l generalizing D P with
  | nil => simpa using hP
  | cons w l ih =>
    rw [DL_cons]
    have := ih (Dw_mem_FLE (g₂ := g₂) (g₃ := g₃) ch w hP)
    rwa [List.length_cons, add_smul, one_smul, add_comm (l.length • ellOnes), ← add_assoc]

end LSG.ME
