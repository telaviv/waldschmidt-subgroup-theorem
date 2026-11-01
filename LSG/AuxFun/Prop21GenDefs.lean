/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21Lat

/-!
# W83 Prop. 2.1 for general lattice blocks (Tier 3): definitions and Lemma L

Coordinates `ℂⁿ`, real coordinate positions `Idx n = Fin n × Fin 2` (so `2n` of them, as in Tier 2),
vectors `e : Idx n → ℂⁿ` (in the intended application an `ℝ`-basis of `ℂⁿ`), and the lattice
`Λ = Σ_c ℤ e_c`. The element with integer coordinates `x` is `vecL e x = Σ_c x_c e_c`, and the
lattice grid of size `A` and step `1/K` is `{gptL e K v : |v_c| ≤ A}`, `gptL e K v = vecL e v / K`.

For the product basis `e_{(j,0)} = α_j δ_j`, `e_{(j,1)} = β_j δ_j` these are `perVec α β` and
`gpt α β K` of `Reps2.lean` (`LSG.Aux.vecL_prodBasis`, `Prop21GenProd.lean`).

**Lemma L** (`LSG.Aux.LemmaLInterp e`), the several-variable interpolation estimate that Tier 3
needs and that the one-variable machinery of Tiers 1–2 cannot give for non-product lattices
(`STAGE_A5_PROP21.md`, §1–§2). It is used only as an explicit hypothesis of
`LSG.Aux.prop21Gen_of_interp` (`Prop21Gen.lean`); it is never assumed as an axiom.

* `LSG.Aux.vecL`, `LSG.Aux.gptL`, `LSG.Aux.LemmaLInterp`.
* `LSG.Aux.grid_smallL` (transfer by the multiplier, as `grid_small2`).
-/

open Complex Finset

namespace LSG.Aux

variable {n κ : ℕ}

/-- The element `Σ_c x_c e_c` of the lattice spanned by `e`. -/
def vecL (e : Idx n → (Fin n → ℂ)) (x : Idx n → ℤ) : Fin n → ℂ :=
  ∑ c, (x c : ℂ) • e c

/-- The grid point `(1/K) Σ_c v_c e_c`. -/
noncomputable def gptL (e : Idx n → (Fin n → ℂ)) (K : ℕ) (v : Idx n → ℤ) : Fin n → ℂ :=
  (K : ℂ)⁻¹ • vecL e v

/-- **Lemma L (several-variable interpolation on a lattice grid), as a hypothesis.**

`LemmaLInterp e` says: there are constants `c > 0`, `C ≥ 1`, `A₀` (depending only on `e`) such that
for every entire `F : ℂⁿ → ℂ`, every grid size `A ≥ max(A₀, 1)` and step `1/K`, and radii
`0 < r`, `C r ≤ R` with `A ≤ r K ≤ 2A` (the grid has radius `≍ r`), if `|F| ≤ ε` on the grid
`{(1/K) Σ_c v_c e_c : |v_c| ≤ A}` and `|F| ≤ M` on the ball `‖z‖ ≤ R` (sup norm), then on the ball
`‖z‖ ≤ r`
`|F(z)| ≤ C^{A²} (ε + (C r/R)^{c A²} M)`.

* The exponent `c A²` is the point: the grid has `(2A+1)^{2n} ≍ A^{2n}` points, which is the
  dimension of the polynomials of degree `≍ A²` in `n` variables, so `A²` is the natural
  interpolation degree. For a product lattice (`n` one-variable lattices) it is Lagrange
  interpolation in each coordinate with `(2A+1)²` nodes; this case is *proved* in
  `LSG.Aux.lemmaLInterp_prodBasis` (`Prop21GenProd.lean`), a non-vacuity check. For a simple
  abelian variety no complex line meets the grid in more than `2A+1` points, and one-variable
  steps only give the exponent `≍ A` (`STAGE_A5_PROP21.md`, §2).
* Intended source [Lit, not verified here]: W83 Lemma 2.3 (Waldschmidt, *Diophantine approximation
  on linear algebraic groups*, Thm 7.4.13), which rests on Masser's Theorem A (Invent. Math. 63,
  1981) — a Schwarz lemma for approximate values on the points `Σ a_k e_k / K`, `|a_k| ≤ A`, of a
  lattice of rank `2n` in `ℂⁿ`. Proof plan: L1 (Cauchy estimates and Taylor remainder on `ℂⁿ`) +
  L2 (norming: a polynomial of degree `< T ≤ c A²` bounded by `1` on the grid is `≤ C^T` on `B_r`)
  + remainder estimate (`STAGE_A5_PROP21.md`, §3).
* Stated as weakly as `prop21Gen_of_interp` allows: constants are existential, `A` may be taken
  large (`A₀`), and the grid radius is pinned to `r` up to the factor `2` (`A ≤ r K ≤ 2A`).
  Nothing is assumed about `e` here; the statement is expected for every `ℝ`-basis `e` of `ℂⁿ`
  and is false for degenerate `e` (e.g. `e = 0`). -/
def LemmaLInterp (e : Idx n → (Fin n → ℂ)) : Prop :=
  ∃ c C : ℝ, ∃ A₀ : ℕ, 0 < c ∧ 1 ≤ C ∧
    ∀ (F : (Fin n → ℂ) → ℂ) (A K : ℕ) (r R ε M : ℝ), Differentiable ℂ F →
      A₀ ≤ A → 1 ≤ A → K ≠ 0 → 0 < r → (A : ℝ) ≤ r * K → r * K ≤ 2 * A → C * r ≤ R →
      0 ≤ ε → 0 ≤ M →
      (∀ v : Idx n → ℤ, (∀ c, |v c| ≤ A) → ‖F (gptL e K v)‖ ≤ ε) →
      (∀ z, ‖z‖ ≤ R → ‖F z‖ ≤ M) →
      ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ C ^ (A ^ 2) * (ε + (C * r / R) ^ (c * (A : ℝ) ^ 2) * M)

lemma vecL_add (e : Idx n → (Fin n → ℂ)) (x y : Idx n → ℤ) :
    vecL e (x + y) = vecL e x + vecL e y := by
  simp only [vecL, Pi.add_apply, Int.cast_add, add_smul, sum_add_distrib]

lemma vecL_zsmul (e : Idx n → (Fin n → ℂ)) (k : ℤ) (x : Idx n → ℤ) :
    vecL e (k • x) = (k : ℂ) • vecL e x := by
  simp only [vecL, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, smul_sum]

lemma vecL_sum (e : Idx n → (Fin n → ℂ)) (P : Fin κ → Idx n → ℤ) (y : Fin κ → ℤ) :
    vecL e (∑ i, y i • P i) = ∑ i, (y i : ℂ) • vecL e (P i) := by
  simp only [vecL, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    sum_smul, smul_sum, mul_smul]
  exact sum_comm

lemma gptL_add (e : Idx n → (Fin n → ℂ)) {K : ℕ} (hK : K ≠ 0) (s x : Idx n → ℤ) :
    gptL e K (s + (K : ℤ) • x) = gptL e K s + vecL e x := by
  have hK' : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK
  simp only [gptL, vecL_add, vecL_zsmul, smul_add, smul_smul, Int.cast_natCast,
    inv_mul_cancel₀ hK', one_smul]

lemma norm_vecL_le (e : Idx n → (Fin n → ℂ)) {S X : ℝ} (hS : ∑ c, ‖e c‖ ≤ S)
    (x : Idx n → ℤ) (hX0 : 0 ≤ X) (hx : ∀ c, |(x c : ℝ)| ≤ X) :
    ‖vecL e x‖ ≤ S * X := by
  calc ‖vecL e x‖ ≤ ∑ c, ‖(x c : ℂ) • e c‖ := norm_sum_le _ _
    _ = ∑ c, |(x c : ℝ)| * ‖e c‖ := by
        refine sum_congr rfl fun c _ => ?_
        rw [norm_smul, Complex.norm_intCast]
    _ ≤ ∑ c, X * ‖e c‖ := by gcongr with c; exact hx c
    _ = X * ∑ c, ‖e c‖ := by rw [mul_sum]
    _ ≤ X * S := by gcongr
    _ = S * X := by ring

lemma norm_gptL_le (e : Idx n → (Fin n → ℂ)) {K : ℕ} (hK : K ≠ 0) {S V : ℝ}
    (hS : ∑ c, ‖e c‖ ≤ S) (v : Idx n → ℤ) (hV0 : 0 ≤ V) (hv : ∀ c, |(v c : ℝ)| ≤ V) :
    ‖gptL e K v‖ ≤ S * V / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  rw [gptL, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_vecL_le e hS v hV0 hv) hKpos.le

/-- **Transfer by the multiplier for Tier 3** (as `grid_small2`): small at the condition
representatives `gptL e K s`, `s ∈ condIdx2`, implies small on the whole grid. -/
lemma grid_smallL {L A K : ℕ} {a b r U ε S C : ℝ} (e : Idx n → (Fin n → ℂ))
    (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n) (hd : (minorMat P I).det ≠ 0)
    (ψ : Fin L → (Fin n → ℂ) → ℂ) (p : Fin L → ℤ) (hK : K ≠ 0) (hr1 : 1 ≤ r)
    (hS0 : 0 ≤ S) (hS : ∑ c, ‖e c‖ ≤ S) (hAK : (A : ℝ) ≤ r * K) (hC0 : 0 ≤ C)
    (hC : (C : ℝ) = ((cAdj P I * cP P : ℤ) : ℝ)) (hb0 : 0 ≤ b) (hbU : b * r ^ 2 ≤ a * U)
    (hQP : ∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
      ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • vecL e (P i)‖) ^ 2) ∧
      ∀ l, ψ l (z + ∑ i, (k i : ℂ) • vecL e (P i)) = m * ψ l z)
    (Bn : ℕ) (hBn : (Bn : ℤ) = A + cAdj P I * cP P * (A + K))
    (hSc : ∀ s ∈ condIdx2 I ((K : ℤ) * (minorMat P I).det).natAbs Bn,
      ‖∑ l, (p l : ℂ) * ψ l (gptL e K s)‖ ≤ 2 * ε)
    (v : Idx n → ℤ) (hv : ∀ c, |v c| ≤ A) :
    ‖∑ l, (p l : ℂ) * ψ l (gptL e K v)‖ ≤ Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) * (2 * ε) := by
  classical
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  obtain ⟨s, y, hvs, hsI, hsb, hxb⟩ := lat_decomp P I hd hK v hv
  set x : Idx n → ℤ := ∑ i, y i • P i with hx
  have hg' : gptL e K v = gptL e K s + ∑ i, (y i : ℂ) • vecL e (P i) := by
    rw [hvs, gptL_add e hK, vecL_sum]
  have hs_mem : s ∈ condIdx2 I ((K : ℤ) * (minorMat P I).det).natAbs Bn := by
    refine Fintype.mem_piFinset.mpr fun c => ?_
    split_ifs with hc
    · obtain ⟨t, -, rfl⟩ := mem_image.mp hc
      exact mem_Ico.mpr ⟨(hsI t).1, (hsI t).2⟩
    · have := hsb c
      rw [← hBn, abs_le] at this
      exact mem_Icc.mpr this
  obtain ⟨m, hm, hmψ⟩ := hQP y (gptL e K s)
  have hmul : ∑ l, (p l : ℂ) * ψ l (gptL e K v) = m * ∑ l, (p l : ℂ) * ψ l (gptL e K s) := by
    rw [hg']
    simp only [hmψ, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  have hC' : ((cAdj P I : ℤ) : ℝ) * (cP P : ℝ) = C := by rw [hC]; push_cast; ring
  have hKr : (K : ℝ) ≤ r * K := le_mul_of_one_le_left hKpos.le hr1
  set B : ℝ := A + C * (A + K)
  have hsB : ∀ c, |(s c : ℝ)| ≤ B := fun c => by
    have := hsb c
    have h' : ((|s c| : ℤ) : ℝ) ≤ ((A + cAdj P I * cP P * (A + K) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [hC'] at h'
    simpa [B] using h'
  have hgs : ‖gptL e K s‖ ≤ S * (1 + 2 * C) * r := by
    refine (norm_gptL_le e hK hS s (by positivity) hsB).trans ?_
    rw [div_le_iff₀ hKpos]
    have : S * B ≤ S * ((1 + 2 * C) * r * K) := by
      gcongr
      simp only [B]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hAK hKr) hC0]
    linarith
  have hxB : ∀ c, |(x c : ℝ)| ≤ C * (A + K) / K := fun c => by
    have := hxb c
    have h' : (((K : ℤ) * |x c| : ℤ) : ℝ) ≤ ((cAdj P I * cP P * (A + K) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    rw [hC'] at h'
    rw [le_div_iff₀ hKpos]; linarith
  have hper : ‖∑ i, (y i : ℂ) • vecL e (P i)‖ ≤ 2 * S * C * r := by
    rw [← vecL_sum]
    refine (norm_vecL_le e hS x (by positivity) hxB).trans ?_
    have : C * (A + K) / K ≤ C * (r + 1) := by
      rw [div_le_iff₀ hKpos]
      nlinarith [mul_le_mul_of_nonneg_left hAK hC0]
    calc S * (C * (A + K) / K) ≤ S * (C * (r + 1)) := by gcongr
      _ ≤ 2 * S * C * r := by
          have hSC := mul_nonneg hS0 hC0
          nlinarith [mul_le_mul_of_nonneg_left hr1 hSC]
  have hm' : ‖m‖ ≤ Real.exp ((S * (1 + 4 * C)) ^ 2 * a * U) := by
    refine hm.trans (Real.exp_le_exp.mpr ?_)
    set u := ‖gptL e K s‖ + ‖∑ i, (y i : ℂ) • vecL e (P i)‖
    have hu : u ≤ S * (1 + 4 * C) * r := by simp only [u]; linarith
    have hu0 : 0 ≤ u := by positivity
    calc b * u ^ 2 ≤ b * (S * (1 + 4 * C) * r) ^ 2 := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * (b * r ^ 2) := by ring
      _ ≤ (S * (1 + 4 * C)) ^ 2 * (a * U) := by gcongr
      _ = (S * (1 + 4 * C)) ^ 2 * a * U := by ring
  rw [hmul, norm_mul]
  exact mul_le_mul hm' (hSc s hs_mem) (norm_nonneg _) (Real.exp_pos _).le

end LSG.Aux
