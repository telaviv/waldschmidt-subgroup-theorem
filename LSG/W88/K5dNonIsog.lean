/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K5dMain

/-!
# W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` with pairwise equal-or-non-isogenous curves

**`LSG.W88.hypStd_of_nonIsog`**: `HyperplaneKappa (gmStd d₀ d₁ Ls)` when the curves have algebraic
invariants and any two of them are either equal (`Ls j = Ls k`) or non-isogenous (`NonIsog`).
This covers e.g. `G_a × E × G_a × E × E′` with `E = ϖℤ[i]`, `E′ = Ω_ρℤ[ρ]`
(`nonIsog_I_rho`, `nonIsog_rho_I`).

## The argument (sketch)

By `K5d.hyperplaneKappaStd_of_rat` it suffices that every abelian tangent `t ⊂ ℂ^m` is
`ℚ̄`-rational. Take a chart of `t` (coordinates `ι : Fin s → Fin m` with `t ≅ ℂ^s`, inverse `lift`).
Fix `k` and put `x_j = lift(e_k)_j`. Every period of `E_{ι k}` in slot `k` has a nonzero multiple
lifting to a lattice point of `t` (`Chart.exists_nsmul_lift_mem`), so `n ω₁ x_j, n' ω₂ x_j ∈ Λ_j`,
where `ω₁, ω₂` are the periods of `E_{ι k}`; hence `(n n' x_j) Λ_{ι k} ⊂ Λ_j`.
* If `Ls (ι k) = Ls j`: `x_j` is a root of a rational quadratic (`isAlgebraic_of_lattice`, the
  one-curve argument of `abTan_rat_const`).
* If `NonIsog (Ls (ι k)) (Ls j)`: `n n' x_j = 0`, so `x_j = 0`.
So all `lift(e_k)` have algebraic coordinates, and they span `t`.

The same computation shows that `lift(e_k)` is supported on the block `{j : Ls j = Ls (ι k)}`:
**`t` splits along the equal-curve blocks** (`mul_mem_of_blockConst`: `t` is stable under
coordinatewise multiplication by any vector that is constant on blocks; with block indicators this
is `t = ⊕_b (t ∩ ℂ^{block b})`). The splitting is not needed for rationality but is recorded for the
vector-extension layer.

## Non-isogeny of `ℤ[i]`- and `ℤ[ρ]`-lattices

`nonIsog_of_tau`: if `ω₂ = τ ω₁`, `ω₂' = τ' ω₁'` and `τ (a + bτ') = c + dτ'`
(`a, b, c, d ∈ ℤ`) forces `a = b = 0`, then `NonIsog L L'` (from `α ω₁ = (a + bτ') ω₁'`,
`α ω₂ = (c + dτ') ω₁'`). For `τ = i` and `τ'` a root of `X² + X + 1` (and conversely) the
condition follows by comparing real and imaginary parts, as `Im τ' = ±√3/2` is irrational.
-/

open Complex Module

namespace LSG.W88

/-- `E_L` and `E_{L'}` are **not isogenous**: there is no `α ≠ 0` with `α Λ ⊂ Λ'`. -/
def NonIsog (L L' : PeriodPair) : Prop :=
  ∀ α : ℂ, α ≠ 0 → ¬ ∀ ω ∈ L.lattice, α * ω ∈ L'.lattice

namespace K5d

variable {m : ℕ}

/-- If `n ω₁ x, n' ω₂ x ∈ Λ'` (`ω₁, ω₂` the periods of `L`) and `L`, `L'` are not isogenous,
then `x = 0`. -/
lemma eq_zero_of_nonIsog {L L' : PeriodPair} (h : NonIsog L L') {x : ℂ} {n n' : ℕ} (hn : n ≠ 0)
    (hn' : n' ≠ 0) (h1 : (n : ℂ) * L.ω₁ * x ∈ L'.lattice) (h2 : (n' : ℂ) * L.ω₂ * x ∈ L'.lattice) :
    x = 0 := by
  by_contra hx
  refine h ((n : ℂ) * n' * x) (by simp [hn, hn', hx]) fun ω hω => ?_
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp hω
  have e : (n : ℂ) * n' * x * (a * L.ω₁ + b * L.ω₂) =
      ((a * n' : ℤ) : ℂ) * ((n : ℂ) * L.ω₁ * x) + ((b * n : ℤ) : ℂ) * ((n' : ℂ) * L.ω₂ * x) := by
    push_cast; ring
  rw [e]
  exact add_mem (LSG.Weierstrass.intCast_mul_mem _ h1 _) (LSG.Weierstrass.intCast_mul_mem _ h2 _)

/-- The lift of the `k`-th basis vector of a chart: a nonzero multiple of `ω₁ · lift(e_k)` and of
`ω₂ · lift(e_k)` (periods of `E_{ι k}`) is a lattice point. -/
lemma lift_single_mem {Ls : Fin m → PeriodPair} {t : Submodule ℂ (Fin m → ℂ)}
    (hab : IsAbelianTangent Ls t) (c : LSG.CM.Chart t) (k : Fin (finrank ℂ t)) :
    ∃ n n' : ℕ, n ≠ 0 ∧ n' ≠ 0 ∧ ∀ j,
      (n : ℂ) * (Ls (c.ι k)).ω₁ * c.lift (Pi.single k 1) j ∈ (Ls j).lattice ∧
      (n' : ℂ) * (Ls (c.ι k)).ω₂ * c.lift (Pi.single k 1) j ∈ (Ls j).lattice := by
  classical
  have hw : ∀ ω ∈ (Ls (c.ι k)).lattice, ∀ k', (Pi.single k ω : Fin (finrank ℂ t) → ℂ) k' ∈
      (Ls (c.ι k')).lattice := by
    intro ω hω k'
    by_cases h : k' = k
    · subst h; simpa using hω
    · simp [h, (Ls _).lattice.zero_mem]
  obtain ⟨n, hn, hn1⟩ := c.exists_nsmul_lift_mem hab (hw _ (Ls (c.ι k)).ω₁_mem_lattice)
  obtain ⟨n', hn', hn2⟩ := c.exists_nsmul_lift_mem hab (hw _ (Ls (c.ι k)).ω₂_mem_lattice)
  have e : ∀ (N : ℕ) (ω : ℂ) (j : Fin m), c.lift (N • (Pi.single k ω : Fin (finrank ℂ t) → ℂ)) j =
      (N : ℂ) * ω * c.lift (Pi.single k 1) j := by
    intro N ω j
    have : (N • (Pi.single k ω : Fin (finrank ℂ t) → ℂ)) = ((N : ℂ) * ω) • Pi.single k 1 := by
      ext i; by_cases h : i = k
      · subst h; simp [nsmul_eq_mul]
      · simp [h]
    rw [this, map_smul]; simp [mul_assoc]
  refine ⟨n, n', hn, hn', fun j => ⟨?_, ?_⟩⟩
  · have h1 := hn1 j; rwa [e] at h1
  · have h2 := hn2 j; rwa [e] at h2

/-- **Block support**: `lift(e_k)` vanishes outside the block of `ι k`. -/
lemma lift_single_eq_zero {Ls : Fin m → PeriodPair}
    (hni : ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k)) {t : Submodule ℂ (Fin m → ℂ)}
    (hab : IsAbelianTangent Ls t) (c : LSG.CM.Chart t) (k : Fin (finrank ℂ t)) (j : Fin m)
    (hj : Ls (c.ι k) ≠ Ls j) : c.lift (Pi.single k 1) j = 0 := by
  obtain ⟨n, n', hn, hn', hmem⟩ := lift_single_mem hab c k
  exact eq_zero_of_nonIsog ((hni (c.ι k) j).resolve_left hj) hn hn' (hmem j).1 (hmem j).2

/-- **`t` splits along the equal-curve blocks**: it is stable under coordinatewise multiplication
by any `D` that is constant on blocks. -/
theorem mul_mem_of_blockConst {Ls : Fin m → PeriodPair}
    (hni : ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k)) {t : Submodule ℂ (Fin m → ℂ)}
    (hab : IsAbelianTangent Ls t) {D : Fin m → ℂ} (hD : ∀ j k, Ls j = Ls k → D j = D k)
    {z : Fin m → ℂ} (hz : z ∈ t) : D * z ∈ t := by
  classical
  obtain ⟨c⟩ := LSG.CM.nonempty_chart t
  have hk : ∀ k, D * c.lift (Pi.single k 1) = D (c.ι k) • c.lift (Pi.single k 1) := by
    intro k; funext j
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : Ls (c.ι k) = Ls j
    · rw [hD j (c.ι k) h.symm]
    · rw [lift_single_eq_zero hni hab c k j h, mul_zero, mul_zero]
  have hsum : LSG.CM.proj c.ι z =
      ∑ k, (LSG.CM.proj c.ι z k) • (Pi.single k 1 : Fin (finrank ℂ t) → ℂ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  rw [← c.lift_proj hz, hsum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul, mul_smul_comm, hk, smul_smul]
  exact Submodule.smul_mem _ _ (c.lift_mem _)

/-- **Abelian tangent spaces of `E₁ × ⋯ × E_m` are `ℚ̄`-rational** when any two curves are equal
or non-isogenous. -/
theorem abTan_rat_nonIsog (Ls : Fin m → PeriodPair)
    (hni : ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k)) (t : Submodule ℂ (Fin m → ℂ))
    (hab : IsAbelianTangent Ls t) : RationalOverQbar t := by
  classical
  obtain ⟨c⟩ := LSG.CM.nonempty_chart t
  have halg : ∀ k j, IsAlgebraic ℚ (c.lift (Pi.single k 1) j) := by
    intro k j
    obtain ⟨n, n', hn, hn', hmem⟩ := lift_single_mem hab c k
    obtain ⟨h1, h2⟩ := hmem j
    rcases hni (c.ι k) j with he | hne
    · rw [he] at h1 h2; exact isAlgebraic_of_lattice _ hn hn' h1 h2
    · rw [eq_zero_of_nonIsog hne hn hn' h1 h2]; exact isAlgebraic_zero
  apply le_antisymm
  · intro z hz
    rw [← c.lift_proj hz]
    have : LSG.CM.proj c.ι z =
        ∑ k, (LSG.CM.proj c.ι z k) • (Pi.single k 1 : Fin (finrank ℂ t) → ℂ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c.lift_mem _, halg k⟩)
  · exact Submodule.span_le.mpr fun _ hw => hw.1

end K5d

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, any two curves equal or non-isogenous**
(`lean_mstar`'s `HyperplaneKappa (gmStd d₀ d₁ Ls)`, verbatim model `MStarCopyStd.lean`). -/
theorem hypStd_of_nonIsog {m : ℕ} (Ls : Fin m → PeriodPair)
    (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hni : ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k)) (d0 d1 : ℕ) :
    MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 Ls) :=
  K5d.hyperplaneKappaStd_of_rat Ls halg (K5d.abTan_rat_nonIsog Ls hni)

/-- The hypothesis `hni` for a family taking only two values `L`, `L'` that are non-isogenous
(both directions). -/
theorem hni_of_pair {m : ℕ} {Ls : Fin m → PeriodPair} {L L' : PeriodPair}
    (hLs : ∀ j, Ls j = L ∨ Ls j = L') (h : NonIsog L L') (h' : NonIsog L' L) :
    ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k) := by
  intro j k
  rcases hLs j with hj | hj <;> rcases hLs k with hk | hk <;> rw [hj, hk]
  · exact Or.inl rfl
  · exact Or.inr h
  · exact Or.inr h'
  · exact Or.inl rfl

/-- `HyperplaneKappa (gmStd d₀ d₁ Ls)` for a family of two non-isogenous curves `L`, `L'`. -/
theorem hypStd_of_pair {m : ℕ} (Ls : Fin m → PeriodPair) {L L' : PeriodPair}
    (hLs : ∀ j, Ls j = L ∨ Ls j = L') (hg : IsAlgebraic ℚ L.g₂ ∧ IsAlgebraic ℚ L.g₃)
    (hg' : IsAlgebraic ℚ L'.g₂ ∧ IsAlgebraic ℚ L'.g₃) (h : NonIsog L L') (h' : NonIsog L' L)
    (d0 d1 : ℕ) : MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 Ls) :=
  hypStd_of_nonIsog Ls (fun j => by rcases hLs j with hj | hj <;> rw [hj] <;> assumption)
    (hni_of_pair hLs h h') d0 d1

/-! ### Non-isogeny from the period ratios -/

/-- **Non-isogeny from the period ratios**: `ω₂ = τ ω₁`, `ω₂' = τ' ω₁'`, and
`τ (a + bτ') = c + dτ'` with `a, b, c, d ∈ ℤ` only for `a = b = 0`. -/
theorem nonIsog_of_tau {L L' : PeriodPair} {τ τ' : ℂ} (hL : L.ω₂ = τ * L.ω₁)
    (hL' : L'.ω₂ = τ' * L'.ω₁)
    (h : ∀ a b c d : ℤ, τ * (a + b * τ') = c + d * τ' → a = 0 ∧ b = 0) : NonIsog L L' := by
  intro α hα hall
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hall _ L.ω₁_mem_lattice)
  obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp (hall _ L.ω₂_mem_lattice)
  rw [hL'] at hab hcd
  rw [hL] at hcd
  have hω' := LSG.Weierstrass.ω₁_ne_zero L'
  have hω := LSG.Weierstrass.ω₁_ne_zero L
  have e : (τ * (a + b * τ') - (c + d * τ')) * L'.ω₁ = 0 := by
    linear_combination τ * hab - hcd
  have e' : τ * (a + b * τ') = c + d * τ' :=
    sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hω')
  obtain ⟨rfl, rfl⟩ := h a b c d e'
  simp only [Int.cast_zero, zero_mul, add_zero] at hab
  exact mul_ne_zero hα hω hab.symm

/-- A root of `X² + X + 1` has real part `−1/2` and `(2 Im)² = 3`. -/
lemma re_im_of_cubeRoot {ρ : ℂ} (hρ : ρ ^ 2 + ρ + 1 = 0) : ρ.re = -1 / 2 ∧ (2 * ρ.im) ^ 2 = 3 := by
  have hre := congrArg Complex.re hρ
  have him := congrArg Complex.im hρ
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re, Complex.add_im,
    Complex.mul_im, Complex.one_im, Complex.zero_im] at hre him
  have h2 : 2 * ρ.re + 1 = 0 := by
    have : ρ.im * (2 * ρ.re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rw [h] at hre; nlinarith [sq_nonneg (ρ.re + 1 / 2)]
    · exact h
  have hr : ρ.re = -1 / 2 := by linarith
  refine ⟨hr, ?_⟩
  rw [hr] at hre; nlinarith

/-- The imaginary part of a root of `X² + X + 1` is irrational. -/
lemma im_ne_rat_of_cubeRoot {ρ : ℂ} (hρ : ρ ^ 2 + ρ + 1 = 0) (q : ℚ) : ρ.im ≠ q := by
  intro hq
  have h3 := (re_im_of_cubeRoot hρ).2
  rw [hq] at h3
  have hirr : Irrational (Real.sqrt (3 : ℕ)) := Nat.prime_three.irrational_sqrt
  apply hirr.ne_rat |2 * q|
  push_cast
  rw [← Real.sqrt_sq_eq_abs, h3]

/-- If `x ≠ 0` is an integer and `x · Im ρ` is rational then contradiction. -/
lemma int_eq_zero_of_mul_im {ρ : ℂ} (hρ : ρ ^ 2 + ρ + 1 = 0) {x : ℤ} {q : ℚ}
    (h : (x : ℝ) * ρ.im = q) : x = 0 := by
  by_contra hx
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  apply im_ne_rat_of_cubeRoot hρ (q / x)
  push_cast
  rw [← h]; field_simp

/-- **`ϖℤ[i]` and `Ω_ρℤ[ρ]` are not isogenous** (`L` has CM by `ℤ[i]`, `L'` by `ℤ[ρ]`). -/
theorem nonIsog_I_rho {L L' : PeriodPair} {ρ : ℂ} (hL : L.ω₂ = I * L.ω₁)
    (hρ : ρ ^ 2 + ρ + 1 = 0) (hL' : L'.ω₂ = ρ * L'.ω₁) : NonIsog L L' := by
  refine nonIsog_of_tau hL hL' fun a b c d h => ?_
  have hr := (re_im_of_cubeRoot hρ).1
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im, hr] at hre him
  -- `hre : −b Im ρ = c − d/2`, `him : a − b/2 = d Im ρ`
  have hb : b = 0 := int_eq_zero_of_mul_im hρ (q := -(c - d / 2 : ℚ)) (by push_cast; linarith)
  subst hb
  have hd : d = 0 := int_eq_zero_of_mul_im hρ (q := (a : ℚ)) (by push_cast at him ⊢; linarith)
  subst hd
  refine ⟨?_, rfl⟩
  have ha : (a : ℝ) = 0 := by push_cast at him; linarith
  exact_mod_cast ha

/-- **`Ω_ρℤ[ρ]` and `ϖℤ[i]` are not isogenous** (the converse direction). -/
theorem nonIsog_rho_I {L L' : PeriodPair} {ρ : ℂ} (hρ : ρ ^ 2 + ρ + 1 = 0)
    (hL : L.ω₂ = ρ * L.ω₁) (hL' : L'.ω₂ = I * L'.ω₁) : NonIsog L L' := by
  refine nonIsog_of_tau hL hL' fun a b c d h => ?_
  have hr := (re_im_of_cubeRoot hρ).1
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im, hr] at hre him
  -- `hre : −a/2 − b Im ρ = c`, `him : −b/2 + a Im ρ = d`
  have hb : b = 0 := int_eq_zero_of_mul_im hρ (q := -(c + a / 2 : ℚ)) (by push_cast; linarith)
  have ha : a = 0 := int_eq_zero_of_mul_im hρ (q := (d + b / 2 : ℚ)) (by push_cast; linarith)
  exact ⟨ha, hb⟩

end LSG.W88
