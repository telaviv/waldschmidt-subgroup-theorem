/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarPer

/-!
# `A` is simple as a complex torus (the `simple` field of the A-block, STAGE_A4 §2.1)

**`simple_latt`**: a complex subspace `t ⊆ ℂ²` with `IsRatSub latt t` is `⊥` or `⊤`. **`simple_kerE`**: the same for
`kerE G` (finite-index transfer `isRatSub_iff_of_nsmul`, `isNsmulIn_latt_kerE`).

Proof. Write `perVec e j = c_j ζ^{(j+1)e}` (`perVec_eq`, `ζ = ζ₅`), so a lattice point `a = Σ nₑ perVec e` has
coordinates `a_j = c_j α(ζ^{j+1})` with `α = Σ nₑ Xᵉ ∈ ℤ[X]`, `deg α ≤ 3`.
* (`real_of_latt`) If `a, b` are lattice points, `a ≠ 0`, `b = c a` with `c ∈ ℂ`, then `β(ζ) = c α(ζ)` and
  `β(ζ²) = c α(ζ²)`. The rational polynomial `P = β·α(X²) − β(X²)·α` vanishes at `ζ`, hence (minimal polynomial =
  `Φ₅`) at `ζ²` and `ζ⁴`; `α` has no root among the primitive 5th roots (degree `< 4`). This gives `β = c α` at all
  four primitive roots, so `β = c α` as polynomials of degree `≤ 3`, and `c = mₑ/nₑ ∈ ℚ`.
* If `t ≠ ⊥, ⊤`, `t` is a complex line; it contains a nonzero lattice point `a` (the lattice points of `t` span `t`),
  and every lattice point of `t` is a complex, hence real, multiple of `a`. So `t ⊆ ℝ a`, but `I • a ∈ t`.
-/

noncomputable section

open Polynomial Module LSG.JacAn LSG.JacAn.Beta

namespace LSG.JacBlock

/-- `ζ₅`. -/
abbrev ζ5 : ℂ := zetaN 5

lemma ζ5_prim : IsPrimitiveRoot ζ5 5 := zetaN_prim 5 (by norm_num)

/-- The integer polynomial of a lattice point. -/
def latPoly (n : Fin 4 → ℤ) : ℚ[X] := ∑ e : Fin 4, C (n e : ℚ) * X ^ (e : ℕ)

lemma aeval_latPoly (n : Fin 4 → ℤ) (x : ℂ) : aeval x (latPoly n) = ∑ e : Fin 4, (n e : ℂ) * x ^ (e : ℕ) := by
  simp [latPoly, map_sum]

lemma latPoly_natDegree (n : Fin 4 → ℤ) : (latPoly n).natDegree < 4 := by
  have : (latPoly n).natDegree ≤ 3 := by
    refine natDegree_sum_le_of_forall_le _ _ fun e _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Nat.lt_succ_iff.mp e.2
  omega

lemma latPoly_coeff (n : Fin 4 → ℤ) (e : Fin 4) : (latPoly n).coeff e = n e := by
  simp only [latPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    have : (e : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h'.symm)
    simp [this]
  · simp

/-- Vanishing at `ζ` transfers to every primitive 5th root. -/
lemma aeval_transfer {P : ℚ[X]} (h : aeval ζ5 P = 0) {μ : ℂ} (hμ : IsPrimitiveRoot μ 5) : aeval μ P = 0 := by
  have hd : minpoly ℚ ζ5 ∣ P := minpoly.dvd ℚ ζ5 h
  rw [← cyclotomic_eq_minpoly_rat ζ5_prim (by norm_num), cyclotomic_eq_minpoly_rat hμ (by norm_num)] at hd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval ℚ μ)

/-- A nonzero rational polynomial of degree `< 4` has no primitive 5th root as a root. -/
lemma aeval_ne_zero {P : ℚ[X]} (hP : P ≠ 0) (hdeg : P.natDegree < 4) {μ : ℂ} (hμ : IsPrimitiveRoot μ 5) :
    aeval μ P ≠ 0 := by
  intro h
  have hd : minpoly ℚ μ ∣ P := minpoly.dvd ℚ μ h
  rw [← cyclotomic_eq_minpoly_rat hμ (by norm_num)] at hd
  have := natDegree_le_of_dvd hd hP
  rw [natDegree_cyclotomic] at this
  have h5 : Nat.totient 5 = 4 := by decide
  omega

lemma prim_pow (k : ℕ) (hk : k.Coprime 5) : IsPrimitiveRoot (ζ5 ^ k) 5 := ζ5_prim.pow_of_coprime k hk

/-- Lattice points as integer combinations of the four periods. -/
lemma latt_repr {v : Fin 2 → ℂ} (hv : v ∈ latt) : ∃ n : Fin 4 → ℤ, v = ∑ e : Fin 4, n e • perVec (e : ℕ) := by
  unfold latt at hv
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_range_iff_of_fintype.mp hv
  exact ⟨n, hn⟩

lemma latt_coord (n : Fin 4 → ℤ) (j : Fin 2) :
    (∑ e : Fin 4, n e • perVec (e : ℕ)) j = cJ j * aeval (ζ5 ^ ((j : ℕ) + 1)) (latPoly n) := by
  rw [aeval_latPoly, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.smul_apply, perVec_eq, zsmul_eq_mul]
  ring

/-- **The CM step**: a complex ratio of two lattice points is real. -/
theorem real_of_latt {a b : Fin 2 → ℂ} (ha : a ∈ latt) (hb : b ∈ latt) (ha0 : a ≠ 0) {c : ℂ}
    (h : b = c • a) : ∃ r : ℝ, c = r := by
  obtain ⟨n, rfl⟩ := latt_repr ha
  obtain ⟨m, rfl⟩ := latt_repr hb
  set α := latPoly n
  set β := latPoly m
  have hc0 : cJ 0 ≠ 0 := cJ_ne_zero (by norm_num)
  have hc1 : cJ 1 ≠ 0 := cJ_ne_zero (by norm_num)
  have hj : ∀ j : Fin 2, aeval (ζ5 ^ ((j : ℕ) + 1)) β = c * aeval (ζ5 ^ ((j : ℕ) + 1)) α := by
    intro j
    have hcj : cJ j ≠ 0 := cJ_ne_zero (by omega)
    have := congrFun h j
    rw [Pi.smul_apply, latt_coord, latt_coord, smul_eq_mul] at this
    exact mul_left_cancel₀ hcj (by rw [this]; ring)
  have h1 : aeval ζ5 β = c * aeval ζ5 α := by simpa using hj 0
  have h2 : aeval (ζ5 ^ 2) β = c * aeval (ζ5 ^ 2) α := by simpa using hj 1
  -- `α ≠ 0`
  have hα : α ≠ 0 := by
    intro h0
    apply ha0
    funext j
    rw [latt_coord, show latPoly n = α from rfl, h0, map_zero, mul_zero]
    rfl
  have h5 : ζ5 ^ 5 = 1 := ζ5_prim.pow_eq_one
  -- the polynomial `P = β·α(X²) − β(X²)·α`
  set P : ℚ[X] := β * α.comp (X ^ 2) - β.comp (X ^ 2) * α
  have hPev : ∀ x : ℂ, aeval x P = aeval x β * aeval (x ^ 2) α - aeval (x ^ 2) β * aeval x α := by
    intro x; simp [P, aeval_comp]
  have hP1 : aeval ζ5 P = 0 := by rw [hPev, h1, h2]; ring
  have hP2 := aeval_transfer hP1 (prim_pow 2 (by decide))
  have hP4 := aeval_transfer hP1 (prim_pow 4 (by decide))
  rw [hPev] at hP2 hP4
  have e4 : (ζ5 ^ 2) ^ 2 = ζ5 ^ 4 := by ring
  have e3 : (ζ5 ^ 4) ^ 2 = ζ5 ^ 3 := by
    calc (ζ5 ^ 4) ^ 2 = ζ5 ^ 5 * ζ5 ^ 3 := by ring
      _ = ζ5 ^ 3 := by rw [h5, one_mul]
  rw [e4] at hP2
  rw [e3] at hP4
  have hα2 := aeval_ne_zero hα (latPoly_natDegree n) (prim_pow 2 (by decide))
  have hα4 := aeval_ne_zero hα (latPoly_natDegree n) (prim_pow 4 (by decide))
  have h4 : aeval (ζ5 ^ 4) β = c * aeval (ζ5 ^ 4) α := by
    have : aeval (ζ5 ^ 2) α * (aeval (ζ5 ^ 4) β - c * aeval (ζ5 ^ 4) α) = 0 := by
      linear_combination -hP2 + aeval (ζ5 ^ 4) α * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα2)
  have h3 : aeval (ζ5 ^ 3) β = c * aeval (ζ5 ^ 3) α := by
    have : aeval (ζ5 ^ 4) α * (aeval (ζ5 ^ 3) β - c * aeval (ζ5 ^ 3) α) = 0 := by
      linear_combination -hP4 + aeval (ζ5 ^ 3) α * h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα4)
  -- `Q = β − c α` (over `ℂ`) has four roots and degree `≤ 3`
  set Q : ℂ[X] := β.map (algebraMap ℚ ℂ) - C c * α.map (algebraMap ℚ ℂ)
  have hQev : ∀ x : ℂ, Q.eval x = aeval x β - c * aeval x α := by
    intro x; simp [Q, eval_map_algebraMap]
  have hinj : Function.Injective (fun i : Fin 4 => ζ5 ^ ((i : ℕ) + 1)) := by
    intro a b hab
    have := ζ5_prim.pow_inj (by omega : (a : ℕ) + 1 < 5) (by omega : (b : ℕ) + 1 < 5) hab
    exact Fin.ext (by omega)
  have hQ : Q = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hinj (fun i => ?_) ?_
    · rw [hQev]
      fin_cases i
      · simpa using sub_eq_zero.mpr h1
      · simpa using sub_eq_zero.mpr h2
      · simpa using sub_eq_zero.mpr h3
      · simpa using sub_eq_zero.mpr h4
    · have hb : (β.map (algebraMap ℚ ℂ)).natDegree < 4 := by
        rw [natDegree_map]; exact latPoly_natDegree m
      have ha : (C c * α.map (algebraMap ℚ ℂ)).natDegree < 4 := by
        refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
        rw [natDegree_map]; exact latPoly_natDegree n
      simp only [Fintype.card_fin]
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hb ha)
  -- compare coefficients at an index with `nₑ ≠ 0`
  obtain ⟨e, he⟩ : ∃ e : Fin 4, n e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hα
    simp [α, latPoly, hcon]
  have hcoef := congrArg (fun q : ℂ[X] => q.coeff (e : ℕ)) hQ
  simp only [Q, coeff_sub, coeff_C_mul, coeff_map, coeff_zero, β, α, latPoly_coeff] at hcoef
  refine ⟨(m e : ℝ) / (n e : ℝ), ?_⟩
  have hne : (n e : ℂ) ≠ 0 := by exact_mod_cast he
  rw [map_intCast, map_intCast] at hcoef
  push_cast
  field_simp
  linear_combination -hcoef

/-- A proper nonzero complex subspace of `ℂ²` is a line through any of its nonzero points. -/
lemma mem_line_of_ne_top {t : Submodule ℂ (Fin 2 → ℂ)} (ht : t ≠ ⊤) {a b : Fin 2 → ℂ} (ha : a ∈ t)
    (hb : b ∈ t) (ha0 : a ≠ 0) : ∃ c : ℂ, b = c • a := by
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent ℂ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    by_cases hu : u = 0
    · subst hu
      simp only [zero_smul, add_zero] at hsu
      exact ⟨(smul_eq_zero.mp hsu).resolve_right ha0, rfl⟩
    · exfalso
      apply hcon (-(s / u))
      have : u • b = -(s • a) := by linear_combination (exp := 1) hsu
      calc b = u⁻¹ • (u • b) := by rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
        _ = -(s / u) • a := by rw [this, smul_neg, smul_smul, neg_smul]; congr 1; field_simp
  have hspan : Submodule.span ℂ (Set.range ![a, b]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  apply ht
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ha
  · exact hb

/-- **`A` is simple** (for the lattice `latt`). -/
theorem simple_latt (t : Submodule ℂ (Fin 2 → ℂ)) (ht : LSG.MEB.IsRatSub latt t) : t = ⊥ ∨ t = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  unfold LSG.MEB.IsRatSub at ht
  set S : Set (Fin 2 → ℂ) := {z | z ∈ t ∧ z ∈ latt}
  -- a nonzero lattice point of `t`
  obtain ⟨a, haS, ha0⟩ : ∃ a ∈ S, a ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    rw [eq_bot_iff]
    intro u hu
    have hu' : u ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin 2 → ℂ)) := hu
    rw [ht] at hu'
    have : Submodule.span ℝ S ≤ ⊥ := by
      rw [Submodule.span_le]; intro z hz; simp [h z hz]
    exact (Submodule.mem_bot ℂ).mpr ((Submodule.mem_bot ℝ).mp (this hu'))
  -- every lattice point of `t` is a real multiple of `a`
  have hreal : S ⊆ (Submodule.span ℝ {a} : Set (Fin 2 → ℂ)) := by
    intro b hbS
    obtain ⟨c, hc⟩ := mem_line_of_ne_top htop haS.1 hbS.1 ha0
    obtain ⟨r, rfl⟩ := real_of_latt haS.2 hbS.2 ha0 hc
    rw [hc]
    exact Submodule.mem_span_singleton.mpr ⟨r, by rw [Complex.coe_smul]⟩
  have hIa : Complex.I • a ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin 2 → ℂ)) := t.smul_mem _ haS.1
  rw [ht] at hIa
  have := (Submodule.span_le.mpr hreal) hIa
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  rw [← Complex.coe_smul] at hr
  have h0 : ((r : ℂ) - Complex.I) • a = 0 := by rw [sub_smul, hr, sub_self]
  have := (smul_eq_zero.mp h0).resolve_right ha0
  have him := congrArg Complex.im this
  simp at him

/-- **`A` is simple**, for the period group `kerE G` (the `simple` field). -/
theorem simple_kerE {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂}
    {hx : p.1 ≠ p.2} (G : GermRad A hp hx) (t : Submodule ℂ (Fin 2 → ℂ))
    (ht : LSG.MEB.IsRatSub (kerE G) t) : t = ⊥ ∨ t = ⊤ :=
  simple_latt t ((LSG.W88.isRatSub_iff_of_nsmul (LSG.W88.latt_le_kerE G) (LSG.W88.isNsmulIn_latt_kerE G) t).mpr ht)

end LSG.JacBlock
