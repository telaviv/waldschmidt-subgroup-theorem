# Referee report: the statement `LSG.W88.Theorem41Abelian`

Date: 2026-10-31.

**Scope.** Does the **statement** in `LSG/W88/Statement.lean` (lines 150–163) say what it claims, and is it
non-vacuous? The claim is W88 Thm 4.1 (pp. 385–386), under (NR), for G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m. I did
not check the proof; Lean did.

**Sources compared:**
* W88 page images:
  * `w88-06.png`: p. 385, the statement.
  * `w88-07.png`: p. 386, the definitions of δ…τ and the inequality.
  * `w88-08.png`, `w88-10.png`, `w88-11.png`: §5d and Cor. 5.3.
* `paper.tex`, Theorem `thm:W88`.
* `FALSITY_HUNT.md` §1.1.

## Verdict: **CORRECT**

* **No FATAL or MAJOR issues.**
* **Equivalent to W88 Thm 4.1** for this G, apart from two documented restrictions: hypothesis (NR) and G₂ = ∏ E_j.
* **Non-vacuous.** Two independent classical consequences were derived from it in Lean, with standard axioms only
  (§6): Gelfond–Schneider and Schneider's theorem on elliptic periods.
* **Four MINOR remarks**, all about documentation or scope.

## 1. `Lam` and `Per` (lines 70–94): correct

* **`Lam` (l. 71–73)** is exactly `exp_G⁻¹ G(ℚ̄)`:
  * the G_a coordinates satisfy `a ∈ ℚ̄^{d₀}`;
  * each `e^{b_i}` is algebraic (nonzero automatically);
  * for each j, either `z_j ∈ Λ_j` (the point O) or `℘_j(z_j) ∈ ℚ̄`. In the second case
    `℘′_j(z_j)² = 4℘³ − g₂℘ − g₃ ∈ ℚ̄`, by Mathlib's `derivWeierstrassP_sq` with `g₂ = 60G₄` and `g₃ = 140G₆`.
  * The lattice disjunct is redundant, because Mathlib's junk value is `℘(l) = 0`. This is harmless.
* **`Per` (l. 76–78)** is `0 × 2πiℤ^{d₁} × Λ₁ × ⋯ × Λ_m = ker exp_G`. Correct.
* **The ℚ̄-structure on T_G** uses the standard coordinates (`AlgVec` on all three blocks, l. 67–68). This is right:
  * for G_m the invariant vector field is t∂_t;
  * for E_j the invariant differential is dx/y = dz, which is defined over ℚ̄ because g₂ and g₃ are algebraic.

## 2. The subgroup family `SubgroupData` (lines 96–122): exactly the right family

* **`torusLie U` (l. 97–98)** is `U^⊥`. This is the Lie algebra of the connected subtorus cut out by the characters in
  U ∩ ℤ^{d₁}. Since `dim_ℂ U^⊥ = d₁ − dim_ℚ U`, the definition `δ₁ = dim U` (l. 134) is correct.
* **`IsAbelianTangent` (l. 109–111)** is correct in both directions:
  * t ∩ Λ spans t over ℝ ⇔ t/(t ∩ Λ) is a compact complex subtorus of ℂ^m/Λ;
  * by Chow, such a subtorus is an abelian subvariety;
  * abelian subvarieties of a product of curves over ℚ̄ are defined over ℚ̄.
* **`h0_rat` (l. 121)** is correct: H₀ is defined over ℚ̄ ⇔ h₀ is spanned by algebraic vectors.
* **Products are justified.** Every connected algebraic subgroup of G_a^{d₀} × G_m^{d₁} × A (A an abelian variety)
  has the form H₀ × T × B.
  * Apply Goursat to the projections. A non-product subgroup would give an isogeny between a quotient of one factor
    type and a quotient of another (unipotent / torus / abelian).
  * In characteristic 0, all the relevant Hom groups vanish: Hom(G_a, G_m), Hom(G_m, G_a), Hom(A, G_a), Hom(G_a, A),
    Hom(A, G_m) and Hom(G_m, A).
  * So the Lean family equals W88's family for this G. The Lean ∃ is neither weaker nor stronger than W88's.
* **The codimensions match p. 386.** For a product G′, π₀(G′) = H₀ and π₁(G′) = T_U. Hence:
  * δ₀ = d₀ − dim h₀ (l. 132);
  * δ₁ = dim U;
  * δ₂ = δ − δ₀ − δ₁ = m − dim t (l. 136).
* **`Proper` (l. 141)** is correct: δ = 0 ⇔ (h₀ = ⊤, U = 0 so that U^⊥ = ⊤, and t = ⊤) ⇔ G′ = G.
* **G′ = 0 is allowed**, as the paper says ("($G'=0$ is allowed.)"). Take h₀ = ⊥, U = ⊤, t = ⊥. Both
  `RationalOverQbar ⊥` and `IsAbelianTangent ⊥` hold, and the derivations in §6 use exactly this case.

## 3. λ, δ, τ, κ: correct

* **κ** = `rk (Y ⊓ Per Ls)` = rk_ℤ(Y ∩ ker exp). This matches p. 385.
* **λ** = `rk Y − rk (Y ⊓ (T_{G′} ⊔ Per))` (l. 160).
  * The AddSubgroup sup is T_{G′} + Ω, which equals exp⁻¹(G′) because G′ is connected.
  * Y → Γ/(Γ ∩ G′) is onto, with kernel Y ∩ exp⁻¹(G′). So λ = rk Γ/(Γ ∩ G′), as on p. 386.
* **τ** = `finrank W − finrank (W ⊓ T_{G′})` = dim W/(W ∩ T_{G′}). This matches p. 386.
* **The inequality** uses d = d₀ + d₁ + m, d₂ = m and N = `finrank ℂ V`. It reads
  (λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ), verbatim p. 386. As in W88, there is no δ₀ on the left and no d₀ on
  the right.
* **`rk`** is computed as `finrank ℚ (span ℚ Y)`.
  * This equals rk_ℤ for subgroups of a ℚ-vector space.
  * Y is finitely generated, so every span involved is finite-dimensional. No junk `finrank = 0` can occur.

## 4. Natural-number subtraction and casts: all safe

I checked how Lean actually elaborates the statement (scratch file `Casts.lean`). I used `#print` with
`pp.coercions` and `pp.numericTypes`, and an `Iff.rfl` against a fully explicit version. The elaborated statement is:

```
↑(rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) + H.δ1 + 2 * H.δ2) * (↑(d0 + d1 + m) - ↑(finrank ℂ ↥V)) ≤
  (↑H.δ - ↑(finrank ℂ ↥W - finrank ℂ ↥(W ⊓ H.tan))) * (↑(d1 + 2 * m) - ↑(rk (Y ⊓ Per Ls)))
```

* **The ℤ-subtractions are the intended ones.** `d − N`, `δ − τ` and `d₁ + 2m − κ` are integer subtractions. None of
  them could truncate anyway:
  * N < d is a hypothesis;
  * τ < δ is a conjunct of the conclusion;
  * κ ≤ rk(Ω ∩ V) ≤ d₁ + 2m.
* **Every ℕ-subtraction is exact** (subtrahend ≤ minuend):
  * `rk Y − rk(Y ⊓ …)` (l. 160): span is monotone, and span Y is finite-dimensional;
  * `finrank W − finrank (W ⊓ tan)` (l. 159, 162);
  * `d0 − finrank h0` (l. 132);
  * `m − finrank t` (l. 136).
* **The strict inequality δ > τ** (l. 159) is present.
* **Properness** (l. 158) is present. It is redundant given δ > τ ≥ 0, but harmless.

## 5. Hypotheses consistent; conclusion not trivially satisfiable

* **The hypotheses (l. 152–157) match p. 385:** g₂ and g₃ algebraic; N < d; W ≤ V and ℚ̄-rational; Y finitely
  generated; Y ⊆ V ∩ Λ(G).
  * N < d forces d ≥ 1, which is W88's assumption d ≥ 1.
  * (NR) (l. 157) is `d₁ + 2d₀ + κ ≤ 2N`. This is the same condition as in `paper.tex`, "2N ≥ d₁ + 2d₀ + κ".
* **The requested instance is consistent.** Take d₀ = 0, d₁ = 2, m = 1, V a hyperplane, W = 0, and Y generated by three
  vectors of Λ(G) ∩ V. Then (NR) reads 2 + κ ≤ 4, so it holds whenever κ ≤ 2.
  * If V = {z₃ = 0}, then G′ = G_m² × 0 satisfies the conclusion: δ = δ₂ = 1, τ = 0, λ = 0, and 2 ≤ 4 − κ. This is
    the expected answer, since V contains T_{G′}.
  * If V contains no T_{G′}, the conclusion is a genuine transcendence statement.
* **The conclusion is not trivially satisfiable:**
  * G′ = G is excluded by `Proper`.
  * G′ = 0 works only when (4.2) fails, that is, when (ℓ − κ + d₁ + 2m)(d − N) ≤ (d − t)(d₁ + 2m − κ).
  * No single subgroup works for all data. In both instances of §6, every admissible H violates the conclusion, so the
    hypotheses yield `False`.

## 6. Sanity derivations (Lean, compiled, standard axioms)

* **Scratch file:**
  `GS.lean`.
  Its full text is in the Appendix.
* **How it was checked:** `lake env lean`, against the built `LSG.W88.Main`.
* **Output:**

```
'ScratchReview.gelfondSchneider' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScratchReview.period_transcendental'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 6.1 Gelfond–Schneider (`gelfondSchneider_of (hT : Theorem41Abelian)`)

**Claim.** If x ≠ 0, e^x ∈ ℚ̄ and b ∈ ℚ̄ \ ℚ, then e^{bx} is transcendental.

**Instance.** G = G_m², so d₀ = m = 0 and d₁ = 2. Take V = W = ℂ(1, b) and Y = ℤ(x, bx). Then κ = 0, and (NR) reads
2 ≤ 2.

**Case analysis on H.**
1. U ≠ 0 by properness, and then (1, b) ∉ U^⊥ because b ∉ ℚ. So τ = 1.
2. δ > τ then forces δ₁ = 2. Hence U = ⊤ and T_{G′} = 0.
3. So λ = 1, and the inequality reads 3·1 ≤ 1·2. This is false.

**What it exercises:** `Lam` (G_m part), `Per` (the 2πiℤ part, through κ = 0), `torusLie`, τ, λ, and every cast.

### 6.2 Schneider's period theorem (`period_of`)

**Claim.** If g₂, g₃ ∈ ℚ̄, then every nonzero ω ∈ Λ is transcendental.

**Instance.** G = G_a × E, so d₀ = m = 1 and d₁ = 0. Take V = W = ℂ(1, 1) and Y = ℤ(ω, ω). Then κ = 0, and (NR)
reads 2 ≤ 2.

**Case analysis on H.**
1. If (1, 1) ∈ T_{G′}, then h₀ = t = ⊤, so δ = 0, which contradicts properness. Hence τ = 1.
2. δ > τ then forces δ = 2, so h₀ = t = 0.
3. So λ = 1, and the inequality reads (1 + 2·1)·1 ≤ 1·2. This is false.

**What it exercises:** `Lam` (the G_a part and the lattice disjunct), the weight 2δ₂, and δ₀. Compare
`LSG.Schneider.period_transcendental`.

### 6.3 Remark: Hermite–Lindemann is not a direct corollary

* The classical W ≠ 0 encoding of Hermite–Lindemann uses G = G_a × G_m, V = W = ℂ(1, 1) and N = 1. It violates (NR),
  since 1 + 2 > 2.
* Padding with extra G_m factors restores (NR), but then the conclusion is trivially satisfied by a subtorus. I checked
  this on paper for G_a × G_m² with V = {(x, x, y)}.
* So HL does not follow directly from the statement as given. This is a consequence of (NR), not a mis-statement; see
  M2.

## Issues

* **MINOR M1 (l. 35, docstring).** The phrase "with hypothesis (NR) of `W_UPGRADE.md`" points to a file that is not in
  `lean_lsg/`. The file lives at `schanuel/five_exp/pilot_epi2_mix/W_UPGRADE.md`. For a standalone repo, drop or
  qualify the reference; (NR) is already stated inline at l. 38.
* **MINOR M2 (l. 157, scope).** (NR) is a genuine weakening of W88 Thm 4.1.
  * It is documented in the docstring and in `INTERFACE.md`.
  * External citations should therefore say "W88 Thm 4.1 under (NR) for G_a^{d₀} × G_m^{d₁} × ∏E_j", never just
    "W88 Thm 4.1".
  * The weakening bites mainly when d₀ is large relative to N. For example, it excludes the natural Hermite–Lindemann
    setup (§6.3).
  * The applications listed in `paper.tex` §2 all satisfy (NR).
* **MINOR M3 (l. 141, 158).** `H.Proper` is implied by the conjunct `τ < δ` (l. 159). It is redundant but harmless,
  and it mirrors W88's wording.
* **MINOR M4 (l. 73).** The disjunct `p.2.2 j ∈ (Ls j).lattice` is redundant, because Mathlib sets `℘(l) = 0` at
  lattice points. It is harmless, and keeping it is clearer. Nothing in the statement depends on the junk value.

## Companion statement `LSG.ME.MultEstAb` (`LSG/ME/MultEstStmt.lean` l. 126–139): checked at a glance

* **Not vacuous.**
  * The hypotheses are satisfiable, for example with d₀ ≥ 1, S = {0} and P = x₁^{nT+1} with D₀ large.
  * The conclusion needs a proper O. Properness is `tan ≠ ⊤`, and through the `lie` field (l. 49) it forces
    `grp ≠ G`. So there is no "O = G" escape.
  * The inequality T^c·|F|·D₀^{t₀}D₁^{t₁}D₂^{t₂} ≤ C·D₀^{d₀}D₁^{d₁}D₂^m, with |F| unbounded, is a real constraint.
* **The ℕ-subtractions** `d₁ − finrank U` and `finrank W − finrank (W ⊓ tan)` are exact.
* **The constant C** depends only on (d₀, d₁, m, Ls). This matches Philippon, where the constant depends on G and its
  embedding.
* **The monomial lower bound** D₀^{t₀}D₁^{t₁}D₂^{t₂} for H(G′; D) is a valid weakening, since every multidegree
  coefficient of a product subgroup is ≥ 1.
* **`ObstrData` omits ℚ̄-rationality of h₀.** This is the right choice for a zero estimate over ℂ. The bridge
  `toSubgroupData` adds rationality explicitly.
* No issues found at this level of reading.

## Appendix: `GS.lean` (sanity derivations)

```lean
import LSG.W88.Main
open Module LSG.W88 Complex

namespace ScratchReview

noncomputable def u0 (b : ℂ) : Tan 0 2 0 := ((0 : Fin 0 → ℂ), ![1, b], (0 : Fin 0 → ℂ))

theorem u0_ne (b : ℂ) : u0 b ≠ 0 := by
  intro h
  have := congrArg (fun p : Tan 0 2 0 => p.2.1 0) h
  simp [u0] at this

theorem alg_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (k : ℤ) : IsAlgebraic ℚ (z ^ k) := by
  have : z ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hz
  exact mem_algebraicClosure_iff.mp (zpow_mem this k)

theorem rk_bot {E : Type*} [AddCommGroup E] [Module ℚ E] : rk (⊥ : AddSubgroup E) = 0 := by
  simp [rk, AddSubgroup.coe_bot]

theorem rk_zmultiples {E : Type*} [AddCommGroup E] [Module ℚ E] {u : E} (hu : u ≠ 0) :
    rk (AddSubgroup.zmultiples u) = 1 := by
  unfold rk
  have : Submodule.span ℚ (AddSubgroup.zmultiples u : Set E) = ℚ ∙ u := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe]
      rw [show (k • u : E) = (k : ℚ) • u by rw [Int.cast_smul_eq_zsmul]]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span (AddSubgroup.mem_zmultiples u)
  rw [this, finrank_span_singleton hu]

/-- **Gelfond–Schneider from `Theorem41Abelian`** (G = G_m², d₀ = m = 0, V = W = ℂ(1,b),
Y = ℤ·(x, bx)): if `x ≠ 0`, `e^x` algebraic, `b` algebraic irrational, then `e^{bx}` is
transcendental. -/
theorem gelfondSchneider_of (hT : Theorem41Abelian) (x b : ℂ) (hx : x ≠ 0)
    (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ q)
    (ha : IsAlgebraic ℚ (exp x)) (hc : IsAlgebraic ℚ (exp (b * x))) : False := by
  let Ls : Fin 0 → PeriodPair := Fin.elim0
  let V : Submodule ℂ (Tan 0 2 0) := ℂ ∙ u0 b
  let u : Tan 0 2 0 := x • u0 b
  let Y : AddSubgroup (Tan 0 2 0) := AddSubgroup.zmultiples u
  have hu0 := u0_ne b
  have hu : u ≠ 0 := smul_ne_zero hx hu0
  have hVdim : finrank ℂ V = 1 := finrank_span_singleton hu0
  have huV : u ∈ V := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- components of k • u
  have hcomp : ∀ k : ℤ, ∀ i, (k • u).2.1 i = (k : ℂ) * x * ![1, b] i := by
    intro k i
    fin_cases i <;> simp [u, u0, zsmul_eq_mul] <;> ring
  -- V is ℚ̄-rational
  have hrat : RationalOverQbarTan V := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, ?_, ?_, ?_⟩
      · exact fun i => i.elim0
      · intro i; fin_cases i
        · simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
        · simpa [u0] using hb
      · exact fun i => i.elim0
    · exact Submodule.span_le.mpr fun w hw => hw.1
  -- Y ∩ Ω = 0
  have hYPer : Y ⊓ Per Ls = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyP⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hyY
    obtain ⟨-, hP1, -⟩ := hyP
    by_cases hk : k = 0
    · simp [hk]
    exfalso
    obtain ⟨n0, hn0⟩ := hP1 0
    obtain ⟨n1, hn1⟩ := hP1 1
    rw [hcomp] at hn0 hn1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hn0 hn1
    have hkx : (k : ℂ) * x ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hx
    have hn0' : (n0 : ℂ) ≠ 0 := by
      intro h; apply hkx; rw [hn0, h]; simp
    have : (k : ℂ) * x * b * (n0 : ℂ) = (k : ℂ) * x * (n1 : ℂ) := by
      calc (k : ℂ) * x * b * n0 = (k * x * b) * n0 := by ring
        _ = (2 * Real.pi * I * n1) * n0 := by rw [hn1]
        _ = (2 * Real.pi * I * n0) * n1 := by ring
        _ = (k : ℂ) * x * n1 := by rw [hn0]
    have hbn : b * n0 = n1 := mul_left_cancel₀ hkx (by linear_combination this)
    apply hbq ((n1 : ℚ) / n0)
    push_cast
    rw [eq_div_iff hn0']; exact hbn
  have hrkYPer : rk (Y ⊓ Per Ls) = 0 := by rw [hYPer]; exact rk_bot
  have hrkY : rk Y = 1 := rk_zmultiples hu
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 0 2 0 Ls (fun j => j.elim0) V V Y
    (by rw [hVdim]; norm_num) le_rfl hrat
    ((AddSubgroup.fg_iff _).mpr ⟨{u}, (AddSubgroup.zmultiples_eq_closure u).symm,
      Set.finite_singleton u⟩)
    (by
      intro y hy
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      refine ⟨zsmul_mem huV k, fun i => i.elim0, fun i => ?_, fun j => j.elim0⟩
      rw [hcomp]
      fin_cases i
      · simpa [exp_int_mul] using alg_zpow ha k
      · have := alg_zpow hc k
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [show (k : ℂ) * x * b = k * (b * x) by ring, exp_int_mul]; exact this)
    (by rw [hrkYPer, hVdim])
  -- structure of H for d₀ = m = 0
  have hδ0 : H.δ0 = 0 := by simp [SubgroupData.δ0]
  have hδ2 : H.δ2 = 0 := by simp [SubgroupData.δ2]
  have hδ : H.δ = H.δ1 := by simp [SubgroupData.δ, hδ0, hδ2]
  have hU : H.U ≠ ⊥ := by
    intro h
    apply hprop
    rw [hδ, SubgroupData.δ1, h, finrank_bot]
  -- u0 b ∉ T_{G'}
  have hnot : u0 b ∉ H.tan := by
    intro hmem
    have h2 : ![1, b] ∈ torusLie H.U := hmem.2.1
    obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have he := h2 φ hφU
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at he
    by_cases h1 : φ 1 = 0
    · apply hφ0
      have h0 : φ 0 = 0 := by
        rw [h1] at he; push_cast at he; simpa using he
      funext i; fin_cases i <;> simp [h0, h1]
    · apply hbq (-(φ 0) / φ 1)
      have h1' : (φ 1 : ℂ) ≠ 0 := by exact_mod_cast h1
      push_cast
      field_simp
      linear_combination he
  have hWtan : V ⊓ H.tan = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvT⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
    by_cases hc0 : c = 0
    · simp [hc0]
    · exact absurd (by simpa [hc0] using H.tan.smul_mem c⁻¹ hvT) hnot
  have hτ1 : finrank ℂ V - finrank ℂ ↥(V ⊓ H.tan) = 1 := by
    rw [hWtan, finrank_bot, hVdim]
  -- so δ₁ = 2, U = ⊤
  have hδ1le : H.δ1 ≤ 2 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupData.δ1] using this
  have hδ1 : H.δ1 = 2 := by rw [hτ1, hδ] at hτ; omega
  have hUtop : H.U = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa [SubgroupData.δ1] using hδ1)
  have htan : H.tan = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨-, hp2, -⟩ := hp
    have hz : p.2.1 = 0 := by
      funext i
      have := hp2 (Pi.single i 1) (by rw [hUtop]; trivial)
      fin_cases i <;> simpa [Fin.sum_univ_two, Pi.single_apply] using this
    have h1 : p.1 = 0 := Subsingleton.elim _ _
    have h3 : p.2.2 = 0 := Subsingleton.elim _ _
    exact (Submodule.mem_bot ℂ).mpr (Prod.ext h1 (Prod.ext hz h3))
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) = 0 := by
    rw [htan, Submodule.bot_toAddSubgroup, bot_sup_eq]; exact hrkYPer
  rw [hrkY, hlam, hδ1, hδ2, hτ1, hδ, hδ1, hrkYPer, hVdim] at hineq
  norm_num at hineq

/-- Instantiated with the proved theorem. -/
theorem gelfondSchneider (x b : ℂ) (hx : x ≠ 0)
    (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ q)
    (ha : IsAlgebraic ℚ (exp x)) : Transcendental ℚ (exp (b * x)) :=
  fun hc => gelfondSchneider_of theorem41Abelian x b hx hb hbq ha hc


noncomputable def e0 : Tan 1 0 1 := (![1], (0 : Fin 0 → ℂ), ![1])

theorem e0_ne : e0 ≠ 0 := by
  intro h
  have := congrArg (fun p : Tan 1 0 1 => p.1 0) h
  simp [e0] at this

/-- **Schneider's period theorem from `Theorem41Abelian`** (G = G_a × E, d₀ = m = 1, d₁ = 0,
V = W = ℂ(1,1), Y = ℤ·(ω, ω)). -/
theorem period_of (hT : Theorem41Abelian) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (ω : ℂ) (hω : ω ∈ L.lattice) (hω0 : ω ≠ 0)
    (halg : IsAlgebraic ℚ ω) : False := by
  let Ls : Fin 1 → PeriodPair := fun _ => L
  let V : Submodule ℂ (Tan 1 0 1) := ℂ ∙ e0
  let u : Tan 1 0 1 := ω • e0
  let Y : AddSubgroup (Tan 1 0 1) := AddSubgroup.zmultiples u
  have hu : u ≠ 0 := smul_ne_zero hω0 e0_ne
  have hVdim : finrank ℂ V = 1 := finrank_span_singleton e0_ne
  have huV : u ∈ V := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hc1 : ∀ k : ℤ, (k • u).1 0 = (k : ℂ) * ω := by intro k; simp [u, e0, zsmul_eq_mul]
  have hc3 : ∀ k : ℤ, (k • u).2.2 0 = (k : ℂ) * ω := by intro k; simp [u, e0, zsmul_eq_mul]
  have hrat : RationalOverQbarTan V := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, ?_, ?_, ?_⟩
      · intro i; fin_cases i; simpa [e0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · exact fun i => i.elim0
      · intro i; fin_cases i; simpa [e0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hYPer : Y ⊓ Per Ls = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyP⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hyY
    obtain ⟨h1, -, -⟩ := hyP
    have := congrFun h1 0
    rw [hc1] at this
    have hk : (k : ℂ) = 0 := by simpa [hω0] using this
    have hk' : k = 0 := by exact_mod_cast hk
    simp [hk']
  have hrkYPer : rk (Y ⊓ Per Ls) = 0 := by rw [hYPer]; exact rk_bot
  have hrkY : rk Y = 1 := rk_zmultiples hu
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 1 0 1 Ls (fun _ => ⟨hg₂, hg₃⟩) V V Y
    (by rw [hVdim]; norm_num) le_rfl hrat
    ((AddSubgroup.fg_iff _).mpr ⟨{u}, (AddSubgroup.zmultiples_eq_closure u).symm,
      Set.finite_singleton u⟩)
    (by
      intro y hy
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      refine ⟨zsmul_mem huV k, fun i => ?_, fun i => i.elim0, fun j => Or.inl ?_⟩
      · fin_cases i
        show IsAlgebraic ℚ ((k • u).1 0)
        rw [hc1]
        exact mem_algebraicClosure_iff.mp (mul_mem
          (mem_algebraicClosure_iff.mpr (isAlgebraic_intCast k)) (mem_algebraicClosure_iff.mpr halg))
      · fin_cases j
        show (k • u).2.2 0 ∈ L.lattice
        rw [hc3]
        rw [show (k : ℂ) * ω = k • ω by simp [zsmul_eq_mul]]
        exact zsmul_mem hω k)
    (by rw [hrkYPer, hVdim])
  have hδ1 : H.δ1 = 0 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupData.δ1] using this
  have hh0le : finrank ℂ H.h0 ≤ 1 := by simpa using Submodule.finrank_le H.h0
  have htle : finrank ℂ H.t ≤ 1 := by simpa using Submodule.finrank_le H.t
  have hnot : e0 ∉ H.tan := by
    intro hmem
    obtain ⟨hh, -, ht⟩ := hmem
    have a1 : H.h0 ≠ ⊥ := fun h => by
      rw [h] at hh
      have := congrFun ((Submodule.mem_bot ℂ).mp hh) 0; simp [e0] at this
    have a2 : H.t ≠ ⊥ := fun h => by
      rw [h] at ht
      have := congrFun ((Submodule.mem_bot ℂ).mp ht) 0; simp [e0] at this
    have b1 : 0 < finrank ℂ H.h0 := Nat.pos_of_ne_zero fun h => a1 (Submodule.finrank_eq_zero.mp h)
    have b2 : 0 < finrank ℂ H.t := Nat.pos_of_ne_zero fun h => a2 (Submodule.finrank_eq_zero.mp h)
    apply hprop
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1]
    omega
  have hWtan : V ⊓ H.tan = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvT⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
    by_cases hc0 : c = 0
    · simp [hc0]
    · exact absurd (by simpa [hc0] using H.tan.smul_mem c⁻¹ hvT) hnot
  have hτ1 : finrank ℂ V - finrank ℂ ↥(V ⊓ H.tan) = 1 := by
    rw [hWtan, finrank_bot, hVdim]
  rw [hτ1] at hτ
  have hh0 : finrank ℂ H.h0 = 0 := by
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1] at hτ; omega
  have ht0 : finrank ℂ H.t = 0 := by
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1] at hτ; omega
  have hδ0 : H.δ0 = 1 := by simp [SubgroupData.δ0, hh0]
  have hδ2 : H.δ2 = 1 := by simp [SubgroupData.δ2, ht0]
  have hδ : H.δ = 2 := by simp [SubgroupData.δ, hδ0, hδ1, hδ2]
  have htan : H.tan = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨hp1, -, hp3⟩ := hp
    rw [Submodule.finrank_eq_zero.mp hh0] at hp1
    rw [Submodule.finrank_eq_zero.mp ht0] at hp3
    replace hp1 := (Submodule.mem_bot ℂ).mp hp1
    replace hp3 := (Submodule.mem_bot ℂ).mp hp3
    exact (Submodule.mem_bot ℂ).mpr (Prod.ext hp1 (Prod.ext (Subsingleton.elim _ _) hp3))
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) = 0 := by
    rw [htan, Submodule.bot_toAddSubgroup, bot_sup_eq]; exact hrkYPer
  rw [hrkY, hlam, hδ1, hδ2, hτ1, hδ, hrkYPer, hVdim] at hineq
  norm_num at hineq

theorem period_transcendental' (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (ω : ℂ) (hω : ω ∈ L.lattice) (hω0 : ω ≠ 0) :
    Transcendental ℚ ω :=
  fun h => period_of theorem41Abelian L hg₂ hg₃ ω hω hω0 h

end ScratchReview

#print axioms ScratchReview.gelfondSchneider
#print axioms ScratchReview.period_transcendental'
```
