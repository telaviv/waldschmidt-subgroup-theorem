# Stage A5, part 1: W83 Prop. 2.1 for general lattice blocks (Tier 3), plan and stop report

Status 2026-10-31: **stopped before coding.** The Tier-3 interpolation step cannot be done with the one-variable
machinery of Tiers 1–2. It needs a genuinely several-variable Schwarz lemma for non-Cartesian point sets: W83 Lemma 2.3
(Masser's Theorem A), or the Bombieri–Lang / Lelong route. Mathlib v4.35 and StrongSix contain neither, and I do not
have a proof of the norming lemma (L2 below) that I can formalise. Estimate: ≈ 5–8.5k lines plus research risk, against
the ~3k budget. No `.lean` files were written.

## 0. Target statement (unchanged; the interface for callers)

`prop21Gen n κ a e P I …` is `prop21Lat` with `perVec α β (P i)` replaced by `ω_i = Σ_k P i k • e k`, where
`e : Fin (2n) → (Fin n → ℂ)` is an ℝ-basis of ℂⁿ, `P : Fin κ → Fin (2n) → ℤ`, and `I : Fin κ → Fin (2n)` injective
with `det (P i (I t)) ≠ 0`. All other hypotheses (growth, `b r² ≤ a U`, (QP), `U ≥ r² log(R/r)`,
`c₂ U^{n+1} ≤ L Δ r^κ log(R/r)^n`) stay as they are.

The mixed form W88 wants for `G_a × G_m × ∏E × A^r` with `V` a hyperplane: keep every coordinate form except one.
Each `A`-block then stays complete, and the periods map into `∏(0 | 2πiℤ | Λ_E) × ∏ Λ_A ⊂ ∏ℂ × ∏ℂ^g`. This is
`prop21Lat` on the product part plus Tier 3 on each g-block, and interpolation goes one block at a time
(`grid_interp2` with blocks in place of coordinates). Everything except the per-block interpolation lemma carries over
from `Reps2`/`Prop21Lat`: the grid `(1/K)·{Σ a_k e_k : |a_k| ≤ A}`, the class count via the minor (`lat_decomp` with
index type `Fin (2n)`), Siegel, and the multiplier transfer. That routine part is ≈ 0.8–1k lines.

## 1. The key estimate the proof needs (per block, g = dim)

Write `Λ = ⊕ ℤe_k ⊂ ℂ^g` and `G = G_{A,K} = {(1/K) Σ a_k e_k : |a_k| ≤ A}`, so `#G = (2A+1)^{2g}`. In Tier 2 the
parameters are `T := U/ℓ` (`ℓ = log(R/r)`), `A ≍ √T`, and `A/K ≍ r`. The class count is then
`#G / r^κ ≍ T^g / r^κ`, which is exactly what `c₂U^{g+1} ≤ LΔ r^κ ℓ^g` pays for.

**Lemma L (needed).** Take `F` entire on ℂ^g with `|F| ≤ ε` on `G` and `|F| ≤ M` on `B_R`. Then, on `B_r`,
`|F| ≤ C^{A²} ε + C^{A²} (C r/R)^{c A²} M`, with `c, C > 0` depending only on `e`.

What matters is the exponent `c A² ≍ T`: the final step needs `(r/R)^{cA²} e^U ≤ e^{-2U}`, that is, `cA² ≥ 3T`.

## 2. Why the per-coordinate route fails, and the cheap variants checked

**Obstruction.** Suppose `A` is simple, or more generally no complex line `L` has `L ∩ Λ` of rank 2. Then every
complex line meets each coset `x + (1/K)Λ` in a coset of a group of rank ≤ 1. So `#(L ∩ G) ≤ 2A+1`, and these points
are collinear along a real segment.

* Any one-variable step (Lagrange plus `norm_le_of_zeros`) on such a line gains at most `(2r/(R−r))^{2A+1}`, which is
  about `e^{-ℓ√T}`. We need `e^{-3U} = e^{-3Tℓ}`.
* Multiplicities do not rescue this. With Hermite data of order `m` at the nodes, the step needs `(2A+1)m ≳ T`, and
  the jet count makes the condition count `≍ A^g T^g / r^{2g}`. The loss is `r^g` even at the best choice `A ≍ r`.
* So every scheme made of one-variable steps along complex lines with exact lattice nodes falls short. This is
  `grid_interp`, `grid_interp2`, and any block analogue.

Variants examined, all [Proved] negative or useless:

* **(a) ℂ-linear change of coordinates.** Tier 2 needs `n` forms `λ_j` with `λ_j(Λ)` discrete. For a full lattice
  this forces `ker λ_j ∩ Λ` to be a full lattice of `ker λ_j`, so `ℂ^g/Λ` is isogenous to a product of elliptic curves.
  This is impossible for simple `A`. An ℝ-linear map to a product lattice is not holomorphic.
* **(b) Cartesian product in `t`-space ℂ^{2g}.** This is the Lang/Waldschmidt trick: `Φ(t) = F(Σ t_k e_k)`, with nodes
  the integer box, and it is Tier 1 in dimension 2g. It is correct and cheap: a corollary of `prop21B`/`Prop21Lin` in
  dimension 2n, ≈ 300 lines. But it needs `A ≍ T` per real direction, so its hypothesis becomes
  `c₂ U^{2n+1} ≤ L Δ r^κ ℓ^{2n}`. That loses `T^n` and is almost certainly fatal for W88 §7's parameter balance. Not
  built.
* **(c) Product of generalized progressions.** Take `Z_j = λ_j(box)`, where `λ_j` are forms dual to a lattice
  ℂ-basis, so `λ_j(Λ)` has rank `g+1`. The product set does carry the full saving `r^{2g}`: the diagonal `τb`-shift
  gives `Y^g` and the `ℤ^g`-shift gives `X^g`. But `#Z_j ≥ 3T` together with the class budget forces `T ≳ r^{g+1}`,
  that is `U ≳ r³ℓ` for g = 2, against W83's `U ≥ r² ℓ`. The Lagrange constants on `Z_j` also need the 1-D density
  bound "≤ C N t/r nodes per disc of radius t". That is a Diophantine condition on the period ratios, and no bound is
  known for transcendental periods.
* **(d) Bounded-degree holomorphic curves through 2-D arrays of lattice points.** These are impossible. The leading
  coefficient `c_d` would need `c_d, c_d ω ∈ Λ_ℚ`, which means a rank-2 complex line again.
* **(e) Theta functions / discrete Fourier on torsion points.** This would need `Ψ` to be quasi-periodic under the
  whole block lattice. On a hyperplane `V` the restricted `Ψ` is only `Ω' = V ∩ Per`-quasi-periodic.

**History agrees [Lit].** Lang's elementary several-variable Schneider–Lang covers only Cartesian products. Bombieri
(1970) needed Hörmander L² for ℤ-combinations, and W83 imports Masser's Theorem A (Invent. Math. 63, 1981) as Lemma 2.3.

## 3. The honest route and revised estimate

**L1.** Power series of entire `F : (Fin n → ℂ) → ℂ` with Cauchy estimates `|c_α| ≤ M_ρ ρ^{-|α|}`, and the Taylor
remainder `|F − P_T|_{r} ≤ M (r/ρ)^T · C^n`.
* There is no several-variable analyticity in Mathlib v4.35: `DifferentiableOn.hasFPowerSeriesOnBall` is for ℂ only,
  and there is no Osgood/Hartogs.
* Proof plan: iterated one-variable Cauchy formula plus differentiation under the integral sign.
* **1–1.5k lines.**

**L2.** Norming lemma: a holomorphic polynomial of degree `< T ≤ c A²` with `|P| ≤ 1` on `G` has `|P|_{B_r} ≤ C^T`.
This is Masser's Theorem A restricted to lattice boxes.
* I do not have a proof I can formalise. Real-variable tools (Markov, Remez, Poisson summation) only reach `T ≲ A`.
* Lelong/Jensen-on-lines gives the exact-zero version. Passing to approximate values brings back L2.
* **3–6k lines, research risk**: the proof must first be reconstructed from Masser 1981, which is not available here.

**L3.** Lemma L = L1 + L2 + the remainder estimate (≈ 0.3k), then the block assembly and `prop21Gen` (≈ 0.8–1k).

**Total ≈ 5–8.5k lines plus research risk.** ABVAR stage A5 (5–8k for Tier 3 + Prop 6.1 + Lemma U + §7) should
probably move to ≈ 10–14k, and R-Prop21 should move up the risk list.

## 4. Cheaper ways around it, for the application

1. **Adapted coordinates (Tier 2 after all) when `dim V ≤ 2`** [Proof sketch]. Take a discrete `Ω' ⊂ V ≅ ℂ²` of
   rank `κ ≤ 3`, and let `H = span_ℝ Ω'`. For a primitive `ω ∈ Ω'` outside the complex line `H ∩ iH`, the form
   `λ_ω` with kernel `ℂω` has `λ_ω(Ω')` discrete (rank ≤ 2, ℝ-independent images). Two ℂ-independent such `ω` give
   coordinates with `Ω' ↪ L₁ × L₂`. The case `κ ≤ 2` is direct. If `κ = 4`, then `V/Ω'` is compact, so `V = T_B` for
   an abelian subvariety `B` (Chow); that is the degenerate case, handled by quotienting.
   * For `dim V ≥ 3` this fails generically. Three generic lattice vectors are ℂ-independent, so no form has discrete
     image once `κ ≥ 5`.
   * Cost: ≈ 0.5k (choice of forms plus the `Prop21Lat` call), replacing `exists_coordsV` by Ω'-adapted forms.
2. **Check the concrete `V` of the M1 targets.** If each `Ω' = V ∩ Per` admits `n` independent forms with discrete
   images, Tier 2 suffices. This is a finite check per instance, and these are hyperplanes (`hyperplaneKappa_of_iso`
   pattern). With the "keep all forms but one" coordinates, each `A`-block is complete and its image is all of `Λ_A`,
   so generically it fails. It survives only if `Ω'` meets each `A`-block in a decomposable part.
3. **Conditional reduction now.** `prop21Gen_of_interp` would take Lemma L as an explicit hypothesis (not an axiom),
   with the §0 statement shape and standard axioms. ≈ 0.8–1k lines. It fixes the caller interface and isolates the
   analytic gap. Not started, per the "stop and report" rule.

## 5. Next concrete step

Get Masser 1981, Theorem A, and Waldschmidt's exposition (the book Thm 7.4.13 cited in `STAGE3_D2.md`). Decide whether
its proof restricted to lattice boxes is formalisable within L2's budget. In parallel, run the finite check in §4.2 on
the M1 hyperplanes. If they all admit Ω'-adapted forms, §4.1–4.2 (≈ 0.5–1k) replaces Tier 3 for M1.

## §4.3 implemented (2026-10-31): `prop21Gen_of_interp`, conditional on Lemma L

Status: **built, sorry-free, standard axioms only** (`propext`, `Classical.choice`, `Quot.sound` for every declaration
below; checked with `#print axioms` from a scratch file, `Axioms.lean` untouched). No existing file was edited.
Build: `lake build LSG.AuxFun.Prop21GenProd` (pulls in the other two), ≈ 40 s per file on top of the cached tree.

### Files

| file | lines | contents |
|---|---|---|
| `LSG/AuxFun/Prop21GenDefs.lean` | 196 | `vecL`, `gptL`, **`LemmaLInterp`** (l. 67), linear/norm lemmas, `grid_smallL` (l. 117) |
| `LSG/AuxFun/Prop21Gen.lean` | 295 | `exists_paramsL` (l. 36), **`prop21Gen_of_interp`** (l. 72) |
| `LSG/AuxFun/Prop21GenProd.lean` | 190 | `prodBasis`, **`lemmaLInterp_prodBasis`** (l. 42), **`prop21Lat_of_gen`** (l. 168) |

### Design choices

* **General form, whole lattice.** `e : Idx n → (Fin n → ℂ)` is any family of `2n` vectors (`Idx n = Fin n × Fin 2`,
  the index type of Tier 2, so `lat_decomp`, `condIdx2`, `card_condIdx2`, `minorMat`, `cAdj`, `cP` are reused verbatim;
  `Idx n ≃ Fin (2n)`). The mixed form W88 wants (product part `∏(0 | 2πiℤ | Λ_E)` completed to lattices, times full
  `Λ_A ⊂ ℂ^g` blocks) is the instance with `e` block-diagonal. No basis hypothesis appears: `e` enters the proof only
  through `LemmaLInterp e`.
* **Lemma L is a `Prop` (`def`), passed as the hypothesis `hL`.** It is stated for the whole lattice, because Masser's
  Theorem A is a statement about an arbitrary lattice in `ℂⁿ`; per-block Lemma L ⇒ Lemma L for a block-diagonal `e`
  (block-by-block interpolation, the analogue of `grid_interp2`) is *not* built (est. 200–300 lines if wanted).

### Exact statements

```lean
def vecL (e : Idx n → (Fin n → ℂ)) (x : Idx n → ℤ) : Fin n → ℂ := ∑ c, (x c : ℂ) • e c
noncomputable def gptL (e : Idx n → (Fin n → ℂ)) (K : ℕ) (v : Idx n → ℤ) : Fin n → ℂ :=
  (K : ℂ)⁻¹ • vecL e v

def LemmaLInterp (e : Idx n → (Fin n → ℂ)) : Prop :=
  ∃ c C : ℝ, ∃ A₀ : ℕ, 0 < c ∧ 1 ≤ C ∧
    ∀ (F : (Fin n → ℂ) → ℂ) (A K : ℕ) (r R ε M : ℝ), Differentiable ℂ F →
      A₀ ≤ A → 1 ≤ A → K ≠ 0 → 0 < r → (A : ℝ) ≤ r * K → r * K ≤ 2 * A → C * r ≤ R →
      0 ≤ ε → 0 ≤ M →
      (∀ v : Idx n → ℤ, (∀ c, |v c| ≤ A) → ‖F (gptL e K v)‖ ≤ ε) →
      (∀ z, ‖z‖ ≤ R → ‖F z‖ ≤ M) →
      ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ C ^ (A ^ 2) * (ε + (C * r / R) ^ (c * (A : ℝ) ^ 2) * M)
```

(sup norm on `Fin n → ℂ`; the second power is `Real.rpow`.) Weakened as far as the assembly allows: existential
constants, `A ≥ A₀` arbitrary, grid radius pinned to `r` up to the factor 2 (`A ≤ rK ≤ 2A`), `R ≥ C r`. Intended source
[Lit, not verified here]: W83 Lemma 2.3 = Waldschmidt DALAG Thm 7.4.13, via Masser 1981 Thm A (Invent. Math. 63).
Expected for every `ℝ`-basis `e`; false for degenerate `e` (e.g. `e = 0`).

```lean
theorem prop21Gen_of_interp (n κ : ℕ) (a : ℝ) (ha : 0 ≤ a) (e : Idx n → (Fin n → ℂ))
    (hL : LemmaLInterp e) (P : Fin κ → Idx n → ℤ) (I : Fin κ → Idx n)
    (hI : Function.Injective I) (hd : (minorMat P I).det ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • ∑ c, (P i c : ℂ) • e c‖) ^ 2) ∧
        ∀ l, ψ l (z + ∑ i, (k i : ℂ) • ∑ c, (P i c : ℂ) • e c) = m * ψ l z) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U)
```

This is `prop21Lat`'s conclusion word for word with `perVec α β (P i)` replaced by `ω_i = Σ_c P_i(c) e_c`, so a
Tier-3 version of `PropG.lean`/`PropGV.lean` can copy their assembly (coordinate rescaling, (QP) from
`exists_qp_mono_uniform`) unchanged, passing `e` and `hL` instead of `α, β, hD`.

Proof (as `prop21Lat`): `D = 10/c + 1`, `A = ⌈√(DU/ℓ)⌉` (so `A ≥ r ≥ A₀`), `K = ⌈A/r⌉` (`A ≤ rK ≤ 2A`); count via
`count_lat` with `S = 1` at `U' = DU/10`; Siegel; `grid_smallL` (multiplier transfer, `lat_decomp`); then Lemma L with
`ε = 2e^{−3U}`, `M = e^{Δ+U}`, and `C^{A²} ≤ e^U`, `(Cr/R)^{cA²} ≤ e^{−5U}` once `log(R/r) ≥ 4D log C`
(`c₁ = exp(6 + C₆ + C + 4D log C + A₀)`).

### Non-vacuity: the product case of Lemma L is proved

```lean
noncomputable def prodBasis (α β : Fin n → ℂ) : Idx n → (Fin n → ℂ) :=
  fun c => Pi.single c.1 (if c.2 = 0 then α c.1 else β c.1)
theorem lemmaLInterp_prodBasis (α β : Fin n → ℂ)
    (hD : ∀ j, ((starRingEnd ℂ) (α j) * β j).im ≠ 0) : LemmaLInterp (prodBasis α β)
theorem prop21Lat_of_gen … -- the exact statement of `prop21Lat`, proved from
                           -- `prop21Gen_of_interp (prodBasis α β) (lemmaLInterp_prodBasis α β hD)`
```

`lemmaLInterp_prodBasis` uses `c = 1`, `A₀ = 1`, `C = max((16G)^{9n} 2^n, 4S)` with Tier 2's `G = 3 S c_i e²`: it is
`grid_interp2` + `lat_coord` at radius `r' = S r`. So the hypothesis is satisfiable, and the conditional theorem
specialises to the unconditional Tier-2 theorem (an independent re-derivation of `prop21Lat`'s statement).

### What is still open

Lemma L itself for non-product `e` (§3: L1 + L2, the research-risk part). Optionally: the block-diagonal reduction
(per-block Lemma L ⇒ `LemmaLInterp` for block-diagonal `e`), and a Tier-3 `PropG` caller.

---------------------------------------------------------------------------------------------------------------------

## Research: routes to L2 (2026-10-31; refocused mid-task on the §4.2 finite check)

Scope: the coordinator reprioritised mid-task. The main item is the §4.2 check: do the concrete hyperplanes of the M1
targets admit Ω′-adapted forms? Item (2) records the L2 sources found so far, with no further hunting. Interpolation
determinants and other alternative routes were not pursued (item 3). No Lean files were touched.

### R0. Two tools for the check

**Criterion C (when is a single form usable).** [Proved] Let `Ω′` be a discrete subgroup of a complex space `V′`, and
`X = ℚΩ′`. Let `π : X ⊗ ℂ → V′` be the complexified inclusion, and `N = ker π`, the space of complex relations among
the periods. Then `U := span_ℂ Ω′ ≅ X_ℂ/N`.
* A form `f` on `V′` has `f(Ω′)` discrete iff, after scaling, `f|_X = ℓ₁ + τℓ₂` with `ℓ₁, ℓ₂ ∈ Hom(X, ℚ)` and
  `τ ∉ ℝ`, or `f|_X = ℓ₁`. (A discrete subgroup of ℂ is commensurable with `ℤ + ℤτ`, `ℤ` or `0`.)
* Ω′-adapted coordinates (Tier 2: `n` forms forming a basis of `V′*`, each with discrete image) exist iff such forms
  span `N^⊥ ⊂ X_ℂ*`. The forms vanishing on `U` are added freely.
* Adaptability passes to subgroups of `Ω′` and to subspaces `V″ ⊂ V′`: restrict, then pick a basis.

In the CM situation everything is defined over a number field. Take a period block `X ≅ K` (`K ⊇ F` a number field).
Every element of `Hom(K, ℚ)` is `Tr_{K/ℚ}(c ·)`, so the usable forms are `x ↦ Σ_ρ (ρ(c₁) + τρ(c₂)) ρ(x)`, summed over
the embeddings `ρ` of `K`. `N` is a sum of whole `ρ`-components. The form vanishes on the `ρ`-component iff
`ρ(c₁/c₂) = −τ`.
* If the components in `N` lie over a set `R` of embeddings of `F`, then `w = c₁/c₂` must lie in `F` and be constant
  on `R`.
* When the stabiliser of that constant value generates a group whose fixed field is `ℚ` (or is totally real), `τ` is
  forced real, and then `f = 0`.

**Lemma E (excess ≤ 1 suffices).** [Proved] Suppose `rank Ω′ ≤ dim_ℂ span_ℂ Ω′ + 1`. Then Ω′-adapted forms exist.

*Proof.*
1. If `rank Ω′ = k := dim U`, the dual basis gives images `ℤ`.
2. Otherwise take a ℤ-basis `ω₁..ω_{k+1}`, with the single complex relation `Σ c_i ω_i = 0`. The vector `c` is not
   proportional to a real vector, by ℝ-independence. So there are indices `p, q` with `c_p, c_q ≠ 0` and
   `c_p/c_q ∉ ℝ`.
3. Let `g_i` (`i ≠ q`) be the dual basis to `{ω_i}_{i≠q}`. Then `g_p(Ω′) = ℤ + ℤ c_p/c_q` is discrete.
4. For `i ∉ {p, q}`, put `h_i = g_i + t_i g_p` with `t_i ∈ ℤ` chosen so that `Im((c_i + t_i c_p)/c_q) ≠ 0`. All but
   one integer works. Then `h_i(Ω′) = ℤ + ℤ(c_i + t_i c_p)/c_q` is discrete.
5. `{g_p, h_i}` is a basis of `U*`; extend by zero on a complement. ∎

This covers STAGE_A5 §4.1 (`dim V ≤ 2`, κ ≤ 3) as a special case.

### R1. Where Prop 2.1 is called

* `Prop61.lean` calls `prop21_G_deg` on the `V` of Thm 4.1, with **caller-chosen** ℤ-independent `ω_i ∈ V ∩ Ω(G)`.
* The §5d engine (`Thm11Kappa.lean` docstring; `K5d*`, `Thm41Sub`) calls Thm 4.1 only on `V′ = V ∩ T_{G′}` with
  `Y′ = Y ∩ T_{G′}`. Here `G′ = T_L × B (× G_a-part)` is the connected subgroup maximising `a/e`. The coordinate-projection
  isogenies are linear isomorphisms, which preserve adaptability.
* So every `Ω′` reaching Prop 2.1 is a subgroup of `V ∩ per` for the **top-level** `V`, and `G′ = G` cannot be excluded
  inside the contradiction argument.
* Caveat: lean_mstar's `Thm11KappaA`, `Thm11KappaAK` and `Thm11KappaX7` quantify over **all** hyperplanes `V`. The
  consumers use only the frame hyperplane `V″ = Ψ''⁻¹(ℂ(1, s))` (`phiF`, `phiG`, `phiX`). Results for `V″` alone need a
  narrowed lean_mstar hypothesis (R3).

### R2. Per-target verdicts

**(T1) Theorem A for `B(1/5,1/5)` and `B(1/7,1/7)`** (`gmA`, frame `gmF`; `fourExpAt_beta5/7`, `two_three_beta5`,
`fourExpAt_pi_div_beta5`): **YES for `V″`, and in fact Tier 1 suffices.** [Proved]
* `V″ = ker(θᵀy + λ(q) − sθᵀx)` with `λ(q) = Σ_j b_j q(s₀, j)`.
* A period of `V″` with zero toric part is `qv q`, with `q` a ℚ-combination of the `[ζ^e]γ`. In copy `j`,
  `q(s₀, j) = P_{s₀}·m_j` with `m_j ∈ F` (`κ s₀ = 1`).
* `λ(q) = P_{s₀} Σ_j b_j m_j = 0` forces `m = 0`, because `b` is `F`-independent. (This is the soundness argument of
  `gmA`.)
* Hence `Ω′ → (toric part) ⊂ 2πiℚ^{2n}` is injective. ℚ-independent rational vectors are ℂ-independent, so **every
  `Ω′ ⊂ V″ ∩ per`, for every `G′`, is ℂ-linearly independent.**
* Tier 1 then applies: `prop21B`/`Prop21Lin` shape, W83's Remark `U ≥ r log(R/r)`. No lattice grid is needed and no L2.
* Same for `g = 3` (`perT`): the argument never uses `g`.

**(T2) Cor A2** (`gmAK` with `LA = ∅`, frame `gmF2` with `μ = 0`; `corA2_beta5`): **YES**, by the same argument
(`phiG` with `μ = 0` is `phiF`). [Proved]

**(T3) X7** (`gmX7`, frame `gmFX`; `x7c`, `thmX7`): **NO, Tier 2 cannot work, even for the concrete `V″`.** [Proved]

Setup:
* `V″ = ker(μ₂ + s₂ − σ(μ₁ + s₁))`, with `σ = βP₃/P₁` (`propX7_K`).
* Using `P₁P₂ = μ′P₃Ω` (`relation_R`) and Wüstholz independence of `P₂, P₃`, `V″ ∩ per ⊗ ℚ` is `X_A ⊕ X_B` (each ≅ `K`,
  rank `6r`). These live in disjoint coordinates.
  - `X_A`: block-0 period `κ₀`, block-2 period `βκ₀` (the lifts `p_h`).
  - `X_B`: `E`-period `κ_E`, block-1 period `(β/μ′)κ_E` (the lifts `p′_h`).
* The block-2 lift is twisted by `σ₅` (`aLift 2 5`), so `X_A` uses the characters `{1,2,3} ∪ 5·{1,2,3} = {1,2,3,5}` of
  `(ℤ/7)^×`.
  - So `N_A` is the sum of the components over `{σ₄, σ₆}`, and `dim span X_A = 4r`.
  - By Criterion C, a usable form needs `w ∈ F` with `σ₄(w) = σ₆(w)`. But `σ₄⁻¹σ₆ = σ₅` generates `(ℤ/7)^×`, so
    `w ∈ ℚ`, `τ ∈ ℚ`, and `f = 0`.
  - **The lattice `X_A` admits no nonzero form with discrete image at all.** (Check at `r = 1`: `κ ↦ (κ, σ₂κ, σ₃κ, σ₅κ)`
    on `O_F`.)
* `X_B` (characters `{1,2,4}` from `E`, `{1,4,5}` from block 1; `N_B` over `{σ₃, σ₆}`) also fails.
  - Usable forms need `w ∈ k = ℚ(√−7)`, and they then also vanish on the `σ₅`-component.
  - So they span only `3r` of the `4r` dimensions of `span X_B`.
* The κ from `X_A` is needed. With `d₁ = 0`, `d₂ = 12r + 2`, `m = 18r` and `d − 1 − t ≤ 1`, (5.4) is `κ > 6r + 4`. The full
  `κ = 12r` works; `κ = 6r` (`X_B` alone) does not.

**Fallback for X7** [count Proved; engine Heuristic]:
* Weaken κ to `κ_ℂ := dim_ℂ span_ℂ(Y ∩ per)`, and give Prop 6.1 a ℂ-independent subfamily (Tier 1).
* Here `κ_ℂ ≥ 4r + 4r = 8r`, and `8r > 6r + 4 ⇔ r ≥ 3`.
* Arranging `r = [K:F] ≥ 3` costs nothing: enlarge `K` by any cubic algebraic number. `hcount` `24r + 4 < 30r` holds.
* The §5d engine with `κ_ℂ` needs `κ_ℂ − κ″_ℂ ≤ d − d″`, which is immediate for complex dimensions. This is unchecked
  against `K5d*`. Otherwise X7 needs L2 or an equivalent.

**All-`V` (verbatim) statements, for completeness.**
* `g = 3`: non-adaptable `Ω′` exist inside hyperplanes containing no algebraic tangent. [Proved]
  - Example: the twisted line `X = {(m, σ₅(βm))} ⊂ F²` in `A₇²`. Its span `U = {y₃ = c x₁, y₂ = c′x₃}` contains no
    `T_{B′}`, and `N` lies over `{σ₄, σ₆}`.
  - Any hyperplane `Hp ⊃ U` that is a non-`F`-rational combination of the two equations contains no `T_{B′}` either.
* `g = 2`: every `Ω′ ⊂ Hp ∩ Λ_B` has excess ≤ 1 for `B ∼ A, A²` (rank count `0` or `4`, then Lemma E). [Proved]
  - For `B ∼ A^s` with `s ≥ 3`: **open**.
  - Twisted `F`-lines are all fine; higher-rank `X` were not analysed.
* So the verbatim generic statements are not covered by Tier 2 for `g = 3`. This is a further reason to narrow.

### R3. Recommendation (replaces STAGE_A5 §4–5 for M1)

1. **M1 needs no Tier 3.**
   - Add to lean_mstar a narrowed hypothesis: `HyperplaneKappa` with the extra premise
     **(TorInj)** `∀ v ∈ V, v ∈ G.per → v.1 = 0 → v = 0` (zero toric part).
   - Prove that `V″` satisfies it in `frame_false`/`frame2_false_K` (`F`-independence of `b`, ≈ 0.1–0.2k lines).
   - Restate `Thm11KappaA`/`Thm11KappaAK` with it (lean_mstar change "L5").
   - lean_lsg then proves the narrowed instances with **Tier 1** Prop 2.1: TorInj is inherited by every `V ∩ T_{G′}`.
   - This deletes the ≈ 5–8.5k Tier-3 block, and R-Prop21 as a risk, from M1.
2. **X7 (M3):** either the `κ_ℂ` fallback (narrowed `Thm11KappaX7` with `κ_ℂ`, `r ≥ 3`; check the engine against `K5d*`
   first), or L2.
3. **M2 (`A^♮`, `Thm11KappaAn`)** was not checked. Run the same TorInj test on `phiF` for `gmAn`; the fibre coordinate
   enters `λ`.
4. The conditional `prop21Gen_of_interp` (§4.3, now built) is needed only for X7 or for verbatim generic statements.

### R4. L2 sources (recorded; hunting stopped per coordinator)

* **Citation correction** [Lit, W83 p. 634 and refs p. 638]. This also corrects the "intended source" line of §4.3.
  - W83's Lemma 2.3 cites **Masser, "Polynomial interpolation in several complex variables", J. Approx. Theory 24
    (1978) 18–34, Théorème A**. It does not cite Invent. Math. 63 (1981). The Invent. Math. 63 reference in W83 is [10],
    W81 (pp. 97–127).
  - Masser's Invent. Math. 63, 81–95 is, from memory, a zero-estimate paper [Heuristic].
  - "Thm 7.4.13 of [9]" is in **Waldschmidt, Astérisque 69–70 (1979), *Nombres transcendants et groupes algébriques***,
    not the Springer 2000 book. The ℂ-independent case uses **Thm 7.3.4** of the same.
* **W83's own text** (local PDF, pp. 634–635) has Lemma 2.3 with explicit constants and a 10-line reduction:
  1. `F = P + G`, `P` the Taylor polynomial of degree `< T`.
  2. Theorem A: `|P|_{r₁} ≤ (2^{10n}/δ)^{nT} max_𝕊 |P|`, as scanned; the normalisation is unclear in the OCR.
  3. A one-variable maximum principle on `Q(t) = t^{T−1}P(x₀/t)`.
  4. A Cauchy bound for `G`, as in W81 Lemma 3.4.

  **No proof of Theorem A itself is in W83.** The rest of Lemma 2.3 is elementary once L1 (several-variable Taylor and
  Cauchy) exists.
* **Theorem A is exactly L2** [Proved, arithmetic]. For the box `𝕊′` of W83, with `(2A+1)^{2n}` points, separation
  `δ ≍ r₁/A`, and `ϑ² ≍ (δ/r₁)^{2n} Card 𝕊 ≍ 1`, the hypothesis `T ≤ 2^{−7n}(δ/r₁)^{2n−2} Card 𝕊` reads `T ≲ A²`. The
  exponent `2n − 2` suggests tubes around complex lines.
* **Naive tube proof fails** [Proved]. Projecting the `≥ T` points in a δ/4-tube onto its line costs `|∇P|·η`. Against a
  Lagrange constant `C^T`, this forces `η ≤ C^{−T} r₁/T`, and then the tube holds too few points. Masser's argument must
  be different.
* Not found: Masser 1978 online (one search, no hit; ScienceDirect's JAT open archive is the likely source). `memSMF` 13
  (1984) is a survey with no proof. Interpolation determinants and the Lang / Bombieri–Lang chapters were not consulted.
