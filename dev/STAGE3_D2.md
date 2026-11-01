# Stage 3, node D2: the κ-saving auxiliary function (W83 Prop. 2.1) — design and status

Started 2026-10-30. Labels as in PLAN.md ([Lit] read in the source, [Design] my choice, [Est] line estimate).
Sources: **W83** = Waldschmidt, Ann. Math. 117 (1983), `../schanuel/five_exp/ref/waldschmidt_1983_AnnMath117.pdf`
(PDF page = journal page − 624); **W88** = `../schanuel/five_exp/ref/w88_pages/w88-11.png`, `-12.png` (Prop. 6.1,
§7); **Lemma U** = `../schanuel/five_exp/pilot_epi2_mix/W_UPGRADE.md`.

---------------------------------------------------------------------------------------------------------------------

## 1. The statements in W83 [Lit]

Notation: for z ∈ ℂⁿ, |z| = max_ν |z_ν|; B(0, R) is the closed polydisc; |f|_R = sup_{B(0,R)} |f|.

**Prop. 2.1 (p. 632–633).** Let θ be a holomorphic theta function for a lattice Ω ⊂ ℂ^g with θ(0) ≠ 0,
ℒ : ℂⁿ → ℂ^g linear, σ = θ∘ℒ, and ω₁, …, ω_κ ∈ ℂⁿ ℝ-linearly independent (0 ≤ κ ≤ 2n). There are c₁, c₂ > 0 such
that: if L ≥ 1, D ≥ 0 are integers, Δ, U, R, r > 0 reals, φ₁, …, φ_L meromorphic on ℂⁿ with periods ω₁, …, ω_κ such
that ψ_λ = σ^D φ_λ are entire, and

  U ≥ Δ,  R/r ≥ c₁,  r ≥ c₁,  U ≥ r² log(R/r),  U ≥ D r²,  Σ_λ |ψ_λ|_R ≤ e^U,  c₂ U^{n+1} ≤ L Δ r^κ (log R/r)ⁿ,

then there are rational integers p₁, …, p_L with 0 < max |p_λ| ≤ e^Δ such that Ψ = Σ p_λ ψ_λ has |Ψ|_r ≤ e^{−U}.
(κ = 0: Thm 3.1 of W81, c₁ = 3, c₂ = 8^{n+1}.) **Remark (p. 636):** if the ω_i are ℂ-linearly independent, U ≥ r²
log(R/r) can be replaced by U ≥ r log(R/r).

**Lemma 2.2 (p. 633).** θ, ℒ ≠ 0 as above, Λ = ℤω₁ + ⋯ + ℤω_m ⊂ ℂⁿ finitely generated. There are c′, c″ > 0 and
𝒯, F ⊂ Λ, F finite, Λ = 𝒯 + F, such that for every S ≥ 1, with Λ(S) = {Σ h_j ω_j : 0 ≤ h_j ≤ S},
|θ∘ℒ(z)| ≥ exp(−c″S²) whenever dist(z, Λ(S) ∩ 𝒯) ≤ c′. (Proof: 𝒯 = {ω ∈ Λ : ℒ(ω) ∈ Δ′ + Ω}, Δ′ a small polydisc on
which θ ≠ 0; quasi-periodicity of θ; F by compactness of the closure of ℒ(Λ) mod Ω.)

**Lemma 2.3 (p. 634; Waldschmidt's book Thm 7.4.13, via Masser's Theorem A).** ϑ > 0, 0 < r₁ ≤ r ≤ R, T ≥ 1, 𝕊 ⊂
B(0, r₁) finite with separation δ, T ≤ 2^{−7n}(δ/r₁)^{2n−2} Card 𝕊, ϑ² ≤ n^{−n}(δ/r₁)^{2n} Card 𝕊. Then every F
continuous on B(0, R), analytic inside, satisfies |F|_r ≤ (cr/R)^T |F|_R + (cr/r₁)^T max_𝕊 |F|, c = 2 + 2(2^{10n}/ϑ)ⁿ.
(Proof: F = P + G, P the Taylor polynomial of degree < T; Masser's Theorem A bounds |P|_{r₁} by its values on 𝕊.)

**Proof of Prop. 2.1 (pp. 635–636).** Complete ω₁..ω_κ to an ℝ-basis ω₁..ω_{2n}; Λ′ = ⊕_{i≤κ} ℤω_i, Λ″ = ⊕_{i>κ} ℤω_i.
T = 4U/log(R/r), T₀ = νT. Points 𝕊 = {λ₁ + rT₀^{−1/2}λ₂ : λ₁ ∈ Λ″(r/c₃) ∩ 𝒯, λ₂ ∈ Λ(T₀^{1/2}/rc₄)}, Card 𝕊 ≤ T₀ⁿ r^{−κ}
(**the κ-saving: conditions only on a fundamental domain of Λ′**). Siegel (Lemma 3.3 of W81): integers |p| ≤ e^Δ with
|Ψ(s)| < e^{−νU} on 𝕊, possible since 4νU T₀ⁿ r^{−κ} < LΔ ⇔ c₂U^{n+1} ≤ LΔr^κ(log R/r)ⁿ. Periodicity:
Ψ(z + ω) = (σ(z+ω)/σ(z))^D Ψ(z) for ω ∈ Λ′; Lemma 2.2 gives |σ(s)| ≥ e^{−c₅r²}, so |Ψ| ≤ e^{−νU/2} on 𝕊′ = 𝕊 + Λ′(r/c₃),
Card 𝕊′ ≥ c₆T₀ⁿ, separation ≥ c₇rT₀^{−1/2}. Lemma 2.3 on 𝕊′ gives |Ψ|_r ≤ (cr/R)^T e^{Δ+U} + c^T e^{−νU/2} ≤ e^{−U}.

## 2. How Prop. 2.1 / Lemma 2.2 feed W88 Prop. 6.1 (via W83 Prop. 2.4 and Lemma U) [Lit]

* **Prop. 2.4, Step 1 (p. 640)** = Lemma U §1.1, eq. (1): Prop. 2.1 on V ≅ ℂⁿ with r = ν²S, R = ν³S, σ = ψ₀ (the
  theta coordinate of Serre's embedding), U = ν⁶Δ, D = D₂° ≤ D₂/ν, the ψ_λ = all monomials λ^a μ^b ψ^c (degrees
  ≤ D₀/ν, ≤ D₁/ν, homogeneous of degree D₂° in ψ), φ_λ = ψ_λ/ψ₀^{D₂°}, κ periods from V ∩ Ker exp_G (W88: from Y ∩ Ω).
  Output: Q_S ∈ ℤ[U, V, W], coefficients ≤ e^{Δ/ν}, |Q_S(λ, μ, ψ)|_{ν²S} ≤ e^{−ν⁶Δ}. Hypothesis U ≥ r² log(R/r) is (NR).
* **Lemma 2.2** is used in Step 2 (p. 641) and in Lemma U §1.2 eq. (2): lower bound for ψ₀ near the points
  t ∈ Y(νS) ∩ 𝒯, to bound the coordinates ξ = ψ/ψ₀ and to make the Liouville step work. It is **not** needed in D2
  (see O1 below); it belongs to D3.
* **Lemma U §1.2–1.3** (D3): Taylor coefficients along W at the points of Y(νS) ∩ 𝒯 (Cauchy + Liouville), then
  translation by F′ via addition laws. **W88 §7**: Philippon applied to P_S (D4).

## 3. Design decisions [Design]

**O1. Lemma 2.2 is not needed inside Prop. 2.1.** W83 uses Lemma 2.2 only to bound (σ(s+ω)/σ(s))^D, because its φ_λ
are only assumed ω-periodic. In every application ℒ(ω) ∈ Ω for ω ∈ Λ′ (periods of G lie over periods of G₂), so the
multiplier is the theta factor of automorphy, an explicit exponential: Ψ(z + ω) = m(ω, z) Ψ(z) with
|m(ω, z)| ≤ exp(a D (|z| + |ω|)²), identically in z (both sides entire). In our library this is
`LSG.Weierstrass.sigma_add` (σ(u + ω) = ±exp(η(ω)(u + ω/2)) σ(u)) with η ℤ-linear on Λ (`eta_add`); for G_m factors the
multiplier is 1, G_a coordinates have zero period component. So the abstract hypothesis is
**(QP)** ∀ ω ∈ Λ′ ∀ z ∃ m, |m| ≤ exp(a D (|z|+|ω|)²) ∧ ∀ λ, ψ_λ(z + ω) = m ψ_λ(z),
and 𝒯 disappears from D2 (the point set is a full grid).

**O2. Lemma 2.3 (Masser's Theorem A, a Bombieri–Lang-type statement for arbitrary separated sets in ℂⁿ) is avoided
by choosing coordinates in which Λ′ lies in a product of discrete rank-≤2 subgroups of ℂ.** If φ₁, …, φ_n is a basis
of V* with each φ_j(Λ′) contained in a discrete subgroup L_j ⊂ ℂ, then in the coordinates φ the grid
Γ = Π_j Γ_j (Γ_j a truncated (1/K)L̂_j, L̂_j ⊇ L_j of rank 1 or 2) is Λ′-stable up to truncation, and interpolation on Γ
is **iterated one-variable Lagrange interpolation + StrongSix's one-variable Schwarz lemma**, one coordinate at a time
(`Function.update`). No several-variable polynomial interpolation, no Lelong numbers.
* **Tier 1 (formalised now): ω₁, …, ω_κ ℂ-linearly independent.** Coordinates with ω_i = e_i, so Λ′ = ℤ^κ × 0 and all
  Γ_j are real arithmetic progressions {k/K : |k| ≤ A}. Node products are factorials; Lagrange constants are ≤ c^N with
  N = 2A+1 ≈ T nodes per coordinate; Card 𝕊 = K^κ N^{n−κ} ≈ Nⁿ/(2r)^κ. This needs only U ≥ r log(R/r) (W83's Remark),
  and κ ≤ n. All M* instances have κ ≤ N = dim V (MG κ = n_K ≤ 5n_K/2 − 1, MX/MX′ κ = 2n_K ≤ 2n_K + 1).
* **Tier 2: the abelian class of `Statement.lean`, general Λ′ = V ∩ (subgroup of Ker exp_G).** Take φ_j = n of the
  coordinate forms of T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m whose restrictions to V form a basis of V*. They send Ker exp_G into
  0 (G_a), 2πiℤ (G_m) or Λ_j (E_j), so L_j is 0, cyclic, or a lattice. Grid: progressions in the first two cases,
  2D grids (1/K)(ℤα_j + ℤβ_j) with ≈ T nodes in lattice coordinates (needs U ≥ r² log(R/r), exactly W83's hypothesis).
  Extra work: (a) the node-product bound for a 2D lattice grid, Π_{ζ′≠ζ}|ζ−ζ′| ≥ (c h)^{N−1} √((N−1)!) — via
  |xα + yβ| ≥ c₀ max(|x|,|y|) and a dyadic-shell count; (b) counting Λ′-classes in the grid via Smith normal form
  (`Submodule.smithNormalForm`): ≤ Π a_i · K^κ · (C A)^{2n−κ} in the adapted basis. ℂ-dependent periods (e.g. ϖ and iϖ
  in one CM coordinate) occur in MX-type configurations, so Tier 2 is needed for the general theorem.
* **Class 𝒞 (vector extensions, MG♮/MX/MX′).** For one E^♮ factor with coordinates (z, w) and periods (λ, η(λ)), the
  forms z and w − (η(ω₁)/ω₁) z send periods to Λ and to a cyclic group: Tier 2 applies. For quotients of (E^m)^♮ by a
  fibre subgroup with matrix M the fibre forms give Σ_j cyclic groups, which need not be discrete when m ≥ 3; then
  either choose the forms on V only (only Λ′ = V ∩ Ker matters) or fall back to Masser's Theorem A. **Risk, to be
  checked against the concrete G″ of the paper before Tier 2 is extended to 𝒞.**

**O3. Several complex variables.** ℂⁿ is `Fin n → ℂ` with Mathlib's sup norm, which *is* W83's |z|; closed polydiscs
are `Metric.closedBall 0 R`. The ψ_λ are entire (`Differentiable ℂ`), as in W83 (and our concrete functions σ³, σ³℘,
σ³℘′, e^{⟨x,z⟩}, z_i are entire). Prop. 2.1 then needs no polydisc Cauchy theory at all: only restrictions to coordinate
lines w ↦ F(update z j w) (entire in one variable) and StrongSix's `norm_le_of_zeros`. D3 (Lemma U) needs Taylor
coefficients along W: reduce, as StrongSix `Thm1/` does, to one-variable Taylor coefficients along finitely many lines
s ↦ F(t + sζ), ζ ∈ W(ℚ̄) (`StrongSix.Thm1.iteratedDeriv_line`, `Thm1/Taylor.lean`), using that a homogeneous polynomial
of degree k in t variables vanishing on the directions {Σ a_i w_i : 0 ≤ a_i ≤ k} is zero.

**O4. Siegel.** Mathlib's `Int.Matrix.exists_ne_zero_int_vec_norm_le` is for exact integer systems; Prop. 2.1 needs
approximate complex conditions, so we prove a pigeonhole lemma directly (cells of side ε for Re and Im of each form).
The coefficient bound is Σ_λ |ψ_λ(s)| ≤ e^U (a sum, as in W83), so no log L term appears.

## 4. Lean formulation

### 4.1 Tier 1 — DONE 2026-10-30 (`LSG/AuxFun/`, namespace `LSG.Aux`, 1007 lines, standard axioms)
(`LSG/Aux/` is impossible on Windows: `AUX` is a reserved device name and Lean rejects the module name.)
```
def LSG.Aux.QuasiPeriodic (κ : ℕ) (a : ℝ) (D : ℕ) (ψ : Fin L → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ k : Fin n → ℤ, (∀ i : Fin n, κ ≤ i.val → k i = 0) → ∀ z, ∃ m : ℂ,
    ‖m‖ ≤ Real.exp (a * D * (‖z‖ + ‖(fun i => (k i : ℂ))‖) ^ 2) ∧ ∀ l, ψ l (z + fun i => (k i : ℂ)) = m * ψ l z

theorem LSG.Aux.prop21 (n κ : ℕ) (hκ : κ ≤ n) (a : ℝ) (ha : 0 ≤ a) :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L D : ℕ) (Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
    1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r * Real.log (R / r) ≤ U → (D : ℝ) * r ^ 2 ≤ U →
    (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
    QuasiPeriodic κ a D ψ → c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
    ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
      ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U)
```
W83 Prop. 2.1 + Remark (p. 636) for ℂ-independent periods in adapted coordinates (periods e₁..e_κ). The growth
hypothesis is sup_z Σ_λ |ψ_λ(z)| ≤ e^U (weaker than W83's Σ_λ |ψ_λ|_R). Constants: c₁ = exp(6000(n+1)),
c₂ = 2(6+9a)·60ⁿ. `#print axioms LSG.Aux.prop21`: [propext, Classical.choice, Quot.sound].

| file | lines | content |
|---|---|---|
| `Siegel.lean` | 118 | `siegel_approx`: approximate complex Siegel lemma (pigeonhole on cells of side ε) |
| `Lagrange.lean` | 99 | `lagBasis`, `lagInterp`, `norm_le_interp`: one-variable interpolation with approximate values (via `StrongSix.norm_le_of_zeros`) |
| `Progression.lean` | 234 | `progNodes A K` = {(j−A)/K}, factorial node products, `prog_constants` (all Lagrange constants ≤ 100^{2A+1}) |
| `Grid.lean` | 88 | `grid_interp`: interpolation on the product grid Zⁿ, coordinate by coordinate (replaces Lemma 2.3) |
| `Reps.lean` | 130 | `condIdx`/`condPt` (condition set = fundamental domain of ℤ^κ × 0), `card_condIdx` = K^κ N^{n−κ}, `grid_decomp` |
| `Prop21.lean` | 338 | `QuasiPeriodic`, `count_arith`, `final_arith`, `siegel_count`, `count_final`, `grid_small`, `exists_params`, `prop21` |

The files are not imported by `LSG.lean` (default target untouched); build with `lake build LSG.AuxFun.Prop21`.

### 4.2 Remaining for D2 (Tier 1′, Tier 2) [Est]
* `Prop21Lin.lean`: arbitrary ℂ-independent ω₁..ω_κ in ℂⁿ (or in V ⊂ T_G) by a ℂ-linear change of variables A with
  A e_i = ω_i; polydiscs move by ‖A‖, ‖A⁻¹‖ (absorbed in c₁, c₂). **250**.
* Tier 2: 2D node products (**350**), mixed grids (**200**), Smith-normal-form class count (**300**), assembly (**300**).
* Concrete (QP) for the functions of G (σ-multipliers, `sigma_add`, `eta_add`; G_m multiplier 1): **250**.
* Total D2 remaining ≈ 1.7k (PLAN estimate for D2 was 3k; Tier 1 took 1.0k).
* Tier 1′ note: the change of variables multiplies the multiplier constant by ‖A‖² and r by ‖A⁻¹‖, so `prop21`
  should first be restated with a single multiplier constant b (QP bound exp(b(|z|+|ω|)²), hypothesis b r² ≤ a U)
  instead of (a, D); `prop21` is the case b = aD. Small refactor (≈ 30 lines).

### 4.3 Lemma 2.2 for our G₂ (goes with D3) [Design]
Use the theta coordinate ψ₀ = Π_j (σ_j³℘_j′)(ℓ_j z) = Π_j −σ_j(2ℓ_j z)/σ_j(ℓ_j z) (nonzero at 0: value (−2)^m), a theta
function with explicit multiplier (from `sigma_add`). Statement: for t ∈ V with ℓ_j(t) ∈ Λ_j + D(0, c′) for all j,
|ψ₀(t)| ≥ exp(−c(1 + |t|)²). 𝒯 = {y ∈ Y : ℓ_j(y) ∈ Λ_j + D(0, c′/2)}; Y = 𝒯 + F with F finite by compactness of the
closure of the image of Y in Π ℂ/Λ_j (finitely many translates of the open neighbourhood cover it). [Est] 400.

## 5. Reuse from StrongSix (Lake dependency, never edited)
| StrongSix file | content | use here |
|---|---|---|
| `Analytic/Schwarz.lean` | `exists_entire_factor`, `norm_le_of_zeros` (entire f, zeros Z ⊂ D(0,r), \|f\| ≤ M on \|w\| = R ⇒ \|f\|_r ≤ M (2r/(R−r))^{#Z}) | **used** (one-variable step of the grid interpolation) |
| `Thm1/Lines.lean` | iterated derivatives along a line | D3 (Taylor coefficients along W) |
| `Thm1/Taylor.lean` | `tc`, `taylor_split`, `tc_mul_factorial` | D3 |
| `Thm1/InterpDet.lean` | interpolation determinants (Laurent) | not used (no determinant version of the mixed-period κ-saving) |
| `Thm1/Growth.lean`, `Params.lean` | log/parameter bookkeeping for Thm 1 | patterns only; parameter shapes differ (S, S², log S scales) |
| `Thm1/Heights.lean`, `Arith/Liouville.lean` | heights, Liouville | D3 (Liouville step) |
| `Thm1/Count.lean`, `Reduce.lean`, `Quot*.lean` | Step R (quotient by an algebraic period span) | not applicable (mixed periods) |

### Status 2026-10-30 (continuation): Tier 1′ DONE
* `Prop21.lean` refactored: `QuasiPeriodicB κ b ψ` (single multiplier constant, bound exp(b(|z|+|ω|)²)) and
  `prop21B` (hypotheses `0 ≤ b`, `b r² ≤ a U` instead of `D r² ≤ U`); `prop21` is now a 10-line corollary (b = aD).
* `Prop21Lin.lean` (≈ 170 lines): `exists_equiv_extend` (ℂ-independent ω₁..ω_κ extend to A ∈ GL(ℂⁿ) with
  A k = Σ k_i ω_i on ℤ^κ × 0; complement + `LinearIndependent.sum_type` + reindex by `finSumFinEquiv`) and
  **`prop21Lin`**: W83 Prop. 2.1 for arbitrary ℂ-independent periods, (QP) stated for all Σ k_i ω_i, hypothesis
  U ≥ r² log(R/r) (W83's form). Constants c₁ = max(c₁⁰,1)·(‖A‖‖A⁻¹‖)², c₂ = 2ⁿc₂⁰, multiplier constant b‖A‖².
  Standard axioms.

### Status 2026-10-30 (continuation): concrete (QP) DONE
`ExpCoords.lean` (278 lines, standard axioms):
* `ellW L t` = (σ³, σ(σ′² − σσ″), −(2σ′³ − 3σσ′σ″ + σ²σ‴)) — entire, = (σ³, σ³℘, σ³℘′) off Λ; **`ellW_add`**:
  W_t(z + λ) = sigmaMult(λ, z)³ W_t(z) for λ ∈ Λ, sigmaMult = ε(λ)e^{η(λ)(z+λ/2)} (`sigma_add`; ℘, ℘′ periodic off Λ,
  extended to Λ by continuity and density of ℂ∖Λ).
* `exists_eta_bound`: ‖η(λ)‖ ≤ C‖λ‖ on Λ (`eta_add`, `eta_zsmul`, coordinates in `L.basis`).
* `Mono d0 d1 m D` (exponents α, β, γ with Σ_t γ_{j,t} = D), `Mono.eval` on `Tan d0 d1 m`, entire
  (`differentiable_eval`); **`Mono.eval_add_per`**: M(p + ω) = expMult(ω, p)·M(p) for ω ∈ `Per Ls`
  (G_a part of periods 0; G_m multiplier e^{2πik} = 1); **`norm_expMult_le`**: ‖expMult‖ ≤ exp(3D(ΣC_j)(‖p‖+‖ω‖)²).
* **`exists_qp_mono`**: for ℓ : ℂⁿ →L T_G and periods ω_i with ℓ ω_i ∈ Per Ls, the family M_l ∘ ℓ satisfies the
  (QP) hypothesis of `prop21Lin` with b = 3DC‖ℓ‖².

### Status 2026-10-30 (continuation): Tier 2 DONE (ℂ-dependent periods)
Files (standard axioms, no sorry): `Grid2.lean` (75 lines, `grid_interp2`: a different node set in each coordinate),
`Lattice2.lean` (333), `Reps2.lean` (228), `Prop21Lat.lean` (528).
* **2D node products without shell counting** (`Lattice2.lean`). Nodes ((p₁−A)α + (p₂−A)β)/K, p ∈ [0,2A]², D = Im(ᾱβ) ≠ 0.
  We have |uα + vβ| ≥ (|D|/(|α|+|β|))·max(|u|,|v|) (via Im(ᾱw) = yD and Im(β̄w) = −xD), and for integers (u,v) ≠ 0,
  max(|u|,|v|)² ≥ max(|u|,1)·max(|v|,1). The latter splits into one-variable factorial products, which gives
  `prod_lat_lower` and **`norm_lagBasis_lat_le`**: |ℓ_p(w)| ≤ (max(X,1)e²)^{(2A+1)²} for |w| ≤ ρ,
  X = (ρK + (|α|+|β|)A)/(c₀A).
* **Class count without Smith normal form** (`Reps2.lean`). Periods ω_i = `perVec α β (P i)` with integer coordinates;
  a κ×κ minor M = `minorMat P I` with d = det M ≠ 0. Write v(I_t) = Kd·u_t + w⁰_t, set y = adj(M)u, and subtract
  K Σ y_i P_i; since M·adj M = d·1, the remainder has s(I_t) = w⁰_t ∈ [0, |Kd|) (**`lat_decomp`**, all bounds are
  integer inequalities). `card_condIdx2` = |Kd|^κ (2B+1)^{2n−κ}.
* **`prop21Lat`**: W83 Prop. 2.1 for periods in Π_j(ℤα_j + ℤβ_j) of rank κ (nonzero minor), possibly ℂ-dependent,
  κ ≤ 2n. Hypotheses as in W83 (U ≥ r² log(R/r)), single multiplier constant b with b r² ≤ a U, and (QP) for all
  Σ k_i ω_i. Grid: (2A+1)² nodes per coordinate, A = ⌈√(10U/ℓ)⌉, K = ⌈SA/r⌉. Constants depend on α, β, P, I, a.
* Abelian-class bridge (what remains to *apply* Tier 2 to `Theorem41Abelian`):
  (a) R-independent periods in Λ̂ ⇒ some κ×κ minor of P is nonzero (rank over ℚ; ≈ 100 lines).
  (b) Choose n coordinate forms of T_G whose restrictions to V form a basis of V*, and complete 0 ⊂ ℤ + iℤ,
      2πiℤ ⊂ ℤ + 2πiℤ, Λ_j to lattices (α_j, β_j). This gives the linear iso ℂⁿ ≅ V, and the periods get integer
      coordinates P (≈ 300 lines).
  (c) Growth Σ_λ |M_λ ∘ ℓ|_R ≤ e^U for the monomials (`GrowthLE` of σ, σ′, σ″, σ‴ is in the library; ≈ 200 lines,
      part of D4's parameter bookkeeping).
  (QP) for these functions is `exists_qp_mono` (concrete) composed with the iso. Vector extensions (class 𝒞):
  the risk noted in §3 O2 is unchanged.
* `#print axioms`: `prop21Lat`, `prop21Lin`, `prop21`, `exists_qp_mono`, `Mono.eval_add_per`:
  [propext, Classical.choice, Quot.sound].

### Status 2026-10-30 (continuation): bridge (a)–(c) and `prop21_G` DONE
Files (standard axioms, no sorry): `Minor.lean` (86), `CoordsV.lean` (135), `MonoGrowth.lean` (140), `PropG.lean` (238).
* (a) `exists_minor_isUnit` (over a field: linearly independent Q₁..Q_κ ∈ K^ι give an injective I with
  (Q_i(I_t)) invertible; columns rank κ ⇒ rows span K^κ ⇒ `exists_linearIndependent'` rows) and
  **`exists_minor_ne_zero`** (ℤ version via `LinearIndependent.iff_fractionRing` and `RingHom.map_det`).
* (b) `tcoord` (the d₀+d₁+m coordinate forms of T_G); **`exists_coordsV`**: n of them restrict to an isomorphism
  ψ : V ≃ ℂⁿ (field minor applied to a basis of V, then `LinearMap.linearEquivOfInjective`). Lattice completion
  `latA`/`latB` (G_a: 1, i; G_m: 1, 2πi; E_j: ω₁, ω₂), `latD` (Im(ᾱβ) ≠ 0; elliptic case from `PeriodPair.indep`
  via `im_conj_mul_ne_zero`), **`per_coord`** (each coordinate of a period of G is a ℤ-combination of latA, latB).
* (c) `growthLE_ellW`, `exists_ellW_growth`, **`exists_mono_growth`**: |M(p)| ≤ (1+|p|)^{D₀} e^{D₁|p|} e^{mDc_W(1+|p|)²};
  **`exists_sum_mono_le_exp`**: Σ_l |M_l|_R ≤ e^U if log L + D₀ log(1+R) + D₁R + mDc_W(1+R)² ≤ U.
* **`prop21_G`** (setting of `LSG/W88/Statement.lean`): Ls, V ≤ Tan d0 d1 m with finrank n, ω : Fin κ → Tan with
  ω_i ∈ V, ω_i ∈ Per Ls, `LinearIndependent ℤ ω`. ∃ c₁ c₂ > 0, ∀ L D Δ U R r and μs : Fin L → Mono d0 d1 m D:
  1 ≤ L, 0 < Δ ≤ U, c₁ ≤ R/r, c₁ ≤ r, **c₁ r² log(R/r) ≤ U**, D r² ≤ U, Σ_l |M_l| ≤ e^U on V ∩ B(0,R),
  c₂U^{n+1} ≤ LΔ r^κ log(R/r)ⁿ ⟹ ∃ p : Fin L → ℤ, p ≠ 0, |p_l| ≤ e^Δ, |Σ p_l M_l(z)| ≤ e^{−U} for z ∈ V, ‖z‖ ≤ r.
  **`prop21_G_deg`**: the same with the growth hypothesis replaced by degree bounds (Σα ≤ D₀, Σβ ≤ D₁) and
  log L + D₀ log(1+R) + D₁R + mDc_W(1+R)² ≤ U.
  Proof: coordinates (b) → periods are `perVec` of integer vectors P; ℤ-independence of P from that of ω (ψ injective);
  minor (a); (QP) from `exists_qp_mono_uniform` (constant independent of D) with b = 3DC‖ℓ‖²; `prop21Lat` in the
  coordinates ℓ = V.subtype ∘ ψ⁻¹; radii rescaled by ‖ℓ‖, ‖ψ‖.
* **Deviation from W83's hypothesis shape:** U ≥ r² log(R/r) becomes c₁ r² log(R/r) ≤ U, because the linear
  coordinates ℂⁿ ≅ V rescale r by ‖ψ‖ (unavoidable for a statement on balls of V). In W83 Prop. 2.4 / Lemma U
  (r = ν²S, R = ν³S, U = ν⁶Δ) the constant is absorbed by ν, like every other constant there.
* G_a/G_m degrees enter only through the growth hypothesis (W83's Σ|ψ_λ|_R ≤ e^U); the elliptic blocks are
  homogeneous of exact degree D (W83's D = D₂°).
