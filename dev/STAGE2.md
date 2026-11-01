# Stage 2 blueprint: the multiplicity estimate on G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m

Started 2026-10-30. Labels as in PLAN.md. This is the design for Philippon's multiplicity estimate (Philippon 1986,
Thm 2.1; Roy's affine treatment, DALAG Ch. 5, 8, as ported in StrongSix `M2/`) with elliptic factors. Vector
extensions (E^♮, for MG♮/MX/MX′) are a later extension of the same design (§7).

## 1. Reuse from StrongSix as a Lake dependency (unchanged)

StrongSix's generic layers are stated for an arbitrary polynomial ring `K[σ]` with a block map `β : σ → ι`:
`Filtered` (block-degree filtration, splitting lemma), `Hilbert`, `HilbertPoly`, `HData`, `Veronese` (filtered
Hilbert functions are eventually polynomial), `Degree`, `Section`, `HDim` (Hilbert dimension and degree), `Bridge`,
`BridgeLow` (`hdim L + ht L = card σ`), `Bezout` (Roy Thm 8.4: `deg_D (I + (F)) ≤ deg_D I` for a complete
intersection I), the generic part of `Wustholz` (Roy 8.16, 8.18 along words), `CM/` (Macaulay unmixedness).
**Check first** (step S2.0): which of these are generic in σ/β/D (D : ι → ℕ) and which hard-code `Fin 2` blocks or
`V3 d₀ d₁`; anything hard-coded gets a generic version in NEW StrongSix files (`M2/WustholzGen.lean`, `M2/SeparateGen.lean`;
existing StrongSix files untouched), else in `LSG/ME/`.

## 2. Coordinates: the multi-cone model [Design]

* Variables `Var d₀ d₁ m`: `X i` (G_a), `Y j`, `Z j` (G_m, with `Y Z = 1`), and for each elliptic factor k three cone
  coordinates `U k, V k, W k` (the point (U:V:W) of E_k ⊂ ℙ², Weierstrass form
  `F_k = V²W − 4U³ + g₂U W² + g₃W³`). Blocks: `X`, `(Y, Z)`, and one block per elliptic factor; degrees
  `D = (D₀, D₁, D₂, …, D₂)`.
* `I_G = (Y_j Z_j − 1, F_k)`: a complete intersection (height d₁ + m), prime (tensor product of domains over an
  algebraically closed field; F_k irreducible).
* Points of G: `GPt K d₀ d₁ m = (Fin d₀ → K) × (Fin d₁ → Kˣ) × (Fin m → E_k-points)`, E-points as Mathlib
  `WeierstrassCurve.Point` (for the group law) with representatives (x : y : 1) and (0 : 1 : 0).
  `vanish E` = polynomials vanishing at **every cone representative** of every point of E (a homogeneous ideal in each
  elliptic block). Affine dimensions of cone ideals are projective dimensions + m, uniformly.
* Projective Nullstellensatz per block: for a prime p ⊇ I_G not containing any block irrelevant ideal
  `(U_k, V_k, W_k)` ("relevant"), `vanish (zeros p) = p`. Irrelevant components are removed by saturation.

## 3. Translations and derivations [Design]

* **Addition laws** (`LSG/Elliptic/AdditionLaws.lean`): a complete system of addition laws of bidegree (2,2) for
  y² = 4x³ − g₂x − g₃ (Lange–Ruppert 1985; Bosma–Lenstra 1995: two laws suffice for any Weierstrass curve). For each
  law A⁽ⁱ⁾ = (A_U, A_V, A_W): (a) `F(A⁽ⁱ⁾(P, Q)) ∈ (F(P), F(Q))` as a polynomial identity; (b) on E × E, A⁽ⁱ⁾(P, Q)
  is 0 or represents P + Q (compare with Mathlib's group law); (c) for all P, Q some A⁽ⁱ⁾(P, Q) ≠ 0.
* Translation by g: `τ_g⁽ⁱ⁾` = the K-algebra map substituting (U, V, W) ↦ A⁽ⁱ⁾((U, V, W), g) in each elliptic block
  (X ↦ X + g_x, Y ↦ g_y Y, Z ↦ g_y⁻¹ Z as in StrongSix). Block degree ×2 on elliptic blocks (Philippon's c₁ = 2).
  The ideal translate `τ_g J = I_G + (τ_g⁽ⁱ⁾ P : P ∈ J, all i)` has `zeros (τ_g J) = zeros J − g`.
* **Invariant derivation** on E: D(x) = y, D(y) = 6x² − g₂/2. On the cone it is induced by three homogeneous
  derivations of degree +1 (c₂ = 1), one per chart, each mapping (F) into (F) (checked by hand 2026-10-30):
  - W·D: `U ↦ V W`, `V ↦ 6U² − (g₂/2) W²`, `W ↦ 0` (exactly D̃F = 0);
  - U·D (mod F): `U ↦ U V`, `V ↦ (3/2)V² + g₂ U W + (3/2) g₃ W²`, `W ↦ 0`;
  - V·D (mod F): `U ↦ −V²/2 − g₂ U W − (3/2) g₃ W²`, `V ↦ 0`, `W ↦ −6U² + (g₂/2) W²`.
  "Vanishing to order T along W at g" uses, in each elliptic block, a chart form nonzero at g_k; it does not depend on
  the choice (Leibniz along words). Words, not monomials in commuting derivations, as in StrongSix.

## 4. The statement `LSG.ME.MultEstAb K` [Design; mirrors `StrongSix.Thm1.MultEst`]

For K algebraically closed of characteristic 0 (used with K = ℚ̄ ⊂ ℂ and K = ℂ), curves with invariants in K:
if P ≠ 0 has block degrees ≤ (D₀, D₁, D₂) (homogeneous of degree D₂ in each elliptic block) and vanishes to order
≥ nT + 1 along W at every point of Σ(n) (0 ∈ Σ, n = d₀ + d₁ + m), then there is a connected algebraic subgroup
G′ ≠ G, given by tangent data (W88-style, §5), with
  T^{c} · #((Σ + G′)/G′) · D₀^{t₀} D₁^{t₁} D₂^{t₂} ≤ C · D₀^{d₀} D₁^{d₁} D₂^{m},
c = dim W − dim (W ∩ T_{G′}), t₀ = dim π₀(G′), t₁ = dim π₁(G′), t₂ = dim G′ − t₀ − t₁.

## 5. The obstruction subgroup (risk R1; analysis in PLAN.md §0.6)

Proof-internal object: G′ = connected component of the stabiliser of a relevant prime. Needed facts, with route:
| fact | route | est. |
|---|---|---|
| Zariski tangent space at 0 = analytic Lie algebra T′ (over ℂ) | translation-invariance of I(G′) ⇒ D_v-stable (PLAN R1 (c)) | 0.8k |
| exp⁻¹(G′) = T′ + Ω + finite; T′ complex; T′ ∩ (0 × ℂ^m) abelian tangent | `Subgroups/Closed`, `Torus` (done) + identity theorem | 0.6k |
| π_L(G′) Zariski closed, hence h₀ × T_U (StrongSix `classify`) | projective elimination along (ℙ²)^m (resultant-free: degree-bounded Nullstellensatz) | 1.5k |
| algebraic dim G′ = dim T′ | ≥: projection argument (STAGE2 §4 lower bound); ≤: a smooth point (generic smoothness in char 0) + homogeneity | 2k |
| H(G′; D) ≥ c D₀^{t₀} D₁^{t₁} D₂^{t₂} | (π_L, π_{J₂}) maps G′ onto π_L(G′) × E^{J₂} (uses the coset structure of G′ ∩ (0 × A)) | 0.8k |
| Wüstholz transversals Q_j | from T′ = h₀ × U^⊥ data on the linear side; on the abelian side via kernels of End-linear maps (CM) or the chart forms of §3 | 1.5k |
| product decomposition (G′ = (G′ ∩ L) × (G′ ∩ A)) | **open**: analytic arguments alone are insufficient (Tate graph); candidates in PLAN R1. Not needed for the W88-style statement; needed (or replaced by a general-G′ version of the paper's tables) for M* | ? |

## 6. Module plan `LSG/ME/` and order of work

S2.0 audit of StrongSix generic layers (§1). S2.1 `Elliptic/AdditionLaws` (§3; independent). S2.2 multi-cone
geometry: `Geom` (points, cone representatives, `vanish`, `zeros`), primality of I_G, relevant-prime Nullstellensatz.
S2.3 `Transl`, `Deriv` with charts. S2.4 `Elimination` (independent). S2.5 `Smooth` (generic smoothness; independent).
S2.6 subgroup layer (§5). S2.7 `Separate`, `Pairing` (cosets, transversals). S2.8 `Chain`, `MainB` (Roy §8.4.1
generalised), `Final`: `MultEstAb ℂ`, `MultEstAb ℚ̄`. S2.9 specialisation lemma: `MultEstAb` with m = 0 ⇒
`StrongSix.Thm1.MultEst`.
Parallelisable now: S2.0, S2.1, S2.4, S2.5. Then S2.2–S2.3, then S2.6–S2.8.

## 7. Vector extensions (later)

E^♮ points (P, t), group law (P, t) + (Q, s) = (P + Q, t + s + c(P, Q)), c = ½(y_P − y_Q)/(x_P − x_Q) generically
(the classical ζ(u+v) − ζ(u) − ζ(v)); embedded in ℙ² × ℙ¹ with addition laws obtained from those of E by clearing the
denominator of c; quotients by fibre vector subgroups via a matrix. Same layers as above; the classification of
subgroups follows the paper's tables (types A–E).

## 8. S2.0 audit result (2026-10-30)
Fully generic in StrongSix (σ, β : σ → ι, D : ι → ℕ, any ideal; reuse unchanged): `Hilbert`, `HilbertPoly`, `HData`,
`Degree`, `Filtered`, `Veronese` (`hfun`), `Section` (`hfun_section`), `HDim` (`hdata`, `hdim_section_lt`,
`hdim_lt_of_lt`), `Bridge`/`BridgeLow` (`hdim_add_height_eq`), `Bezout` (`bezout`: any complete intersection list
`l` with `height = length` — Weierstrass cubics and YZ − 1 are fine; added set of block degree ≤ D), `Component`
l. 28–90 (`exists_prime_hdim`, …), `Wustholz` l. 28–221 (`DL`, `qprod`, Roy 8.16, `indep_mod`), `Pairing.exists_biorth`,
`CM/*`. Field needs: `Infinite K` for `bezout`, `CharZero` for Wüstholz, `IsAlgClosed` for the component layer.
To generalise in StrongSix (user-approved): `wustholz_count`/`wustholz` (hard-coded `V3`, `Fin 2`; ~105 lines,
mechanical), the point-agnostic core of `Separate` (`restrE` … `hfun_union_le`, ~150 lines), `Pairing.exists_c0`.
To redesign in LSG (translations are not degree-preserving algebra automorphisms with elliptic factors): `Transl`,
`Component` l. 92–341, `Separate` (rest), `Chain`, `MainB`.

## 9. Progress 2026-10-30
* S2.4 elimination DONE (`LSG/ME/Elimination.lean`: `isClosed_proj`, `isClosed_proj_blocks`, `isClosed_proj_sigma`).
* S2.5 smooth points DONE (`LSG/ME/SmoothPoint.lean`: `trdeg_le_finrank_tangentSpace`, `exists_smooth_point`, with
  e = `Algebra.trdeg K (K[X]/p)`). Bridge (i) DONE: `LSG/ME/DimTrdeg.lean` `hdim_eq_trdeg`, `trdeg_add_height_eq`,
  `ringKrullDim_quotient_eq_trdeg` (any field). Former open bridges for S2.6: (i) trdeg(K[X]/p) = hdim p (StrongSix's Hilbert dimension;
  via `hdim_add_height_eq` and trdeg = card σ − ht p, e.g. by Noether normalisation — not in Mathlib v4.35);
  (ii) homogeneity: translate a smooth point of a Zariski-closed subgroup to the identity.
* S2.0 generic StrongSix files DONE (`StrongSix/M2/WustholzGen.lean`, `SeparateGen.lean`, StrongSix commit 458219a).
* S2.1 addition laws DONE (`LSG/Elliptic/AdditionLaws*.lean`: law₁ = Mathlib addXYZ ×4, law₂ = Bosma–Lenstra/RCB ×32,
  bidegree (2,2) over ℤ[g₂,g₃]; `Fv_lawᵢ_mem`, `toPoint_lawᵢ`, `law_complete`, `toPoint_eq_iff`, `rep`).
* S2.6 subgroup layer, items 1–4 DONE (`StabG`, `SubgroupProj`, `SubgroupLie`, `SubgroupExpSurj`, `SubgroupLift`,
  `SubgroupDhat`, `SubgroupTangent`): stabiliser of a closed set is a closed subgroup (Noetherian argument, any ideal);
  π_L(H) closed and = prodSet (StrongSix `classify`); exp⁻¹(H) closed, contains Per, complex linear part `lieAlg`,
  abelian part `IsAbelianTangent`; `mem_TZ_iff` (Zariski tangent at 0 = lieAlg); exp_G surjective.
  Open: item 5 (hdim H⁰ = dim lieAlg; H⁰ definition; smooth point transport; ~1–1.5k) and item 6 (Hilbert lower
  bound with projection exponents).
* S2.6 items 5–6 DONE (2026-10-30, uncommitted; `SubgroupComp`, `SubgroupGraded`, `SubgroupIrred`, `SubgroupTanSp`,
  `SubgroupDim`, `SubgroupConeE`, `SubgroupHilbAux`, `SubgroupHilb`; 1.9k lines, standard axioms). H⁰ := zcl(exp lieAlg)
  (`H0`, closed subgroup ⊆ H, `vanish_H0_isPrime` via lines + `vanish {g}` prime); `hdim_H0`: hdata(vanish H⁰).1 =
  dim lieAlg + m (≤ at the identity via `TZ = lieAlg`, ≥ at a smooth point with all V_k ≠ 0 rescaled to a V-normalised
  point; no τ-transport of tangent spaces needed); `finite_cosets_H0` (components + `vanish_gtransl_isPrime`);
  `hfun_H0_ge(')`: H(L⁰;tD₀,tD₁)·((tD₂+1)²)^{t₂} ≤ H(vanish H⁰;tD), L⁰ = V × T_{lsat(qspan Λ)} ⊆ π_L(H⁰), t₂ = dim of
  the abelian tangent of H⁰ (cone monomials on E: (n+1)² independent; product independence; `exists_H0_point`).
  Mathlib's graded-prime criterion with `Lex (Fin m → ℕ)` times out (Pi.Lex instance defeq); avoided.

## 10. Design correction (2026-10-30): Philippon's operators instead of derivation words in the chain
* Chain v1 (`Order*.lean`, `Chain.lean`, committed) generates L_r by derivation words D_l P. With elliptic factors each
  chart derivation raises elliptic degree by 1, so the generators have elliptic degree 2(D₂ + rT). Bézout then bounds
  everything in the grading D′ ~ D₂ + nT, i.e. the multiplicity estimate holds with D₂ replaced by D₂ + nT. W88's
  parameters have T log S = D₂S², so T ≫ D₂: fatal. (Roy's affine version is fine for linear groups only because
  their invariant derivations preserve degree.) Also v1's `Deriv.VanishesAlong` is too strong (non-homogeneous Dw at
  cone points; counterexample in the agent report); `Dh` (homogenised) is the correct derivation.
* **Fix (Philippon 1986 §4.1, Déf. 4.1–4.2, Prop. 4.3–4.4):** the operator δ^κ_g Q = ∂_z^κ Q(T(X, z))|_{z=0}, where
  T(X, z) represents (h, z) ↦ h + g + exp(z·w) by polynomials in X of *fixed* degree c_i (addition laws) with
  coefficients analytic in z. Derivatives in z hit only the coefficients, so δ^κ_g Q has degree c·D for every κ: no
  restriction on T (Philippon's remark after Cor. 2.2). Algebraically: the formal exponential of each factor —
  G_a: x + z w; G_m: y·exp(z w); E: the formal solution (s(z), 1, t(z)) of the V-chart ODE
  s′ = −1/2 − g₂ s t − (3/2) g₃ t², t′ = −6 s² + (g₂/2) t², s(0) = t(0) = 0 (coefficients in ℚ[g₂, g₃]) — composed
  with law(X, ·) (bidegree (2,2)). δ^κ_g Q = coefficient of z^κ in Q(law(X, law(rep g, P(z w)))), degree ≤ 4D.
* Derivation words (`Dh`, v1) remain the right tool inside Wüstholz's lemma (`wustholz'`): there degrees only shift t by
  S₀c₀, which does not affect leading coefficients of Hilbert polynomials (t → ∞, D fixed). The bridge needed:
  "order > k along W at g in Philippon's sense ⇒ Dh-words of length ≤ k vanish" (v1's `VanAll`/`transl_van` help).
* Product decomposition (R1, last open piece): proof found 2026-10-30 — (1) π_A(T′) is Λ-rational by a transcendence-
  degree count through the exp parametrisation plus `hdim_H0`; (2) a nontrivial graph part would give a ℂ-linear form
  on the rational space π_A(T′) with values in 2πiℤ (or 0) on its lattice, hence zero. Agent running (`Product*.lean`).
  The Tate-graph obstruction is avoided because step (2) uses that H⁰ ∩ L has finitely many components (Noetherian).
  Possible weakening of `SubgroupData`: drop `h0_rat` if Q̄-rationality of h₀ is costly (automatic for d₀ ≤ 1, which
  covers all M* applications).
* Wüstholz layer DONE (`WustAlg`, `WustCoset`, `WustTrans`, `WustId`): `wustholzM'` (D_iQ_j ≡ δ_ij·M, M a non-zero-
  divisor), `glue` (chart-dependent derivations glued with separators — a single chart fails on cosets with constant
  2-torsion coordinates), `exists_transversals`, **`wustholz_cosets`** (input: A ≤ VOg Dmix Wmix (vanish E) S₀, supplied
  by `mem_VOg_mix` from canonical-chart vanishing), `hfun_cosets_ge_subgroup`:
  #R · H(H⁰; t) ≤ 2^m · H(⋃ a + H⁰; 2t + c). `derivation_aeval` clash fixed (SmoothDeriv's is `derivation_aeval_sum`).
* **Product decomposition DONE** (`ProductRat`, `ProductGraph`): `lieAlg_eq_prod` (T′ = h₀ × U^⊥ × T′_A),
  `isAbelianTangent_comap_inAbL`, `exists_subgroupData (hrat)`, `exists_subgroupData_of_le_one` (d₀ ≤ 1). R1 closed.
  **Q̄-rationality of h₀** (`SubgroupData.h0_rat`) is false for arbitrary ℂ-subgroups (ℂ·(1, π) ⊆ G_a²) but true for
  the stabilisers that occur, which are defined over Q̄: plan (final assembly) — the chain ideals have Q̄ coefficients;
  minimal primes of J ⊗ ℂ are extensions of minimal primes of J over Q̄ (Q̄ algebraically closed); eliminants and linear
  parts of Q̄-defined sets are Q̄-defined. Statement kept as is (W88 asks G′ defined over Q̄); automatic for d₀ ≤ 1.
* **Chain v2 DONE** (`FormalExp`, `PhOpCurve`, `PhOp`, `PhOpBridge`, `PhOpTwo`, `Chain2`): formal ODE solver and
  formal exponentials; `phOp` with **elliptic degree ≤ 2D for every κ** (`phOp_mem_FLE`); `zeros_phOp` (Philippon
  Prop. 4.4); `OrdGt` (formal order along W, law-independent); `gensR2 ⊆ FLE (dblE D)`, generators of A2 ⊆ FLE(4D);
  `exists_flat2`; `hAVO2`; bridge `vanCan_of_ordGt`/`ordGt_of_vanCan` to Dh-words (feeds `mem_VOg_mix` →
  `wustholz_cosets`). Remaining for MultEst: the final assembly (Roy §8.4.1 / MainB with these pieces, the component
  lemma, final arithmetic) and Q̄-descent for h₀.

## 11. MultEstAb: statement, design correction (irrelevant components), status (2026-10-31)

### 11.1 Done (sorry-free, standard axioms)
* `LSG/ME/SubgroupHilb2.lean` (333 l.): **`hfun_H0_ge''`** (the corrected Hilbert lower bound of degree
  `t₀ + t₁ + t₂ + m`: extra factor `(tD₂+1)^{m − t₂}` from the free cone scalings of the blocks `k ∉ ι`),
  via `indep_H0_core` (the old independence, for any `L0 ⊆ π_L(H⁰)`), `sep_free_scalings` (if
  `Σ_γ B_γ ∏_{k∈J} V_k^{γ_k} ∈ vanish E` with `B_γ` free of the blocks `J`, then `B_γ ∏ V_k ∈ vanish E`; proof by
  zero scalings + `MvPolynomial.funext` + coefficient extraction), primality of `vanish H⁰` and `V_k ∉ vanish H⁰`;
  `hfun_H0_ge_gen`; `prodSet_ML_subset_projL` (so the exponents can be taken from the product decomposition:
  `t₀ = dim (linV ML) = dim h₀`, `U = qspan (latt ML)`).
* `LSG/ME/MultEstStmt.lean` (141 l.): **`ObstrData`** (h₀, U, t, `IsAbelianTangent`, `grp = zcl (exp_G T_{G′})`, a
  Zariski-closed subgroup with Lie algebra `T_{G′}` (`lie`)), `ObstrData.tan`, `Proper := tan ≠ ⊤`,
  `toSubgroupData` (under `RationalOverQbar h0`; automatic for d₀ ≤ 1), **`ObstrData.ofSubgroup`** (from a closed
  subgroup `H`: `grp = H⁰`, `tan = lieAlg H`), `ofSubgroup_proper` (`H ≠ G ⇒ Proper`), and the statement
  **`MultEstAb`** (exact text in the file; inequivalence = `g − g′ ∉ O.grp`).
* `LSG/ME/MainAbChain.lean` (213 l.): relevant radicals `relI L = I(Z(L))`; **`exists_flat_rel`** (pigeonhole on the
  relevant radicals of chain v2); **`exists_relevant_prime`** (prime `p ⊇ relI L`, same hdim, `vanish (zeros p) = p`,
  via `exists_components`); **`component_rel`** (Roy's component step: `{h | h + V ⊆ Z(L)}` is covered by finitely
  many cosets of `stabG V` when `hdim I(V) = hdim relI L`); `zeros_transl_subset` (`h ∈ Z(A) ⇒ h + V ⊆ Z(L_r)`).
* `LSG/ME/Slice.lean` (288 l.): affine slices `sl α I = I + (ℓ_k − 1)`, `ℓ_k = V_k + α_k W_k`; `nrm`, `vanishS`,
  `sl_vanish_le`; **`hom_mem_vanish_of_mem_sl`**; **`hfun_le_sl`**: `H(vanish E; t) ≤ ∏_k (tD_k+1) · H(sl α (vanish E); t)`
  (`vanish E` prime, `ℓ_k ∉ vanish E`); **`hfun_sl_coset_ge`**: polynomial lower bound of degree `t₀+t₁+t₂` for
  `H(sl α I(a + H⁰); 2t)` (from `hfun_H0_ge''`, `hfun_le_transl`, `hfun_le_sl`).
* `LSG/ME/SliceIG.lean` (423 l.): (S3) done: **`hfun_slIG_le`** (standard monomials, measure
  `Σ (Y+Z+U+V)`-exponents), `lGs`, `slIG_eq_ofList`, `slIG_ne_top`, **`hdata_slIG`** (`hdim (sl α I_G) = d₀+d₁+m`,
  `deg ≤ (d₀+d₁+m)! D_x^{d₀} (2D_yz)^{d₁} ∏ 3 D_k`, hdim lower bound via Krull
  `Ideal.height_span_le_card_of_span_ne_top` + `hdim_add_height_eq`), **`height_slIG`** (complete intersection).
* `LSG/ME/MainAbWIP.lean`: superseded by `MainAb.lean` and deleted (2026-10-31).
* Engineering: `FormalExp.chartAt_zero` renamed `chartAt_zero_gen` (clashed with `SubgroupTangent.chartAt_zero`;
  the subgroup layer and chain v2 can now be imported together).

### 11.2 Design flaw found: irrelevant components dominate the filtered Hilbert functions
Every generator of `L_r = Lr2 r` and of Roy's `A` is multihomogeneous of **positive** degree in every elliptic
block (`P` has degree `D₂ ≥ 1` there; `phOp` and `τ` substitute `law(X_k, ·)`, homogeneous of degree 2 in `X_k`).
Hence the affine locus `{X_k = 0} × {Y Z = 1} × ∏_{k' ≠ k} cone(E_{k'}) × 𝔸^{d₀}` (dimension `d₀ + d₁ + 2m − 2`)
lies in the affine zero set of `L_r` and of `A` for every `k`. So for `m ≥ 1`:
* `hdim L_r ≥ d₀ + d₁ + 2m − 2` for all r: `exists_flat2` is true but useless, and a prime `p ⊇ L_{r+1}` with
  `hdim p = hdim L_r` (`exists_prime_hdim`) can be irrelevant (`zeros p = ∅`, `stabG ∅ = G`);
* `hdim A` can exceed `hdim I(⋃ cosets of GV)` (e.g. `GV` finite: relevant dim `m`, irrelevant `d₀+d₁+2m−2`), so
  StrongSix's steps `hdimA = hdim J` (`deg_le_of_hfun` with Wüstholz) and the Bézout comparison fail;
* the Nullstellensatz `vanish (zeros L) = √L` (used in MainB step 4) fails for the cone model.
(In Philippon's multiprojective setting irrelevant primes have zero homogeneous Hilbert function; StrongSix's
filtered/affine setting had no vertices.) `hfun_H0_ge''`, the subgroup layer, Wüstholz identity data, `hAVO2`,
`zeros_phOp` are unaffected (they concern relevant objects or zero sets).

Remaining order of work: S1 → S5 → S4 → S6. Everything except the assembly is independent of the choice of α
(the lemmas take α and the hypotheses `ℓ_k ∉ p` as arguments).

### 11.3 The fix: relevant radicals for geometry, affine slices for Hilbert functions
* Geometry (done, `MainAbChain`): pigeonhole on `relI L_r`, relevant prime `p`, component step with `relI L_r`.
* Hilbert functions: pick `α : Fin m → ℂ` such that no relevant minimal prime of the finitely many ideals involved
  (`relI A`, `J = I(⋃_{a∈R'} (a + H⁰))` and its cosets) contains some `ℓ_k` (finitely many affine points of each
  `E_k` to avoid: `y_P ≠ −α_k`; the identity always has `ℓ_k = 1`). Then compare **sliced** ideals in StrongSix's
  filtered setting (same ring `K[Var]`, same `blk`, grading `D = 4 • Dfun D₀ D₁ D₂`):
  - (S1) slice Nullstellensatz: for `I = I_G + (multihomogeneous gens)`, the affine zeros of `sl α I` are the
    normalised representatives `nrm α g` of the `g ∈ Z(I)` with all `lval α g k ≠ 0`; `√(sl α I) = vanishS α (Z(I))`
    (Mathlib's `vanishingIdeal_zeroLocus_eq_radical`); `hdim (sl α p) = hdim p − m` for relevant primes `p` with
    `ℓ_k ∉ p` (slicing a cone by a hyperplane section per block; via `hdim_eq_trdeg`), and `vanishS` of a finite
    union of cosets has the hdim of one coset. [~400 l.]
  - (S2) `hfun_le_sl`, `hfun_sl_coset_ge` [done].
  - (S3) [DONE, `SliceIG`] `sl α I_G = Ideal.ofList (lG ++ ofFn (ℓ_k − 1))` is a complete intersection (height `d₁ + 2m`: `≤` Krull
    `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`, `≥` from (S3′) + `hdim_add_height_eq`) and (S3′)
    `H(sl α I_G; t) ≤ (tD₀+1)^{d₀} (2tD₁+1)^{d₁} (3tD₂+3)^m` by standard monomials (reductions `Y Z → 1`,
    `V → 1 − α W`, `U³ → ¼(V²W + g₂UW² + g₃W³)`, measure `Σ (U + V + Y + Z)`-exponents; standard monomials have no
    `V`, `U`-exponent ≤ 2, `min(Y, Z) = 0`), so `deg (sl α I_G) ≤ (d₀+d₁+m)! D₀^{d₀} (2D₁)^{d₁} (3D₂)^m` (copy
    StrongSix `hfun_IG_le`/`hdata_IG`). [~400 l.]
  - (S4) sliced Wüstholz: `wustholzM'` for `J_α = sl α J` with the sliced glued derivations
    `D'ᵢ = Dᵢ − Σ_k (Dᵢ ℓ_k) · Eul_k` (`Dᵢ` from `exists_transversals`, `Eul_k` the Euler derivation of block k;
    `D'ᵢ (ℓ_k − 1) ∈ (ℓ_k − 1)`, `Eul_k` preserves `vanish E` (`comp_mem_vanish`) and commutes with `Dh` up to `Dh`);
    `Qⱼ ∈ vanish E ⊆ J_α`, `D'ᵢQⱼ ≡ δᵢⱼ M`, `M` a non-zero-divisor mod `J_α` (take `M` multihomogeneous); and
    `sl α A ≤ VOg D' J_α T` from `A ≤ ordIdeal W T (⋃ s + GV)` (`vanCan_of_ordGt`, `mem_VOg_mix`). [~500 l.]
  - (S5) cosets: `hfun_sum_cosets_ge` for the sliced ideals `sl α I(a + H⁰)` (the separator proof is generic:
    `hfun_inter_ge` with a separator that is a non-zero-divisor) + `hfun_sl_coset_ge` per coset. Needed lemma:
    `sl α p` (or `vanishS α (zeros p)`) is prime for a relevant prime `p` with all `ℓ_k ∉ p` (dehomogenisation:
    `K[Var]/sl α p ≅ ((K[Var]/p)[ℓ⁻¹])_0`; elementary route: for `P Q` with `PQ ∈ sl α p`, homogenise both with powers
    of `ℓ` and use `hom_mem_vanish_of_mem_sl`). [~250 l.]
  - (S6) assembly in `MainAbWIP` (MainB steps 4–9 with `sl α`): `hdim (sl α A) = hdim (sl α J)` (S1),
    A1 Wüstholz (S4), A2 cosets (S5), A3 `bezout` for `sl α A = sl α I_G ⊔ span (τ-translates of gensR2)`
    (generators in `FLE (4 • Dfun)` by `transl_gensR2_mem_FLE`, `dblE_dblE_le`), A4 (S3), A5 `hfun_sl_coset_ge`;
    dimensions: `hdim (sl α I_G) = d₀ + d₁ + m`, `hdim (sl α I(H⁰)) = dim lieAlg = t₀ + t₁ + t₂`; then the
    final arithmetic (adapt StrongSix `final_arith`: `D₂`-exponents `t₂` vs `m`; constant `C` absorbs
    `4^{…}`, `2^m (2·)^{…}`, `3^m`, factorials, `ℓ^ℓ`). [~600 l.]

### 11.4 (S4) sliced Wüstholz: DONE (2026-10-31, S4 agent; `SliceWust.lean`, `SliceWustCoset.lean`)
* **`wustholz_cosets_sl`** (`SliceWustCoset`): same hypotheses as `wustholz_cosets` plus `α` with
  `lsl α k ∉ vanish (gtransl a (H0 …))` for all `a ∈ R`, `k`. Conclusion:
  `∃ c0, ∀ A S0 k, ℓ k ≤ S0 → A ≤ VOg (Dmix Ls) (Wmix W) (vanish E) S0 → ∀ t,
   (k+1)^ℓ · hfun blk D ℂ (sl α (vanish E)) t ≤ hfun blk D ℂ (sl α A) (t + S0 c0)`, `E = ⋃_{a∈R} (a + H⁰)`.
  `c0` depends on `(H, W, R, D, α)` (not on `A, S0, k, t`); α is fixed before `t → ∞`, so this is harmless.
* Abstract core **`wustholz_sl_of_data`** (`SliceWust`): any Euler-stable `J`, glued data `(Dᵢ, Qⱼ, M)` mod `J` with
  `M` a non-zero-divisor mod `sl α J`, `Dᵢ` lowering `VOg Dw Ws J` by one, `[Eul_k, Dw] = Dw`.
* Corrections to the §11.3 (S4) plan:
  - `D′ᵢ ℓ_k = Dᵢℓ_k (1 − ℓ_k)` (not 0: `Eul_k ℓ_k = ℓ_k`); still `D′ᵢ (ℓ_k − 1) ∈ L := (ℓ_k − 1)_k`, so `D′ᵢ L ⊆ L`
    (`Dsl_mem_Lsl`). `[Eul_k, Dh ch w] = Dh ch w` holds exactly (`Eul_Dh`), so `Eul_k` preserves every `VOg`.
  - **No primality of `sl α p` is needed** for the multiplier: `nzd_sl` — a *multihomogeneous* `M ∉ I(C_a)` (all a) is a
    non-zero-divisor mod `sl α I(⋃ C_a)` (homogenise `x` mod `L` with powers of `ℓ`, `exists_hom_sl`, then
    `hom_mem_vanish_of_mem_sl` per coset). The price: `M` must be multihomogeneous, so the transversal data were
    rebuilt (`exists_transversals_sl`): `N = det` is homogeneous (`exists_identity_data_hom`), the transported
    `N′ = Lc_{chartAt σ} τN` has degree `1 + 2e` for every coset (`transport_hom`), separators are replaced by
    homogeneous components (`exists_hom_sep`) and balanced to a common degree by powers `ℓ^c` (`lpow`; uses `ℓ_k ∉ I(C_a)`).
  - **For S5:** `nzd_sl` with `s = {a}` also gives the non-zero-divisor separators that `hfun_inter_ge` needs for the
    sliced coset sum (take homogeneous separators, `exists_hom_sep`), again without primality of `sl α p`. Note
    `sl α (I₁ ⊓ I₂) ≤ sl α I₁ ⊓ sl α I₂`, so a lower bound for `H(⨅_a sl α I(C_a))` bounds `H(sl α I(E))` from below.

### 11.5 **`multEstAb : MultEstAb` DONE (2026-10-31)** — sorry-free, `[propext, Classical.choice, Quot.sound]`
`LSG/ME/MainAb.lean` (332 l.), with the constant `CstAb d₀ d₁ m = n^n d₀^{d₀} d₁^{d₁} 4^m 2^n n! 4^{d₀} 8^{d₁} 12^m`
(`n = d₀+d₁+m`). Grading `D = Dfun (4D₀) (4D₁) (4D₂)`. New files of this stage (all sorry-free):
* `SliceDim.lean` (377 l., S1): partial slices `vanishP s α E` (normalised in the blocks `k ∈ s`), `homP` +
  `eval_homP`, **`vanishP_isPrime`** (by homogenisation; no kernel/localisation needed), `vanishP_mono`,
  `lsl_sub_one_(not)Mem_vanishP`, **`hdim_vanishP_add_le`** (`hdim vanishP univ + m ≤ hdim I(E)`, `m` sections with
  `hdim_section_lt`), `hom_mem_vanish_of_mem_vanishP`, `sl_vanish_le_vanishP`, `Zs`, `exists_coords_of_IG`,
  **`radical_sl`** (slice Nullstellensatz `√(sl α I) = I(Zs α I)` for `I_G ≤ I`).
* `Slice.lean`: `hfun_le_sl` generalised to **`hfun_le_of_hom`** (any ideal whose multihomogeneous elements lie in `I(E)`).
* `MainAbSlice.lean` (221 l., S5 + S6 pieces): `ordGt_of_eval_phOp`, **`Zs_subset_transl`** (normalised zeros of `A`),
  **`exists_good_alpha`** (`ℓ_k = V_k + α_k W_k` avoiding finitely many translates), `point_of_lsl_notMem`,
  **`hdim_vanishP_cosets_le`**, **`hfun_sum_cosets_P`** (S5 with the prime ideals `vanishP univ α (a + V)`; the
  §11.4 shortcut via `nzd_sl` was not needed).
* `PhOpHom.lean` (98 l.): **`isHomE_phOp`** (via `sc2`, `isWH_of_scale_two`; generators of `A` are multihomogeneous, so
  `A ≤ VOg Dmix (I(SG)) T` by `mem_VOg_mix`, as `wustholz_cosets_sl` requires).
* `MainAbAux.lean` (386 l.): `IG_le_VOg_mix`, `exists_reps_G`, `biUnion_gtransl_cover`, `coords_nscal_univ`,
  `finrank_torusLie` (from `W88.K11.finrank_annC`), `finrank_submodule_prod`, `deg_le_of_hfun'`, `lower_deg`, `lin3`,
  **`hfun_P_coset_ge`** (`(tD₀/t₀+1)^{t₀}(tD₁/t₁+1)^{t₁}(tD₂+1)^{t₂} ≤ 4^m H(vanishP univ α I(a+H⁰); 2t)`),
  `CstAb`, `final_arith_ab`.
Proof outline (`MainAb`): chain + relevant pigeonhole → relevant prime `p`, `GV = stabG Z(p)`, `H⁰` → Roy's `A`,
`A ≤ VOg` → component step → cosets (`finite_cosets_H0`, distinct reps `Rs`) → `α` good for all cosets →
`hdim (sl α A) ≤ dim T′` (`radical_sl`, `Zs_subset_transl`, `component_rel`, `hdim_vanishP_cosets_le`, `hdim_H0`) and
`hdim (sl α I(SG)) ≥ t₀+t₁+t₂ = dim T′` with the degree bound (coset count, `hfun_P_coset_ge`, `lower_deg`) →
Wüstholz `wustholz_cosets_sl` with `S0 = T`, `k = T/ℓ` → Bézout for `sl α A = Ideal.ofList lGs ⊔ span F₀`
(`height_slIG`) → `hdata_slIG` → `final_arith_ab`; `|F| ≤ |Rs|`.
Remaining (outside `MultEstAb`): `ℚ̄`-rationality of `h₀` for `toSubgroupData` when `d₀ ≥ 2`; the Stage 3 use.
