# LSG: Waldschmidt's linear subgroup theorem with period term, for groups with CM elliptic factors, in Lean 4

Started 2026-10-30. Lean 4 + Mathlib v4.35.0 (same pin as `lean_beta/`, `schanuel/six_exp/lean/` = StrongSix,
`lean_cm4e/`). `.lake/packages` is a directory junction to StrongSix's packages (no second Mathlib download).
Final product: standard axioms only, no `sorry`, no `axiom`, no `native_decide`.

Labels: [Lit] read in a source, [Design] my choice, to be validated in Lean, [Est] line estimate.

---------------------------------------------------------------------------------------------------------------------

## Stage 0: feasibility audit

### 0.1 What has to be proved (the minimal target)

The paper `schanuel/five_exp/pilot_thmM/paper/paper.tex` (merged M* paper, 15 pp.) proves MG, MG♮, MX, MX′ by applying
**W88 Thm 4.1** directly to explicit quotient groups G″ and excluding every connected algebraic subgroup; Theorem M's
first proof uses RW93's K-form, whose case (a) is again W88 Thm 4.1 (the cases M1, M3 were checked directly on the
group). The κ-saving is W83 Prop. 2.1/2.4; the multiplicity along W is Lemma U (`pilot_epi2_mix/W_UPGRADE.md`), which
holds under

  **(NR)** 2N ≥ d₁ + 2d₀ + κ  (N = dim V).

The groups G″ that occur [Lit, paper §§3, 5, MX_PRIME]:

| theorem | G″ | d₀ | d₁ | G₂ | N | κ |
|---|---|---|---|---|---|---|
| MG  | G_m^{2n} × A″, A″ = E^n/B_{ker ψ} (≈ E^{n/2}) | 0 | 2n | abelian, dim n/2 | d − 1 | n |
| MG♮ | G_m^{2n} × Q″, Q″ = ext. of A″ by G_a (non-split everywhere) | 0 | 2n | dim n/2 + 1 | d − 1 | n |
| MX  | G_a × G_ℓ, G_ℓ = ext. of E_i^n × E_ρ^n by G_a | 1 | 0 | dim 2n + 1 | d − 1 | 2n |
| MX′ | twisted G_ℓ′ | 0 | 0 | dim 2n + 2 | d − 1 | 2n |
| M (M1, M3) | E × G_m × G_a with K-structure (via RW93 (b)) | 1 | n | … | d − 1 | 1·n |

In every application V″ is a **hyperplane** (N = d − 1), W″ = ker Ψ″ has codimension 2, and (NR) is strict.

The classical inputs the corollaries use are all instances of the same theorem (hyperplane case, W large), so no
separate formalisation of Wüstholz, Masser, Bertrand–Masser or Chudnovsky is needed:
* Baker (homogeneous, Q-independent logs are Q̄-independent): already proved in StrongSix (`waldschmidtTheorem1`).
* Ω ∉ Q̄𝓛, η* ∉ Q̄𝓛 (MG2, MG♮2): W88 Thm 4.1 on G_m^r × E (resp. × E^♮), V hyperplane.
* Masser (k-independent elliptic logs are Q̄-independent; Theorem M's last step) and Bertrand–Masser / Wüstholz
  (1 and elliptic logs on non-isogenous curves; MX's last step): hyperplane case on G_a × E^m (× E′^{m′}).
* **MG1 does not need Chudnovsky** [Design, check]: the needed Q̄-independence of 2πi, π², π²/Ω is equivalent to
  Q̄-independence of 1, π, η(Ω), Ω (using η(Ω) = κ₁Ω + κ₂π/Ω on a CM curve), a hyperplane instance on
  G_a × G_m × E^♮.

**Minimal theorem (target `LSG.W88.theorem41`)** [Design]:

> W88 Thm 4.1 **under (NR)**, for G = G_a^{d₀} × G_m^{d₁} × G₂ with G₂ in the class 𝒞 of
> *quotients of (E₁^{m₁} × E₂^{m₂})^♮ by Q̄-rational vector subgroups of the fibre*, E₁, E₂ CM elliptic curves over
> Q̄ (r = 0, i.e. pure abelian G₂ = E₁^{m₁} × E₂^{m₂}, included).

Every G″ above is isogenous to a group of this shape (A″ ∼ E^{n/2}; Q″ ∼ pushout of (E^{n/2})^♮ along a linear form;
G_ℓ is such a pushout already), and Thm 4.1 is invariant under isogeny (λ, δᵢ, τ, κ, N unchanged; Y pulled back through
the tangent isomorphism). So the M* deductions become: subgroup classification of G″ (paper tables) + isogeny transport
+ the count. Hyperplane-only would not save much: the proof (Siegel + zero estimate) is the same for every N, and the
parameter choice is uniform.

Statement design [Design]: concrete coordinates, like StrongSix's `WaldschmidtTheorem1`, so that no abstract
algebraic-group theory appears in the statement. T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^{m} × ℂ^{r};
Λ(G) = {(a, b, z, w) : a ∈ Q̄^{d₀}, e^{b} ∈ Q̄^×, each z_j ∈ Λ_j or ℘_j(z_j) ∈ Q̄, w − M·ζ(z) ∈ Q̄^r} (with η in place of
ζ at lattice points), Ω(G) = 0 × 2πiℤ^{d₁} × {(λ, Mη(λ))}; connected algebraic subgroups given by data
(h₀ ⊂ Q̄^{d₀}, U ⊂ ℚ^{d₁}, S_i ⊂ k_i^{m_i}, fibre part) with explicit tangent spaces. The classification theorem
("every connected algebraic subgroup is of this form") is then *internal* to the proof (it is where the stabiliser from
the zero estimate is turned into data), and downstream users only ever see concrete data.

### 0.2 What Mathlib v4.35.0 has (surveyed 2026-10-30)

| Topic | Mathlib | Gap for us |
|---|---|---|
| ℘, ℘′ for a `PeriodPair` (A. Yang) | `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (1081 l.): lattice, ℘, ℘′, `deriv ℘ = ℘′`, periodicity, parity, power series, meromorphy, pole order, g₂, g₃, **℘′² = 4℘³ − g₂℘ − g₃** | σ, ζ, η, Legendre, addition theorem, degree-2 property (℘(z)=℘(w) ⇔ z ≡ ±w), uniformisation as a group hom, CM action, half-period values |
| Jacobi theta | `NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`: θ(z, τ) entire, quasi-periodicity in z, parity, term bounds | zeros (triple product absent) |
| infinite products | `Analysis/SpecialFunctions/Log/Summable.lean`, `MultipliableUniformlyOn`, `DedekindEta.lean` (tprod holomorphic, nonvanishing, logDeriv = tsum) | Weierstrass σ product (template: Dedekind η) |
| complex analysis | Cauchy integral (discs, rectangles), Liouville, max modulus, removable singularities, **Jensen's formula** (`JensenFormula.lean`, `AnalyticOnNhd.sum_divisor_le`), Schwarz (unit disc) | residue theorem / argument principle for polygons (needed only for Legendre's relation) |
| elliptic curves (algebraic) | `AlgebraicGeometry/EllipticCurve/*`: Weierstrass curves, affine/projective/Jacobian points and **group law with explicit formulas**, division polynomials, j, models | the analytic–algebraic dictionary; addition laws as a complete system of bihomogeneous forms; E^♮ |
| heights | `NumberTheory/Height/EllipticCurve.lean`: naive height, **approximate parallelogram law**, Northcott; `NumberField/House.lean`: house, **Siegel's lemma** (`exists_ne_zero_int_vec_house_le`) | heights of points of E^♮; multiprojective heights of polynomials |
| commutative algebra | Krull height, Lasker, Nullstellensatz, Noether normalisation, homogeneous ideals | Hilbert–Serre, degree, Bézout, CM: **all built in StrongSix `M2/`, `CM/`** for K[X, Y] |
| algebraic groups | none (no group schemes as varieties with Lie algebras, no abelian varieties, no CM theory) | everything is done in coordinates |

### 0.3 What transfers

* **StrongSix** (`schanuel/six_exp/lean`, 17.7k lines, axiom-clean):
  - `Thm1/` (3.9k): Laurent interpolation determinants for G_a^{d₀} × G_m^{d₁}, Schwarz, Liouville, lattice counting,
    the map s from an obstruction, parameter bookkeeping. Its κ is handled by **Step R** (quotient by ℂ·(Y ∩ Ω), a
    rational subtorus). **This does not transfer to M\***: there the periods are *mixed* periods of G_m × E (or of
    G_a × E^♮), whose span is not the Lie algebra of an algebraic subgroup. So the κ-saving must come from the
    auxiliary function itself (W83 Prop. 2.1: Siegel's lemma with conditions only on a fundamental domain mod the
    periods). Re-usable: Liouville (`Arith/`), Schwarz on discs (`Analytic/`), lattice counting, parameter lemmas.
  - `M2/` + `CM/` (6.6k + 1.7k): Philippon's multiplicity estimate in Roy's affine form (DALAG Ch. 5, 8) for
    K[X, Y] with 𝔊 = 0: filtered Hilbert functions, hdim + ht = #vars (Macaulay unmixedness), Bézout by
    complete-intersection chains, Wüstholz's lemma by linear algebra, main argument with prime ideals. **The template
    for Stage 2**, to be generalised to a multigraded quotient ring R/𝔊 (𝔊 = ideal of the closure of G ≠ 0) with
    translations and invariant derivations that raise degree by bounded constants (Philippon's c₁, c₂).
  - `Roy/` (2.7k): Roy's categorical reduction; not needed (we exclude subgroups by hand, as the paper does).
* **LogIrr** (`schanuel/five_exp/padic_e2/lean`): p-adic, Ω = ⊥, no zero estimate. Nothing elliptic; not used.
* **diaz-modulus-lean** (carlok, Apache-2.0, `six_exp/ref/prior_art/`): Siegel's lemma, Liouville, a Schwarz lemma
  for Cartesian products, Gel'fond–Schneider, Baker via Bertrand–Masser (DALAG Ch. 4), Schneider–Lang for
  ℂ^{d₀} × (ℂ^×)^{d₁}. Useful as a model for the one-variable **Schneider–Lang criterion** (Stage 1); no elliptic content.
* **lean_cm4e** (parallel session): target statements, case-check arithmetic, Lemma L. It plans a *conditional*
  certificate from a hypothesis `WaldschmidtGmE`. Interface in §0.7.

### 0.4 The zero (multiplicity) estimate: choice

Options for G_a^{d₀} × G_m^{d₁} × G₂, G₂ ∈ 𝒞:
1. **Philippon 1986, Thm 2.1** (BSMF 114; errata 1987), in Roy's commutative-algebra formulation as already ported in
   StrongSix. Needs: a (multi)projective embedding of G with an ideal 𝔊; addition laws of bounded bidegree (Philippon's
   c₁); invariant derivations of bounded degree (c₂); Cohen–Macaulayness of the homogeneous coordinate ring (E^m ⊂
   (ℙ²)^m is a complete intersection, so CM holds); Hilbert functions and Bézout in that ring; the classification of
   connected algebraic subgroups of G.
2. Masser–Wüstholz 1981/1985: intersection theory (Bézout for multiprojective varieties via degrees). Mathlib has no
   intersection theory; strictly harder to formalise.
3. A CM shortcut: none known. CM is used only through the subgroup classification (abelian subvarieties of E^m ↔
   k-subspaces of k^m) and through the weights α_K.
4. Avoiding zero estimates (Schneider–Lang on Cartesian products, Bertrand–Masser style): gives the analytic subgroup
   theorem in the hyperplane case for *W large*, but not the M* counts, which use 3n points, κ = n and the exact
   weights (the inequality for G′ = 0 is 5n > 4n with κ, 5n ≤ 6n without).

**Decision: option 1**, generalising StrongSix `M2/` from K[X, Y] to the multigraded ring
R = K[X; Y; (U_j : V_j : W_j)_{j≤m}; fibre coords]/𝔊 [Design]. The single-grading trick of StrongSix (one Veronese
grading per multidegree D, M2_PLAN §2) carries over: P of multidegree D is a linear form in the D-Veronese ring.

Embedding of the factors [Lit: Serre, Astérisque 69 App. II; W83 p. 639; Bertrand App. I]:
* E ⊂ ℙ² (Weierstrass), addition laws: Lange–Ruppert's complete system of three laws of bidegree (2,2) (explicit,
  checkable by polynomial identities in Lean via `ring`/`linear_combination` modulo the curve equations).
* E^♮: points (P, t) with group law (P, t) + (Q, s) = (P + Q, t + s + c(P, Q)), c(P, Q) = ½(y_P − y_Q)/(x_P − x_Q)
  (the classical ζ(u + v) − ζ(u) − ζ(v)); embedded in ℙ² × ℙ¹; translation and derivation formulas raise bidegree by
  bounded amounts. A quotient of (E^m)^♮ by a fibre vector subgroup is the same construction with a matrix M.

### 0.5 The auxiliary function with κ (Stage 3): choice

W83 Prop. 2.1 + 2.4 (Siegel's lemma, conditions only on a fundamental domain of V ∩ Ker exp, the saving r^{−κ}) +
Lemma U (multiplicity along W via Taylor coefficients at the points, `W_UPGRADE.md` §1.2) + W88 §7 (the proof of
Thm 4.1 from Prop. 6.1 and Philippon). Not interpolation determinants: the mixed-period κ has no determinant analogue
that we know of (Step R needs an algebraic period span). Analytic inputs: entire functions of order 2 representing
exp_{G₂} (σ³, σ³℘, σ³℘′ and σ-multiples of ζ for E^♮), lower bound |σ| ≥ e^{−c(νS)²} near the points (W83 Lemma 2.2),
Schwarz lemma in several variables on balls (via one-variable restriction, as StrongSix does), Liouville.

### 0.6 Dependency tree and estimates [Est]

```
A  ℘/σ/ζ library ─────────────────────────────────────────────────────────────┐   (Stage 1–2 groundwork)
   A1 σ (Weierstrass product), zeros = Λ, ζ = σ′/σ, ζ′ = −℘          1.5k      │
   A2 quasi-periods η, σ(z+ω) = ±e^{η(z+ω/2)}σ(z), order-2 growth     0.8k      │
   A3 ℘″ = 6℘² − g₂/2, half-period values, alg. independence         0.5k      │
   A4 Legendre ω₁η₂ − ω₂η₁ = 2πi (argument principle on a polygon)   1.5k      │
   A5 addition theorem, degree 2, exp_E : ℂ/Λ ≅ E(ℂ) group hom        2.5k      │
      (bridge to Mathlib's `WeierstrassCurve.Affine.Point` group law)          │
   A6 CM: ℘(az) rational in ℘(z) for a ∈ O_k, algebraic coefficients  1.5k      │
   A7 E^♮ points, cocycle, exp_{E^♮}, periods (λ, η(λ))               1.5k      │
B  Schneider–Lang (one variable) + Schneider's theorems  [Stage 1]    3–4k     │
C  Multiplicity estimate on G_a^{d₀} × G_m^{d₁} × G₂, G₂ ∈ 𝒞  [Stage 2]          │
   C1 multigraded R/𝔊, Veronese, Hilbert functions (generalise M2)    5k       │
   C2 CM of R/𝔊 (complete intersection) + unmixedness                 2k       │
   C3 Bézout with multiplicities in R/𝔊                               3k       │
   C4 addition laws (Lange–Ruppert; E^♮ cocycle), translations        3k       │
   C5 invariant derivations, Wüstholz's lemma                          2.5k     │
   C6 classification of connected algebraic subgroups of G            4k  ← risk│
   C7 Hilbert-function lower bounds on subgroups and cosets            2k       │
   C8 main argument (Roy §8.4.1 generalised)                           2.5k     │
D  W88 Thm 4.1 under (NR)  [Stage 3]                                            │
   D1 heights: points of E^m, E^♮ (Mathlib naive height + parallelogram) 1.5k  │
   D2 W83 Prop 2.1/2.4: Siegel with periods, κ-saving                   3k     │
   D3 Lemma U (multiplicity along W), Cauchy + Liouville                1.5k    │
   D4 W88 §7: parameters, zero estimate ⇒ G′, the inequality             2.5k   │
E  M* deductions  [Stage 3]                                                     │
   E1 Lemma K, isogeny transport, quotient groups G″ (as coordinates)   2k     │
   E2 subgroup tables of G″ (paper §§3, 5) and the case checks          3k     │
   E3 MG, MG♮, MX, MX′, Theorem M; corollaries (2^ϖ, 2^{ϖ/π}, MG1, MX1)  2.5k   │
F  Axioms.lean, README, TRUST, paper  [Stage 4]                                 ┘
```
Total ≈ 55–65k lines (StrongSix: 17.7k in about two days of agent work). Stage 1 is self-contained and useful alone;
Stages 2–3 are a multi-week formalisation at StrongSix's pace.

**R1 in detail (analysis 2026-10-30).** What the proof needs from the stabiliser G′ = G_V⁰ (a Zariski-closed connected
subgroup, over ℂ): its tangent space T′ with (a) exp⁻¹(G′) = T′ + Ω up to finite index, (b) algebraic dimension
= dim_ℂ T′ (Hilbert-function bounds; components σ + G′ of the obstruction ideal), (c) Zariski tangent space at 0 = T′
(Wüstholz's lemma needs transversal functions Q_j), (d) the dimensions of the projections π₀(G′), π₁(G′) (W88's δ₀, δ₁;
subgroups of G_a × G_ℓ are *not* products: the paper's type-E graphs), (e) Q̄-rationality of π₀-part. Plan:
* (a): G̃′ = exp⁻¹(G′) is a closed subgroup of ℂ^d containing Ω; `Subgroups/Closed.lean` (done) + `Subgroups/Torus.lean`
  (agent) give G̃′ = linPart ⊕ discrete, the lattice property on the abelian part, finiteness. linPart is complex by the
  identity theorem (G′ is cut out by polynomials in holomorphic coordinates).
* (c): **[corrected 2026-10-30]** the argument below is false as written (D_w P is not multihomogeneous: diagonal of
  E×E, P = U₁W₂ − U₂W₁, w = (1,1)); fixed in `LSG/ME/SubgroupDhat.lean` by homogenising D_w with chart forms; the
  equality is proved (`mem_TZ_iff`). Original sketch: If v ∈ T₀^{Zar}(G′) and P ∈ I(G′) then (D_v P)(z) = D_v(τ_z P)(0) = 0 for z ∈ G′, because I(G′) is
  translation-invariant (translations act on polynomials via addition laws). So I(G′) is D_v-stable, P∘exp vanishes on
  ℂv, and v ∈ linPart. The converse inclusion is immediate.
* (b): ≥ by a projection argument (restrict polynomials in coordinates on which T′ projects isomorphically). ≤ needs a
  smooth point (generic smoothness in characteristic 0: separating transcendence basis + primitive element, the
  Jacobian criterion at one point) and homogeneity. ~1.5k lines; Mathlib has transcendence bases, primitive element,
  separability.
* Purely analytic arguments cannot replace the algebraic input: the graph of the Tate uniformisation ℂ^× → E is a
  closed complex Lie subgroup of G_m × E that is not algebraic. So (d) needs algebraicity too (Hom(E, G_m) = 0 in the
  form "a Zariski-closed subgroup of L × A has Lie algebra (T′∩Lie L) ⊕ (T′∩Lie A)", for L linear, A abelian).
* Fallback if (b)/(d) prove too costly: state Thm 4.1 with W88's projection-based δ's for a general T′ satisfying (a)–(c),
  and redo the paper's subgroup tables in that generality.

**Main risks.** (R1) C6, the subgroup classification, has no StrongSix analogue beyond tori; for E^m it needs
"Lie(H) ∩ Λ^m is a full lattice in Lie(H)" for a Zariski-closed connected subgroup H, i.e. some analytic structure of
H(ℂ) (fallback: classify only the stabilisers that actually arise, which are defined by translation-stable ideals, by an
algebraic argument on torsion points). (R2) Philippon's c₁ for non-complete G₂ (E^♮): the addition laws of fixed
bidegree (W_UPGRADE §1.4 gives an elementary argument). (R3) Legendre needs a residue computation on a parallelogram,
absent from Mathlib. (R4) Size: Stage 2 alone is larger than StrongSix's M2.

### 0.65 Repository structure (decision of the main session, 2026-10-30)

* `lean_lsg/` stays a separate repo. **StrongSix (`schanuel/six_exp/lean`) becomes a Lake path dependency**; it is a
  finished, axiom-clean artifact. (User, 2026-10-30: changing StrongSix for reusability is allowed. Agreed with the main session: only NEW generic files
  are added there (`StrongSix/M2/WustholzGen.lean`, `SeparateGen.lean`); existing StrongSix files untouched, build green,
  `Axioms.lean` output unchanged, the pre-existing uncommitted 2026-10-18 files left alone.) Where StrongSix needs generalising (multiplicity
  estimate, Thm1 transcendence proof), the general version is proved in `lean_lsg`, with a lemma showing it specialises
  to StrongSix's statement where possible (e.g. `MultEst` on G_a^{d₀} × G_m^{d₁}, `WaldschmidtTheorem1`).
  (Lakefile switched 2026-10-30: `[[require]] name = "StrongSix" path = "../schanuel/six_exp/lean"`; manifest entry
  added by hand as a `path` package.)
* **The conditional M* certificate lives in a separate repo `lean_mstar/`** (MX session: W88 Thm 4.1 / κ / Lemma U
  as a named hypothesis, TRUST.md, paper-to-Lean map). `lean_lsg` is the general theory only (no `LSG/MStar/`). Our final
  theorem must match `lean_mstar`'s named hypothesis exactly (read `lean_mstar/` once it exists, and adapt
  `LSG/W88/Statement.lean` or add a bridge); at the end `lean_mstar` takes `lean_lsg` as a dependency and discharges it.
* Papers: the M* math paper (`schanuel/five_exp/pilot_thmM/paper/`) cites the Lean certificate; the formalisation gets
  its own paper in `lean_lsg/paper/`, a sequel to the strong-six formalisation paper.

### 0.7 Interface with the parallel conditional certificate (`lean_cm4e/`)

`lean_cm4e` will state W88 Thm 4.1 for G_m⁴ × E_i (Roy linear form) as a hypothesis `WaldschmidtGmE` (its BLUEPRINT
§4). Our final declaration `LSG.W88.theorem41` will be stated in concrete coordinates (§0.1), for a class containing
G_m^{d₁} × E^{m}. A bridge lemma `LSG.Bridge.waldschmidtGmE` will be added once their hypothesis is fixed; until then
the coordinates and conventions are recorded in `lean_lsg/INTERFACE.md` (also copied to the shared notes folder) so that
they can match them. Coordination is through files only.

---------------------------------------------------------------------------------------------------------------------

## Stage 1 plan: Schneider's theorem via the Schneider–Lang criterion

**Prior formalisations (checked 2026-10-30: web search, Mathlib v4.35.0 source, our prior-art folders).** None found of
Schneider's theorem or any transcendence result about elliptic functions, in any proof assistant; none of the
one-variable Schneider–Lang criterion for meromorphic functions of finite order. Closest: Gel'fond–Schneider in Lean 4
(Karatarakis–Wiedijk, arXiv:2603.24823, partly in Mathlib); diaz-modulus-lean's Schneider–Lang for ℂ^{d₀} × (ℂ^×)^{d₁}
(exponential functions only, DALAG Cor. 4.2); Isabelle/HOL elliptic functions and modular forms (Eberl–Li–Paulson,
ITP 2026, LIPIcs.ITP.2026.23: ℘, addition theorem, theta, Jacobi triple product, η, G₂ — no transcendence); Mathlib has
℘ but no σ, ζ, η. Chudnovsky–Chudnovsky arXiv:2610.31112 (Lean, Oct 2026) prove irrationality-exponent bounds for CM
periods with uniformisation/theta/CM inputs as hypotheses (Diophantine, not transcendence; see vendor review). Claim for
the paper (to recheck before submission): *first formal proof of a transcendence theorem for elliptic functions, and of
the meromorphic Schneider–Lang criterion; first Lean development of the Weierstrass σ and ζ functions.*

**STATUS 2026-10-30: DONE.** `LSG.Schneider.period_transcendental`, `LSG.Schneider.period_div_pi_transcendental`
(`LSG/SchneiderMain.lean`), standard axioms only (`Axioms.lean`). Inputs: `LSG.schneiderLang` (`LSG/SchneiderLang/`,
1.5k lines; conclusion m ≤ 4[K:ℚ]⌈ρ⌉), `LSG.Weierstrass.weierstrassOrderTwo` (σ/ζ library, `LSG/Weierstrass/`, 1.4k lines),
`LSG/Weierstrass/Basic.lean`, `LSG/Schneider.lean`. 1b (℘(α) transcendental) is with the addition-theorem agent.

Targets (`LSG/Schneider.lean`):
* `LSG.Schneider.period_transcendental`: L a period pair with g₂, g₃ ∈ Q̄, ω ∈ Λ∖0 ⇒ ω ∉ Q̄.
* `LSG.Schneider.period_div_pi_transcendental`: same hypotheses ⇒ ω/π ∉ Q̄.
* (1b, after A5) `LSG.Schneider.wp_transcendental`: α ∈ Q̄∖Λ ⇒ ℘(α) ∉ Q̄; and the elliptic Gel'fond–Schneider analogue.

Proof [Lit: Lang, *Introduction to transcendental numbers*, Ch. II–III; Waldschmidt, *Nombres transcendants*]:
* **B** (`LSG/SchneiderLang/`): if g₁…g_N, h are entire of order ≤ ρ, fᵢ = gᵢ/h, K[f] is closed under d/dz and two
  fᵢ are algebraically independent over a number field K, then {w : h(w) ≠ 0, fᵢ(w) ∈ K ∀i} is finite.
  Statement: `LSG.SchneiderLang` in `LSG/Interface.lean`.
* **A1–A2** (`LSG/Weierstrass/Sigma.lean`): h = σ³, g_℘ = σ(σ′² − σσ″), g_℘′ = 2σ′³ − 3σσ′σ″ + σ²σ‴, all entire of
  order 2 (σ has order 2 by quasi-periodicity; derivatives by Cauchy estimates), σ(z) ≠ 0 off Λ.
* **A3** (`LSG/Weierstrass/Basic.lean`): ℘″ = 6℘² − g₂/2; ℘′(ω/2) = 0 and 4e³ − g₂e − g₃ = 0 for e = ℘(ω/2) when
  ω/2 ∉ Λ; (z, ℘) and (℘, e^{2πiz/ω}) algebraically independent over any subfield.
* Assembly: WLOG ω primitive (so ω/2 ∉ Λ); points w_k = ω/2 + kω, k ∈ ℤ.
  ω ∈ Q̄: functions (z, ℘, ℘′) over K = Q(g₂, g₃, e, ω): values ((k+½)ω, e, 0).
  ω/π ∈ Q̄: functions (℘, ℘′, e^{λz}), λ = 2πi/ω ∈ Q̄, over K = Q(g₂, g₃, e, λ): values (e, 0, −1).
  Infinitely many points contradict B.

## Vendor review: Chudnovsky–Chudnovsky arXiv:2610.31112 ancillary Lean (2026-10-30)

Downloaded (read only, never built or run) to `vendor_review/chudnovsky_2610.31112/` (git-ignored candidate; ~1950 files,
218k lines, Lean v4.34.1, Mathlib d13f23b7 — **not** our pin v4.35.0; Apache-2.0, namespace `OAI`/`QuadraticPi`).
* **No** `axiom`/`sorry`/`native_decide`/`implemented_by`/`extern`/`unsafe` in code (grep, Explore review).
* Power endpoint `QuadraticPi.LemniscatePowerExponentConclusion.lemniscate_power_main`: no hypotheses.
* CM endpoint `QuadraticPi.EllipticCMPaperNormalization.paper_period_main_of_noninteger_CM`: classical inputs are
  **explicit hypotheses**: uniformisation (`hg2`, `hg3`: L.g₂, L.g₃ match the curve), theta simple zero
  (`hsimple : deriv (multiplier L) 0 ≠ 0`, never proved there), CM (`hCM : PreservesLattice L α`), period
  identification (`hperiod`: membership in a scaled lattice).
* Reusable for us (would need porting to v4.35):
  - **Lemniscatic period identification, proved** (~1.5k lines): `omegaPair_g₂_eq_four` (g₂ = 4 for the lattice of
    Ω = 2∫₀¹ dt/√(1−t⁴)), `period_eq_Omega_of_real_branch`, `unit_g₂_re_pos`, `weierstrassP_mul_I`. Together with
    Ω = Γ(1/4)²/(2√(2π)) (Beta integral) this would discharge `lean_mstar`'s `hg₂`.
  - theta/growth (~430 lines; zeros at lattice points, quasi-periodicity, Gaussian bounds) — superseded by our σ library;
  - Liouville for algebraic integers via `Algebra.norm` (~250 lines) — we have our own route;
  - the OAI algebraic-geometry library (~94k lines: Čech cohomology, Serre vanishing, Koszul, regular sequences, local
    Bézout, Hilbert polynomials) — possibly relevant to Stage 2 (Hilbert functions, CM rings), to be assessed then.
* Absent there: ζ, σ, quasi-periods, Legendre, addition theorem, analytic↔algebraic group law, CM rational maps,
  Schwarz lemma, heights, classical zero estimates (they use a jet-interpolation surjectivity "EPA" instead).

### Lemniscatic g₂ = 4 port (2026-10-30)
`LSG/Lemniscate/` (1523 lines; ported from `QuadraticPi/Lemniscate*` + new `Gamma.lean`, `G2.lean`), axiom-clean:
`LSG.Lemniscate.g₂_eq_four_of`, `g₂_isAlgebraic_of (L) (h₁ : L.ω₁ = (varpi : ℂ)) (h₂ : L.ω₂ = I * varpi)`, with
`varpi` = the Γ-formula (same body as `CM4E.varpi`). Checked: `g₂_isAlgebraic_of CM4E.lemniscatic rfl rfl` typechecks
against verbatim copies of lean_mstar's definitions. **This discharges lean_mstar's `hg₂` once lean_mstar depends on
lean_lsg.** Not in the default build target (`LSG.lean`) yet, so it can be dropped cleanly.

**Licence caveat (blocks publication of these files).** The source's `SOURCE-NOTICE.txt` grants Apache-2.0 only for
its `OAI/` tree; for `QuadraticPi/` (where every ported file comes from) it "makes no new licensing election for the
authors' original additions", and those files carry no licence line. So the port is fine for local use but must not
be pushed or published until the licence is clarified with the authors, or the files are replaced by an independent
proof (the mathematics — CM gives g₃ = 0, real-branch identification of the period with 2∫₀¹dt/√(1−t⁴) — is standard).
`NOTICE` records this.

**DONE 2026-10-30 (independent rewrite).** `LSG/LemniscateIndep/` (628 lines, clean room: the agent never opened the
vendor tree or the ported files; route: square-lattice symmetries, real-line analysis on (0, ϖ/2] with the substitution
τ = √(e/℘) and the mean value theorem, Γ-formula via the Beta integral). The ported `LSG/Lemniscate/`, `NOTICE` and
`LICENSES/` are deleted. Bridge for lean_mstar: `LSG.Bridge.isAlgebraic_g₂ L h₁ h₂` (hg₂) and
`LSG.Bridge.irrational_varpi_div_pi_of L h₁ h₂` (hS) in `LSG/Bridge/Lemniscatic.lean`, axiom-clean. **Before any
publication: the local git history still contains the unlicensed port (commit 46f0cd8); publish from a history that
excludes it (fresh repo or rewritten history).**

**Decision (user, 2026-10-30): rewrite independently.** A fresh agent that has not read the vendor tree writes our own
proof (`LSG/Lemniscate/` replaced file by file; NOTICE and LICENSES/ removed when no ported file remains). Route: g₃ = 0 by
the i-symmetry; ℘ real on ℝ (conjugation-stable lattice); ℘′ ≠ 0 on (0, ϖ/2) because zeros of ℘′ are half-periods
(from the degree-2 lemma of `LSG/Weierstrass/` — addition agent); hence e₁ = ℘(ϖ/2) > 0, e₁² = g₂/4 and
ϖ/2 = ∫_{e₁}^∞ dx/√(4x³ − g₂x) = (g₂/4)^{−1/4}·Ω/2; Ω = Γ(1/4)²/(2√(2π)) by the Beta integral (`Gamma.lean` is ours
and stays). Starts once the addition agent reports.


## Status 2026-10-31 (end of Stage 2)
* Stage 1 DONE: Schneider (ω, ω/π, ℘(α) transcendental), Schneider–Lang criterion, σ/ζ/η/Legendre, addition theorem,
  dictionary with Mathlib's group law; independent g₂(ϖℤ[i]) = 4.
* **Stage 2 DONE: `LSG.ME.multEstAb : MultEstAb`** — Philippon's multiplicity estimate on G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m
  (curves from period pairs, over ℂ), standard axioms only. Route as in STAGE2.md: multi-cone model, addition laws,
  Philippon's degree-stable operators (§10), affine slices against the cone-vertex flaw (§11), projective Wüstholz
  with a multiplier, subgroup layer (stabiliser, H⁰, dimension = Lie algebra, product decomposition). ~35k lines total.
* Stage 3 so far: W83 Prop 2.1 in the W88 setting (`prop21_G`), W88 Prop 6.1 under (NR) with b ≥ 1 (`prop61_b`), the
  W88 §5d bridge to lean_mstar's `Thm11Kappa`; W88 §7 running. Open: ℚ̄-rationality of h₀ for d₀ ≥ 2 (automatic for
  d₀ ≤ 1); vector extensions (MG♮, MX, MX′); M* deductions; paper.

## Scope update (main session, 2026-10-31)
lean_lsg does **not** redo the M* deductions: lean_mstar proves them from its `hW`-type hypotheses (`HyperplaneKappa` of
`GroupModel`s) and will add lean_lsg as a dependency to discharge every variant that fits G_a^{d₀} × G_m^{d₁} × E^m from
`theorem41Abelian`. Remaining lean_lsg scope:
1. Theorem 4.1 for **vector extensions** (E^♮ factors and their quotients), stated so that lean_mstar's
   `Thm11KappaMGn`, `Thm11KappaMGnK`, `Thm11KappaMXG`, `MainNat.Thm11KappaNat` become instances (design: VECEXT.md).
2. Later: Theorem 4.1 for products with **CM abelian-variety factors** (lean_mstar `AbVar/` models: Theorem A, X7).
3. README / TRUST, and the formalisation paper about W88 itself (M* consequences: one paragraph citing lean_mstar).
Publish from a clean history (commit 46f0cd8 contains an unlicensed port).

## Paper-plan update (main session, 2026-10-31)
The two math papers are merged into one, `schanuel/five_exp/paper_cm/` (written by the MX session). The formalisation
paper gets a **full application section on lean_mstar** (not one paragraph). Showcase: unconditional 4E at cϖ/π
and cϖ (2^{ϖ/π}, 2^ϖ), Theorem M, MG, MX. Cite paper_cm for the mathematics.

**TODO for the next paper pass** (docs pass of 2026-10-31 did not do this):
* Write the full application section on lean_mstar: unconditional 4E at cϖ/π and cϖ (2^{ϖ/π}, 3^{ϖ/π} and 2^ϖ, 3^ϖ
  not both algebraic), Theorem M, MG, MX (and MX′, Theorem S if wanted), citing `schanuel/five_exp/paper_cm/` for the
  mathematics. The current paper only has short paragraphs (§1 "Why it matters", §vecext "The bridges to lean_mstar").
* Update the bibliography entry `MstarPaper` (still the old title "Four exponentials at CM periods, and a bilinear
  statement…") to the merged paper_cm, and `LeanMstar` (lean_mstar now has lean_lsg as a Lake dependency).
* The docs pass already rewrote §vecext to the proved state (Theorem `thm:vec`, scope as in REVIEW_STATEMENT_VEC C1),
  the abstract, §1, §stats (counts at c751289) and §trust; keep the C1 scope wording in the new section.

## Paper-plan update 2 (main session, user-approved, 2026-10-31)
Results that are direct instances of Roy–Waldschmidt 1993 Théorème (iii) / W88 §5d move from the math paper into the
formalisation paper: MG (2^{ϖ/π}, 3^{ϖ/π}), SMG(a), SE(1), MX/MX′/deg2, Theorem M, X7, X9, X^κ (honest novelty: first
explicit statements and first complete formal proofs; RW93 only outlines the general proof). Source for the section:
`schanuel/five_exp/paper_cm/FOR_LEAN_PAPER.md` (written by the MX session: statement, derivation (group, α_K, κ, bound),
lean_mstar theorem name, status). Paper section to write: **"Explicit consequences, formally verified"**; cite paper_cm
only for results beyond RW93. This supersedes the "lean_mstar application section" TODO above.

## ABVAR risk update (2026-10-31; decision by main session)
**Top risk R-Prop21**: Tier-3 W83 Prop 2.1 for a simple abelian surface (non-split period lattice) needs a
several-variable lattice-point interpolation estimate (Masser 1981 Thm A = W83 Lemma 2.3 = DALAG Thm 7.4.13); one-variable
grid steps provably fall short (`STAGE_A5_PROP21.md`). Formalisation cost only: W83 imports Masser's Theorem A as a published
lemma, so the papers are unaffected. Decision:
1. §4.2 finite check on the concrete AbVar hyperplanes (Theorem A for B(1/5,1/5), B(1/7,1/7), X7, Cor A2); if every
   Ω′ = V ∩ Per admits Ω′-adapted forms, build §4.1 (≈0.5–1k) for those instances and skip Tier 3 for M1. (running)
2. §4.3 `prop21Gen_of_interp` with Lemma L as an explicit hypothesis (not an axiom), caller interface fixed. (running)
3. L2 (Masser's Theorem A) waits for the sources (Masser, Invent. Math. 63 (1981); Waldschmidt DALAG Ch. 7), requested from
   the user by the main session. Do not attempt before they arrive.
**Outcome of the §4.2 check (STAGE_A5 "Research: routes to L2")**: Theorem A (B(1/5,1/5), B(1/7,1/7)) and Cor A2 need
only Tier 1/2, *provided* lean_mstar narrows `Thm11KappaA`/`Thm11KappaAK` to hyperplanes with (TorInj): every v ∈ V ∩ per with
zero toric part is 0 (true for the frame hyperplane V″ by F-independence of b; inherited by V ∩ T_{G′}). Proposed to lean_mstar.
X7 is NOT Tier-2-adaptable (Galois obstruction on X_A); options: a κ_ℂ variant (count 8r > 6r+4 for r ≥ 3; engine
compatibility [Heuristic]) or L2. M2 (`gmAn`) unchecked. **Citation correction**: W83 Lemma 2.3 cites Masser, "Polynomial
interpolation in several complex variables", J. Approx. Theory 24 (1978) 18–34, Théorème A (not Invent. Math. 63 (1981));
Thm 7.4.13 is in Waldschmidt, Astérisque 69–70 (1979), not the 2000 book.
Main session (2026-10-31): TorInj narrowing for Theorem A / Cor A2 **approved**; interface to be coordinated with the MX
session; needs a fidelity referee (concrete frame hyperplanes satisfy it; not vacuous). X7: L2 or κ_ℂ, low priority. Do not
fetch the Masser paper ourselves (user's call).
lean_mstar TorInj interface (agreed 2026-10-31): `HyperplaneKappaOn G good` (= HyperplaneKappa with premise `good V`),
`TorInj G V := ∀ v ∈ V, v ∈ G.per → v.1 = 0 → v = 0`; `Thm11KappaA/AK := … HyperplaneKappaOn (gmA …) (TorInj (gmA …))`.
Lands after lean_mstar's SE₀ work. L2 (E7 premises, `ChowlaSelberg7`) done in lean_mstar 3acf0c9; L1 queued.
TorInj review: CORRECT (REVIEW_TORINJ.md). M2 TODO: run the TorInj test for `gmAn` / `gmAnK` / `gmX7` when M2 starts
(MX session will narrow those hypotheses the same way if it passes). L1 (Wüstholz corollaries) in progress in lean_mstar.

## Paper plan (user-confirmed, 2026-10-31)
No more harvesting; two papers: (1) this Lean formalisation paper, with the section "Explicit consequences, formally
verified"; (2) the math paper "A complete proof of the Roy–Waldschmidt theorem with period term, with explicit consequences
at CM and Beta periods" (MX session; scope in `schanuel/five_exp/paper_cm/SCOPE_GENERAL.md`). Answer the MX session's
questions about which cases lean_lsg covers.
ABVAR decision (2026-10-31): A[M] (torsion algebraicity) is avoided — the AbVar bridge scales the data y by a common
denominator M (lam is a ℚ-span; rk and κ = rk(Y ∩ per) unchanged; conclusion independent of y), so lean_lsg's AbVar theorem
takes Λ(G) with A-parts in the period lattice (exp = origin). Charts X₀, X₄, X₈ cover the model (X₀ = X₄ = 0 occurs).

## Decision (main session, 2026-11-01): stop at M2, publication prep
M3 (genus 3: B(1/7,1/7), X7) is not pursued now; `M3.md` keeps the plan. Publication prep, in order: (1) finish the lean_mstar
narrowing hand-off for M2 and confirm `two_three_beta5'` unconditional there; (2) final whole-repo audit (axioms,
sorry/native_decide, build time, certificate data size, TRUST.md consistent); (3) draft the Lean paper incl. "Explicit
consequences, formally verified" from `schanuel/five_exp/paper_cm/FOR_LEAN_PAPER.md`; (4) fresh-history export (without
46f0cd8) in a separate folder; nothing pushed. L8 (TorsionX7 split) optional.

Update 2026-11-05: step (1) done. lean_mstar `8458732` has `Bridge.two_three_beta5'_uncond` with no hypothesis; copies re-synced.

Update 2026-11-06: steps (2)-(4) done on the export side. lean_lsg itself keeps the StrongSix path dependency, because lean_mstar builds against it; only the export pins StrongSix to `b7f1649`.
