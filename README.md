# Waldschmidt's subgroup theorem with period term, in Lean 4

This repository contains a Lean 4 + Mathlib proof of **Waldschmidt's algebraic subgroup theorem with period term**
(M. Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in several variables*, in: *New Advances in
Transcendence Theory*, Cambridge Univ. Press, 1988, Thm. 4.1; "W88" below). It is proved for the groups

    G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m,      E_j elliptic curves with algebraic g₂, g₃,

under the extra hypothesis **(NR)** `2N ≥ d₁ + 2d₀ + κ` (N = dim V, κ the period rank). Along the way the project
proves Philippon's multiplicity estimate on these groups, Waldschmidt's auxiliary function with periods,
Schneider's theorems on elliptic functions, the meromorphic Schneider–Lang criterion, and builds the Weierstrass σ
and ζ functions. It also proves the theorem, in restricted cases, for groups whose factor `G₂` is built from universal
vector extensions `E^♮` (section [Vector extensions](#vector-extensions-restricted-cases) below, with the exact scope),
for `G_a^{d₀} × G_m^{d₁} × A^r` with `A` the Jacobian of `y⁵ = x(1 − x)`, on toric-injective hyperplanes and for
data whose `A`-components are periods (section [Abelian-variety factors](#abelian-variety-factors-m1)), and, with the
same two restrictions, for `G_a^{d₀} × G_m^{d₁} × Q`, `Q` a push-out of `(A_σ̄^♮)^m` for a `G_a`-extension `A_σ̄^♮` of
`A` (section [Vector extension of the Jacobian](#vector-extension-of-the-jacobian-m2)).

All results below depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is
no `sorry`, no added `axiom` and no `native_decide`. See [TRUST.md](TRUST.md).

This is the sequel to the formalisation of Roy's strong six exponentials theorem
([telaviv/strong-six-exponentials](https://github.com/telaviv/strong-six-exponentials), "StrongSix"). StrongSix proves
W88 Thm. 4.1 for linear groups `G_a^{d₀} × G_m^{d₁}`, in Roy's form, and is a Lake dependency of this project.

## The main theorem

```lean
-- LSG/W88/Statement.lean (the statement, in coordinates; read this file first)
def LSG.W88.Theorem41Abelian : Prop := ...

-- LSG/W88/Main.lean
theorem LSG.W88.theorem41Abelian : LSG.W88.Theorem41Abelian
```

In words. Let `T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m`, with `exp_G(a, b, z) = (a, e^b, (℘_j(z_j), ℘_j'(z_j)))`. Let
`V ⊂ T_G` have dimension `N < d = d₀ + d₁ + m`, let `W ⊂ V` be spanned by vectors with algebraic coordinates, and let
`Y ⊂ V` be a finitely generated subgroup of logarithms of algebraic points, with `κ = rk(Y ∩ ker exp_G)`. If
`2N ≥ d₁ + 2d₀ + κ`, there is a connected algebraic subgroup `G' = H₀ × T_U × B ≠ G` defined over `ℚ̄` with `δ > τ` and

    (λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2m − κ),

where `δ = codim G'`, `δ₁ = codim T_U`, `δ₂ = codim B`, `λ = rk Y/(Y ∩ (T_{G'} + ker exp_G))` and
`τ = dim W/(W ∩ T_{G'})`. Subgroups are given by data: a `ℚ̄`-rational subspace `h₀ ⊂ ℂ^{d₀}`, a subspace
`U ⊂ ℚ^{d₁}` (Lie algebra `U^⊥`), and the tangent space `t ⊂ ℂ^m` of an abelian subvariety, characterised by
"`t ∩ (Λ₁ × ⋯ × Λ_m)` spans `t` over `ℝ`".

W88 states the theorem for every commutative `G₂` and without (NR). Cite this formalisation as **"W88 Thm 4.1 under
(NR) for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`"**, never as "W88 Thm 4.1". (NR) is exactly the range in which W88's
Prop. 6.1 (multiplicities along `W` with the period saving) is proved here; see TRUST.md for what it excludes.

## What is proved

All declarations in this table are in the default build target (`LSG.lean`); the main ones are listed in
`Axioms.lean`.

| result | Lean declaration |
|---|---|
| **W88 Thm 4.1 under (NR)** for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` | `LSG.W88.theorem41Abelian : Theorem41Abelian` |
| Philippon's multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` over `ℂ` (statement `LSG.ME.MultEstAb`, `LSG/ME/MultEstStmt.lean`) | `LSG.ME.multEstAb : MultEstAb` |
| W88 Prop. 6.1 under (NR) (auxiliary function with the κ-saving and multiplicities along `W`; log-exponent `b ≥ 1`) | `LSG.W88.prop61_b` |
| Thm 4.1 under (NR) for `G_a^{k₀} × G_m^{k₁} × B`, `B` any abelian subvariety of a product of elliptic curves | `LSG.CM.thm41Sub : Thm41Sub` |
| W88 §5d (Thm 1.1 with the κ-refined hypothesis (5.4)) for `G_m^{d₁} × E` | `LSG.W88.thm11Kappa` |
| W88 §5d for `G_a^{d₀} × G_m^{d₁} × E^r` (one curve repeated, any curve with algebraic invariants) | `LSG.W88.hypStdCM`, `LSG.W88.hypStdCMAt`, `LSG.W88.hypStdCMAt_zero` |
| W88 §5d for mixed curves, given that abelian tangent spaces are `ℚ̄`-rational (`hrat`) | `LSG.W88.hypStd_of_rat` |
| Schneider: a nonzero period `ω` of a lattice with algebraic `g₂, g₃` is transcendental | `LSG.Schneider.period_transcendental` |
| Schneider: `ω/π` is transcendental | `LSG.Schneider.period_div_pi_transcendental` |
| Schneider: `℘(α)` is transcendental for algebraic `α ∉ Λ` | `LSG.Schneider.wp_transcendental` |
| the Schneider–Lang criterion for meromorphic functions of finite order (one variable) | `LSG.schneiderLang : SchneiderLang` (statement in `LSG/Interface.lean`) |
| `℘, ℘'` are quotients of entire functions of order 2 (via `σ³`) | `LSG.Weierstrass.weierstrassOrderTwo` |
| Legendre's relation `η₁ω₂ − η₂ω₁ = ±2πi` | `LSG.Weierstrass.legendre` |
| addition theorem for `℘`; `z ↦ (℘, ℘'/2)` is a homomorphism to Mathlib's group law | `LSG.Weierstrass.weierstrassP_add`, `LSG.Weierstrass.expE_add` |
| quasi-periodicity of `σ`; degree-two property of `℘` | `LSG.Weierstrass.sigma_add`, `LSG.Weierstrass.weierstrassP_eq_iff` |
| `g₂(ϖℤ[i]) = 4` for `ϖ = Γ(1/4)²/(2√(2π))` | `LSG.LemniscateIndep.g₂_eq_four_of` |
| for `lean_mstar`: `g₂(ϖℤ[i])` algebraic, `ϖ/π` transcendental and irrational | `LSG.Bridge.isAlgebraic_g₂`, `LSG.Bridge.transcendental_varpi_div_pi`, `LSG.Bridge.irrational_varpi_div_pi_of` |
| sanity checks: Gel'fond–Schneider and Schneider's period theorem *derived from* `theorem41Abelian` | `LSG.W88.Sanity.gelfondSchneider`, `LSG.W88.Sanity.period_transcendental'` |

The Weierstrass σ function is defined as the Weierstrass product and ζ as its series; both are new in this project
(Mathlib v4.35.0 has `℘` and `℘'` for a `PeriodPair`, but no σ, ζ or quasi-periods).

## Vector extensions (restricted cases)

The M\* applications MG♮, MX, MX′ and Theorem 1.1(a) at `cϖ` need groups

    G = G_a^{d₀} × G_m^{d₁} × G₂,      G₂ = push-out of (E₁ × ⋯ × E_m)^♮ along an algebraic r × m matrix M,

where `E^♮` is the universal vector extension of `E` (periods `(λ, η(λ))`). Here `T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r`,
`exp(z, w) = ((℘(z), ℘′(z)), w − ζ(z))` on `E^♮`, and the "fibre" is the vector part `0 × 0 × 0 × ℂ^r` of `G₂`. The
statements are in `LSG/W88/StatementVec.lean` (namespace `LSG.W88.Vec`), `V5d2Stmt.lean` and `V5dOnto.lean`; they have
the same conclusion `Concl41` as `Theorem41Abelian`, with `d₂ = m + r` and subgroups `T_U × (B̃ + Γ)` (`SubgroupDataV`).
The extra premises are of two kinds:

* `LiftAlg Ls` (algebraic points of an abelian subvariety `B` lift to algebraic points of `B^♮`) and `PerTanRat Ls`
  (the Lie algebra of `B^♮` is `ℚ̄`-rational). Both are true for every family of curves with algebraic `g₂, g₃`, but
  they are **Lean-proved only for the CM curves used** (powers of a CM curve: `LSG.CM.liftAlg_block`,
  `LSG.CM.perTanRat_block`; the products `E_i^n × E_ρ^n` of the MX bridges: `liftAlg_mx`, `perTanRat_mx`).
* Genuine scope restrictions on `G` and `V`, listed in the table.

| result | Lean declaration | scope (besides (NR)) |
|---|---|---|
| W88 Thm 4.1 under (NR) | `LSG.W88.theorem41VecLA : Theorem41VecLA` | `r ≤ 1`, `V ∩ fibre = 0`, any algebraic `M`; `LiftAlg` |
| the same with `M` onto (proved first, shorter route) | `LSG.W88.theorem41VecLA_onto : Theorem41VecLAOnto` | `r ≤ 1`, `M` onto, `V ∩ fibre = 0`; `LiftAlg` |
| W88 Thm 4.1 under (NR) | `LSG.W88.theorem41Vec2 : Theorem41Vec2` | `d₀ = 0`, `r ≤ 2`, `dim (V ∩ fibre) ≤ 1`; `LiftAlg`, `PerTanRat` |
| W88 §5d ((5.4) with `d₂ = m + r`; no (NR)) | `LSG.W88.V5d.hyperplaneKappaVec_uncond : HyperplaneKappaVec` | `r ≤ 1`; `LiftAlg`, `PerTanRat` |
| W88 §5d | `LSG.W88.V5d.hyperplaneKappaVec2_uncond : HyperplaneKappaVec2` | `d₀ = 0`, `r ≤ 2`; `LiftAlg`, `PerTanRat` |
| Philippon's multiplicity estimate for `G_a^{d₀} × G_m^{d₁} × G₂` (as a quotient of `G_a^{d₀+r} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮`) | `LSG.MEV.multEstVec : MultEstVec` | any algebraic `M`, all degrees |
| lean_mstar's hypotheses `Thm11KappaMXG`, `Thm11KappaMGn L`, `Thm11KappaMGnK L` (every `CMLattice`; premise `KappaOneZero L` in lean_mstar's statement), `Thm11KappaNat` | `LSG.W88.V5d.thm11KappaMXG_uncond`, `thm11KappaMGn_uncond`, `thm11KappaMGnK_uncond`, `thm11KappaNat_uncond` | unconditional |
| lean_mstar's `Thm11KappaSMGn L` (with the premise `KappaOneZero L`, as adopted in lean_mstar `1635927`) | `LSG.W88.V5d.thm11KappaSMGn_uncond` | unconditional |
| lean_mstar's `Thm11KappaMXP` (Theorem MX′, `r = 2`) | `LSG.W88.V5d.thm11KappaMXP_uncond` | unconditional |
| W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` when any two curves are equal or non-isogenous (e.g. ℚ(i) and ℚ(ρ) curves) | `LSG.W88.hypStd_of_nonIsog`, `hypStd_of_pair`, `nonIsog_I_rho` | unconditional |
| a standard model `gmStdVec` of `G_a^{d₀} × G_m^{d₁} × ((∏E_j)^♮ pushed out along M)` and its §5d statement (`r ≤ 1`; one CM curve repeated, `KappaOneZero`) | `LSG.W88.hyperplaneKappa_gmStdVec`, `hypStdVecCM`, `hypStdVecCM_eOne` | unconditional |
| non-vacuity check: `η(ω₁) ∉ ℚ̄·ω₁` for the lemniscatic lattice, derived from the vector statements | `LSG.W88.SanityVec.eta_ne_alg_mul_lem`, `_lem2`, `_5d` | sanity |

All of these are in the default target and in `Axioms.lean`. Supporting results: W88 Prop. 6.1 for the class
(`LSG.AuxV.prop61V_b`, `V ∩ fibre = 0`; a polynomial fibre direction for `Theorem41Vec2`), and a model of `E^♮` in
`ℙ⁴` with eight complete addition laws of bidegree (3,3) (`LSG.Elliptic.NLaw_mem`, `NLaw_complete`, `NLaw_expN_all`).

Cite these results as **"W88 Thm 4.1 under (NR) for `G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` a push-out of `(∏ E_j)^♮` along an
algebraic `M`, in the cases `r ≤ 1` with `V ∩ fibre = 0`, or `d₀ = 0`, `r ≤ 2` and `dim (V ∩ fibre) ≤ 1`; for curves
satisfying `LiftAlg` (and `PerTanRat`), which hold for all curves over `ℚ̄` and are Lean-proved for the CM curves
used"**, and §5d for `r ≤ 1` and for `d₀ = 0`, `r ≤ 2`. Never cite them as "W88 Thm 4.1 for vector extensions".
**Not proved:** the general statement `Theorem41Vec` (no restriction on `r`, `d₀` or `V ∩ fibre`).

The statements were reviewed independently (`reviews/REVIEW_STATEMENT_VEC.md`; no fatal or major issue, the claim-scope
caveat above, minor docstring remarks). The design and development history are in `dev/VECEXT.md`, `dev/STAGE5_MEV.md`,
`dev/STAGE5_AUXV.md`, `dev/STAGE5_S7V.md` and `dev/STAGE6_MXP.md`.

## Abelian-variety factors (M1)

lean_mstar's Theorem A and Corollary A2 at `B(1/5, 1/5)` need W88 for groups with a factor `A^r`, where `A` is the
Jacobian of the genus-2 curve `C : y⁵ = x(1 − x)`, a simple abelian surface with CM by `ℚ(ζ₅)`. In Lean, `A` is
presented by its period lattice on the model `Y² = 4X⁵ + 1` (`X = −y`, `Y = 2x − 1`): `T_A = ℂ²` with the coordinates
`z_j = ∫ X^j dX/Y` (`j = 0, 1`), and `latt ⊂ ℂ²` is the lattice generated by four explicit periods `perVec e`
(Beta values). The statements are in `LSG/W88/StatementAbVar.lean` (`TanA`, `LamA`, `PerA`, `IsAbelianTangentA`,
`SubgroupDataA`, `TorInjA`, `Theorem41AbVarPer`, `gmLsgA`, `HyperplaneKappaAbVar`).

```lean
theorem LSG.W88.hyperplaneKappaAbVar : LSG.W88.HyperplaneKappaAbVar    -- LSG/W88/AbVar5dFinal.lean
theorem LSG.W88.theorem41AbVarPer : LSG.W88.Theorem41AbVarPer        -- LSG/W88/AbVarThm41.lean
theorem LSG.W88.thm11KappaA5 :                                       -- LSG/W88/AbVar5dFinal.lean
    MStarCopy.Thm11KappaA 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0
theorem LSG.W88.thm11KappaAK5 :                                      -- LSG/W88/AbVarFinal.lean
    MStarCopy.Thm11KappaAK 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 0 ∅
```

| result | Lean declaration | scope |
|---|---|---|
| W88 §5d ((5.4) with `d₂ = 2r`; no (NR)) for `G_a^{d₀} × G_m^{d₁} × A^r` | `LSG.W88.hyperplaneKappaAbVar : HyperplaneKappaAbVar` | `V` toric-injective (`TorInjA`); the `A`-components of the `y_i` are periods (`LamA`; by scaling, rational periods) |
| W88 Thm 4.1 under (NR) for the same `G` | `LSG.W88.theorem41AbVarPer : Theorem41AbVarPer` | the same two restrictions |
| lean_mstar's `AbVar.Thm11KappaA 5 2 (·+1) perA5 0` (Theorem A at `B(1/5,1/5)`) and `AbVar.Thm11KappaAK 5 2 (·+1) perA5 0 ∅` (Corollary A2) | `LSG.W88.thm11KappaA5`, `LSG.W88.thm11KappaAK5` | unconditional |
| W88 Thm 4.1 under (NR) and toric injectivity for `G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m`, `B_k` abstract abelian blocks with analytic and Taylor packages | `LSG.W88.theorem41B_of` | generic; from `MultEstB` |
| Philippon's multiplicity estimate for `G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m`, generic over abelian blocks (statement `LSG.MEB.MultEstB`) | `LSG.MEB.multEstB_holds : MultEstB` | any family of `AbBlock`s |
| the Jacobian block: Grant's model of `A` in `ℙ⁸` with nine addition laws, as an `AbBlock` | `LSG.JacBlock.aBlock`, `LSG.Jac.a1Facts : A1Facts` | kernel certificates (TRUST.md §7) |
| abelian tangent spaces of `A^r` are `ℚ̄`-rational (CM argument) | `LSG.W88.ratTangentsA` | unconditional |

**Scope** (reviews/REVIEW_STATEMENT_ABVAR.md, issues C1 and m6). The proved statements are W88 §5d and Thm 4.1 for
`G_a^{d₀} × G_m^{d₁} × A^r` with two restrictions, both of which only weaken W88:
1. the hyperplane `V` is toric-injective (`TorInjA`: `V` contains no nonzero `ℚ`-period of `A^r` alone);
2. every `y ∈ Y` has its `A`-part in the period lattice (`LamA`), so `Γ = exp(Y) ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × {0}`;
   by the scaling lemma `hyperplaneKappaOn_spanLam` the `A`-components may be rational periods, i.e. torsion points.

This is all that lean_mstar's models `gmA` and `gmAK … ∅` use. For `G = A^r` alone (`d₀ = d₁ = 0`) the restricted
form is empty, so it must not be cited as "W88 for `A^r`". Cite it as **"W88 §5d (and Thm 4.1 under (NR)) for
`G_a^{d₀} × G_m^{d₁} × A^r`, `A = Jac(y⁵ = x(1 − x))`, for toric-injective hyperplanes `V` and subgroups `Y` whose
`A`-components are (rational) periods"**.

**What "`A` is the Jacobian" means here.** The statements mention `A` only through `latt ⊂ ℂ²` and the standard
`ℚ̄`-structure of `ℂ²`. Lean computes the four periods as integrals of `X^j dX/Y` over explicit loops on
`Y² = 4X⁵ + 1` (Beta closed forms), proves that they are `ℝ`-independent, and proves that they are periods of an
analytic exponential map `expP : ℂ² → ℙ⁸` onto Grant's model, with discrete kernel `ker expP ⊆ ℚ·latt`. The
identification of that torus with `Jac(C)`, and of complex subtori with abelian subvarieties, is classical and not
formalised (TRUST.md §2, identifications (I1)–(I4)). lean_mstar's final theorems (e.g. `two_three_beta5_uncond`) are
statements about explicit numbers and do not depend on it.

**Architecture.**
* `LSG/Jac/` (stage A1): Grant's model `V(Q) ⊂ ℙ⁸` of `A`, the addition laws of bidegree (2,2), the chart flows,
  doubling, and the facts `A1Facts` that the analytic side consumes. Every heavy polynomial identity is a
  kernel-evaluated certificate (`decide +kernel`) for a checker with a soundness theorem; the data (`Data/`) and
  the checks (`Cert/`) are generated by `scripts/jac/` and are untrusted inputs.
* `LSG/JacAn/` (A2): the genus-2 Abel map, Abel's theorem locally (Euler–Jacobi), the Beta periods, the global
  analytic exponential `expP : ℂ² → ℙ⁸` by doubling the germ, its homomorphism property, `latt ≤ ker expP`,
  discreteness of the kernel, rank 4.
* `LSG/JacAn3/` (A3): the entire nowhere-zero lift `θ` of `expP`, its factor of automorphy, the normalised lift `θ_N`
  of order 2, ψ-Liouville (the nine laws are correct and complete on the image), Taylor algebraicity in three charts.
* `LSG/JacAn4/` (A4.1b): surjectivity: every nonzero point of `V(Q)` is `c · θ_N(z)` (`ThetaData.surjA`).
* `LSG/MEB/` (A4): the multiplicity estimate `MultEstB` for `G_a^{d₀} × G_m^{d₁} × ∏ B_k`, generic over the interface
  `AbBlock` (entire lift, explicit ideal, laws correct on the image, chart flows, Hilbert and local-CI certificates);
  `multEstB_holds`.
* `LSG/JacBlock/` (A4.6): the instance `aBlock` (simplicity of `A`, surjectivity certificates, Hilbert bound,
  local-CI systems) and the analytic and Taylor packages.
* `LSG/AuxFunA/` (A5): W83 Prop. 2.1 under toric injectivity, and Lemma U for abelian blocks.
* `LSG/W88/AbVar*.lean` (A5–A6): Prop. 6.1 and §7 for abelian blocks (`theorem41B_of`), the §5d engine (pivot, Roy,
  `ℚ̄`-rationality), the `TanA` endpoints, and the lean_mstar bridge (`AbVarMStar*.lean`, copies in
  `MStarCopyAbVar.lean`).

The design and history are in `dev/ABVAR.md`, `dev/STAGE_A1.md`–`dev/STAGE_A5.md`, `dev/STAGE_A4_BEZOUT.md`, `dev/STAGE_A4_GAMMA.md`,
`dev/STAGE_A5_PROP21.md` and `reviews/REVIEW_TORINJ.md`. The statements were reviewed independently (`reviews/REVIEW_STATEMENT_ABVAR.md`;
no fatal or major issue, the scope caveat above, docstring remarks that are now fixed).

## Vector extension of the Jacobian (M2)

lean_mstar's Theorem MG♮-A at `B(1/5, 1/5)` (the headline: `2^t` and `3^t` are not both algebraic for
`t = B(1/5, 1/5) = Γ(1/5)²/Γ(2/5)`, without the `/π`) needs W88 for groups with a factor `Q`, the push-out along `bᵀ`
of `(A_σ̄^♮)^m`. Here `A` is the Jacobian of M1, and `A_σ̄^♮` is the 3-dimensional extension of `A` by `G_a` whose class
is the σ̄-eigenline of second-kind differentials, `[X³dX/Y] = −(1/5)[dx/y]`. In Lean, `T_{A_σ̄^♮} = ℂ² × ℂ` with
coordinates `(z, w)`, and the period of `(z, w)` over `λ ∈ latt` is `(λ, η̄(λ))` with `η̄` the fibre period. The
statements are in `LSG/W88/AbVarVStmt.lean` (namespace `LSG.W88`: `TanAV`, `LamAV`, `PerAV`, `SubgroupDataAV`,
`Concl41AV`, `Theorem41AbVarVPer`, `FibOK`, `PerTanFib`, `gmLsgAV`, `HyperplaneKappaAbVarV`); they are generic over a
family of vector blocks `B : Fin m → VBlock` and a matrix `M : ℂ^m → ℂ^r`.

```lean
theorem LSG.MEBV.multEstV_holds : LSG.MEBV.MultEstV                                -- LSG/MEBV/SubgroupMain.lean
theorem LSG.W88.theorem41AbVarVPer (An) (Tay : TayAllV B) (M) (hM : Function.Surjective M.mulVec)
    (hMa : AlgMat M) (hr : r ≤ 1) : Theorem41AbVarVPer An M                       -- LSG/W88/AbVarVSec7.lean
theorem LSG.W88.hyperplaneKappaAbVarV_aBlockV (b : Fin m → ℂ)
    (hb : MStarCopy.IsAdaptedBasisD (MStarCopy.zetaN 5) (Nat.totient 5) b) :
    HyperplaneKappaAbVarV (fun _ : Fin m => LSG.JacBlockV.aBlockVAn)
      (Matrix.of fun (_ : Fin 1) j => b j)                                         -- LSG/W88/AbVarV5dFinal.lean
theorem LSG.W88.thm11KappaAn5 :                                                    -- LSG/W88/AbVarMStarN.lean
    MStarCopy.Thm11KappaAn 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 MStarCopy.perB5
theorem LSG.W88.thm11KappaAnK5 :                                                   -- LSG/W88/AbVarMStarNK.lean
    MStarCopy.Thm11KappaAnK 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 MStarCopy.perB5 ∅
```

| result | Lean declaration | scope |
|---|---|---|
| W88 §5d ((5.4) with `d₂ = 2m + 1`; no (NR)) for `G_a^{d₀} × G_m^{d₁} × Q`, `Q` the push-out of `(A_σ̄^♮)^m` along `bᵀ` | `LSG.W88.hyperplaneKappaAbVarV_aBlockV` | `V` toric-injective (`TorInjAV`); the `A^m`-components of the `y_i` are periods (`LamAV`); `r = 1`, `b` adapted |
| W88 Thm 4.1 under (NR) for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`, any `VBlock` family with analytic and Taylor packages | `LSG.W88.theorem41AbVarVPer` | `M` onto and algebraic, `r ≤ 1`; `V` toric-injective; base parts in the lattice (`LamAV`) |
| Philippon's multiplicity estimate for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`, generic over vector blocks (statement `LSG.MEBV.MultEstV`, `LSG/MEBV/Stmt.lean`) | `LSG.MEBV.multEstV_holds : MultEstV` | any `VBlock` family, onto `M` |
| lean_mstar's `AbVar.Thm11KappaAn 5 2 (·+1) perA5 perB5` (Theorem MG♮-A at `B(1/5,1/5)`) and `AbVar.Thm11KappaAnK 5 2 (·+1) perA5 perB5 ∅` (both stated on toric-injective hyperplanes, lean_mstar `8458732`) | `LSG.W88.thm11KappaAn5`, `LSG.W88.thm11KappaAnK5` | unconditional; `K`-form only for `LAn = ∅` |
| the `A^♮` block: the `ℙ¹¹` model (Grant's variety with `T₀, T₄, T₈`, Plücker quadrics, 81 laws of bidegree (3,3)) as a `VBlock`, with analytic and Taylor packages | `LSG.JacBlockV.aBlockV`, `aBlockVAn`, `aBlockVTay` | Hilbert certificate `LSG.Jac.hilbV` (`hilb_deg = 41`, TRUST.md §7b) |
| the fibre periods: `η̄(perVec e) = (3/5)ζ^{4e}·perB5`, `perB5 = (1 − ζ⁴)B(4/5, 4/5)` | `LSG.JacAn.ThetaData.etaB_perVec`, `ThetaData.etaB_perVec_nat'` | unconditional |

**Scope** (reviews/REVIEW_STATEMENT_M2.md, issue C1). The proved §5d statement is W88 (5.4) for
`G = G_a^{d₀} × G_m^{d₁} × Q`, `Q` the push-out of `(A_σ̄^♮)^m` along `bᵀ`, under all of:
1. `V` toric-injective: `V ∩ (ℚ ⊗ Ω(Q)) = 0`, i.e. `V` contains no nonzero rational period of `Q`;
2. the `y_i` have `A^m`-component 0 up to torsion, i.e. their abelian coordinates are periods (`LamAV`). The
   `G_a^{d₀}`, `G_m^{d₁}` and **fibre** components are arbitrary algebraic, so
   `Γ ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × ker(Q → A^m)(ℚ̄)`, up to torsion. Unlike M1, the form with `d₀ = d₁ = 0` is not
   empty (non-torsion fibre points are allowed);
3. a one-dimensional push-out (`r = 1`), `M = bᵀ` with `b` adapted (`θ(j, e) = ζ^e b_j` `ℚ`-independent). This is what
   makes `FibOK` hold (`PerTanFib`, `perTanFib_aBlockV_of_adapted`).

The Thm 4.1 form holds for any `VBlock` family with packages and any onto algebraic `M` with `r ≤ 1`, under toric
injectivity, the lattice restriction on the base parts, and (NR). The generic Props are W88 instances only for
algebraic `M` (and, for §5d, under `PerTanFib B M`); the proved instances satisfy both. Each restriction only weakens
W88. Cite as **"W88 §5d (and Thm 4.1 under (NR)) for `G_a^{d₀} × G_m^{d₁} × Q`, `Q` the push-out along `bᵀ` of
`(A_σ̄^♮)^m`, `A = Jac(y⁵ = x(1 − x))`, for toric-injective hyperplanes `V` and subgroups `Y` whose `A^m`-components
are periods"**, never as "W88 for vector extensions of abelian varieties".

**Bridge status** (reviews/REVIEW_STATEMENT_M2.md, issue C2, now closed). lean_mstar `8458732` narrowed `Thm11KappaAn` and
`Thm11KappaAnK` to the toric-injective hyperplanes, as dev/M2.md §1.6 proposed, with the new lemma `perAn_inj` (its frame
hyperplanes are toric-injective) and the premise `hκN`. `CM4E/Bridge/AbVar.lean` there proves its own definitions from
`thm11KappaAn5`, `thm11KappaAnK5`, and derives with no hypothesis `two_three_beta5'_uncond`, `fourExpAt_beta5'_uncond`,
`fourExpAt_div_beta5_uncond`, `wuestholzB5_uncond`, `mgAn5_K_uncond`. `MStarCopyAbVarN.lean`, `MStarCopyAbVarNOn.lean` are
verbatim copies of those definitions.

**What "`A_σ̄^♮` is the extension" means here** (identification (I5), reviews/REVIEW_STATEMENT_M2.md §5). Lean presents
`A_σ̄^♮` by an explicit model over `ℚ` in `ℙ¹¹` (Grant's variety plus `T₀, T₄, T₈`, the Plücker quadrics and the 81
(3,3) laws), with an entire uniformisation `(z, w) ↦ (θ_N(z), T(z, w))` built from theta functions. It proves the laws
correct and complete (the `VBlock` fields `lawV_eq`, `lawV_complete`; `LSG/JacBlockV/Laws.lean`), surjectivity off
`{X = 0}` (`surjV`, `surjVV`), the cocycle `ThetaData.fibT_add` with
the same multiplier as `θ_N`, rational fibre flows, the fibre periods `η̄ = −3 × (periods of X³dX/Y)`, and
non-splitting (the period matrix has rank 3, `span_perV`). Classical and **not formalised**: the cone Nullstellensatz
at `{X = 0}`, and that this group *is* the `G_a`-extension of `Jac(C)` with class `[X³dX/Y]` (extensions correspond to
periods of second-kind differentials). The final theorems `thm11KappaAn5`, `thm11KappaAnK5` (and lean_mstar's
`two_three_beta5'` after adoption) are statements about explicit numbers (ζ₅, `perA5`, `perB5`) and do not depend on
(I5); it matters only for the name "W88 §5d for `G_a^{d₀} × G_m^{d₁} × Q`".

**Architecture.**
* `LSG/JacAnV/` (M2.2–M2.3; 16 files, ≈ 2.2k lines): the analytic `A_σ̄^♮`. Lemma K♮ (Liouville), the fibre
  coordinates `T_k = θ_k(w + ℓ) − ⅓∂₀θ_k` (`ThetaData.fibT`), their cocycle, the fibre addition laws, the fibre period
  `η̄` (`ThetaData.etaB`) and its values, `τ₀ = 0`, rank 3, growth.
* `LSG/MEBV/` (M2.4a, M2.5; 47 files, ≈ 10.9k lines, 45 in the default target): the frozen interface `VBlock` (an
  `AbBlock` plus fibre data: lift linear in `w`, fibre flows, Plückers, `(3,3)` laws, a Hilbert certificate with linear
  forms, X-only slicing; `Block.lean`, `Geom.lean`) and the statement `MultEstV` (`Stmt.lean`); the core proof (algebraic
  half: primality, slices, translations, stabilisers, local-CI Bézout; analytic half: Philippon's operators, Wüstholz)
  and `multEstV_holds` (`SubgroupMain.lean`). `MainV.lean` and `Sanity.lean` (`pointVBlock`, a satisfiability check of
  the interface) are outside the default target.
* `LSG/JacBlockV/` (M2.4b, M2.7; 13 files, ≈ 2.2k lines): the instance `aBlockV` (model, Plückers, 81 `pderiv`-defined
  laws, surjectivity, B5/B6 transported), the packages `aBlockVAn`, `aBlockVTay`, the period formula `etaB_perVec_nat'`,
  and the §5d block-family properties `perTanFib_aBlockV`, `perTanPiv_aBlockV`, `ratTangentsV_aBlockV`
  (`PerTanFib{,2,3}.lean`).
* `LSG/AuxFunAV/` (M2.6; 8 files, ≈ 2.0k lines): Taylor package `VBlockTay`, monomials and growth (`TanAV`, `PerAV`,
  `etaB`), W83 Prop. 2.1 under toric injectivity (`TorInjAV`, `prop21AV`), Lemma U (`sPart`, `lemmaU_AV`).
* `LSG/W88/AbVarV*.lean` (M2.6–M2.7; 14 files, ≈ 4.3k lines): the statements (`AbVarVStmt.lean`), Prop. 6.1, the
  polynomial `PWV`, §7 (`theorem41AbVarVPer`), and the §5d engine (`AbVarV5d{Hyp,Rank,Core,Piv,Roy,Rat,Final}.lean`).
  The lean_mstar bridge (M2.8; 4 files, ≈ 0.8k lines) is `AbVarMStarN.lean`, `AbVarMStarNK.lean` with the copies
  `MStarCopyAbVarN.lean` and `MStarCopyAbVarNOn.lean` (verbatim, lean_mstar `8458732`).
* M2 certificates `LSG/Jac/B6V*` (10 files, ≈ 0.8k lines): `B6V.lean` (generated by `scripts/jac/gen_jac_b6vsem.py`)
  proves the Hilbert bound `hilbV` (every homogeneous polynomial of degree 41 lies in the ideal plus the linear forms
  `T₀, T₄, T₈, X₀ + X₄ + X₈`) from 8 kernel-checked identities (`Cert/B6V_<v>.lean`, data `Data/B6V.lean`), and the
  Wronskian cocycle `kappaV`. Same checker and trust model as M1 (TRUST.md §7b).

In total M2 adds 112 files (≈ 23.2k lines) under `LSG/`, of which 110 are in the default target; `Axioms.lean` audits
5 more declarations (`multEstV_holds`, `theorem41AbVarVPer`, `hyperplaneKappaAbVarV_aBlockV`, `thm11KappaAn5`,
`thm11KappaAnK5`). The design and history are in `dev/M2.md` and `dev/STAGE_M2_2.md`. The statements and the bridge were
reviewed independently (`reviews/REVIEW_STATEMENT_M2.md`; no fatal or major issue, the scope caveat C1 and the bridge status
C2 above, docstring remarks m1–m3 and m5 that are now fixed).

## Building and checking

You need [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0` are
pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get          # prebuilt Mathlib (fresh clone only; see below)
lake build                  # the default target LSG
lake env lean Axioms.lean   # every line should print [propext, Classical.choice, Quot.sound]
```

**StrongSix is a Lake git dependency**, pinned in `lakefile.toml` to commit `b7f1649` of
[telaviv/strong-six-exponentials](https://github.com/telaviv/strong-six-exponentials). Lake clones it and builds it from
source (the Mathlib cache does not cover it): the 77 modules this project imports add about 0.9 h of time per file, roughly 15 minutes at four at a time [estimate]. We checked the pin by building this repository against a clean clone of that commit.

**Packages.** Lake creates `.lake/packages` itself, and `lake exe cache get` downloads the prebuilt Mathlib.

**Cold build, measured.** On 2026-11-05 we deleted `.lake/build` and rebuilt the default target with Mathlib and StrongSix
already built, using

```sh
LEAN_NUM_THREADS=4 lake build
```

on Windows 11 with 32 logical processors and 31.7 GB of RAM. It took **3 h 33 min** wall-clock with no errors, and ran at
most four `lean` processes. Times per file sum to 14 h: 9.4 h in `LSG/Jac/`, of which 6.9 h are the ten E1 certificate
files. The largest working set sampled for one process was 7.6 GB and for all of them together 16.9 GB (one sample per
minute). The Windows commit charge rose from 30 GB before the build to a peak of 69.5 GB, so leave room for about 40 GB of
commit (RAM plus page file). An earlier attempt on the same machine, with Lake's default concurrency, failed about 92%
through with `failed to read file … .olean` errors. We suspect memory exhaustion but did not diagnose it [Heuristic], so
keep the thread limit, and lower it on a smaller machine.

The default target `LSG` is 737 modules (about 168.5k lines; ten files of `LSG/`, about 1.6k lines, are outside it). Of these, the abelian chain
(`theorem41Abelian` and the abelian §5d bridges) is 133 files (about 35k lines), the abelian-variety layer of M1 is 323
files (about 67k lines, of which 27k are generated certificate data in `LSG/Jac/Data/` and `LSG/Jac/Cert/`), and the
vector extension of M2 adds 110 files (about 23k lines; its certificates are small).

**The cost is dominated by the kernel certificates of `LSG/Jac/`.** Built two files at a time, they took about
2.7 h wall-clock, i.e. about 5 CPU-hours (logs `scripts/jac/build_*.log`; dev/STAGE_A1.md §10). The E1 certificates
(10 files, about 1300 range declarations) are 2.4 h wall of this, about 4.5 CPU-hours; the degree-5 table, V1/V2,
flows, P2 and B5 add well under an hour. The rest of the library is comparatively fast: the slowest ordinary steps
recorded were a few minutes each (for example about 5 min for `LSG.W88.Prop61` and its prerequisites on top of the
multiplicity-estimate oleans).

**Memory.** Each certificate declaration stays below about 3.5 GB, but one `lean` process checks up to 200 of them
and its working set grows: the E1 files peak at 4–5 GB each when built two at a time (E44 measured 4.96 GB;
dev/STAGE_A1.md §10.6), and the cold build above sampled up to 7.6 GB. Lake checks independent files in parallel, so on a
machine with less than about 32 GB of RAM build the certificate modules a few at a time first (`scripts/jac/build_e1.sh` builds given `LSG.Jac.Cert.*` modules two at a time) and then run
`lake build`.

## Repository layout

| path | content |
|---|---|
| `LSG/W88/Statement.lean` | **the statement** `Theorem41Abelian` (`Tan`, `Lam`, `Per`, `SubgroupData`, `rk`) |
| `LSG/W88/Main.lean` | `theorem41Abelian`, `thm11Kappa` |
| `LSG/W88/Sanity.lean` | Gel'fond–Schneider and Schneider's period theorem derived from the statement |
| `LSG/Weierstrass/` | σ (product), ζ (series), quasi-periods η, order-two growth, Legendre (rectangle integrals only), addition theorem, degree two, dictionary with Mathlib's elliptic-curve group law |
| `LSG/SchneiderLang/`, `LSG/Schneider*.lean`, `LSG/Interface.lean` | the Schneider–Lang criterion and Schneider's theorems |
| `LSG/LemniscateIndep/`, `LSG/Bridge/` | `g₂(ϖℤ[i]) = 4` (independent proof); statements used by lean_mstar |
| `LSG/Subgroups/` | closed subgroups of `ℝⁿ`, subtori, lattice points of abelian tangent spaces |
| `LSG/Elliptic/AdditionLaws*.lean` | two addition laws of bidegree (2,2) on `E ⊂ ℙ²`, completeness, comparison with Mathlib's group law |
| `LSG/ME/` | Stage 2: the multiplicity estimate `MultEstAb` (multi-cone model, translations, Philippon's operators, subgroup layer, Wüstholz's lemma, affine slices, assembly `MainAb.lean`) |
| `LSG/AuxFun/` | Stage 3: W83 Prop. 2.1 (Siegel with periods), Lemma U, algebraic points, chart lower bounds |
| `LSG/W88/Prop61*.lean`, `LSG/W88/Sec7*.lean` | W88 Prop. 6.1 and §7 (Thm 4.1 from Prop. 6.1 and the multiplicity estimate) |
| `LSG/W88/Thm11Kappa.lean`, `K11*.lean`, `K5d*.lean`, `Thm41Sub.lean`, `LSG/CM/Coord.lean`, `LSG/CM/Transport.lean` | W88 §5d bridges; Thm 4.1 for abelian subvarieties by coordinate-projection isogenies |
| `LSG/W88/MStarCopy*.lean` | verbatim copies of lean_mstar's hypothesis statements and group models (see TRUST.md) |
| `LSG/W88/StatementVec.lean`, `V5d2Stmt.lean`, `V5dOnto.lean` | **the vector-extension statements** (`TanV`, `LamV`, `PerV`, `SubgroupDataV`, `LiftAlg`, `PerTanRat`, `Concl41`, `Theorem41VecLA`, `Theorem41VecLAOnto`, `Theorem41Vec2`, `HyperplaneKappaVec`, `HyperplaneKappaVec2`, and the unproved `Theorem41Vec`) |
| `LSG/W88/MainVec.lean`, `V5dOnto*.lean`, `V5dMXPMain.lean`, `V5dSMGn.lean` | the proved vector-extension endpoints and lean_mstar bridges |
| `LSG/MEV/` | the multiplicity estimate `MultEstVec` (model of `E^♮`, Philippon's operators, subgroup layer, slices, Wüstholz, 4-block grading for non-onto `M`) |
| `LSG/AuxFunV/`, `LSG/AuxFun/Prop21LatT*.lean`, `LSG/W88/Prop61V*.lean`, `LSG/W88/Sec7V*.lean` | Prop. 2.1 / 6.1 and W88 §7 for the class (with a polynomial fibre direction for `r ≤ 2`) |
| other `LSG/W88/V5d*.lean`, `LSG/Elliptic/Natural*.lean`, rest of `LSG/CM/` | §5d engine for the class, the `ℙ⁴` model of `E^♮` and its addition laws, CM toolkit (`LiftAlg`, `PerTanRat` for CM blocks) |
| `LSG/W88/StatementAbVar.lean` | **the abelian-variety statements** (`TanA`, `LamA`, `PerA`, `IsAbelianTangentA`, `SubgroupDataA`, `TorInjA`, `Theorem41AbVarPer`, `HyperplaneKappaOnLsg`, `gmLsgA`, `HyperplaneKappaAbVar`) |
| `LSG/W88/AbVar5dFinal.lean`, `AbVarThm41.lean`, `AbVarFinal.lean` | the proved abelian-variety endpoints (`hyperplaneKappaAbVar`, `theorem41AbVarPer`, `thm11KappaA5`, `thm11KappaAK5`) |
| other `LSG/W88/AbVar*.lean`, `MStarCopyAbVar.lean` | Prop. 6.1, §7 and the §5d engine for abelian blocks; the lean_mstar bridge and its verbatim copies |
| `LSG/Jac/` | Grant's model of `A = Jac(y⁵ = x(1 − x))` in `ℙ⁸`, addition laws, flows, `A1Facts`; kernel checkers with soundness theorems; generated data (`Data/`) and `decide +kernel` certificates (`Cert/`) |
| `LSG/JacAn/`, `LSG/JacAn3/`, `LSG/JacAn4/` | Abel map and Beta periods, the analytic exponential `expP` and its kernel; the lift `θ_N`, laws on the image, Taylor data; surjectivity onto the model |
| `LSG/MEB/` | the multiplicity estimate `MultEstB`, generic over abelian blocks (`AbBlock`) |
| `LSG/JacBlock/` | the Jacobian block `aBlock` and its analytic and Taylor packages |
| `LSG/AuxFunA/` | Prop. 2.1 under toric injectivity and Lemma U for abelian blocks |
| `LSG/W88/AbVarVStmt.lean` | **the M2 statements** (`TanAV`, `LamAV`, `PerAV`, `SubgroupDataAV`, `Concl41AV`, `Theorem41AbVarVPer`, `FibOK`, `PerTanFib`, `gmLsgAV`, `HyperplaneKappaAbVarV`) |
| other `LSG/W88/AbVarV*.lean`, `AbVarMStarN*.lean`, `MStarCopyAbVarN*.lean` | Prop. 6.1, §7 and the §5d engine for vector blocks; the endpoints `theorem41AbVarVPer`, `hyperplaneKappaAbVarV_aBlockV`; the lean_mstar bridge `thm11KappaAn5`, `thm11KappaAnK5` and its copies |
| `LSG/JacAnV/` | the analytic `A_σ̄^♮`: Lemma K♮, fibre coordinates, cocycle, fibre laws, fibre periods |
| `LSG/MEBV/` | the multiplicity estimate `MultEstV`, generic over vector blocks (`VBlock`) |
| `LSG/JacBlockV/` | the `A^♮` block `aBlockV`, its packages, the fibre period formula, `PerTanFib`/`PerTanPiv`/`RatTangentsV` for it |
| `LSG/AuxFunAV/` | Taylor package, monomials, Prop. 2.1 under toric injectivity and Lemma U for vector blocks |
| `scripts/` | Python generators of polynomial identities and certificates (`vecext_spike/`, `mev_curve/` for the `E^♮` laws; `jac/`, `jacblock/` for the Jacobian block, including `jac/gen_jac_b6vsem.py` for B6V; `m2_spike/` exploratory); untrusted, see TRUST.md. `m2_lean_mstar_template/` holds the review's (unbuilt) lean_mstar narrowing template |
| `Axioms.lean` | axiom audit |
| `dev/PLAN.md`, `dev/INTERFACE.md`, `dev/STAGE*.md`, `dev/VECEXT*.md`, `dev/ABVAR.md`, `dev/M2.md` | development notes (plans, design decisions, status) |
| `reviews/REVIEW_STATEMENT.md`, `reviews/REVIEW_STATEMENT_VEC.md`, `reviews/REVIEW_TORINJ.md`, `reviews/REVIEW_STATEMENT_ABVAR.md`, `reviews/REVIEW_STATEMENT_M2.md` | the independent fidelity reviews of `Theorem41Abelian`, of the vector-extension statements, of the toric-injectivity premise, of the abelian-variety statements and of the M2 (`A^♮`) statements and bridge |
| `paper/` | the formalisation paper (`paper.tex`; compiled copy in `paper/build/`) |

Every Lean file starts with a docstring that says what it proves.

## Relation to lean_mstar

`lean_mstar` (the author's sibling project) is a separate Lean certificate for the paper *Four exponentials at periods
of CM abelian varieties* (draft). Its results assume W88 for specific groups as named hypotheses, and it has this
project as a Lake path dependency to discharge them. This project proves all of its elliptic and vector-extension W88
hypotheses, the two abelian-variety hypotheses at `y⁵ = x(1 − x)`, and the two second-kind ones:
* abelian: `lean_mstar`'s `Thm11Kappa L d₁` is `LSG.W88.thm11Kappa`, its `HypStdCMAt L d` is `LSG.W88.hypStdCMAt`, and
  its `hg₂`, `hS` follow from `LSG.Bridge.*`;
* vector extensions: `Thm11KappaMXG`, `Thm11KappaMGn L`, `Thm11KappaMGnK L`, `Thm11KappaNat`, `Thm11KappaSMGn L` and
  `Thm11KappaMXP` are the `LSG.W88.V5d.*_uncond` theorems above;
* abelian varieties: `AbVar.Thm11KappaA 5 2 (·+1) perA5 0` and `AbVar.Thm11KappaAK 5 2 (·+1) perA5 0 ∅` are
  `LSG.W88.thm11KappaA5` and `LSG.W88.thm11KappaAK5`. lean_mstar commit `9b569e0` (`CM4E/Bridge/AbVar.lean`) wires
  them in and derives, with no hypothesis, `two_three_beta5_uncond` (`2^t, 3^t` are not both algebraic at
  `t = B(1/5,1/5)/π`), `wuestholzA5_uncond`, `fourExpAt_beta5_uncond` and `fourExpAt_pi_div_beta5_uncond` (Theorem
  MG-A at `cB(1/5,1/5)/π` and `cπ/B(1/5,1/5)`); `d7c6da1` adds the `K`-form `mgA5_K_uncond`. Corollary A2 at
  `B(1/5,1/5)` (`corA2_beta5_uncond`) keeps lean_mstar's named input `NotLtildeA (perA5 0)`;
* vector extension of the Jacobian (M2): `AbVar.Thm11KappaAn 5 2 (·+1) perA5 perB5` and `AbVar.Thm11KappaAnK … ∅`, on
  toric-injective hyperplanes, are `LSG.W88.thm11KappaAn5` and `thm11KappaAnK5`. lean_mstar commit `8458732`
  (`CM4E/Bridge/AbVar.lean`) wires them in and derives, with no hypothesis, `two_three_beta5'_uncond` (**`2^t, 3^t` are
  not both algebraic at `t = B(1/5,1/5)`**), `wuestholzB5_uncond`, `fourExpAt_beta5'_uncond`,
  `fourExpAt_div_beta5_uncond` (Theorem MG♮-A at `cB(1/5,1/5)` and `c/B(1/5,1/5)`) and the `K`-form `mgAn5_K_uncond`.

The bridges are stated against verbatim copies of lean_mstar's definitions (`LSG/W88/MStarCopy*.lean`) and checked by
typechecking against unmodified lean_mstar (TRUST.md §5). With them, lean_mstar's four exponentials statements at
`t = cϖ/π` and `t = cϖ` (e.g. `2^{ϖ/π}, 3^{ϖ/π}` and `2^ϖ, 3^ϖ` are not both algebraic), Theorem M, MG, MX and MX′ are
unconditional on W88 (they may still use other named classical inputs; see lean_mstar's README), and so are the
abelian-variety results at `B(1/5,1/5)` listed above. Not covered: the other CM abelian-variety hypotheses of lean_mstar
(`Thm11KappaX7`, `Thm11KappaXA`, and the `N = 7` instance `Thm11KappaA 7 …`). Details: TRUST.md §6.

## Status, provenance and caveats

- **The Lean kernel has checked every proof listed above. No human expert has reviewed the definitions, the
  statements or the proofs.** The statement reviews so far were done by independent AI sessions: of
  `Theorem41Abelian` (`reviews/REVIEW_STATEMENT.md`; verdict CORRECT, four minor remarks), of the vector-extension
  statements (`reviews/REVIEW_STATEMENT_VEC.md`; no fatal or major issue, the claim-scope caveat C1, minor docstring remarks),
  of the toric-injectivity premise (`reviews/REVIEW_TORINJ.md`), of the abelian-variety statements and the lean_mstar
  bridge (`reviews/REVIEW_STATEMENT_ABVAR.md`; no fatal or major issue, the scope caveat C1, minor remarks), and of the M2
  statements and bridge (`reviews/REVIEW_STATEMENT_M2.md`; no fatal or major issue, the scope caveat C1, the bridge status C2,
  minor remarks).
- The plans, the Lean code and the documentation were written by AI models (Claude, Anthropic) working in Claude Code
  under the direction of the author. The author is responsible for the intended statements.
- `LSG/SchneiderLang/Analytic.lean` and `Arith.lean` adapt lemmas from StrongSix (same author, Apache 2.0). No
  third-party Lean code is included.
- **History.** The public repository starts from one fresh commit, because the private development history contains a
  port of third-party Lean files whose licence was unclear. Those files were deleted and replaced by an independent proof
  (`LSG/LemniscateIndep/`) written by an agent that never read them, and the public history excludes them. Hashes of
  this project's commits cited in this repository (for example in `TRUST.md` and `dev/`) refer to the development history.

## License

Apache License 2.0 (`LICENSE`).
