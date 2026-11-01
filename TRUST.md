# What you have to trust

## 1. Axioms

`lake env lean Axioms.lean` prints, for the main theorem and each of its main ingredients,

```
'LSG.W88.theorem41Abelian' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.ME.multEstAb' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.prop61_b' depends on axioms: [propext, Classical.choice, Quot.sound]
...
```

(63 declarations, all with the same three axioms; output rechecked on 2026-11-06 against the cold build recorded in
the README.) Among them are
the vector-extension endpoints `LSG.MEV.multEstVec`, `LSG.W88.theorem41VecLA`, `theorem41VecLA_onto`, `theorem41Vec2`,
`LSG.W88.V5d.hyperplaneKappaVec_uncond`, `hyperplaneKappaVec2_uncond` and the six lean_mstar bridges
`thm11KappaMXG_uncond`, `thm11KappaMGn_uncond`, `thm11KappaMGnK_uncond`, `thm11KappaNat_uncond`,
`thm11KappaSMGn_uncond`, `thm11KappaMXP_uncond`, and the abelian-variety endpoints `LSG.Jac.a1Facts`,
`LSG.JacBlock.aBlock`, `LSG.MEB.multEstB_holds`, `LSG.W88.hyperplaneKappaAbVar`, `LSG.W88.theorem41AbVarPer` and the
lean_mstar bridges `LSG.W88.thm11KappaA5`, `thm11KappaAK5`, and the M2 endpoints `LSG.MEBV.multEstV_holds`,
`LSG.W88.theorem41AbVarVPer`, `LSG.W88.hyperplaneKappaAbVarV_aBlockV` and the bridges
`LSG.W88.thm11KappaAn5`, `thm11KappaAnK5`; all are in the default target. These are Lean's three
standard axioms, the ones Mathlib uses. The project contains no `sorry`, no `axiom` declaration and no `native_decide`, so no
proof relies on the compiler. The kernel certificates of `LSG/Jac/` use `decide +kernel`, which is checked by the
kernel itself (§7).

The dependency StrongSix (Lake git dependency, pinned to `b7f1649`) is itself axiom-clean; `#print axioms` covers its declarations too.

## 2. The statement: what it says, and where to read it

The kernel checks the proof. It cannot check that the statement means what we claim. Read, in this order:

| file | what to check |
|---|---|
| `LSG/W88/Statement.lean` (≈ 165 lines) | **the theorem.** `Tan d0 d1 m = ℂ^{d₀} × ℂ^{d₁} × ℂ^m`; `Lam Ls` (logarithms of algebraic points: `a` algebraic, every `e^{b_i}` algebraic, every `z_j` in `Λ_j` or with `℘_j(z_j)` algebraic); `Per Ls` (`0 × 2πiℤ^{d₁} × Λ₁ × ⋯ × Λ_m`); `torusLie U` (`U^⊥`); `IsAbelianTangent Ls t` (`t ∩ Λ` spans `t` over `ℝ`); `SubgroupData` (`h₀` `ℚ̄`-rational, `U ⊂ ℚ^{d₁}`, abelian tangent `t`) and its `tan`, `δ0`, `δ1`, `δ2`, `δ`, `Proper`; `rk` (`ℚ`-dimension of the `ℚ`-span); `Theorem41Abelian` |
| `LSG/W88/Main.lean` | `theorem41Abelian : Theorem41Abelian` and nothing else of substance |
| `LSG/ME/MultEstStmt.lean` | the multiplicity estimate `MultEstAb` (only if you care about this intermediate endpoint) |
| `LSG/Interface.lean` | `SchneiderLang`, `WeierstrassOrderTwo`, `GrowthLE` (for the Stage 1 endpoints) |
| `LSG/SchneiderMain.lean` | Schneider's theorems; their statements use only Mathlib's `PeriodPair`, `weierstrassP`, `lattice`, `g₂`, `g₃` |
| `LSG/W88/StatementVec.lean` (≈ 265 lines) | **the vector-extension statements.** `TanV d0 d1 m r = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r`; `LamV Ls M` (logarithms of algebraic points; the fibre condition is `s − Mζ(z)` algebraic, with LSG's Weierstrass `ζ`); `PerV Ls M` (`0 × 2πiℤ^{d₁} × {(λ, Mη(λ))}`); `SubgroupDataV` (`U`, abelian tangent `t`, rational vector part `gam`) and its `tan`, `δ0`, `δ1`, `δ`, `δ2`, `Proper`; `LiftAlg`, `PerTanRat`; `Concl41`; `Theorem41Vec`, `Theorem41VecLA`, `HyperplaneKappaVec` |
| `LSG/W88/V5d2Stmt.lean`, `LSG/W88/V5dOnto.lean` (statement part) | `Theorem41Vec2`, `HyperplaneKappaVec2`; `Theorem41VecLAOnto` |
| `LSG/W88/StatementAbVar.lean` (≈ 280 lines) | **the abelian-variety statements.** `TanA d0 d1 r = ℂ^{d₀} × ℂ^{d₁} × (ℂ²)^r`; `latt` (`LSG/JacAn3/Normalize.lean`: the lattice of the four periods `perVec e`, `LSG/JacAn/Rank4.lean`); `LamA` (`a` algebraic, `e^{b_i}` algebraic, `A`-parts in `latt`); `PerA` (`0 × 2πiℤ^{d₁} × latt^r`); `IsAbelianTangentA`; `SubgroupDataA`; `TorInjA`; `Theorem41AbVarPer`; `HyperplaneKappaOnLsg`, `gmLsgA`, `HyperplaneKappaAbVar` |
| `LSG/W88/MStarCopyAbVar.lean` | verbatim copies of lean_mstar's `Thm11KappaA`, `Thm11KappaAK` and their models (§5) |
| `LSG/W88/AbVarVStmt.lean` (≈ 240 lines) | **the M2 statements** (vector extension of the Jacobian). `TanAV d0 d1 r B = ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k} × ℂ^r` (`LSG/AuxFunAV/Mono.lean`, with `etaB`, `PerAV`, `PerAVf`); `LamAV` (`a` algebraic, `e^{b_i}` algebraic, base parts in `lat`, `sPart = s − Mη(z)` algebraic); `AlgTanAV`; `SubgroupDataAV` (`U`, rational `t`, `ℚ̄`-rational `Γ`; `tan = Γ + U^⊥ + perTanA M t`); `Concl41AV`; `Theorem41AbVarVPer`; `FibOK`, `PerTanFib`, `gmLsgAV`, `HyperplaneKappaAbVarV`. The block interface is `LSG/MEBV/Block.lean` (`VBlock`), the multiplicity estimate `LSG/MEBV/Stmt.lean` (`MultEstV`) |
| `LSG/JacAnV/Fibre.lean`, `LSG/JacBlockV/Inst.lean`, `An.lean` | the `A^♮` block: fibre coordinates `fibT`, fibre period `etaB`, the instance `aBlockV` (`η = etaB`), `span_perV` |
| `LSG/W88/MStarCopyAbVarN.lean`, `MStarCopyAbVarNOn.lean` | verbatim copies of lean_mstar `8458732`'s `gmAn`, `Thm11KappaAn`, `gmAnK`, `Thm11KappaAnK` (§5, §6) |

The elliptic curves are Mathlib's: a `PeriodPair` `L` (two `ℝ`-independent complex numbers), with
`L.weierstrassP`, `L.g₂ = 60 G₄`, `L.g₃ = 140 G₆` and the proved equation `℘'² = 4℘³ − g₂℘ − g₃`. The σ and ζ
functions of `LSG/Weierstrass/` do not occur in the statement of `Theorem41Abelian`.

What `Theorem41Abelian` means, in mathematical notation, is written out in the docstring of `Statement.lean` and in the
README. Points to keep in mind:

* **(NR) is a genuine restriction.** The hypothesis `d1 + 2 * d0 + rk (Y ⊓ Per Ls) ≤ 2 * finrank ℂ V` is not in W88.
  It is the range in which W88 Prop. 6.1 (multiplicities along `W` with the period saving κ) is proved here, following
  Lemma U of the M\* paper (Appendix A). It excludes, for example, the usual encoding of Hermite–Lindemann
  (`G = G_a × G_m`, `V = W = ℂ(1, 1)`), and adding `G_m` factors to restore (NR) makes the conclusion trivially
  satisfiable (reviews/REVIEW_STATEMENT.md §6.3). All applications in the M\* paper satisfy (NR).
* **`G₂` is a product of elliptic curves** for `theorem41Abelian` (for vector extensions see the next point). W88
  allows any commutative `G₂`. `LSG.CM.thm41Sub`
  extends the theorem to `G_a^{k₀} × G_m^{k₁} × B`, `B` any abelian subvariety of a product of elliptic curves.
* **Vector extensions are proved only in restricted cases.** For `G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of
  `(E₁ × ⋯ × E_m)^♮` along an algebraic `r × m` matrix `M`, the proved statements are:
  * W88 Thm 4.1 under (NR) for `r ≤ 1` and `V ∩ fibre = 0`, any algebraic `M`, given `LiftAlg`
    (`LSG.W88.theorem41VecLA : Theorem41VecLA`; the onto-`M` case `theorem41VecLA_onto` was proved first);
  * W88 Thm 4.1 under (NR) for `d₀ = 0`, `r ≤ 2` and `dim (V ∩ fibre) ≤ 1`, given `LiftAlg` and `PerTanRat`
    (`LSG.W88.theorem41Vec2 : Theorem41Vec2`);
  * W88 §5d (5.4), without (NR), for `r ≤ 1` and for `d₀ = 0`, `r ≤ 2`, given `LiftAlg` and `PerTanRat`
    (`LSG.W88.V5d.hyperplaneKappaVec_uncond`, `hyperplaneKappaVec2_uncond`).

  `LiftAlg` and `PerTanRat` are true for all curves with algebraic `g₂, g₃` (reviews/REVIEW_STATEMENT_VEC.md §5), but are
  **Lean-proved only for CM blocks** (`LSG.CM.liftAlg_block`, `perTanRat_block`, and the products `liftAlg_mx`,
  `perTanRat_mx` used by the MX bridges). The restrictions on `r`, `d₀` and `V ∩ fibre` are genuine. The general
  `LSG.W88.Vec.Theorem41Vec` is **not** proved. Cite as in the README ("in the cases …"), never as "W88 Thm 4.1 for
  vector extensions" (reviews/REVIEW_STATEMENT_VEC.md, issue C1).
* **Abelian-variety factors are proved with two restrictions.** For `G = G_a^{d₀} × G_m^{d₁} × A^r`, `A` the Jacobian
  of `y⁵ = x(1 − x)`, the proved statements (`LSG.W88.hyperplaneKappaAbVar`, `theorem41AbVarPer`) are W88 §5d and
  Thm 4.1 under (NR) **for toric-injective hyperplanes `V` and subgroups `Y` whose `A`-components are (rational)
  periods** (reviews/REVIEW_STATEMENT_ABVAR.md, C1): `Γ = exp(Y) ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × A^r_tors`. This is what
  lean_mstar's models `gmA` and `gmAK … ∅` use. For `G = A^r` alone (`d₀ = d₁ = 0`) the restricted form is empty
  (m6); do not cite it as "W88 for `A^r`".
* **What is identification, not Lean, for `A`** (reviews/REVIEW_STATEMENT_ABVAR.md §5). The statements mention `A` only
  through `latt ⊂ ℂ²` and the standard `ℚ̄`-structure. Lean proves: the generators of `latt` are integrals of
  `X^j dX/Y` over explicit loops on `Y² = 4X⁵ + 1` with Beta closed forms (`curveIntegral_cycleE`,
  `liftPath_mem_curve`); they equal lean_mstar's `perA5` up to `5(−1)^s` (`perA5_scale`); `latt` has rank 4
  (`linearIndependent_perVec`); for the analytic map `expP : ℂ² → ℙ⁸` built on the certified Grant-model data,
  `latt ≤ ker expP`, `ker expP` is discrete and `ker expP ⊆ ℚ·latt` (`lattice_le_ker`, `isNsmulIn_latt_kerE`), and
  every nonzero point of Grant's model `V(Q)` is `c·θ_N(z)` (`ThetaData.surjA`), so `ℂ²/ker expP → V(Q)` is a
  bijective analytic homomorphism compatible with the Abel–Jacobi map; abelian tangents of `A^r` are `ℚ̄`-rational
  (`ratTangentsA`). Classical and **not formalised** [Lit] (there is no Jacobian in Mathlib):
  * (I1) the Abel–Jacobi uniformisation `Jac(C)(ℂ) ≅ ℂ²/Λ_C` in the coordinates `(∫dX/Y, ∫X dX/Y)`, with
    `ℚ̄`-structure dual to `H⁰(C, Ω¹_{/ℚ})`; with the Lean facts, `ℂ²/latt` is isogenous to `Jac(C)` and the
    `ℚ`-period spaces and `ℚ̄`-structures agree (whether `latt = Λ_C` is not decided and not needed);
  * (I2) complex subtori of `A^r` are abelian subvarieties (Chow), and Goursat for the subgroups of
    `G_a^{d₀} × G_m^{d₁} × A^r`;
  * (I3) the isomorphism `y⁵ = x(1 − x) ≅ Y² = 4X⁵ + 1` (`X = −y`, `Y = 2x − 1`; elementary);
  * (I4) only for the stronger phrase "Lean constructs the Jacobian": Grant's model `V(Q)` with its law is the
    Jacobian (Grant 1990) and `ker expP = Λ_C`.

  So the *name* "W88 for `G_a^{d₀} × G_m^{d₁} × Jac(C)^r`" rests on (I1)–(I3). The truth of `thm11KappaA5`,
  `thm11KappaAK5`, and of lean_mstar's `two_three_beta5_uncond` etc., does not: they are kernel theorems about
  explicit numbers (ζ₅ and the Beta values `perA5`).
* **Vector extension of the Jacobian (M2) is proved with three restrictions** (reviews/REVIEW_STATEMENT_M2.md, C1). For
  `G = G_a^{d₀} × G_m^{d₁} × Q`, `Q` the push-out along `bᵀ` of `(A_σ̄^♮)^m` (`A_σ̄^♮` the `G_a`-extension of `A` with
  class `[X³dX/Y] = −(1/5)[dx/y]`), `LSG.W88.hyperplaneKappaAbVarV_aBlockV` is W88 §5d (5.4) under:
  1. `V` toric-injective (`TorInjAV`): `V ∩ (ℚ ⊗ Ω(Q)) = 0`;
  2. the `y_i` have `A^m`-component 0 up to torsion (`LamAV`: base parts in `latt`); their `G_a`, `G_m` and **fibre**
     components are arbitrary algebraic, so `Γ ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × ker(Q → A^m)(ℚ̄)` up to torsion (for
     `d₀ = d₁ = 0` the form is not empty, unlike M1);
  3. `r = 1`, `M = bᵀ` with `b` adapted (`θ(j, e) = ζ^e b_j` `ℚ`-independent); this is what makes `FibOK` hold.

  `LSG.W88.theorem41AbVarVPer` is Thm 4.1 under (NR) for any `VBlock` family with packages and any onto algebraic `M`,
  `r ≤ 1`, under restrictions 1–2. Each restriction only weakens W88. The generic Props are W88 instances only for
  algebraic `M` and (for §5d) under `PerTanFib B M` (m2); the proved instances satisfy both. The engine hypotheses
  `PerTanPiv`, `RatTangentsV`, `Thm41FamV` (`AbVarV5dHyp.lean`) occur in no final statement and are discharged for
  `aBlockV`. `LSG.W88.thm11KappaAn5`, `thm11KappaAnK5` cover lean_mstar's `Thm11KappaAn`, `Thm11KappaAnK` (both on
  toric-injective hyperplanes), and `Thm11KappaAnK` only for `LAn = ∅` (m4); see §6 for the status.
* **What is identification, not Lean, for `A_σ̄^♮`** (reviews/REVIEW_STATEMENT_M2.md §5). In addition to (I1)–(I4):
  * (I5) [Lit]: the `ℚ`-model in `ℙ¹¹` (Grant's variety plus `T₀, T₄, T₈`, the Plücker quadrics and the 81 (3,3) laws)
    is a commutative group variety `ℚ̄`-isomorphic to `A_σ̄^♮`. Lean proves the laws correct and complete
    (`lawV_eq`, `lawV_complete`), surjectivity off `{X = 0}` (`surjV`), the cocycle `ThetaData.fibT_add` with the same
    multiplier as `θ_N`, rational fibre flows, the fibre periods `η̄(perVec e) = (3/5)ζ^{4e}(1 − ζ⁴)B(4/5, 4/5)`, i.e.
    `−3` times the periods of `X³dX/Y` (`ThetaData.etaB_perVec_nat'`), and non-splitting (`span_perV`). Not
    formalised: the cone Nullstellensatz at `{X = 0}`, and that this group *is* the extension with class `[X³dX/Y]`
    (the classical correspondence of extensions with periods of second-kind differentials).

  The name "W88 §5d for `G_a^{d₀} × G_m^{d₁} × Q`" rests on (I1)–(I3) and (I5). The truth of `thm11KappaAn5`,
  `thm11KappaAnK5` (and of lean_mstar's `two_three_beta5'` after adoption) does not: they are statements about
  explicit numbers (ζ₅, `perA5`, `perB5`).
* **Mixed curves in §5d.** `LSG.W88.hypStd_of_rat` (W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, different curves)
  assumes `hrat`: abelian subvarieties of `E₁ × ⋯ × E_m` have `ℚ̄`-rational tangent spaces. This is true for curves
  over `ℚ̄` but proved here only for a power of one curve (`abTan_rat_const`, used by `hypStdCM`, `hypStdCMAt`).
  `theorem41Abelian` itself needs no such hypothesis.
* **Subgroups.** The conclusion quantifies over `SubgroupData`, i.e. over products `H₀ × T_U × B`. For
  `G_a^{d₀} × G_m^{d₁} × A` every connected algebraic subgroup is such a product (all Hom groups between unipotent,
  toric and abelian pieces vanish in characteristic 0), so this is W88's family (reviews/REVIEW_STATEMENT.md §2). The
  classification of the obstruction subgroup is *proved* inside the multiplicity estimate (`LSG.ME.lieAlg_eq_prod`);
  the review's argument only concerns whether the statement quantifies over the right family.

## 3. Independent fidelity reviews

### 3a. The abelian statement

`reviews/REVIEW_STATEMENT.md` is a referee report on `Theorem41Abelian`, written on 2026-10-31 by an AI session that did not
write the proof. It compared the Lean statement with W88 pp. 385–386 (page images), the M\* paper's Theorem `thm:W88`,
and checked how Lean elaborates every cast and natural-number subtraction (`pp.coercions`, an `Iff.rfl` against a
fully explicit version).

**Verdict: CORRECT.** No fatal or major issue; equivalent to W88 Thm 4.1 for this `G` apart from (NR) and
`G₂ = ∏ E_j`; non-vacuous. Four minor remarks:
* M1: a docstring pointed to a file outside the repository (fixed: it now cites the M\* paper, Appendix A);
* M2: (NR) is a genuine weakening and must be stated in citations (see §2);
* M3: `Proper` is implied by `τ < δ` (redundant, harmless);
* M4: the lattice disjunct in `Lam` is redundant because Mathlib sets `℘(λ) = 0` at lattice points (harmless).

The review also looked at `MultEstAb` at a glance and found no issue. It did not review the vector-extension
statements, the copies of lean_mstar's statements (§5), or any proof.

### 3b. The vector-extension statements

`reviews/REVIEW_STATEMENT_VEC.md` is a second referee report, written on 2026-10-31 by an AI session that did not write the
proofs, on `StatementVec.lean`, `V5d2Stmt.lean` and `V5dOnto.lean`. It compared the definitions with W88 pp. 375,
385–386, 388–389 and 394–395 (page images), checked the elaborated casts and natural-number subtractions, the
`ℚ̄`-structure of `E^♮` and of the push-out, `LamV` = `exp_G⁻¹ G(ℚ̄)`, `PerV` = `ker exp_G`, soundness and completeness
of the subgroup family `SubgroupDataV`, and the bridges' use of lean_mstar's models.

**Verdict: no fatal or major issue in any statement**; every definition matches W88 for this class, and the proved
Props are non-vacuous. As a sanity derivation it proved in Lean (scratch file, standard axioms; text in the report's
appendix) that `η(ω₁) ∉ ℚ̄·ω₁` for the lemniscatic curve, three times: from `theorem41VecLA_onto`, from `theorem41Vec2`
and from `hyperplaneKappaVec_uncond`. Remarks:
* C1: the claim must state its scope (the cases of §2 above); "W88 Thm 4.1 for vector extensions" unqualified would
  be an overclaim;
* C2: the unproved targets are true if W88 Prop. 6.1 holds for the class (heuristic);
* m1–m3: stale documentation and docstrings (the documentation part is fixed; the docstring fixes in
  `StatementVec.lean` / `V5dOnto.lean` are listed as a TODO at the end of the report);
* m4: the lattice case of `LamV` depends on the junk value `ζ(λ) = η(λ)` of LSG's `ζ`, proved in-file
  (`zeta_of_mem_lattice`), so a change of definition would break the build rather than change `LamV`;
* m5: `Proper` and the lattice disjunct of `LamV` are redundant (harmless);
* m6: no Lean derivation yet exercises the non-lattice `ζ`-branch of `LamV` (a candidate check is described).

It did not check any proof. One status statement in the report is out of date: its verdict table and C1 list
`Theorem41VecLA` (non-onto `M`) as unproved, but `LSG.W88.theorem41VecLA` proves it for every algebraic `M` (commit
`4edd2d7`); see the erratum at the end of the report. §2 above uses the corrected scope.

### 3c. The toric-injectivity premise

`reviews/REVIEW_TORINJ.md` reviewed lean_mstar's narrowing of `Thm11KappaA` / `Thm11KappaAK` to toric-injective hyperplanes
(`HyperplaneKappaOn … TorInj`, lean_mstar `ec4a5ab`). **Verdict: CORRECT**, no fatal or major issue: the narrowed
hypotheses are implied by the old ones (checked in Lean), and every consumer in lean_mstar still applies. Its minor
note M1 (the bridge must match lean_mstar's period space) is resolved by `TorInjA` (§3d).

### 3d. The abelian-variety statements and the lean_mstar bridge

`reviews/REVIEW_STATEMENT_ABVAR.md` is a referee report, written on 2026-10-31 by an AI session that did not write the
proofs, on `StatementAbVar.lean`, the objects it uses (`latt`, `perVec`, `cycleE`, `perA5`, `kerE`) and the bridge files
`AbVarMStar.lean`, `AbVarMStarK.lean`, `AbVarFinal.lean`, `AbVar5dFinal.lean`, `MStarCopyAbVar.lean`. It compared them
with W88 pp. 375, 385–386 and 394–395 (page images) and with lean_mstar 9b8d036.

**Verdict: no fatal or major issue in any Lean statement.** Every definition matches W88 for this `G`; the model
`gmLsgA` is sound; the copies are verbatim. End-to-end check: lean_mstar's `two_three_beta5` and `wuestholzA5_of`,
applied to `thm11KappaA5`, use the standard axioms only. Non-vacuity witnesses in Lean: a nonzero subspace of `ℂ²`
that is not an abelian tangent, and the emptiness of the restricted form for `G = A^r`. Remarks:
* C1: the scope (§2 above); lean_mstar's paper sentence omitted the period-`A`-part restriction;
* m1: `Theorem41AbVarPer` was stated but not proved (fixed: `LSG.W88.theorem41AbVarPer`, `AbVarThm41.lean`, a
  coordinate translation of the block-generic `theorem41B_of`);
* m2: docstrings overstated `latt` and `PerA` (fixed: `latt` is a finite-index sublattice of `ker E`, `PerA` a
  finite-index subgroup of `Ω(G)` with the same `ℚ`-span; every use is index-insensitive);
* m3: lean_lsg's own `HyperplaneKappaOn` differed from lean_mstar's in premise order and shared its short name (fixed:
  renamed `HyperplaneKappaOnLsg`, documented as equivalent up to premise order);
* m4, m6: docstrings of `HyperplaneKappaAbVar` and of the module now state the `LamA` restriction and the
  emptiness for `d₀ = d₁ = 0`;
* m5: stale README/TRUST rows (fixed by this update);
* m7: the wording of "`A` is the Jacobian" (§2 above; the paper uses the review's wording).

It did not check any proof.

### 3e. The M2 statements (vector extension of the Jacobian) and the lean_mstar bridge

`reviews/REVIEW_STATEMENT_M2.md` is a referee report, written on 2026-11-01 by an AI session that did not write the proofs, on
`AbVarVStmt.lean`, `AbVarV5dHyp.lean`, the objects they use (`TanAV`, `etaB`, `PerAV`, `sPart`, `TorInjAV`,
`VBlockAn`, `VBlock`), the `aBlockV` fibre data, the frozen core `MultEstV`, and the bridge files `AbVarMStarN.lean`,
`AbVarMStarNK.lean`, `MStarCopyAbVarN.lean`, `MStarCopyAbVarNOn.lean`. It compared them with W88 pp. 385–386 and
394–395 and with lean_mstar `4d36ee3`.

**Verdict: no fatal or major issue in any Lean statement.** Every definition matches W88 for this `G`;
`SubgroupDataAV` is exactly the family of connected algebraic subgroups, and the `FibOK` conjunct of `gmLsgAV.sub` is
automatic for the instance; the fibre periods are the σ̄ second-kind periods. The copies are verbatim, and
`Thm11KappaAnOn` (the name then used here) is exactly the dev/M2.md §1.6 narrowing, implied by lean_mstar's `Thm11KappaAn` as it then stood. New in the
review (scratch, Lean, standard axioms): `perAn_inj` (lean_mstar's frame hyperplanes are toric-injective), the three
lean_mstar consumers re-run under the narrowed hypothesis, and `two_three_beta5'` and Wüstholz's `perB5/π ∉ ℚ̄`
derived from `thm11KappaAn5` against unmodified lean_mstar `4d36ee3`. Non-vacuity witnesses: `η̄(perVec 0) ≠ 0`,
a non-torsion fibre point in `LamAV`, and `sub` = the family for the instance. Remarks:
* C1: the scope (§2 above);
* C2: the final theorems targeted a narrowing that lean_mstar had not adopted; closed by lean_mstar `8458732` (§6);
* m1, m2: docstrings omitted the `LamAV` restriction and the conditions (`M` algebraic, `PerTanFib`) under which
  the generic Props are W88 instances (fixed);
* m3: stale README/TRUST rows and the `hilb_deg = 33` docstring in `MEBV/Block.lean` (fixed; the value is 41);
* m4: `Thm11KappaAnK` is covered only for `LAn = ∅` (stated in §2 and §6);
* m5: the short name `etaB` is used both for `LSG.AuxAV.etaB` (blockwise) and `LSG.JacAn.ThetaData.etaB` (fibre
  period), and the unrestricted copy `MStarCopy.Thm11KappaAn` is unused (both noted in docstrings).

It did not check any proof.

## 4. Sanity derivations

`LSG/W88/Sanity.lean` derives two classical theorems from the *statement* `Theorem41Abelian` (taken as a hypothesis)
and then instantiates them with the proved theorem:

* `gelfondSchneider_of`, `gelfondSchneider` (`G = G_m²`, `V = W = ℂ(1, b)`, `Y = ℤ(x, bx)`, κ = 0, (NR) `2 ≤ 2`): if
  `x ≠ 0`, `e^x` algebraic and `b` algebraic irrational, then `e^{bx}` is transcendental. Exercises `Lam` (toric part),
  `Per` through κ, `torusLie`, `τ`, `λ` and every cast.
* `period_of`, `period_transcendental'` (`G = G_a × E`, `V = W = ℂ(1, 1)`, `Y = ℤ(ω, ω)`): a nonzero period of a
  lattice with algebraic invariants is transcendental. Exercises the `G_a` part, the lattice disjunct, the weight
  `2δ₂` and `δ₀`.

In both cases every admissible subgroup violates the conclusion, so the hypotheses yield `False`; the statement has
teeth. The second derivation also cross-checks Stage 1: `LSG.Schneider.period_transcendental` proves the same theorem
by a different route (Schneider–Lang).

## 5. Copies of lean_mstar's statements

The bridges to `lean_mstar` are stated against **verbatim copies** of lean_mstar's definitions (bodies copied
verbatim, only the namespace changed):
* `LSG/W88/MStarCopy.lean` (`CM4E.Waldschmidt`: `GroupModel`, `HyperplaneKappa`, `gmE`, `Thm11Kappa`);
* `MStarCopyStd.lean` (`HypStd`, `HypStdCM`, `HypStdCMAt`, model `gmStd`; from lean_mstar `5026ff8`, `95ddbfa`);
* vector-extension models and hypotheses: `MStarCopyMX.lean` (`gmXG`, `Thm11KappaMXG`), `MStarCopyMGn.lean`
  (`gmMGn`, `gmMGnK`, `Thm11KappaMGn`, `Thm11KappaMGnK`), `MStarCopyNat.lean` (`gmQ`, `Thm11KappaNat`),
  `MStarCopySMGn.lean` (`gmSMGn`, `Thm11KappaSMGn` in the `KappaOneZero`-premised form of lean_mstar `1635927`),
  `MStarCopyMXP.lean` (`gmXP`, `Thm11KappaMXP`);
* abelian-variety models and hypotheses: `MStarCopyAbVar.lean` (`HyperplaneKappaOn`, `TorInj`, `thetaD`, `KspanD`,
  `IsAdaptedBasisD`, `zetaN`, `thetaA`, `perAgen`, `algA`, `gmA`, `Thm11KappaA`, `perA5`, `betaG`, `twistA`, `lamAK`,
  `gmAK`, `Thm11KappaAK`; from lean_mstar `9b8d036`);
* M2: `MStarCopyAbVarN.lean` (`perAngen`, `algAn`, `gmAn`, `Thm11KappaAn`, `perB5`) and, in `MStarCopyAbVarNOn.lean`,
  `twistAn`, `lamAnK`, `gmAnK`, `Thm11KappaAnK`; from lean_mstar `8458732`.

**How the copies are checked.** Each lean_lsg endpoint is typechecked against lean_mstar's **unmodified** definitions:
lean_mstar has lean_lsg as a Lake path dependency and proves its own hypotheses from the lean_lsg theorems, for
example `example : CM4E.Gen.Thm11KappaMXP := fun h1 h2 h3 h4 r b hb => LSG.W88.V5d.thm11KappaMXP_uncond h1 h2 h3 h4 r b
⟨hb.indep, …⟩` (the copies of the structures `CMLattice` and `IsAdaptedFieldBasis` are repackaged field by field; the
exact lines are in dev/INTERFACE.md). The lean_mstar commits that do this are:
* `3118c4d`, `d55b0c7`, `f9f4cca` (abelian: `Thm11Kappa`, `HypStdCMAt`, `HypStdCM`; copies from `5026ff8`, `95ddbfa`);
* `ce7e12f` (`Thm11KappaMXG`, `Thm11KappaMGn`, `Thm11KappaMGnK`, `Thm11KappaNat`; lean_lsg `0ed4c24`);
* `6685a57` (`Thm11KappaSMGn`, statement of `1635927`; lean_lsg `36b7f5c`);
* `785303b` (`Thm11KappaMXP`; lean_lsg `4f27015`);
* `9b569e0` (`AbVar.Thm11KappaA 5 …`, `AbVar.Thm11KappaAK 5 … ∅`, in `CM4E/Bridge/AbVar.lean`; lean_lsg `483e2b0`);
* `8458732` (`AbVar.Thm11KappaAn 5 …`, `AbVar.Thm11KappaAnK 5 … ∅`, in `CM4E/Bridge/AbVar.lean`).

The checks are in lean_mstar's `CM4E/Bridge/` (the vector-extension ones in `CM4E/Bridge/Vec.lean`) and
`CM4E/Unconditional.lean`.

So a drift of a copy away from lean_mstar's definition breaks lean_mstar's build instead of passing silently. Whether
lean_mstar's group models are true of the groups they describe is checked by lean_mstar's own reviews, not by this
project; reviews/REVIEW_STATEMENT_VEC.md §7 looked at the vector-extension models in passing and found nothing wrong, and the
bridges prove model soundness (`hsub`) for every nonzero `SubgroupDataV`.

## 6. Relation to lean_mstar: which hypotheses are discharged

`lean_mstar` assumes W88 for specific groups as named hypotheses `hW : HyperplaneKappa G`. This project provides:

| lean_mstar hypothesis | discharged by | status |
|---|---|---|
| `Thm11Kappa L d₁` (W88 §5d for `G_m^{d₁} × E`) | `LSG.W88.thm11Kappa L d₁` | unconditional |
| `Bridge.HypStdCMAt L d`, `HypStdCM L` (§5d for `G_a^{d} × G_m^{d₁} × E^r`) | `LSG.W88.hypStdCMAt`, `LSG.W88.hypStdCM` | unconditional; lean_mstar derives `Gen.Thm11KappaMG`, `SMG`, `M`, `MGK` from it |
| `HypStd` (mixed curves) | `LSG.W88.hypStd_of_rat` | needs `hrat` (§2) |
| `hg₂ : IsAlgebraic ℚ lemniscatic.g₂` | `LSG.Bridge.isAlgebraic_g₂ CM4E.lemniscatic rfl rfl` | unconditional |
| `hS : Irrational (varpi / π)` | `LSG.Bridge.irrational_varpi_div_pi_of` | unconditional |
| `Gen.Thm11KappaMXG`, `Gen.Thm11KappaMGn L`, `Gen.Thm11KappaMGnK L` (every `CMLattice`), `MainNat.Thm11KappaNat` | `LSG.W88.V5d.thm11KappaMXG_uncond`, `thm11KappaMGn_uncond`, `thm11KappaMGnK_uncond`, `thm11KappaNat_uncond` (via `theorem41VecLA_onto` and `hyperplaneKappaVec_uncond`, `r ≤ 1`) | unconditional; `LiftAlg`, `PerTanRat` proved for the CM curves |
| `Gen.Thm11KappaSMGn L` | `LSG.W88.V5d.thm11KappaSMGn_uncond` | unconditional; carries the premise `KappaOneZero L` (κ₁ = 0), as in lean_mstar's statement since `1635927` |
| `Gen.Thm11KappaMXP` (MX′, `r = 2`) | `LSG.W88.V5d.thm11KappaMXP_uncond` (via `theorem41Vec2` and `hyperplaneKappaVec2_uncond`, `d₀ = 0`, `r = 2`) | unconditional |
| `AbVar.Thm11KappaA 5 2 (·+1) perA5 0` (Theorem A at `B(1/5,1/5)`), `AbVar.Thm11KappaAK 5 2 (·+1) perA5 0 ∅` (Corollary A2) | `LSG.W88.thm11KappaA5`, `LSG.W88.thm11KappaAK5` (via `hyperplaneKappaAbVar`; scope §2) | unconditional |
| `AbVar.Thm11KappaAn 5 2 (·+1) perA5 perB5` (Theorem MG♮-A at `B(1/5,1/5)`), `AbVar.Thm11KappaAnK 5 2 (·+1) perA5 perB5 ∅`, both on toric-injective hyperplanes (`HyperplaneKappaOn … TorInj`, dev/M2.md §1.6, lean_mstar `8458732`) | `LSG.W88.thm11KappaAn5`, `LSG.W88.thm11KappaAnK5` (via `hyperplaneKappaAbVarV_aBlockV`; scope §2) | unconditional; `K`-form only for `LAn = ∅` |
| other CM abelian-variety hypotheses (`Thm11KappaX7`, `Thm11KappaXA`, `Thm11KappaA 7 …`) | — | not covered (later scope; design note `dev/ABVAR.md`) |

So in lean_mstar the four exponentials statements at `cϖ/π` and at `cϖ` (Theorem 1.1(a)), Theorem M for `Ω = cϖ`, MG,
MG♮, MX, MX1, MX′, deg2 and Theorem S are unconditional on W88 (some still use other named classical inputs, listed in
lean_mstar's README and TRUST). Of the abelian-variety results, those at `B(1/5,1/5)` are unconditional on W88
(lean_mstar `9b569e0`, `d7c6da1`: `two_three_beta5_uncond`, `wuestholzA5_uncond`, `fourExpAt_beta5_uncond`,
`fourExpAt_pi_div_beta5_uncond`, `mgA5_K_uncond`; `corA2_beta5_uncond` keeps the named input `NotLtildeA (perA5 0)`);
the others remain conditional. Theorem MG♮-A at `B(1/5,1/5)` is also unconditional on W88 (lean_mstar `8458732`:
`two_three_beta5'_uncond`: `2^t, 3^t` at `t = B(1/5,1/5)`; `wuestholzB5_uncond`, `fourExpAt_beta5'_uncond`,
`fourExpAt_div_beta5_uncond`, `mgAn5_K_uncond`). lean_mstar no longer keeps a copy of part of this library: `b4f8018` removed `CM4E/Ext/` and imports it directly.

## 7. Generated files and kernel certificates

### 7a. Vector extensions

Some files of the vector-extension layer contain polynomial identities with cofactors produced by Python scripts
(sympy, python-flint). The scripts are **untrusted inputs**: each identity is re-proved in Lean (`ring`,
`linear_combination`), so a wrong cofactor makes the build fail.

| Lean files | generator |
|---|---|
| `LSG/Elliptic/NaturalLawsPoly.lean`, `NaturalLawsAff.lean`, `NaturalLawsSpecial.lean` | `scripts/vecext_spike/` (`kappa.py`, `verify5.py`, `affine_ids.py`, `gen_lean.py`, `gen_special.py`) |
| `LSG/MEV/FibreId00.lean` … `FibreId11.lean` | `scripts/mev_curve/` (`defs.py`, `fibre_ids.py`, `gen_fibre.py`) |

A few hand-placed identities elsewhere also use cofactors found with sympy (for example the chart change
`cc_blk` in `LSG/MEV/HomDeriv.lean`); they are likewise re-proved in Lean. Since the vector-extension results joined the
default target, these files are part of it (they feed `multEstVec` and everything built on it). The abelian chain
(`theorem41Abelian` and the abelian §5d bridges) imports none of them and uses no generated data.

### 7b. The Jacobian block (`LSG/Jac/`, `LSG/JacBlock/`)

The facts about Grant's model of `A` (the addition laws preserve the model, flow invariance, doubling identities, the
degree-7 Nullstellensatz for `dup X ≠ 0`, the local complete-intersection systems, …) are polynomial identities in
nine variables, too large for `ring`. They are checked as follows.
* **The Python generators are untrusted.** `scripts/jac/` (`gen_jac_*.py`; python-flint, exact `fmpq`/`fmpz`)
  produces the identity data (`LSG/Jac/Data/`, ≈ 22k lines, ≈ 6 MB) and the certificate files (`LSG/Jac/Cert/`,
  88 files). `scripts/jacblock/` produces the smaller certificates of `LSG/JacBlock/` (surjectivity, Hilbert bound,
  tangency), which are re-proved by `ring` / `linear_combination` (`dev/STAGE_A4_GAMMA.md`).
* **M2 (`A^♮`)** adds 10 files with the same checker: `scripts/jac/gen_jac_b6vsem.py` generates `LSG/Jac/B6V.lean`
  (the Hilbert bound `hilbV` in degree 41 and the Wronskian cocycle `kappaV`), `LSG/Jac/Data/B6V.lean` and eight
  `decide +kernel` certificates `LSG/Jac/Cert/B6V_<v>.lean` (identities `D_v X_v⁵ = Σ c_k sub(G_k)`). They are small
  (≈ 0.8k lines in all). The 81 fibre laws of `aBlockV` are not certificates: they are defined by `pderiv` from the
  certified A-laws and proved correct semantically (`LSG/JacBlockV/Laws.lean`).
* **The kernel rechecks every certificate.** Each `Cert/` declaration is a Boolean computation (packed normal forms
  modulo the ideal of the model, accumulated in Kronecker-packed natural numbers) proved `= true` by
  `decide +kernel`, i.e. evaluated by the Lean kernel, not by compiled code. There is no `native_decide`.
* **A soundness theorem turns the computation into mathematics.** `CheckerSound.lean` (`sound2`, `sound_bidegree`),
  `NFSound.lean` (the normal-form tables), `P2Sound.lean`, `RangeSound.lean` and `SplitSound.lean` (ranges and
  splits of one check), `B56Sound.lean`: if the check returns `true`, the stated polynomial identity holds over any
  commutative ring (in particular over `ℂ`, and in `MvPolynomial (Fin 9) ℂ`). The semantic files (`E1Sem_*`, `V1`,
  `V2`, `P2`, `B56`, `E1Final`) state the identities in ordinary mathematical form, and `a1Facts : A1Facts` packages
  them for the analytic side. A wrong generator output makes the build fail; it cannot produce a false theorem.

**Cost and memory.** The certificates take about 5 CPU-hours to check (about 2.7 h wall-clock two files at a time;
logs in `scripts/jac/build_*.log`; the E1 family alone is about 1300 range declarations and 4.5 CPU-hours). Each
declaration stays below about 3.5 GB, but a whole-file `lean` process creeps up to **4–5 GB** for the E1 files (E44:
4.96 GB, dev/STAGE_A1.md §10.6; up to 7.6 GB was sampled in the four-at-a-time cold build), so building many of them in parallel needs a lot of RAM (README, "Building and
checking").

## 8. Licence history

An earlier stage ported, for local use only, about 1.5k lines of Lean from the ancillary files of Chudnovsky–
Chudnovsky, arXiv:2610.31112 (the lemniscatic period identification `g₂ = 4`). Their licence did not cover those files
(the source grants Apache-2.0 only for a different subtree). The port was never published. It was deleted and replaced
by an independent proof, `LSG/LemniscateIndep/` (628 lines), written by an agent that never opened the vendor tree or
the ported files (route: square-lattice symmetries, the real branch of `℘` on `(0, ϖ/2]`, the Beta integral).
The private development history contains the port (commit `46f0cd8`; removed in `5fa6997`), so it is not published: the
public repository starts from one fresh commit that excludes it. Hashes of this project's commits cited in this file refer
to that development history.

`LSG/SchneiderLang/Analytic.lean` and `Arith.lean` adapt lemmas from StrongSix (same author, Apache 2.0). No other
external Lean code is included.

## 9. What has not been checked

* No human expert has read the statements or the proofs.
* The vector-extension review (§3b) checked statements only; its suggested extra derivation (m6, the non-lattice
  `ζ`-branch of `LamV`) has not been done. Its docstring fixes m1–m3 are done.
* The abelian-variety review (§3d) checked statements only. The identifications (I1)–(I4) of §2 (Abel–Jacobi
  uniformisation, Chow and Goursat, the change of model, Grant's theorem) are classical [Lit] and not formalised.
* The M2 review (§3e) checked statements only. The identification (I5) of §2 (the `ℙ¹¹` model is `A_σ̄^♮`) is classical
  [Lit] and not formalised.
* The cold build (README, "Building and checking") reused prebuilt Mathlib; the machine, the time and the memory are
  recorded there. It has been run on one machine only.
* The prior-formalisation claims (README, paper) rest on a search done on 2026-10-30 (web, Mathlib v4.35.0, our
  collected prior-art folders) and a shorter web-only search on 2026-11-06 that found nothing new; they should be
  rechecked just before submission.
