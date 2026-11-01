# Referee report: the abelian-variety statements (`StatementAbVar.lean`) and the lean_mstar bridge (M1)

Date: 2026-10-31.

**Scope.** Do the **statements** below say what they claim, and are they non-vacuous? The claim is W88 Thm 4.1
(pp. 385–386) and W88 §5d (5.4) (pp. 394–395) for G = G_a^{d₀} × G_m^{d₁} × A^r, with A the Jacobian of
y⁵ = x(1 − x) (in the model Y² = 4X⁵ + 1), restricted to toric-injective hyperplanes. I did not check the proofs;
Lean did. Same format as `REVIEW_STATEMENT.md`, `REVIEW_STATEMENT_VEC.md` and `REVIEW_TORINJ.md`.

**Statements reviewed:**
* `LSG/W88/StatementAbVar.lean`: `TanA`, `AlgVecA`, `AlgTanA`, `RationalOverQbarA`, `LamA`, `PerA`, `IsAbelianTangentA`,
  `SubgroupDataA` (`tan`, `δ0`, `δ1`, `δ2`, `δ`, `Proper`), `TorInjA`, `Theorem41AbVarPer`, lean_lsg's own
  `HyperplaneKappaOn`, `gmLsgA`, `HyperplaneKappaAbVar`.
* The underlying objects: `latt` (`LSG/JacAn3/Normalize.lean`), `perVec` (`LSG/JacAn/Rank4.lean`), `cycleE`, `omegaJ`,
  `perA5` (`LSG/JacAn/BetaPeriods.lean`), `kerE` and `lattice_le_ker` (`LSG/JacAn/PeriodKer.lean`),
  `isNsmulIn_latt_kerE` (`LSG/W88/AbVarPer.lean`).
* The bridge: `LSG/W88/AbVarMStar.lean`, `AbVarMStarK.lean`, `AbVarFinal.lean`, `AbVar5dFinal.lean`,
  `MStarCopyAbVar.lean`.

**Sources compared:**
* W88 page images in `schanuel/five_exp/ref/w88_pages/`: `w88-01.png` (p. 375: G any commutative algebraic group over
  ℚ̄, G₂ of dimension d₂ = d − d₀ − d₁), `w88-06.png`, `w88-07.png` (pp. 385–386, Thm 4.1 and δ…τ).
* lean_mstar at 9b8d036: `CM4E/AbVar/ThmA.lean`, `MGAK.lean`, `Basis.lean`, `Fermat7.lean`, `CM4E/Waldschmidt.lean`,
  `CM4E/Gen/Frame.lean`. lean_mstar moved to d7c6da1 during this review (another session added
  `CM4E/Bridge/AbVar.lean` and doc changes). `git diff 9b8d036 d7c6da1` touches none of these files.
* `ABVAR.md` §1.2, §2.0, §2.3; `REVIEW_TORINJ.md`; lean_mstar `TRUST.md` and `paper/paper.tex` (the AbVar sentences).

## Verdict

**No FATAL or MAJOR issue in any Lean statement.**
* Every definition matches W88 for this G. The model `gmLsgA` is sound.
* The bridge targets verbatim copies of lean_mstar's `Thm11KappaA` / `Thm11KappaAK`. The end-to-end check passes:
  lean_mstar's `two_three_beta5` and `wuestholzA5_of`, applied to lean_lsg's theorem, use standard axioms only (§5).
* The caveats are about scope and documentation. The proved §5d statement has two restrictions:
  - the hyperplane must be toric-injective;
  - every `y` must have its `A`-part in the period lattice, so Γ has trivial `A`-component.

  The second restriction is missing from lean_mstar's paper sentence (issue C1). Some docstrings overstate what `latt`
  and `PerA` are (m2).

| Prop / definition | Verdict | Status in the repo |
|---|---|---|
| `TanA`, `AlgVecA`, `AlgTanA`, `RationalOverQbarA` (the ℚ̄-structure) | CORRECT | — |
| `latt` | CORRECT: a finite-index sublattice of the period lattice of Jac(C) (docstring overstates; m2) | `latt ≤ kerE`, `kerE ⊆ ℚ·latt`, rank 4: proved |
| `LamA` | CORRECT: logarithms of points `(a, e^b, 0)`, a deliberate restriction (C1) | — |
| `PerA` | CORRECT WITH CAVEATS: possibly a finite-index subgroup of Ω(G); harmless (§1, m2) | — |
| `IsAbelianTangentA` | CORRECT; not always satisfiable (Lean witness, §6) | — |
| `SubgroupDataA`, `tan`, `δ0`, `δ1`, `δ2`, `δ`, `Proper` | CORRECT | — |
| `TorInjA` | CORRECT: the `TorInj` of REVIEW_TORINJ, with `per` = full ℚ-period space | — |
| `Theorem41AbVarPer` | CORRECT WITH CAVEATS (C1; m1) | **not proved** (no theorem has this type) |
| lean_lsg `HyperplaneKappaOn` | CORRECT: equivalent to lean_mstar's up to premise order (Lean-checked), but not verbatim (m3) | — |
| `gmLsgA` | CORRECT (sound model) | — |
| `HyperplaneKappaAbVar` | CORRECT WITH CAVEATS (C1; empty for d₀ = d₁ = 0, m6) | **proved**: `LSG.W88.hyperplaneKappaAbVar` |
| `MStarCopyAbVar.lean` copies | CORRECT: verbatim, confirmed by the end-to-end typecheck | — |
| `thm11KappaA5`, `thm11KappaAK5` | CORRECT: they are lean_mstar's statements | **proved**, standard axioms |

## 1. Coordinates, `latt`, `LamA`, `PerA`, the ℚ̄-structure

**The curve and the coordinates** [Proved, partly in Lean].
* X = −y, Y = 2x − 1 maps y⁵ = x(1 − x) onto Y² = 4X⁵ + 1, since Y² = 1 − 4x(1 − x) = 1 − 4y⁵ = 1 + 4X⁵. It is an
  isomorphism of the smooth projective models, with inverse x = (Y + 1)/2, y = −X.
* Lean uses only the second model. The lifts `liftPath e` are the images of the lifts of [0, 1] on the first model:
  `liftPath_mem_curve` checks they lie on Y² = 4X⁵ + 1.
* `omegaJ j = X^j dX/Y`, j = 0, 1, is a ℚ-basis of H⁰(C, Ω¹) (genus 2, odd-degree model).
* The A-coordinates of `TanA` are z_j = ∫ X^j dX/Y. These are coordinates dual to a ℚ-rational basis of invariant
  differentials. So "all coordinates algebraic" (`AlgVecA`) is the ℚ̄-structure of Lie A [Lit, standard].
* lean_mstar's coordinates are dual to dx/y^{4−s}. On C one has dX/Y = (1/5) dx/y⁴ and X dX/Y = −(1/5) dx/y³, so its
  coordinates are 5(−1)^s z_s. That is exactly `cA` in `iotaA`, and the scaling is algebraic, so the two ℚ̄-structures
  agree. Lean checks the corresponding identity of numbers, `perA5_scale`:
  `ζ^{(s+1)e} perA5 s = cA s · perVec e s`.

**`latt` is a full-rank sublattice of the period lattice** [Proved in Lean, plus a one-line Lit identification].
* `perVec e = ∫_{cycleE e} (dX/Y, X dX/Y)`. Here `cycleE e = [ζ^e]ℓ · ([ζ^{e+1}]ℓ)⁻¹` is a closed loop on C at (0, −1).
  - The integrals are computed in Lean: `curveIntegral_cycleE`, giving c_j (ζ^{j+1})^e with
    c_j = ((−1)^j/5)(1 − ζ^{j+1})B((j+1)/5, (j+1)/5).
  - The improper point Y = 0 at t = 1/2 is handled twice: once a.e. in `BetaPeriods.lean`, and once by a perturbed
    path with Y ≠ 0 throughout and the same Abel integral (`exists_pert_lift`).
* The four periods are ℝ-linearly independent (`linearIndependent_perVec`). So `latt` has rank 4 in ℂ² ≅ ℝ⁴.
* Every integral of a holomorphic differential over a closed loop on C is a period. So `latt ⊆ Λ_C`, where Λ_C is the
  H₁-period lattice, and the index is finite since both have rank 4.
* Lean additionally proves the same against its own analytic exponential:
  - `lattice_le_ker`: `latt ≤ kerE G` for every base. The A1 interface is instantiated: `LSG.Jac.a1Facts`.
  - `kerE` is discrete.
  - `isNsmulIn_latt_kerE`: `kerE ⊆ ℚ·latt`.
* So `ℚ·latt = ℚ·kerE = ℚ·Λ_C`. Whether `latt = Λ_C` (Rohrlich-type cyclicity) is not decided, and nothing below needs
  it.

**`LamA`** is a set of logarithms of algebraic points [Proved].
* a ∈ ℚ̄^{d₀}, e^{b_i} ∈ ℚ̄, and the A-part lies in `latt^r ⊆ ker exp`. So exp_G(p) = (a, e^b, 0) ∈ G(ℚ̄). The origin
  of the model is `e₄ = origin9`, which is algebraic, and `germ_zero` gives exp(0) = e₄.
* `LamA` is much smaller than Λ(G): it contains only the points with trivial A-component. This is the design choice of
  ABVAR §2.3 ("rational-period A-parts"). The scaling lemma `hyperplaneKappaOn_spanLam` extends it to `span_ℚ LamA`,
  i.e. torsion A-components. That covers lean_mstar's `gmA` and `gmAK … ∅`, whose logarithm generators are toric
  logarithms and periods. It is a genuine restriction of W88 and must be stated (C1).

**`PerA` vs Ω(G)** [Proved].
* `PerA = 0 × 2πiℤ^{d₁} × latt^r`. This is a finite-index subgroup of Ω(G) = 0 × 2πiℤ^{d₁} × Λ_C^r, and equal to it if
  `latt = Λ_C`.
* Every use is insensitive to the index:
  - `gmLsgA.per` and `TorInjA` use `span_ℚ PerA = ℚ ⊗ Ω(G)`.
  - κ in `Theorem41AbVarPer` is `rk(Y ⊓ PerA)` with `Y ⊆ LamA`. A `y ∈ Y` already has its A-part in `latt^r`, so
    `Y ∩ PerA = Y ∩ Ω(G)` exactly.
  - λ uses `Y ⊓ (tan ⊔ PerA)`. If y = t + ω with ω ∈ Ω(G), then Nω ∈ PerA for some N ≥ 1. So
    `span_ℚ(Y ∩ (tan + PerA)) = span_ℚ(Y ∩ (tan + Ω(G)))`, and `rk` is a ℚ-dimension.
  - `IsAbelianTangentA` uses the ℝ-span of `t ∩ latt^r`, which equals the ℝ-span of `t ∩ Λ_C^r` (same N argument).
* The docstrings "Its period lattice is Λ = latt" (l. 13) and "`PerA` (periods, Ω(G) = ker exp_G)" (l. 22) overstate
  this (m2).

## 2. `SubgroupDataA`: exactly the connected algebraic subgroups

* **Products** [Lit/Proved, as in `REVIEW_STATEMENT.md` §2]. A connected algebraic subgroup of
  G_a^{d₀} × G_m^{d₁} × A^r is H₀ × T_U × B. The proof is Goursat: Hom between any two of G_a, G_m and A vanishes in
  characteristic 0.
* **`IsAbelianTangentA t` ⇔ t = T(B) for an abelian subvariety B ⊆ A^r** [Lit, standard].
  - If `t ∩ latt^r` spans t over ℝ, then t/(t ∩ Λ^r) is a compact complex subtorus of A^r. Such a subtorus is an
    abelian subvariety: it is a closed analytic subgroup of a projective variety, so Chow applies. It is defined over
    ℚ̄, since A is.
  - Conversely, T(B) ∩ Λ^r is a full lattice in T(B).
  - ℚ̄-rationality of t is automatic. lean_lsg even proves it for this A in Lean (`ratTangentsA`, CM argument).
* **Codimensions** (p. 386):
  - δ₀ = d₀ − dim h₀;
  - δ₁ = dim_ℚ U, since dim_ℂ U^⊥ = d₁ − dim U;
  - δ₂ = 2r − dim t = codim of B in A^r = δ − δ₀ − δ₁;
  - δ = δ₀ + δ₁ + δ₂.
  All the ℕ-subtractions are exact: `finrank t ≤ 2r = finrank (Fin r → Fin 2 → ℂ)`, and `finrank h₀ ≤ d₀`.
* **`Proper`** ⇔ δ ≠ 0 ⇔ G′ ≠ G. G′ = 0 is allowed (h₀ = ⊥, U = ⊤, t = ⊥).

## 3. `TorInjA`, `Theorem41AbVarPer`, `HyperplaneKappaOn`, `gmLsgA`, `HyperplaneKappaAbVar`

**`TorInjA V`** says: every v ∈ V ∩ span_ℚ PerA with v.2.1 = 0 is 0.
* v ∈ span_ℚ PerA forces v.1 = 0. So TorInjA says V contains no nonzero element of 0 × 0 × ℚ·latt^r, i.e. no nonzero
  ℚ-period of A^r alone.
* This is REVIEW_TORINJ's `TorInj`, with `per` the full ℚ-period space (`ℚ·latt = ℚ·kerE`). So REVIEW_TORINJ M1 (the
  bridge must match `per`) is resolved.
* The bridge proves `ι(PerA) ⊆ gmA.per` (`hmem`, via `latt_repr'` and `genA`), so lean_mstar's `TorInj V` implies
  `TorInjA (ι⁻¹V)`. This is the safe direction: the lean_lsg hypothesis applies to more hyperplanes.

**`Theorem41AbVarPer`** is `Theorem41Abelian` with `Tan → TanA`, `m ↦ 2r` (d₂ = 2r), `Lam → LamA`, `Per → PerA`, and the
extra premise `TorInjA V`.
* The inequality reads (λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2·2r − κ) with d = d₀ + d₁ + 2r. This is verbatim p. 386.
* (NR) is `d₁ + 2d₀ + κ ≤ 2N`, the same documented weakening as in `REVIEW_STATEMENT.md` M2.
* The casts are the same as in the abelian statement (`REVIEW_STATEMENT.md` §4): the ℤ-subtractions d − N, δ − τ and
  d₁ + 4r − κ cannot truncate, and every ℕ-subtraction is exact.
* It is a special case of W88 Thm 4.1, so it is true [Lit].
* **No Lean theorem has this type** (m1). The proved Thm 4.1 is the generic `theorem41B_of` for block families
  (`AbVarSec7.lean`, from `multEstB_holds`). `Theorem41AbVarPer` is its exact analogue in `TanA` coordinates, but the
  instantiation is not written.

**lean_lsg's `HyperplaneKappaOn`** (l. 159) has the premise `good V` after `G.Rational W`. lean_mstar's has it right
after the binders.
* The two are logically equivalent. The scratch file proves the `↔` by permuting arguments (Appendix).
* They are not definitionally equal. The docstring calls it "lean_mstar's HyperplaneKappaOn", and the name clashes with
  the verbatim copy `MStarCopy.HyperplaneKappaOn` (m3). `hkOn_transport` already bridges the two orders correctly.

**`gmLsgA`** is sound for G = G_a^{d₀} × G_m^{d₁} × A^r.
* d₁ = d1 and d₂ = 2r. d₀ and d₁ are maximal, since A^r has no G_a or G_m quotient, so (5.4) does not involve d₀.
* `lam = LamA ⊆ Λ(G)`.
* `per = span_ℚ PerA = ℚ ⊗ Ω(G)`.
* `sub ⊇` the Lie algebras of all connected algebraic subgroups (§2).

**`HyperplaneKappaAbVar` = ∀ d₀ d₁ r, `HyperplaneKappaOn (gmLsgA d₀ d₁ r) TorInjA`.**
* This is W88 §5d (5.4) for this G [p. 394; (5.4) read with rk Y, as in `REVIEW_STATEMENT_VEC.md` §3], under two
  restrictions:
  1. V is toric-injective;
  2. every y_i ∈ LamA, so Γ = exp(Y) ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × {0}. Up to the scaling lemma, the A-components are
     torsion.
* Both restrictions only weaken the statement, so it is implied by W88 [Lit]. It is proved in Lean
  (`LSG.W88.hyperplaneKappaAbVar`, standard axioms).
* There is no (NR), as in the other §5d forms. Under TorInj, κ ≤ d₁ (REVIEW_TORINJ §3(d)).

## 4. The bridge

**The copies** (`MStarCopyAbVar.lean`) were compared by reading them against lean_mstar 9b8d036. These are verbatim,
including binders and `variable` contexts:
* `HyperplaneKappaOn` (good V first, as in REVIEW_TORINJ M3);
* `TorInj`;
* `thetaD`, `KspanD`, `IsAdaptedBasisD`;
* `zetaN`, `thetaA`, `perAgen`, `algA`, `gmA`, `Thm11KappaA`, `perA5`, `betaG`;
* `twistA`, `lamAK`, `gmAK`, `Thm11KappaAK`.

The older copies (`GroupModel`, `gmF`, `gmF2`, `perGen`, `lamGen`, `tor1/2`, `qv`, `dotL`, `PsiG`, `TF`) are covered by
the end-to-end typecheck below, which needs definitional agreement of every unfolded constant.

**The transport** (`hkOn_transport`, `iotaA`) is sound in every component:
* ι is the toric reindexing plus `q(s, j) = 5(−1)^s z_j(s)`, an algebraic scaling. So algebraic vectors correspond and
  `G.Rational W` transfers.
* `G.lam ⊆ ι(span_ℚ LamA)`. Common denominators make `rk` unchanged.
* `G.per ⊆ ι(span_ℚ PerA)`, so κ_mstar ≤ κ_lsg, which only strengthens the transferred premise. With `hmem` the two
  spans are in fact equal.
* d₁ and d₂ agree: 2|ι| and `finrank (Fin 2 × Fin r → ℂ) = 2r`.
* Every nonzero `SubgroupDataA` tangent lands in lean_mstar's `sub`.
  - For `gmF`: `lam_ne_zero_of_abelian`. A nonzero abelian t contains a nonzero lattice point z, and Σ b_j z_j(0) ≠ 0
    by ℚ-independence of ζ^e b_j.
  - For `gmF2`: `exists_alg_lam_ne` (an algebraic such z, using `ratTangentsA`), or a rational toric vector.
  - So lean_mstar's `sub`-soundness for these two models is now a Lean theorem, relative to the classification in §2.
    REFEREE_HYP_A needed the CM classification (Shimura–Taniyama) here.
* `good`: TorInj ⇒ TorInjA (§3).

**End-to-end check** (scratch file in lean_mstar's root, `lake env lean`, deleted afterwards). Lake reports
`LSG.W88.AbVarFinal` up to date (`lake build --no-build`). The lean_mstar oleans are newer than their sources, and
those files have no uncommitted changes. Output:

```
'scratch_thmA5' depends on axioms: [propext, Classical.choice, Quot.sound]
'scratch_thmAK5' depends on axioms: [propext, Classical.choice, Quot.sound]
'scratch_two_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.hyperplaneKappaAbVar' depends on axioms: [propext, Classical.choice, Quot.sound]
'scratch_wuestholz' depends on axioms: [propext, Classical.choice, Quot.sound]
'scratch_t0_not_abelian' depends on axioms: [propext, Classical.choice, Quot.sound]
'scratch_pureA_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `scratch_thmA5 : CM4E.AbVar.Thm11KappaA 5 2 (fun s => (s:ℕ)+1) CM4E.AbVar.perA5 0` is
  `fun r b hb => LSG.W88.thm11KappaA5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩`, exactly as briefed.
  The same holds for `Thm11KappaAK … ∅`.
* `scratch_two_three := CM4E.AbVar.two_three_beta5 scratch_thmA5`.
* `scratch_wuestholz := CM4E.AbVar.wuestholzA5_of scratch_thmA5`, which is Wüstholz's (1 − ζ₅)B(1/5,1/5)/π ∉ ℚ̄.
* lean_mstar's own `CM4E/Bridge/AbVar.lean` (added by another session as 9b569e0) does the same repackaging.

## 5. What is proved about "A is the Jacobian", and what is identification

**The statements involve no Jacobian object.**
* `gmLsgA`, `HyperplaneKappaAbVar` and `Theorem41AbVarPer` mention A only through `latt ⊆ ℂ²` (in `LamA`, `PerA` and
  `IsAbelianTangentA`) and the standard ℚ̄² structure.
* lean_mstar's `Thm11KappaA 5 …` mentions only the numbers ζ₅ and `perA5`.
* `expP`, `kerE`, Grant's model V(Q) and `A1Facts` appear only inside proofs.

So the truth of `thm11KappaA5`, and of lean_mstar's `two_three_beta5_uncond` etc., depends on no modelling
identification. Since M1, these results no longer rest on REFEREE_HYP_A's model soundness either: they are kernel
theorems about explicit numbers. The identification matters only for the *name*: the claim that the proved Prop "is
W88 §5d for G_a^{d₀} × G_m^{d₁} × Jac(C)^r".

**Proved in Lean:**
* The four generators of `latt` are integrals of X^j dX/Y over explicit loops on Y² = 4X⁵ + 1, with Beta closed forms
  (`curveIntegral_cycleE`, `liftPath_mem_curve`).
* They equal lean_mstar's `perA5` up to the factor 5(−1)^s (`perA5_scale`, `period_omega0/1`).
* `latt` has rank 4 (`linearIndependent_perVec`).
* For the concrete analytic map `expP : ℂ² → ℙ⁸` built on the certified Grant-model data `a1Facts`:
  - `latt ⊆ ker expP`, `ker expP` is discrete, and `ker expP ⊆ ℚ·latt` (`lattice_le_ker`, `isNsmulIn_latt_kerE`);
  - `expP` does not depend on the base divisor (`expP_base_indep`);
  - `expP` is compatible with Abel integrals along paths: E(∫_{D₀}^{D} ω) is the Grant point of the Mumford coordinates
    of D (`expP_periodic_of_paths`, `PeriodKer.lean`);
  - every nonzero point of V(Q) is c·θ_N(z) (`ThetaData.surjA` with `surjFacts : SurjFacts a1Facts`).

  So ℂ²/ker expP → V(Q) is a bijective analytic group homomorphism compatible with the Abel–Jacobi map.
* Every abelian tangent of A^r is ℚ̄-rational (`ratTangentsA`).
* A nonzero abelian tangent is not killed by λ (`lam_ne_zero_of_abelian`).

**Identification, not provable in Lean today (no Mathlib Jacobian)** [Lit]:
* (I1) The Abel–Jacobi uniformisation: Jac(C)(ℂ) ≅ ℂ²/Λ_C in the coordinates (∫dX/Y, ∫X dX/Y), with ℚ̄-structure
  dual to H⁰(C, Ω¹_{/ℚ}). Combined with the Lean facts, ℂ²/latt is isogenous to Jac(C), the ℚ-period spaces agree,
  and the ℚ̄-structures agree.
* (I2) Complex subtori of A^r are abelian subvarieties (Chow), and Goursat (§2).
* (I3) The isomorphism y⁵ = x(1 − x) ≅ Y² = 4X⁵ + 1. It is elementary (§1). Lean uses it only to build the lifts.
* (I4) Not needed for any statement, only for the stronger phrase "Lean constructs the Jacobian": V(Q), with the
  certified law, is the Jacobian (Grant 1990), and `ker expP = Λ_C`. Lean proves V(Q) ≅ ℂ²/ker expP (surjectivity
  included), and V(Q) is a closed subset of ℙ⁸ cut out by explicit quadrics (`onQ_quad`, `onQ_closed`). That V(Q) is
  the Jacobian and not some other model is Grant's theorem. Surjectivity onto V(Q) is all of V(Q); it says nothing
  about whether V(Q) is Jac(C).

## 6. Degenerate witnesses: none found

* **`IsAbelianTangentA` is not always satisfiable.** Lean witness `scratch_t0_not_abelian`: for r = 1, the nonzero
  subspace t₀ = {z : z₀ = 0} ⊆ ℂ² is *not* an abelian tangent. The proof goes through `lam_ne_zero_of_abelian` with
  b = 1, with ℚ-independence of 1, ζ, ζ², ζ³ from Mathlib's `linearIndependent_pow` and `natDegree_minpoly_zetaN`.
  ⊥ and ⊤ are abelian (latt spans ℂ² over ℝ), as they must be.
* **`gmLsgA.sub` cannot trivialise the conclusion.** A nonzero S ≤ V must be h₀ × U^⊥ × t with h₀ ℚ̄-rational and t
  abelian. A generic hyperplane contains none, by the witness above together with ℚ̄-rationality of h₀.
* **The hypothesis is not trivially true.** It implies lean_mstar's `two_three_beta5` and Wüstholz's
  (1 − ζ₅)B(1/5,1/5)/π ∉ ℚ̄ (§4). Both are genuine transcendence statements.
* **`TorInjA` is not unsatisfiable.** span_ℚ PerA is a finite-dimensional ℚ-space, so a generic hyperplane meets it
  only in 0. lean_mstar proves TorInj for its frame hyperplane V″ (`torInj_ker_phiF`), and the bridge transfers it.
* **ℕ-subtraction.** `HyperplaneKappaOn` casts everything to ℤ, verbatim with lean_mstar. The ℕ-subtractions in
  `SubgroupDataA` and `Theorem41AbVarPer` are exact (§2, §3).
* **Empty-type corners:**
  - r = 0: TanA has an empty A-block, TorInjA is automatic, and the statement is the linear-group case.
  - d₁ = 0: TorInjA says V ∩ ℚ·latt^r = 0.
  - **d₀ = d₁ = 0 (G = A^r alone): the restricted form is empty.** By TorInjA, V ∩ LamA = 0 (Lean:
    `scratch_pureA_empty`). Every y is then 0, and the premise rk > … ≥ 0 fails. Correct, not vacuity of the general
    statement, but the content needs d₀ + d₁ ≥ 1 (m6).
  - In `Theorem41AbVarPer` with d₀ = d₁ = 0, G′ = 0 always satisfies the conclusion, consistent with (4.2) failing.
* **Representation.** `SubgroupDataA` has no redundant fields: `tan` determines (h₀, U^⊥, t), and every quantity is a
  function of these.

## Issues

**C1 — scope of the claim (MINOR for the Lean statements; the current lean_mstar paper sentence over-claims).**
* The proved statement is W88 §5d for G_a^{d₀} × G_m^{d₁} × A^r with two restrictions: V toric-injective, **and** the
  A-components of the y_i periods (by scaling, torsion). So Γ ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × A^r_tors.
* lean_mstar `paper/paper.tex` l. 4294–4295 says "from lean_lsg's hyperplane statement for G_a^{d₀}×G_m^{d₁}×A^r, A
  the Jacobian of y⁵ = x(1 − x), on toric-injective hyperplanes". It omits the second restriction.
* lean_lsg's README and paper do not yet mention the AbVar statement.
* **Fix:** say "W88 §5d for G_a^{d₀} × G_m^{d₁} × A^r, A = Jac(y⁵ = x(1 − x)), for toric-injective hyperplanes V and
  subgroups Y whose A-components are (rational) periods". Optionally add "this is all lean_mstar's models `gmA` and
  `gmAK ∅` use".

**m1 — MINOR: `Theorem41AbVarPer` is stated but never proved.**
* Its docstring and the module header present it as one of "the statements" with no status. ABVAR §2.3 calls it "the
  first lean_lsg target". The route actually taken is `Theorem41B` (blocks) → §5d.
* **Fix:** either derive `theorem41AbVarPer : Theorem41AbVarPer` from `theorem41B_of multEstB_holds (aBlockAnF r) …`
  through the `TanA ↔ MEB.Tan` identification already used in `AbVar5dA.lean`, or mark it "not proved; superseded by
  `Theorem41B`" in the docstring.

**m2 — MINOR: the docstrings overstate `latt` and `PerA`.**
* `StatementAbVar.lean` l. 13 says "Its period lattice is Λ = latt". l. 22 says "`PerA` (periods,
  Ω(G) = ker exp_G)".
* What is proved is `latt ≤ kerE ⊆ ℚ·latt` (finite index). Every use is index-insensitive (§1).
* **Fix:** "`latt` is a finite-index sublattice of `ker E` (`lattice_le_ker`, `isNsmulIn_latt_kerE`); `PerA` is a
  finite-index subgroup of Ω(G), with the same ℚ-span".

**m3 — MINOR: lean_lsg's own `HyperplaneKappaOn` is not lean_mstar's.**
* `good V` comes after `G.Rational W`; lean_mstar puts it first. The two are equivalent (Lean-checked) but not
  definitionally equal. The docstring says "(`lean_mstar`'s `HyperplaneKappaOn`)".
* `LSG.W88.HyperplaneKappaOn` and `LSG.W88.MStarCopy.HyperplaneKappaOn` have the same short name. Opening `MStarCopy`
  inside `namespace LSG.W88` makes it ambiguous.
* **Fix:** reorder the binder to match (then `hkOn_transport` simplifies), or rename it (`HyperplaneKappaOnL`) and say
  "equivalent up to premise order".

**m4 — MINOR: the docstring of `HyperplaneKappaAbVar`** ("The W88 §5d hypothesis for G_a^{d₀} × G_m^{d₁} × A^r
(toric-injective hyperplanes)") omits the restriction `lam = LamA` (period A-parts). The module header has it.
* **Fix:** add "with `lam = LamA` (A-parts in Λ; `span_ℚ LamA` by `hyperplaneKappaOn_spanLam`)".

**m5 — MINOR: stale documentation.**
* `README.md` l. 196–197 ("Not covered: the CM abelian-variety models") and `TRUST.md` §6 (row "CM abelian-variety
  models (`AbVar.*`) | — | not covered") are out of date: `thm11KappaA5` and `thm11KappaAK5` are proved and in
  `Axioms.lean`.
* The README review list and "Status" bullet do not mention this review. TRUST §9 should list the identifications
  (I1)–(I3) of §5.
* **Fix:** add the two rows ("`AbVar.Thm11KappaA 5 2 (·+1) perA5 0`, `AbVar.Thm11KappaAK … ∅` |
  `LSG.W88.thm11KappaA5`, `thm11KappaAK5` | unconditional"). The other AbVar hypotheses (`An`, `AnK`, `X7`, `XA`,
  `A 7 …`) stay "not covered".

**m6 — MINOR (observation): the proved form is empty for G = A^r alone.**
* With d₀ = d₁ = 0, TorInjA forces V ∩ LamA = 0 (`scratch_pureA_empty`), so the premise of (5.4) never holds.
  Similarly, the d₁ = 0 case says nothing about non-torsion points.
* This is the intended scope (lean_mstar's frames have d₁ = 2n ≥ 2). It should not be cited as "W88 for A^r".
* **Fix:** one sentence in the module docstring.

**m7 — MINOR: the wording of "A is the Jacobian".**
* Docstrings say "A = Jac(y² = 4x⁵ + 1)" and "for Jac(y⁵ = x(1 − x))". The statements are about the complex torus
  ℂ²/latt with the standard ℚ̄-structure. The identification is (I1)–(I3) of §5.
* **Fix (paper):** "Here A is the Jacobian of C: y⁵ = x(1 − x), presented in Lean by its period lattice in the
  coordinates ∫dX/Y, ∫X dX/Y on the model Y² = 4X⁵ + 1. Lean computes these periods (Beta values) and proves that they
  are periods of an analytic exponential map onto Grant's model in ℙ⁸ with discrete kernel. The identification of that
  torus with Jac(C), and of complex subtori with abelian subvarieties, is classical and not formalised. The final
  theorems (e.g. `two_three_beta5_uncond`) are statements about explicit numbers and do not depend on it."

## Appendix: scratch file (`lean_mstar/ScratchReviewAbVarE2E.lean`, deleted; copy in the session scratchpad)

```lean
import CM4E.AbVar.ThmA
import CM4E.AbVar.MGAK
import CM4E.AbVar.CorA2
import LSG.W88.AbVarFinal

theorem scratch_thmA5 : CM4E.AbVar.Thm11KappaA 5 2 (fun s => (s:ℕ)+1) CM4E.AbVar.perA5 0 :=
  fun r b hb => LSG.W88.thm11KappaA5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

theorem scratch_thmAK5 : CM4E.AbVar.Thm11KappaAK 5 2 (fun s => (s:ℕ)+1) CM4E.AbVar.perA5 0 ∅ :=
  fun r b hb => LSG.W88.thm11KappaAK5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

theorem scratch_two_three :
    ¬ (IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1 / 5) (1 / 5) / Real.pi * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1 / 5) (1 / 5) / Real.pi * Complex.log 3))) :=
  CM4E.AbVar.two_three_beta5 scratch_thmA5

#print axioms scratch_thmA5
#print axioms scratch_thmAK5
#print axioms scratch_two_three
#print axioms LSG.W88.hyperplaneKappaAbVar

theorem scratch_wuestholz : CM4E.AbVar.WuestholzA5 := CM4E.AbVar.wuestholzA5_of scratch_thmA5
#print axioms scratch_wuestholz

-- lean_lsg's own HyperplaneKappaOn vs lean_mstar's: same up to premise order
example {Vt : Type} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt] (G : CM4E.Waldschmidt.GroupModel Vt)
    (good : Submodule ℂ Vt → Prop) :
    CM4E.Waldschmidt.HyperplaneKappaOn G good ↔
      LSG.W88.HyperplaneKappaOn (Vt := Vt) ⟨G.d₁, G.d₂, G.alg, G.lam, G.per, G.sub⟩ good :=
  ⟨fun h V W m y h1 h2 h3 hg h4 h5 => h V W m y hg h1 h2 h3 h4 h5,
   fun h V W m y hg h1 h2 h3 h4 h5 => h V W m y h1 h2 h3 hg h4 h5⟩

-- non-vacuity of `IsAbelianTangentA`: the nonzero subspace {z₀ = 0} of ℂ² (r = 1) is NOT an abelian tangent
theorem scratch_indep : LinearIndependent ℚ
    (fun p : Fin 1 × Fin 4 => LSG.JacAn.Beta.zetaN 5 ^ (p.2 : ℕ) * (fun _ => (1:ℂ)) p.1) := by
  have h := linearIndependent_pow (K := ℚ) (CM4E.AbVar.zetaN 5)
  have hd : (minpoly ℚ (CM4E.AbVar.zetaN 5)).natDegree = 4 := by
    rw [CM4E.AbVar.natDegree_minpoly_zetaN 5 (by norm_num)]; decide
  let e : Fin 1 × Fin 4 ≃ Fin (minpoly ℚ (CM4E.AbVar.zetaN 5)).natDegree :=
    (Equiv.prodCongr (Equiv.refl _) (finCongr hd.symm)).trans (Equiv.uniqueProd _ _)
  have := h.comp e e.injective
  convert this using 1
  funext p
  show LSG.JacAn.Beta.zetaN 5 ^ (p.2 : ℕ) * 1 = CM4E.AbVar.zetaN 5 ^ ((e p : Fin _) : ℕ)
  rw [mul_one]
  rfl

def t0 : Submodule ℂ (Fin 1 → Fin 2 → ℂ) where
  carrier := {z | z 0 0 = 0}
  add_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq, Pi.add_apply] at *; rw [ha, hb, add_zero]
  zero_mem' := rfl
  smul_mem' c a ha := by simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *; rw [ha, mul_zero]

theorem scratch_t0_ne : t0 ≠ ⊥ := by
  intro h
  have hm : (fun _ : Fin 1 => fun k : Fin 2 => if k = 0 then (0:ℂ) else 1) ∈ t0 := by
    show (if (0 : Fin 2) = 0 then (0:ℂ) else 1) = 0; simp
  rw [h] at hm
  have := congrFun (congrFun ((Submodule.mem_bot ℂ).mp hm) 0) 1
  simp at this

theorem scratch_t0_not_abelian : ¬ LSG.W88.IsAbelianTangentA t0 := by
  intro ht
  obtain ⟨z, hz, hne⟩ := LSG.W88.lam_ne_zero_of_abelian (r := 1) (t := t0) (b := fun _ => (1:ℂ)) ht
    scratch_t0_ne scratch_indep
  apply hne
  have : z 0 0 = 0 := hz
  simp [this]
#print axioms scratch_t0_not_abelian

-- observation: for G = A^r alone (d₀ = d₁ = 0) the TorInj + period-A-part form has no nonzero `y`
theorem scratch_pureA_empty {r : ℕ} (V : Submodule ℂ (LSG.W88.TanA 0 0 r)) (hV : LSG.W88.TorInjA V)
    (y : LSG.W88.TanA 0 0 r) (hyV : y ∈ V)
    (hyL : y ∈ (LSG.W88.LamA : AddSubgroup (LSG.W88.TanA 0 0 r))) : y = 0 :=
  hV y hyV (Submodule.subset_span ⟨Subsingleton.elim _ _, fun i => i.elim0, hyL.2.2⟩) (Subsingleton.elim _ _)
#print axioms scratch_pureA_empty
```

The text above has been lightly reformatted: line breaks were added, `scratch_pureA_empty` is written in term mode
here (the compiled file had `by refine …`), and one trivial `TorInjA` example was omitted. The verbatim file is
`AbVarE2E.lean`.
The file compiled in about 20 s with `lake env lean` in lean_mstar's root. It was deleted afterwards. No file in either
repository was edited, apart from writing this report, and no git state was changed.
