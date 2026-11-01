# Referee report: the vector-extension statements (`StatementVec.lean`, `V5d2Stmt.lean`, `V5dOnto.lean`)

Date: 2026-10-31.

**Scope.** Do the **statements** below say what they claim, and are they non-vacuous? The claim is W88 Thm 4.1
(pp. 385–386, with the κ period term), resp. W88 §5d (5.4) (pp. 394–395), for
G = G_a^{d₀} × G_m^{d₁} × G₂, where G₂ is the push-out of (E₁ × ⋯ × E_m)^♮ along an algebraic r × m matrix M.
I did not check the proofs; Lean did. Same format as `REVIEW_STATEMENT.md` (the abelian statement).

* `LSG/W88/StatementVec.lean`: `TanV`, `LamV`, `PerV`, `SubgroupDataV` (with `tan`, `δ0`, `δ1`, `δ`, `δ2`,
  `Proper`), `LiftAlg`, `PerTanRat`, `Concl41`, `Theorem41Vec`, `Theorem41VecLA`, `HyperplaneKappaVec`.
* `LSG/W88/V5d2Stmt.lean`: `Theorem41Vec2`, `HyperplaneKappaVec2`.
* `LSG/W88/V5dOnto.lean`: `Theorem41VecLAOnto`.

**Sources compared:**
* W88 page images in `schanuel/five_exp/ref/w88_pages/`:
  * `w88-01.png`: p. 375, Theorem 1.1 and (1.2) (`m = rk_ℤ Y`, maximal `d₀, d₁`);
  * `w88-06.png`, `w88-07.png`: pp. 385–386, Theorem 4.1 and the definitions of δ, δ₀, δ₁, δ₂, λ, τ ("Here we do
    not assume that d₀ and d₁ are maximal");
  * `w88-08.png`: §4d, π₀, π₁ and the codimensions for non-product G′;
  * `w88-10.png`, `w88-11.png`: §5b–d, Lemma 5.2, Cor. 5.3, (5.4), and the conclusion of Theorem 1.1.
* `VECEXT.md` (design), `STAGE6_MXP.md`, `REVIEW_STATEMENT.md`.
* The bridges `V5dIso.lean`, `V5d2Iso.lean`, `V5dOntoBridges.lean`, `V5dMXGcm.lean`, and the verbatim lean_mstar
  copies `MStarCopy.lean`, `MStarCopyMX.lean`, `MStarCopyMXP.lean`.

## Verdict

**No FATAL or MAJOR issue in any statement.** Every definition matches W88 for this class, and every proved Prop
has a genuine classical consequence, derived in Lean with standard axioms only (§6). The extra premises are either
true for all intended curves (`LiftAlg`, `PerTanRat`) or honest scope restrictions (`r ≤ 1`, `r ≤ 2`, `d₀ = 0`,
`V ∩ fibre`, M onto). The caveats concern scope and documentation. If the paper ever says "W88 Thm 4.1 for vector
extensions" without qualification, that would be an overclaim (issue C1).

| Prop / definition | Verdict | Status in the repo |
|---|---|---|
| `TanV`, the ℚ̄-structure (`AlgVecV`, `RatSubV`, `RatPair`) | CORRECT | — |
| `LamV` (Λ(G)) | CORRECT (depends on a junk value, guarded; m4) | — |
| `PerV` (Ω(G)) | CORRECT | — |
| `SubgroupDataV`, `tan`, `δ0`, `δ1`, `δ`, `δ2`, `Proper` | CORRECT (non-unique representation, harmless; m3) | — |
| `LiftAlg` | CORRECT: a true statement for every curve over ℚ̄ | Lean-proved for CM blocks (`liftAlg_block`) |
| `PerTanRat` | CORRECT: a true statement for every curve over ℚ̄ | Lean-proved for CM blocks (`perTanRat_block`) |
| `Concl41` | CORRECT | — |
| `Theorem41Vec` | CORRECT WITH CAVEATS (C1, C2) | not proved |
| `Theorem41VecLA` | CORRECT WITH CAVEATS (C1, C2) | not proved (superseded by `Onto`) |
| `Theorem41VecLAOnto` | CORRECT WITH CAVEATS (C1, m2) | **proved**: `LSG.W88.theorem41VecLA_onto` |
| `Theorem41Vec2` | CORRECT WITH CAVEATS (C1) | **proved**: `LSG.W88.theorem41Vec2` |
| `HyperplaneKappaVec` | CORRECT WITH CAVEATS (C1) | **proved**: `LSG.W88.V5d.hyperplaneKappaVec_uncond` |
| `HyperplaneKappaVec2` | CORRECT WITH CAVEATS (C1) | **proved**: `LSG.W88.V5d.hyperplaneKappaVec2_uncond` |

## 1. Coordinates, exp, Λ(G), Ω(G), ℚ̄-structure: correct

**The group E^♮ over ℚ̄** [Proved, standard]. Define the group on pairs (P, t), with P ∈ E and t ∈ G_a, by
(P₁, t₁) + (P₂, t₂) = (P₁ + P₂, t₁ + t₂ − f(P₁, P₂)), where f = ½(y₁ − y₂)/(x₁ − x₂) is the cocycle of the ζ
addition theorem.
* This group is defined over ℚ̄, because g₂ and g₃ are algebraic.
* exp(z, w) = ((℘(z), ℘′(z)), w − ζ(z)) is a homomorphism ℂ² → E^♮, since
  ζ(u + v) − ζ(u) − ζ(v) = f(u, v).
* Its kernel is {(λ, η(λ))}, because ζ(z + λ) = ζ(z) + η(λ).
* The extension is non-split (Legendre), so this is the universal vector extension. Ext¹(E, G_a) is
  one-dimensional, so the only freedom is the scaling of w, and any scaling by an algebraic number is ℚ̄-rational.
* The invariant differentials dx/y = dz and dt − x dx/y = dw are defined over ℚ̄. So the standard coordinates
  (z, w) are ℚ̄-rational, and so are the coordinates (a, b, z, s) of `TanV`.

**The push-out** [Proved]. G₂ = ((E^m)^♮ × G_a^r)/{(−u, Mu)}. The map (z, w, s′) ↦ (z, Mw + s′) identifies T(G₂)
with ℂ^m × ℂ^r, ℚ̄-rationally, because M is algebraic (`AlgMat`).

**`LamV` = exp_G⁻¹ G(ℚ̄)** [Proved].
* The torus, G_a and ℘ conditions are as in the abelian review. As there, ℘′ is algebraic by the Weierstrass
  equation.
* The s-condition. For z with no coordinate in a lattice, (z, s) maps to the class of ((P, 0), s − Mζ(z)). Every
  ℚ̄-point of G₂ lifts to (E^m)^♮ × G_a^r, since the kernel G_a^m is connected and we are over ℚ̄. So the class is
  algebraic iff there is u ∈ ℚ̄^m with s − Mζ(z) + Mu ∈ ℚ̄^r, iff s − Mζ(z) ∈ ℚ̄^r.
* Lattice coordinates. If z_j ∈ Λ_j, then exp(z_j, w_j) = exp(0, w_j − η(z_j)). This is the fibre point
  w_j − η(z_j), which is algebraic iff that number is. Lean's `ζ` takes the value η(λ) at λ ∈ Λ (proved,
  `zeta_of_mem_lattice`), so one formula covers both cases, coordinatewise.
* Consistency check: s − Mζ(z) is invariant under adding a period (λ, Mη(λ)). So `LamV + PerV ⊆ LamV`, and the
  signs of `LamV` and `PerV` agree.

**`PerV` = ker exp_G** [Proved]. The class of (exp_♮(z, w′), s − Mw′) is 0 iff
exp_♮(z, w′) = ι(−u) and s − Mw′ = Mu for some u. That forces z ∈ Λ, u = η(z) − w′ and s = Mη(z). Hence
ker exp_G = 0 × 2πiℤ^{d₁} × {(λ, Mη(λ))}, exactly as stated. This holds for every M, onto or not.

**LSG's `ζ` and `η` are the genuine functions.**
* `zeta` is the Weierstrass series. It is the same definition as lean_mstar's `CM4E.Ext.Weierstrass.zeta`, which
  `MStarCopyMX.lean` copies verbatim.
* `eta ω = ζ(ω₁/2 + ω) − ζ(ω₁/2)` is evaluated at a non-lattice point.
* `zeta_add` holds for every z.

## 2. `SubgroupDataV`: exactly the right family of tangent spaces

**Soundness** (every datum is a connected algebraic subgroup over ℚ̄) [Lit/Proved].
* t is the tangent space of an abelian subvariety B ⊂ ∏E_j (as in the abelian review). B is defined over ℚ̄.
* B^♮ ↪ (E^m)^♮ is injective, because H¹(∏E_j, O) → H¹(B, O) is onto.
* T(B^♮) = `perTanId t`:
  * every λ ∈ t ∩ Λ has the unique period lift (λ, η(λ)), and that lift lies in T(B^♮);
  * the dimensions agree. Lean proves dim `perTanId t` = 2 dim t, via `perTanId_bij` in `V5dPer.lean`.
* So `tan` = Γ + U^⊥ + (id × M)T(B^♮) is the tangent space of T_U × (B̃ + Γ). This subgroup is connected,
  algebraic and defined over ℚ̄, because Γ is ℚ̄-rational (`gam_rat`).

**Completeness** (every connected algebraic subgroup is representable) [Proved, standard].
* Split off the torus by Goursat. Here Hom(G_m, ·) and Hom(·, G_m) vanish against extensions of abelian varieties
  by vector groups.
* For K ⊂ G_a^{d₀} × G₂, let B be the image of K in ∏E_j, and Γ := K ∩ (G_a^{d₀} × fibre). Γ is connected,
  because vector groups have no finite subgroups.
* Then π⁻¹(B) is the push-out of B^♮ along some ψ, and ψ(H¹(B,O)^∨) ⊂ Γ. A sub-extension of π⁻¹(B)/Γ → B is a
  splitting, and splittings form a torsor under Hom(B, vector group) = 0. So K = B̃ + Γ.
* This agrees with VECEXT §1.2.

**Non-uniqueness (harmless).**
* A datum whose `gam` does not contain the fibre part ψ(H) of B̃ still describes the genuine subgroup B̃ + Γ, whose
  vector part is Γ + ψ(H) ⊋ Γ.
* Every quantity in `Concl41` depends only on `tan`:
  * `δ` = d − dim tan;
  * `δ0` uses fst(gam) = fst(tan), since `torIncl` and `g2Incl` have first component 0;
  * `δ1` = dim U = d₁ − dim pr₁(tan);
  * `τ` and `λ` are computed from `tan`.
* So no representation trick can produce a degenerate witness. The docstring "the vector part" slightly misdescribes
  `gam` (m3).

**The codimensions match W88 pp. 385–386 and 388–389.**
* δ₀ = dim G_a^{d₀}/π₀(G′), and T(π₀G′) = fst(tan).
* δ₁ = dim G_m^{d₁}/π₁(G′), with pr₁(tan) = U^⊥.
* δ = codim, and δ₂ = δ − δ₀ − δ₁.
* δ ≥ δ₀ + δ₁ holds because tan ⊂ fst(gam) × U^⊥ × ℂ^{m+r}. So the ℕ-subtraction in `δ2` is exact.
* `Proper` ⇔ tan = ⊤ fails ⇔ G′ ≠ G.

## 3. λ, τ, κ, the inequality, d₂ = m + r: correct

* **κ** = `rk (Y ⊓ PerV)` = rk_ℤ(Y ∩ Ker exp_G), as on p. 385.
* **λ** = `rk Y − rk (Y ⊓ (tan + PerV))`. This is rk Γ/(Γ ∩ G′), because exp⁻¹(G′) = T_{G′} + Ω(G) for connected
  G′.
* **τ** = dim W − dim(W ∩ T_{G′}).
* **The inequality** (λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ) holds with d = d₀ + d₁ + m + r and
  d₂ = dim G₂ = m + r. This is verbatim p. 386.
* **Non-maximal d₀.** A non-onto M puts G_a factors into G₂ (weight 2), so d₀ is not maximal. W88 Thm 4.1
  explicitly allows this.
* **(5.4) in `HyperplaneKappaVec(2)`** reads rk Y > (d₁ + 2(m + r) − κ)(d − 1 − dim W). This is p. 394, with
  m := rk_ℤ Y as in (1.2).
  * The printed "κ = ℓ − m" on p. 394 is a typo for ℓ = m − κ (ℓ = rk Γ, p. 389). (5.5) follows from (5.4) only
    with ℓ = m − κ. The Lean form uses rk Y, which is the correct reading.
  * For non-maximal d₀, the Lean d₂ is larger than W88's maximal d₂. That makes the hypothesis stronger and the
    statement weaker, which is the safe direction.
* **The conclusion of §5d**, "V contains a non-zero algebraic Lie sub-algebra defined over ℚ̄" (p. 376), is
  `∃ H, H.tan ≠ ⊥ ∧ H.tan ≤ V`. Correct.

## 4. Casts and natural-number subtraction: all safe

The scratch file `VecCasts.lean` ran `#print` with `pp.coercions` and `pp.numericTypes`. The elaborated `Concl41`
is:

```
↑(rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV Ls M)) + H.δ1 + 2 * H.δ2) * (↑(d0 + d1 + m + r) - ↑(finrank ℂ ↥V)) ≤
  (↑H.δ - ↑(finrank ℂ ↥W - finrank ℂ ↥(W ⊓ H.tan))) * (↑(d1 + 2 * (m + r)) - ↑(rk (Y ⊓ PerV Ls M)))
```

* **The ℤ-subtractions** are d − N, δ − τ and d₁ + 2(m + r) − κ. None of them can truncate:
  * N < d is a hypothesis;
  * τ < δ is a conjunct;
  * κ ≤ rk Ω = d₁ + 2m.
* **The ℕ-subtractions** are `rk Y − rk(…)`, `finrank W − finrank(W ⊓ tan)`, `d0 − finrank(fst gam)`,
  `(d0+d1+m+r) − finrank tan` and `δ − δ0 − δ1`. Each is exact: span is monotone, Y is finitely generated, and the
  bound δ ≥ δ₀ + δ₁ is in §2.
* **In `HyperplaneKappaVec(2)`** every term is cast to ℤ before any subtraction. The elaborated form is
  `↑d1 + 2 * (↑m + ↑r) − ↑κ` and `↑d0 + ↑d1 + ↑m + ↑r − 1 − ↑(finrank W)`.

## 5. The extra premises

**True for every curve with algebraic g₂, g₃ (they make nothing vacuous):**
* **`LiftAlg`** [Proved, standard].
  * Take z ∈ t with exp(z) ∈ B(ℚ̄). B^♮ → B is a surjective morphism over ℚ̄, so exp(z) lifts to P̃ ∈ B^♮(ℚ̄).
  * A logarithm (z′, w′) ∈ T(B^♮) of P̃ has z′ − z ∈ t ∩ Λ. Subtract the generator (z′ − z, η(z′ − z)) of
    `perTanId t`. The result is (z, w) ∈ `perTanId t` with exp algebraic, so w − ζ(z) ∈ ℚ̄^m by §1.
  * Lean proves it only for CM blocks with κ₁ = 0 (`LSG.CM.liftAlg_block`, `liftAlg_append`).
* **`PerTanRat`** [Proved, standard]. B^♮ is defined over ℚ̄, so its Lie algebra `perTanId t` is ℚ̄-rational in the
  ℚ̄-coordinates (z, w). Lean proves it only for CM blocks (`perTanRat_block`).

**Genuine scope restrictions.** These are not true-for-free; they are conditions on G or V:
* `r ≤ 1` with `V ⊓ fibreV = ⊥` (`Theorem41VecLA`);
* additionally `Surjective M.mulVec` (`Theorem41VecLAOnto`);
* `d₀ = 0`, `r ≤ 2` and `dim(V ∩ fibre) ≤ 1` (`Theorem41Vec2`);
* `r ≤ 1` (`HyperplaneKappaVec`), and `d₀ = 0`, `r ≤ 2` (`HyperplaneKappaVec2`).

Each is satisfiable together with all the other hypotheses (§6). (NR) is the same documented weakening as in the
abelian statement (`REVIEW_STATEMENT.md` M2).

## 6. Not vacuous, not trivially satisfiable

**Degenerate witnesses tried, none works:**
* G′ = G is excluded by `Proper`.
* G′ = 0 works only when (4.2) fails.
* Representation tricks change nothing, since every quantity depends only on `tan` (§2).
* Empty-type corners are handled correctly:
  * d₀ = d₁ = 0 (`Fin 0`): subsingleton blocks, and δ₀ = δ₁ = 0 as expected;
  * r = 0: the statement reduces to `Theorem41Abelian`, because `perTan t` projects onto t when t ∩ Λ spans t
    over ℝ;
  * m = 0, r ≥ 1: G₂ = G_a^r with `PerV`-fibre = 0, which is correct;
  * d = 0: excluded by N < d.

**Sanity derivations** (Lean, compiled against the built library, standard axioms only). The scratch file is
`VecSanity.lean`;
its full text is in the Appendix.

```
'ScratchVec.eta_ne_alg_mul_lem' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScratchVec.eta_ne_alg_mul_lem2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScratchVec.eta_ne_alg_mul_5d' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* **Claim.** For the lemniscatic curve (given g₂, g₃ ∈ ℚ̄), η(ω₁) ∉ ℚ̄·ω₁. Equivalently π/ϖ² ∉ ℚ̄; this is a case
  of Masser's ℚ̄-linear independence of ω and η [Lit]. It is derived three times:
  * from `theorem41VecLA_onto` (`Theorem41VecLAOnto`);
  * from `theorem41Vec2` (`Theorem41Vec2`);
  * from `hyperplaneKappaVec_uncond` (`HyperplaneKappaVec`).
* **Instance.** G = E^♮, so d₀ = d₁ = 0, m = r = 1 and M = 1. Take V = W = ℂ(1, β) and Y = ℤ(ω₁, η(ω₁)) ⊂ Ω.
  Then κ = 1, (NR) reads 1 ≤ 2, V ∩ fibre = 0, and (5.4) reads 1 > 3·0.
* **Case analysis.**
  1. λ = 0 and δ₂ = δ ≤ 2, so the inequality reads 2δ ≤ 3(δ − τ). This forces τ = 0 and δ ≥ 1, hence
     T_{G′} = V.
  2. If t = 0, then T_{G′} ⊂ fibre, which contradicts V ∩ fibre = 0.
  3. If t = ⊤, then (ω₂, η(ω₂)) ∈ T_{G′} = V, so η₂ = βω₂. Then η₁ω₂ − η₂ω₁ = 0, which contradicts
     `legendre_ne_zero`.
* **What it exercises:** `PerV` with M, `perTanId`/`perTan`, `fibreV`, the 2δ₂ weight, `SubgroupDataV` for a
  non-split group, `LiftAlg`/`PerTanRat` (CM instances), and every cast.
* **Not exercised:** the non-lattice ζ-branch of `LamV`. It is checked on paper in §1. A Lean check is suggested as
  m6.

## 7. Bridges and lean_mstar's models

* **The interface** (`hyperplaneKappa_of_iso`, `…_iso2`) uses `LamV`, `PerV` and `SubgroupDataV` in the safe
  directions:
  * model `lam` ⊂ `LamV` up to multiples;
  * model `per` ⊂ span_ℚ `PerV`, so κ_model ≤ κ, which only strengthens (5.4);
  * `G.alg` ⇒ `AlgVecV ∘ ι⁻¹`;
  * d₂ = m + r;
  * every nonzero `tan` lies in `G.sub`.
  These are exactly the hypotheses that make lean_mstar's `HyperplaneKappa G` a consequence. They are
  Lean-checked, and nothing in them requires `LamV` or `PerV` to be smaller than the truth.
* **lean_mstar's conventions agree with LSG's.** In `LogNat`, w − ζ(z) has periods (λ, η(λ)). I checked, on paper
  via Legendre, that `etaLem m n = (m − ni)π/ϖ` and `etaR m n = (m + nρ̄)·2π/(√3Ω_ρ)` are η(mω₁ + nω₂) for the
  orientations used (Im(ω₂/ω₁) > 0).
* **The models' d₂ is right, with maximal d₀:**
  * `gmXG`: d₂ = 2·card + 1 with M = (θᵀ, θᵀ), which is onto, so d₀ = 1 is maximal;
  * `gmXP`: d₂ = 2·card + 2 with M = [[0, θᵀ], [θᵀ, 0]] of rank 2, so d₀ = 0 is maximal.
* **Observation for lean_mstar (no issue).** The `sub` families of `gmXG` and `gmXP` contain only ⊥ and subspaces
  with an algebraic vector outside ker Ψ″. So the "soundness" sentence in `GroupModel`'s docstring is a real
  mathematical claim (Lemma K).
  * The bridges now prove it for every nonzero `SubgroupDataV` (`hsub`). Together with the completeness in §2, this
    discharges that trust item.
  * Since `HyperplaneKappa (gmXG b)` etc. are now theorems (`V5dOntoBridges`, `V5dMXPMain`), lean_mstar no longer
    needs to trust model soundness for those hypotheses, only its own final statements. I noticed nothing wrong in
    the models.

## Issues

**C1 — scope of the claim (statements fine; MAJOR only if the claim is worded loosely).**
* The proved results are:
  * Thm 4.1 under (NR) + `LiftAlg`, for (r ≤ 1, M onto, V ∩ fibre = 0) [`Onto`];
  * Thm 4.1 under (NR) + `LiftAlg` + `PerTanRat`, for (d₀ = 0, r ≤ 2, dim V ∩ fibre ≤ 1) [`Vec2`];
  * §5d, without (NR), for r ≤ 1 [`HyperplaneKappaVec`] and for d₀ = 0, r ≤ 2 [`…Vec2`].
* The general `Theorem41Vec`, and `Theorem41VecLA` for non-onto M with d₀ ≥ 1, are **not** proved.
* **Fix:** the paper should say "W88 Thm 4.1 under (NR) for G_a^{d₀} × G_m^{d₁} × G₂, G₂ a push-out of
  (∏E_j)^♮ along an algebraic M, in the cases r ≤ 1 with M onto and V ∩ fibre = 0, or d₀ = 0, r ≤ 2 and
  dim(V ∩ fibre) ≤ 1; for curves satisfying `LiftAlg` (and `PerTanRat`), true for all curves over ℚ̄ and
  Lean-proved for the CM curves used". Never just "W88 Thm 4.1 for vector extensions".

**C2 — MINOR, truth of the unproved targets [Heuristic].**
* `Theorem41Vec` and `Theorem41VecLA` are true if W88 Thm 4.1 holds for this class under (NR), that is, if the
  Lemma U repair of W88 Prop. 6.1 extends to G₂ with a vector part.
* Lean confirms this only in the proved cases. For non-onto M with d₀ ≥ 1 the extra G_a is weighted 2 inside G₂
  rather than 0 in d₀. W88 allows this, but the (NR) repair has not been checked there. `V5dOntoMain` handles that
  presentation only for codim V′ = 1, via `concl41_sw`.
* **Fix:** label `Theorem41Vec`/`Theorem41VecLA` as "[Lit], conditional on W88 Prop. 6.1 for the class", or drop
  `Theorem41VecLA` now that `Onto` and `Vec2` supersede it.

**m1 — MINOR, stale documentation.**
* The `StatementVec.lean` header says `Theorem41VecLA` "is the first proof target; it suffices for every lean_mstar
  bridge". In fact `Thm11KappaMXP` needs `Theorem41Vec2` (r = 2), and the proof targets that were actually reached
  are `Onto` and `Vec2`.
* `TRUST.md` (§"Vector extensions are not yet proved", and the table "conditional on `Theorem41VecLA`"), the README
  status table, and `paper.tex` §"Vector extensions: status" ("Vector extensions are not proved") are out of date:
  `theorem41VecLA_onto`, `theorem41Vec2`, `hyperplaneKappaVec_uncond`, `hyperplaneKappaVec2_uncond` and the
  `…_uncond` bridges exist.
* **Fix:** update these to list the proved Props with their premises, as in C1.

**m2 — MINOR, `Theorem41VecLAOnto` at r = 0.**
* The docstring says the Prop "includes r = 0, the abelian groups". It still requires `LiftAlg Ls`, so for non-CM
  curves it does **not** subsume `Theorem41Abelian` (which needs no such premise).
* **Fix:** add "(under `LiftAlg`)" to the docstring.

**m3 — MINOR, `SubgroupDataV.gam` docstring.**
* "The vector part, inside G_a^{d₀} × (fibre of G₂)" is accurate only when gam ⊇ fib(B̃). In general the vector
  part of G′ is gam + ψ(H¹(B,O)^∨).
* Harmless, since all quantities depend on `tan` only (§2).
* **Fix:** add one sentence: the representation is not unique, and only `tan` matters.

**m4 — MINOR, junk-value dependence in `LamV`.**
* The lattice case of `LamV` is correct only because Lean's `ζ` takes the junk value η(λ) at λ ∈ Λ. This comes from
  `1/0 = 0` in the l = 0 summand, so `ζ(0) = 0`.
* It is proved in-file (`zeta_of_mem_lattice`), so a change in the definition of `zeta` would break the build
  rather than silently change `LamV`. Unlike the abelian statement (`REVIEW_STATEMENT.md` M4), the meaning here does
  depend on the junk value.
* **Fix (optional):** keep the lemma next to `LamV` (it is), or state the s-condition with an explicit case split
  (`η` on lattice coordinates).

**m5 — MINOR (as abelian M3/M4).**
* `Proper` is implied by `τ < δ`.
* In `LamV`, the disjunct `z_j ∈ Λ_j` is redundant, because Mathlib's `℘(λ) = 0`.

**m6 — MINOR, suggestion for an additional check.**
* No Lean derivation yet exercises the non-lattice ζ-branch of `LamV`. A candidate check: for G = G_a × E^♮
  (d₀ = 1, m = r = 1, M = 1), take a hyperplane V = {s = αa + βz} with α, β ∈ ℚ̄, and W = V, Y = ℤ(1, u, ζ(u)),
  where u ∉ Λ and ℘(u) ∈ ℚ̄.
* On paper, `Theorem41VecLAOnto` then gives ζ(u) ∉ ℚ̄ + ℚ̄u. Every admissible G′ fails: the line ℂ(1, 0, α) gives
  5 ≤ 4, and G′ = 0 gives 5 ≤ 4. This is a case of Masser's linear independence of 1, u, ζ(u).
* About 150 lines on top of `VecSanity.lean`.

## Appendix: `VecSanity.lean` (sanity derivations)

```lean
import LSG.W88.V5dOnto
import LSG.W88.V5dPer
import LSG.W88.V5dFrame2
import LSG.CM.Inst
import LSG.CM.Block
import LSG.W88.V5dOntoMain
import LSG.W88.V5dMXPMain

open Module Complex LSG.W88 LSG.W88.Vec

namespace ScratchVec

abbrev T := TanV 0 0 1 1

noncomputable def u0 (β : ℂ) : T := (0, 0, ![1], ![β])

theorem u0_ne (β : ℂ) : u0 β ≠ 0 := by
  intro h
  have := congrArg (fun p : T => p.2.2.1 0) h
  simp [u0] at this

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

/-- Periods are logarithms of algebraic points (here `d₀ = d₁ = 0`). -/
theorem perV_le_lamV {m r : ℕ} (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    {p : TanV 0 0 m r} (hp : p ∈ PerV Ls M) : p ∈ LamV Ls M := by
  obtain ⟨-, -, hlat, hs⟩ := hp
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun j => Or.inl (hlat j), ?_⟩
  have hz : zetaV Ls p.2.2.1 = etaV Ls p.2.2.1 := by
    funext j; exact zeta_of_mem_lattice (Ls j) (hlat j)
  rw [hz, ← hs, sub_self]
  intro i; simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0 : ℂ))

noncomputable def Ls1 (L : PeriodPair) : Fin 1 → PeriodPair := fun _ => L
noncomputable def M1 : Matrix (Fin 1) (Fin 1) ℂ := 1
noncomputable def V1 (β : ℂ) : Submodule ℂ T := ℂ ∙ u0 β

theorem V1_dim (β : ℂ) : finrank ℂ (V1 β) = 1 := finrank_span_singleton (u0_ne β)

theorem V1_fib (β : ℂ) : V1 β ⊓ fibreV = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvF⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
  have := (LSG.W88.V5d.mem_fibreV_iff.mp hvF).2.2
  have hc : c = 0 := by simpa [u0] using congrFun this 0
  simp [hc]

theorem tan_ne (L : PeriodPair) (β : ℂ) (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (Ls1 L) M1) (hVeq : V1 β = H.tan) : False := by
  classical
  have hVdim := V1_dim β
  by_cases ht : H.t = ⊥
  · -- `T_{G'}` lies in the fibre
    have hle : H.tan ≤ fibreV := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨p, -, rfl⟩
        exact LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, rfl⟩
      · rintro _ ⟨p, -, rfl⟩
        exact LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, rfl⟩
      · rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, rfl⟩ := hp
        have h1 := LSG.W88.V5d.fst_mem_of_mem_perTanId (Ls1 L) hq
        rw [ht] at h1
        refine LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
        exact (Submodule.mem_bot ℂ).mp h1
    have h2 : V1 β ⊓ fibreV = V1 β := inf_eq_left.mpr (hVeq ▸ hle)
    rw [V1_fib] at h2
    have := congrArg (fun S : Submodule ℂ T => finrank ℂ S) h2
    simp [hVdim] at this
  · -- `t = ⊤`: the second period lies in `V`, contradicting Legendre
    have htop : H.t = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : 0 < finrank ℂ H.t := Nat.pos_of_ne_zero fun h0 =>
        ht (Submodule.finrank_eq_zero.mp h0)
      have h2 := Submodule.finrank_le H.t
      simp at h2 ⊢; omega
    let q : (Fin 1 → ℂ) × (Fin 1 → ℂ) := (![L.ω₂], etaV (Ls1 L) ![L.ω₂])
    have hq : q ∈ perTanId (Ls1 L) H.t := Submodule.subset_span
      ⟨by rw [htop]; trivial, fun j => by simpa [q, Ls1] using L.ω₂_mem_lattice, rfl⟩
    have hmem : g2Incl ((LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M1)) q) ∈ H.tan :=
      Submodule.mem_sup_right ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [← hVeq] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have e1 := congrArg (fun p : T => p.2.2.1 0) hc
    have e2 := congrArg (fun p : T => p.2.2.2 0) hc
    simp [u0, q, M1, etaV, Ls1] at e1 e2
    have hleg := LSG.Weierstrass.legendre_ne_zero L
    apply hleg
    rw [hη, ← e2, ← e1]; ring

/-- Analysis of the subgroup produced by the theorem. -/
theorem H_false (L : PeriodPair) (β : ℂ) (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁)
    (Y : AddSubgroup T) (hrkY : rk Y = 1) (hYP : Y ≤ PerV (Ls1 L) M1)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (Ls1 L) M1) (hprop : H.Proper)
    (hτ : finrank ℂ (V1 β) - finrank ℂ ↥(V1 β ⊓ H.tan) < H.δ)
    (hineq : (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV (Ls1 L) M1)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
        ((0 + 0 + 1 + 1 : ℕ) - finrank ℂ (V1 β) : ℤ) ≤
      ((H.δ : ℤ) - (finrank ℂ (V1 β) - finrank ℂ ↥(V1 β ⊓ H.tan) : ℕ)) *
        ((0 + 2 * (1 + 1) : ℕ) - rk (Y ⊓ PerV (Ls1 L) M1) : ℤ))) : False := by
  classical
  have hVdim := V1_dim β
  have hYPer : Y ⊓ PerV (Ls1 L) M1 = Y := inf_eq_left.mpr hYP
  have hδ0 : H.δ0 = 0 := by simp [SubgroupDataV.δ0]
  have hδ1 : H.δ1 = 0 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupDataV.δ1] using this
  have hδ2 : H.δ2 = H.δ := by simp [SubgroupDataV.δ2, hδ0, hδ1]
  have hδdef : H.δ = 2 - finrank ℂ H.tan := rfl
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV (Ls1 L) M1)) = 1 := by
    rw [inf_eq_left.mpr (hYP.trans le_sup_right), hrkY]
  rw [hrkY, hlam, hδ1, hδ2, hYPer, hrkY, hVdim] at hineq
  have hb1 : finrank ℂ ↥(V1 β ⊓ H.tan) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : V1 β ⊓ H.tan ≤ V1 β); omega
  rw [hVdim] at hτ
  have hb : finrank ℂ ↥(V1 β ⊓ H.tan) = 1 := by push_cast at hineq; omega
  have hδpos : 1 ≤ H.δ := by omega
  have hVt : V1 β ≤ H.tan := by
    have h1 : finrank ℂ (V1 β) ≤ finrank ℂ ↥(V1 β ⊓ H.tan) := by omega
    have := Submodule.eq_of_le_of_finrank_le (inf_le_left : V1 β ⊓ H.tan ≤ V1 β) h1
    rw [← this]; exact inf_le_right
  have htan_le : finrank ℂ H.tan ≤ 1 := by omega
  have hVeq : V1 β = H.tan := Submodule.eq_of_le_of_finrank_le hVt (htan_le.trans hVdim.ge)
  exact tan_ne L β hη H hVeq

/-- **Sanity derivation from the proved `Theorem41VecLAOnto`** (`G = E^♮`, `d₀ = d₁ = 0`, `m = r = 1`,
`M = 1`, `V = W = ℂ(1, β)`, `Y = ℤ(ω₁, η(ω₁))`, `κ = 1`): `η(ω₁)` is not an algebraic multiple of `ω₁`. -/
theorem eta_ne_alg_mul (hT : Theorem41VecLAOnto) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (hLA : LiftAlg (Ls1 L))
    (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁) : False := by
  classical
  have hω0 : L.ω₁ ≠ 0 := by
    intro h; have := L.indep.ne_zero 0; simp [h] at this
  have hy0 : (L.ω₁ : ℂ) • u0 β ≠ 0 := smul_ne_zero hω0 (u0_ne β)
  have hyV : (L.ω₁ : ℂ) • u0 β ∈ V1 β := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hyP : (L.ω₁ : ℂ) • u0 β ∈ PerV (Ls1 L) M1 := by
    refine ⟨Subsingleton.elim _ _, fun i => i.elim0, fun j => ?_, ?_⟩
    · simpa [u0, Ls1] using L.ω₁_mem_lattice
    · funext i
      fin_cases i
      simp [u0, M1, etaV, Ls1, hη, mul_comm]
  have hYP : AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β) ≤ PerV (Ls1 L) M1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    exact zsmul_mem hyP k
  have hrkY := rk_zmultiples hy0
  have hrat : RatSubV (V1 β) := by
    apply le_antisymm
    · rw [V1, Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, fun i => i.elim0,
        fun i => i.elim0, ?_, ?_⟩
      · intro i; fin_cases i; simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · intro i; fin_cases i; simpa [u0] using hβ
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hM : AlgMat M1 := by
    intro i j; fin_cases i; fin_cases j; simpa [M1] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  have hSurj : Function.Surjective M1.mulVec := fun x => ⟨x, by simp [M1]⟩
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 0 0 1 1 (Ls1 L) M1 (fun _ => ⟨hg₂, hg₃⟩) hM le_rfl hLA hSurj
    (V1 β) (V1 β) (AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β))
    (by rw [V1_dim]; norm_num) le_rfl hrat (V1_fib β)
    ((AddSubgroup.fg_iff _).mpr ⟨{(L.ω₁ : ℂ) • u0 β},
      (AddSubgroup.zmultiples_eq_closure _).symm, Set.finite_singleton _⟩)
    (fun z hz => ⟨by
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
        exact zsmul_mem hyV k, perV_le_lamV (Ls1 L) M1 (hYP hz)⟩)
    (by rw [inf_eq_left.mpr hYP, hrkY, V1_dim]; norm_num)
  exact H_false L β hη _ hrkY hYP H hprop hτ hineq

theorem eta_ne_alg_mul_lem (hg₂ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₃) (β : ℂ) (hβ : IsAlgebraic ℚ β) :
    LSG.Weierstrass.eta LSG.W88.MStarCopy.lemniscatic LSG.W88.MStarCopy.lemniscatic.ω₁ ≠
      β * LSG.W88.MStarCopy.lemniscatic.ω₁ :=
  fun h => eta_ne_alg_mul theorem41VecLA_onto _ hg₂ hg₃
    (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem) β hβ h

-- `eta_ne_alg_mul2` is `eta_ne_alg_mul` verbatim with the `hT …` call replaced by
--   `LSG.W88.theorem41Vec2 0 0 1 1 (Ls1 L) M1 (fun _ => ⟨hg₂, hg₃⟩) hM rfl (by norm_num) hLA hPT
--      (V1 β) (V1 β) Y (by rw [V1_dim]; norm_num) le_rfl hrat (by rw [V1_fib]; simp) …`
-- (extra premise `hPT : PerTanRat (Ls1 L)`), and
theorem eta_ne_alg_mul_lem2 (hg₂ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₃) (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta LSG.W88.MStarCopy.lemniscatic LSG.W88.MStarCopy.lemniscatic.ω₁ =
      β * LSG.W88.MStarCopy.lemniscatic.ω₁) : False :=
  eta_ne_alg_mul2 _ hg₂ hg₃ (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem)
    (LSG.CM.perTanRat_block (p := 1) LSG.CM.cmLem) β hβ hη

-- `eta_ne_alg_mul_5d`: same set-up, then
--   obtain ⟨H, hne, hle⟩ := LSG.W88.V5d.hyperplaneKappaVec_uncond 0 0 1 1 (Ls1 L) M1
--     (fun _ => ⟨hg₂, hg₃⟩) hM le_rfl (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem)
--     (LSG.CM.perTanRat_block (p := 1) LSG.CM.cmLem) (V1 β) (V1 β) Y (by rw [V1_dim]) le_rfl hrat
--     hYfg hYVL (by rw [inf_eq_left.mpr hYP, hrkY, V1_dim]; norm_num)
--   have h1 : 1 ≤ finrank ℂ H.tan := Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
--   have hVeq : H.tan = V1 β := Submodule.eq_of_le_of_finrank_le hle ((V1_dim β).le.trans h1)
--   exact tan_ne L β hη H hVeq.symm

end ScratchVec

#print axioms ScratchVec.eta_ne_alg_mul_lem
#print axioms ScratchVec.eta_ne_alg_mul_lem2
#print axioms ScratchVec.eta_ne_alg_mul_5d
```

(The two abbreviated proofs are written out in full in the scratch file named in §6. The whole file compiles in
about 40 s with `lake env lean` against the built library. It was deleted from the repository afterwards.)

## TODO (added 2026-10-31, documentation pass)

The documentation part of m1 is done (README, TRUST, `paper.tex` now list the proved Props with their scope). The
docstring fixes in the Lean files are **deferred**, because another agent is building against `StatementVec.lean`:

* **m1** (`LSG/W88/StatementVec.lean`):
  * module header, l. 45 ("is the first proof target; it suffices for every lean_mstar bridge"): say that
    `Theorem41VecLA` is proved (`LSG.W88.theorem41VecLA`, `MainVec.lean`), as are `Theorem41VecLAOnto` and
    `Theorem41Vec2`, and that `Thm11KappaMXP` needs `Theorem41Vec2` (`r = 2`);
  * docstring of `Theorem41VecLA`, l. 234 ("**The first proof target**"): replace by a pointer to
    `LSG.W88.theorem41VecLA`.
* **m2** (`LSG/W88/V5dOnto.lean`, l. 12, "this includes `r = 0`, the abelian groups"): add "(under `LiftAlg`)"; for
  non-CM curves it does not subsume `Theorem41Abelian`.
* **m3** (`LSG/W88/StatementVec.lean`, l. 174, `SubgroupDataV.gam`, "the vector part, inside
  `G_a^{d₀} × (fibre of G₂)`"): add that the representation is not unique (the vector part of `G′` is
  `gam + ψ(H¹(B, O)^∨)`), and that only `tan` enters the conclusion.

Not docstrings, still open: m4 (optional case split in `LamV`) and m6 (the extra derivation for the non-lattice
`ζ`-branch of `LamV`).

**Erratum to this report (to be confirmed by the reviewer).** The verdict table (row `Theorem41VecLA`: "not proved
(superseded by `Onto`)"), C1 ("`Theorem41VecLA` for non-onto M with d₀ ≥ 1 [is] **not** proved") and C2 are out of
date: `LSG.W88.theorem41VecLA : LSG.W88.Vec.Theorem41VecLA` is proved for every algebraic `M`
(`LSG/W88/MainVec.lean`, commit `4edd2d7`, via `LSG.MEV.multEstVec` with the 4-block grading; in `LSG.lean` and
`Axioms.lean`, standard axioms). So the proved case "r ≤ 1, V ∩ fibre = 0" holds without "M onto", and only the
general `Theorem41Vec` remains unproved. The documentation states the scope in this corrected form.
