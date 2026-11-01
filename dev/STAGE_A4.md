# STAGE A4: the multiplicity estimate for `G_a^{d₀} × G_m^{d₁} × A^r` (design)

Written 2026-10-31. **Design note: no Lean was written, nothing was built, no git state was changed.** Spikes (untrusted
Python, mod p) are in `scripts/a4_spike/` with their outputs (`*.out`).

Sources read: `ABVAR.md` §3, §5 and the A0 results; `STAGE_A4_BEZOUT.md`; `STAGE_A1.md` (incl. checkpoint 4);
`STAGE_A2.md` §7–§9; `STAGE_A3.md`; `PLAN.md` (last sections, TorInj); lean_mstar `CM4E/AbVar/ThmA.lean` (`gmA`,
`Thm11KappaA`), `MGAK.lean` (`gmAK`, `Thm11KappaAK`); `LSG/ME/*` (all module docstrings; `MainAb`, `MultEstStmt`,
`Geom`, `SliceDim`, `StabG` in full); `LSG/MEV` (file list, imports); `LSG/W88/Sec7.lean` (the consumer); StrongSix
`M2/{BezoutUnmixed,LCI,LCIBlocks}.lean` (statements); `LSG/JacAn3/{PsiLiouville,TaylorCharts,TaylorFields}.lean`
(headers), `LSG/JacAn/A1Facts.lean` (fields).

Labels: [Proved] = in Lean, standard axioms (cited by name); [Proof] = complete paper argument given here; [Lit];
[Numerical] = exact or mod-p computation outside Lean; [Heuristic]; [Est] = line estimate (calibration: ME 16.5k,
MEV 18.5k, A1–A3 as built); [Design] = my choice.

---------------------------------------------------------------------------------------------------------------------

## 0. Summary

1. **Architecture: (c), a new generic core `LSG/MEB/` over abstract "abelian blocks"**, used only by the new
   instance. `LSG/ME` and `LSG/MEV` are not edited; the core imports only those ME files that are already generic.
   * The block interface is **semantic and analytic**: an entire, nowhere-zero lift `θ`, laws that are correct and
     complete *on the image of `θ`*, chart flows satisfied by `θ`, an explicit ideal whose zero set is the image, plus
     a Hilbert certificate and a local-CI certificate. That is exactly what A1–A3 already deliver.
   * The reason is not only risk. ME's elliptic block works with explicit formal identities modulo the cone form
     (`OrderId`, `tr_eq`, the curve lemma over `K⟦z⟧`). The A-block analogue of those identities is A1's E1 family.
     E1 cost about 4.5 CPU-hours for 2 laws × 2 charts. ME needs every law in every chart, about 20–40 times that.
     So a "formal" `BlockData` interface (route (a) as ABVAR sketched it) is infeasible for A. A semantic interface
     makes all of these identities consequences of `ThetaData.laws_eq` and the flow equation.
   * Blocks form a **heterogeneous family** `B : Fin m → AbBlock`. Later E-factors (X7: `G_a² × E^{3r} × A^{3r}`) are
     one more instance (2–4k) and need no further copy.
2. **Consumed from the Jacobian block** (§2): `θ_N`, `kerE`, the 81 laws with `laws_eq`/`laws_complete`, the chart
   flows in charts 0, 4, 8 (`theta_PF_of_rel`, `quadA_cover`), local injectivity at `O` (`germ_locInj`). Most of this is
   [Proved] already. Missing:
   * **full surjectivity onto `V(I_A)`**. The ME genuinely needs it (§2.2); expP-image plus Zariski density is not
     enough. Cost 2–3.5k (A3 agent) plus small certificates. A new route for the boundary is in §2.3, with spike
     degrees 4–5.
   * B5 and B6 certificates (§3). B6 has a new Gröbner-free route from one degree-4 certificate (spike).
   * simplicity of `A` as a complex torus (0.3k);
   * `kerE ⊆ ℚΛ` (0.2–0.3k).

   Not needed: primality of the explicit ideal; V1 for laws 1–3, 5–8; any formal exponential; the F-subspace
   classification (that is A6's job).
3. **B5–B7** (§3):
   * B5 (34 exact identities) reuses A1's P2 exact-identity checker unchanged.
   * B6 is 41 single-copy degree-4 checks with the existing degree-4 normal-form table.
   * B7 is `bezout_blocks` in the core assembly.
4. **Plan** (§4): core 11.5–16.5k, A-instance 1.5–2.5k, surjectivity 2–3.5k, so **≈ 15–22.5k to `multEstB` for
   M1**. ABVAR's A4 row said 20–30k. Three agents plus the existing A3 agent; ≈ 6–9 agent-days on the critical path
   [Heuristic].

---------------------------------------------------------------------------------------------------------------------

## 1. Architecture decision

### 1.1 Options

| | (a) `BlockData` refactor of `LSG/ME` | (b) third parallel copy for `G_a^{d₀} × G_m^{d₁} × A^r` | (c) **hybrid: new generic core, ME untouched** |
|---|---|---|---|
| risk to proved ME | **high**. 8–12k changed lines in a proved 16.5k development. `LSG/MEV` imports 21 ME modules and `W88/Sec7` consumes `multEstAb`, so the refactor ripples into 18.5k more lines | none | none (read-only imports of generic ME files) |
| fits the A-block? | badly. ME's block facts are formal identities mod `F` (`OrderId` sympy identities, `tr_eq`, `curve_eq` over `K⟦z⟧`). An interface on that level forces E1-type certificates for 9 laws × several charts × both arguments (E1: 4.5 CPU-h for about 80 identities), i.e. infeasible. A semantic interface means rewriting the E-block anyway, which is (c) | yes | yes (designed for it) |
| lines to M1 [Est] | 12–18k + MEV fixes 1–3k | 13–20k | 15–22.5k (core 11.5–16.5k + instance 1.5–2.5k + surjectivity 2–3.5k) |
| later E-factors (X7), genus 3 | in principle | a fourth copy (E + A mixed, +12–16k); genus 3 another copy | E-instance 2–4k; genus 3 needs only *existence* of laws with `law_eq` (theta-analytic laws fit the interface directly, which softens R-laws3) |
| build isolation | ME rebuild | the copy imports the heavy `LSG/Jac` certificates unless split | the core never imports `LSG/Jac` and builds in minutes; only the instance does |
| parallel start | blocked by the refactor | starts now | starts now (against the frozen interface, as A2 did with `A1Facts`) |

**Recommendation [Design]: (c).** The extra cost over (b) is about 10% in lines. It buys zero risk to ME/MEV, a
fast-building core that can be written before A1/A3 finish, and free heterogeneous products for M3. (a) is
rejected: it puts the proved ME at risk, and the formal interface it implies does not fit the A-block.

### 1.2 Shape of the core

Directory `LSG/MEB/` (namespace `LSG.MEB`). The group is `G = G_a^{d₀} × G_m^{d₁} × ∏_{k<m} B_k`.

```lean
/-- An abelian block over ℂ: a complex torus `ℂ^g ⧸ per` with an explicit model in `ℙ^{N−1}`. -/
structure AbBlock where
  g N : ℕ
  -- explicit model (only for Bézout / Hilbert / the Nullstellensatz)
  gens : List (MvPolynomial (Fin N) ℂ)
  gens_hom : ∀ Q ∈ gens, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d
  -- uniformisation
  θ : (Fin g → ℂ) → (Fin N → ℂ)
  θ_entire : Differentiable ℂ θ
  θ_ne : ∀ z, θ z ≠ 0
  θ_model : ∀ z, ∀ Q ∈ gens, eval (θ z) Q = 0
  per : AddSubgroup (Fin g → ℂ)
  θ_per : ∀ z, ∀ ω ∈ per, ∃ c ≠ 0, θ (z + ω) = c • θ z
  θ_ker : ∀ z w, (∃ c, θ w = c • θ z) → w - z ∈ per
  per_lattice : IsZLattice ℝ per                      -- discrete, spans ℂ^g over ℝ
  -- surjectivity: the zero set of `gens` is exactly the cone over the image
  surj : ∀ X : Fin N → ℂ, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) → ∃ z c, X = c • θ z
  -- laws: bihomogeneous of bidegree (2,2), correct and complete on the image
  ι : Type; [fι : Fintype ι]
  law : ι → Fin N → MvPolynomial (Fin N ⊕ Fin N) ℂ
  law_bihom : ∀ i k, IsBihom (2, 2) (law i k)
  law_eq : ∀ i u v, ∃ κ : ℂ, evalLaw (law i) (θ u) (θ v) = κ • θ (u + v)
  law_complete : ∀ u v, ∃ i, evalLaw (law i) (θ u) (θ v) ≠ 0
  -- chart flows (Wüstholz derivations, Zariski tangent spaces)
  charts : Finset (Fin N)
  chart_cover : ∀ X ≠ 0, (∀ Q ∈ gens, eval X Q = 0) → ∃ c ∈ charts, X c ≠ 0
  W : Fin N → Fin g → Fin N → MvPolynomial (Fin N) ℂ    -- homogeneous of degree 2, W c j c = 0
  θ_flow : ∀ c ∈ charts, ∀ j l z,
    θ z c * fderiv ℂ θ z (Pi.single j 1) l - θ z l * fderiv ℂ θ z (Pi.single j 1) c = eval (θ z) (W c j l)
  -- independent coordinates at the identity (Hilbert lower bound, transversality)
  i₀ : Fin N; is : Fin g → Fin N
  θ_i₀ : θ 0 i₀ ≠ 0
  coords_locInv : (fderiv ℂ (fun z j => θ z (is j) / θ z i₀) 0).IsInvertible
  -- simple as a complex torus
  simple : ∀ t : Submodule ℂ (Fin g → ℂ), IsRat per t → t = ⊥ ∨ t = ⊤
  -- Hilbert upper bound (B6) and local complete intersection (B5), in projective certificate form
  hilb : ∃ (y : Fin (g+1) → Fin N) (n₀ : ℕ), ∀ M : degree-(n₀) monomial,
           M ∈ Ideal.span gens ⊔ Σ_a X (y a) • (degree n₀−1 part)
  lci : ∃ (s : ℕ) (S : Fin s → MvPolynomial _ ℂ) (F : Fin s → List _),
           (∀ i, (F i).length = N - 1 - g ∧ ofList (F i) ≤ span gens ∧ ∀ Q ∈ gens, S i * Q ∈ ofList (F i)) ∧
           ∀ v, ∃ e, X v ^ e ∈ span gens ⊔ span (range S)
```

(`IsRat per t`: `t.restrictScalars ℝ = span_ℝ (t ∩ per)`, the W88 `IsAbelianTangent` with `per` in place of the
`Ls j` lattices.) About 25 fields. For the A-block the source of each field is in §2.1. For an E-block they would come
from `exists_smul_rep` (surj), the two laws plus the Stage 1 dictionary (`law_eq`), `Deriv` (charts), `SliceIG`
(hilb), `locGen_ofList` (lci: one generator), and the lift `σ³·(℘, ℘′, 1)` (σ is in LSG from Stage 1).

Derived objects in the core (all [Design]):
* points `Pt B := (Fin B.g → ℂ) ⧸ B.per`, an `AddCommGroup` for free, so no group law on the model is ever needed;
  `rep b := θ (Quotient.out b)` (any representative; the cone scalings absorb the choice);
* `GPt := (Fin d₀ → ℂ) × Additive (Fin d₁ → ℂˣ) × (∀ k, Pt (B k))`, with `coords`, `vanish`, `zeros`, `gtransl` as
  in `ME.Geom`, and variables `Var d₀ d₁ B` with `e k (c : Fin (B k).N)`;
* `IGsem := vanish univ`. It is **prime by analyticity**, by the argument of `ME.vanish_H0_isPrime` (the coordinates
  are analytic in `(z, λ)` on a connected domain). `IGexp := ofList (lG_m ++ ⋃ blocks gens)`, and
  `rad_IGexp : IGexp.radical = IGsem` (Nullstellensatz plus `surj` plus `ME.eval_coordsZ_eq_zero`-type density);
* translations `τ g c` through `law`. `eval_transl` is semantic, from `law_eq`; there is no polynomial identity;
* `OrdGt W Q n p` **analytic**: for all `w ∈ W` and `k ≤ n`,
  `iteratedDeriv k (t ↦ Q(x_p + tξ, y_p e^{tη}, θ_k(z̃_k + t w_k))) 0 = 0`. No charts and no formal series: a nonzero
  scalar function does not change the order of a homogeneous `Q`. W88's `ordGt_of_vanishAlong` becomes nearly
  definitional;
* Philippon operators `phOp g w c c' κ Q := Σ_μ ([t^κ] coeff_μ(t)) X^μ`, where
  `Q(law_c(X, law_{c'}(rep g, θ(t w)))) = Σ_μ coeff_μ(t) X^μ` (the coefficients are entire in `t`). Degree
  stability is immediate from `law_bihom`;
* chart derivations `Dh` from `W` exactly as in ME, glued over cosets as in `ME.WustTrans` (canonical chart = some
  `c ∈ charts` with `X_c(σ) ≠ 0`, by `chart_cover`).

Statement (shape of `MultEstAb`, `ME/MultEstStmt.lean`):
```lean
def MultEstB : Prop := ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ C : ℕ, ∀ W S P T D₀ D₁ D₂,
  0 ∈ S → IsHomB P (fun _ => D₂) → P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → P ∉ IGsem →
  1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ → (∀ σ ∈ sig S n, OrdGt W P (n * T) σ) →
  ∃ O : ObstrDataB d₀ d₁ B, O.Proper ∧ ∀ F ⊆ S, (pairwise inequivalent mod O.grp) →
    T ^ (dim W − dim (W ⊓ O.tan)) * F.card * D₀ ^ dim O.h0 * D₁ ^ (d₁ − dim O.U) * D₂ ^ dim O.t
      ≤ C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, (B k).g)
```
Here `n = d₀ + d₁ + m`, `O.t ⊆ ∏_k ℂ^{g_k}` satisfies `IsRat (∏ per)`, and `P ∉ IGsem` is the natural hypothesis (it
says exactly that `P ∘ θ ≢ 0`, which is what A5's auxiliary function gives). M1 uses `d₀ = 0`, `m = r` (`gmA`, `gmAK`),
and `d₀ = 1` for `NotLtildeA`.

### 1.3 What the core reuses, what it re-proves

| ME part (lines) | in the core | [Est] new |
|---|---|---|
| generic files: `SmoothDeriv`, `SmoothPoint`, `DimTrdeg`, `Elimination`, `WustAlg`, `SubgroupHilbAux` (≈ 1.7k); generic lemmas in `WustCoset` (`hfun_inter_ge`), `MainAbAux` (`deg_le_of_hfun'`, `lower_deg`), `SubgroupConeE.indep_prod_fin` | **imported** | 0 |
| `Geom`, `IG`, `Slice`, `SliceDim`, `SliceIG` (1.7k; `IGPrime` dropped) | retyped; `IGsem`/`IGexp`; Hilbert upper bound as a product of block bounds; `radical_sl` via `surj` | 1.6–2.2k |
| `Transl`, `TranslHF`, `StabG`, `OrderTransl` (1.2k) | semantic `eval_transl` from `law_eq` | 0.9–1.3k |
| `Deriv`, `Order`, `OrderId`, `FormalExp`, `PhOp*`, `Chain`, `Chain2` (4.3k) | analytic `OrdGt`, `phOp`, Taylor/word bridge from `θ_flow`, the two-parameter lemma (§4 risk R2); `OrderId` and the formal ODE disappear | 2.5–4k |
| subgroup layer (`SubgroupLie`, `Lift`, `ExpSurj`, `Tangent`, `TanSp`, `Dhat`, `Dim`, `Irred`, `Comp`, `Graded`, `Proj`, `Hilb`, `Hilb2`, `ProductRat`, `ProductGraph`; ≈ 4.3k) | lifts are just `θ` (no `(z−l)³(℘,℘′,1)` patching); exp is onto `Pt` by definition; `SubgroupConeE` replaced by `coords_locInv`; new: rationality calculus and the **pivot lemma** (below) | 3.5–5k |
| Wüstholz (`WustId`, `WustTrans`, `WustCoset`, `SliceWust`, `SliceWustCoset`; ≈ 1.4k) | retyped | 1.2–1.6k |
| assembly (`MainAb`, `MainAbAux`, `MainAbChain`, `MainAbSlice`, `MultEstStmt`; ≈ 1.3k) | B7 included (§3.3) | 1.3–1.8k |
| **total** | | **11.5–16.5k** |

**Pivot lemma** [Proof]. For simple blocks and `t ⊆ ∏_k ℂ^{g_k}` with `IsRat (∏ per) t`, there is `J ⊆ Fin m` such
that `t → ⊕_{k∈J} ℂ^{g_k}` is an isomorphism.
* Induction on `m`. `p_m(t)` is rational and complex, so by `simple` it is `0` or all of `ℂ^{g_m}`.
* In the first case, recurse.
* In the second case `t′ = t ∩ ker p_m` is rational (intersection of rational subspaces: `ℝ` is flat over `ℚ`) and
  complex. Recurse to get `J′`, and take `J = J′ ∪ {m}`. Injectivity and the dimension count are immediate.

This is what the Hilbert lower bound for `H⁰` needs: `(π_L, π_J) : H⁰ → L⁰ × ∏_J B_k` is onto. Each pivot block
contributes the monomials in `(X_{i₀}, X_{is})`, independent on the cone by `coords_locInv` (a homogeneous polynomial
in those coordinates that vanishes on the cone vanishes on an open set of `ℂ^g`, hence is `0`). Each non-pivot
block contributes the free scalings `X_{i₀}^γ` (as in `SubgroupHilb2`). The exponent is `t₂ + m`. [Est 0.4–0.7k inside
the subgroup row.]

---------------------------------------------------------------------------------------------------------------------

## 2. What the ME consumes from the Jacobian block

### 2.1 Field-by-field (A-block instance `LSG/JacBlock/`, `aBlock : AbBlock`, `g = 2`, `N = 9`)

| field / candidate | needed? | provided by | status, cost |
|---|---|---|---|
| prime / unmixed explicit ideal | **no** (primality). `IGsem` is prime analytically (core); unmixedness of the *slice* comes from B5 | — | STAGE_A1 §5's "do not prove primality" confirmed |
| `gens` = 9 quadrics + 3 cubics; `θ_model` | yes | `ThetaData.thetaN_onQ` (A3 [Proved]) for the quadrics; cubics: 27 single-copy checks `X_k C_j ∈ (Q)₄` (they exist because `(Q)₄ = I₄`, ABVAR A0.1 [Numerical]) | 0.1k + 27 tiny checks (degree-4 NF table) |
| `θ`, `θ_entire`, `θ_ne`, `θ_per` | yes | `ThetaData.thetaN`, `analyticAt`, `thetaN` nowhere zero, `thetaN_add`/`facN` (A3 [Proved]) | glue 0.1k |
| `per`, `θ_ker`, `per_lattice` | yes | `per := kerE G` (`LSG.JacAn.kerE`); `lattice_le_ker`, `expP_ker_discrete`, `Beta.linearIndependent_perVec` (A2 [Proved]). `θ_ker` follows from `laws_eq` + `laws_complete` (if `θ w ∥ θ z`, then `law(θ w, negP θ z) ∥ law(θ z, negP θ z) ∥ θ 0`, so `θ(w−z) ∥ θ 0`) | 0.2–0.3k, incl. `kerE/Λ` finite (discrete over a full lattice) |
| `surj` (all of `V(I_A)`) | **yes, essential** (§2.2) | **not yet**: A3.8/A3.9 + boundary exit (§2.3) | **2–3.5k**, A3 agent; certificates by γ |
| laws, `law_bihom` | yes | A1 `A32`/`lawK` (81 coordinates; law `m` = column `m`), `lawK_smul_left/right` (A1/A3 batch [Proved]) | glue |
| `law_eq`, `law_complete` | yes | **`ThetaData.laws_eq`** (`lawK k m (θ_N u)(θ_N v) = κ θ_N(u+v)_k θ_N(u−v)_m`, `κ ≠ 0`), **`ThetaData.laws_complete`** (A3 [Proved]) | glue 0.1k |
| V1 for laws 1–3, 5–8 (laws preserve `V(Q)` on all of `V(Q)²`) | **no**: translations are only evaluated at group points, and `IGexp ⊆ IGsem` | — | saves ≈ 7 × 3.5 CPU-min of A1 work |
| formal exponential; Philippon operators | **no** (not consumed from the block) | built analytically in the core from `θ` and `law` | — |
| `charts = {0, 4, 8}`, `chart_cover`, `W`, `θ_flow` | yes | **`quadA_cover`** (pure algebra) and **`ThetaData.theta_PF_of_rel`** (A3 `TaylorCharts`), A1 `flowW` (chart 0), `W4` + `W4rel` [Proved], `W8` + `W8rel` (`A1Facts` fields, A1 supplying) | glue; W8 pending in A1. [Numerical, `charts_modp.out`]: quadratic chart fields exist for **all nine** charts, so the cover could be enlarged if useful |
| `i₀ = 4`, `is = (1, 8)`, `coords_locInv` | yes | **`germ_locInj`** / `germDerEquiv` (A2 `ExpKer`), from `W4_origin_indep` [Proved] | glue 0.1k |
| `simple` | yes (pivot lemma) | **new** [Proof]: if a complex line `ℓ` meets `Λ` in rank 2, then (writing `perVec e j = c_j ζ^{(j+1)e}`, `Rank4`) two ℤ-independent `α, β ∈ ℤ[ζ]` satisfy `σ₂(α)/σ₁(α) = σ₂(β)/σ₁(β)`. So `γ = α/β` is fixed by `ζ ↦ ζ²`, which generates `Gal(ℚ(ζ₅)/ℚ)`, hence `γ ∈ ℚ`: a contradiction. The line `0 × ℂ` meets `Λ` in `0`. Pass from `kerE` to `Λ` through finite index | 0.3–0.4k |
| `hilb` (B6) | yes | **new**, §3.2 | 0.3–0.5k + 41 tiny checks |
| `lci` (B5) | yes | **new**, §3.1 | 0.3–0.6k + 34 exact identities |
| subgroup classification of `A^r` (F-subspaces) | **not in the ME**. The ME needs only `simple` and the pivot lemma. The F-subspace description is lean_mstar's `sub` soundness (A6) | A6 | ABVAR §2.1, 1.5k, unchanged |
| stabiliser → tangent map, `H⁰` dimension, smooth points | yes, but **generic** (core), from `θ_flow`, `coords_locInv` and the imported `SmoothPoint` | core | — |
| `H⁰(nL)` dimension (Hilbert lower bound) | yes, generic (pivot lemma + `coords_locInv`) | core | — |
| order 2, quasi-periodicity, Taylor heights | **no** (A5's) | A3 `thetaN_order2`, `thetaN_monomial_qp`, `TaylorA` | — |

### 2.2 What kind of surjectivity [Proved, for this proof architecture]

**Needed: every nonzero zero of the explicit ideal is a point.** In Lean-ish form:
`∀ X ≠ 0, (∀ Q ∈ gensA, Q X = 0) → ∃ z c, X = c • θ_N z`.
* ME uses it in `exists_coords_of_IG` → **`radical_sl`** (the slice Nullstellensatz, MainAb step 8:
  `hdim (sl α A) ≤ dim T′`), and in the component step (`Zs_subset_transl`, which translates zeros of `A` by group
  elements, so every zero must *be* a group element).
* Neither step can use the image only. A zero `x` of `sl α A` outside `E(ℂ²)` would add a component to `Z(sl α A)`
  that no coset of `H⁰` covers.
* Replacing `IGexp` by `IGsem` does not help. The zero set of `IGsem` is the Zariski closure of `E(ℂ²)`, so one would
  need "`E(ℂ²)` is Zariski closed", which is the same statement given `E(ℂ²) ⊆ V(Q)`. Zariski density of the image is
  automatic and useless here.
* It is used **only** through `rad_IGexp` and `exists_coords`. Everything else (translations, derivations, Wüstholz,
  stabilisers) is evaluated at group points and needs no surjectivity.

### 2.3 How to get it (owner: A3 agent, `LSG/JacAn3/` or a new `LSG/JacSurj/`; certificates by γ)

* **S-a, affine points** [Design; STAGE_A1 §5]. If `X ∈ V(I_A)` and `X₀ = 1`, then `X = grant p` with
  `p = (X₃, −X₂, X₇, X₆)` and `OnChart p`.
  - Certificates: `X_i − grantᵢ(p)` (`i = 1, 4, 5, 8`), `chartR1 p`, `chartR0 p` all lie in `I_A + (X₀ − 1)`
    (single copy; the cubics are needed).
  - 0.2–0.4k + data.
* **S-b, chart points are in `E(ℂ²)`**.
  - Generic divisors: A2 `follow_par`/`surj_trans` with `ThetaData.laws_eq` (untranslation). Path-connectedness of the
    generic locus of `C_aff²` uses Mathlib's homotopy lifting for covering maps (`Topology/Homotopy/Lifting.lean`) on
    `x : C_aff ∖ {y = 0} → ℂ ∖ {roots}`.
  - Non-generic chart points: closedness of `E(ℂ²)` (compact fundamental domain, as in `psi_const`) together with
    density.
  - 1–2k. STAGE_A3 §2.5(a) estimated 0.5–1k for the generic part alone.
* **S-c, boundary `X₀ = 0`: flow exit (new)** [Proof modulo certificates].
  - `quadA_cover` gives `X₄ ≠ 0` or `X₈ ≠ 0` there.
  - In chart `c ∈ {4, 8}`, run the real-time ODE `V′ = W^{[c]}_v(V)` from `X`. `V(Q)` is invariant under it (small
    single-copy certificates `D^{[c]} Q_i ∈ I_A`).
  - If `X₀(γ(t))` vanished near `0`, every pure Taylor coefficient `D_v^k X₀(X)` (`k ≤ 3`, all directions `v`) would
    vanish.
  - **Certificate**: `X_c^N ∈ I_A + (X₀, symmetrised D^{[c]}-words of X₀ of order ≤ 3)`.
    [Numerical, `boundary_flow_modp.out`]: **N = 4 for c = 4, N = 5 for c = 8** (and N = 4 for c = 1…7). Checkable with
    the existing degree-4/5 NF tables (`TableFacts.nfValid`, `TableFacts5.nfValid5`).
  - So `γ(t)` is affine for small `t ≠ 0`, hence in `E(ℂ²)` by S-a and S-b. Closedness then gives `X ∈ E(ℂ²)`.
  - This replaces STAGE_A3 §2.5(b)'s "boundary = classes of degree < 2" computation. 0.5–0.9k + certificates.
* Optionally the same flow-exit argument replaces the chart-density step of S-b, using a discriminant `Δ` of the
  generic locus. Not spiked.

---------------------------------------------------------------------------------------------------------------------

## 3. B5–B7

### 3.1 B5 `locGen_slA : LocGen (Ideal.span gensA ⊔ span {ℓ − 1}) 7` (any linear `ℓ`)

**Data** [Numerical, `b5_cover_modp.out`]:
* 4 choices of `F_i = (F_{i,1..6})`, random integer combinations of the quadrics.
* For each, `((F_i) : I_A)₃` has dimension 55, with exactly one class `S_i ∉ I_A`.
* With 3 choices, `(S)_N + I_N` stays one short of `S_N` (rank 728/729 at `N = 9`, so probably a common zero). With
  **4 choices, `(S₁..S₄)₇ + I₇ = S₇` at `N = 7`**, the same degree as P2.

**Identities**, all exact over ℤ after scaling:
* (M) `S_i · G = Σ_k h_{ik}^G F_{i,k}` for the 3 complementary quadrics and the 3 cubics `G`. That is 4 × 6 = 24
  identities of degree 5 or 6, with cofactors of degree 3 or 4.
* (C) `D_v X_v⁷ = Σ_i C_{vi} S_i + Σ_j H_{vj} G_j` for `v < 9`, `G_j` the 12 generators. That is 9 identities of
  degree 7, in exactly the P2 format (`D_i X_i⁷ = Σ C_ik dup_k + Σ H_ij Q_j`).

**Checker**: reuse A1's exact-identity pipeline **unchanged**.
* `CheckerP2` and `P2Sound.exact_of_idSeq` (single copy, `Y`-table `T0`, `X`-side identity table, `2^d`-slot
  accumulator).
* Identity tables: degree 7 = `LSG.Jac.Data.P2Tab` (import). Degrees 5 and 6 are new generated data files in
  `LSG/JacBlock/Data/` (generator adapted from `scripts/jac/gen_jac_p2data.py`, copied to `scripts/jacblock/`).
* Exact cofactors come from flint `fmpq` linear algebra, as for `p2_cert.json`.
* Kernel cost [Est]: (C) is like P2 (about 1 CPU-h); (M) is smaller (≤ 3·10³ products each), ≈ 0.3–0.5 CPU-h.
* **Caveat**: `scripts/jac/build_p2.log` currently ends in "deep recursion detected" on `Cert/P2_*`. B5 should start
  after A1's P2 build is green, inheriting its fix.

**Lean glue** (`LSG/JacBlock/LocCI.lean`):
* dehomogenisation of (M) to the slice (`ME.Slice.hom_mem_vanish_of_mem_sl` pattern; `S_i·(ℓ − 1) ∈ ofList l_i` is
  trivial);
* the **cover lemma**, generic (100–150 lines): `x_v⁷ ∈ I + (S)` for all `v` and `ℓ ≡ 1` give
  `ℓ^{55} ∈ (x_v⁷)_v`, hence `1 ∈ sl ℓ I ⊔ span (range S)`;
* then StrongSix `LocGen.of_cover` with `l_i = [F_{i,1..6}, ℓ − 1]`.

The certificates are independent of `ℓ`. Total 0.3–0.6k + data.

### 3.2 B6 `hilb_A` (Gröbner-free, new)

[Numerical, `b6_noether_modp.out`]: with `y = (X₀, X₄, X₈)` (the chart cover triple of `quadA_cover`),
**`(S/I_A)₄ = y₁(S/I_A)₃ + y₂(S/I_A)₃ + y₃(S/I_A)₃`** (rank 144/144). Random `y` also works. `(X₀, X₁, X₄)` and
`(X₀, X₂, X₃)` fail.

[Proof] Given this, for `n ≥ 4`: `S_n = S_{n−4} S_4 ⊆ (y) S_{n−1} + I_n`. By induction `S_n ⊆ Σ_{|a|=n−3} y^a S_3 + I_n`,
so `dim (S/I_A)_n ≤ 165 · C(n−1, 2)`. A generic lemma then gives `H(sl ℓ I; n) ≤ dim (S/I)_n` (homogenise with `ℓ`;
the map `P ↦ Σ_k ℓ^{n−k} P_k` has kernel in `sl ℓ I`). The core's product lemma combines blocks. The constant
(165 instead of 9) goes into `C`.

**Certificate**: 41 of the 144 standard monomials of A1's degree-4 table are not divisible by `X₀`, `X₄` or `X₈`
(checked against the table's basis). For each such monomial `s`, prove `s ≡ X₀a₀ + X₄a₄ + X₈a₈ mod (Q)₄` (`a_i` cubic)
as a single-copy degree-4 check with the existing table (the `law0_neg`/`Diag.single_of_check` mode). With
`nfValid` this covers all 495 degree-4 monomials. 0.3–0.5k + 41 tiny checks.

### 3.3 B7 (inside the core assembly `MEB/Main.lean`)

* Roy's ideal is `A := IGexp ⊔ span F₀`, as in `MainAb`.
  - `A ≤ VOg …` holds because `IGexp ⊆ IGsem`, and derivation words preserve `IGsem` (semantic, `SubgroupTangent`
    pattern with `H = G`).
  - So no flow-invariance certificate for `I_A` is needed.
* Step 8 (`radical_sl`) uses `surj`. Step 13 (properness) uses `rad_IGexp` and `P ∉ IGsem`:
  `hdim (IGexp ⊔ (P)) = hdim (IGsem ⊔ (P)) < hdim IGsem`.
* **Step 12**: write `sl α IGexp = ofList (YZ − 1)_j ⊔ ⨆_k (slA_k).map (rename (e k))`. Then
  * `StrongSix.M2.bezout_blocks` with `r_k = 7` (B5) gives `deg (sl α A) ≤ deg (sl α IGexp)`;
  * B6 + `LocGen.height_eq_of_hdim` give `hdim = d₀ + d₁ + 2r`;
  * the count check `hdim + (d₁ + 7r) = d₀ + 2d₁ + 9r = card Var` passes (STAGE_A4_BEZOUT already checked it).
* `final_arith` with block constants (`2·165` per A-block in place of `12`). 100–200 lines, as estimated.
* lean_lsg imports `StrongSix.M2.LCIBlocks` directly (path dependency; committed in StrongSix as b7f1649, not
  imported by `StrongSix.lean`).

---------------------------------------------------------------------------------------------------------------------

## 4. Staged plan

### 4.1 Stages (riskiest first)

| stage | content | owner | checkpoint | [Est] |
|---|---|---|---|---|
| **A4.0** | freeze `MEB/Block.lean` (§1.2), `MEB/Geom.lean` (points, `coords`, `vanish`, `zeros`, `IGsem` prime, `gtransl`), `MEB/Stmt.lean` (`MultEstB`, `ObstrDataB`) | coordinator | compiles. Every `AbBlock` field has a source or an owner in §2.1. The A3 agent confirms the `surj` and `θ_flow` field shapes | 0.6–0.9k |
| **A4.1a** (risk R2) | analytic `OrdGt`, `phOp` and degree stability; Taylor ↔ `Dh`-words bridge from `θ_flow`; **the two-parameter lemma** (`ordGt_phOp` analogue: homogeneous components of `t ↦ Q∘Θ(p + t₁w + t₂w′)` along `W`) | β | `ordGt_phOp_B` proved for an arbitrary family of `AbBlock`s | 1.5–2.5k |
| **A4.1b** (risk R1) | surjectivity S-c (flow exit + certificates), then S-a, then S-b | A3 agent (+ γ for certificates) | `surjA : ∀ X ≠ 0, OnQ X → ∃ z c, X = c • θ_N z` | 2–3.5k |
| **A4.1c** | B5 and B6 certificate generators and raw checks (after P2 is green); simplicity; `kerE/Λ` finite | γ | `locGen_slA`, `hilb_A`, `simpleA` | 1–1.6k + data |
| A4.2 | core geometry: slices, Hilbert upper (product), `radical_sl`/`rad_IGexp`, translations (semantic), stabilisers, components, `TranslHF` | α | `zeros_translI_B`, `stabG_isSubgroup_B`, `hdata_slIGexp` | 3–4.5k |
| A4.3 | subgroup layer: Lie algebra (closed, ℂ-linear), `TZ = lieAlg`, `H⁰` prime, dimension, product decomposition, rationality calculus and pivot lemma, Hilbert lower bound | β | `hfun_H0_ge_B`, `lieAlg_eq_prod_B` | 3.5–5k |
| A4.4 | chains v2, relevant radicals, Wüstholz transversals and the sliced Wüstholz lemma | α | `wustholz_cosets_sl_B` | 2–3k |
| A4.5 | assembly with B7 | α | **`multEstB : MultEstB`** (any family of `AbBlock`s; standard axioms) | 1.3–1.8k |
| A4.6 | instance `aBlock : AbBlock` from A1/A2/A3 + A4.1b/c; `multEstGmA` for `G_a^{d₀} × G_m^{d₁} × A^r` | γ | axiom audit; the statement A5/A6 consume | 0.5–0.9k |
| **total to M1-ME** | | | | **≈ 15–22.5k** + generated data |

Each checkpoint is an axiom audit of its named theorems from a scratch file (not `Axioms.lean`), as in A1–A3. Light
builds only (`lake build LSG.MEB.<file>`); the core never imports `LSG.Jac.*`.

### 4.2 Parallelisation (no file conflicts)

* **α (core, algebraic side)** owns `LSG/MEB/{Model,Slice*,SliceIG,Transl*,Stab*,Comp*,Chain*,Wust*,SliceWust*,Main*}`.
* **β (core, analytic side)** owns `LSG/MEB/{Exp,Ord*,PhOp*,Deriv*,Subgroup*,Product*,Rational}`.
* **Coordinator** owns `LSG/MEB/{Block,Geom,Stmt}.lean`. Frozen after A4.0; changes on request only.
* **γ (A-instance)** owns `LSG/JacBlock/**` and `scripts/jacblock/**`. It imports `LSG.Jac.*`, `LSG.JacAn.*` and
  `LSG.JacAn3.*` read-only and never edits them.
* **A3 agent** (existing) builds `surj` in its own directory, with γ supplying certificate files under
  `LSG/JacBlock/Cert/`.
* Nobody edits `LSG/ME`, `LSG/MEV`, `LSG/Jac`, `LSG/JacAn*`, existing StrongSix files, `LSG.lean` or `Axioms.lean`.

Dependencies:
* α and β both need only A4.0. α's A4.4 needs β's A4.1a (Taylor/word bridge). β's A4.3 needs α's A4.2 (`StabG`,
  `zcl`) only at its end.
* γ is independent until A4.6.
* Critical path: A4.0 → A4.2 → A4.4 → A4.5 (α), with β alongside. ≈ 6–9 agent-days at the throughput of A1–A3
  [Heuristic].

### 4.3 Main risks (ordered)

1. **R1, surjectivity** (A4.1b). It is essential (§2.2), not yet in Lean, and lives in another agent's directory.
   * S-c now has a concrete plan with small certificates (spike: degrees 4–5).
   * S-b's path-connectedness (covering-space lifting) is the hardest remaining piece.
   * Mitigation: start it now; the core is written against the `surj` field and does not wait.
2. **R2, the analytic two-parameter lemma** (A4.1a).
   * It needs homogeneous components of an analytic function of two variables along `W`
     (`HasFPowerSeriesAt`/`iteratedFDeriv` symmetry in Mathlib v4.35; the bookkeeping is unverified).
   * Fallback: Taylor series of `θ` as formal solutions of the chart ODE (`ME.FormalExp.solve` is generic), with the
     curve lemma derived from `laws_eq` one variable at a time.
   * Spike it first.
3. **R3, core size**: 11.5–16.5k ±40%. ME's estimate was met only after the slice redesign (STAGE2 §11). The slice
   design carries over unchanged, which lowers this risk.
4. **R4, certificate pipeline**: B5 (C) depends on A1's P2 checker (currently "deep recursion" in the build log). B5
   (M) needs new degree-5/6 identity tables. Fallback: the split-declaration pattern of `V1L4`.
5. **R5, interface drift**: A1/A2/A3 field names are still moving (`W8`, `special_hP₀`, the `A1Facts` batches). The
   `AbBlock` instance (A4.6) is a thin glue file, so drift costs hours, not days.
6. **R6, not covered here**: A5's Tier-3 Prop 2.1 (R-Prop21) and A6's F-subspace classification. TorInj is
   unaffected: the ME is hyperplane-agnostic.

### 4.4 Later (M3, not on the M1 path)

* E-block instance: `θ_E = (σ³℘, σ³℘′, σ³)`, laws from `LSG.Elliptic`, `surj` from `exists_smul_rep`, `lci` by
  `locGen_ofList`. 2–4k. X7's group is then a heterogeneous family, at no core cost.
* Genus 3 (`A₇`): the interface asks for laws only through `law_eq`/`law_complete`, so theta-analytic existence fits.
  `gens`, `hilb` and `lci` still need data on P²⁶ (162 quadrics; ABVAR A0.4 says this is not the obstacle).

---------------------------------------------------------------------------------------------------------------------

## 5. Spike files (`scripts/a4_spike/`, untrusted Python, p = 1000003)

| file | result |
|---|---|
| `charts_modp.py` / `.out` | a quadratic chart field `W^{[c]}` (`X₀W^{[c]}_{ji} = X_cW_{ji} − X_iW_{jc}` on `A`) exists for **every** chart `c = 0…8` (27–51 standard-monomial terms) |
| `b5_cover_modp.py` / `.out` | per choice of 6 quadrics, `((F):I_A)₃` has dim 55 and one class outside `I_A`; **4 choices cover at N = 7** (3 choices: 728/729 at N = 9) |
| `b6_noether_modp.py` / `.out` | **`(S/I_A)₄ = (X₀, X₄, X₈)(S/I_A)₃`** (144/144); random triples work; `(X₀,X₁,X₄)`, `(X₀,X₂,X₃)` do not |
| `boundary_flow_modp.py` / `.out` | `X_c^N ∈ I_A + (X₀, symmetrised chart-c derivatives of X₀ of order ≤ 3)` with **N = 4 (c = 1…7), N = 5 (c = 8)** |

---------------------------------------------------------------------------------------------------------------------

## 6. A4.0: the frozen interface (2026-10-31)

**Status [Proved].** Four new files in `LSG/MEB/` (namespace `LSG.MEB`):

| file | lines |
|---|---|
| `Block.lean` | 113 |
| `Geom.lean` | 245 |
| `Stmt.lean` | 144 |
| `Sanity.lean` | 104 |

* `lake build LSG.MEB.Sanity` builds all four, about 20 s per file warm.
* No `sorry`, `axiom` or `native_decide`.
* A scratch audit file runs `#print axioms` on the main declarations (`AbBlock`, `AbBlock.rep_mk`, `expG_surjective`,
  `coords_expG`, `notMem_IGsem_of_eval_ne`, `MultEstB`, `ObstrDataB.expG_mem`, `Sanity.pointBlock`,
  `Sanity.notMem_IGsem_one`). Every one prints `[propext, Classical.choice, Quot.sound]`.
* Imports: Mathlib, `StrongSix.M2.{SeparateGen,Filtered}` and `LSG.W88.Statement` (Mathlib-only, for `torusLie`).
  **Nothing from `LSG/ME`, `LSG/MEV` or `LSG/Jac*`.**
* Not added to `LSG.lean` or `Axioms.lean`. The only remaining warnings are style (lines over 100 characters in
  docstrings, the module-system hint), as elsewhere in the repo.

**"Frozen"** means: the names and statements below change only on request to the coordinator, and the request is
recorded in §6.5. New lemmas and definitions in new files are free.

### 6.1 `Block.lean`

Helper definitions:
* `IsRatSub (Λ : AddSubgroup V) (t : Submodule ℂ V) : Prop` means `t.restrictScalars ℝ = span ℝ {z | z ∈ t ∧ z ∈ Λ}`.
  Instance arguments: `[AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]`.
* `biW N : Fin N ⊕ Fin N → ℕ × ℕ`: bidegree weights, `(1,0)` on the first copy and `(0,1)` on the second.
* `evalLaw L X Y : Fin N → ℂ := fun k => eval (Sum.elim X Y) (L k)`.

`structure AbBlock`, fields in this order (A-block source and owner in brackets):

| group | fields | A-block |
|---|---|---|
| sizes | `g N : ℕ` | `2`, `9` |
| model | `gens : List (MvPolynomial (Fin N) ℂ)`; `gens_hom : ∀ Q ∈ gens, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d` | 9 quadrics + 3 cubics [γ] |
| uniformisation | `θ : (Fin g → ℂ) → Fin N → ℂ`; `θ_analytic : ∀ z, AnalyticAt ℂ θ z`; `θ_ne : ∀ z, θ z ≠ 0`; `θ_model : ∀ z, ∀ Q ∈ gens, eval (θ z) Q = 0` | `ThetaData.thetaN`, its analyticity, `thetaN_onQ` + 27 checks `X_k C_j ∈ (Q)₄` [A3; γ] |
| periods | `per : AddSubgroup (Fin g → ℂ)`; `per_discrete : DiscreteTopology per`; `per_span : Submodule.span ℝ (per : Set (Fin g → ℂ)) = ⊤`; `θ_per : ∀ ω ∈ per, ∀ z, ∃ c : ℂ, c ≠ 0 ∧ θ (z + ω) = c • θ z`; `θ_ker : ∀ z w, (∃ c : ℂ, θ w = c • θ z) → w - z ∈ per` | `kerE G`; `expP_ker_discrete`; `lattice_le_ker` + `linearIndependent_perVec`; `fac_spec`; `θ_ker` from `laws_eq` + `laws_complete` [γ] |
| surjectivity | `surj : ∀ X : Fin N → ℂ, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) → ∃ z, ∃ c : ℂ, X = c • θ z` | §2.3 [A3 agent] |
| laws | `nL : ℕ`; `law : Fin nL → Fin N → MvPolynomial (Fin N ⊕ Fin N) ℂ`; `law_hom : ∀ i k, (law i k).IsWeightedHomogeneous (biW N) ((2, 2) : ℕ × ℕ)`; `law_eq : ∀ i u v, ∃ κ : ℂ, evalLaw (law i) (θ u) (θ v) = κ • θ (u + v)`; `law_complete : ∀ u v, ∃ i, evalLaw (law i) (θ u) (θ v) ≠ 0` | `nL = 9`, law `m` = column `m` of `A32`, converted from A1's `SP` data to `MvPolynomial` (glue: `evalSP = eval`); `ThetaData.laws_eq`, `laws_complete` [γ] |
| charts | `charts : Finset (Fin N)`; `chart_cover : ∀ X, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) → ∃ c ∈ charts, X c ≠ 0`; `W : Fin N → Fin g → Fin N → MvPolynomial (Fin N) ℂ`; `W_hom : ∀ c j l, (W c j l).IsHomogeneous 2`; `W_chart : ∀ c j, W c j c = 0`; `θ_flow : ∀ c ∈ charts, ∀ (j : Fin g) (l : Fin N) (z : Fin g → ℂ), θ z c * fderiv ℂ θ z (Pi.single j 1) l - θ z l * fderiv ℂ θ z (Pi.single j 1) c = eval (θ z) (W c j l)` | `{0, 4, 8}`, `quadA_cover`; `flowW`/`W4`/`W8` rescaled to speed 1; `theta_PF_of_rel` [γ] |
| coordinates | `i₀ : Fin N`; `is : Fin g → Fin N`; `θ_i₀ : θ 0 i₀ ≠ 0`; `coords_locInv : ∃ f' : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ), HasFDerivAt (fun z j => θ z (is j) / θ z i₀) (f' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0` | `i₀ = 4`, `is = (1, 8)`; `germ_locInj`/`germDerEquiv` [γ] |
| simplicity | `simple : ∀ t : Submodule ℂ (Fin g → ℂ), IsRatSub per t → t = ⊥ ∨ t = ⊤` | the CM argument of §2.1 [γ] |
| B6 | `hilb_y : Fin (g + 1) → Fin N`; `hilb_deg : ℕ`; `hilb : ∀ M, M.IsHomogeneous hilb_deg → M ∈ Ideal.span {Q \| Q ∈ gens} ⊔ Ideal.span (Set.range fun a => X (hilb_y a))` | `y = (0, 4, 8)`, `hilb_deg = 4`; 41 checks [γ] |
| B5 | `lci_s : ℕ`; `lci_S : Fin lci_s → MvPolynomial (Fin N) ℂ`; `lci_F : Fin lci_s → List (MvPolynomial (Fin N) ℂ)`; `lci_len : ∀ i, (lci_F i).length + g + 1 = N`; `lci_F_le : ∀ i, Ideal.ofList (lci_F i) ≤ Ideal.span {Q \| Q ∈ gens}`; `lci_mem : ∀ i, ∀ Q ∈ gens, lci_S i * Q ∈ Ideal.ofList (lci_F i)`; `lci_cover : ∀ v, ∃ e : ℕ, X v ^ e ∈ Ideal.span {Q \| Q ∈ gens} ⊔ Ideal.span (Set.range lci_S)` | `s = 4`, the cubics `S_i`, six quadric combinations each; 24 + 9 exact identities [γ] |

Differences from the §1.2 sketch [Design]:
* `θ_analytic` (`AnalyticAt`) replaces `Differentiable`. This avoids several-variable "differentiable ⇒ analytic", and
  A3 has `analyticAt_theta`.
* `per_discrete` + `per_span` replace `IsZLattice`.
* Laws are indexed by `Fin nL`, so `AbBlock : Type`.
* `hilb` is stated for homogeneous `M` of degree `hilb_deg`. The `lci` fields need no homogeneity of `S_i`, `F_i`.

Notes for γ:
* `per := kerE G`. A5's `StatementAbVar` uses `PerA` with `latt`, and `latt ≤ kerE` has finite index. The bridge
  (`IsRatSub` for `kerE` ↔ for `latt`, and the `N • u` in `htil`) belongs to the instance and to A5, not the core.
* `θ_flow` has speed 1. Rescale A1's `Wn = 2W`, `W4n = 4·W4` and `W8` accordingly. `PFAt` is invariant under
  rescaling `θ`, so `thetaN` can be used directly.

### 6.2 `Geom.lean`

* **Block points.**
  - `AbBlock.Pt b := (Fin b.g → ℂ) ⧸ b.per` (an abbrev, so `AddCommGroup` comes for free).
  - `AbBlock.rep b p := b.θ (Quotient.out p)`.
  - `AbBlock.mk_out_sub` (`out (mk u) - u ∈ per`), `AbBlock.rep_mk` (`∃ c, c ≠ 0 ∧ rep (mk u) = c • θ u`),
    `AbBlock.rep_ne_zero`.
* **Variables and blocks.**
  - `inductive Var (d₀ d₁ : ℕ) (B : Fin m → AbBlock)` with constructors `x (i : Fin d₀)`, `y (j : Fin d₁)`,
    `z (j : Fin d₁)`, `e (k : Fin m) (c : Fin (B k).N)`. `DecidableEq` is derived; `Fintype` comes through
    `Var.equivSum`.
  - `inductive Blk (m : ℕ)` with constructors `x | yz | e (k : Fin m)`, and `blk : Var d₀ d₁ B → Blk m`.
* **Groups and exponential.**
  - `GPt d₀ d₁ B := (Fin d₀ → ℂ) × Additive (Fin d₁ → ℂˣ) × (∀ k, (B k).Pt)`, with `GPt.ym`.
  - `Tan d₀ d₁ B := (Fin d₀ → ℂ) × (Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ)`.
  - `expU`, `expGf`, `expGf_add`, **`expG d₀ d₁ B : Tan d₀ d₁ B →+ GPt d₀ d₁ B`**, `expG_apply`, **`expG_surjective`**.
* **Lift and cone coordinates.**
  - **`liftB u : Var d₀ d₁ B → ℂ`**: `x i ↦ u.1 i`, `y j ↦ exp (u.2.1 j)`, `z j ↦ exp (-u.2.1 j)`,
    `e k c ↦ (B k).θ (u.2.2 k) c`.
  - `coords g lam` (`lam : Fin m → ℂˣ` scales block `k` of `rep`).
  - **`coords_expG : ∃ lam, coords (expG d₀ d₁ B u) lam = liftB u`**.
* **Vanishing ideals.**
  - `vanish E` (through `StrongSix.M2.vanish'`), `mem_vanish`, `vanish_antitone`.
  - **`IGsem d₀ d₁ B := vanish Set.univ`**.
  - **`notMem_IGsem_of_eval_ne : eval (liftB u) P ≠ 0 → P ∉ IGsem d₀ d₁ B`**.
* **Zariski topology and subgroups.** `zeros`, `IsZClosed`, `zcl`, `subset_zcl`, `isZClosed_zcl`, `IsSubgroupG`
  (fields `zero_mem`, `add_mem`, `neg_mem`), `gtransl`, `mem_gtransl`.

**Not in A4.0 (first tasks of the core agents):**
* `IGsem_isPrime` (α): the `ME.vanish_H0_isPrime` argument with `liftB` and `coords_expG`;
* `IGexp`, `rad_IGexp` and the slices (α);
* the translations `τ` and Philippon operators (α, β).

### 6.3 `Stmt.lean`: the form W88 §7 / Prop 6.1 consume

**Template.** In `W88/Sec7.lean` (`theorem41Abelian_of`), `prop61_b` yields `∃ x, Psi x ≠ 0` and
`VanishAlong Psi W T (∑ j, h j • y j)`. With `Psi = fun u => eval (liftB u) P`, these become the hypotheses directly,
**with no bridge lemma**:
* `P ∉ IGsem`, by `notMem_IGsem_of_eval_ne`;
* `OrdGtB … n`, for any `n < T`.

Definitions:
* `perAb B := AddSubgroup.pi Set.univ fun k => (B k).per`.
* `Per d₀ d₁ B : AddSubgroup (Tan d₀ d₁ B)`, equal to `0 × 2πiℤ^{d₁} × ∏ per_k`.
* `wk k : Var d₀ d₁ B → ℕ`; `IsHomB P d := ∀ k, P.IsWeightedHomogeneous (wk k) (d k)`; `DfunB D₀ D₁ D₂ : Blk m → ℕ`.
* `sigB S r`, as `ME.sig`.
* **`OrdGtB W P n p`** (analytic, at some lift):
  ```lean
  ∃ u, expG d₀ d₁ B u = p ∧ ∀ w ∈ W, ∀ k ≤ n,
    iteratedDeriv k (fun s : ℂ => eval (liftB (u + s • w)) P) 0 = 0
  ```
* `tanOf h0 U t := h0.prod ((torusLie U).prod t)`.
* **`structure ObstrDataB d₀ d₁ B`**, with fields:
  - `h0`, `U`, `t`, and `t_rat : IsRatSub (perAb B) t`;
  - `grp`, `grp_eq : grp = zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set _))`, `grp_sub : IsSubgroupG grp`,
    `grp_closed : IsZClosed grp`;
  - `lie : ∀ v, (∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ grp) ↔ v ∈ tanOf h0 U t`;
  - **`htil : ∀ u, expG d₀ d₁ B u ∈ grp → ∃ N : ℕ, 0 < N ∧ N • u ∈ (tanOf h0 U t).toAddSubgroup ⊔ Per d₀ d₁ B`**.

  Plus `ObstrDataB.tan`, `ObstrDataB.Proper` (`tan ≠ ⊤`) and `ObstrDataB.expG_mem`.
* **`MultEstB`**: exactly the shape of `ME.MultEstAb`, with `IsHomB`, `StrongSix.M2.FLE ℂ blk (DfunB D₀ D₁ D₂)`,
  `P ∉ IGsem d₀ d₁ B`, `sigB`, `OrdGtB`, `ObstrDataB`, and right-hand side
  `C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, (B k).g)`.

About `htil`:
* It is new compared with `ME.ObstrData`. It is W88's `htil_le_span`, moved into the core (β proves it via `exp⁻¹(H⁰)`
  and the finite index of `H⁰` in `H`).
* With it, the §7 counting (`exists_inequiv_grid`) and the additive-part and character lemmas of `Sec7Count` need only
  `grp_eq`, `grp_sub` and `htil`. The A5 consumer then needs no subgroup layer.

### 6.4 `Sanity.lean`, and why there is no elliptic instance

* **`pointBlock : AbBlock`**:
  - the data: `g = 0`, `N = 1`, `θ ≡ 1`, `gens = []`, `per = ⊥`, one law `X₀² Y₀²`, `hilb_deg = 1`, `lci_S = 1`,
    `lci_F = []`;
  - it shows the field list is satisfiable and exercises the law and certificate fields;
  - the analytic fields hold vacuously, because `ℂ⁰` is a point.
* `notMem_IGsem_one` instantiates the statement-side definitions on `G_a^{d₀} × G_m^{d₁} × pt^m`.
* **The elliptic `AbBlock` was skipped: it is not cheap** (est. 1.5–3k, not ≤ 0.5k). What costs real work:
  - **`θ` entire and nowhere zero.** `θ = (σ³℘, σ³℘′, σ³)` (cone order `U, V, W`) needs removable singularities at
    `Λ`, and `σ³℘′ → −2` there. LSG has `σ` from Stage 1 but no entire cone lift; `ME.SubgroupLift` deliberately uses
    the local lifts `(z−l)³(℘, ℘′, 1)`.
  - **`law_eq` at every pair, including lattice points.** It has to come from the algebraic laws (`LSG.Elliptic`) and
    the Stage 1 dictionary, extended by the identity theorem in two variables.
  - **`θ_flow`** for the cone charts, through the poles.
  - **`θ_ker`**: `℘(w) = ℘(z)` and `℘′(w) = ℘′(z)` imply `w − z ∈ Λ`.
  - **`coords_locInv`** at `0`.

  The real test of the interface is γ's A-block instance (A4.6), almost all of whose fields are already proved
  (§2.1). The E-instance stays in §4.4 (M3).

### 6.5 Change requests

Record each one as: date, requester, field, reason, decision.

* **Note (2026-10-31, γ, A4.6): no change requested.** Every frozen field was instantiated for the A-block
  (`LSG.JacBlock.aBlockOf`, `LSG/JacBlock/ABlock.lean`). Two remarks, neither needing a change:
  - Numerals in `Fin b.N` do not elaborate for a concrete block (`OfNat (Fin (aBlockOf …).N) 4` fails, since
    `N` is a structure projection). Consumers write `(4 : Fin 9)`; `(aBlockOf …).i₀ = (4 : Fin 9)` holds by `rfl`.
  - `hilb_deg = 14` for the A-block (not 4): six certificates plus a pigeonhole argument, instead of 41. Only the Hilbert
    constant changes.

* **CR1 (2026-10-31, α): `MultEstB`, the number of summands and the order.** `sigB S (d₀ + d₁ + m)` and
  `OrdGtB W P ((d₀ + d₁ + m) * T)` were changed to `sigB S (d₀ + d₁ + ∑ k, (B k).g)` and
  `OrdGtB W P ((d₀ + d₁ + ∑ k, (B k).g) * T)`.
  - Reason: Philippon's `n` is `dim G`. Roy's pigeonhole (`ME.exists_flat_rel`) needs `n` strict drops of the
    relevant Hilbert dimension between `hdim (relI L₀) ≤ hdim IGsem − 1 = d₀ + d₁ + Σ_k (g_k + 1) − 1` and
    `hdim (relI L_n) ≥ m` (ideals vanishing at the identity contain the `m` block cones). That forces
    `n ≥ d₀ + d₁ + Σ g_k`. With `n = d₀ + d₁ + m` (copied from `ME.MultEstAb`, where every `g_k = 1`) the chain
    argument fails as soon as some `g_k ≥ 2`, e.g. for the A-block.
  - Effect on consumers: the auxiliary function must vanish on `Σ(dim G)` to order `> dim G · T`. That is the
    standard form of Philippon's hypothesis and only changes the parameter `n` in A5's construction.
  - Decision: applied by α (coordinator unavailable). Only `Stmt.lean`'s `MultEstB` and its docstring changed;
    nothing else in `Block`/`Geom`/`Stmt` was touched.

---------------------------------------------------------------------------------------------------------------------

## 7. α/β interface (maintained by α; β please append requests/answers in §7.3)

Status: **2026-10-31 (α), checkpoint 2**: A4.2, A4.4 and A4.5 done. `multEstB_of : MEBInputs → MultEstB`, and Wüstholz is derived from the tangent-space bound `TZProp` (field `tz`). File ownership as in §4.2 (α also owns the new files `ModelIG`, `SliceBlock`, `MainAux`, `MainHyp`, `MainGrp`, `WustB`, `WustAlgB`, `WustCosetB`). Every α statement below that depends on β is stated in
α's files as an explicit hypothesis (a `Prop`-valued structure field or theorem argument), never as an axiom.

### 7.1 What α provides (β may import these instead of re-proving)

All [Proved], standard axioms only (`#print axioms` from a scratch file: `[propext, Classical.choice, Quot.sound]`),
no `sorry`. Build: `lake build LSG.MEB.Main` builds everything below.

| file | lines | content (namespace `LSG.MEB`) |
|---|---|---|
| `Model.lean` | 519 | `wV`, `wE`, `wk_eq_wE`, `isHomB_iff_wV`, `eval_scale`, `coords_mul`, **`eval_coords_eq_zero_iff`**; `coordsZ`, `eval_coordsZ_eq_zero`; Zariski basics (`zeros_vanish`, `vanish_injOn`, `vanish_le_vanish_iff`, `isZClosed_zeros`, `isZClosed_iInter`, `IsZClosed.inter`, `zcl_minimal`, `vanish_zcl`, `zcl_mono`, `mem_zeros_iff_le_vanish`, `mem_zeros_span`, `mem_vanish_singleton_iff`, `vanish_ne_top`, `vanish_empty`); `comp_mem_vanish`, **`multiComp_mem_vanish`**, `sum_multiComp`, `exists_homog`, `homogVanish`, `exists_homogVanish_ne`, `zeros_homogVanish`; **`vanish_singleton_isPrime`**; `gtransl_*`; simp lemmas `coords_x/y/z/e`, `GPt.ym_*`, `blk_*` |
| `ModelIG.lean` | 302 | `liftZ`, `LZ`, `liftZ_analyticAt`, `mem_IGsem_iff_liftZ`, **`IGsem_isPrime`** (identity theorem on `Tan × ℂ^m`), `AbBlock.blockI`, `YZ`, `lYZ`, **`IGexp`**, `IGexp_le_vanish`, `IGexp_le_IGsem`, **`exists_coordsZ_of_IGexp`** (uses `surj`), **`rad_IGexp`**, `mem_IGsem_iff_coordsZ` |
| `Transl.lean` | 231 | `evalLaw_smul_hom`, `AbBlock.evalLaw_rep`, **`τ g c := lawSub c (coords g 1)`**, `transl_mem_FLE`, `isHomB_transl`, **`eval_transl`**, `Good`, `exists_good`, **`eval_transl_good`**, `exists_sq_mul`, `transl_mem_IGsem`, `transl_mem_vanish_gtransl`, `translI`, **`zeros_translI`** |
| `StabG.lean` | 239 | `isZClosed_gtransl`, `gtransl_eq_of_subset`, `stabG`, **`stabG_isSubgroup`**, `stabG_eq_zeros`, **`isZClosed_stabG`**, **`zcl_isSubgroup`**, `exists_components`, **`vanish_gtransl_isPrime`** (no law polynomial: closed-cover argument) |
| `TranslHF.lean` | 177 | `nLaw B = ∏ nL_k`, **`hfun_le_transl`** (`H(I(E);t) ≤ nLaw · H(I(E+g);2t)`), `HasData.comp_two`, **`hdim_vanish_gtransl`** |
| `Slice.lean` | 307 | `Alpha B` (one linear chart form per block), `lsl`, `sl`, `lval`, `nrm`, `vanishS`, `Nsub`, `hfun_eq_finrank_quotient`, `hom_mem_vanish_of_mem_sl`, `hfun_le_of_hom`, **`hfun_le_sl`**, **`exists_good_alpha`** |
| `SliceBlock.lean` | 375 | per block, from `hilb`/`lci` only: `homogeneousComponent_mem_span`, `hilb_hom`, `Std e`, **`hom_mem_span_Std`**, `card_Std_le`, **`mem_span_Std_slice`** (B6); `lform`, `slB`, **`locGen_slB`** (B5), `g_lt_N` |
| `SliceIG.lean` | 433 | `hfun_le_of_span`, **`hfun_slIGexp_le`** (B6, all blocks), **`slIGexp_eq_blocks`** (block form for `bezout_blocks`), **`locGen_slIGexp`**, `card_Var`, `polB`, `cB`, **`hdata_slIGexp`** (`hdim = d₀ + d₁ + Σ g_k`, degree bound) |
| `SliceDim.lean` | 356 | `nscal`, `vanishP`, `homP`, `eval_homP`, **`vanishP_isPrime`**, **`hdim_vanishP_add_le`**, `hom_mem_vanish_of_mem_vanishP`, `sl_vanish_le_vanishP`, `Zs`, `exists_coords_of_IGexp`, **`radical_sl`** |
| `Comp.lean` | 401 | **`hfun_inter_ge`**, `vanish_union`, `exists_sep_proj`, `not_gtransl_subset`, `exists_reps_G`, `coords_nscal_univ`, `biUnion_gtransl_cover`, `relI`, **`exists_relevant_prime`**, **`component_rel`**, `point_of_lsl_notMem`, **`hdim_vanishP_cosets_le`**, **`hfun_sum_cosets_P`** |
| `Chain.lean` | 343 | `sigB` lemmas, `gensR2`, `Lr2` (`IGsem ⊔ …`), degrees, `Lr2_le_vanish_zero`, **`hdim_ge_of_le_vanish_zero`**, **`hdim_IGsem_le`** (`≤ dim G + m`), `exists_gen_L0_notMem`, `hdim_Lr2_zero_lt_IGsem`, **`exists_flat_rel`** (`n = dim G`), **`hAVO2`**, **`Zs_subset_transl`** |
| `MainAux.lean` | 206 | `finrank_torusLie`, `finrank_submodule_prod`, `finrank_tanOf`, `deg_le_of_hfun'`, `lower_deg`, `lin3`, `pow_self_mono`, `CstB`, **`final_arith_B`** |
| `MainHyp.lean` | 68 | **`SubgroupData`**, **`MEBInputs`** (§7.2: the inputs still to be proved) |
| `Main.lean` | 321 | **`multEstB_of : MEBInputs → MultEstB`** (incl. B7 via `StrongSix.M2.bezout_blocks`) |
| `SliceWust.lean` | 283 | `Lsl`, `lpow`, `exists_hom_sl`, **`nzd_sl`**, `Eul`, `Eul_apply`, `Eul_mem_vanish`, `Eul_mem_VOg`, `Dsl`, `DL_mem_Lsl`, **`wustholz_sl_of_data`** (imports the generic `ME.WustAlg`) |
| `MainGrp.lean` | 95 | `mem_vanish_expG_iff`, **`vanish_expG_isPrime`** (`zcl (exp t)` irreducible, identity theorem on `t × ℂ^m`), **`vanish_grp_isPrime`** (ME's `vanish_H0_isPrime`, for any `ObstrDataB`) |
| `WustAlgB.lean` | 186 | `Dh_add_apply`, `Dh_smul_apply`, `Dh_C_mul`, `pairL`, `Dh_X`, **`Eul_Dh`**, `homOrd`, `IGsem_le_homOrd`, **`homOrd_le_VOg`** (item 3, via β's `DL_Dmix_mem_vanish`), **`TZProp`**, **`exists_biorth`** |
| `WustCosetB.lean` | 284 | `isWH_det`, `rescale_rel`, **`coset_data`** (identity data on each coset, pairing at a point of the coset, no transport), **`exists_seps`**, **`exists_wustData`** (gluing), **`wust_of_tz`** |
| `WustB.lean` | 93 | **`WustData`** (transversal data + order bridge), **`wust_of_data`**, **`wust_field_of_data`**: the field `SubgroupData.wust` from `WustData` on every finite union of distinct cosets of `H⁰` |

Name clashes: β please do not define the names above in `LSG.MEB`; if β already has a copy, tell α in §7.3 and α
will rename.

### 7.2 What α needs from β: `MEBInputs` (`LSG/MEB/MainHyp.lean`)

`multEstB_of : MEBInputs → MultEstB` is proved. The remaining input is
```lean
def MEBInputs : Prop := ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ cL : ℕ, 0 < cL ∧
  ∀ H : Set (GPt d₀ d₁ B), IsSubgroupG H → IsZClosed H → Nonempty (SubgroupData d₀ d₁ B cL H)
```
For a Zariski-closed subgroup `H`, `SubgroupData d₀ d₁ B cL H` has the fields below. `cL` may depend only on
`d₀ d₁ m B` (ME: `4^m`; for MEB it will contain `nLaw B` from `hfun_le_transl`).

| field | statement (abridged; exact form in `MainHyp.lean`) | ME analogue | owner |
|---|---|---|---|
| `O` | `ObstrDataB d₀ d₁ B`; `O.grp` is the identity component `H⁰` | `ObstrData.ofSubgroup`, `H0` | β |
| `grp_le` | `O.grp ⊆ H` | `H0_subset` | β |
| `cosets` | `∃ Rc, (∀ c ∈ Rc, c ∈ H) ∧ H ⊆ ⋃ c ∈ Rc, gtransl c O.grp` | `finite_cosets_H0` | β |
| `hdim` | `∀ D, (∀ i, 1 ≤ D i) → (hdata blk D ℂ (vanish O.grp)).1 = finrank ℂ O.tan + m` | `hdim_H0` | β |
| `coset_ge` | `∀ α a, (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) → ∀ D₀ D₁ D₂ t, (t*D₀/t₀+1)^t₀ (t*D₁/t₁+1)^t₁ (t*D₂+1)^t₂ ≤ cL * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP univ α (gtransl a O.grp)) (2*t)` with `t₀ = finrank O.h0`, `t₁ = d₁ − finrank ℚ O.U`, `t₂ = finrank O.t` | `hfun_P_coset_ge` | β (uses α's `hfun_le_transl`, `hfun_le_of_hom`, `hom_mem_vanish_of_mem_vanishP`) |
| `tz` | `TZProp O`: for `g`, `u` with `expG u = g`, and `w`, if `deriv (r ↦ P(liftB (u + r w))) 0 = 0` for every multihomogeneous `P ∈ I(g + O.grp)`, then `w ∈ O.tan` | `mem_TZ_iff` (at every point) | β′ (request (5)) |

**Wüstholz.** Done (checkpoint 2): `WustCosetB.wust_of_tz` derives the sliced Wüstholz lemma from `tz`, for
ideals `A ≤ homOrd W S₀ E` (spanned by multihomogeneous elements of `ordIdealB`; Roy's `A` is of this form). The
older reduction (kept): `WustB.wust_field_of_data` reduces it to `WustData d₀ d₁ B W E ℓ` on
`E = ⋃_{a ∈ R} (a + H⁰)` (distinct cosets, `ℓ = dim W − dim (W ⊓ O.tan)`), with `M ∉ I(a + H⁰)`: derivations `Dv`,
`Q_j ∈ I(E)`, multihomogeneous `M` with `Dv i Q_j − δ_ij M ∈ I(E)`; an order ideal `VOg Dw Ws I(E)` with
`[Eul_k, Dw] = Dw`, `Dv` lowering it by one, and the bridge `A ≤ ordIdealB W S₀ E → A ≤ VOg Dw Ws I(E) S₀`.
ME's route to such data: identity data at `0` (pairing with left kernel `lieAlg`; β), transport
to the cosets by `τ` (needs the translation identity for the chart derivations; β's Taylor/word bridge), glue with
separators, then the abstract sliced Wüstholz lemma with Euler corrections (generic algebra; α). Concretely, α
needs from β, for the chart derivations `Dh c w : Derivation ℂ K[Var] K[Var]` built from `θ_flow`:
1. identity data: `w₁..w_ℓ ∈ W`, `T_j ∈ I(H⁰)` multihomogeneous of one multidegree, `N ∉ I(H⁰)` multihomogeneous,
   `Dh c w_i T_j − δ_ij N ∈ I(H⁰)` [`exists_identity_data_hom`];
2. the translation identity: for `σ ∈ G`, `Dh (chartAt σ) w (τ σ c P) ≡ Lc · τ σ c (Dh c' w P)` modulo `I(σ + V)` on
   multihomogeneous `P` [`ME.WustTrans.transport`, `tr_id`];
3. the order bridge: `A ≤ ordIdealB W S0 E` ⇒ words of length `≤ S0` in the `Dh c w` (`w ∈ W`, all charts) map `A`
   into `I(E)` [`mem_VOg_mix`];
4. Euler compatibility `Eul_k ∘ Dh − Dh ∘ Eul_k = Dh` [`Eul_Dh`].

**Revised estimates (α, 2026-10-31) [Est].** α's A4.2/A4.4/A4.5 core is 4.75k lines, against a plan of 6.3–9.3k.
What is left:
* α: nothing on the critical path. `WustData` is constructed (`WustAlgB` + `WustCosetB`, 0.47k), without transport.
* β′: `SubgroupData` (`O` with `htil`, `grp_le`, `cosets`, `hdim`, `coset_ge`, `tz`), as planned in A4.3 (3.5–5k).
  `tz` is request (5).

### 7.3 Requests and answers

**β → α, 2026-10-31 (1): translations by an arbitrary vector.** β needs translation by a *moving* (non-group) point
for `phOp`, so β writes the substitution once, in `LSG/MEB/PhOpLaw.lean` (imports `Model` only):
* `lawPt (c : ∀ k, Fin (B k).nL) (X Y : Var d₀ d₁ B → ℂ) : Var d₀ d₁ B → ℂ`: `x ↦ X + Y`, `y ↦ X·Y`, `z ↦ X·Y`,
  block `k` ↦ `evalLaw ((B k).law (c k)) X_k Y_k`;
* `lawSub c (Y : Var d₀ d₁ B → ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ B) ℂ` (second argument
  a constant vector), `eval_lawSub : eval X (lawSub c Y Q) = eval (lawPt c X Y) Q`;
* `dblB D : Blk m → ℕ` (`x, yz ↦ D`, `e k ↦ 2 D`), `lawSub_mem_FLE : Q ∈ FLE ℂ blk D → lawSub c Y Q ∈ FLE ℂ blk (dblB D)`,
  `isHomB_lawSub : IsHomB Q d → IsHomB (lawSub c Y Q) (2 • d)`.

Proposal: α defines `τ g c := lawSub c (coords g 1)` in `Transl.lean` (so `transl_mem_FLE` and homogeneity are
one-liners). β's translation-invariance lemma is stated for `lawSub c (coords v lam) Q`, so it applies to `τ` by
`rfl`. If α keeps an independent `τ`, please add `τ g c = lawSub c (coords g 1)`.

**β → α (2): what β delivers for the chain and Roy's vanishing claim** (target statements; all for `IsHomB P d`;
`OrdGtB` is the frozen one):
* `Ord.lean`: `OrdAt W P n u` (the inner condition of `OrdGtB` at the lift `u`, at every constant block scaling `μ`);
  `ordGtB_iff (hP : IsHomB P d) : OrdGtB W P n p ↔ ∀ u, expG d₀ d₁ B u = p → OrdAt W P n u` (lift-independence);
  `ordIdealB W n E : Ideal _` (order `> n` at every lift and every scaling of every point of `E`), `mem_ordIdealB_of
  (hQ : IsHomB Q d) : (∀ g ∈ E, OrdGtB W Q n g) → Q ∈ ordIdealB W n E`, `IGsem_le_ordIdealB`, `ordIdealB_le_vanish`,
  `ordIdealB_anti`.
* `PhOp.lean`: `phOp (g : GPt d₀ d₁ B) (w : Tan d₀ d₁ B) (c c' : ∀ k, Fin (B k).nL) (κ : ℕ) Q`;
  `eval_phOp : eval X (phOp g w c c' κ Q) = iteratedDeriv κ (fun t => eval (lawPt c X (lawPt c' (coords g 1)
  (liftB (t • w)))) Q) 0 / κ!`; `phOp_mem_FLE : Q ∈ FLE ℂ blk D → phOp g w c c' κ Q ∈ FLE ℂ blk (dblB D)`;
  `isHomB_phOp : IsHomB Q d → IsHomB (phOp g w c c' κ Q) (2 • d)` (all `κ`).
* `PhOpTwo.lean`:
  - `phOp_mem_vanish (h : OrdGtB W P n (h₀ + g)) (hw : w ∈ W) (hκ : κ ≤ n) : phOp g w c c' κ P ∈ vanish {h₀}`
    (every `c, c'`; gives `Lr2_le_vanish_zero` with `h₀ = 0`);
  - `ordGtB_of_phOp_mem_vanish (h : ∀ w ∈ W, ∀ κ ≤ n, ∀ c c', phOp g w c c' κ P ∈ vanish {h₀}) :
    OrdGtB W P n (h₀ + g)` (with the previous item: `zeros_phOp`);
  - **two-parameter lemma** `ordGtB_phOp (h : OrdGtB W P N (y + σ)) (hw : w' ∈ W) (hκ : κ + T ≤ N) :
    OrdGtB W (phOp σ w' c c' κ P) T y`;
  - translation invariance, every law choice: `ordGtB_lawSub (h : OrdGtB W Q n (y + v)) (lam) :
    OrdGtB W (lawSub c (coords v lam) Q) n y`.

  With these, `hAVO2` is: `L_{r+1} ⊆ p`, `v ∈ Z(p)`, `s ∈ S`, `h ∈ GV` ⇒ (zeros) `P` has order `> (r+1)T` at
  `(s + h + v) + σ` ⇒ (two-parameter) `phOp σ w' κ P` has order `> T` at `s + h + v` ⇒ (translation) the generator has
  order `> T` at `s + h`.
* Derivations (`Deriv*.lean`) and the subgroup layer (`Subgroup*.lean`): statements will be added here as they firm
  up; ME names are kept where the statement is the same.

**α → β, 2026-10-31 (1): accepted.** `Transl.lean` defines `τ g c := lawSub c (coords g 1)` (`τ_def` is `rfl`) and
builds on `lawSub_mem_FLE`, `isHomB_lawSub`, `eval_lawSub`. α's chain will consume exactly the statements of request
(2) (`phOp_mem_vanish`, `ordGtB_of_phOp_mem_vanish`, `ordGtB_phOp`, `ordGtB_lawSub`, `ordIdealB`, `mem_ordIdealB_of`,
`IGsem_le_ordIdealB`, `ordIdealB_le_vanish`), as they now stand in `PhOpTwo.lean`/`Ord.lean`.

**α → β, 2026-10-31 (2): name clash fixed.** α's `evalLaw_smul` (in `Transl.lean`) is renamed `evalLaw_smul_hom`, so
β's `AbBlock`-form `evalLaw_smul` in `PhOpTwo.lean` keeps its name.

**α → all, 2026-10-31 (3): CR1 applied to `Stmt.lean`** (§6.5): in `MultEstB`, `n = d₀ + d₁ + Σ_k g_k` (was
`d₀ + d₁ + m`). Every `LSG.MEB` file rebuilds once; no other definition changed.

R2 verdict (β): the analytic route works in Mathlib v4.35 with a big-O calculus (`LSG/MEB/OrdAn.lean`, [Proved]): no
symmetric multilinear maps, no polarization, no formal exponential. Every law choice (even degenerate ones) is
handled by the bound `|law scalar| ≤ M` near a point, so ME's Nullstellensatz step `transl_van` is not needed.

**A5 consumer (A3 agent) → α/β/γ, 2026-10-31: how `MultEstB` is consumed** (plan: `STAGE_A5.md`).
* Only the frozen `Stmt.lean` is used; no request to change it. Instance `B = fun _ => aBlock`, `m = r`.
* Hypotheses are produced as §6.3 says: `IsHomB` and `FLE` by construction, `P ∉ IGsem` via `notMem_IGsem_of_eval_ne`,
  `OrdGtB` from `VanishAlong` of `u ↦ eval (liftB u) P` at the lift `Σ h_j y_j`.
* Fields of the output used: `Proper`, the count, `grp_eq`, `grp_sub`, `htil`, `lie`, `t_rat`. `grp_closed` is unused.
* γ: A5 assumes `aBlock.g` and `aBlock.N` reduce to `2` and `9` by `rfl` (so `Fin aBlock.g → ℂ` is `Fin 2 → ℂ`), and
  `aBlock.θ = D.thetaN`, `aBlock.per = kerE G`, `aBlock.i₀ = 4`. A5 bridges `kerE` to `latt` itself (finite index,
  `LSG/W88/AbVarPer.lean`); γ need not prove `kerE = latt`.
* β: if the subgroup layer proves the pivot lemma (STAGE_A4 §1.3) as a standalone statement about
  `t ⊆ ∏ ℂ^{g_k}` with `IsRatSub (perAb B) t` and `simple`, A5's §5d engine will import it rather than re-prove it.

**β → A5 / α, 2026-10-31: pivot lemma delivered** [Proved], `LSG/MEB/Rational.lean` (imports `Stmt` only):
```lean
theorem LSG.MEB.pivot {m : ℕ} {B : Fin m → AbBlock} {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)}
    (ht : IsRatSub (perAb B) t) :
    ∃ J : Finset (Fin m), (∀ z ∈ t, (∀ k ∈ J, z k = 0) → z = 0) ∧
      ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ t, ∀ k ∈ J, z k = y k
```
(`simple` is the `AbBlock` field, so it is not a hypothesis.) Also in the file, stable names:
`isRatSub_map` (images under `φ` with `φ(Λ) ⊆ Λ'`), `isRatSub_inf_ker` (`t ⊓ ker φ` for discrete `Λ, Λ'`),
`discreteTopology_perAb`. No clash with `LSG/W88/AbVarPer.lean` (`PerL`, `perAbL`, `IsNsmulIn`, …): checked.

**β status, 2026-10-31** (all [Proved], standard axioms, no `sorry`): `OrdAn.lean` (R2 core), `PhOpLaw.lean`
(`lawPt`, `lawSub`, `eval_lawSub`, `dblB`, `lawSub_mem_FLE`, `isHomB_lawSub`, as in request (1)), `Ord.lean`
(`OrdAt`, `ordIdealB` and its laws, `ordGtB_iff`, `mem_ordIdealB_of`, `ordGtB_of_mem_ordIdealB`, `liftOf`,
`mem_Per_of_expG_eq`), `PhOp.lean` (`phOp`, `coeff_phOp`, `eval_phOp`, `phOp_mem_FLE`, `isHomB_phOp`), `Rational.lean`.
Note `eval_phOp` is stated with `tcoef κ f = f⁽ᵏ⁾(0)/κ!`. Next: `PhOpTwo.lean` (the four lemmas of request (2)).

**β → α, 2026-10-31 (3): request (2) delivered; derivations and the word bridge delivered** (all [Proved], standard
axioms, no `sorry`):
* `PhOpTwo.lean`: `phOp_mem_vanish`, `ordGtB_of_phOp_mem_vanish`, `ordGtB_phOp`, `ordGtB_lawSub` exactly as in
  request (2) (every statement takes `hP : IsHomB P d`; `phOp_mem_vanish`/`ordGtB_phOp`/`ordGtB_lawSub` hold for
  **every** law choice). Helpers: `evalLaw_smul` (bidegree `(2,2)`), `lawPt_liftZ`, `isBigO_eval_liftZ_rel`,
  `isBigO_liftB_of_rel`.
* `Deriv.lean` (item 5 of §7.2, first half):
  - `Lk ch k = X (e k (ch k))`, `Lc ch = Π Lk`, `Lo ch k = Π_{k' ≠ k} Lk`; `DhCoef`; **`Dh ch w : Derivation ℂ
    (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ)`** (`ch : ∀ k, Fin (B k).N`, `w : Tan d₀ d₁ B`),
    `Dh_apply : Dh ch w P = ∑ v, DhCoef ch w v * pderiv v P`;
  - `isHomB_Dh : IsHomB P d → IsHomB (Dh ch w P) (d + 1)`;
  - `eval_Dh_liftB (hch : ∀ k, ch k ∈ (B k).charts) (hP : IsHomB P d) u w`: the analytic meaning (from `θ_flow`);
  - **`Dh_mem_ordIdealB (hch) (hP : IsHomB P d) (hw : w ∈ W) : P ∈ ordIdealB W (n + 1) E → Dh ch w P ∈ ordIdealB W n E`**;
  - `DhWord l P` (`l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)`, applied right to left), **`DhWord_mem_vanish
    (hl : ∀ p ∈ l, (∀ k, p.1 k ∈ (B k).charts) ∧ p.2 ∈ W) (hP : IsHomB P d) (hlen : l.length ≤ T)
    (h : P ∈ ordIdealB W T E) : DhWord l P ∈ vanish E`** (ME's `vanCan_of_ordGt`/`mem_VOg_mix` content).
  - Consequence for B7: `IGsem ≤ ordIdealB W n E` for every `n` (`IGsem_le_ordIdealB`), so every `Dh`-word maps a
    multihomogeneous element of `IGsem` into every `vanish E`.
* Not yet (β, next): `Dh_mem_FLE` (block-degree shift, ≈ 60 lines; tell β the exact form `VOg`/`WustholzGen` wants);
  Wüstholz identity data at `0` (needs `TZ ⊆ lieAlg` from the subgroup layer); the subgroup layer (§7.2 item 4).

**β → α, 2026-10-31 (4): degrees of `Dh` and StrongSix-form words; first subgroup-layer file** ([Proved], standard
axioms):
* `Deriv.lean`: `eOnes : Blk m → ℕ` (`1` on abelian blocks); **`Dh_mem_FLE : P ∈ FLE ℂ blk D → Dh ch w P ∈ FLE ℂ blk
  (D + eOnes)`** (ME's form, `ellOnes ↦ eOnes`); `Dh_eq_mkDerivation`; `Dmix p := Dh p.1 p.2`,
  `Wmix W := {p | (∀ k, p.1 k ∈ (B k).charts) ∧ p.2 ∈ W}` (ME's names); `DL_Dmix_mem_FLE : DL Dmix l P ∈ FLE (D +
  l.length • eOnes)`; **`DL_Dmix_mem_vanish (hl : ∀ p ∈ l, p ∈ Wmix W) (hP : IsHomB P d) (hlen : l.length ≤ T)
  (h : P ∈ ordIdealB W T E) : StrongSix.M2.DL Dmix l P ∈ vanish E`** (StrongSix's `DL`, first letter applied first).
* `SubgroupLie.lean` (H a Zariski-closed subgroup, `hH : IsSubgroupG H`, `hc : IsZClosed H`): `Htil hH`,
  `isClosed_Htil`, `Per_le_Htil`, `expG_eq_zero_of_mem_Per`, `expG_mem_iff` (membership via `homogVanish` at `liftB`),
  `smul_mem_Htil_of_real` (real lines are complex lines), **`lieAlg hH`** (`mem_lieAlg : v ∈ lieAlg hH ↔ ∀ c,
  expG (c • v) ∈ H`), `mem_lieAlg_iff_real`, `lieAlg_mono`; `mem_vanish_expG_image_iff`, `vanish_expG_image_isPrime`;
  **`H0 hH := zcl (expG '' lieAlg hH)`** with `H0_isSubgroup`, `isZClosed_H0`, `H0_subset`, `expG_mem_H0`,
  **`vanish_H0_isPrime`**, **`lieAlg_H0`**. These give `SubgroupData.grp_le` and `grp_prime` once `O.grp := H0 hH`.

β plan for the rest of `SubgroupData` (fields of `MainHyp.lean`; [Design]):
1. *Product decomposition* (the crux): `lieAlg hH = tanOf h0 U t` with `IsRatSub (perAb B) t`. Route: the abelian
   slice `S_A = {z | (0,0,z) ∈ Htil}` is closed and contains `perAb`, so `LSG.Subgroups.span_linPart_inter_lattice`
   (Mathlib-only, importable) gives the rational `t = linPart S_A`; `π_A(lieAlg) ⊆ t` and the linear part
   `h0 × U^⊥` need ME's trdeg count (`ProductRat`, `ProductGraph`) through the generic `LSG.ME.{SmoothPoint, DimTrdeg}`.
2. `lie`: from `lieAlg_H0`. `htil`: generic from `grp_eq` + `lie` (linear forms on `h0`, characters in `U`, and
   `LSG.Subgroups.exists_finset_cosets` on the abelian slice; W88's `htil_le_span` argument).
3. `hdim`, `cosets`, `univ_of_top`: tangent-space bound (`SmoothPoint.trdeg_le_finrank_tangentSpace`, TZ = lieAlg)
   and α's `exists_components`/`vanish_gtransl_isPrime`.
4. `coset_ge`: pivot lemma + `coords_locInv` (sliced, as ME's `hfun_P_coset_ge`).

**α → β′, 2026-10-31 (5): what α needs for Wüstholz, and what α does itself.** α will build `WustData` per coset
without ME's transport step. On each coset it pairs at a point `g` of that coset, with a chart that is nonzero at
`g`. Of §7.2 items 1–4:
* item 3 (the `ordIdealB → VOg` bridge) is β's `DL_Dmix_mem_vanish`. α extends it to non-homogeneous ideals (α shows
  `ordIdealB` is closed under multihomogeneous components);
* item 4 (`[Eul_k, Dh] = Dh`) and the linearity of `Dh ch w` in `w` are pure derivation algebra; α does them in
  `WustAlgB.lean`;
* item 2 (the translation identity) is **not needed** with per-coset pairing;
* item 1 reduces to one analytic input, the **tangent-space bound at every point of every coset**. α requests it from
  β′, in this form:
```lean
theorem tz_le_lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) (g : GPt d₀ d₁ B) (u : Tan d₀ d₁ B)
    (hu : expG d₀ d₁ B u = g) (w : Tan d₀ d₁ B)
    (h : ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomB P d →
      P ∈ vanish (gtransl g (H0 hH)) → deriv (fun r : ℂ => eval (liftB (u + r • w)) P) 0 = 0) :
    w ∈ lieAlg hH
```
  This is ME's `TZ ⊆ lieAlg` (`mem_TZ_iff`), at an arbitrary point `g` of the coset `g + H⁰`. At `g = 0` it is β's
  plan item 3 (tangent-space bound). For general `g`: replace `P` by `τ (−g) c P` (α's `transl_mem_vanish_gtransl`)
  and compare orders, `ordGtB_lawSub`/`isBigO_liftB_of_rel`-style, with good laws at `(g, −g)`.
  - **Done (α, checkpoint 2):** `SubgroupData.wust` is replaced by `tz : TZProp O` (`WustAlgB.lean`; with
    `O.grp = H0 hH` and `O.tan = lieAlg hH` it is exactly `tz_le_lieAlg`). `wust_of_tz` derives Wüstholz, and
    `multEstB_of` uses it.

**α → β′, 2026-10-31 (6): α claims `coset_ge`** (coordinator's reassignment; β's plan step 4). α works in new files
only (`LSG/MEB/CosetGe*.lean`, `HilbH0*.lean`) and does not edit `Subgroup*.lean`. Statements use `lieAlg hH` /
`H0 hH` from `SubgroupLie.lean`. β′'s product decomposition (`lieAlg hH = tanOf h0 U t`, `IsRatSub (perAb B) t`) enters
only as a hypothesis until β′ delivers it. Plan:
1. `CosetGe.lean`: the sliced bound from an unsliced lower bound for `H⁰`. That is ME's `hfun_P_coset_ge`: translate
   (`hfun_le_transl`), then slice (`hfun_le_of_hom`), with `cL = cH · nLaw B · 2^m`.
2. `HilbH0*.lean`: the unsliced lower bound `X(t) · (tD₂+1)^{t₂+m} ≤ cH · H(I(H⁰); t)`, `X(t) = (tD₀/t₀+1)^{t₀} (tD₁/t₁+1)^{t₁}`.
   Independent families on `exp(lieAlg) × ℂ^m`: coordinate monomials on `h₀`, characters on the torus part, and
   pivot-block monomials in `(X_{i₀}, X_{is})` (`coords_locInv`, β's `pivot`).
   - β′ please tell α in §7.3 the final names and shapes of the product decomposition.

   **Status (α, 2026-10-31):** step 1 is [Proved]: `CosetGe.lean`, `coset_ge_of_lower : H0LowerBound O cH → (field
   coset_ge with cL = cH · nLaw B · 2^m)`. `H0LowerBound O cH` is
   `∀ D₀ D₁ D₂ t, (t*D₀/t₀+1)^t₀ * (t*D₁/t₁+1)^t₁ * (t*D₂+1)^(t₂+m) ≤ cH * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t`,
   with `cH` depending only on `d₀ d₁ m B`.

   **Status (α′, 2026-10-31): step 2 is [Proved]**, so `coset_ge` is closed. Standard axioms only (`#print axioms` from
   a scratch file: `[propext, Classical.choice, Quot.sound]` for `h0LowerBound`, `h0LowerBound_uniform`,
   `coset_ge_of_obstr`, `eventually_lift`, `card_le_hfun_vanish`); no `sorry`/`axiom`/`native_decide`; each file built
   with `lake build LSG.MEB.<File>`. 694 lines in all (estimate was 1.5–2.5k). The bound is proved for **every**
   `O : ObstrDataB` (only `grp_eq` and `t_rat` are used), so no product-decomposition hypothesis is needed.
   * `HilbH0Aux.lean` (242): `C_mem_FLE0`, `X_mem_FLE`, `pow_mem_FLE`, `prod_mem_FLE`; **`card_le_hfun_vanish`** (a
     family in `FLE(tD)` independent modulo `I(E)` has `≤ H(I(E); t)` members); **`eq_zero_of_eventually_eval`**
     (`funext_set` on a box of balls); **`AbBlock.chartRatio`** (`θ_{is j}/θ_{i₀}`), `AbBlock.continuous_θ_apply`,
     **`AbBlock.chartRatio_image_mem_nhds`** (`coords_locInv` + `HasStrictFDerivAt.map_nhds_eq_of_equiv`);
     **`exists_mem_torusLie`** (values on coordinates independent mod `U` are attained in `U^⊥`);
     **`exists_pivot_section`** (continuous linear section of the pivot projection), **`finrank_le_pivot`**
     (`dim t ≤ Σ_{k ∈ J} g_k`).
   * `HilbH0Fam.lean` (227): `linPoly`, `eval_linPoly`, `linPoly_mem_FLE`; `pivG B J k` (`g_k` on `J`, else `0`),
     `pivM B J T k = T/(pivG+1)+1`; `HIdx`, `HCrd`; **`hPoly`** `= ∏ lp_l^{a_l} · ∏ Y_{jj k}^{b_k} · ∏_k X_{k,i₀}^{c_k}
     ∏_j X_{k,is j}^{d_kj}`; `hExp`; **`eval_hPoly`** (on a lift with coordinates `w`, `hPoly i = w^{hExp i}`),
     **`hExp_injective`**, **`hPoly_mem_FLE`**, **`card_HIdx`**; `cHB B = ∏_k (g_k+1)^{g_k+1}`, `one_le_cHB`,
     **`count_le`**.
   * `HilbH0.lean` (225): `hBase`, **`eventually_lift`** (every target point near `hBase` comes from some
     `u ∈ O.tan`, `μ`: IFT on pivot blocks, the pivot section, `exp ∘ log` on the torus, free scalings),
     `eval_monomial_fun`, **`h0LowerBound (O : ObstrDataB d₀ d₁ B) : H0LowerBound O (cHB B)`**,
     **`h0LowerBound_uniform`** (the hypothesis of β″'s `mebInputs_of_lower`), **`coset_ge_of_obstr`** (the field
     `coset_ge` for any `O`, `cL = cHB B · nLaw B · 2^m`), `cHB_nLaw_pos`.
   * Scratch check: `multEstB_of (mebInputs_of_lower h0LowerBound_uniform) : MultEstB` elaborates, axioms
     `[propext, Classical.choice, Quot.sound]` (β″'s `SubgroupMain.multEstB_holds` is the same assembly).

**β′ → α, 2026-10-31 (6): request (5) delivered; dimension theory done** ([Proved], standard axioms, no `sorry`;
each file built with `lake build LSG.MEB.<File>`):
* `SubgroupTZ.lean` (286 lines): `blkPt_lawPt`, `blkPt_coords_one`, **`ordGtB_of_lawSub`** (converse of
  `ordGtB_lawSub` for a good law), `eval_liftB_eq_zero_of_mem_vanish`, `mem_vanish_of_liftB`,
  `isHomB_of_mem_homogVanish`, `dirD P u w := deriv (r ↦ P(liftB (u + r w))) 0`, `ordGtB_span_iff`,
  `gtransl_self_of_mem`, **`ordGtB_one_of_one`**, **`ordGtB_one_of_coset`**, `Dh_mem_vanish_of_dirD`, `lineW`,
  `exists_chart_zero`, `lineW_isBigO`, **`mem_lieAlg_of_dirD`**, **`mem_lieAlg_of_ordGtB`** (ME's `TZ ⊆ lieAlg`; no
  Euler correction is needed since `eval_Dh_liftB` holds at every lift).
* `SubgroupImm.lean` (280 lines): **`AbBlock.fderiv_inj`** (`θ` is a projective immersion everywhere: `coords_locInv` at
  `0`, law translation elsewhere), `dLZ u μ w σ` (derivative of `r ↦ liftZ (u + r w) (μ + r σ)`), `dLZl`,
  **`dLZl_injective`** (nonzero scalings), `tangent_of_curve`, **`dLZ_mem_tangentSpace`**, `tangentSpace_anti`,
  **`dirD_eq_zero_of_tangent`** (`LSG.ME.tangentSpace` = Zariski tangent space of the affine cone).
* `SubgroupDim.lean` (278 lines): `ordGtB_span_of_dirD`, `mem_lieAlg_of_coset`, **`tz_le_lieAlg`** (exactly the
  statement of request (5)), `finrank_Tan`, `exists_smooth_G`, `tangentSpace_IGsem_eq`, `tangent_coset_le_map`,
  **`hdim_le_of_subset`** (`hdim I(Y) ≤ dim lieAlg H + m`, `Y ⊆ H` irreducible nonempty), **`le_hdim_H0`**,
  **`hdim_H0`** (`hdim I(H⁰) = dim lieAlg H + m`), `coset_eq_of_le`, **`finite_cosets_H0`** (representatives in `H`).
  No homogeneity argument: everything is computed at one smooth point of the cone of `G` (SmoothPoint + α's
  `hdim_IGsem_le`), and irreducible `Y ⊆ H` are translated to pass through it.
* With `O.grp = H0 hH` and `O.tan = lieAlg hH` these give the fields `grp_le` (`H0_subset`), `cosets`
  (`finite_cosets_H0`), `hdim` (`hdim_H0`) and `tz` (`tz_le_lieAlg`). Still missing for `SubgroupData` (β′, next):
  the product decomposition `lieAlg hH = tanOf h0 U t` with `IsRatSub (perAb B) t` (port of ME `ProductRat` +
  `ProductGraph`, now possible with `hdim_H0`/`hdim_le_of_subset` in place of `trdeg_H0`), then `lie` (from
  `lieAlg_H0`) and `htil`, then the constructor `SubgroupData.ofSubgroup` (minus α's `coset_ge`).

**β′ checkpoint 2, 2026-10-31: product decomposition step 1 done; continuation plan** ([Proved], standard axioms,
`#print axioms` from a scratch file: `[propext, Classical.choice, Quot.sound]` for `tz_le_lieAlg`, `hdim_H0`,
`finite_cosets_H0`, `hdim_le_of_subset`, `isRatSub_map_piA`, `lieAlg_zcl_map_piA`, `mem_lieAlg_of_ordGtB`,
`AbBlock.fderiv_inj`; no `sorry`/`axiom`/`native_decide`):
* `SubgroupRat.lean` (275 lines; imports `SubgroupDim`, `Rational`, `LSG.ME.ProductRat` for the generic
  `eq_zero_of_eval_elim`/`card_le_trdeg_of_indep`/`exists_coord_surj`, `LSG.Subgroups.TorusLattice`): `piA`, `inAbL`
  (`inAbL_apply : inAbL z = (0, 0, z)`), `inAbL_injective`, `rhoL`, `varL`, `span_perAb`, **`isRatSub_of_linPart`**
  (a complex `t` with `z ∈ t ↔ ∀ s : ℝ, s • z ∈ S`, `S` closed `⊇ perAb`, is rational), **`lieAlg_zcl_map_piA`**
  (`map inAbL (map piA (lieAlg hH)) = lieAlg (zcl (exp ⋯))`, ME's trdeg count with `hdim_H0`), **`isRatSub_map_piA`**
  (`IsRatSub (perAb B) ((lieAlg hH).map piA)`).

**Continuation plan (for β′ or a successor), in order** [Design]:
1. `SubgroupGraph.lean`: port ME `ProductGraph.lean` (347 lines) with `Ls → B`, `expE → QuotientAddGroup.mk`,
   `(Ls k).lattice → (B k).per`, `isAbelianTangent_map_piA → isRatSub_map_piA` (use `IsRatSub`: `t.restrictScalars ℝ =
   span ℝ {z ∈ t ∩ Λ}`, so a real-linear form vanishing on `t ∩ perAb` vanishes on `t`), `lieAlg Ls hH hc → lieAlg hH`.
   Pieces: `eq_zero_of_lattice` (a `ℂ`-linear `f` on `lieAlg` vanishing on `lieAlg ⊓ ker piA` with `Re f = 0` at the
   `u` with `piA u ∈ perAb` vanishes); `inLpt : StrongSix.Thm1.GPt ℂ d₀ d₁ → GPt d₀ d₁ B` (`(a, y, 0)`); `ML hH :=
   {g | inLpt g ∈ H0 hH}`; `ML_isSubgroup`; `substL lam` (block variables `e k c ↦ C (lam k * rep 0 c)`),
   `eval_substL`, `ML_eq_zeros` (Zariski closed in StrongSix's sense), `ML_eq_prodSet` (StrongSix `classify`:
   `ML = prodSet V Λ`); `linExp`, `chr_linExp`, `expG_eq_inLpt` (for `piA u ∈ perAb`), `linExp_mem_ML`,
   `mem_lieAlg_of_linExp`, `phiL`, `eq_zero_of_forall_exp`, `linPart_mem`, `mem_lieAlg_of_linV`,
   `mem_torusLie_qspan`, **`mem_lieAlg_iff`**, **`lieAlg_projL_mem`** (`π_L(lieAlg) ⊆ lieAlg`), `linV_ML_eq`,
   **`lieAlg_eq_prod`**: `lieAlg hH = tanOf V (qspan Λ) t` with `t := (lieAlg hH).comap inAbL` (`= map piA` by
   `lieAlg_projL_mem`, so `IsRatSub` by `isRatSub_map_piA`). Skip ME's `exists_subgroupData*` and the `ℚ̄` part
   (`ObstrDataB` has no rationality condition on `h0`).
2. `SubgroupHtil.lean`: port W88 `Sec7Count.htil_le_span` (`LSG/W88/Sec7Count.lean` l. 150–260) to
   `htil : expG u ∈ H0 hH → ∃ N > 0, N • u ∈ (tanOf h0 U t).toAddSubgroup ⊔ Per`. Route: `H0` is `exp(tan)` up to
   finite index on the abelian slice: linear forms vanishing on `h0` kill `u.1` (the additive coordinates of `H0`
   lie in `V`, from `ML`/`classify`); characters `φ ∈ U` give `Σ φ_j u_{1j} ∈ 2πiℤ` after subtracting a `tan`-vector;
   for the abelian part use `LSG.Subgroups.exists_finset_cosets` on the closed subgroup `(Htil (H0 hH)).comap inAbL`
   (contains `perAb`, linear part `t`): finitely many cosets of `t + perAb`, so a multiple lies in `t + perAb`.
3. `SubgroupData.lean`: `ObstrDataB.ofSubgroup hH hc` with `h0, U, t` from `lieAlg_eq_prod`, `t_rat` from
   `isRatSub_map_piA`, `grp := H0 hH`, `grp_eq` (`H0 = zcl (exp (lieAlg hH))` and `lieAlg_eq_prod`), `grp_sub :=
   H0_isSubgroup`, `grp_closed := isZClosed_H0`, `lie` (from `lieAlg_H0` + `lieAlg_eq_prod`: `∀ c, exp (c v) ∈ H0 ↔
   v ∈ lieAlg (H0) = lieAlg hH`), `htil` (step 2). Then the `SubgroupData` fields: `grp_le := H0_subset hH hc`,
   `cosets := finite_cosets_H0 hH hc`, `hdim := hdim_H0 hH hc` (rewrite `O.tan = lieAlg hH`), `tz := tz_le_lieAlg hH hc`
   (unfold `TZProp`, rewrite `O.grp`, `O.tan`); `coset_ge` is α's.

**β″ → α′/all, 2026-10-31 (7): β′'s continuation plan is done; `MEBInputs` and `MultEstB` are proved** ([Proved];
standard axioms only, `#print axioms` from a scratch file gives `[propext, Classical.choice, Quot.sound]` for every
name below; no `sorry`/`axiom`/`native_decide`; each file built with `lake build LSG.MEB.<File>`):
* `SubgroupGraph.lean` (305 lines; imports `SubgroupRat`, `LSG.ME.ProductGraph` for the generic
  `mem_torusLie_qspan`/`eq_zero_of_forall_exp`): `eq_zero_of_lattice` (via `isRatSub_map_piA`), `inLpt`, `ML hH`,
  `ML_isSubgroup`, `substL`, `eval_substL`, `ML_eq_zeros`, `ML_eq_prodSet` (StrongSix `classify`), `linExp`,
  `chr_linExp`, `expG_eq_inLpt`, `linExp_mem_ML`, `mem_lieAlg_of_linExp`, `phiL`, `linPart_mem`,
  `mem_lieAlg_of_linV`, **`mem_lieAlg_iff`**, **`lieAlg_projL_mem`**, `linV_ML_eq`. **Stable names of the product
  decomposition** (for α′; `H` Zariski closed, `hH : IsSubgroupG H`, `hc : IsZClosed H`):
  - `h0Of hH : Submodule ℂ (Fin d₀ → ℂ) := (lieAlg hH).comap (LinearMap.inl ..)` (`mem_h0Of : a ∈ h0Of hH ↔ (a, 0, 0) ∈ lieAlg hH`, `Iff.rfl`);
  - `UOf hH : Submodule ℚ (Fin d₁ → ℚ) := qspan (latt (ML hH))`;
  - `tOf hH := (lieAlg hH).comap inAbL` (`mem_tOf : z ∈ tOf hH ↔ (0, 0, z) ∈ lieAlg hH`, `Iff.rfl`);
  - **`lieAlg_eq_tanOf hH hc : lieAlg hH = tanOf (h0Of hH) (UOf hH) (tOf hH)`**; `tOf_eq_map_piA hH hc : tOf hH =
    (lieAlg hH).map piA`; **`isRatSub_tOf hH hc : IsRatSub (perAb B) (tOf hH)`**.
* `SubgroupHtil.lean` (200 lines; imports `LSG.W88.Sec7Count` for the generic `exists_rat_torus`,
  `coe_pow_toNat_mul`): `eval_zcl_expG`, `fst_mem_of_zcl`, `chr_eq_one_of_zcl`, `exists_nsmul_abB`
  (`LSG.Subgroups.exists_finset_cosets` on `exp⁻¹(G′) ∩ (0 × 0 × ℂ^g)`), `natAbs_smul_mem`, **`htil_of_zcl`**: for
  `G′ = zcl (exp (tanOf h0 U t))` with `inAbL z ∈ lieAlg G′ ↔ z ∈ t`, `exp u ∈ G′ → ∃ N > 0, N • u ∈ tanOf h0 U t + Per`
  (exactly the field `ObstrDataB.htil`).
* `SubgroupData.lean` (121 lines): `H0_eq_zcl_tanOf`, `lieAlg_H0_eq_tanOf`, **`ObstrDataB.ofSubgroup hH hc`**
  (`h0Of/UOf/tOf`, `grp = H0 hH`; all fields incl. `t_rat`, `lie`, `htil`), simp lemmas `ofSubgroup_grp/_h0/_U/_t`,
  **`ofSubgroup_tan : (ofSubgroup hH hc).tan = lieAlg hH`**, `ofSubgroup_tz`, `ofSubgroup_hdim`; `CosetGeB O cL` (the
  statement of the field `coset_ge`); **`SubgroupData.ofSubgroup hH hc (hcg : CosetGeB (ObstrDataB.ofSubgroup hH hc)
  cL)`** (every field except `coset_ge` built here), **`SubgroupData.ofLower hH hc (hlow : H0LowerBound _ cH) :
  SubgroupData d₀ d₁ B (cH * nLaw B * 2 ^ m) H`**, **`mebInputs_of_lower`** (`MEBInputs` from `∃ cH > 0, ∀ O,
  H0LowerBound O cH` for each `B`).
* `SubgroupMain.lean` (29 lines; imports `SubgroupData`, α′'s `HilbH0`, α's `Main`): **`mebInputs : MEBInputs`**
  (`mebInputs_of_lower` with α′'s `h0LowerBound`, `one_le_cHB`; `cL = cHB B · nLaw B · 2^m`) and
  **`multEstB_holds : MultEstB := multEstB_of mebInputs`**. Both `[propext, Classical.choice, Quot.sound]`.
* Not done here: `LSG.lean`/`Axioms.lean` do not yet import `SubgroupMain` (coordinator's files); nothing else is
  open for A4.3/A4.5.

---------------------------------------------------------------------------------------------------------------------

## 8. A4.1b `surj`: delivered (A3 agent, 2026-10-31)

**Theorem** (`LSG/JacAn4/Surj.lean`; standard axioms plus `A1Facts` and `SurjFacts`):

```
LSG.JacAn.ThetaData.surjA {A : A1Facts} (SF : SurjFacts A) {B₁ B₂ p hp hx} {G : GermRad A hp hx}
    (D : ThetaData G) : ∀ X : P9, X ≠ 0 → A.OnQ X → ∃ z : Fin 2 → ℂ, ∃ c : ℂ, X = c • D.thetaN z
```

`P9 = Fin 9 → ℂ`.

**Match with the frozen field.** `AbBlock.surj : ∀ X : Fin N → ℂ, X ≠ 0 → (∀ Q ∈ gens, eval X Q = 0) →
∃ z, ∃ c : ℂ, X = c • θ z`, with `g = 2`, `N = 9` and `θ := D.thetaN`. The conclusion and the binder order match
exactly. The only conversion is the hypothesis: γ must supply `(∀ Q ∈ gens, eval X Q = 0) → A.OnQ X`.

**How γ converts `gens` to `OnQ` (choose one).**
1. **Through `SurjFacts.gensI`.** If `gensA : List (MvPolynomial (Fin 9) ℂ)` is the list of the 12 generators with
   `eval X (gensA.get i) = SF.gensI i X`, then `(∀ Q ∈ gensA, eval X Q = 0) → ∀ i, SF.gensI i X = 0`, and
   `SF.gensI_iff` turns this into `A.OnQ X`. This is the natural route, since γ discharges `gensI` itself.
2. **Through the quadrics.** With `A1FactsInst`, `A.OnQ = LSG.Jac.OnQ`, and A1's `onQ_iff` gives
   `OnQ X ↔ ∀ j, quad X j = 0`. The 9 quadrics are the first 9 entries of `gens`; the 3 cubics are not needed for this
   direction.

The instance field is then
`surj := fun X hX hgens => D.surjA SF X hX (hconv X hgens)`.
* `θ_model` is the converse direction: `OnQ (θ_N z)` is `ThetaData.thetaN_onQ`, plus `OnQ → gens` (again
  `gensI_iff`).
* The cubics' vanishing on `V(Q)` is part of `gensI_iff`.

**Inputs still to be discharged by γ.** `SurjFacts` (`LSG/JacAn4/SurjFacts.lean`): `affine_chart`, `anchor`, `gensI`
with `gensI_diff`, `gensI_iff`, `tanC4/8` with `_cont`, `gensI_tan4/8`, and `exit4/8`. The forms are those of
STAGE_A1's request section. Explicit-polynomial variants of the exit words are acceptable, and I will adapt
`FlowExit.lean`.

**Proof outline** (STAGE_A3 §11): closedness of the cone (`Closed`); path-connectedness of the generic locus
(`CurveConn`); `follow_par` with the anchor (`Generic`, `Anchor`); chart points including the non-generic ones, by
explicit perturbation (`Affine.chart_mem`); boundary flow exit (`ExitTaylor`, `FlowExit`); base independence
(`Surj.imgCone_transfer`).
