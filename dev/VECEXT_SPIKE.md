# VECEXT spike: a model of `E^♮` with complete addition laws (risk 1 of VECEXT.md)

Written 2026-10-31. Labels: [Lean] proved in Lean (standard axioms), [CAS] exact computer algebra (sympy /
python-flint), [Proof sketch], [Numerical] (exact linear algebra over `F_p` for random curves), [Design].

## 0. Verdict

**Risk 1 is resolved, with one correction to VECEXT §3.2: the laws have bidegree `(3, 3)`, not `(2, 2)`.**

* The proposed model `X = V(F, G) ⊂ ℙ⁴`, coordinates `(U, V, W, T₁, T₃)`, `G = W T₃ − V T₁ + 2U²`, is correct:
  a complete intersection surface of degree 6 whose points with `(U, V, W) ≠ 0` are exactly `E^♮` [Lean
  `eq_ptAff_or_ptO`], plus a boundary line `L = {U = V = W = 0}` in the closure [Proof sketch]. The ideal is prime
  [Proof sketch, §2.3].
* **There is no addition law of bidegree `(2, 2)` at all on this model** [Numerical: the space of `(2, 2)` laws is 0,
  two random curves over `F_p`, §4.3]. The reason is the one missing section `T₂ = U·t` (§2.4).
* **Eight laws of bidegree `(3, 3)`** (`NLaw i j k`: `E`-law `law₁`/`law₂` × multipliers `λ(P), μ(Q) ∈ {V, W}`)
  form a complete system [Lean]:
  (a) they preserve the ideal: `F(A), G(A) ∈ (F(P), G(P), F(Q), G(Q))`, as polynomial identities over any
  commutative ring (`NLaw_mem`);
  (b) at every pair of points of `E^♮` each law is a multiple of the sum, in all six configurations (generic,
  doubling, opposite points, points over `O`), algebraically over any field of characteristic 0
  (`NLaw_ptAff`, `NLaw_dbl`, `NLaw_neg`, `NLaw_ptO_left/right`, `NLaw_ptO_ptO`) and analytically for **all**
  `(z₁, w₁), (z₂, w₂) ∈ ℂ²`: `NLaw(exp(z₁,w₁), exp(z₂,w₂)) = c • exp(z₁+z₂, w₁+w₂)` (`NLaw_expN_all`);
  (c) at every pair of points some law is nonzero (`NLaw_complete`).
* The laws are affine-linear in the fibre coordinates and commute with fibre translations (`NLaw_fib_left/right`).
* Impact on the multiplicity-estimate plan (§7): Philippon's constant is `c₁ = 3` for `E^♮`-blocks (vs 2 for `E`):
  constants only. Nothing else in VECEXT §3.2 changes; several steps get easier.

## 1. Conventions

`E : V²W = 4U³ − g₂UW² − g₃W³` (`F`, as in `AdditionLaws.lean`; affine `y² = 4x³ − g₂x − g₃`, `x = ℘`, `y = ℘'`).
Following VECEXT §1.1, `exp(z, w) = (exp_E z, w − ζ(z))`, so a point of `E^♮` is `(P, t)` with `t = w − ζ(z)`. Then
`(P₁, t₁) + (P₂, t₂) = (P₁ + P₂, t₁ + t₂ − c(P₁, P₂))`, `c = ζ(z₁+z₂) − ζ(z₁) − ζ(z₂) = ½ (y₁ − y₂)/(x₁ − x₂)`.
(The task statement wrote `+ c`; that is the convention `t = ζ(z) − w`. Nothing below depends on the choice.)

**ζ addition formula** [Lean `zeta_add_formula`]: for `u, v, u ± v ∉ Λ`,
`ζ(u+v) − ζ(u) − ζ(v) = ½ (℘'(u) − ℘'(v))/(℘(u) − ℘(v))`.
Proof (no Laurent expansions): the defect `h(u, v)` has `∂_u h = 0` on `S_v = {u : u, u+v, u−v ∉ Λ}` (from `ζ' = −℘`,
`weierstrassP_add` and `℘'² = 4℘³ − g₂℘ − g₃`); `S_v` is connected (complement of a countable set), so `h(·, v)` is
constant there. Symmetry and oddness give `h(u,v) = h(−u,v) = h(v,−u) = h(−v,−u) = h(−u,−v) = −h(u,v)`.

## 2. The model

### 2.1 What `T₁, T₃` are
All five coordinates are sections of `π^*O_E(3·O)` on `E^♮` (`π : E^♮ → E`) of fibre degree ≤ 1:
over an affine point, `(U : V : W : T₁ : T₃) = (x : y : 1 : t : y t − 2x²)` (`ptAff x y t`), i.e.
`T₁ = W t`, `T₃ = V t − 2U²/W`. At `O`, with the trivialisation `σ³ ~ z³`: `U ~ z`, `V ~ −2`, `W ~ z³`,
`T₁ ~ z³(w − 1/z) → 0`, `T₃ = −2w + O(z³)`, so the fibre over `O` is `(0 : 1 : 0 : 0 : w')` (`ptO w'`) with
`w' = T₃/V = lim (t − 2x²/y)`. Analytically `w' = w − ζ(λ)` at `z = λ ∈ Λ` (Lean's `ζ(λ) = η(λ)`); this is
`expN` in `NaturalGroup.lean`. The pole of `t` at `O` (simple) cancels against the zero of `W` (order 3) in `T₁`,
and against `2U²/W` (simple pole) in `T₃`: `t − 2x²/y = w + O(z³)`.

### 2.2 Points [Lean]
* `Fn_ptAff`, `Gn_ptAff`, `Fn_ptO`, `Gn_ptO`: the points lie on `X`.
* `eq_ptAff_or_ptO` (field, `2 ≠ 0`): a vector with `F = G = 0` and `(U, V, W) ≠ 0` is `W • ptAff(U/W, V/W, T₁/W)`
  (with `(U/W, V/W)` on `E`) if `W ≠ 0`, and `V • ptO(T₃/V)` if `W = 0`. With `ptAff_injective`, `ptO_injective`,
  `ptAff_ne_smul_ptO`: **`X ∖ L` is exactly `E^♮`**, `L = {U = V = W = 0}` (a line; `F` and `G` vanish on it).
* Fibre translation is linear: `ptAff x y (t+v) = ptAff x y t + v·(0,0,0,1,y)`, `ptO(w+v) = ptO w + v·(0,0,0,0,1)`,
  i.e. `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV` (`ptAff_add_fib`, `ptO_add_fib`), as VECEXT §3.2 says.
* Slices: `W(T₃ + αT₁) + 2U² = (V + αW) T₁ + G` (`slice_rel`): on `ℓ = V + αW = 1`, `T₁ = W t′ + 2U²`,
  `t′ = T₃ + αT₁`, so the slice ring is `(sliced E ring)[t′]` (VECEXT §3.2 confirmed).

### 2.3 Geometry [Proof sketch]
* `dim X = 2`: over each point of `E` with `(V, W) ≠ 0` the equation `G` is a nonzero linear form in `(T₁, T₃)`.
* `L ⊂ closure(E^♮)`: `(x : y : 1 : t : yt − 2x²) → (0 : 0 : 0 : 1 : y)` as `t → ∞`; every `y ∈ ℂ` and `y = ∞`
  (`ptO(w)`, `w → ∞`) occur. So `X = closure(E^♮)` is irreducible and `E^♮ = X ∖ L` is open dense.
* `J = (F, G)` is prime: a complete intersection (codim 2, two equations) is unmixed; `X` is irreducible; `J` is
  reduced at a smooth point of `E^♮` (Jacobian of `(F, G)` has rank 2 there: `∇F ≠ 0` on `E`, `∂G/∂T₃ = W`,
  `∂G/∂T₁ = −V`). Unmixed + generically reduced + irreducible ⇒ prime.
* Hilbert function `H_X(D) = C(D+4,4) − C(D+2,4) − C(D+1,4) + C(D−1,4) = 3D² + 2` (`D ≥ 1`); degree 6.

### 2.4 Relation to the complete linear system, and why `(2, 2)` fails
The space of sections of `π^*O(3·O)` of fibre degree ≤ 1 is `H⁰(E, F₂ ⊗ O(3·O))`, `F₂` Atiyah's rank-2
bundle: dimension 6, basis `(U, V, W, T₁, T₂, T₃)` with **`T₂ = U t`** (regular at `O`: `U t ~ z·(−1/z)`).
It embeds `E^♮ ⊂ X̃ = ℙ(F₂) ⊂ ℙ⁵` (`C₀ + 3f` is very ample on the ruled surface `ℙ(F₂)`, `e = 0`); `X̃` is smooth of
degree 6 with boundary `C₀ ≅ E` a plane cubic in `U = V = W = 0`. VECEXT's `X` is the projection of `X̃` from a point
of that plane: `C₀ → L` is the 3 : 1 map `P ↦ (1 : y_P)`; `X` is not normal along `L`, harmless since `L ∩ E^♮ = ∅`.
Ideal of `X̃` in degree 2: `G₁ = UT₁ − WT₂`, `G₂ = G`, `G₃ = UT₃ − VT₂ + ½(V² + g₂UW + g₃W²)` (not a complete
intersection).

Why `(2, 2)` fails on `X`: a law is `A = s · m^*(X)` with `A_{T₁} = A_W · t₃`. For `s` of fibre degree 0 the
`t₁`-coefficient of `A_{T₁}` is the `E`-law component `lawW(P, Q)`, a quadric in `(U₁, V₁, W₁)`; in degree 2 the
`t`-coefficients available on `X` are `(V, W)·H⁰(O(3·O)) = span(UW, UV, VW, V², W²)`, missing `U²` (Koszul:
`H⁰(L) ⊕ H⁰(L) → H⁰(L²)` has cokernel `H¹(O_E) ≠ 0`), and `law₁W ∋ −12U₁²U₂W₂`. In degree 3 the cokernel is
`H¹(O(3·O)) = 0`, so every fibre-degree-1 section is available: multiplying by `λ(P) μ(Q)`, `λ, μ ∈ {V, W}`, makes
everything representable without `T₂` (`W T₂ = U T₁`, `V T₂ = U T₃ + ½(V² + g₂UW + g₃W²)`). The general statement
(laws with `T`-dependent `s` included) is the [Numerical] count of §4.3.

## 3. The eight laws

For `i ∈ {1, 2}`, `λ, μ ∈ {V, W}` (Lean index `0 ↦ V`, `1 ↦ W`), with `(lU, lV, lW) = lawᵢ(P, Q)` (bidegree
`(2,2)`, `AdditionLaws.lean`), `M = λ(P)μ(Q)`, `T_V = T₃`, `T_W = T₁`:
```
A^{(i,λ,μ)}(P, Q) = ( 2M lU, 2M lV, 2M lW,
                      2μ(Q) lW T_λ(P) + 2λ(P) lW T_μ(Q) − κᵂ_{iλμ}(P, Q),
                      2μ(Q) lV T_λ(P) + 2λ(P) lV T_μ(Q) − κⱽ_{iλμ}(P, Q) )
```
* `κᵂ, κⱽ`: bidegree `(3, 3)` forms in the `E`-variables only, integer coefficients, 6–30 terms each
  (`NaturalLawsPoly.lean`, `kapWᵢλμ`, `kapVᵢλμ`). On `E × E` they are determined by
  `κᵂ = M lW m − 2μ lW ρ_λ − 2λ lW ρ_μ`, `κⱽ = M(lV m + 4lU²/lW) − 2μ lV ρ_λ − 2λ lV ρ_μ`,
  `m = (y₁−y₂)/(x₁−x₂)`, `ρ_V = 2U²/W`, `ρ_W = 0` (`λ t = T_λ + ρ_λ`), i.e. `A_{T₁} = A_W t₃`, `A_{T₃} = A_W(y₃t₃ − 2x₃²)`.
  Example: `κᵂ_{1WW} = 4(U₁W₂ − U₂W₁)²(V₁W₂ − V₂W₁)` (affine `4(x₁−x₂)²(y₁−y₂)`, `law₁W = 4(x₁−x₂)³`).
* Bihomogeneous of bidegree `(3, 3)` (`NLaw_smul`), affine-linear in the `T`'s, vanishing when `(U,V,W)(P) = 0`
  (`NLaw_zero_of_base`).
* Linear combinations: every law here is `s·m^*X` with `s = 2λ(P)μ(Q)·lawᵢ/m^*(U,V,W)`, so any linear combination of
  the eight is again a law; in particular `λ, μ` may be any forms in `span(V, W)` (e.g. `λ = μ = ℓ = V + αW`, natural
  on the slice `ℓ = 1`, where `T_ℓ = t′`) [Proof sketch].

## 4. Certificates

### 4.1 (a) law preservation [Lean `NLaw_mem`, any commutative ring]
* `F(A_U, A_V, A_W) = (2M)³ F(lawᵢ) ∈ (F(P), F(Q))` (`Fn_NLaw` + `Fv_lawᵢ_mem`).
* `G(A) = 2M·Φ`, `Φ = lV κᵂ − lW κⱽ + 4M lU²`: **the `T`-terms cancel identically** (`G_law_shape`, a 9-atom
  `ring` identity). `Φ` is a bidegree `(5,5)` form in the `E`-variables with
  `Φ = q₁ F(P) + q₂ F(Q)`, explicit integer cofactors (12–31 terms; `phiᵢλμ`, eight identities, `Φ` up to 156 terms),
  found by division with respect to `U₁³`, `U₂³` (the leading terms of `F(P)`, `F(Q)` in lex order are coprime, so
  `{F(P), F(Q)}` is a Gröbner basis and division is a membership test).
  So `G(A)` even lies in `(F(P), F(Q))`.

### 4.2 (b) group law, all configurations [Lean]
Points: `ptAff x y t` (affine base) and `ptO w` (over `O`); each case is an exact identity
`NLaw(P̂, Q̂) = (one component of NLaw) • (sum)`:

| case | sum | theorem | field |
|---|---|---|---|
| `x₁ ≠ x₂` | `(x₃, y₃, t₁+t₂ − m/2)`, chord | `NLaw_ptAff` | char 0 |
| `P = Q`, `y ≠ 0` | `(x(2P), y(2P), t₁+t₂ − m/2)`, `m = (12x²−g₂)/(2y)` | `NLaw_dbl` | char 0 |
| `Q = −P` | `ptO(t₁ + t₂)` | `NLaw_neg` | comm. ring |
| `(O, w) + (x, y, t)` | `(x, y, t + w)` | `NLaw_ptO_left` | comm. ring |
| `(x, y, t) + (O, w)` | `(x, y, t + w)` | `NLaw_ptO_right` | comm. ring |
| `(O, w₁) + (O, w₂)` | `ptO(w₁ + w₂)` | `NLaw_ptO_ptO` | comm. ring |

By `eq_ptAff_or_ptO` and `NLaw_smul` every pair of points of `E^♮` is one of these. Each case reduces, through a
"shape lemma" (`shape_ptAff`, `shape_gen`, `shape_Oleft`, …: pure field algebra), to identities for the values of
`lawᵢ` and `κ` at the configuration modulo the curve equation: 20 affine identities (`NaturalLawsAff.lean`) and 106
special-configuration identities (`NaturalLawsSpecial.lean`), all with sympy-generated cofactors.
Analytic form: `NLaw_expN` (`z₁, z₂, z₁ ± z₂ ∉ Λ`, from `NLaw_ptAff`, `weierstrassP_add`, `derivWeierstrassP_add`,
`zeta_add_formula`), `NLaw_expN_of_add` (doubling included, by continuity in `z₂`), and **`NLaw_expN_all`**: for all
`(z₁, w₁), (z₂, w₂)`, `∃ c, NLaw(expN z₁ w₁, expN z₂ w₂) = c • expN(z₁+z₂, w₁+w₂)` (cases over `O` via `zeta_add`,
`ζ(λ) = η(λ)`, periodicity of `℘, ℘'`). So the table *is* the group law of `E^♮` transported by `exp`.

### 4.3 Dimension counts [Numerical: exact rank over `F_p`, `p = 10⁹+7`, random `g₂, g₃`, random points]
`lawdim.py`: laws = tuples of bidegree-`(c,c)` forms with `A_j = A_W·X_j(P+Q)` on `E^♮ × E^♮`.

| model | `c` | `dim R_c` | dim of law space |
|---|---|---|---|
| 5 coordinates (`X`, VECEXT) | 2 | 14 | **0** (two curves) |
| 5 coordinates | 3 | 29 | 31 |
| 6 coordinates (`X̃`, with `T₂`) | 2 | 18 | 6 (= `h⁰(O_X̃(1))`, Lange–Ruppert-type correspondence) |

(A zero nullspace of the evaluation system over `F_p` proves there are no `(2,2)` laws for that curve over `F_p`; it
indicates the same for generic curves in characteristic 0.)

### 4.4 (c) completeness [Lean `NLaw_complete`, field with `2 ≠ 0`, `Δ ≠ 0`]
For `P, Q` with `F = 0` and `(U,V,W) ≠ 0`: pick `i` with `lawᵢ(P,Q) ≠ 0` (`law_complete`) and `λ, μ ∈ {V, W}` nonzero
at `P`, `Q` (`V = W = 0` forces `U = 0` on `E`); then the base part `2M·lawᵢ ≠ 0`. `toPoint_NLaw`: the base part of a
nonzero law represents the Mathlib sum `P + Q`.

## 5. Lean files (namespace `LSG.Elliptic`; not imported by `LSG.lean`; build with `lake build LSG.Elliptic.NaturalGroupFull`)

| file | lines | content |
|---|---|---|
| `LSG/Elliptic/NaturalZeta.lean` | 176 | `zeta_add_formula`, `zeta_add_eq` |
| `LSG/Elliptic/NaturalModel.lean` | 195 | `Gfib`, `Fn`, `Gn`, `Inat`, `ptAff`, `ptO`, `eq_ptAff_or_ptO`, fibre translation, `slice_rel`, `G_law_shape` |
| `LSG/Elliptic/NaturalLawsPoly.lean` | 398 | 16 `κ` definitions, 8 `Φ` identities (generated) |
| `LSG/Elliptic/NaturalLaws.lean` | 235 | `NLaw`, `phi_eq`, **`NLaw_mem` (a)**, `NLaw_smul`, `NLaw_zero_of_base`, `NLaw_fib_left/right` |
| `LSG/Elliptic/NaturalLawsAff.lean` | 451 | 20 affine identities for the generic case (generated) |
| `LSG/Elliptic/NaturalGroup.lean` | 326 | `NLaw_ptAff`, `expN`, `NLaw_expN`, `NLaw_expN_of_add`, **`NLaw_complete` (c)**, `toPoint_NLaw` |
| `LSG/Elliptic/NaturalLawsSpecial.lean` | 731 | 106 special-configuration identities (generated) |
| `LSG/Elliptic/NaturalGroupFull.lean` | 375 | `NLaw_ptO_left/right`, `NLaw_ptO_ptO`, `NLaw_neg`, `NLaw_dbl`, **`NLaw_expN_all` (b)** |

No `sorry`, `axiom`, `native_decide`; every listed theorem: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
All files compile without warnings. Cold compile ≈ 3 min (the `Φ` identities ≈ 45 s).

Generators (`scripts/vecext_spike/`, run in this order from that folder; sympy + python-flint):
`kappa.py` (solves for `κ`, weighted ansatz, exact `fmpq` linear algebra) → `verify5.py` (checks `G(A) = 2MΦ`,
divides `Φ` by `F(P), F(Q)`, checks the generic (b) identities) → `affine_ids.py` → `gen_lean.py OUTDIR`
(writes `NaturalLawsPoly.lean`, `NaturalLawsAff.lean`) → `gen_special.py OUTDIR` (`NaturalLawsSpecial.lean`);
`lawdim.py model c [seed]` for §4.3.

## 6. Alternatives considered
* **6-coordinate model `X̃ ⊂ ℙ⁵`** (`T₂ = U t` added): `(2, 2)` laws exist (6-dim space; e.g. `s = lawᵢ`,
  components `(lawᵢ, lawᵢW t₃, lawᵢU t₃, lawᵢV t₃ − 2lawᵢU²/lawᵢW)`), so `c₁ = 2`. But `X̃` is not a complete
  intersection (degree-6 surface spanning `ℙ⁵`), `V(F, G₁, G₂, G₃)` contains the spurious plane `U = V = W = 0`, and
  law preservation needs the full ideal (cubic generators). On slices it is a CI after eliminating `T₂` (a degree-2
  relation, which distorts the degree filtration by a factor ≤ 2). Not recommended: `X` with `c₁ = 3` is simpler.
* **`ℙ² × ℙ¹` with fibre coordinate `(W : T₁) = (1 : t)`**: not an embedding (the whole fibre over `O` maps to `t = ∞`).
  Any embedding needs a fibre coordinate that is a section of `π^*O(n·O)`, which is what `T₁, T₃` are.

## 7. Impact on the multiplicity-estimate plan (VECEXT §3.2, STAGE2 §3, §10, §11)
1. **`c₁ = 3` for `E^♮` blocks.** Translation `τ_g` multiplies the `E^♮`-block degree by 3 (STAGE2's `E`-blocks: 2);
   Philippon's operator `δ^κ_g Q = Q(law(X, law(rep g, exp(zw))))` has `E^♮`-block degree `≤ 3D` for every `κ` and the
   generators of Roy's `A` lie in `FLE(9D)` instead of `FLE(4D)`. Only the constant `C` changes (powers of `3/2` per
   `E^♮`-block). STAGE2's `dblE`, `phOp_mem_FLE`, `transl_gensR2_mem_FLE` are written for factor 2 and need a
   parameterised version (or parallel `E^♮` files) — part of the already planned R2 refactor.
2. **Eight laws instead of two**, indexed by `Fin 2 × Fin 2 × Fin 2`. The `τ_g J` construction ("all laws") is
   unchanged in form. With the fixed point `g = Q`, (c) needs only `λ(P) ≠ 0` for some `λ ∈ {V, W}`.
3. **Relevant = base part `≠ 0`**. The boundary `L` (inside `X`, not only the vertex) is killed by every law
   (`NLaw_zero_of_base`) and by every slice `ℓ = V + αW = 1` (`ℓ` vanishes on `L`). So STAGE2 §11's slicing fix applies
   verbatim; the sliced zero sets consist of points of `E^♮` only, and the sliced ring `(sliced E ring)[t′]` is a CI
   (`slice_rel`), so `bezout` applies. In the unsliced cone the irrelevant locus is the plane `U = V = W = 0`
   (dimension 2 vs 3 for the cone over `X`), handled exactly like the vertex in §11.2.
4. **Fibre equivariance** (`NLaw_fib_left/right`): `A(P + v·fib(P), Q) = A(P, Q) + v·fib(A(P, Q))`. The `ker M`-action
   is by fibre translations, so translates of `ker M`-invariant polynomials are `ker M`-invariant (needed in
   VECEXT §3.2 "Push-out ⇒ product") — now an algebraic identity. The fibre part of the formal exponential is exact and
   algebraic: `exp(0, w)·P = P + w·fib(P)` (degree 1, no ODE).
5. **Formal exponential in the base direction**: as for `E` (V-chart ODE at `O`) plus the fibre coordinate
   `T₃/V = −(ζ + 2℘²/℘') = O(z³)` (coefficients in `ℚ[g₂, g₃]`), obtained from the same ODE extended by
   `d t/dz = x`. To do (STAGE2 `FormalExp` pattern).
6. **Hilbert function** of an `E^♮` block: `3D² + 2` (degree 6) instead of `3D` (degree 3); the subgroup lower bounds
   (`hfun_H0_ge''`) must count `T`-monomials: on `E^♮` the monomials `x^a y^b t^c` give `≥ c' D²`. Fine since
   `dim E^♮ = 2`.
7. Nothing in VECEXT's estimate of 2k lines for "addition laws for `E^♮` blocks" is invalidated; the laws and
   (a)–(c) are now done (≈ 2.9k Lean lines including 1.6k generated identities), the remainder of that item
   (translations, `zeros(τ_g J)`) reuses STAGE2's code.

## 8. Gaps
* (b) is stated per configuration and analytically (`NLaw_expN_all`); there is no Lean definition of `E^♮` as an
  abstract group (`AddCommGroup`) over a general field. The table in §4.2 is that definition; proving associativity
  algebraically is not needed for the multiplicity estimate (only translations by group elements are used, and the
  analytic `exp` is a homomorphism by `NLaw_expN_all`).
* `NLaw_dbl`, `NLaw_ptAff` assume `CharZero` (`ring` with `m/2`); the `O`-cases and (a) hold over any commutative ring;
  (c) needs `2 ≠ 0`, `Δ ≠ 0`.
* Primality of `(F, G)`, `L ⊂ closure(E^♮)`, very-ampleness on `X̃`, and the `(2,2)` non-existence are [Proof sketch] /
  [Numerical], not in Lean (none is needed downstream: Stage 2 works with `I(Z)` and slices).
* The files are not imported by `LSG.lean` (left for the integrator).
