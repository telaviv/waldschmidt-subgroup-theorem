# ABVAR: discharging lean_mstar's abelian-variety hypotheses — design and feasibility

Written 2026-10-31. **Design note only: no Lean was written, nothing was built.**

Labels:
* [Proved]: the argument is complete here (paper level, not Lean).
* [Lit]: read in, or verified against, a source.
* [Heuristic]: plausible but unchecked.
* [Design]: my choice.
* [Est]: line estimate, calibrated on lean_lsg (ME 16.5k, MEV 18.5k, AuxFun 6.5k, AuxFunV 4.3k, W88 17k, Weierstrass +
  Elliptic + CM 9.3k).
* [Spike]: output of `scripts/abvar_spike/`.

Sources read:
* lean_mstar: `CM4E/AbVar/{ThmA,ThmAn,MGAK,X7,X7Torsion,Fermat7,FrameX,CorA2,Basis}.lean`,
  `CM4E/{Waldschmidt,Gen/Frame,Gen/Frame2,Gen/ThmM}.lean`, `TRUST.md` §3, `reviews/REFEREE_HYP_{A,AN,AK,X7}.md` (verdict
  tables).
* lean_lsg: `README.md`, `PLAN.md`, `VECEXT.md`, `INTERFACE.md`, `STAGE2.md`, `STAGE5_MEV.md`, `LSG/AuxFun/Prop21*.lean`
  (headers), `LSG/LemniscateIndep/*` (headers).
* Literature, checked on the web 2026-10-31: Lange–Ruppert (Invent. Math. 79, 1985), via Arène–Kohel–Ritzenthaler (LMS
  JCM 2012) and Kohel; Flynn's P¹⁵ model (72 quadrics) and survey; Serre, Astérisque 69–70 App. II (text read: order ≤ 2
  uniformisation via theta functions, Weil); Gross–Rohrlich (Invent. Math. 45, 1978).

---------------------------------------------------------------------------------------------------------------------

## 0. Decisions and recommendation

1. **Prove instances only.** The targets are:
   * `Thm11KappaA 5 2 (fun s => s+1) perA5 0` and `Thm11KappaA 7 3 (fun s => s+1) perT 0`;
   * `Thm11KappaAn 5 2 (fun s => s+1) perA5 perB5`;
   * `Thm11KappaAK 5 2 (fun s => s+1) perA5 0 ∅`;
   * `Thm11KappaX7 ∅` and `Thm11KappaX7 LAJ`.

   The generic forms are false for arbitrary parameters (§1.1). **Every instance is true as written (§1).** The one
   hidden extra input is that `E7` has algebraic `g₂, g₃` (Chowla–Selberg at discriminant −7). It is not a premise of
   `Thm11KappaX7`; I recommend lean_mstar make it one (§1.5).
2. **The Wüstholz inputs need no new analysis.**
   * `WuestholzA5`, `WuestholzA7` and `WuestholzB5` are *formal corollaries* of the corresponding `Thm11Kappa…` instances.
     The proof: a rational hyperplane `V = W` through one period lift (§1.6, [Proved]).
   * This can be done in lean_mstar **now** (≈ 0.4k lines). It removes three named inputs whatever happens to the rest.
3. **The missing object, `Jac(C)`.** Both curves are odd-degree hyperelliptic curves: `u = 2x − 1` gives
   `u² = 1 − 4y^N` (§2.0, [Proved], [Spike]). The recommended route is **(a), curve first**:
   * Mumford coordinates, and a local inverse of the Abel map.
   * Abel's theorem through the Euler–Jacobi identity, which is elementary.
   * A global `exp` by the duplication law, and periods by Beta integrals.
   * One continuation-along-a-path lemma. It gives surjectivity of `exp`, the identification of the Abel–Jacobi set
     `LAJ`, and the period `γ` all at once.

   Theta functions (route (b)) cannot supply the `ℚ̄`-structure without Riemann's vanishing theorem. Route (c), an abstract
   block interface, is the right *engineering* for the multiplicity estimate (ME), but it needs a concrete model behind
   it. No reduction (route (d)) exists: `A₅` and `A₇` are simple of primitive CM type. Two CM simplifications help a lot:
   * **For every instance except `LAJ`, the `A`-parts of `Y` are rational periods.** Only the finite group `A[M]` is
     ever evaluated, so no height theory on `A` is needed (§2.3).
   * The Legendre analogue for `A^♮` is a Vandermonde determinant (§2.1, [Spike]).
4. **The ME** needs a block interface plus a Jacobian block. There are two new obstacles:
   * the cone over an abelian variety of dimension ≥ 2 is not Cohen–Macaulay, so StrongSix's complete-intersection
     Bézout must become a top-dimensional prime-by-prime Bézout;
   * explicit (2,2) addition laws are plausible to kernel-check for genus 2 (on Grant's P⁸) but not for genus 3
     (P²⁶: 1.26M coefficients per law, [Spike]).
5. **Size [Est].** Throughout, "first kind" means the hypotheses `Thm11KappaA` / `Thm11KappaAK`, as opposed to the
   vector-extension (`A^♮`) hypothesis `Thm11KappaAn`.

   | stage | lines |
   |---|---|
   | genus 2, first kind (milestone M1) | 45–70k |
   | genus 2, `A^♮` (M2) | +20–35k |
   | genus 3 and X7 (M3) | +25–45k |
   | `E7` by Chowla–Selberg (−7) | +3–8k |
   | **total** | **≈ 95–160k** |

   For comparison, all of lean_lsg so far is ≈ 75k lines.

**Recommendation.**
1. Do A0 now:
   * the lean_mstar Wüstholz corollaries;
   * a Python/flint spike that computes and certifies a complete system of (2,2) addition laws on Grant's P⁸ model of
     `v² = t⁵ + 1`, with certificate sizes;
   * a design of top-dimensional Bézout against StrongSix `bezout`.
2. Then build **M1 (genus 2, first kind)**. It discharges `Thm11KappaA 5 …` and `Thm11KappaAK 5 … ∅`, hence
   `two_three_beta5` (`t = B(1/5,1/5)/π`), `fourExpAt_beta5`, `fourExpAt_pi_div_beta5` and `corA2_beta5` (the last still
   with `NotLtildeA`).
3. The paper's headline `two_three_beta5'` (`t = B(1/5,1/5)`) needs `A^♮` (M2). This cannot be avoided (§2.4).
4. Genus 3 / X7 (M3) waits for the A0 decision on how to get addition laws for P²⁶.

---------------------------------------------------------------------------------------------------------------------

## 1. Statement fidelity

### 1.1 Common frame
* `GroupModel` (`CM4E/Waldschmidt.lean:97–113`) and `HyperplaneKappa` (`:125–132`). The soundness rules are in the
  docstring at `:79–95`: `lam ⊂ Λ(G)`, `per ⊂ ℚ ⊗ Ω(G)`, and every connected subgroup over `ℚ̄` lies in `sub`.
* The frames are:
  - `gmF` (`Gen/Frame.lean:77–85`): `sub = T_L × h` with `h = ⊥ ∨ λ ≠ 0` on `h`;
  - `gmF2` (`Gen/Frame2.lean:44–51`, uniform `sub`: some algebraic `x ∈ S` with `Ψ''x ≠ 0`);
  - `gmFX` (`AbVar/FrameX.lean:46–53`; `d₁ = 0`, `d₂ = dim Q + 2`, conservative).
* **Generic statements.** `Thm11KappaA N g κ P s₀` (`ThmA.lean:83–84`) and `Thm11KappaAn` (`ThmAn.lean:56–57`) are W88
  instances only for parameters that come from a real CM abelian variety. For example, `P = 0` gives a group model with
  no periods, and nothing makes it true. The file headers (`ThmA.lean:27–29`, `ThmAn.lean:24`) and REFEREE_HYP_A #5 /
  AN #7 say so. **lean_lsg proves the instances.** The final lean_mstar theorems already take instance hypotheses
  (`fourExpAt_beta5`, `ThmA.lean:210`; `two_three_beta5'`, `ThmAn.lean:254`), so no lean_mstar change is needed for
  this.

### 1.2 `Thm11KappaA 5 2 (fun s => s+1) perA5 0` — TRUE
The objects: `gmA` (`ThmA.lean:79–80`), `perAgen` (`:72–73`), `algA` (`:76`), `perA5` (`:195–196`).

| item | check | label |
|---|---|---|
| coordinates | `z_s` is dual to `ω_s = dx/y^{4−s}` (`s = 0, 1`), which is defined over ℚ; so `algA` (all coordinates algebraic) is the `ℚ̄`-structure of `Lie A^r`. In the hyperelliptic model `dx/y^{4−s} = −5 y^s dy/u` (the standard basis `dy/u, y dy/u`) | [Proved], [Spike] `cm_checks.py` |
| CM action | `[ζ](x, y) = (x, ζy)` pulls `dx/y^k` back to `ζ^{−k} dx/y^k`, so `κ = (1, 2)`, as in `fun s => s+1` | [Proved] |
| period | with `ℓ` the lift of `[0,1]` with `y > 0` and `γ = ℓ − [ζ]ℓ` (closed, since the endpoints are fixed by `ζ`): `z_s(γ) = (1 − ζ^{s+1}) B((s+1)/5, (s+1)/5) = perA5 s`. `z_s([ζ^e]γ) = ζ^{κ_s e} perA5 s` is `perAgen` | [Proved]; numerics in REFEREE_HYP_A (10⁻⁶⁰) and `cm_checks.py` |
| `per` vs the full lattice | `per = span_ℚ perGen`. `H₁(A, ℚ)` is a 1-dimensional `F`-space (`2g = 4 = [F:ℚ]`) and `γ ≠ 0`, so `span_ℚ {[ζ^e]γ} = ℚ ⊗ Ω(A)` **exactly**. Hence `κ` is the true `κ`. Whether `ℤ[ζ]γ = H₁(A, ℤ)` (Rohrlich-type cyclicity, not verified) is irrelevant | [Proved] |
| `lam` | `span_ℚ` of toric logarithms and periods. `Λ(G)` is a `ℚ`-space (division points of algebraic points are algebraic), so `lam ⊂ Λ(G)` | [Proved] |
| `sub` | `F = ℚ(ζ₅)` has no imaginary quadratic subfield, so every CM type is primitive: `A` is simple with `End⁰ A = F`. Connected subgroups are `T_L × B_S` (Goursat), with `T(B_S) = ⊕_s σ_{κ_s}(S) ⊗ ℂ`. On the `s₀` block, `λ = Σ b_j q(s₀, j)` vanishes on `ℂS` only if `Σ b_j m_j = 0` for all `m ∈ S ⊂ F^r`, which forces `S = 0` (`b` is `F`-independent) | [Lit] (Shimura–Taniyama), [Proved] |
| `d₁, d₂` | `d₁ = 2n`, `d₂ = 2r`; `A^r` has no `G_a`/`G_m` part | [Proved] |

### 1.3 `Thm11KappaAn 5 2 (fun s => s+1) perA5 perB5` — TRUE
The objects: `gmAn` (`ThmAn.lean:52–53`), `perAngen` (`:43–46`), `algAn` (`:49`), `perB5` (`:173`).
* **Fibre coordinate.** `w = ⟨·, [dx/y]⟩`, with `[dx/y] ∈ H¹_dR(A)` a ℚ-rational class.
  - The class is canonical: it is the `ζ⁴`-eigenvector, since `[ζ]^*(dx/y) = ζ^{−1}`.
  - `dx/y = −5y³ dy/u` has its only pole at `∞`, so it is of the second kind with no residue, and `P̄ = ∫_γ dx/y`
    is well defined on homology.
  - `∫_γ dx/y = (1 − ζ⁴) B(4/5, 4/5) = perB5`. [Proved]; [Spike] agrees to 15 digits.
* **The group.** `W'` (the other fibre directions, and `Σ_j b_j w_j = 0`) is `ℚ̄`-rational. `Q''` is a non-split
  extension of `A^r` by `G_a` (it is split iff `f` vanishes on the fibre). So `Q''` has no `G_a` quotient and
  `d₀ = 0` is maximal.
* **Periods.** The periods of `Q''` are the images of `Ω((A^♮)^r)`, which gives `perAngen`.
* **Subgroups.** The `sub` condition holds by Mazur–Messing universality, exactly as `ThmAn.lean:26–29` says: a section
  over `B_S` needs `Σ_j b_j σ̄(m_j) = 0` on `S`, so `S = 0`. [Lit, Proved]
* For the lean_lsg bridge, `Q''` has the VECEXT class shape: the push-out of `(A^r)^♮` along an algebraic form, with
  `A` in place of the `E`'s.

### 1.4 `Thm11KappaAK` / `Thm11KappaAnK` (`MGAK.lean:133–134`, `311–312`)
* **The only use is `LA = ∅`** (`corA2`, `CorA2.lean:36`; `corA2_beta5`, `:139`). `Thm11KappaAnK` has no instance
  anywhere in lean_mstar.
* With `LA = ∅` the statement is TRUE. The model is `gmA`'s group on the frame `gmF2`, and the uniform `sub`
  (`Frame2.lean:51`) is sound:
  - a nonzero `T_L × B_S` contains a rational toric vector with `θᵀl ≠ 0`, or a vector of `T(B_S)` with `λ ≠ 0`
    (§1.2);
  - in both cases the vector can be chosen algebraic, because `T(B_S)` is `ℚ̄`-rational.
* With a nonempty `LA`, the statement is true only for coherent, normalised logarithm tuples (REFEREE_HYP_AK #5).
  lean_lsg can prove it for `LA ⊆ LogA := {v : exp_A(v) ∈ A(ℚ̄)}` in its own `exp`. It can also prove it for the
  ℚ-span of Abel–Jacobi tuples once `exp ∘ AJ = id` holds (§2.2, lemma a6). No lean_mstar change is needed unless a
  nonempty `LA` is ever used.

### 1.5 `Thm11KappaX7 LA` (`X7.lean:119–120`) — TRUE, with one hidden period identification
The objects: `gmX7` (`:113–114`), `lamX7` (`:100–103`), `perX7` (`:106–107`), `mu1`/`mu2` (`:81`, `:87`), `E7`
(`:54–70`), `omega7 = B(1/7, 2/7)` (`Fermat7.lean:109`), `perT` (`X7.lean:73`).
* **Uses.** `LA = ∅` (`x7c`, `X7.lean:535`) and `LA = LAJ` (`X7Torsion.lean:113`; `x7a_AJ` `:119`, `x7b_AJ` `:126`).
* **Coordinates and periods.** `z_s` is dual to `dx/y^{6−s} = −7 y^s dy/u`, so `κ = (1, 2, 3)`, and `perT s = perA (s+1)`.
  This uses the same cycle construction as §1.2. [Proved]
* **`A₇` is simple.** The type `{1,2,3}` mod 7 has trivial stabiliser and is not the type `{1,2,4}` induced from
  `ℚ(√−7)` ([Spike] `cm_checks.py`). `Hom(A₇, E) = 0`.
* **`sub`.** On `E^{3r}`, `{ζ^e b_j}_{e<3}` is a `k`-basis of `K`. On `A^{3r}`, the slot forms catch every block (§1.2
  argument per slot). On `G_a²`, `Ψ'' = id`. [Proved]
* **`LAJ` is sound.**
  - `AJPath.triple` (`X7Torsion.lean:109–110`) is `∫ dx/y^{6−s}` along a lift with algebraic endpoints. That is the
    eigen-coordinate triple of `Q − O` in the normalisation of `perT`.
  - Its `ℚ`-span consists of logarithms of algebraic points (division points).
* **Hidden input.** `perX7`, `lamX7` and the soundness of `gmX7` need `E7` (the lattice `B(1/7,2/7)·ℤ[α]`) to have
  algebraic `g₂, g₃`.
  - This is true (Chowla–Selberg; REFEREE_HYP_X7 checks `j = −3375`). But it is **not a premise** of `Thm11KappaX7`,
    unlike `Thm11Kappa L d₁` (`Waldschmidt.lean:149–150`), which takes `hg₂ hg₃`.
  - lean_lsg would have to prove it, and that is harder than the lemniscatic `g₂ = 4`:
    + no single Beta substitution exists;
    + `B(1/7, 2/7)` is a period of `(1−x)dx/y⁶` on the Klein quartic `y⁷ = x(1−x)²`, whose Jacobian is `∼ E³`
      [Lit, standard; the differential is my check];
    + so the route is an explicit map from the Klein quartic to `E`, plus a real-period comparison.
  - [Est] 3–8k, high variance.
  - **Recommended lean_mstar change L2:** make `IsAlgebraic ℚ E7.g₂ → IsAlgebraic ℚ E7.g₃ →` premises of
    `Thm11KappaX7` (the `Thm11Kappa` convention), and carry them as a named input. This mirrors `hg₃'` for `Ω_ρ`
    (TRUST.md l. 45).

### 1.6 `WuestholzA5`, `WuestholzA7` (`ThmA.lean:199`, `:202`) and `WuestholzB5` (`ThmAn.lean:176`): corollaries of the instances
**Claim [Proved].** `Thm11KappaA 5 2 (·+1) perA5 0 → WuestholzA5`; the same for `A7` (with `perT`) and for `B5` (from
`Thm11KappaAn 5 2 (·+1) perA5 perB5`, with `λ = snd`).

Proof. Suppose `P₀ := perA5 0 = απ` with `α ∈ ℚ̄`; `α ≠ 0` since `P₀ ≠ 0`.
1. Set up. Take an adapted `b` (`exists_adapted_basisN`), `K = span_ℚ θ`, `j₀ = 0`, and `μ ∈ ℚ̄ ∖ K` (for example
   `2^{1/(d+1)}`, `d = [K:ℚ]`).
2. The hyperplane. Put `φ(x, y, q) = λ(q) − a θᵀx − aμ θᵀy` with `a = α/(2i)`. The vector
   `y₀ = tor1 (j₀,0) (2πi) + qv(pv_{j₀,0}) ∈ lam` satisfies `φ(y₀) = b_{j₀}P₀ − a·b_{j₀}·2πi = 0`.
   `V = W = ker φ` is a hyperplane, and `ℚ̄`-rational because `φ` has algebraic coefficients.
3. The hypothesis applies. The premise (5.4) reads `1 > (…)·(d − 1 − dim W) = 0`. So `HyperplaneKappa` gives
   `S = torSub L × h ⊆ V`, `S ≠ ⊥`.
4. `h = ⊥`. Otherwise some `x ∈ h` has `λx ≠ 0`, while `(0, x) ∈ V` gives `λx = 0`.
5. `L = ⊥`. For `l ∈ L`, `θᵀl₁ + μθᵀl₂ = 0` with `θᵀlᵢ ∈ K` and `μ ∉ K` forces `θᵀl₁ = θᵀl₂ = 0`, so `l = 0`.
   This contradicts `S ≠ ⊥`.

For `B5` replace `λ` by the fibre coordinate (`perAngen` at `je = (j₀, 0)` has fibre `b_{j₀}P̄`). ∎

* The same conclusion follows from W88 Thm 4.1 for `G_m × A` in "Baker mode": `V = W` a rational hyperplane through
  `(2πi, z(γ))`. `T_{G'} ⊂ V` forces `G' = 0`, and then `(0 + 1 + 2g)·1 ≤ 1·(1 + 2g − 1)` fails. [Proved]
* So the question "can P/π be obtained the way Stage 1 got ω/π via Schneider?" has a simpler answer. **Nothing separate
  is needed: the inputs fall out of the same instance.**
* Not covered by this trick, because they need `G_a` factors or the smallest-subgroup form:
  - `NotLtildeA` (`CorA2.lean:28`; `G_a × G_m^m × A`);
  - `WuestholzBeta7` (`X7.lean:286`; `G_a × A × E`);
  - `WuestholzX7` (`:491`);
  - `TorsionX7` (`X7Torsion.lean:32`; `A²`, iterated).

  They are hyperplane instances of the general theorem that lean_lsg would prove (`d₀ ≥ 1`). `TorsionX7` additionally
  needs a §5d-style iteration. [Heuristic]

---------------------------------------------------------------------------------------------------------------------

## 2. The missing object `Jac(C)`, `C : y^N = x(1 − x)`, `N = 5, 7`

### 2.0 The curves are hyperelliptic [Proved, Spike `cm_checks.py`]
* `u = 2x − 1` gives `u² = 1 − 4y^N` (genus `(N−1)/2`, odd degree, one point at `∞`). Over `ℚ̄`, `y = −4^{−1/N} t` gives
  `u² = t^N + 1`.
* `dx/y^k = −N y^{N−1−k} dy/u`. So the eigen-differentials are the standard `y^s dy/u` (first kind, `s < g`) and
  `y^s dy/u` (`g ≤ s < 2g`, second kind).
* `[ζ] : (y, u) ↦ (ζy, u)` is a hyperelliptic automorphism.

This makes the whole hyperelliptic toolkit available: Mumford coordinates, Cantor's algorithm, Grant's P⁸ model for
genus 2, and Kleinian functions.

### 2.1 What any route must supply, by consumer
* **ME** (over `ℂ`; lean_lsg's `MultEstAb` is over `ℂ`, so no `ℚ̄`-structure is needed here):
  - a projective or multiprojective model with prime ideal `𝔊`;
  - Hilbert-function bounds (on slices);
  - a complete system of addition laws of bounded bidegree;
  - Philippon operators from a formal exponential (chain v2, STAGE2 §10);
  - points `= exp(ℂ^g)` (surjectivity; lean_lsg's `SubgroupExpSurj` analogue);
  - stabilisers turned into tangent data (subgroup layer).
* **Auxiliary function:**
  - `exp` coordinates as `σ^D·φ` with `σ` entire of order 2 and a quasi-periodic multiplier (hypothesis
    `QuasiPeriodicB`, `Prop21.lean`);
  - `ℚ̄` Taylor coefficients along `ℚ̄`-directions at the points of `Y`, with height bounds (an ODE with `ℚ̄`
    coefficients);
  - **W83 Prop 2.1 for a g-dimensional lattice block.** lean_lsg's Tier 2 (`Prop21Lat.lean`) needs coordinate forms that
    send the periods into products of rank-2 lattices. `Λ(A₅)` is not ℂ-decomposable (`A` is simple), and one
    eigen-coordinate maps it onto a dense rank-4 subgroup of `ℂ`. A Tier 3 is needed.
* **Bridges:**
  - `z_s(γ) = perA5 s`, `P̄ = perB5`;
  - `ker exp ⊇ ℤ[ζ]γ`, a lattice;
  - `[ζ]` linear in eigen-coordinates;
  - abelian subvarieties of `A^r` correspond to `F`-subspaces. Via lattices: a complex subspace `t` with `t ∩ Λ^r` a
    full lattice is `⊕ σ_{κ_s}(S) ⊗ ℂ`. The proof uses the fact that the Galois translates of a primitive type generate
    the Boolean algebra of singletons ([Proved]; atoms checked in `cm_checks.py`) [Est 1.5k];
  - for X7, products with `E^{3r}`;
  - for `A^♮`, that the periods span `T(A^♮)`. **This is a Vandermonde determinant for CM**:
    `det = det(diag P_k) · det(ζ^{−ke})`. Numerically `det = −(2500/3)π²` for `N = 5` [Spike], the expected
    Legendre/Riemann-relation shape. No intersection form is needed.

### 2.2 Routes

| | (a) curve first | (b) theta / Kleinian σ | (c) abstract interface | (d) reduction |
|---|---|---|---|---|
| model | Mumford chart `J∖Θ` (a complete intersection: `g` equations in `𝔸^{2g}`) + Grant P⁸ (g = 2) | `ℂ^g/Λ` with a Riemann form; level-3 theta functions | whatever instance is plugged in | none exists |
| `ℚ̄`-structure | automatic: functions on `C^{(g)}`; `∂/∂z_s` by inverting the Abel Jacobian (ℚ coefficients) | needs Riemann's vanishing theorem / Jacobi inversion to link θ to `C` (hard core, 15–30k, high risk) | from the instance | — |
| periods | `∫_γ y^s dy/u` = Beta integrals (Mathlib `betaIntegral`; lean_mstar `betaG_eq_betaIntegral`) | must also identify the full symplectic period matrix | from the instance | — |
| group law | Cantor on the chart (generic genus-2 law: 88–695 terms per coordinate numerator, [Spike] `cantor.py`); projective (2,2) laws (A0) | Riemann theta formula, genus-generic, no explicit polynomials (Koizumi projective normality, Lefschetz; 10–20k) | interface fields | — |
| order 2 | duplication functional equation [Heuristic: degree-2 resonance] or theta | free (theta functions are entire of order 2) | field | — |
| verdict | **recommended** (12–20k for the object, g = 2) | use at most for growth, or for genus-3 addition laws | **use for the ME engineering** | — |

**Route (a) in detail** (genus-generic code for `u² = t^{2g+1} + 1` where possible):
* a1. **Mumford chart.** `(a, b)` with `a` monic of degree `g`, `deg b < g`, `a | f − b²`: a complete intersection.
  - The generic sum is one Cantor step for g = 2, two for g = 3 (`cantor.py`).
  - The projective model: Grant P⁸ (3Θ) for g = 2 [Lit: Flynn's survey says that for `y² = quintic` the Jacobian
    embeds in P⁸, and cites Grant 1990].
  - A basis `1, ℘₁₁, ℘₁₂, ℘₂₂, ℘₁₁₁, …, ℘₁₂² − ℘₁₁℘₂₂` is [Heuristic: from memory, not checked in Grant].
* a2. **Abel's theorem, locally** [Proved]. Let the points `(x_i, y_i)` be the zeros of `R = f − c²` on `y = c(x)`. Then
  `Σ_i x_i^k dx_i/y_i = 2Σ_i x_i^k δc(x_i)/R'(x_i) = 0` for `k ≤ g − 1`, by Euler–Jacobi: `deg(x^k δc) ≤ deg R − 2` in
  both regimes `deg c ≤ g` and `deg c ≥ g + 1`. [Spike] numeric check of Euler–Jacobi.
* a3. **Local `exp`** near a generic divisor, by the holomorphic inverse function theorem.
  - **Mathlib check needed:** analyticity of a ℂ-differentiable local inverse in several variables, and the identity
    theorem on `ℂ^g` (risk R4).
* a4. **Global `exp`** by `exp(z) = [2^k] exp(z/2^k)` (duplication is a rational map on the chart and a degree-4 morphism
  on P⁸). It is a homomorphism by the identity theorem from a2.
* a5. **Kernel.** It is discrete (local biholomorphism) and contains `z(γ)` and `z([ζ^e]γ)`; then it is a lattice of
  rank `2g`.
* a6. **Continuation lemma.** For a `C¹` path on `C` from the base point, `exp(∫ ω) = [P(1) − P(0)]` (open-closed
  argument on `[0,1]`, using a3). This yields three things:
  - `z(γ) ∈ ker exp`;
  - **surjectivity**: every point of `J` is `Σ[P_i − ∞]` *by the Mumford description itself*, and `exp` is a
    homomorphism (Jacobi inversion without Riemann–Roch);
  - `LAJ ⊆ LogA` (for X7).
  - Remaining for surjectivity: the points of the boundary `Θ` of the projective closure are exactly the classes of
    degree `< g` (an algebraic computation on the P⁸ model).
* a7. **Order 2.** Either theta functions (Serre's route; Serre, App. II §3.4 takes a theta function with given
  divisor, citing Weil), or the entire lift `Φ(z) = Dup^{∘k}(Φ₀(z/2^k))`, with `|Φ| ≤ e^{c|z|²}`.
  - The functional equation `H(z) − 4H(z/2) = m(z)` for the log-multiplier is resonant in degree 2, so an
    `e^{quadratic}` correction term is needed. [Heuristic; risk R3]
* a8. **ODE for the Taylor coefficients.** `∂/∂z_s` of the Mumford coordinates are rational in them, with ℚ coefficients.
  This works for any `g`.

### 2.3 CM simplification: rational periods only [Proved]
* In `gmA`, `gmAn`, `gmAK ∅` and `gmX7 ∅`, the `A`-component of every generator of `lam` is a period. So every
  `y ∈ Y` has its `A`-part in `(1/M)Ω_A` for one `M`, and `exp(sy)_A ∈ A[M]`, a fixed finite set.
* The auxiliary function then needs, on `A`:
  - only that `A[M] ⊂ A(ℚ̄)` (finite fibres of `[M]`, a ℚ̄-morphism);
  - Taylor coefficients at those finitely many points (translation by algebraic points, a8).
  
  It needs no heights of non-torsion points.
* **Design:** the first lean_lsg target is `Theorem41AbVarPer` (W88 4.1 under (NR) for
  `G_a^{d₀} × G_m^{d₁} × ∏E_j × A^r` with the `A`-parts of `Y` in `ℚΩ_A`). The full `Λ(G)` version is only for
  `Thm11KappaX7 LAJ` (M3).

### 2.4 No reduction; `A^♮` is needed for the headline [Heuristic, Γ-monomial check]
* `A₅` and `A₇` are simple, with no elliptic factor. Fermat Jacobians decompose into the same `A`'s.
* `FourExpAt(cB(1/5,1/5))` could come from MG-A only if `π·B(1/5,1/5)` were a first-kind period of a CM abelian variety.
  The first-kind Fermat periods `Γ(r/5)Γ(s/5)/Γ((r+s)/5)` (`r + s < 5`) are, up to `ℚ̄ˣ`:
  `B(1/5,1/5)`, `Γ(1/5)Γ(2/5)²/π`, `Γ(1/5)Γ(2/5)²/π` and `B(1/5,1/5)`.
  - None is `π·B` *as a Γ-monomial*.
  - An equality would be a Γ-relation outside the Deligne/Koblitz–Ogus ones. That is expected false (Rohrlich–Lang),
    but it is unproved, hence [Heuristic]: there is no *known* first-kind route.
* So `two_three_beta5'` needs `Thm11KappaAn`, i.e. `A^♮` (M2). `two_three_beta5` (`t = B/π`) needs only M1.

---------------------------------------------------------------------------------------------------------------------

## 3. The ME generalisation

### 3.1 What is block-specific today
* `LSG/ME` (16.5k) hard-codes the block `(U, V, W)` with a Weierstrass cubic. `LSG/MEV` (18.5k) is a **parallel copy**
  for the `E^♮` block `(U, V, W, T₁, T₃)`.
* Block-specific:
  - `Geom`, `IG`/`IGPrime`/`IGNull` (primality and complete-intersection height of `I_G`);
  - `Transl` + addition laws;
  - `FormalExp`/`PhOp*` (formal exponential, Philippon operators);
  - MEV's `Flow`/`Curve`/`Canon`/`Assoc`;
  - the cone parts of the subgroup layer (`SubgroupConeE`: `(n+1)²` independent cone monomials);
  - `SliceIG` (standard monomials of a complete-intersection slice), `SliceDim`;
  - the chart data in `Wust*`;
  - the constants of `MainAb`.
* Generic: the StrongSix layers (`Hilbert`, `HDim`, `Bezout` *for complete intersections*, `Component`, CM), the chain
  combinatorics, the stabiliser, the product decomposition, the slice Nullstellensatz.
* A third and fourth parallel copy (`J₂`, `J₃`, and `J₂^♮`) would cost ≈ 3 × 18k. A **`BlockData` interface** costs a
  refactor of ≈ 8–12k changed lines; after that each block is data plus 3–6k. [Est; Design: refactor]

### 3.2 New obstacles for a Jacobian block
* **O1 — not a complete intersection, not Cohen–Macaulay.** No projective model of an abelian variety of dimension
  ≥ 2 is a complete intersection, and its affine cone is not Cohen–Macaulay (`H¹(A, O_A) ≠ 0`) [Lit, standard].
  - StrongSix `bezout` (complete-intersection chain) and `SliceIG`/`height_slIG` do not apply.
  - Fix: **top-dimensional Bézout for a prime ambient ideal**: `deg_top(𝔭 + (F)) ≤ deg 𝔭 · deg F` for `F ∉ 𝔭`,
    iterated over top-dimensional components (Philippon/Nesterenko). It needs no Cohen–Macaulay property.
  - [Est 1.5–3k]
  - The Mumford charts *are* complete intersections, but they are not dehomogenisations of one global model compatible
    with translation degrees, so they do not replace this.
* **O2 — addition laws.**
  - Complete systems of bidegree (2,2) exist for every symmetric projectively normal embedding [Lit: Lange–Ruppert,
    restated by Kohel and by Arène–Kohel–Ritzenthaler].
  - Sizes [Spike] `dims.py`, from `h⁰(kΘ) = k^g` and projective normality; Flynn's 72 for P¹⁵ is reproduced:

    | model | #quadrics | coefficients per (2,2) law, mod `(I(P), I(Q))` | normal-form space of one identity, bidegree (4,4) |
    |---|---|---|---|
    | g = 2, P⁸ | 9 | 11,664 | 20,736 |
    | g = 2, P¹⁵ | 72 | 65,536 | 65,536 |
    | g = 3, P²⁶ | 162 | 1,259,712 | 2,985,984 |
    | g = 3, P⁶³ | 1,568 | 16.8M | 16.8M |

  - **Genus 2 on P⁸**: certificates of order 10⁵–10⁶ terms in total. That is beyond `linear_combination` (MEV's 32
    fibre identities with ≤ 30-term corrections already take 5 min). It is plausible with a lean_beta-style
    `decide +kernel` certificate format over `ℤ[ζ]`-free integer data (the curve `t⁵ + 1` is defined over ℤ).
    [Heuristic; this is A0's job]
  - **Genus 3**: not plausible explicitly. The options are:
    + theta-analytic laws (route (b) used only for the ME);
    + a smaller multiprojective model [Heuristic, none known];
    + postponing X7.
* **O3 — derivations and formal exponential.** There are `g` commuting invariant derivations. The formal `exp` is the
  inverse of the formal Abel integral (a8), and Philippon's `δ` operators via laws ∘ formal `exp` keep the degree fixed
  (chain v2), for any `g`. [Design]
* **O4 — the subgroup layer.**
  - `H⁰` dimension: smooth point plus homogeneity, as now.
  - Hilbert lower bound for `B ⊂ A^r`: project to coordinates on which `T_B` projects isomorphically; this replaces
    `SubgroupConeE`.
  - The classification uses §2.1's lattice / CM lemma.
  - [Est 3–5k on top of the interface]
* **ME total** for the Jacobian block, genus 2: **20–30k** including the interface refactor, plus generated
  certificates. Genus 3 reuses the code; its data is the open question.

---------------------------------------------------------------------------------------------------------------------

## 4. Wüstholz inputs (summary)
* Answered in §1.6: they follow from the `HyperplaneKappa` instances by a rational-hyperplane argument, or from Thm 4.1
  for `G_m × A` (resp. `G_m × A^♮`) in Baker mode.
* Unlike Stage 1, where Schneider–Lang was the *only* available tool for `ω/π`, here the instance is assumed or proved
  anyway, so no separate transcendence argument is needed.
* `WuestholzB5` is also equivalent to `B(1/5,1/5) ∉ ℚ̄` (Schneider 1941), via `beta5_mul` (`ThmAn.lean:190`).

---------------------------------------------------------------------------------------------------------------------

## 5. Staged plan (riskiest first)

| stage | content | checkpoint | [Est] |
|---|---|---|---|
| **A0a** | lean_mstar: `wuestholzA5_of`, `wuestholzA7_of`, `wuestholzB5_of` (§1.6; a shared lemma, `μ ∉ K` via Eisenstein) | compiles in lean_mstar; TRUST rows move from named input to corollary | 0.3–0.5k |
| **A0b** | Python/flint: Grant P⁸ for `v² = t⁵ + 1`: the 3Θ basis, quadrics (+ cubics?), a complete (2,2) system and the degree-4 duplication; certificate sizes; one prototype `decide +kernel` identity in a scratch project (not lean_lsg) | total certificate ≤ ~10⁶ terms and compile ≤ ~1 h ⇒ go for genus 2; decide the genus-3 law strategy | spike |
| **A0c** | design of top-dimensional Bézout vs StrongSix `Bezout`/`CM` | written plan; StrongSix files touched: new ones only | design |
| A1 | hyperelliptic Jacobian algebra (genus-generic): Mumford reps, Cantor law on `J∖Θ`, P⁸ model, boundary points, `[ζ]` | P⁸ ideal prime, chart ⊂ model | 4–7k |
| A2 | analytic `exp`: a2–a6, a8; Beta periods (`perA5`, `perB5`) | `exp (z γ) = 0`, kernel a lattice, `exp` surjective onto the model | 8–14k |
| A3 | order 2 (theta, or duplication with the resonance fix) | `QuasiPeriodicB` for the `A` block | 2–5k |
| A4 | `BlockData` refactor + Jacobian block + top-dimensional Bézout + subgroup layer | `MultEstAbA` (ME for `G_a × G_m × ∏E × A^r`) | 20–30k |
| A5 | Tier-3 Prop 2.1 (lattice blocks), Prop 6.1, Lemma U, §7, `Theorem41AbVarPer` | statement + proof | 5–8k |
| A6 | §5d engine + CM classification + bridges (`hyperplaneKappa_of_iso` pattern) | `thm11KappaA5`, `thm11KappaAK5` verbatim against lean_mstar | 3–5k |
| **M1** | genus 2, first kind: `two_three_beta5`, `fourExpAt_beta5`, `fourExpAt_pi_div_beta5`, `corA2_beta5` (+`NotLtildeA`) | | **≈ 45–70k** |
| A7 | `A^♮` for genus 2: second-kind coordinate, `P̄`, Vandermonde spanning, `A^♮` block (MEV analogue), `AuxV` analogue, bridges | `thm11KappaAn5`; lean_mstar gets `two_three_beta5'` | 20–35k (M2) |
| A8 | genus 3 + X7: data/model per A0b, `E7` (L2 premise or Chowla–Selberg −7), `G_a² × E^{3r} × A^{3r}` bridge, full `Λ(G)` (heights on `J`) for `LAJ` | `thm11KappaX7_empty`, `thm11KappaX7_LAJ` | 25–45k (+3–8k) (M3) |

**lean_mstar changes:**
* **L1** (now): the A0a corollaries.
* **L2**: put `E7`'s `g₂, g₃ ∈ ℚ̄` into `Thm11KappaX7` as premises, or as a named input `E7Alg`.
* **L3** (later): depend on lean_lsg and import the instance theorems (MStarCopy pattern; no statement changes for
  `ThmA`/`ThmAn`/`MGAK` instances).
* **L4** (docs): TRUST should say that the headline `two_three_beta5'` needs `A^♮` (M2), while `two_three_beta5` arrives
  at M1.

---------------------------------------------------------------------------------------------------------------------

## 6. Risks (ordered)
1. **R-size.** ≈ 95–160k lines, 1.3–2× everything lean_lsg has so far. The estimates for A4 and A7 are ±40%.
2. **R-laws3.** There is no kernel-checkable explicit addition-law system for the genus-3 Jacobian (P²⁶ numbers in
   §3.2). This blocks X7 unless theta-analytic laws are formalised (10–20k extra) or a smaller model is found.
3. **R-Bezout.** The non-Cohen–Macaulay ambient needs a new Bézout layer. StrongSix's complete-intersection route does
   not transfer.
4. **R-order2.** Order-2 functions without theta functions: duplication with the degree-2 resonance. The fallback is
   g-variable Riemann theta (Mathlib only has one-variable `jacobiTheta₂`), 1.5–2.5k, plus linking `σ`'s divisor to `Θ`
   (hard; avoid).
5. **R-SCV.** Several-variable complex analysis in Mathlib v4.35: analyticity of ℂ-differentiable maps on `ℂ^g`, the
   identity theorem, meromorphic functions. Unverified; check before A2.
6. **R-Prop21.** Tier 3 for a non-decomposable `g`-dimensional period lattice.
7. **R-E7.** Chowla–Selberg at −7. Avoided by L2, but then it stays a named input.
8. Removed by the CM structure:
   * the Legendre analogue (Vandermonde);
   * heights on `A` for the first-kind targets (§2.3);
   * the subgroup classification (primitive types: Boolean-algebra lemma).

## 7. Spike files (`scripts/abvar_spike/`, untrusted, Python)
* `dims.py`: the model and law-size table of §3.2.
* `cantor.py [g]`: generic Cantor sum on `v² = t^{2g+1} + 1` over `ℚ(a, b, a', b')`, with term counts. g = 2: one step,
  `a₀''` 115/34 terms (numerator/denominator), `a₁''` 88/34, `b₀''` 695/104, `b₁''` 518/104.
  - g = 3 (two steps) did **not finish in 1200 s** in sympy (`cantor_g3.out`). That is a tool limit, not a measured
    size. It does suggest that even the affine genus-3 law is large, which is consistent with R-laws3.
  - A flint `fmpz_mpoly` rewrite would be needed for a real g = 3 count.
* `cm_checks.py`:
  - hyperelliptic normal form and differentials;
  - primitivity, and Boolean-algebra atoms of the CM types;
  - the `A^♮` period-matrix determinants (`N = 5`: `−(2500/3)π²` to 12 digits; `N = 7`: nonzero);
  - `perA5 0` and `perB5` against the cycle integrals;
  - the Euler–Jacobi check.

---------------------------------------------------------------------------------------------------------------------

## A0 results (2026-10-31: A0b addition-law spike, A0c Bézout design)

All scripts and outputs are in `scripts/abvar_spike/`; the Lean prototypes are in `scripts/abvar_spike/lean_proto/`
(they were built and run in a scratch Lake project outside lean_lsg; nothing in `LSG/` or StrongSix was touched).
Each "[Proved]" below is an exact computer-algebra verification (python-flint `fmpq`, or exact mod-p linear algebra
in a direction where mod p implies ℚ). None of it is a Lean proof yet.

### A0.0 Verdict
* **Genus 2: GO**, with a different certificate design from the one §3.2 assumed.
  - **Explicit cofactor certificates are NO-GO.** Their total is 1.44M cofactor terms (5.8M expanded products). A naive
    sparse-list kernel checker did not finish one identity: it ran more than 7 CPU-minutes and reached 13.6 GB
    resident before it was killed.
  - **What works**:
    + a normal-form plus Kronecker big-integer checker, with no stored cofactors, at about 25 s of kernel time and
      ≤ 4 GB per identity (measured);
    + a *semantic* derivation of correctness and completeness for all laws (§A0.3), which needs only about 73 big
      identities.
  - Measured or extrapolated cost: about 45–55 CPU-minutes, i.e. 15–20 min wall clock on 3–4 parallel files. Stored
    data is about 2–3·10⁴ numbers. Both are inside the A0b criterion (≲ 10⁶ terms, ≲ 1 h).
* **Genus 3: NO-GO for explicit P²⁶ laws.** It extrapolates to more than 10³ times the genus-2 kernel work per identity
  (§A0.4).
  - Chart-only (Cantor) laws do not cover `Θ` and give no global translation operators.
  - Recommendation: theta-analytic laws (existence only, genus-generic), or postpone X7.
* **Bézout (A0c).**
  - lean_lsg's ME already slices away the cone vertex, so the obstruction is *not* the non-CM vertex. It is that the
    sliced A-block ideal is not a global complete intersection.
  - Fix: a **local complete-intersection Bézout**, i.e. StrongSix `bezout` with "complete intersection" replaced by
    "unmixed along the chain", which follows from local CI plus StrongSix's CM library. A-block local CI comes from
    small single-copy certificates.
  - Estimate 1.9–3.2k lines. **This corrects §3.2 O1**: a CM-free "top-dimensional prime-by-prime" Bézout does *not*
    suffice in this architecture (§A0.5).

### A0.1 The model (`grant_model.py`, `ideal_P8.py`, `coble_check.py`)
* **Curve.** `u² = 1 − 4y⁵` with `x = −y` is `y² = 4x⁵ + 1`, Baker/Grant normal form with `λ₀ = 1` and the other
  `λᵢ = 0`. Everything is over ℚ (in fact ℤ[1/2]).
* **Coordinates.** Mumford coordinates on `J∖Θ` are `a = x² − s₁x + s₂`, `b = b₁x + b₀`, with two chart relations
  `r₁ = r₀ = 0` (`model.json`). The basis is Grant's 3Θ basis, derived and checked, not assumed:
  - `X₀ = 1`; `X₁ = ℘₁₁ = b₁²/4 − s₁³ + s₁s₂`; `X₂ = ℘₁₂ = −s₂`; `X₃ = ℘₂₂ = s₁`;
  - `X₄ = ℘₁₁₁ = −2b₀s₁² + b₀s₂ − b₁³/4 + b₁s₁³ − 3b₁s₁s₂`; `X₅ = ℘₁₁₂ = −b₀s₁ − b₁s₂`; `X₆ = ℘₁₂₂ = b₀`;
    `X₇ = ℘₂₂₂ = b₁`;
  - `X₈ = ℘₁₂² − ℘₁₁℘₂₂ ≡ b₀b₁/2 + 2s₁²s₂`.

  Checks:
  - The `℘ᵢⱼ` come from Baker's `℘₁₁ = (F(x₁,x₂) − 2y₁y₂)/4(x₁−x₂)²` and the inverse Abel Jacobian. The symmetry of
    the third derivatives is checked.
  - Pole orders along `Θ` are 0, 2, 2, 2, 3, 3, 3, 3, 3 (Laurent expansion at `P₂ → ∞`). The 9 functions are
    independent, so they form a basis of `L(3Θ)` ([Proved] given `h⁰(3Θ) = 9` [Lit, Riemann–Roch]).
* **Ideal.** `dim S_d/I_d = 9d²` for d = 1…5 [Proved].
  - `I₂` is spanned by 9 quadrics (`ideal.json`).
  - **`I₃` needs 3 extra cubics**: `dim (Q)₃ = 81 < 84`. But `(Q)_d = I_d` for d = 4, 5, so the quadrics cut out
    `A` scheme-theoretically [Proved for d ≤ 5]. This is enough for every bidegree-(4,4) certificate.
  - The 9 quadrics are exactly the partial derivatives of a unique cubic, the **Coble cubic** (printed in
    `coble_check.out`).
  - This agrees with the literature: Coble showed that 9 quadrics cut out A set-theoretically, and Barth that they do so
    scheme-theoretically [Lit, secondary: quoted in arXiv:1303.1132, not read in the originals]; the ideal is generated
    by quadrics and cubics when the embedding is projectively normal [Lit: ar5iv 1604.06228, statement only]; Koizumi
    gives projective normality.
* **Symmetries.**
  - μ₁₀ acts by `(x, y) ↦ (t²x, t⁵y)`, giving weights `wt X = (0,6,4,2,9,7,5,3,8)`. Every law and identity is
    weight-homogeneous, which is the source of the ≈ 1/10 sparsity.
  - `[−1] = diag(1,1,1,1,−1,−1,−1,−1,1)`.
  - The origin is `O = e₄` [Numerical].

### A0.2 The (2,2) laws (`laws_modp.py`, `laws_exact.py`, `checks_modp.py`, `symmetry_checks.py`)
* **Form.** `A_k^{(m)}(P,Q) = X_k(P+Q)·X_m(P−Q)·B(P,Q)³` in affine normalisation, for m = 0…8 (one law per section
  `X_m` of `L`, Lange–Ruppert [Lit]).
  - Here `B = X₁(P)X₀(Q) − X₀(P)X₁(Q) + X₂(P)X₃(Q) − X₃(P)X₂(Q)`. This is Baker's
    `σ(u+v)σ(u−v)/σ(u)²σ(v)²`; it was found as the 1-dimensional solution space of a linear system, not assumed.
  - The laws were interpolated mod three primes with Cantor arithmetic. Each system was consistent (rank `[A | b]` =
    1296 = number of unknowns). They were then rationally reconstructed and cross-checked against each prime.
* **Sizes.**
  - 8,235 terms for all 81 coordinates, 854–973 per law. §3.2 counted 11,664 per law; the difference is the weight
    sparsity.
  - The common denominator is 32, and integer coefficients are ≤ 1536 (11 bits).
  - **(S1)** `A_k^{(m)}(X, [−1]Y) = A_m^{(k)}(X, Y)`, coefficient for coefficient [Proved].
  - **(S2)** `A_k^{(m)}(Y, X) = ±A_k^{(m)}(X, Y)` [Proved].
  - So 45 polynomials (≈ 4.2k terms) define everything, and (S1) can be made *definitional* in Lean.
* **Duplication.** `Dup = A^{(4)}(X, X)`, the law whose section is nonzero at `O`. It has degree 4 and 321 terms in
  total.
* **Numerical checks (mod 10⁹+7).**
  - All 9 laws agree with Cantor addition on 30 random pairs.
  - `Dup` agrees with Cantor doubling.
  - `A^{(m)}(X, O) ∝ X`.
  - Law 0 vanishes identically on `{P − Q ∈ Θ}`.
* **(V1) membership** [Proved]: all 81 `Q_j(A^{(m)}(X,Y)) ∈ (Q(X)) + (Q(Y))`.
  - Criterion: `N_Xᵀ C N_Y = 0`, with `N` the degree-4 normal-form map modulo `(Q)₄ = I₄`.
  - Before reduction the left-hand sides have 9.7k–15.2k terms each, 1.07M in total.
  - Explicit cofactors (Macaulay lift, re-expanded and checked): 1.44M terms, 5.84M expanded products, denominators up
    to 368,640 (`cert_sizes.json`).
* **(V2′) rank one** [Proved]: `A_k^{(m)}A_0^{(0)} − A_k^{(0)}A_0^{(m)} ∈ (Q(X)) + (Q(Y))` for all 81 (k, m) (64 of them
  nontrivial). The normal form was computed in exact integers (`v2_all.out`; its messages say "NF(Q_j(A))", but the
  identity is V2′).
* **Completeness** [Proved]:
  - `J = (all 81 A_k^{(m)}) + I(X) + I(Y)` contains every form of bidegree (4,3), and also (4,4)
    (`completeness_runs.out`). It does not contain every form of bidegree (3,3) (rank 6400 of 6561).
  - The rank is computed mod p by weight blocks. A full rank mod p of a ℤ_(p)-matrix gives a full rank over ℚ. Here p
    is a prime of good reduction, the mod-p normal forms have the right dimension 9e², and the law denominators are
    powers of 2.
  - So the 9 laws are a complete system.
  - The 3-law subsets {0,3,4}, {0,4,7}, {0,1,4} are *not* complete at bidegree (4,4): ranks 14904, 15444 and 13788 of
    20736 (`subsets44.out`).
* **Size of a Nullstellensatz certificate for completeness.**
  - It would be `X_a⁴Y_b³ ∈ J` for a covering set of pairs (a, b), at least 9 identities.
  - Each has 81 cofactors of bidegree (2,1) (26,244 unknowns) plus ideal cofactors, about 10⁶ or more terms per
    identity [Heuristic].
  - **Not recommended**; see §A0.3.

### A0.3 Recommended Lean architecture for the genus-2 laws
1. **Data.**
   - The 45 polynomials, with `A_m^{(k)} := A_k^{(m)}(X, [−1]Y)` so that (S1) holds by definition.
   - The degree-4 normal-form table: 495 rows, ≤ 15 nonzero entries each, denominator 7680.
   - 351 small normal-form lemmas `X^μ ≡ NF(μ) mod (Q)`: 9.3k cofactor terms in total, ≤ 35 per lemma.
2. **Kernel checker** (normal form plus two-level Kronecker, Nat-only with sign-split pairs; `gen_lean_kron_nat.py`).
   - It computes `Σ_μ KX(μ)·Σ_{α+α′=μ} Σ c c′ KY(β+β′)` in the kernel and checks that it is 0. Here `KX`, `KY` are
     big-integer encodings of normal-form rows, with slot width bounded by the L1 norm (≈ 50 bits).
   - Nothing like a cofactor is stored.
   - A soundness framework is needed: the evaluator equals the encoded normal form; uniqueness of signed digits under
     the L1 bound; normal-form lemmas imply membership or vanishing on A × A. [Est 1.0–1.5k lines.]
3. **Big identities actually needed:**
   - V2′ for k, m ∈ 1…8: 64 identities;
   - V1 for law 0 only: 9 identities;
   - **G1**, law 0 against Cantor/Abel on an open subset of chart × chart, for the 4 Mumford coordinates.
     + Pulled back to the chart, law 0 has 160–722 terms per coordinate (`g1_proxy.py`), comparable with Cantor's
       88–695.
     + Est. ≈ 10⁵ term-pairs per identity [Heuristic, not measured].
   - The other 72 V1 identities are *not* needed: membership follows semantically once every law computes addition and
     `I_A` is a vanishing ideal.
4. **Semantic correctness and completeness** [Proved, paper level].
   - *Inputs*:
     + A3 gives an entire, nowhere-zero lift `θ : ℂ² → ℂ⁹` of `exp`, whose factor of automorphy is in normalised
       Appell–Humbert form `e_ω(z) = χ(ω)·exp(πH(z,ω) + (π/2)H(ω,ω))`, as for a symmetric `L`.
     + G1 plus the identity theorem give `A^{(0)}(θ(u), θ(v)) ∈ ℂ·θ(u+v)`; the 2×2 minors vanish on an open set,
       hence everywhere.
   - *The function ψ.* Let `N(u,v) = [A_k^{(m)}(θ(u), θ(v))]`.
     + Column 0 is `φ(u,v)·θ(u+v)`.
     + By (S1), row 0 is `c(v)^{−2}φ(u,−v)·θ_m(u−v)`, with `θ(−v) = c(v)[−1]θ(v)`.
     + By V2′, `N = ψ·θ(u+v)θ(u−v)ᵀ` on `{N₀₀ ≠ 0}`.
     + `ψ` is entire, because `θ` is nowhere zero.
   - *ψ is periodic.* The normalised factors give `e_ω(u+v)e_ω(u−v) = e_ω(u)²` and
     `e_ω(u+v)/e_ω(u−v−ω) = e_ω(v)²`. So `ψ` is Λ×Λ-periodic and, by Liouville on ℂ⁴, constant; it is nonzero because
     law 0 is nonzero somewhere.
   - *Conclusion.* Every law computes `P + Q` wherever it is nonzero. At each point some `θ_k(u+v)θ_m(u−v) ≠ 0`, so
     **the system is complete**. No Nullstellensatz certificate is needed. [+0.3–0.6k lines in A3]
5. **Prototype timing** (`lean_proto/TIMINGS.txt`), on V1(m=0, j=0) and V2′(4,7):
   - The Nat-only checker takes 38 s and 32 s per file, of which about 10 s is data elaboration. Kernel time is about
     22–28 s per identity, peak 3.3–4.0 GB. False claims are rejected.
   - The same checker with `Int` arithmetic took 65–120 s and up to 5.2 GB.
   - The naive list checker failed (see above).
   - Kernel throughput is about 0.8 ms per innermost term-product. That is interpretive overhead (a 20,000-step
     7-kbit Nat fold takes < 3 s), so further speed-ups are plausible [Heuristic].
6. **Extrapolation.**
   - Kernel time: 64 × 25 s + 9 × 35 s + G1 (4 × ~60 s, est.) ≈ 36 min.
   - Normal-form lemmas and data: ≈ 5–10 min.
   - Total ≈ 45–55 CPU-minutes, ≤ 4 GB per file. Data should be shared through one imported data file, and the
     identities split over about 8 files.

### A0.4 Genus 3 recommendation
* **Explicit P²⁶ laws.**
  - Each law has 27 × 216² = 1.26M nominal coefficients, about 90k after μ₁₄ weight sparsity, so about 3.3k terms per
    coordinate.
  - One product of two law coordinates is then about 10⁷ term-pairs, versus 1.2·10⁴ in genus 2.
  - V2′ needs about 676 identities. That makes about 10¹⁰ term-pairs, more than 10³ times genus 2 per identity
    [Heuristic extrapolation].
  - **No-go.**
* **Charts only** (Cantor on the Mumford chart, glued).
  - Correctness would be free from Abel (A2). But Philippon's `zeros(τ_g J) = zeros(J) − g` needs, for every `(x, g)`,
    some law of bounded bidegree that is defined there.
  - The Cantor chart misses `x ∈ Θ`, `x + g ∈ Θ` and the gcd locus. Gluing translated charts `A∖(Θ+c)` needs
    translations in P²⁶ coordinates.
    + These are linear only for `c ∈ A[3]` (Heisenberg), over ℚ(A[3]). Even then a covering is not guaranteed, since
      one point can lie on many `Θ + c`.
  - lean_lsg's gluing (Wüstholz transversals) glues derivations, not translation operators. So charts do **not**
    suffice for the ME as designed.
* **Recommendation for M3.**
  - Either theta-analytic (2,2) laws: existence through the level-3 theta addition formula and Koizumi, genus-generic,
    est. 10–20k. That would also make the genus-2 certificates (A1c) unnecessary.
  - Or postpone X7.
  - Decide after M1. The genus-3 ideal and local-CI data (single copy, 27 variables, 162 quadrics) are not the
    obstacle.

### A0.5 A0c: Bézout without a global complete intersection
* **Where lean_lsg uses it.**
  - `MainAb.lean:245–258` calls `StrongSix.M2.bezout blk D hD (height_slIG …) hFD` on
    `sl α A = Ideal.ofList lGs ⊔ span F₀`; MEV does the same at `MainVec.lean:286` and `MainVec4.lean:291`.
  - Inside `bezout` (StrongSix `M2/Bezout.lean`), the complete-intersection hypothesis is used only through
    `ofList_isUnmixed` (Macaulay, `CM/Unmixedness.lean`) at each chain step, and through `height_append`.
* **What breaks for an A-block.**
  - `sl α I_A` lives in 9 variables, with 13 generators (9 dehomogenised quadrics, 3 cubics, `ℓ − 1`) and height 7.
    It is not a global complete intersection, so `height_slIG` has no analogue.
  - Its ring is the coordinate ring of the smooth affine surface `A ∖ {ℓ = 0}`. **The non-CM cone vertex has already
    been removed by slicing.**
* **Why a CM-free top-dimensional Bézout does not help.**
  - The leading coefficient of `hfun(sl α A)` is `Σ_{𝔮 top-dim minimal} ℓ(A_𝔮/J_𝔮)·deg 𝔮`, i.e. it counts *lengths*.
    The Wüstholz lower bound (`wustholz_cosets_sl`) also counts lengths.
  - Length equals intersection multiplicity only where the ambient ring is CM. At non-CM points there is a genuine
    excess: for the cone over two skew lines, a generic codimension-2 linear section has length 3 > degree 2
    [standard].
  - So some form of CM at the top-dimensional components is unavoidable. In the sliced setting it holds because the
    slice is smooth; what is missing is a cheap proof. **Local complete intersection** is that proof.
* **Lemmas.** New files only: `StrongSix/M2/BezoutGen.lean`, or `LSG/ME/BezoutLCI.lean` and `LSG/Jac/LocCI*.lean`.

  | lemma | statement | reuses | est. |
  |---|---|---|---|
  | B1 `bezout_unmixed` | for `I₀` with `hU : ∀ l, ht(I₀ ⊔ ofList l) = ht I₀ + l.length → IsUnmixed (I₀ ⊔ ofList l)`, `F ⊆ FLE D`, `J = I₀ ⊔ span F ≠ ⊤`: `(hdata J).2 ≤ (hdata I₀).2` | StrongSix `bezout` proof verbatim with `rs ↦ I₀ ⊔ ofList rs`: `exists_avoid_span`, `hdim_of_height`, `nzd_of_not_mem_ass`, `hfun_section`, `HasData.of_le_Δ`, `hdata_le_of_le`; generalise `height_append` | 250–400 |
  | B2 `LocCI`, `isUnmixed_of_locCI` | `LocCI J :≡ ∀ 𝔪 ⊇ J maximal, ∃ s ∉ 𝔪, ∃ l, ofList l ≤ J ∧ s•J ≤ ofList l ∧ l.length = ht J`; then `J` is unmixed | CM lib: `MvPolynomial.isCM_of_isCM`, `localize_at_prime_isCohenMacaulay_of_isCohenMacaulay`, `isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing`, `associated_prime_eq_minimalPrimes_isCohenMacaulay`, `quotient_regular_isCohenMacaulay_iff_isCohenMacaulay`; associated primes under localisation (Mathlib; ≈150 l. if missing) | 400–700 |
  | B3 `locCI_sup_ofList`, `hU_of_locCI` | `LocCI J`, heights add ⇒ `LocCI (J ⊔ ofList Ps)` (use `l ++ Ps`), hence `hU` for B1 | B2 | 100 |
  | B4 `locCI_blocks` | block ideals in disjoint variables: `LocCI` each ⇒ `LocCI` of the sum, `ht(Σ J_k) = Σ ht J_k` | `hdim_add_height_eq`, SliceIG product bounds, Krull `Ideal.height_le_card_of_mem_minimalPrimes_span_finset` | 300–500 |
  | B5 `locCI_slA` | the A-block slice is LocCI | certificates below + `Slice.hom_mem_vanish_of_mem_sl`, `SliceDim.homP` (dehomogenisation) | 300–600 + data |
  | B6 `hfun_slA_le`, `hdata_slA` | `H(sl α I_A; t) ≤ 9(tD)² + O(t)` (any constant times `t²` suffices); `hdim = 2` | generic standard-monomial lemma generalising `SliceIG.hfun_slIG_le`; a Gröbner basis of `I_A`; Krull for `hdim ≥ 2` | 400–700 |
  | B7 MainAb adaptation | `height_slIG` + `bezout` ↦ B1 + `hU` from B2–B5; extra constant `18^r`-type in `CstAb` | inside the A4 BlockData refactor | 100–200 |
  | **total** | | | **1.9–3.2k** |

* **B5 certificates** (`loc_ci_modp.py`, [Numerical mod p]).
  - For 6 random integer combinations `F` of the quadrics, the colon `((F) : I_A)` contains **cubics `S ∉ I_A`**: in
    degree 3 the colon has dimension 55, with 2 basis vectors not vanishing on J.
  - Where `S(a) ≠ 0`, the 6 forms `F` generate `I_A` locally, so the slice is a local complete intersection at `a`.
  - Per choice of `F`:
    + `S·Q_j ∈ (F)` in degree 5 for the 3 complementary quadrics, and `S·C_j ∈ (F)` in degree 6 for the 3 cubics;
    + cofactors of degree 3–4, single copy, 9 variables.
  - With about 3 choices, plus a single-copy Nullstellensatz certificate that the chosen `S_i` have no common zero on
    `A`, the total is ≲ 5·10⁴ terms [Heuristic].
  - Alternative B5′: local rings via translation into the Mumford chart, which is a global complete intersection
    `ℚ[s₁,s₂,b₁,b₀]/(r₁,r₀)`; CM of complete intersections is in StrongSix. No certificates, but 1.5–2.5k lines of
    homogeneous-localisation work. Not preferred.

### A0.6 Revised estimates (replace the corresponding rows of §5)
| stage | was | now | change |
|---|---|---|---|
| A1 Jacobian algebra (Mumford, Cantor, P⁸ model, boundary, `[ζ]`) | 4–7k | 5–8k | the model is explicit and small (above); law data 4.2k terms (S1); `Dup` 321 terms |
| **A1c (new)** law certificates: kernel checker + soundness, 351 normal-form lemmas, V2′ (64), V1 law 0 (9), G1 (4), V3 | — | 1.5–2.5k + generated data; ≈ 45–55 CPU-min, ≤ 4 GB per file | measured prototype |
| A2 analytic `exp` | 8–14k | 8–14k | also: law 0 equals analytic addition (G1 + Abel + identity theorem) |
| A3 order 2 | 2–5k | 2.5–5.5k | plus the ψ-Liouville correctness/completeness argument; A3 must deliver normalised factors of automorphy |
| A4 BlockData + Jacobian block + Bézout + subgroup layer | 20–30k | 20–30k | Bézout layer = local-CI Bézout B1–B7 (1.9–3.2k) instead of "top-dimensional Bézout" |
| **M1 total** | 45–70k | **≈ 47–73k** | |
| A8 genus 3 + X7 | 25–45k | 35–65k, or postpone | explicit laws no-go; theta-analytic laws +10–20k (genus-generic, could also retire A1c) |

**Risk updates.**
* R-laws3 is confirmed and sharpened (§A0.4).
* R-Bezout is downgraded: the ingredients exist in StrongSix's CM library, and the plan is concrete.
* New: **R-kernel**. The kernel checker's soundness framework and throughput (0.8 ms per term-product today) are the
  A1c risk. The measured margin is about 1 h.
* **R-G1**: the chart identity law 0 = Cantor has not been measured.

## Risk-list update (2026-10-31)
**R-Prop21 is now the top risk.** Tier-3 W83 Prop 2.1 needs Masser's Theorem A (several-variable interpolation on lattice
points); see `STAGE_A5_PROP21.md` and PLAN.md "ABVAR risk update". A5 estimate: 10–14k + research risk (was 5–8k); M1 ≈ 55–85k.
Mitigations in progress: §4.2 finite check / §4.1 Ω′-adapted forms for the concrete targets; §4.3 conditional layer.
