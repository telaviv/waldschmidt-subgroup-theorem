# STAGE A3: the theta lift, order 2, and correctness/completeness of the 81 laws (genus 2, `y² = 4x⁵ + 1`)

Status 2026-10-31: plan and paper proofs (this file). **A3.1 done [Proved]**: `LSG/JacAn3/Theta.lean` (306 lines).
* Main results: `exists_thetaData`, `ThetaData.theta`, `theta_eq`, `analyticAt_theta`, `theta_ne_zero`, `theta_onQ`,
  `expP_eq_theta`.
* **`theta_two_smul`**: `θ(2z) = e^{−p₂(z)} • dup(θ z)`.
* Standard axioms plus `A1Facts`; no new field was needed. Builds on A2 checkpoint 6 (lean_lsg 152889c):
* `expP G : ℂ² → ℙ⁸`;
* `Λ = ⟨perVec e⟩ ⊆ ker E`, discrete, rank 4;
* `expP_base_indep`.

Scope (coordinator, after checkpoint 6):
1. An entire, nowhere-zero lift `θ` with a normalised factor of automorphy, and order-2 growth.
2. ψ-Liouville: correctness and completeness of the 9 laws, then untranslated surjectivity.
3. What the auxiliary function needs (`QuasiPeriodicB`, algebraic Taylor coefficients).

Labels: [Proved] = in Lean; [Proof] = complete paper proof, written here; [Plan] = design; [Est] = line estimate.

**Verdict in brief.**
* Nothing essential is missing for (1) or for (2) on the image `E(ℂ²)`. Mathlib v4.35 has:
  - several-variable Liouville (`Differentiable.apply_eq_apply_of_bounded`, for any normed `E`);
  - Borel–Carathéodory (`Complex.borelCaratheodory`, new in 2026);
  - Cauchy estimates (`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`);
  - Taylor series of entire functions (`Complex.taylorSeries_eq_of_entire`);
  - Poincaré's lemma on convex sets (`exists_forall_hasFDerivAt_of_fderiv_symmetric`).
* **The a7 degree-2 resonance is not an obstacle.** The resonant quadratic term is *forced to vanish* by periodicity
  plus P2 (§1.4). The proof needs no theta functions and no `H¹(Λ, 𝒪)` computation.
* Item (2) on all of `V(Q)` (untranslated surjectivity onto *every* model point, including the boundary `X₀ = 0`)
  needs an algebraic input that is not yet in Lean (§2.5).
* New `A1Facts` fields are needed, all already proved by A1 or trivial for A1 (§4).

---------------------------------------------------------------------------------------------------------------------

## 1. The lift θ, its factor of automorphy, order 2 [Proof]

Notation:
* `Ẽ_k(z) = dupᵏ(germ(z/2ᵏ))` on `B_k = ball(0, 2ᵏε)` (A2 `expLift`).
* `d(v) = dup(germ v)₄`, which is nonzero on `ball(0, ε)` (`GermRad.good`), with `d(0) = c ≠ 0` (`dup_origin`).
* `expLift_succ`: `Ẽ_{k+1}(z) = d(z/2^{k+1})^{4ᵏ} Ẽ_k(z)`.

### 1.1 Construction without limits (the coboundary trick)

On a smaller ball `ball(0, ε₁)`, `d(v)/c` lies in the slit plane, so `ℓ(v) := log c + Log(d(v)/c)` is analytic and
`e^ℓ = d`.
* Let `p = Σ p_n` be its power series at 0, with radius `≥ r > 0` (`HasFPowerSeriesOnBall`), and write `p₂(z) = p 2 (z, z)`.
* Define the formal series `G := Σ_{n ≠ 2} p_n / (4 − 2ⁿ)`.
  - Its coefficients are no larger than those of `p`, since `|4 − 2ⁿ| ≥ 1` for `n ≠ 2`.
  - So `G` is analytic on `ball(0, r)`.
* The coefficient identity `4G(w) − G(2w) = ℓ(w) − p₂(w)` holds for `|2w| < r`.

Put `Φ_k(z) := 4ᵏ G(z/2ᵏ) + (k/4) p₂(z)`. Then `Φ_{k+1}(z) − Φ_k(z) = 4ᵏ ℓ(z/2^{k+1})`, and

  **`θ(z) := Ẽ_k(z) · exp(−Φ_k(z))`** for any `k` with `z/2ᵏ ∈ ball(0, min(ε₁, r/2))`

is independent of `k`, exactly as for `expP`. Consequences:
* `θ` is analytic everywhere (on each ball it is a product of analytic maps).
* `θ` is nowhere zero (`expLift_ne_zero`).
* `θ(z)` lies on the model (`OnQ`).
* `[θ(z)] = E(z)`.

**Doubling equation.** `Ẽ_{k+1}(2z) = dup(Ẽ_k(z))` by definition. Together with `dup(aX) = a⁴ dup X`:

  **`θ(2z) = e^{−p₂(z)} · dup(θ(z))`**.

The constant and linear Taylor terms of `ℓ` are absorbed exactly. Only the resonant quadratic term `p₂` survives:
this is the a7 resonance, `2² = 4`.

[Est] 0.5–0.7k (`JacAn3/Theta.lean`).

### 1.2 The factor of automorphy

For `ω ∈ Λ`, `E(z + ω) = E(z)` (`expP_periodic_perVec`). Both `θ(z+ω)` and `θ(z)` are nonzero, so
`θ(z + ω) = e_ω(z) θ(z)` with a unique scalar `e_ω(z)`.
* `e_ω` is entire: locally it is `θ_k(z+ω)/θ_k(z)` for a coordinate `k` with `θ_k(z₀) ≠ 0`.
* `e_ω` is nowhere zero.
* Cocycle: `e_{ω+ω'}(z) = e_ω(z+ω') e_{ω'}(z)`.
* Doubling, from §1.1: `e_{2ω}(2z) = e^{−p₂(z+ω)+p₂(z)} e_ω(z)⁴`.

**Logarithm.** By Poincaré's lemma on the convex set `ℂ²`, applied to the closed holomorphic 1-form `de_ω/e_ω`, there
is an entire `f_ω` with `e^{f_ω} = e_ω`. In Mathlib the lemma is real; the primitive is ℂ-differentiable because its
derivative is ℂ-linear.

[Est] 0.3–0.45k.

### 1.3 Two-sided growth (this is where P2 enters)

Let `h(z) := log ‖θ(z)‖` (sup norm), which is continuous.
* By P2 (`dup_ne_zero` on `V(Q)`) and compactness of `S = V(Q) ∩ {‖X‖ = 1}`, there are `0 < δ ≤ C` with
  `δ‖X‖⁴ ≤ ‖dup X‖ ≤ C‖X‖⁴` on `V(Q)`. Compactness needs `V(Q)` closed: new field `onQ_closed`, which is trivial
  from A1's `onQ_iff`.
* With §1.1 this gives `|h(2z) − 4h(z) + Re p₂(z)| ≤ C₀`.
* `h` is bounded on the unit ball. Dyadic iteration then gives

  **`|h(z)| ≤ K (1 + ‖z‖)² (1 + log(1 + ‖z‖))`** for all `z`. This is two-sided, and is the point of P2.
* Hence `|Re f_ω(z)| = |log|e_ω(z)|| = |h(z + ω) − h(z)| ≤ K_ω (1 + ‖z‖)² log(2 + ‖z‖)`.

[Est] 0.3–0.4k.

### 1.4 `f_ω` is affine, and the resonance vanishes

**Lemma RP (several variables).** Let `f` be entire on `ℂ²` with `|Re f(z)| ≤ M(‖z‖)` and `M(R)/R³ → 0`. Then
`f(z) = f(0) + Df(0)z + ½D²f(0)(z, z)`.
* Proof on each line `g(t) = f(tz)`:
  - Borel–Carathéodory on `ball(0, R)` bounds `‖g‖ ≤ 2M(R) + 3|g(0)|` on `ball(0, R/2)`.
  - The Cauchy estimate gives `|g⁽ⁿ⁾(0)| ≤ n!(2M(R) + 3|g(0)|)/(R/2)ⁿ → 0` for `n ≥ 3`.
  - `taylorSeries_eq_of_entire` then gives `g(t) = g(0) + g′(0)t + g″(0)t²/2`.
* The line derivatives are identified with `iteratedFDeriv f 0` by `ContinuousLinearMap.iteratedFDeriv_comp_right`.
* [Est] 0.3–0.5k.

So `f_ω(z) = Q_ω(z) + L_ω(z) + c_ω`: quadratic, plus linear, plus constant.

**Cocycle mod 2πi.**
* The defect `f_{ω+ω'}(z) − f_ω(z+ω') − f_{ω'}(z)` is a polynomial `D` with `e^D ≡ 1`. Hence `D′ = 0`, so `D` is a
  constant in `2πiℤ`.
* Comparing degrees:
  - `Q_{ω+ω'} = Q_ω + Q_{ω'}`;
  - `L_{ω+ω'} = L_ω + L_{ω'}`;
  - `c_{ω+ω'} ≡ c_ω + c_{ω'} + L_ω(ω') (mod 2πi)`.

**Doubling (§1.2), compared degree by degree.** Write `P(z) = −p₂(z)` and `β(z, ω) = p₂(z+ω) − p₂(z) − p₂(ω)`, which is
ℂ-bilinear.
* Degree 2: `4Q_{2ω} = 4Q_ω`. Additivity gives `Q_{2ω} = 2Q_ω`. So **`Q_ω = 0`**.
* Degree 1: `2L_{2ω} = 4L_ω − β(·, ω)`. Additivity gives `L_{2ω} = 2L_ω`. So **`β(·, ω) = 0` for all `ω ∈ Λ`**.
  - `β(z, ·)` is ℂ-linear and vanishes on `Λ`, which spans `ℂ²` over ℝ. So `β = 0`, hence `p₂(z) = ½β(z, z) = 0`.
  - **The resonant term is zero.** So `θ(2z) = dup(θ(z))` and
    `|h(2z) − 4h(z)| ≤ C₀`, which gives **`log‖θ(z)‖ ≤ c‖z‖² + C`** (order 2, the upper bound).
* Paper check: for a genuine theta function, `ℓ = −log c + log θ₄(2v) − 4 log θ₄(v)`, so `ℓ₂ = (4 − 4)a₂ = 0`.
  This is consistent, and the argument above proves it without theta functions.

So **`f_ω(z) = L_ω(z) + c_ω`**, with `L : Λ → (ℂ²)*` additive. Extend `L` ℝ-linearly through the ℝ-basis
`perVec 0..3`.

### 1.5 Normalisation

**Integrality.** Comparing `c_{ω+ω'}` with `c_{ω'+ω}` gives `L_ω(ω') − L_{ω'}(ω) ∈ 2πiℤ`.

**The ψ-sufficient normalisation.** Put `φ(ω) := ½ Re(L_ω(ω) − 2c_ω)`.
* By integrality, `φ` is additive on `Λ`.
* Extend `φ` ℝ-linearly and set `λ(x) := φ(x) − iφ(ix)`, which is ℂ-linear with `Re λ = φ`.
* Replace `θ` by `θ e^{λ}`. Then:
  - `L` is unchanged and `c_ω ↦ c_ω + λ(ω)`;
  - the doubling equation becomes `θ(2z) = e^{−λ(z)} dup θ(z)` (sign aside), which is harmless for growth.

**Normalised factor (N):** `e_ω(z) = exp(L_ω(z) + c_ω)` with `Re(2c_ω − L_ω(ω)) = 0`.

**Equivalence with Appell–Humbert [Proof sketch].**
* Write `L_ω(z) = M(z, ω) + πH(z, ω)`, where `M` is ℂ-bilinear and `H` is ℂ-linear in `z` and conjugate-linear in `ω`.
* Integrality makes `E(ω, ω') = (L_ω(ω') − L_{ω'}(ω))/2πi` real and alternating. The ℂ-bilinear component of `2πiE` is
  the antisymmetric part of `M`, and `2πiE ∈ iℝ` has no conjugate-bilinear component, so `M` is symmetric. The
  alternating property forces `H` to be hermitian.
* `M` is removed by `θ ↦ θ e^{−M(z,z)/2}`. Then `c_ω = (π/2)H(ω, ω) + log χ(ω)` with `|χ| = 1` and
  `χ(ω+ω') = χ(ω)χ(ω')(−1)^{E(ω,ω')}`.
* This is exactly `e_ω(z) = χ(ω) exp(πH(z, ω) + (π/2)H(ω, ω))`.
* **Optional**: (N) is all that ψ and the auxiliary function use. [Est] (N) 0.3–0.4k; full Appell–Humbert +0.3–0.5k.

**Bounds delivered.**
* `|L_ω(z)| ≤ K‖ω‖‖z‖`.
* `|Re c_ω| = ½|Re L_ω(ω)| ≤ K‖ω‖²`.
* Hence **`|e_ω(z)| ≤ exp(K(‖z‖ + ‖ω‖)²)`**, the `QuasiPeriodicB` multiplier bound, together with
  `‖θ(z)‖ ≤ e^{c‖z‖² + C}`.

---------------------------------------------------------------------------------------------------------------------

## 2. ψ-Liouville: correctness and completeness of the 81 laws [Proof on `E(ℂ²)`; Plan for `V(Q)`]

Notation:
* `N_{km}(u, v) := A32 k m (θ(u), θ(v))` for `u, v ∈ ℂ²`, an entire function on `ℂ⁴`. Law `m` is `(N_{km})_k`.
* A1 [Proved]:
  - `rank_one`: `N_{km}N_{00} = N_{k0}N_{0m}` on `V(Q)²`;
  - `law_S1`: `A32 k m (X, [−1]Y) = A32 m k (X, Y)`;
  - `law0 = A32 · 0`, `dup X = A32 · 4 (X, X)`, and bihomogeneity of bidegree (2, 2).

### 2.1 Column 0 and row 0
* **Untranslated homomorphism.** `law0(θu, θv) ∥ θ(u+v)`.
  - This is A2's `hom_trans` argument with `Y = θ(v)`, `θ(v)₀ ≠ 0` (`PF0_law0_expLift`, anchored at
    `law0(e₄, Y) ∝ Y`), then the identity theorem in `v`.
  - Hence `N_{k0} = φ(u, v) θ_k(u+v)` with `φ` entire. [Est] 0.2–0.3k.
* **`[−1]`.** `negP θ(v) = c(v) θ(−v)`, `c` entire and nowhere zero.
  - Route a: `flowW j (negP X) = −negP(flowW j X)`, checked by hand on A2's explicit `flowW`. With a new field
    `W4_negP` (the same for `W4`, a data identity A1 can check trivially), `v ↦ negP germ(−v)` solves the chart-4 flow
    with value `e₄`, so it equals `germ` (`flow_unique`).
  - Route b, with no new field: the general inversion `Ẽ(a) ∥ law0(Ẽ(a+b), negP Ẽ(b))`. This is A2's `inv_trans` at a
    base `b`, extended to all `b` by `expP_base_indep` and the identity theorem; then put `a = −v`, `b = v`.
  - [Est] 0.1–0.3k.
* **Row 0.** By S1, `N_{0m}(u, v) = law0(θu, negP θv)_m = c(v)² φ(u, −v) θ_m(u − v)`.

### 2.2 ψ
* `N_{00} = φ θ₀(u+v) ≢ 0`:
  - `φ ≢ 0` because `law0(X, e₄) = −8X₀X` (A1 `law0_origin`), and `θ₀ ≢ 0` (e.g. at the A2 base point);
  - analytic functions on connected `ℂ⁴` form a domain.
* On the dense open set `{N_{00} ≠ 0}`, `rank_one` gives `N = ψ θ(u+v) θ(u−v)ᵀ`.
* Define `ψ(u, v) := N_{km}/(θ_k(u+v)θ_m(u−v))` for any `(k, m)` with a nonzero denominator. The cross-identities hold
  on a dense set, hence everywhere, so `ψ` is a well-defined entire function on `ℂ⁴`.

### 2.3 |ψ| is Λ×Λ-periodic, so ψ is constant
Bihomogeneity gives `N(u+ω, v) = e_ω(u)² N(u, v)` and `N(u, v+ω) = e_ω(v)² N(u, v)`. So
* `ψ(u+ω, v) = ψ · e_ω(u)² / (e_ω(u+v) e_ω(u−v))`, which has modulus 1 because `f_ω` is affine;
* `ψ(u, v+ω) = ψ · e_ω(v)² / (e_ω(u+v) e_{−ω}(u−v))`, which has modulus `exp Re(L_ω(ω) − 2c_ω) = 1` by (N).

Use the compact fundamental domain `F = {Σ tᵢ perVec i : t ∈ [0,1]⁴}` (every `z = f + ω`). Then `|ψ|` is bounded by its
maximum on `F × F`, and Liouville on `ℂ⁴` (`apply_eq_apply_of_bounded`, `E = ℂ² × ℂ²`) makes `ψ ≡ κ`. `κ ≠ 0` because
`N₀₀ ≢ 0`.

### 2.4 Conclusions on the image
`A32 k m (θu, θv) = κ θ_k(u+v) θ_m(u−v)` for all `u, v`. Therefore:
* **Correctness**: law `m` at `(E(u), E(v))` is `κθ_m(u−v) · θ(u+v)`. Wherever it is nonzero it represents
  `E(u+v)`.
* **Completeness**: some `θ_k(u+v)θ_m(u−v) ≠ 0`, so at every pair of image points some law is nonzero.
* By-products: a complete addition law on `E(ℂ²)`, untranslated (`E(u) ⊕ E(v) = E(u+v)`); `dup` computes `[2]`;
  A2's `surj_trans` loses its `hT`.

[Est] §2.1–2.4: 0.7–1.0k.

### 2.5 Untranslated surjectivity onto the model points [Plan; partly blocked]
* **(a) Generic affine points** (Mumford divisors `D = P₁ + P₂` with `x₁ ≠ x₂` and `y_i ≠ 0`).
  - A2's `surj_trans` plus §2.4 give `[grantJ D] = E(c)` for every `D` reachable from the base by a generic path.
  - Still missing: path-connectedness of the generic locus of `C × C`. This is curve topology: the double cover
    `x : C_aff ∖ {y = 0} → ℂ ∖ {roots}` is connected because the monodromy around a root swaps the sheets.
  - [Est] 0.5–1k.
* **(b) Every point of `V(Q)`.** `E(ℂ²)` is compact, so it suffices that generic chart points are dense in `V(Q)`
  (projectively). That statement is algebraic. Two A1 options:
  - (i) "affine part of `V(Q)` = image of the Mumford chart" (STAGE_A1 §3 lists it as not yet in Lean), plus an
    explicit description of the boundary `X₀ = 0` as the classes of degree `< 2` (the curve `Θ`), plus a local limit
    computation;
  - (ii) the inversion identity V3, `X ∥ law0(law0(X, Y), [−1]Y)` on `V(Q)²` where nonzero, plus a nonvanishing
    argument at boundary `X`.
  - **This is the one place where something essential is missing in Lean.** It does not block (1), (2a) or (3).
    [Est] 1–2k (A3) + an A1 certificate.

---------------------------------------------------------------------------------------------------------------------

## 3. What the auxiliary function needs [Plan]

1. **Quasi-periodicity.** `QuasiPeriodicB` (`Prop21.lean`) is stated for the coordinate lattice `ℤ^κ × 0`, but `Λ` is
   not of that shape (the A-block is ℂ-indecomposable). The A-block uses `prop21Gen_of_interp`
   (`Prop21Gen.lean`, Tier 3, conditional on `LemmaLInterp`), whose hypothesis is
   `ψ_l(z + Σkᵢωᵢ) = m ψ_l(z)` with `|m| ≤ exp(b(|z| + |ω|)²)`.
   - For `ψ_l` = monomials of degree `D` in the `θ` coordinates (times the other blocks' factors), `m = e_ω(z)^D`, and
     §1.5 gives `b = DK`.
   - Deliverable: `theta_quasiPeriodic` in exactly the Prop21Gen hypothesis shape, plus `‖θ(z)‖ ≤ e^{c‖z‖²+C}` (the
     growth hypothesis `Σ‖ψ_l‖ ≤ e^U` on `B_R`). [Est] 0.1–0.2k.
2. **Algebraic Taylor coefficients.**
   - The aux function uses `θ_l/θ_0` (affine Grant coordinates) along algebraic directions at the points of `Y`. By §2.3
     of ABVAR these lie in `(1/M)Ω_A`, so `E(sy) ∈ A[M]`.
   - Source: the chart-0 flow (A2 `PF0_expLift`, N1). `∂_j(X_l/X_0)` is a quadratic polynomial in `X/X₀` with
     ℚ-coefficients (`flowW` is explicit). This is the analogue of `ks_wpSeries` (`WpSeries.lean`): coefficients in
     `K = ℚ(E(sy), directions)` with `house ≤ A Bʲ`, denominators `E(E²)ʲ j!`.
   - At points with `X₀ = 0`, use the chart-4 flow `W4` (A1 data).
   - [Est] 0.6–1.0k (a KS-recursion for a 9-dimensional quadratic ODE).
3. **Algebraicity of `A[M]`.** The points `E(ω/M)` must have algebraic coordinates. Three routes:
   - (i) `[M]X = O` is a finite ℚ-system (finite by discreteness of `ker E`, `M⁴` points), and a finite algebraic set
     over ℚ has algebraic points (Aut(ℂ/ℚ)-orbit or elimination argument);
   - (ii) explicit for CM (`[1 − ζ]`-torsion);
   - (iii) restrict `Y` to `Λ` itself (`E = O`).
   - [Est] 0.5–1.5k depending on the route. This belongs to A5/A6, not A3.

---------------------------------------------------------------------------------------------------------------------

## 4. New `A1Facts` fields needed by A3

| field | statement | A1 status |
|---|---|---|
| `lawK` | `Fin 9 → Fin 9 → P9 → P9 → ℂ` (`= A32`), with `law0 X Y k = lawK k 0 X Y` and `dup X k = lawK k 4 X X` | definitional (`dup = lawPt 4 x x`) |
| `lawK_S1` | `lawK k m X (negP Y) = lawK m k X Y` | **proved** (`law_S1`) |
| `rank_one` | `OnQ X → OnQ Y → lawK k m X Y * lawK 0 0 X Y = lawK k 0 X Y * lawK 0 m X Y` | **proved** (`V2.lean`) |
| `lawK_smul_left/right` | bidegree (2, 2) | trivial (homogeneous data) |
| `lawK_analytic` | analytic in `(X, Y)` | glue |
| `onQ_closed` | `IsClosed {X | OnQ X}` | trivial from `onQ_iff` |
| `W4_negP` (optional, route a of §2.1) | `W4 j (negP X) = −negP (W4 j X)` | data check |

P2 (`dup_ne_zero`) is used essentially in §1.3, for the lower bound `‖dup X‖ ≥ δ‖X‖⁴`. Without it the two-sided growth
fails and the resonance argument of §1.4 does not start. P3 (`special_hP₀`) is used through `Λ ⊆ ker E`.

## 5. Plan and estimates

| step | file (new, `LSG/JacAn3/`) | content | [Est] |
|---|---|---|---|
| A3.1 | `Theta.lean` | `ℓ`, `G`, `Φ_k`, `θ`, `k`-independence, analytic, nowhere zero, `[θ] = E`, doubling | 0.5–0.7k |
| A3.2 | `Factor.lean` | `e_ω`: existence, analyticity, cocycle, doubling; `f_ω` (Poincaré) | 0.3–0.45k |
| A3.3 | `Growth.lean` | dup two-sided bound (P2 + `onQ_closed`), dyadic lemma, `|h| ≤ K(1+‖z‖)²log` | 0.3–0.4k |
| A3.4 | `PolyGrowth.lean` | Lemma RP (Borel–Carathéodory + Cauchy + Taylor; lines) | 0.3–0.5k |
| A3.5 | `Normal.lean` | cocycle algebra: `Q = 0`, `p₂ = 0`, `L` additive and ℝ-linear, (N), bounds, order 2 | 0.4–0.6k |
| A3.6 | `PsiLiouville.lean` | `lawK` interface, untranslated hom, `[−1]`, `ψ`, periodicity, Liouville, correctness/completeness on `E(ℂ²)` | 0.7–1.0k |
| A3.7 | `AuxQP.lean` | `theta_quasiPeriodic` in Prop21Gen shape, growth | 0.1–0.2k |
| **A3 core (1)+(2) on the image + (3.1)** | | | **2.6–3.85k** |
| A3.8 | `Surj.lean` | §2.5(a): generic affine points (curve topology) | 0.5–1k |
| A3.9 | — | §2.5(b): all of `V(Q)`; needs an A1 certificate | 1–2k + A1 |
| optional | `AppellHumbert.lean` | full `χ, H` form | 0.3–0.5k |
| later (A5/A6) | — | Taylor-coefficient KS recursion (§3.2), algebraicity of `A[M]` (§3.3) | 1.1–2.5k |

Order: A3.1 → A3.2 → A3.3 → A3.4 → A3.5 → A3.7 → A3.6 → A3.8. A3.1–A3.5 use only the current `A1Facts` (plus
`onQ_closed`); A3.6 needs the §4 fields.

Risks:
* (R1) Lemma RP's line-to-`iteratedFDeriv` bookkeeping. Mitigation: work with `iteratedDeriv` of `t ↦ f(tz)` and
  recover `D²f(0)` from polarisation.
* (R2) Poincaré's lemma is stated over ℝ, so ℂ-linearity must be transferred. Fallback: build `f_ω` along rays,
  `f(z) = log e(0) + ∫₀¹ De(tz)z/e(tz) dt`, with differentiation under the integral.
* (R3) §2.5(b) depends on A1.

---------------------------------------------------------------------------------------------------------------------

## 6. Checkpoint A3-2 (2026-10-31): A3.2–A3.5 and A3.7 [Proved]

Everything builds with light builds. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for:
* `p2_eq_zero`, `theta_two_smul'`, `fac_affine`, `Lf_add`;
* `norm_facN`, `facN_bound`, `thetaN_order2`, `thetaN_monomial_qp`;
* `quadExp_of_growth`, `growth_dyadic`.

No `sorry` and no `native_decide`. The only hypothesis is `A1Facts` (P2 is used in A3.3, P3 through `Λ ⊆ ker E`).

| file (`LSG/JacAn3/`) | lines | content |
|---|---|---|
| `Factor.lean` (A3.2) | 133 | `IsPer`; `fac`; `fac_spec`: `θ(z+c) = fac c z • θ z`; `analyticAt_fac`; `fac_add` (cocycle); `fac_two` (doubling) |
| `Growth.lean` (A3.3) | 234 | `dup_bounds` (`δ‖X‖⁴ ≤ ‖dup X‖ ≤ C‖X‖⁴` on `V(Q)`); `dyadic_bound`, `dyadic_bound₀`; `growth_dyadic`; `fac_growth_dyadic` |
| `PolyGrowth.lean` (A3.4) | 199 | `quad_of_re_dyadic` (Borel–Carathéodory + Cauchy + Taylor); **`quadExp_of_growth`** |
| `Normal.lean` (A3.5a) | 254 | `fac_quad`, `homog_exp_one`, `cocycle_parts`, `doubling_parts`; **`Mb_diag_zero`**, **`Lf_add`**, **`p2_eq_zero`**; `theta_two_smul'`, `fac_affine`; `latBasis` |
| `Normalize.lean` (A3.5b) | 231 | `latt`; `Lext`, `PhiN`, `lamN`; **`thetaN`** (entire, nowhere zero, `[θ_N] = E`); `thetaN_add`; **`norm_facN`**; **`facN_bound`**; **`thetaN_order2`** |
| `AuxQP.lean` (A3.7) | 47 | **`thetaN_monomial_qp`**: degree-`D` monomials in `θ_N` share the multiplier `facN^D`, with bound `exp(D b (‖z‖+‖c‖)²)` (the Prop21Gen hypothesis shape) |

Notes on the files:
* `quadExp_of_growth` needs no several-variable logarithm. It uses one-variable logs along the lines `t ↦ g(tz)`, and
  identifies the coefficients through `fderiv` and `fderiv ∘ fderiv` at 0. This makes Poincaré's lemma (risk R2)
  unnecessary.
* `Normal.lean` turns §1.4 into Lean exactly as on paper.
  - The cocycle and the doubling relation are compared through `homog_exp_one`.
  - `M_c(z,z) = 0` follows from `M_{2c} = M_c` (doubling) together with `M_{2c} = 2M_c` (cocycle).
  - Then `L` is additive and `p₂(z,c) + p₂(c,z) = 0` for every period `c`.
  - `p₂ = 0` follows because the four periods form an ℝ-basis of `ℂ²` (`latBasis`).
* `Normalize.lean`: (N) is stated as `‖facN c z‖ = exp(½ Re L_c(c) + Re L_c(z))`, which is exactly what §2.3 uses.
  Full Appell–Humbert (`χ`, `H`) was not formalised (optional).

**A1Facts batch (added this checkpoint; it breaks `A1FactsInst` until A1 updates `mkA1Facts`):**
* `onQ_closed`, `negP_eq`, `lawK`, `law0_lawK`, `lawK_S1`, `rank_one`, `lawK_smul_left/right`, `lawK_analytic`,
  `W4_negP`.
* They are listed in STAGE_A2 §7.
* Only `onQ_closed` is used so far (A3.3). The rest are for A3.6.

### 6.1 A3.6 design refinements (next)
* **`Θ₀ ≢ 0`** (needed for `N₀₀ ≢ 0`). If `θ_N(z)₀ ≡ 0`, then on the germ ball `germ₀ ≡ 0`. `PF0_expLift` then
  gives `flowW 0 (germ v) 4 = 6 germ₁(v)² = 0`, so `germ₁ ≡ 0` near 0. Hence `W4 j e₄ 1 = 0` for `j = 0, 1`
  (derivative at 0), contradicting `W4_origin_indep`. Then `N₀₀(u, 0) = −8a²Θ₀(u)² ≢ 0`, using `Θ(0) = a e₄` and
  `law0_origin`.
* **Untranslated homomorphism.** Generalise A2's `hom_trans_near` from the second argument `Ψ(z₀ + w)` to any
  chart-0 projective flow solution `Y(w)` with `Y(w₁)₀ ≠ 0`, here `Y = Ẽ_k` near a `w₁` with `Θ(w₁)₀ ≠ 0`. Then
  `par_of_eventually` on the connected domain, as in `hom_trans`. [Est] 0.2–0.3k.
* **`[−1]`** via `W4_negP`, `negP_eq` and `flow_unique` on the germ.
* **ψ without patching.** The cross identity `N_km Θ_k′Θ_m′ = N_k′m′ Θ_kΘ_m` holds wherever `N₀₀ ≠ 0`, by the
  algebraic consequence of `rank_one`. The identity theorem plus `N₀₀ ≢ 0` then gives it everywhere. Define
  `ψ = N_{k₀m₀}/(Θ_{k₀}Θ_{m₀})` with `k₀, m₀ = nzIdx`, which is locally a fixed quotient, hence entire.
* Periodicity of `|ψ|` from `norm_facN` and `L_{−c} = −L_c`; boundedness via the fundamental domain of `latBasis`;
  Liouville on `ℂ² × ℂ²`.

---------------------------------------------------------------------------------------------------------------------

## 7. Checkpoint A3-3 (2026-10-31): A3.6 ψ-Liouville [Proved]

**Result.** The 81 laws on `E(ℂ²)` are correct and complete:
* `lawK k m (θ_N u) (θ_N v) = κ · θ_N(u+v)_k · θ_N(u−v)_m` for all `u, v`, `k, m`, with `κ ≠ 0`.
* Hence every law that is nonzero at `(E u, E v)` represents `E(u+v)`, and at every pair some law is nonzero.

**Inputs.** Standard axioms plus `A1Facts`, now including the A3 field batch:
* `lawK`, `law0_lawK`, `lawK_S1`, `rank_one`, `lawK_smul_left/right` and `lawK_analytic`;
* `negP_eq` and `W4_negP`;
* `onQ_closed`, through A3.3.

**Audit.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `laws_eq`, `laws_complete`,
`law_computes_add`, `hom_untrans`, `theta_neg_par` and `psi_const`. No `sorry`, no `native_decide`.

| file (`LSG/JacAn3/`) | lines | content |
|---|---|---|
| `PsiPrep.lean` | 246 | **`exists_theta0_ne`** (`θ₀ ≢ 0`: otherwise `flowW` forces `germ₁ ≡ 0`, contradicting `W4_origin_indep`); `theta_zero`; `negL`, `germ_neg` (flow uniqueness with `W4_negP`), **`theta_neg_par`** (`negP (θ v) ∥ θ(−v)`); `theta_PF0`; **`hom_untrans`** (`law0 (θ u) (θ v) ∥ θ(u+v)` for all `u, v`) |
| `PsiLiouville.lean` | 293 | `col0`, `row0`, `exists_N00_ne`, **`cross`**, `psi`, `psi_spec`, `analyticAt_psi`, `psi_per1/2`, `fundDom`, `exists_fund`, **`psi_const`**, **`laws_eq`**, **`laws_complete`**, `law_correct`, **`law_computes_add`** |

How the proofs go:
* **`hom_untrans`** proves the homomorphism directly, not as a corollary of A2's translated version. It runs the
  `hom_trans_near` argument with the second argument `Y = normalize₀ ∘ θ` near a point `w₁` where `θ₀(w₁) ≠ 0`, then
  applies `par_of_eventually` on `ℂ² × ℂ²`.
* **Avoiding a patched ψ.** By `rank_one`, the cross identity times `N₀₀` vanishes identically, which is pure algebra.
  Since `N₀₀ ≢ 0` (`N₀₀(w₁, 0) = −8a²θ₀(w₁)²`), the identity theorem gives the cross identity everywhere. `ψ` is then
  globally defined through `nzIdx`, and analytic because it is locally a fixed quotient.
* **Periodicity of `|ψ|`** uses `norm_facN` and `L_{−c} = −L_c`. Boundedness uses the fundamental domain of `latBasis`
  (`Int.fract` coordinates), and Liouville is `Differentiable.apply_eq_apply_of_bounded` on `ℂ² × ℂ²`.

**Status of A3 (scope (1) + (2) on the image + (3.1)).** Complete in Lean (A3.1–A3.7, ≈ 2.0k lines).

Not done:
* Surjectivity onto all of `V(Q)`, including the boundary, deferred by the coordinator (§2.5).
* Generic-affine surjectivity (§2.5(a)).
* The full Appell–Humbert form (optional).
* The §3.2–3.3 items for A5/A6 (Taylor-coefficient recursion, algebraicity of `A[M]`).

---------------------------------------------------------------------------------------------------------------------

## 8. Checkpoint A3-4 (2026-10-31): algebraic Taylor coefficients (§3.2) [Proved]

**Statement shape.** This is the `KS` of `TaylorK.lean`, i.e. the A-block analogue of `ks_wpSeries`.
* Fix a number field `K ↪ ℂ`, a point `z₀`, a direction `c ∈ ℂ²` with `c_j` of size `(H_c, d_c)`, and a chart `X_k = 1`
  in which the affine coordinates of `E(z₀)` have size `(A, E)`.
* Then every affine coordinate `s ↦ θ(z₀ + s c)_l / θ(z₀ + s c)_k` is `KS ι A B E (d_c d_W E)` whenever `1 ≤ A`,
  `1 ≤ B` and `81 · 2H_c H_W · A ≤ B`.
* Concretely, the `j`-th Taylor coefficient lies in `K`, with house `≤ A Bʲ` and denominator `E (d_c d_W E)ʲ j!`.
* Here `(H_W, d_W)` is the size of the chart's flow coefficients: `(10, 2)` for chart 0.
* The coordinates are those of `E = [θ] = [θ_N]` (`normalize_thetaN`), so they feed `KS.poly` (`LemmaUAlg.lean`)
  directly, exactly as `wpP`/`wpQ` do for elliptic factors.

**Audit.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `ks_quadODE`, `ks_chart0`, `ks_chart4`,
`ks_chart_rel`, `quadA_cover` and `flowW_quad`. No `sorry`.

| file (`LSG/JacAn3/`) | lines | content |
|---|---|---|
| `QuadODE.lean` | 128 | `tco_finsum`, `analyticAt_finsum`; **`ks_quadODE`**: an `n`-dimensional quadratic ODE with coefficients of size `(H, d_q)` and initial values of size `(A, E)` gives `KS ι A B E (d_q E)` for `n²HA ≤ B` (namespace `LSG.Aux`) |
| `TaylorA.lean` | 166 | `qm`, `flowC`, **`flowW_quad`** (explicit coefficient table of `flowW`, in `½ℤ`), `sz_flowC` (size `(10, 2)`); `normalize_thetaN`; **`ks_chart`** (general chart with a quadratic flow); `theta_PF4`; **`ks_chart0`** (explicit); **`ks_chart4`** (given `W4`'s coefficient table) |
| `TaylorCharts.lean` | 147 | **`quadA_cover`**; **`theta_PF_of_rel`** (the projective flow in a chart `X_k = 1`); **`ks_chart_rel`** |

* **`quadA_cover`**: charts `X₀`, `X₄`, `X₈` cover the model (pure algebra on a copy of A1's quadrics). Charts 0 and 4
  alone do **not** cover it: `(0,…,0,±2,1) ∈ V(Q)` has `X₀ = X₄ = 0` (sympy check, scratchpad `chart04.py`).
* **`theta_PF_of_rel`** obtains the projective flow in a chart `X_k = 1` from a Wronskian relation
  `X_k flowW = X₀ W − X_l W₀` and `W_k = 0`, by the identity theorem. This is how chart 8 is handled.

**A1 inputs needed to use charts 4 and 8 (not added as fields yet; proposed batch).**
1. `W4` as an explicit quadratic coefficient table with sizes (A1 data in `W4.lean`). This is the `hW4c`/`hWsz`
   hypotheses of `ks_chart4`.
2. Chart-8 data: `W8`, its coefficient table and sizes, `W8rel : OnQ X → X 8 * flowW j X l = X 0 * W8 j X l − X l * W8 j X 0`,
   and `W8_eight : W8 j X 8 = 0`. These exist by the same projective-normality argument as `W4`, and A1 generates
   them like `W4`.
3. `onQ_quad : OnQ X → ∀ j, quadA X j = 0` (A1's `onQ_iff`), so that `quadA_cover` applies to `θ`.

With items 1–3, every point of `E(ℂ²)` with algebraic affine coordinates in some chart gets the `KS` bound.

**Next on this item.** Algebraicity of the torsion points `A[M]` (§3.3), if A5/A6 needs it: that `E(ω/M)` has
algebraic affine coordinates, with size bounds.

---------------------------------------------------------------------------------------------------------------------

## 9. Taylor batch discharged; algebraicity of `A[M]`: analysis (2026-10-31)

### 9.1 Taylor batch [Proved]
**New fields** (`A1Facts.lean`, STAGE_A2 §7):
* `onQ_quad`, with `quadA` moved into `A1Facts.lean`;
* the `W4` table (`W4num`, `W4den`, `W4den_pos`, `W4H`, `W4num_bound`, `W4_table`);
* the chart-8 data (`W8`, `W8num`, `W8den`, `W8den_pos`, `W8H`, `W8num_bound`, `W8_table`, `W8rel`, `W8_eight`).

**`TaylorFields.lean` (63 lines)** discharges the hypotheses:
* **`ks_chart4F`** and **`ks_chart8`** (the `KS` bounds in charts 4 and 8);
* **`theta_chart_cover`**: every `θ z` has `X₀ ≠ 0`, `X₄ ≠ 0` or `X₈ ≠ 0`.

So every point of `E(ℂ²)` whose affine coordinates in a covering chart are algebraic gets the `KS` bound. All
`LSG.JacAn*` modules build.

### 9.2 `A[M] ⊂ A(ℚ̄)`: what it needs [Analysis]
**Target.** For `c ∈ Λ` and `M ≥ 1`, the affine coordinates of `E(c/M)` (in a covering chart) are algebraic.
* The `A`-parts of `Y` lie in `(1/M)Λ` for an instance-dependent `M` (ABVAR §2.3: `lam = span_ℚ(logs, periods)`).
  So general `M` is needed.
* Sizes are automatic once algebraicity holds: finitely many numbers in one number field.

**Obstacle.** Every standard argument needs an *algebraic* characterisation of the torsion points:
* the Galois-orbit argument (`σ ∈ Aut(ℂ/ℚ)` permutes the finite set `{X ∈ V(Q) : [M]X = O}`);
* elimination (a finite `ℚ`-algebraic set has algebraic points);
* finiteness of the fibres of `dup` (ampleness).

Each needs one of:
1. **surjectivity `E(ℂ²) = ℙ(V(Q))`**, so that `[M]` is a morphism on all of `V(Q)` via the complete laws, and its
   kernel is finite (`ker E / Λ` finite, since `Λ` is cocompact and `ker E` discrete); or
2. a proof that `E(ℂ²)` is Zariski closed with a `ℚ`-defined ideal (Chow's theorem; not in Mathlib); or
3. finiteness of `{X ∈ ℙ(V(Q)) : [M]X = O}` by a direct algebraic argument (dimension or ampleness theory; not in
   Mathlib).

On top of 1, it needs **"finite `Aut(ℂ/ℚ)`-orbit ⇒ algebraic"**, which is not in Mathlib. It requires extending
`t ↦ t + 1` on `ℚ(x)`, `x` transcendental, to an automorphism of `ℂ` through a transcendence basis. [Est] 0.3–0.6k.
Alternatively, elimination via Mathlib's Nullstellensatz, with field-of-definition bookkeeping. [Est] 0.4–0.8k.

**Routes to surjectivity onto `V(Q)`** (the item deferred in §2.5):
* **(S-div).** Divisor route (§2.5(a)+(b)).
  - Every generic Mumford divisor `D` is hit, by `surj_trans` plus completeness plus path-connectedness of the
    generic locus (curve topology).
  - The affine part of `V(Q)` equals the chart image (A1, algebraic).
  - The boundary `X₀ = 0` points are limits of affine points (A1 description of `V(Q) ∩ {X₀ = 0}`, plus a local
    computation).
  - Then compactness of `E(ℂ²)`. [Est] 1.5–3k plus A1 certificates.
* **(S-smooth).** A1 certifies that `V(Q)∖0` is smooth of dimension 2: a Nullstellensatz certificate for the 6×6
  minors of the Jacobian of the quadrics.
  - `E` is then an open map into the 2-manifold `ℙ(V(Q))` (local immersion, dimension count), and its image is closed
    (compact).
  - This still needs connectedness of `ℙ(V(Q))`, i.e. irreducibility. Not obviously cheaper.

**Cheap special cases.** These are not the general `M`, but are useful sanity checks. They are algebraic directly,
by explicit divisors and `surj_trans`-type path following from the algebraic base `D₀ = (0,−1) + (α,3)`:
* `(0, ±1) − ∞` is 5-torsion: `div(y ∓ 1) = 5(0, ±1) − 5∞`, since `y² − 1 = 4x⁵`;
* the Weierstrass points `(e, 0) − ∞` (`4e⁵ + 1 = 0`) are 2-torsion;
* `A[1 − ζ]` arises as fixed points of the explicit `μ₁₀` action `muP`.

**Recommendation.** Algebraicity of `A[M]` for general `M` should come *after* surjectivity onto `V(Q)`. The minimal
path is (S-div) plus the Galois lemma, about 2–3.5k in total. If the A5/A6 instances need only specific `M` (e.g.
`M | 10`), the cheap cases above may suffice. This should be checked against the instance statements before
committing to (S-div).

---------------------------------------------------------------------------------------------------------------------

## 10. AbVar statement file and the CM classification plan (2026-10-31)

### 10.1 `LSG/W88/StatementAbVar.lean` (263 lines) [Proved where stated]
The definitions mirror `Statement.lean`, for `G = G_a^{d₀} × G_m^{d₁} × A^r`, `A = Jac(y² = 4x⁵+1)`,
`T_G = TanA d₀ d₁ r = ℂ^{d₀} × ℂ^{d₁} × (ℂ²)^r`:
* `LamA` is an `AddSubgroup`: `G_a` part algebraic, `e^{b_i}` algebraic, `A`-parts in `latt` (rational periods).
* `PerA = 0 × 2πiℤ^{d₁} × Λ^r`.
* `IsAbelianTangentA` (`t ∩ Λ^r` spans `t` over `ℝ`), `SubgroupDataA` `(h₀, U, t)` with `δ₂ = 2r − dim t`, and
  `TorInjA` (every `v ∈ V ∩ span_ℚ PerA` with zero toric part is `0`).
* `latt_le_kerE` [Proved]: `exp_A = origin` on `Λ`, for every A2 base.

The two forms of the target statement:
* **`Theorem41AbVarPer`**: W88 Thm 4.1 with (NR) and (TorInj), with `d₂ = 2r`.
* **`HyperplaneKappaAbVar`** = `∀ d₀ d₁ r, HyperplaneKappaOn (gmLsgA d₀ d₁ r) TorInjA`. Here `HyperplaneKappaOn` is
  `lean_mstar`'s, as agreed in PLAN.md, and `gmLsgA` is a `MStarCopy.GroupModel` with `lam = LamA` and
  `per = span_ℚ PerA`.

**Scaling reduction [Proved].**
* `exists_nsmul_mem_closure` and `exists_common_nsmul`: a finite family in `span_ℚ S` has a common positive multiple
  in `⟨S⟩`.
* `span_range_nsmul`: `span_ℚ (M y) = span_ℚ y`.
* **`hyperplaneKappaOn_of_scale`**: if `lam ⊆ span_ℚ S` with `S ⊆ L`, the §5d hypothesis for `lam := L` implies it
  for the original model. This holds for any extra premise `good`, e.g. `TorInj`. The reason: `M y_i ∈ V`,
  `rk` and `κ` are unchanged because `per` is a `ℚ`-subspace, and the conclusion does not involve `y`.
* `hyperplaneKappaOn_spanLam`: the `lean_mstar`-shaped model `lam = span_ℚ LamA ⊇ span_ℚ lamGen` reduces to `gmLsgA`.

**Note.** The scaling argument is exact for the §5d form, where `per` is a `ℚ`-span. It does **not** transfer verbatim
to the Thm 4.1 form: there `κ = rk(Y ∩ Per)` with `Per` a subgroup, and `rk(MY ∩ Per)` can exceed `rk(Y ∩ Per)`. The
bridge therefore goes through the §5d form, which is what `lean_mstar` consumes.

### 10.2 CM classification (next) [Plan]
**Target.** A complex `t ⊆ (ℂ²)^r` satisfies `IsAbelianTangentA t` iff `t = ⊕_s cJ_s · σ_{s+1}(S) ⊗ ℂ` for an
`F`-subspace `S ⊆ F^r`, `F = ℚ(ζ₅)`, with CM type `{σ₁, σ₂}`.

**Coordinates.** Use `x ∈ ℚ^{4r}` (basis `ζ^e`, `e < 4`), `Φ(x)_{j,s} = cJ_s Σ_e x_{j,e} ζ^{(s+1)e}`. `Φ_ℝ` is an
`ℝ`-isomorphism by `linearIndependent_perVec`, and `Λ^r = Φ(ℤ^{4r})`.

**(⇐).** `Φ(S ⊗ ℝ)` is complex because multiplication by `i` preserves `σ₁(S)⊗ℂ ⊕ σ₂(S)⊗ℂ` coordinatewise. It is
spanned by `Φ(S ∩ ℤ^{4r})`. [Est] 0.2k.

**(⇒).** Let `S_ℚ = Φ⁻¹(t) ∩ ℚ^{4r}`, so `span_ℝ S_ℚ = Φ⁻¹(t)` by the hypothesis. It must be shown that `S_ℚ` is stable
under multiplication by `ζ` (the companion matrix `Z`); `F`-stability then follows since `F = ℚ(ζ)`. The argument, in
the eigen-coordinates `Ψ_k(x) = Σ_e x_e ζ^{ke}` (`k = 1..4`, Vandermonde over `F`):
* Complex structure: `S ⊗ F = (S⊗F ∩ U₁₂) ⊕ (S⊗F ∩ U₃₄)`, with `U_{ab} = {Ψ_c = 0 : c ∉ {a,b}}`, all `F`-rational.
  Getting this needs base change `F → ℂ` of intersections and a dimension count.
* `Gal(F/ℚ) ∋ (ζ ↦ ζ²)` acts coordinatewise on `F^{4r}`, preserves `S ⊗ F` (since `S` is rational), and permutes the
  `U`'s: `{1,2} ↦ {2,4}`, `{3,4} ↦ {1,3}`.
* Primitivity: `{1,2} ∩ {2,4} = {2}` etc., so the intersections split `S ⊗ F` into single eigenlines.
* `Z` acts by `ζ^k` on `Ψ_k`, so `Z(S⊗F) ⊆ S⊗F`. Rationality (`S ⊗ F ∩ ℚ^{4r} = S`) then gives `Z S ⊆ S`.
* [Est] 1.0–1.5k.

**Mathlib.** Needed: explicit automorphisms of `ℚ(ζ₅)` (`IsCyclotomicExtension`, `autToPow`), base change of
subspaces along `ℚ ⊆ F ⊆ ℂ`, and `span_K S ∩ ℚⁿ = S` for a `ℚ`-subspace `S`. No several-variable analysis is needed.

**Consumer.** A6 bridges (`hyperplaneKappa_of_iso` pattern). The A4/ME subgroup layer may need only the `(⇐)`
direction or the `IsAbelianTangentA` form; check STAGE_A4.md (not yet written) before building `(⇒)`.

### 10.3 `λ ≠ 0` without the classification [Proved] (`LSG/W88/AbVarSub.lean`, 75 lines)
**Statement (`lam_ne_zero_of_abelian`).** If `IsAbelianTangentA t`, `t ≠ ⊥`, and `θ(j, e) = ζ^e b_j` is
`ℚ`-linearly independent (`IsAdaptedBasisD.indep`), then `∃ z ∈ t, Σ_j b_j z_j(0) ≠ 0`.

**Proof.**
* `exists_lattice_point`: `t ≠ ⊥` contains a nonzero lattice point.
* Its slot-0 coordinates are `cJ₀ Σ_e n_{je} ζ^e` with `n ∈ ℤ`.
* So `λ(z) = cJ₀ Σ_{j,e} n_{je} θ(j, e)`, which is nonzero unless `n = 0`.

**Audit.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

**What it gives the bridge.** This is exactly the `sub` condition of `lean_mstar`'s `gmF` (`h = ⊥ ∨ ∃ x ∈ h, λ x ≠ 0`)
for `λ(q) = Σ_j b_j q(s₀, j)` at `s₀ = 0` (`κ s₀ = 1`). So the gmA soundness step needs **no** CM classification.
* The classification route (ThmA.lean header: `T(B) = ⊕ σ_s(S) ⊗ ℂ`, then `F`-independence of `b`) is replaced by
  "a nonzero lattice point plus `ℚ`-independence of `θ`".
* The same argument works for any slot `s₀`: `{ζ^{κ e}}_{e}` is again a `ℚ`-basis of `F`, and `θ` is then replaced by
  `θ_κ(j, e) = ζ^{κe} b_j`.

**Consequence for §10.2.** The full classification (`(⇒)`, about 1.0–1.5k lines) is no longer on the bridge's critical
path. It is needed only if the ME subgroup layer (A4) wants subgroups in `F`-subspace form.

---------------------------------------------------------------------------------------------------------------------

## 11. A4.1b surjectivity (in progress, 2026-10-31)

**Goal.** `∀ X ≠ 0, OnQ X → ∃ z c, X = c • θ_N z`. This is the `surj` field of `MEB/Block.lean`, with
`gens` = 9 quadrics + 3 cubics. The cubics vanish on `V(Q)∖0` pointwise, so `OnQ` (quadrics) is the right hypothesis.

**Done [Proved]** (`LSG/JacAn4/`, standard axioms):
* **`Closed.lean` (110 lines)**: `isClosed_imgCone` (the cone `{0} ∪ {c θ_N z}` is closed: nonzero points normalise
  into the compact set `{u θ_N f/‖θ_N f‖ : |u| = 1, f ∈ fundDom}`) and `mem_imgCone_of_tendsto`.
* **`CurveConn.lean` (239 lines)**: path-connectedness of the generic locus, the step STAGE_A4 R1 flags as hardest.
  - `lift_path`: path lifting through the covering `z ↦ z²` of `ℂ∖0` (Mathlib `isCoveringMap_npow`,
    `exists_path_lifts`).
  - `sign_swap`: a half circle in a Weierstrass chart, with `X_W(−ρ) = X_W(ρ)` by injectivity of `f` near a simple
    root.
  - `isPathConnected_covB`: the curve over `ℂ ∖ B`, `B` finite and containing the roots.
  - **`isPathConnected_genPairs`**: `{(P₁,P₂) : y_i ≠ 0, x₁ ≠ x₂}`. The proof moves one point at a time through an
    auxiliary point.

**Remaining plan.**
1. **S-b generic.** For a generic `D = (P₁, P₂)`, take a path in `GenPairs` from `D₀` (special base) to `D`. Then:
   - Get `IsAbelAlong` by `exists_abelAlong`, and `k` by compactness.
   - `follow_par` at `t = 1` gives `Par(T(c + w), Ψ_D(w))`, with `T(c) = law0(Ẽ c, P₀)`.
   - With the anchor (`P₀ ∥ θ(z₀)`, A1 field `anchor`) and `laws_eq`, `Ψ_D(w) ∥ θ(c + w + z₀)` wherever
     `T(c + w) ≠ 0`. Such `w` exist arbitrarily near 0, since `T ≢ 0` near any point by the identity theorem.
   - Hence `D ∈` cone by closedness.
   - For the anchor itself, `θ(c₂) ∥ law0(D₂, negP P₀) ∥ P₀` (inversion `inv_trans` plus `follow_par` to `D₂`).
   - [Est] 0.4–0.6k.
2. **S-a** with `affine_chart` (A1): `X₀ = 1 ⇒ X = grantJ p`, `p` on the chart. [Est] 0.1k glue.
3. **Non-generic chart points.**
   - Route (i): density of generic chart points in the chart (explicit perturbation of the two points along the
     curve; collision and Weierstrass cases) plus closedness. [Est] 0.3–0.6k.
   - Route (ii): flow exit with a discriminant certificate (not spiked).
4. **S-c, boundary flow exit.**
   - Real-time Picard–Lindelöf for `V′ = W^{[c]}_v(V)`.
   - Invariance of `V(I_A)` via the linear ODE for `gensI(V(t))` (`gensI_tan4/8`).
   - The exit words force `V(t)₀ ≠ 0` for small `t ≠ 0` (Taylor bound).
   - Closedness. [Est] 0.5–0.8k.
5. **A1 requests** (STAGE_A1.md, "Requests from the A3 agent for A4.1b"): `affine_chart`, `anchor`,
   `gensI` + `tanC4/8` + `gensI_tan4/8`, `exitWord`/`exit4`/`exit8`.

### 11.1 Checkpoint (2026-10-31): generic-divisor assembly and S-c ODE parts [Proved, modulo `SurjFacts`]

**Inputs.** `SurjFacts` (`LSG/JacAn4/SurjFacts.lean`, 59 lines) is a separate structure, *not* an `A1Facts` field. Its
fields are `affine_chart`, `anchor`, `gensI`, `gensI_diff`, `gensI_iff`, `tanC4/8`, `tanC4/8_cont`, `gensI_tan4/8` and
`exit4/8`, exactly as in STAGE_A1's request section, with `derivW`, `exitWord` and `P0of` defined there. γ discharges
them.

**Audit.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `generic_mem`, `anchor_mem`,
`exists_anchored_base`, `flow_exit_mem`, `boundary_mem` and `taylor_exit`. No sorry.

| file (`LSG/JacAn4/`) | lines | content |
|---|---|---|
| `Generic.lean` | 216 | **`exists_follow`** (a path in `GenPairs`, `exists_abelAlong`, compactness for `k`, `follow_par` at `t = 1`); cone calculus (`cone_smul`, `expLift_eq_smul`, `law0_mem_cone`, `par_mem_cone`, `transP_mem_cone`, `frequently_transP_ne`); **`generic_mem`** (`P₀ ∈` cone ⇒ every generic Grant point is in the cone); **`anchor_mem`** (`law0(D₂, −P₀) = λP₀` ⇒ `P₀ ∈` cone, via `inv_trans`) |
| `Anchor.lean` | 50 | **`exists_anchored_base`**: from `SurjFacts.anchor`, a generic base with `P₀ ∈` cone for every `θ`-datum over it |
| `ExitTaylor.lean` | 93 | **`taylor_exit`**: `h_j' = h_{j+1}`, `h_j(0) = 0` for `j < K`, `h_K(0) ≠ 0` ⇒ `h₀(t) ≠ 0` for small `t ≠ 0` |
| `FlowExit.lean` | 175 | **`flow_exit_mem`** (C¹ ODE existence, invariance via `ODE_solution_unique_of_mem_Icc_right` for the generator values, exit words, closedness); `contDiff_exitWord`, `contDiff_W8`; **`boundary_mem`** (`SurjFacts` + `quadA_cover`: boundary model points are in the cone, given that the affine ones are) |

**Remaining for `surjA`.**
1. Affine model points (`X₀ ≠ 0`). Rescale to `X₀ = 1`, apply `affine_chart` (`X = grantJ p`, `p` on the chart),
   then use the chart point `p`:
   - generic (`x₁ ≠ x₂`, `y ≠ 0`): `generic_mem` at the anchored base;
   - non-generic: density plus closedness.
   [Est] 0.3–0.6k (the non-generic density is the main part).
2. Base-independence of the cone (`expP_base_indep` + `expP_eq_thetaN`). Assembly into
   `surjA : ∀ X ≠ 0, A.OnQ X → ∃ z c, X = c • θ_N z` for every `θ`-datum. [Est] 0.1–0.2k.

### 11.2 `surjA` complete [Proved, modulo `SurjFacts`] (2026-10-31)
**Audit.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `ThetaData.surjA`,
`ThetaData.affine_mem` and `chart_mem`. No sorry.

| file (`LSG/JacAn4/`) | lines | content |
|---|---|---|
| `Affine.lean` | 244 | `chart_div`, `curve_approx`, **`chart_mem`**, **`affine_mem`** (see below) |
| `Surj.lean` | 54 | **`imgCone_transfer`** (base independence) and **`surjA : ∀ X ≠ 0, A.OnQ X → ∃ z c, X = c • θ_N z`** for every `θ`-datum |

`chart_mem` covers every chart point:
* distinct roots: perturb the Weierstrass points along `(X_W(t), t)`;
* double root `x₀`: `y₀ ≠ 0` because `f` has simple roots (derivative of `f − b² = (x−x₀)²q`); the points
  `(x₀ ± t, Y(x₀ ± t))` converge through symmetric difference quotients.

`affine_mem` rescales to `X₀ = 1` and applies `affine_chart`.

`LSG/JacAn4/` is now about 1.24k lines. Plug-in instructions for γ are in STAGE_A4 §8.

**Note from γ (2026-10-31): `SurjFacts` is discharged.** `LSG/JacBlock/SurjFactsInst.lean`:
`LSG.JacBlock.surjFactsOf A hOnQ hlaw0 hneg hW4 hW8 : SurjFacts A` for any `A : A1Facts` with A1's `OnQ`, `lawPt 0`,
`negP`, `W4n/4`, `W8n/4` (all `rfl` for A1's instances), and `surjFactsMk … : SurjFacts (mkA1Facts …)`. Field
statements are exactly those of `LSG/JacAn4/SurjFacts.lean` (17:02 version); standard axioms only. Exit words:
`exit4` uses `v = e₀, k = 3`; `exit8` uses `v ∈ {e₀, e₁}`. Explicit polynomial forms `exitWord_W4G_k`/`exitWord_W8G_k`
(`k ≤ 3`) are in `LSG/JacBlock/Exit.lean` if useful. Details: `STAGE_A4_GAMMA.md`.
