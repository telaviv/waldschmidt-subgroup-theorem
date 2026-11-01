# STAGE A2: the analytic core of `Jac(C)`, `C : y² = 4x⁵ + 1` (local part)

Written 2026-10-31. Companion to `ABVAR.md` §2.2 route (a), items a2–a8, and §6 (risk R-SCV; the A2 brief calls it R4).
The model is the one fixed in ABVAR A0.1. It is `≅ y⁵ = x(1 − x)` via `X = −y`, `Y = 2x − 1`.

**Status.**
* **Checkpoint 1** (commit 2187462): items 1–4 of the brief, a seed of a8 and the FTC building block of a6. That is
  8 files, 1107 lines (§2.1–2.9).
* **Checkpoint 2** (this update; not committed): everything in A2 that does not depend on A1. That is 6 more files,
  1370 lines (§2.10–2.14):
  - a3′, the charts at the Weierstrass points and at `∞`;
  - a8, the full closed polynomial ODE of the Mumford coordinates;
  - the exp-free half of a6 (the continuation lemma): the Abel integral along a path, patched from chart primitives,
    including paths through Weierstrass points;
  - the a5 input that the periods of `cycleE e` are differences of Abel integrals along paths with the same endpoints;
  - `localExp_follow`, the exact statement a4 plugs into.
* In total: 14 files and 2477 lines.
  - There is no `sorry`, `axiom` or `native_decide`.
  - All 49 audited top-level theorems (24 + 25) print `[propext, Classical.choice, Quot.sound]`. The audit was run from
    scratch files and is **not** in `Axioms.lean`.
  - Nothing was added to `LSG.lean` or `Axioms.lean`, and git was not touched.
* **The interface a4 needs from A1 is in §5.**

Build:
`export PATH="$HOME/.elan/bin:$PATH"; lake build LSG.JacAn.PeriodPath LSG.JacAn.Follow LSG.JacAn.LocalExpODE LSG.JacAn.AbelLocal`.
That covers all 14 files. Each file takes 20–50 s once Mathlib is cached. The files import only Mathlib and each other:
not StrongSix, and not `LSG/Jac`.

---------------------------------------------------------------------------------------------------------------------

## 1. R-SCV verdict (Mathlib v4.35 audit)

**Verdict: GREEN.** Several-variable complex analysis is not a blocker for A2.
* What Mathlib lacks (Hartogs and Osgood) is avoidable by design: build every map as *analytic* from the start, never
  as merely ℂ-differentiable.
* The glue cost is 107 lines (`Glue.lean`) and took under an hour.
* Path integrals already exist (`curveIntegral`). This saves the 0.5–1k lines that ABVAR implicitly budgeted for them.

| need | Mathlib (exact names) | gap / glue |
|---|---|---|
| holomorphic maps `ℂ^g → ℂ^g` | Model `ℂ^g` as `Fin g → ℂ` (sup norm, complete) or `ℂ × ℂ`. `AnalyticAt ℂ`, `AnalyticOnNhd ℂ` work for any normed domain. Also `analyticAt_pi_iff`, `analyticAt_fst`/`analyticAt_snd`, `AnalyticAt.comp`/`.add`/`.mul`/`.div`/`.cpow`, `AnalyticOnNhd.eval_polynomial`, `AnalyticAt.exists_ball_analyticOnNhd`, `AnalyticAt.eventually_analyticAt` | **Missing: Hartogs/Osgood.** "ℂ-differentiable on an open subset of ℂ^g ⇒ analytic" exists only for domain ℂ (`DifferentiableOn.analyticOnNhd`, `Analysis/Complex/CauchyIntegral.lean:706`). **Avoided**: every A2 map is a composition of analytic maps. No several-variable Cauchy formula either (`torusIntegral` exists, but no Cauchy theorem for it). |
| strict derivative from analyticity | `AnalyticAt.hasStrictFDerivAt` (with `fderiv`), `HasFPowerSeriesAt.hasStrictFDerivAt` | `hasStrictFDerivAt_of_analyticAt` (prescribed derivative, 4 lines) |
| IFT with **analytic** inverse | `HasStrictFDerivAt.toOpenPartialHomeomorph`, `.localInverse`, `.to_localInverse` (derivative `f'.symm`), `.eventually_left_inverse`, `.eventually_right_inverse`, `.localInverse_apply_image`, `.localInverse_continuousAt`; **`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`** (`Analysis/Analytic/Inverse.lean:657`, any complete spaces) | `analyticAt_localInverse` and `eventually_analyticAt_localInverse` (≈ 15 lines) |
| identity theorem on connected open `U ⊆ ℂ^g` | `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, `AnalyticOnNhd.eq_of_eventuallyEq` (on `univ`, `PreconnectedSpace E`), all in `Analysis/Analytic/Uniqueness.lean`, for an arbitrary normed domain | none needed |
| holomorphic branch of `√f` | `AnalyticAt.cpow` (base in `slitPlane`), `Complex.cpow_nat_inv_pow` | `exists_sqrt_branch` (15 lines) |
| primitive of a holomorphic 1-variable function | `DifferentiableOn.isExactOn_ball` (Morera on a disc, `Analysis/Complex/HasPrimitives.lean`), `Differentiable.isExactOn_univ` | `exists_primitive_ball` (vector-valued and analytic, 10 lines) |
| path integrals of 1-forms | **`curveIntegral`** (notation `∫ᶜ x in γ, ω x`, `MeasureTheory/Integral/CurveIntegral/Basic.lean`) for `ω : E → E →L[𝕜] F` along `Path a b`. Also `curveIntegral_def`, `curveIntegralFun_def` (uses `derivWithin` on `unitInterval`), `curveIntegral_eq_intervalIntegral_deriv`, `CurveIntegrable`, `curveIntegral_trans`, `curveIntegral_symm`, `curveIntegral_segment`. Homotopy invariance for `C²` homotopies and Poincaré on convex sets are in `CurveIntegral/Poincare.lean` (`curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`, `exists_forall_hasFDerivAt_of_fderiv_symmetric`). FTC: `intervalIntegral.integral_eq_sub_of_hasDerivAt` | none. `PathInt.lean` links `curveIntegral` to branch primitives |
| Beta integrals | `Complex.betaIntegral`, `Complex.betaIntegral_convergent`, `Complex.Gamma_mul_Gamma_eq_betaIntegral` | `betaG` copied from lean_mstar |
| constancy from zero derivative | `IsOpen.is_const_of_deriv_eq_zero`, `IsOpen.exists_is_const_of_deriv_eq_zero` | none needed |

Still missing, for later stages and not needed in A2: meromorphic functions of several variables, and `g`-variable
theta functions (only `jacobiTheta₂`). Both matter only if A3 takes the theta route (R-order2).

---------------------------------------------------------------------------------------------------------------------

## 2. What was proved

All declarations are in namespace `LSG.JacAn`; those in `BetaPeriods.lean` are in `LSG.JacAn.Beta`. Line numbers are
the declaration lines.

### 2.1 `Glue.lean` (107 lines): R-SCV glue
* `analyticAt_localInverse` (l. 38): `AnalyticAt 𝕜 f a`, `HasStrictFDerivAt f (f' : E ≃L F) a` ⇒
  `AnalyticAt 𝕜 (hf.localInverse f f' a) (f a)`.
* `eventually_analyticAt_localInverse` (l. 51).
* `hasStrictFDerivAt_of_analyticAt` (l. 58).
* `exists_sqrt_branch` (l. 69): `F` analytic at `x₀`, `y₀² = F x₀ ≠ 0` ⇒ there is `Y` analytic at `x₀` with
  `Y x₀ = y₀` and `Y² = F` everywhere.
* `exists_primitive_ball` (l. 95): holomorphic `f : ℂ → E` on `ball c r` ⇒ there is `G` with `G c = 0`, `G' = f` on
  the ball, and `G` analytic there.

### 2.2 `EulerJacobi.lean` (106 lines): genus-free algebra
* `coeff_interpolate_card_sub_one` (l. 29): the top coefficient of the Lagrange interpolant.
* `sum_nodalWeight_mul_eval_eq_zero` (l. 39) and **`sum_eval_div_prod_eq_zero`** (l. 49): Euler–Jacobi,
  `Σ_i p(vᵢ)/∏_{j≠i}(vᵢ − vⱼ) = 0` for `deg p + 2 ≤ #s`, over any field.
* `eq_C_leadingCoeff_mul_nodal` (l. 58), `eval_derivative_eq_of_roots` (l. 75),
  `eval_derivative_ne_zero_of_roots` (l. 83).
* **`eulerJacobi_roots`** (l. 95): if `R` has `#s = deg R` distinct roots and `deg q + 2 ≤ #s`, then
  `Σ_i q(vᵢ)/R'(vᵢ) = 0`.

### 2.3 `Branch.lean` (83 lines): local branches, genus-generic, any `f : ℂ[X]`
* `omegaVec g Y x = (x^k / Y x)_{k<g}`.
* `structure LocalBranch f g`: a disc `ball x₀ r`, a holomorphic `Y` with `Y² = f` and `Y ≠ 0`, and the Abel integrals
  `I : ℂ → (Fin g → ℂ)` with `I x₀ = 0`, `I' = omegaVec g Y`, `I` analytic.
* **`LocalBranch.exists_of_mem`** (l. 59): a branch exists at every affine point with `y₀ ≠ 0`, and `B.Y x₀ = y₀`.

### 2.4 `Abel2.lean` (240 lines): genus-2 Abel map and local exp (brief item 2)
Here `B₁, B₂ : LocalBranch f 2` and `abel2 (x₁, x₂) = B₁.I x₁ + B₂.I x₂`, on `dom2` = the product of the two discs.
* `hasFDerivAt_abel2` (l. 53) and `analyticAt_abel2` (l. 60).
* **`abelJac_matrix`** (l. 48): the Jacobian columns are `(1/y₁, x₁/y₁)` and `(1/y₂, x₂/y₂)`.
  `abelJac_det` (l. 92): `det = (x₂ − x₁)/(y₁y₂)`.
* **`abelJacEquiv`** (l. 72): the Jacobian is a `ContinuousLinearEquiv` when `x₁ ≠ x₂` and `yᵢ ≠ 0`. The explicit
  inverse is `abelJacInv` (l. 65).
* `hasStrictFDerivAt_abel2` (l. 97).
* `abelInv` (l. 109): the local inverse.
* **`analyticAt_abelInv`** (l. 113), `abelInv_abel2_self`, `abel2_abelInv`, `abelInv_abel2`, and
  `eventually_abelInv_good` (l. 130: the inverse stays in the discs and off the diagonal).
* `mumford` (l. 147): `(s₁, s₂, b₁, b₀) = (x₁+x₂, x₁x₂, (y₁−y₂)/(x₁−x₂), (x₁y₂−x₂y₁)/(x₁−x₂))`.
* `analyticAt_mumford` (l. 151); `mumford_dvd_aux` (l. 166) and **`mumford_dvd`** (l. 190): `a ∣ f − b²`.
* **`localExp := mumford ∘ abelInv`** (l. 204), the local exponential onto Mumford coordinates.
  - **`analyticAt_localExp`** (l. 207) and `eventually_analyticAt_localExp` (l. 217);
  - `localExp_abel2_self` (l. 212);
  - **`localExp_mem_chart`** (l. 223): near `z₀`, `localExp z` satisfies the chart relation `a ∣ f − b²`;
  - `localExp_spec` (l. 233).

### 2.5 `LocalExpDeriv.lean` (84 lines): a8 seed
* `hasFDerivAt_abelInv` (l. 32): `D(abelInv)(z₀) = abelJacInv p`, so the `∂xᵢ/∂z` are rational in `(xᵢ, yᵢ)` over ℚ.
* **`hasFDerivAt_localExp_s₁`** (l. 46): `∂s₁ = b₀ dz₀ + b₁ dz₁`.
* **`hasFDerivAt_localExp_s₂`** (l. 64): `∂s₂ = (b₁s₂ + b₀s₁) dz₀ − b₀ dz₁`.
* Under the A0.1 dictionary (`℘₂₂ = s₁`, `℘₁₂ = −s₂`, `℘₂₂₂ = b₁`, `℘₁₂₂ = b₀`, `℘₁₁₂ = −b₀s₁ − b₁s₂`) these
  become `∂ᵢ℘ⱼₖ = ℘ᵢⱼₖ`. That is an independent Lean-level consistency check of Grant's basis in A0.1.

### 2.6 `AbelLocal.lean` (176 lines): Abel's theorem locally (brief item 3, a2)
Notation: `c_t = Σ_{j≤m} c_j(t) Xʲ` (`cPoly`) and `R_t = f − c_t²`.
* `deriv_root_eq` (l. 74): implicit differentiation, `R'(xᵢ) xᵢ' = 2 c(xᵢ) δc(xᵢ)`.
* **`abel_local`** (l. 97): `Σ_i xᵢ^k xᵢ'/yᵢ = 0` for `k + m + 2 ≤ #s = deg R_{t₀}`, with distinct roots and `yᵢ ≠ 0`.
* **`hasDerivAt_abelSum`** (l. 131): if the points move on local branches `B i`, then
  `d/dt Σ_i (B i).I (xᵢ(t)) = 0`, provided `g + m + 1 ≤ #s`. For `deg f = 2g + 1` this holds for every `m`.
* **`abelSum_const`** (l. 157): the Abel sum is constant on a connected open parameter set.

### 2.7 `BetaPeriods.lean` (243 lines): brief item 4
* Verbatim copies of lean_mstar's `zetaN`, `betaG`, `perA5`, `perB5` and `betaG_eq_betaIntegral`.
* `liftPath e : Path (0,−1) (0,1)`, `t ↦ (−ζ^e (t(1−t))^{1/5}, 2t − 1)`. This is `[ζ^e]ℓ` in the model.
  `liftPath_mem_curve` (l. 85) shows it lies on `Y² = 4X⁵ + 1`.
* `cycleE e = liftPath e ⬝ (liftPath (e+1))⁻¹` (l. 97). This is `[ζ^e]γ` for the γ of ABVAR §1.2.
* `omegaJ j p = (p.1^j/p.2) • fst`, the form `X^j dX/Y`.
* **`curveIntegral_cycleE`** (l. 200), with Mathlib's `curveIntegral`:
  `∫_{[ζ^e]γ} X^j dX/Y = ((−1)^j/5)((ζ^e)^{j+1} − (ζ^{e+1})^{j+1}) B((j+1)/5, (j+1)/5)`, for all `j`.
  It goes through `curveIntegral_liftPath` (l. 193) and `Complex.betaIntegral`.
* **`period_omega0`**: `∫_γ dX/Y = perA5 0 / 5`. **`period_omega1`**: `∫_γ X dX/Y = −perA5 1 / 5`.
  **`period_omega3`**: `∫_γ X³ dX/Y = −perB5 / 5`.
* These match ABVAR §1.2–1.3, because `dX/Y = (1/5) dx/y⁴`, `X dX/Y = −(1/5) dx/y³` and `X³ dX/Y = −(1/5) dx/y` on
  `C₅`. `cycleE e` gives `perAgen` (the `ζ^{κ_s e}` factors).

### 2.8 `PathInt.lean` (68 lines): a6 building block
* `integral_omega_eq_sub` (l. 31) and **`curveIntegral_eq_sub`** (l. 47): for a `C¹` path `(u, Y∘u)` inside a branch
  disc, `∫ᶜ omegaJ j = I_j(u 1) − I_j(u 0)`.

### 2.9 New top-level theorems of checkpoint 1
* `LSG.JacAn.analyticAt_localInverse`, `LSG.JacAn.eulerJacobi_roots`, `LSG.JacAn.LocalBranch.exists_of_mem`.
* `LSG.JacAn.abelJac_matrix`, `LSG.JacAn.abelJacEquiv`, `LSG.JacAn.analyticAt_localExp`, `LSG.JacAn.localExp_mem_chart`.
* `LSG.JacAn.hasFDerivAt_localExp_s₁`, `LSG.JacAn.hasFDerivAt_localExp_s₂`.
* `LSG.JacAn.abel_local`, `LSG.JacAn.hasDerivAt_abelSum`, `LSG.JacAn.abelSum_const`.
* `LSG.JacAn.Beta.curveIntegral_cycleE`, `LSG.JacAn.Beta.period_omega0`, `LSG.JacAn.Beta.period_omega1`,
  `LSG.JacAn.Beta.period_omega3`.
* `LSG.JacAn.curveIntegral_eq_sub`.

### 2.10 `Charts.lean` (231 lines): a3′, genus-generic
* **Weierstrass charts.** `structure WeierChart f g` (l. 38) uses `y` as the coordinate at a simple root `e`.
  - It has `x = X(y)` with `f(X y) = y²` and `X 0 = e`, `f'(X y) ≠ 0`, and Abel integrals `I` with
    `I' = weierVec = (2X^k/f'(X))_k`.
  - **`WeierChart.exists_of_root`** (l. 59): a chart exists whenever `f(e) = 0` and `f'(e) ≠ 0`. It is built from the
    analytic inverse of `x ↦ f(x)` via `analyticAt_localInverse`.
  - `hasDerivAt_X` (l. 98): `X'(y) = 2y/f'(X y)`.
  - **`WeierChart.hasDerivAt_branch`** (l. 113): `d/dy B.I(X y) = weierVec` wherever `B.Y(X y) = y`.
* **Charts at `∞`.** `revPoly f g` (l. 129) is the polynomial `F(τ) = τ^{4g+2} f(τ⁻²)`.
  - `revPoly_eval` (l. 132) proves this identity, for `deg f ≤ 2g + 1` and `τ ≠ 0`.
  - `revPoly_eval_zero` (l. 144): `F(0) = f_{2g+1}`.
* `structure InfChart f g` (l. 157) has `H = √F`, so `x = τ⁻²` and `y = τ^{−(2g+1)}H`. Its Abel integrals satisfy
  `I' = infVec = (−2τ^{2(g−1−k)}/H)_k`, which is holomorphic at `τ = 0`.
  - **`InfChart.exists_of_lc`** (l. 175): a chart exists when `f_{2g+1} ≠ 0`.
  - `InfChart.mem_curve` (l. 203): the chart points lie on the curve.
  - **`InfChart.hasDerivAt_branch`** (l. 211): `d/dτ B.I(τ⁻²) = infVec` wherever `B.Y(τ⁻²) = τ^{−(2g+1)}H(τ)`.

### 2.11 `LocalExpODE.lean` (196 lines): a8 complete
The setting: genus 2, any quintic `f = quintic a₀ … a₅` (l. 45).
* `LocalBranch.hasDerivAt_Y` (l. 33): `Y' = f'/(2Y)`, for any genus.
* **`odeVF`** (l. 71) is the closed polynomial vector field in `m = (s₁, s₂, b₁, b₀)`, with coefficients in
  `ℚ[a₀ … a₅]`:
  - `∂s₁ = b₀dz₀ + b₁dz₁`;
  - `∂s₂ = (b₁s₂ + b₀s₁)dz₀ − b₀dz₁`;
  - `∂b₁ = ½(a₂ + a₃s₁ + a₄(s₁² − 2s₂) + a₅(s₁³ − 4s₁s₂) − b₁²)dz₀ + ½(a₃ + 2a₄s₁ + a₅(3s₁² − 2s₂))dz₁`;
  - `∂b₀ = −½(−a₁ + 2a₃s₂ + 2a₄s₁s₂ + a₅(2s₁²s₂ − 3s₂²) + 2b₀b₁)dz₀ + (∂b₁/∂z₀)dz₁`.
  - The right-hand sides came from a weighted sympy ansatz (untrusted). Lean checks them, with `linear_combination`
    cofactors that are linear in `v`.
* `hasFDerivAt_localExp_b₁` (l. 80), `hasFDerivAt_localExp_b₀` (l. 113), and **`hasFDerivAt_localExp`** (l. 147):
  `D(localExp_i)(z₀) = odeVF (localExp z₀) i`.
* `abelInv_eventuallyEq_rebase` (l. 159): changing the base point does not change `abelInv` locally.
* **`localExp_ode`** (l. 178): the ODE holds at every `z` near `z₀`.
* Consistency check: for `f = 4x⁵ + 1` it gives `∂b₁/∂z₁ = 6s₁² − 4s₂`, which is Grant's `℘₂₂₂₂ = 6℘₂₂² + 4℘₁₂`.

### 2.12 `Continuation.lean` (411 lines): a6, exp-free, paths with `y ≠ 0`
* **`exists_patch`** (l. 90), pure topology over any abelian group. Local primitives `F s` on `ball s (ε s)`, with
  differences constant on overlaps, patch to a global `A` with `A 0 = 0`. The proof is a Lebesgue number plus an
  induction (`patch_step`). **`patch_unique`** (l. 140).
* `LocalBranch.Y_eqOn` (l. 170) and **`LocalBranch.I_sub_eq`** (l. 182): two branches that agree at one point of the
  convex intersection of their discs agree on all of it, and their `I`'s differ by a constant there.
* **`exists_abelAlong`** (l. 232) and the property `IsAbelAlong` (l. 264): the Abel integral along a continuous path
  `(u, Yp)` with `Yp ≠ 0` exists.
* **`abelAlong_branch`** (l. 271): *any* branch carrying the path on `[t, t']` computes `A t' − A t`.
  **`abelAlong_unique`** (l. 298).
* `IsAbelAlong.hasDerivAt` (l. 336) and `.continuousOn` (l. 352).
* **`.eq_integral`** (l. 368): `A 1 = ∫₀¹ u'ω(u)`. **`.curveIntegral`** (l. 382): the components are Mathlib curve
  integrals of `x^j dx/y`.

### 2.13 `ContinuationW.lean` (263 lines): a6 through Weierstrass points
* `exists_injOn_ball` (l. 32): `f` is locally injective where `f' ≠ 0`.
* `eventually_eq_of_hasDerivAt_zero` (l. 40).
* Chart-overlap compatibility: `WeierChart.X_eventuallyEq` (l. 51), `I_sub_eventually` (l. 62) and
  `I_sub_branch_eventually` (l. 74).
* `inductive PathChart` (l. 101) is an `x`-branch or a `y`-chart, with `F` (l. 108) and `Carries` (l. 113).
  **`PathChart.eventually_compat`** (l. 119).
* **`exists_abelAlongW`** (l. 208): the Abel integral exists along any continuous path on the affine curve whose zeros
  of `y` are simple roots of `f`. That covers every path when `f` is squarefree.

### 2.14 `Follow.lean` (73 lines) and `PeriodPath.lean` (196 lines)
* `mumfordPts` (Follow l. 28): intrinsic Mumford coordinates of `(x₁, y₁) + (x₂, y₂)`.
* **`localExp_follow`** (Follow l. 39), genus 2. Take two path Abel integrals `A₁, A₂` along a moving generic divisor
  `D(t)`. Near every `s`, the local exponential based at `D(s)` maps `z(s) + (A(t) − A(s))` to `mumfordPts D(t)`,
  where `A = A₁ + A₂`. **This is the hook for a4** (§3).
* In `PeriodPath.lean`:
  - `IsAbelAlongW` (l. 29), `.continuousOn` (l. 41), `.hasDerivAt` (l. 79, in both chart types);
  - **`.curveIntegral`** (l. 95): for piecewise-`C¹` data whose `Yp` has countable zeros, `(A 1)_j = ∫ᶜ x^j dx/y`.
    The proof uses FTC off a countable set (`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`), and the
    endpoints may be singular.
  - `f₅ = 4x⁵ + 1` (l. 133).
  - **`abelAlong_liftPath`** (l. 142): along `[ζ^e]ℓ`, which crosses the Weierstrass point at `t = 1/2`, the Abel
    integral exists and `(A 1)_j = ((−1)^j/5)(ζ^e)^{j+1}B((j+1)/5, (j+1)/5)`.
  - **`period_eq_abelAlong`** (l. 186): `∫_{[ζ^e]γ} x^j dx/y = A_e(1)_j − A_{e+1}(1)_j`, for two Abel integrals along
    paths with the same endpoints `(0, −1) → (0, 1)`.

### 2.15 New top-level theorems of checkpoint 2
* `LSG.JacAn.WeierChart.exists_of_root`, `LSG.JacAn.WeierChart.hasDerivAt_branch`, `LSG.JacAn.InfChart.exists_of_lc`,
  `LSG.JacAn.InfChart.hasDerivAt_branch`.
* `LSG.JacAn.hasFDerivAt_localExp`, `LSG.JacAn.localExp_ode`.
* `LSG.JacAn.exists_patch`, `LSG.JacAn.patch_unique`, `LSG.JacAn.LocalBranch.I_sub_eq`, `LSG.JacAn.exists_abelAlong`,
  `LSG.JacAn.abelAlong_branch`, `LSG.JacAn.abelAlong_unique`, `LSG.JacAn.IsAbelAlong.curveIntegral`.
* `LSG.JacAn.exists_abelAlongW`, `LSG.JacAn.IsAbelAlongW.curveIntegral`.
* `LSG.JacAn.localExp_follow`, `LSG.JacAn.abelAlong_liftPath`, `LSG.JacAn.period_eq_abelAlong`.

The import roots that cover everything are `LSG.JacAn.PeriodPath`, `LSG.JacAn.Follow`, `LSG.JacAn.LocalExpODE` and
`LSG.JacAn.AbelLocal`.

---------------------------------------------------------------------------------------------------------------------

## 3. Plan for the rest of A2 (a4, a5, the a6 plug-in)

**Key structural fact [Proved, standard].** The origin `0 ∈ J` is not in the Mumford chart `J ∖ Θ`, since `Θ ∋ 0`. The
divisor `2∞` sits on the curve `{P + ιP}` that `Sym²C → J` contracts. So no chart of `Sym²C` gives `exp` near
`z = 0`; the local exp lives near *generic* `z₀`.

ABVAR a4's `exp(z) = [2^k]exp(z/2^k)` must therefore be read through a translate. **Design:**
`E(z) := law(Dupᵏ(Ψ(z₀ + z/2ᵏ)), neg(Dupᵏ(Ψ(z₀))))`
* `Ψ = grantEmb ∘ localExp` is the P⁸ embedding of the local exponential, analytic near `z₀` by
  `analyticAt_localExp`.
* Projective equality means that all 2×2 minors vanish.
* The lift to `ℂ⁹` is local. The entire nowhere-zero lift is A3's job.

| item | content | depends on | est. lines |
|---|---|---|---|
| a4 | Define `E` as above, for `k` with `z/2ᵏ` in the domain. **Independence of `k`**: `Dup(law(P, Q)) ∝ law(Dup P, Dup Q)` (A1, see §5, or from the identity theorem below) and the local doubling `Ψ(z₀ + 2w) ∝ law(Dup Ψ(z₀ + w), neg Ψ(z₀))`. The local doubling comes from S-G1/S-dup (§5) plus Abel: `abelSum_const` turns the Cantor relation `D + D' ∼ D''` into `A(D) + A(D') = A(D'')` near generic points. **Analyticity** on `ℂ²` by patching over `k`. **Homomorphism**: `E(z + w)` and `law(E z, E w)` are analytic in `(z, w)` and agree near one point, so `AnalyticOnNhd.eq_of_eventuallyEq` (on 2×2 minors) gives agreement everywhere. | A1 §5 items 1–3 | 1.5–2.5k |
| a6 plug-in | **E follows paths**. For a moving generic divisor `D(t)` with path Abel integrals `A₁ + A₂`: the set of `t` with `E(z₀ + A(t)) ∝ grantEmb(mumfordPts D(t))` is open in `[0,1]` (by `localExp_follow` and local agreement of `E` with `Ψ` up to translation, which comes from the homomorphism property) and closed (by continuity). Hence it is all of `[0,1]`; the tools are `patch_unique`/`abelAlong_unique`-style connectedness. Paths through Weierstrass points use `exists_abelAlongW`. **Surjectivity onto `J ∖ Θ`** follows (connect `D₀` to any generic `D`); onto `Θ` it needs A1 §5 item 5. | a4 | 0.4–0.8k |
| a5 | **Kernel.** `E(z(γ)) = 0`: by `period_eq_abelAlong`, `z([ζ^e]γ)` is a difference of path Abel integrals between the same endpoints, and the a6 plug-in applies. Discreteness comes from local injectivity of `abelInv` plus the homomorphism property. **Rank 4**: by `curveIntegral_cycleE` the four vectors `z([ζ^e]γ)`, `e = 0..3`, are `ζ^{(s+1)e}` times `z_s(γ)`. That is a Vandermonde determinant in `ζ`, and `B((s+1)/5, (s+1)/5) > 0`. | a4, a6 plug-in | 0.6–1.2k |
| a7 | Order 2: stage A3. The *upper bound* `log‖Φ(z)‖ ≤ c|z|²` is immediate from translate-and-double (`deg Dup = 4`, `4ᵏ ≍ |z|²`). The Appell–Humbert normalisation stays R-order2. | a4 | (A3) |
| optional | Paths through `∞` (an `InfChart` case in `PathChart`). Not needed while `D₀` and the paths stay affine. | — | 0.2–0.4k |

**Order:** a4 (as soon as A1 exposes §5 items 1–3), then the a6 plug-in, then a5.

---------------------------------------------------------------------------------------------------------------------

## 4. Revised A2 estimate

| | ABVAR (§5 / A0.6) | now |
|---|---|---|
| done (checkpoints 1 + 2) | — | 2.5k (measured) |
| remaining: a4, a6 plug-in, a5 | — | 2.5–4.5k |
| **A2 total** | 8–14k | **≈ 5–7k** |

**Risks now.**
* Everything left is **gated on A1** (§5).
* The analytic content of a6 is done, including the Weierstrass-point crossings needed by the period paths.
* R-G1 (the size of the chart identity law 0 = Cantor) is A1's risk.
* On the A2 side the remaining risk is engineering: projective equalities as 2×2 minors, and patching `E` over `k`.

---------------------------------------------------------------------------------------------------------------------

## 5. Interface A2 needs from A1 (for a4)

`STAGE_A1.md` did not exist when this section was written (A1 is still at the certificate checker, `LSG/Jac/Checker*`).
This is the **proposed** interface. Names are suggestions; A1 may rename and record the mapping. Conventions on the
A2 side:
* Mumford coordinates `m : Fin 4 → ℂ` are ordered `(s₁, s₂, b₁, b₀)`, with `a = x² − s₁x + s₂` and `b = b₁x + b₀`;
  see `mumford`/`mumfordPts`.
* The curve is `f₅ = C 4 * X^5 + C 1` (`LSG.JacAn.f₅`).
* `P⁸` points are `Fin 9 → ℂ` in A0.1 order `X₀..X₈`.
* Everything is over `ℂ`. Polynomial maps should be explicit functions, or `MvPolynomial` evaluations, so that
  analyticity is automatic (`AnalyticOnNhd.eval_mvPolynomial`, or `fun_prop`).

1. **Model data.**
   - `grantEmb : (Fin 4 → ℂ) → (Fin 9 → ℂ)`: the A0.1 basis, with `X₀ = 1`, `X₁ = b₁²/4 − s₁³ + s₁s₂`, …,
     `X₈ = b₀b₁/2 + 2s₁²s₂`.
   - `chartRel m : Prop` (`r₁ = r₀ = 0`), together with
     `chartRel m ↔ (X² − C s₁ X + C s₂) ∣ f₅ − (C b₁ X + C b₀)²`. The right-hand side is what A2 proves
     (`mumford_dvd`, `localExp_mem_chart`).
   - `quad : Fin 9 → (Fin 9 → ℂ) → ℂ`, the 9 quadrics, with `chartRel m → quad j (grantEmb m) = 0`.
2. **Polynomial maps.**
   - `law : Fin 9 → (Fin 9 → ℂ) → (Fin 9 → ℂ) → (Fin 9 → ℂ)`, the (2,2) laws `A^{(m)}`.
   - `dup : (Fin 9 → ℂ) → (Fin 9 → ℂ)`, which is `law 4 X X`.
   - `neg = diag(1,1,1,1,−1,−1,−1,−1,1)`.
3. **Semantics on the chart.** A2 consumes exactly these.
   - **S-Cantor.** Let `D = P₁ + P₂` and `D' = P₃ + P₄` be generic: `x₁..x₄` distinct and `yᵢ ≠ 0`. Let `c` be the
     cubic through `(xᵢ, yᵢ)`, `i = 1..4`, and let `x₅, x₆` be the other two roots of `f₅ − c²`. Define
     `cantorAdd (mumfordPts D) (mumfordPts D') := mumfordPts((x₅, −c x₅) + (x₆, −c x₆))`.
     This is the algebraic relation that `abel_local`/`abelSum_const` turn into
     `A(D) + A(D') = A(D'')`. A2 can also state it itself if A1 prefers to supply only `cantorAdd` as a rational map.
   - **S-G1.** For generic `m, m'` (an explicit nonvanishing condition, e.g. a resultant): `law 0 (grantEmb m)
     (grantEmb m')` is proportional to `grantEmb (cantorAdd m m')`, and the proportionality factor is nonzero there.
   - **S-dup.** `dup (grantEmb m)` is proportional to `grantEmb (cantorAdd m m)` on generic `m`. This is the
     tangent-line version of S-Cantor (`c` tangent at `P₁` and `P₂`).
   - **S-neg.** `neg (grantEmb m) = grantEmb (s₁, s₂, −b₁, −b₀)`.
4. **Not needed from A1:**
   - `Dup ∘ law ∝ law ∘ (Dup × Dup)`. A2 gets it from the identity theorem once `E` is analytic.
   - Completeness and the V1/V2′ identities. These are needed only by A4's ME.
5. **Later, for surjectivity onto `Θ`:** the points of the model with `X₀ = 0` correspond to classes of degree `< 2`.

---------------------------------------------------------------------------------------------------------------------

## 6. Answer to STAGE_A1 §4.2/§6: does (E1) + `localExp_ode` give what a4 needs?

**Verdict: partly.**
* **Confirmed: the local translation law.** (E1) + `localExp_ode` replace S-G1 for *translation by a fixed point*,
  with no Cantor and no Abel. Two A2-side lemmas are needed, and both are cheap:
  - **(N1)** `grant ∘ localExp` solves the flow, `∂_j X̂ = W_j(X̂)`.
    + This is the push-forward of `odeVF` along `grant`. I checked it **exactly in sympy**: of the 16 identities,
      11 hold identically and 5 hold modulo `r₁, r₀`, with cofactors of degree `≤ 2`.
    + So A1's `flow_W.json` and A2's `odeVF` agree. The Lean proof is next on A2's list.
  - **(U)** Uniqueness for the flow system on `ℂ²`: two analytic solutions of `∂_j V = W_j(V)` that agree at one
    point agree on a connected neighbourhood. Restrict to real segments `t ↦ w₀ + tξ` and use Mathlib
    `ODE_solution_unique_of_mem_Icc` (polynomial `W` is Lipschitz on compact convex sets).
  - Then for `Y ∈ V(Q)` fixed, `w ↦ [lawPt 0 (Ψ(z₀ + w), Y)]` solves the flow wherever its `X₀` is nonzero. This uses
    (E1), the chain rule and (N1). By (U) it equals any other local solution with the same value at one point.
* **Refuted: (E1) alone does not give translate-and-double.** Two gaps:
  1. **Doubling.** `dup = law 4` on the diagonal, and law 0 vanishes identically there (`P − P = 0 ∈ Θ`). So (E1)
     says nothing about `dup`. The rank-one transfer law 0 → law 4 needs points where both are nonzero, and on the
     diagonal there are none.
     - A4 needs **(E2) `dup`-equivariance**: `dup₀ D_j dup_l − dup_l D_j dup₀ ≡ 2 X₀ W_{jl}(dup)` mod `I(X)`. It is a
       single-copy identity, degree 9 in `X`.
     - Equivalently, (E1) for law 4 in the first argument plus (S2) gives (E2) on the diagonal by the chain rule.
  2. **Anchors.** (U) needs agreement at a point where both sides are *affine*.
     - Without Cantor the only anchors are `lawPt 4 P P = dup P` (definition) and `law0_origin`
       (`law0(x, O) ∝ x`).
     - The second sits at the origin, which is on `Θ`, i.e. not affine in the chart `X₀ = 1`.
     - In translate-and-double every identity used must be anchored. Examples: "`dup ∘ Ψ` is the translate of
       `Ψ(2·)`", "translate by `P₀`, then by `−P₀`, is the identity", and "`dup` is a homomorphism".
     - Anchoring at an explicit algebraic base point `P₀` would mean many exact evaluations; I don't recommend it.

**Recommended a4 design: a germ at the origin, then doubling.** It needs one more chart.
* `F(w) := lawPt 0 (Ψ(z₀ + w), negP P₀)`, with `P₀ = Ψ(z₀)`. This is a projective-analytic germ at `w = 0` with
  `F(0) ∝ origin`.
* `E(z) := dupᵏ(F(z/2ᵏ))`.
* **Independence of `k`.** Both `dup(F(v))` and `F(2v)` solve the flow near `v = 0`, and both equal the origin at
  `v = 0` (using `dup(O) ∝ O`). Anchoring there needs the flow **in the chart `X₄ = 1`**, where `O = e₄` is affine;
  there (U) applies.
* **Homomorphism.** Compare `w ↦ lawPt 0 (E z, E w)` with `w ↦ E(z + w)` near `z = 0`, anchored by `law0_origin` +
  (S2). Then use the identity theorem on the 2×2 minors of the analytic lifts.
* **Link to `Ψ`.** `lawPt 0 (E w, P₀) ∝ Ψ(z₀ + w)`, anchored at `w = 0` by `law0(O, P₀) ∝ P₀`. This is what the a6
  plug-in (`localExp_follow`) uses.

**Requests to A1**, in priority order. Sizes are my estimates against §4.2:

| id | statement | size |
|---|---|---|
| (E1) | as in §4.2: law 0, first argument, `j = 1, 2`, `l = 1..8` | as planned |
| (S2) | `A(Y, X) = ±A(X, Y)` as a data identity (gives second-argument equivariance) | planned, 0.2k |
| (E2) | `dup`-equivariance, single copy (or (E1) for law 4) | ≈ (E1) |
| (W4) | the flow in the chart `X₄ = 1`: quadratics `W⁽⁴⁾_{ji}` (Wronskians with respect to `X₄`; they exist because `θ₀·(θ₄∂_jθ_i − θ_i∂_jθ₄) = θ₄W_{ji}(θ) − θ_iW_{j4}(θ)`, and the Wronskians lie in `H⁰(6Θ) = Sym² H⁰(3Θ)` by projective normality), and (E1)/(E2) in chart-4 form (`A₄`, `dup₄`, `W⁽⁴⁾` in place of `A₀`, `dup₀`, `W`). The chart-4 forms do not follow from the chart-0 forms without `X₀` being a non-zero-divisor mod `I(A)`, which is essentially primality; so certify them directly. | ≈ 2 × (E1) |
| (P) | pointwise facts: `A_k^{(0)}(X, negP X) ≡ 0` mod `I(X)` for `k ≠ 4` (single copy, degree 4; or via (S1) and the vanishing of row 0 on the diagonal); `dup(origin) = c · origin` with `c ≠ 0` (one evaluation) | small |
| (glue) | `AnalyticAt` of `lawPt`, `dup`, `grant`, `negP` (polynomial maps) | 0.1k |

**On the A2 side:** (N1), (U), analytic lifts and the 2×2-minor calculus, and a witness that the base point is
nondegenerate (`X₀(2P₀) ≠ 0`, i.e. `A_4^{(0)}(P₀, negP P₀) ≠ 0`). Estimate: a4 is 1.5–2.5k, unchanged.

**Alternative.** If A3 builds the entire theta lift `θ` first, then (F1) + `law0_origin` + `rank_one` give the global
law (STAGE_A1 §4.2). In that case a4 reduces to "θ near `z₀` is `Ψ`", which is (N1) + (U), and none of (E2), (W4) or
(P) is needed. Which route to take is the coordinator's call: (E1)+(E2)+(W4)+(P) for a4 now, or (F1) and wait for A3.

---------------------------------------------------------------------------------------------------------------------

## 7. a4 progress: route 1 (coordinator decision), checkpoint 3

**Done in Lean.** There are 5 new files (809 lines), not committed. No `sorry`. All 17 audited theorems print
`[propext, Classical.choice, Quot.sound]`. All of a4 builds against the interface `A1Facts`; the files do not import
`LSG/Jac`.

* **(U)** `Flow.lean`.
  - `flowW` is A1's table, with A2 index `j = 0, 1` equal to A1's `1, 2`; `contDiff_flowW`.
  - `flowCLM`, and `IsFlowSol W c k V w` (`V w k = 1` and `DV = c·W(V)`).
  - **`flow_unique`**: two solutions on a ball that agree at the centre agree on the ball. It works for any `C¹`
    fields `W` and any speed `c`. The proof restricts to real segments and uses `ODE_solution_unique_of_mem_Icc_right`
    with Lipschitz bounds on a compact ball.
* **(N1)** `FlowGrant.lean`.
  - `grantJ` equals A1's `grant`, coordinate by coordinate.
  - `chartR1J`/`chartR0J` equal A1's `chartR1`/`chartR0`. `chartR_mumfordPts`: the chart relations hold at the Mumford
    coordinates of a pair of points.
  - **`grant_localExp_flow`**: `grantJ ∘ localExp` is a chart-0 solution of `flowW` near `z₀`. Lean checks all 16
    push-forward identities; 5 of them use the chart relations. So A1's `flow_W.json` agrees with A2's `odeVF`.
* **Interface and transport** `A1Facts.lean`.
  - `structure A1Facts` lists the fields below.
  - `derivAlong` is the formal `D_j`.
  - **`hasFDerivAt_normalize`**: the projective flow equation `Z_c DZ_l − Z_l DZ_c = κ W(Z)` implies that `Z/Z_c`
    solves `DV = κ W(V)`.
  - **`law0_transport₀`** and **`law0_transport₄`** (from E1); **`dup_transport₄`** (from E2, speed 2).
* **Germ and local doubling** `Germ.lean`.
  - `germ w = normalize 4 (law0 (Ψ(z₀+w)) (negP P₀))`.
  - **`germ_zero`** (`= e₄`) and **`eventually_germ_flow`** (a chart-4 solution near 0).
  - **`germ_dup`**: `normalize 4 (dup (germ v)) = germ (2v)` on a ball. This is (U) anchored at the origin in the chart
    `X₄ = 1`.
  - The base nondegeneracy `hP₀ : law0 P₀ (negP P₀) 4 ≠ 0` is a hypothesis; it means `X₀(2P₀) ≠ 0`.
* **Global exponential** `Exp.lean`.
  - `germ_good` collects the germ data; `GermRad` and `exists_germRad` give the radius.
  - `expLift k z = dupᵏ(germ(z/2ᵏ))`.
  - **`expLift_succ`**: consecutive lifts differ by a nonzero scalar, i.e. independence of `k`.
  - **`expLift_ne_zero`**, which uses (P2).
  - **`expP : ℂ² → ℙ(ℂ⁹)`** (Mathlib `Projectivization`). **`expP_eq`**: `expP z` is the class of every admissible
    lift. **`analyticAt_expLift`**: so `expP` is projective-analytic.

**`A1Facts` fields: exact statements for A1 to certify.** Here `law0 = LSG.Jac.lawPt 0`, `dup = LSG.Jac.dup`,
`negP = LSG.Jac.negP` and `OnQ = LSG.Jac.OnQ`. `dlaw0 i X Y` and `ddup i X` are the formal `∂/∂X_i`, and
`derivAlong W j dF X = Σ_i W j X i • dF i X`. A2's `j = 0, 1` is A1's `j = 1, 2`.

| field | statement (on `OnQ X`, `OnQ Y`) | status |
|---|---|---|
| `E1_4` | input chart 0, output chart 4: `law0 X Y 4 * D_j(law0·Y)_l − law0 X Y l * D_j(law0·Y)_4 = X 0 * W4 j (law0 X Y) l`, `D = derivAlong flowW` | A1 (E1) |
| `E1_40` | input chart 4, output chart 0: `law0 X Y 0 * D⁴_j(law0·Y)_l − law0 X Y l * D⁴_j(law0·Y)_0 = X 4 * flowW j (law0 X Y) l`, `D⁴ = derivAlong W4` | A1 (E1, chart-4 input) |
| `E1_44` | input chart 4, output chart 4: `law0 X Y 4 * D⁴_j(…)_l − law0 X Y l * D⁴_j(…)_4 = X 4 * W4 j (law0 X Y) l` | A1 (E1, chart-4 input) |
| `E2_4` | `dup X 4 * D⁴_j dup_l − dup X l * D⁴_j dup_4 = 2 * X 4 * W4 j (dup X) l`, `D⁴ = derivAlong W4` | A1 (E2, chart 4) |
| `W4`, `W4_four`, `W4_smul`, `W4_contDiff` | the chart-4 quadratics (Wronskians with respect to `X₄`), `W4 j X 4 = 0`, homogeneous of degree 2, `C¹` | A1 data + trivial |
| `W4_origin_indep` | `W4 0 e₄ 1 * W4 1 e₄ 8 − W4 0 e₄ 8 * W4 1 e₄ 1 ≠ 0` (the flow at `O` is transversal in the coordinates `(X₁, X₈)`; A1's values `W4 0 e₄ 1 = −1/2`, `W4 1 e₄ 8 = 1`) | A1 (evaluation) — **new, checkpoint 5** |
| `W4rel` | `X 4 * flowW j X l = X 0 * W4 j X l − X l * W4 j X 0` | A1 (cubic, single copy) |
| `special_hP₀` | for some `α` with `α⁵ = 2` (e.g. the real root): `law0 P₀ (negP P₀) 4 ≠ 0` at `P₀ = grantJ (mumfordPts' 0 (−1) α 3)`, i.e. the base divisor `(0, −1) + (α, 3)` is nondegenerate (`X₄(2P₀) ≠ 0`) | A1 (one evaluation in `ℚ(2^{1/5})`) — **new, checkpoint 6** |
| `onQ_closed` | `IsClosed {X | OnQ X}` | A1 (from `onQ_iff`) — **new, A3 batch** |
| `negP_eq` | `negP X = (X₀, X₁, X₂, X₃, −X₄, −X₅, −X₆, −X₇, X₈)` | A1 (definitional) — **new, A3 batch** |
| `lawK`, `law0_lawK` | the 81 coordinates `A32 k m`; `law0 X Y k = lawK k 0 X Y` | A1 (definitional) — **new, A3 batch** |
| `lawK_S1` | `lawK k m X (negP Y) = lawK m k X Y` | A1 `law_S1` (proved) — **new, A3 batch** |
| `rank_one` | `OnQ X → OnQ Y → lawK k m X Y · lawK 0 0 X Y = lawK k 0 X Y · lawK 0 m X Y` | A1 `rank_one` (proved) — **new, A3 batch** |
| `lawK_smul_left/right` | bidegree (2, 2) | A1 (homogeneous data) — **new, A3 batch** |
| `lawK_analytic` | analytic in `(X, Y)` | A1 (glue) — **new, A3 batch** |
| `W4_negP` | `OnQ X → W4 j (negP X) = negP (W4 j X)` (sign forced by `W4rel`) | A1 (data check) — **new, A3 batch** |
| `onQ_quad` | `OnQ X → ∀ j, quadA X j = 0` (`quadA` = copy of `LSG.Jac.quad` in `A1Facts.lean`) | A1 (`onQ_iff`) — **new, Taylor batch** |
| `W4num`, `W4den`, `W4den_pos`, `W4H`, `W4num_bound`, `W4_table` | `W4 j X l = Σ_{a,b} (W4num j l a b / W4den) X_a X_b`, `|W4num| ≤ W4H` | A1 (`W4.lean` data) — **new, Taylor batch** |
| `W8`, `W8num`, `W8den`, `W8den_pos`, `W8H`, `W8num_bound`, `W8_table` | the chart-8 quadratics (Wronskians with respect to `X₈`) as an explicit table | A1 (generate like `W4`) — **new, Taylor batch** |
| `W8rel` | `OnQ X → X 8 * flowW j X l = X 0 * W8 j X l − X l * W8 j X 0` | A1 (cubic identity, like `W4rel`) — **new, Taylor batch** |
| `W8_eight` | `W8 j X 8 = 0` | A1 (data) — **new, Taylor batch** |
| `law0_neg` | `law0 X (negP X) k = 0` for `k ≠ 4` | A1 (P) |
| `dup_origin` | `∃ c ≠ 0, dup e₄ = c • e₄` | A1 (P, evaluation) |
| `dup_ne_zero` | `X ≠ 0 → dup X ≠ 0` on `V(Q)`. **New (P2)**: completeness of law 4 on the diagonal. A single-copy Nullstellensatz certificate `X_i^N ∈ (dup) + I` is possible; cost unknown. Alternatively A3's ψ-argument. | **open: A1 to assess** |
| `law0_swap`, `swapSign` | `law0 Y X = s • law0 X Y`, `s ≠ 0` | A1 (S2) |
| `law0_onQ`, `dup_onQ`, `negP_onQ`, `origin_onQ`, `grantJ_onQ`, `onQ_smul` | model preservation | A1 has `law0_onQ` (V1), `negP_onQ`, `origin_onQ`, `grant_onQ`; `dup_onQ` needs a V1-type certificate for law 4 on the diagonal |
| `law0_origin` | `law0 X e₄ = (−8 X₀) • X` | A1 has it |
| `law0_smul_left/right`, `dup_smul` | bihomogeneity, degree 4 | trivial from the data |
| `hasFDerivAt_law0`, `hasFDerivAt_dup`, `law0_analytic`, `dup_analytic` | glue: derivative equals the formal partials, analytic | A1 glue, 0.1k |

The fields `law0_smul_*` and `law0_swap` are not used yet. They are what the homomorphism step
needs (below).

**Next (a4 rest, then the a6 plug-in and a5).**
* The **projective flow equation** `PF^{[c]}(G): G_c DG_l − G_l DG_c = κ W^{[c]}_l(G)` is invariant under `G ↦ λG` and
  is an analytic identity.
  - Near 0, `expLift k ∝ germ`, by iterating `germ_dup`. So `PF⁴(expLift k)` holds near 0, and by the identity theorem
    on the whole ball of radius `2ᵏε`.
  - `W4rel` plus the witness `W4_origin` give `PF⁰` as well.
* **Homomorphism.** Compare `z ↦ law0(Ẽ z, Ẽ w)` and `z ↦ Ẽ(z + w)`.
  - Both satisfy `PF⁰`: the first by `E1_0` plus Euler homogeneity, extended by density; the second by the above.
  - At `z = 0` they agree projectively: `law0(e₄, Ẽ w) ∝ Ẽ w` by `law0_origin` and `law0_swap`.
  - (U) gives agreement for generic `w`; the identity theorem on 2×2 minors gives all `(z, w)`.
* **Link.** `law0(Ẽ w, P₀) ∝ Ψ(z₀ + w)`, the same way.
* Then the a6 plug-in (`localExp_follow`) and a5 (§3).
* Estimate for the rest of a4: 0.7–1.2k lines.

### 7.1 Interface change (after STAGE_A1 §8.6)

* **`W4_origin` is removed.** A1 showed it is false: `X₀` vanishes to order 3 along Θ, so `W4 j e₄ 0 = 0`.
  - It was used only to show that `Ẽ` leaves Θ near 0, i.e. as a density witness for the chart-0 version of E1.
  - That step is now avoided altogether, so neither `W4 0 e₄ 1 ≠ 0` nor any other witness is needed.
* **E1 is now needed with chart-4 input.**
  - `E1_0` (input chart 0, output chart 0) is **dropped**.
  - `E1_40` (input 4, output 0) and `E1_44` (input 4, output 4) are **added**.
  - `E1_4` (input 0, output 4, used by the germ) is kept.
  - Reason: near `z = 0` the exponential is in the chart `X₄ = 1` (`Ẽ(0) = e₄`), and the transports start there. A1's
    plan for `E2_4` already builds the chart-4-input machinery.
* **The remaining a4 steps avoid any witness that `Ẽ` leaves Θ.** Write `T(w) := law0(Ẽ w, P₀)`.
  1. Link: `T(w) ∝ Ψ(z₀ + w)`. It is anchored at `law0(e₄, P₀) ∝ P₀`, which is affine.
  2. Translated homomorphism: `law0(Ẽ z, T(w)) ∝ T(z + w)`. It is anchored at `law0(e₄, Ψ(z₀ + w)) ∝ Ψ(z₀ + w)`,
     which is affine.
  3. Inversion: `Ẽ(a) ∥ law0(T(a), negP P₀)` for all `a`, by the germ definition near 0 and the identity theorem.
  4. Periods: `T(c) ∝ P₀` implies `E(z + c) = E(z)` for all `z`.
  None of these needs `Ẽ(w)₀ ≠ 0`.
* **Signs.** `law0_swap` has `swapSign = −1` (A1). P2 (`dup_ne_zero`) stays a named hypothesis, pending A3, as the
  coordinator decided.

### 7.2 Checkpoint 4: the global flow equation, homomorphism, link, the a6 plug-in, and the a5 rank

There are 5 new files (1041 lines), not committed. No `sorry`. All 19 audited theorems print
`[propext, Classical.choice, Quot.sound]`. Everything is still against `A1Facts`, with the corrected fields of §7.1.

* **`PF.lean`: the projective flow equation.**
  - `PFAt W κ c G w` states `G_c DG_l − G_l DG_c = κ W_l(G)`.
  - It holds for flow solutions (`of_flowSol`) and gives one after normalisation (`hasFDerivAt_normalize`).
  - It is invariant under rescaling (`smul`, `of_eventually_smul`) and translation (`comp_add`).
  - Chart switch 4 → 0 is `A1Facts.PFAt_chart` (W4rel; it divides by `G₄`, not `G₀`).
  - **`PFAt.of_eventually`** is the identity theorem.
  - `analyticOnNhd_flowW`.
  - `A1Facts.PFAt_law0_40` and `A1Facts.PFAt_law0_44` (E1 with chart-4 input).
* **`ExpGlobal.lean`.**
  - `expLift_near0`: `Ẽ ∝ germ` on `ball 0 ε`.
  - **`PF4_expLift`** and **`PF0_expLift`**: on the whole ball of radius `2ᵏε`, `E` satisfies the flow equation in both
    charts, i.e. the global flow equation.
  - `transP k w = law0 (Ẽ w) P₀ =: T(w)`. **`PF0_transP`**: `T` satisfies PF⁰.
  - **`link`**: `normalize 0 (T w) = Ψ(z₀ + w)` near 0.
* **`ExpHom.lean`.**
  - `Par` is parallelism (all 2×2 minors vanish), with its calculus; **`par_of_eventually`** is the identity theorem for
    it.
  - **`hom_trans`** (translated homomorphism): `law0 (Ẽ z) (T w) ∥ T(z + w)` for `z, w, z + w ∈ U`. It is proved near
    `(0, 0)` by (U) anchored at `Ψ`, then on the convex domain by the identity theorem in `ℂ² × ℂ²`.
  - **`inv_trans`**: `Ẽ a ∥ law0 (T a) (negP P₀)` on `U`.
  - **`periodic_of_trans`** / **`expP_periodic`**: `T(c) = λP₀`, `λ ≠ 0`, implies `E(z + c) = E(z)`.
  - These are all the group-law facts that a5 and the ME need, in translated form. The untranslated `E(z) ⊕ E(w) = E(z + w)`
    is not needed.
* **`ExpFollow.lean`: the a6 plug-in.**
  - **`follow_trans`**: for a continuous path of generic divisors `D(t)` from the base pair, with path Abel integrals
    `A = A₁ + A₂`, `T(A(t)) ∥ grantJ(mumfordPts D(t))` for all `t`. That is, `E(A(t)) ⊕ P₀ = [D(t)]`.
  - Proof: the set of good times is clopen in `[0,1]`, using (U) and `localExp_follow`.
  - Hypothesis `hT`: `T(A(t)) ≠ 0` along the path. `law0` vanishes exactly when `E(A(t)) − P₀ ∈ Θ`, which has complex
    codimension 1, so a generic path avoids it. Discharging it for the concrete paths is still to do.
* **`Rank4.lean`: the a5 rank.**
  - **`linearIndependent_perVec`**: the four period vectors `z([ζᵉ]γ)`, `e < 4`, are ℝ-linearly independent.
  - Proof: `perVec e j = c_j (ζ^{j+1})ᵉ` with `c_j ≠ 0` (Γ-values). A real relation gives a polynomial of degree `≤ 3`
    vanishing at `ζ, ζ²` and, by conjugation, at `ζ³, ζ⁴`.

**Remaining for A2.**
1. **`z([ζᵉ]γ) ∈ ker E`.**
   - By `expP_periodic`, it suffices to show `T(z(γ)) ∝ P₀`.
   - That follows from `follow_trans` along the loop `D(t) = γ(t) + Q₂`, but two pieces are missing:
     + (a) `localExp_follow`/`follow_trans` must cross the Weierstrass point of `ℓₑ` at `t = 1/2`. Either use a local
       exp with one `y`-chart (`WeierChart`; an Abel2 variant), or perturb `ℓₑ` inside the W-chart disc (the path Abel
       integral is unchanged; `exists_abelAlongW` machinery).
     + (b) The nondegeneracy `hT` along the loop: choose `Q₂` generically.
   - Estimate 0.5–1k lines.
2. **Discreteness of `ker E`.**
   - `E(c) = O` implies `T(c) ∝ P₀`, so by `expP_periodic` the kernel is a group.
   - Locally `E = germ` is injective near 0 if `DF(0)` is injective, i.e. the 2×2 minor of `(W4 0 e₄, W4 1 e₄)` on
     coordinates `(1, 8)` is nonzero. A1's values give `−1/2 · 1 − W4 0 e₄ 8 · W4 1 e₄ 1`.
   - **New interface field `W4_origin_indep`**: `W4 0 e₄ 1 * W4 1 e₄ 8 − W4 0 e₄ 8 * W4 1 e₄ 1 ≠ 0`, an evaluation for
     A1.
   - Estimate 0.2–0.4k lines.
3. **Surjectivity onto `J ∖ Θ`.** This is `follow_trans` plus path-connectivity of the generic divisor space, plus
   cancellation of `⊕P₀` (from `hom_trans`, `inv_trans`). Estimate 0.3–0.6k lines.

**Revised estimate for the rest of A2: 1–2k lines.**

### 7.3 Checkpoint 5: the kernel, the periods and translated surjectivity (`ExpKer.lean`, 321 lines)

No `sorry`. All 7 audited theorems print `[propext, Classical.choice, Quot.sound]`.

**Interface.** There is one new field, **`W4_origin_indep`** (table above). Its only use is the local injectivity of the
germ.

**(2) Discreteness and group property: done.**
* `germ_locInj`: `pr18 ∘ germ` (`pr18 = (X₁, X₈)`) has invertible derivative `germDerEquiv` at 0, by the inverse
  function theorem. So the germ is locally injective.
* **`expP_ker_small`**: `E c = E 0` with `c` small implies `c = 0`.
* **`expP_periodic_of_ker`**: `E c = E 0` implies `E(z + c) = E z` for all `z`, so `ker E` is a subgroup. The proof is
  `T c ∝ P₀` followed by `expP_periodic`.
* **`expP_ker_discrete`**: uniformly separated, so `ker E` is a discrete subgroup.
* With `Rank4.linearIndependent_perVec`, `ker E` is a lattice of rank 4 as soon as it contains the four
  `z([ζᵉ]γ)`, which is item (1).

**(1) Periods in the kernel: the core is done; the Weierstrass crossing is still open.**
* **`expP_periodic_of_two_paths`**:
  - Hypotheses: `T a ∥ X` and `T b ∥ X` for an affine `X` (`X₀ = 1`), with `T a, T b ≠ 0` and
    `law0 X (negP P₀) ≠ 0`.
  - Conclusion: `E(z + (a − b)) = E z`.
  - Proof: (U) near `b` for `T(· + a − b)` and `T`, then `inv_trans`, then `par_of_eventually`.
  - No loop or path concatenation is needed.
* **`expP_periodic_of_loop`**: two nondegenerate generic paths from the base pair to a common end divisor give
  `E(z + (A(1) − A'(1))) = E z`.
* **Remaining for `z([ζᵉ]γ)`.**
  - `period_eq_abelAlong` gives `z([ζᵉ]γ) = A_e(1) − A_{e+1}(1)` for the lifts `[ζᵉ]ℓ`, `[ζ^{e+1}]ℓ` from `(0,−1)` to
    `(0,1)`. Pair them with a fixed generic second point `Q₂`; the constant path has `A ≡ 0`.
  - But the lifts cross a Weierstrass point at `t = 1/2`, and `follow_trans` needs `y ≠ 0`.
  - **Chosen option: perturb inside the W-chart.**
    + On `[1/2 − η, 1/2 + η]` replace `Y = 2t − 1` by `Y' = 2t − 1 + iδ·max(0, η − |t − 1/2|)` and set
      `u' = X_W(Y')`.
    + The increment of the mixed Abel integral over the segment is `W.I(Y(t₂)) − W.I(Y(t₁))` for both paths.
    + This needs a lemma that a chart carrying the path on an interval computes the increments (the
      `abelAlong_branch` analogue for `IsAbelAlongW`), and constancy of `A' − A` on the subintervals where the paths
      agree. Then `A'_e(1) = A_e(1)`.
    + Estimate 0.3–0.5k lines, mostly piecewise continuity.
  - **Nondegeneracy (`hT` along the two perturbed paths, `law0(D_end, −P₀) ≠ 0`).**
    + Mathematically, generic `Q₂` works: for each `t` only finitely many `Q₂` are bad.
    + A Lean proof needs algebraic-geometry input (`Θ ∩ (curve translate)` is finite), or the complete system of laws
      (A3's ψ-argument, all 9 laws), which lets `follow_trans` switch laws where law 0 vanishes.
    + **Recommendation**: discharge `hT` through completeness. A1's P2 (`dup_ne_zero`) plan has the same source: the
      A3 ψ-argument, or a degree-7 Nullstellensatz certificate.
    + Until then the period theorem carries `hT` as hypotheses.

**(3) Surjectivity onto `J ∖ Θ`: done in translated form.**
* **`surj_trans`**: every generic divisor `D` reachable from the base pair by a nondegenerate generic path satisfies
  `T c ∥ grantJ D` and `Ẽ c ∥ law0 (grantJ D) (negP P₀)`, i.e. `E(c) = D ⊖ P₀`, with `c = A(1)`.
* Removing the translation (`D` itself in the image) needs either `P₀ ∈ E(ℂ²)` or cancellation of `⊕P₀`. Both are
  algebraic group-law facts on `A` (associativity of law 0 with `negP`). They follow from completeness plus
  `rank_one` (A3), and are not derivable from E1/E2 alone, because every anchor available sits at the origin or at
  affine translates.
* Path-connectedness of the generic divisor space is assumed through the path hypothesis.

**Revised estimate for the rest of A2: 0.3–0.5k lines** (the W-crossing perturbation). After that, A2 is complete
modulo the nondegeneracy hypotheses, which are gated on completeness (A3, or A1's P2-type certificate).

---------------------------------------------------------------------------------------------------------------------

## 8. The `hT` cycle: assessment and a cycle-free route

**The cycle.**
* A3's ψ-Liouville argument (ABVAR §A0.3 item 4) needs `Λ ⊆ ker E`.
* `expP_periodic_of_loop` needs `hT` (`T(A(t)) ≠ 0` along the paths) and `hXn`.
* I had proposed to get `hT` from completeness, i.e. from A3. That is circular.

**Diagnosis.** `hT` is an artefact of the proof, not of the mathematics.
* `T(w) = law0(Ẽw, P₀)` vanishes exactly when `E(w) − P₀ ∈ Θ`. This can genuinely happen along a path.
* `follow_trans` used `T(A(s)) ≠ 0` only to *normalise* at the start of each (U) step.
* Parallelism (all 2×2 minors vanish) is an analytic identity. The identity theorem (`par_of_eventually`) propagates it
  through zeros of `T`, so normalisation can be avoided.

### Options

| option | what it needs | verdict | est. |
|---|---|---|---|
| **(a)** concrete `Q₂`/`P₀` plus certified `T ≠ 0` along the paths | `T(A(t))` is not computable independently of the follow argument: `E` is defined by ODE plus doubling. A certified bound needs either certified numerics for `E` (interval ODE plus `dupᵏ` in Lean), or an algebraic criterion (`D(t) − 2P₀ ∉ Θ`, by resultants) whose link to `T(A(t)) ≠ 0` *is* the follow statement, which is circular. No dominant-term inequality in `Q₂` is apparent. | not recommended | 2–4k+, high risk |
| **(b)** genericity of `Q₂` | (i) base-independence of `E` (easy, by (U)); (ii) joint analyticity of `T` in `(w, Q₂)`; (iii) the zero set of `φ(t, q)`, holomorphic in `q` and real-analytic in `t`, has null projection to the `q`-plane. Item (iii) needs real-analytic paths, implicit-function/Weierstrass-preparation for the zero curves, and rectifiability. None of this is in Mathlib. | not recommended | 2–4k, high risk |
| **(c)** A1 certifies completeness of the 81 laws (`X_i⁴Y_j³ ∈ (laws) + I`) | A0.2 estimated `≳ 10⁶` terms per identity and `≥ 9` identities. Even with μ₁₀/[−1] symmetry, two-copy degree-(4,3) normal forms at the current throughput is a large job, and it still needs law switching in `follow` (+0.5k). | not needed for A2 (useful later for untranslated surjectivity) | A1 to estimate; likely ≫ P2 |
| **(d)** A3 with `Λ′ = ker E` | Rank 4 of `ker E` needs either the periods in the kernel (the same issue) or openness/compactness of `E(ℂ²) ⊆ A`, which needs the local manifold structure of `V(Q)` at every point (algebraic geometry) or properness. | not cheaper | — |
| **(e′) identity-theorem continuation** | below; no completeness and no nondegeneracy | **recommended** | **0.5–0.8k** (+ W-crossing 0.3–0.5k) |

### (e′) in detail [Proof sketch; all ingredients are already in Lean]
1. **Base-independent local exponentials.** At a generic divisor `D` let `Ψ_D(w) = grantJ(localExp_D(z_D + w))`.
   - It is a chart-0 flow solution, by (N1).
   - Two local exponentials at the same divisor, or at divisors along a path with matching values, agree near the
     common point. Both are chart-0 flow solutions with the same *affine* value (`X₀ = 1` always), so (U) applies.
   - With `localExp_follow`: `Ψ_{D(s)}(A(t) − A(s) + w′) = Ψ_{D(t)}(w′)` for `t` near `s` and small `w′`.
2. **Follow without `hT`.** Let `P(s)` be: `Par(T(A(s) + w), Ψ_{D(s)}(w))` for all `w` near 0.
   - **Upgrade.** `P(s)` near 0 implies `P(s)` on the whole ball where `Ψ_{D(s)}` is an analytic flow solution
     (`par_of_eventually`; the ball is connected and both sides are analytic).
   - **Open.** By the upgrade plus step 1, `P(s)` gives `P(t)` for `t` near `s`.
   - **Closed.** If `t_n → s` with `P(t_n)`, then by step 1 with base `s`, `Par(T(A(s) + ·), Ψ_{D(s)})` holds on an open
     set near `A(t_n) − A(s)`, hence on the whole ball.
   - **Start.** `P(0)` is `link` (plus step 1).
   - So `P(s)` holds for all `s ∈ [0,1]`, with no hypothesis `T ≠ 0`.
3. **Periods from two paths without nondegeneracy.**
   - Both paths end at `D_end`. So `Par(T(a + w), Ψ_end(w))` and `Par(T(b + w), Ψ_end(w))` near 0, with
     `Ψ_end(w)₀ = 1` as pivot. Hence `Par(T(a + w), T(b + w))` near 0.
   - On a ball `V` near `b` this gives `Par(T(u + c), T(u))`, `c = a − b`.
   - Three scalar analytic functions on the connected domain `U ∩ (U − c)` are not identically zero:
     + `T(u)₀`, nonzero at `u = 0`;
     + `T(u + c)₀`, nonzero at `u = −c`;
     + `law0(T(u), −P₀)_m`, nonzero at `u = 0`, by `hP₀`.
   - By a three-step density lemma (an analytic function not identically zero on a connected open set has no open zero
     set, which is the identity theorem), some open `V′ ⊆ V` has all three nonzero.
   - On `V′`, `inv_trans` gives `Par(Ẽ(u + c), Ẽ(u))`. By `par_of_eventually` this holds on the whole domain, so
     `E(z + c) = E z`.
   - **Neither `hT` nor `hXn` is needed.**
4. **W-crossing** (§7.3; independent). It replaces the lifts `[ζᵉ]ℓ` by `y ≠ 0` perturbations with the same Abel
   integral endpoints. Steps 1–3 then put `z([ζᵉ]γ)` in `ker E`.

**Cycle check.** A2 then delivers `Λ = ⟨z([ζᵉ]γ)⟩ ⊆ ker E`, discrete, of rank 4. It uses only standard axioms and
`A1Facts`, with no completeness and no `hT`. A3 can use `Λ` and then provide completeness. Completeness is used only
afterwards: for untranslated surjectivity, and for the translated form at the thin set where `T` vanishes.

**One remaining dependency to watch: P2 (`dup_ne_zero`).**
* It is used by `expLift_ne_zero`, i.e. so that `E` is a map to `ℙ⁸`, and therefore by every `expP` statement.
* If P2 came from A3's ψ-argument, the cycle would reappear (A3 → P2 → `expP` → Λ → A3).
* **Recommendation: A1 certifies P2** with the degree-7 Nullstellensatz certificate of STAGE_A1 §8.5 (≈ 1 CPU-h,
  0.5–1k lines).
* Alternatively, A2 can restate the kernel results at the lift level (`Par(Ẽ(z + c), Ẽ z)`, without `expP`), which
  needs no P2. A3's factor of automorphy, however, needs a nowhere-zero lift, so P2 is needed there anyway.

**Recommendation.**
1. A2: implement (e′) steps 1–3 (0.5–0.8k) and the W-crossing (0.3–0.5k). Total ≈ 0.8–1.3k. Drop `hT` and `hXn`
   from the period theorems.
2. A1: certify P2. Completeness (c) is optional and can come later from A3.
3. A3: proceed with `Λ` from A2. No cycle.

---------------------------------------------------------------------------------------------------------------------

## 9. Checkpoint 6: route (e′) and the Weierstrass crossing. `Λ ⊆ ker E`, discrete, of rank 4

**Result [Proved, Lean; standard axioms plus `A1Facts`].** For every base divisor and every germ radius
`G : GermRad A hp hx`, `LSG.JacAn.lattice_le_ker G` proves all four of the following:
* `perVec e ∈ kerE G` for all `e : ℕ`;
* `AddSubgroup.closure (range (perVec ∘ Fin 4)) ≤ kerE G`;
* `kerE G` is discrete;
* the four periods are `ℝ`-linearly independent.

Here `perVec e = z([ζᵉ]γ) = (∫_{[ζᵉ]γ} dx/y, ∫_{[ζᵉ]γ} x dx/y)` and `kerE G = {c | E c = E 0}`, an `AddSubgroup`.

**Hypotheses dropped.**
* There is no `hT` and no `hXn` anywhere on this route.
* The older `follow_trans` and `expP_periodic_of_loop` (with `hT`/`hXn`) remain in `ExpFollow`/`ExpKer`. They are
  superseded and nothing new uses them.

**Axiom audit.** The following print `[propext, Classical.choice, Quot.sound]`:
* `lattice_le_ker`, `expP_periodic_perVec`, `expP_base_indep`, `expP_periodic_of_paths`, `follow_par`,
  `exists_special_base`.

The audit file sits in the scratchpad, not in `Axioms.lean`. No `sorry` or `native_decide` occurs in `LSG/JacAn`.

### 9.1 New files (light builds, all compile)

**`ExpFollow2.lean` (333 lines), (e′) steps 1–3:**
* `flow_eventuallyEq`: step 1, chart-0 flow solutions with equal values agree nearby.
* `exists_ne_zero_of_open`: the density lemma.
* `psi_flowNear`, `FlowNear`, `FollowGood`.
* **`follow_par`**: step 2, follow in parallelism form, propagated through zeros of `T` by the identity theorem.
* **`expP_periodic_of_paths`**: step 3, two generic divisor paths from the base with a common end give
  `E (z + (A(1) − A′(1))) = E z`.

**`WCross.lean` (259 lines), the Weierstrass crossing:**
* `IsAbelAlong.toW`, `abelAlongW_agree`, `abelAlongW_chart`.
* `tent`, `pertY η t = 2t − 1 + i·max(0, η − |t − ½|)`, and `pertU = u + (X_W(pertY) − X_W(2t − 1))`.
* `carries_pert`, `pert_sq`, `pertY_ne_zero`, `continuous_pertU_diff`.
* **`abelAlong_perturb_eq`**: the perturbed path has the same Abel integral at `t = 1`.

**`PeriodKer.lean` (286 lines), assembly:**
* **`exists_pert_lift e`** replaces `[ζᵉ]ℓ` by a path with these properties:
  - `y ≠ 0` throughout;
  - the same endpoints `(0, −1) → (0, 1)`;
  - `|x| < 1` (since `|x_e(t)| ≤ 4/5`, and the perturbation is `< 1/5` by continuity of `X_W` at `0`);
  - the same Abel integral at `t = 1`, namely the Beta values of `abelAlong_liftPath`.
* `abelAlong_const`: a constant path has Abel integral `0`.
* **`exists_special_base`**: the base `D₀ = (0, −1) + (α, 3)`, `α⁵ = 2`, has a germ radius. This uses the new field
  `special_hP₀`.
* **`expP_periodic_special`** applies `expP_periodic_of_paths` at `D₀` to the divisor paths
  `D_e(t) = (x̃_e(t), ỹ_e(t)) + (α, 3)` and `D_{e+1}(t)`:
  - common end `(0, 1) + (α, 3)`;
  - `hdiag` holds because `|x̃| < 1 ≤ |α|`;
  - `k` is chosen from compact bounds on the path integrals.
  - Then `A_e(1) − A_{e+1}(1) = perVec e` (`period_eq_abelAlong`).
* **`expP_base_indep`**: `E` is independent of the base. Both germs are chart-4 `W4`-flow solutions with value `e₄`,
  so `flow_unique` applies and the lifts coincide for large `k`.
* `expP_periodic_perVec` (every base), `kerE`, **`lattice_le_ker`**.

### 9.2 Interface change: new `A1Facts` field `special_hP₀` (P3)

`special_hP₀ : ∃ α, α ^ 5 = 2 ∧ law0 P₀ (negP P₀) 4 ≠ 0` with `P₀ = grantJ (mumfordPts' 0 (−1) α 3)`. Also new is
`mumfordPts'`, a copy of `Follow.mumfordPts` placed in `A1Facts.lean`.
* **Meaning.** `X₄(D₀ ⊖ D₀) ≠ 0` under the explicit law, i.e. the base pair is nondegenerate for the germ.
* **Request to A1.** Evaluate the expression at one fifth root of 2, e.g. symbolically in `ℚ[α]/(α⁵ − 2)`, which is a
  field, so nonvanishing there holds at every root.
* **If it fails.** Any other affine point `Q = (x_Q, y_Q)` with `|x_Q| ≥ 1` works after a one-line change in
  `exists_special_base` and `expP_periodic_special`, where `hdiag` needs `|x_Q| ≥ 1`. The base `(0, −1)` is fixed by
  the lifts.
* **Why a field.** This is the only place a concrete base is needed. Every other base is reached by `expP_base_indep`.

### 9.3 Remaining dependencies

* **P2 (`dup_ne_zero`)** remains an `A1Facts` field. A1 is certifying it (§8). It is used by `expLift_ne_zero`, hence
  by `expP`.
* **P3 (`special_hP₀`)** is new. It is one evaluation.
* Untranslated surjectivity and the thin set where `T = 0` still need completeness (A3 or the 81-law certificate).
  `surj_trans` in `ExpKer` still carries its `hT`, which is not on the `Λ` route.
