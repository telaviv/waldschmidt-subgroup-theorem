# STAGE6_MXP: `Thm11KappaMXP` (Theorem MX′, `r = 2`) unconditionally

Started 2026-10-31. Labels as in PLAN.md. Target: lean_mstar's `CM4E.Gen.Thm11KappaMXP` (`CM4E/Gen/MXP.lean`),
via a verbatim copy `LSG/W88/MStarCopyMXP.lean`.

## 0. The statement is true as written [checked]
* `gmXP b` is the model of `G'' = G_i × G_ρ`, `G_i` = push-out of `(E_i^n)^♮` along `θᵀ` (tangent `(z_i, s₂)`),
  `G_ρ` likewise (tangent `(z_ρ, s₁)`). Class `𝒞` data: `d₀ = d₁ = 0`, `m = 2n`, curves `mxLs r = E_i^n ++ E_ρ^n`
  (as for MXG), `r = 2`, `M = [[0, θᵀ], [θᵀ, 0]]` (row 0 = `s₁` collects the `E_ρ` quasi-periods). `d₂ = 2n + 2 = m + r`.
* `lam`, `per`: same generators as `gmXG`, placed in other slots; the quasi-period values (`η(ϖ) = π/ϖ`,
  `η(iϖ) = −iπ/ϖ`, `η(Ω_ρ) = η_ρ`, `η(ρΩ_ρ) = ρ̄η_ρ`) were already checked for MXG (`perXG_le`, `lamGen_mem`).
* `sub`: the conclusion is equivalent to "`V` contains an algebraic `x` with `Ψ''(x) ≠ 0`". Every nonzero rational
  member `H` has such an `x`: if `T_H ⊆ ker Ψ''` then its fibre part is `0` (`Ψ'' = (s₁, s₂)` on the fibre), and a
  lattice point `λ = mϖ` of `t_i` gives `θᵀm = θᵀm̄ = 0`, so `m = 0` (same for `t_ρ`, `m = a + ρb`).
* `LiftAlg`, `PerTanRat` for `mxLs r`: proved (`liftAlg_mx`, `perTanRat_mx`). No `κ₁`-type premise is missing.
No premise issue found.

## 1. Why `Theorem41VecLA` does not suffice, and what is needed [Design]
* **No `r ≤ 1` presentation.** `rank M = 2`; a `G_a^{d₀}` factor contributes `0` to the extension class, so every
  class-`𝒞` presentation of `G''` (or a group mapping onto it) has `r ≥ 2`.
* **R-Λ is unavoidable.** For a hyperplane `V`, `V ∩ fibre` is `≥ 1`-dimensional; if it is a rational line or the
  whole fibre, `V` contains `(0,0,a,b)` algebraic with `Ψ'' = (a, b) ≠ 0` (trivial case). Otherwise `V ∩ fibre = ℓ`
  is an irrational line, and Prop. 2.1 must handle the direction `ℓ`. The fibre coordinates send periods to
  `θᵀη(Λ^n)` (rank `2n`, not discrete), and `ℓ` can lie in the `ℂ`-span of the `κ` periods (e.g. in Prop. D′'s
  own `V`), so no choice of coordinates puts the periods into a product of rank-2 lattices.
* **R-rat is unavoidable.** The obstruction from `MultEstVec` has no rationality; its fibre part may be an
  irrational line (e.g. `ℓ`).

## 2. Route [Design]
Prove a version of Theorem 4.1 that covers exactly what the §5d engine needs for MXP, then run the engine at `r ≤ 2`.

**`Theorem41Vec2`**: `Theorem41Vec` with premises `d₀ = 0`, `r ≤ 2`, `LiftAlg`, `PerTanRat`,
`dim (V ∩ fibre) ≤ 1` (instead of `r ≤ 1`, `V ∩ fibre = 0`).

### 2.1 Prop. 2.1 with one polynomial direction (R-Λ)
On `V` with `V ∩ fibre = ℂu`: coordinates `(x, t)`, `x` = base coordinates of `π(V)` (`π` forgets `s`; `π|V` has
kernel `ℂu`), `v = σ(x) + t u`. Then
* `MonoV.eval (p + t u)` is a polynomial of degree `≤ D` in `t` (fibre forms are affine in `s`);
* the multiplier `expMult(πω, πp)` does not see `t`; the periods are `ω = (x_ω, τ_ω)`, `x_ω` in the product lattice,
  `τ_ω` arbitrary but `|Σ y_i τ_i| = O(r)` for the integer combinations used by the grid;
* **`prop21LatT`**: `prop21Lat` with an extra variable `t`, functions polynomial of degree `≤ D` in `t`. Siegel
  conditions at (representative, `t`-node), `D + 1` nodes in `[0, r]`; the grid transfer and the final step use exact
  Lagrange interpolation in `t` (loss `≤ e·K^D`, absorbed by `D r² ≤ aU`, `r ≥ c₁`). The condition count gains a
  factor `D + 1`, paid by one power of `U` (`(D+1) log(R/r) ≤ 2U`), so `prop21_GVT_deg` has the interface of
  `prop21_GV_deg` with `dim (V ∩ fibre) ≤ 1` in place of `V ∩ fibre = 0`.
* `prop61V2_b` = `prop61V_b` verbatim with `prop21_GVT_deg`.

### 2.2 Rationality repair for `d₀ = 0`, `r ≤ 2` (R-rat)
`T′ = Γ_full + U^⊥ + perTan t` (complex obstruction), from §7: `q(λ + u + 2δ₂) ≤ e(δ_T − τ)`, `δ_T − τ ≥ 1`, `e ≥ 2q`.
* `Γ_full` rational: `H = (U, t, Γ_full)`, `T_H = T′`.
* Otherwise `Γ_full` is an irrational line in `ℂ²`. `T_S = T(dataRat) ⊆ T′ ⊆ T_E = T(U, t, ℂ²)`, `j' = dim T_E/T′ ≤ 1`.
  - **S** (`H = dataRat`): `λ` unchanged (`LiftAlg`, existing `inf_tanPerV_eq`), `δ₂ += j`, `δ += j`; works iff
    `τ_S ≤ τ` (uses `2q ≤ e`).
  - **E** (`H = (U, t, ℂ²)`): `λ_E ≤ λ`, `δ₂ −= j'`, `δ −= j'`; works iff `τ_E = τ − j'`.
  - **One of them works**: if E fails, `W ∩ T′ = W ∩ T_E` is rational (frame of `H_E`), every algebraic vector of `T′`
    lies in `T_S` (`PerTanRat`: algebraic lift in `perTanId`), so `W ∩ T′ ⊆ T_S` and S works.

### 2.3 §5d engine at `r ≤ 2`, `d₀ = 0`
`coreV_onto` with: frames for all `r` (`V_f` rational from `PerTanRat`, intersection with coordinate subspaces);
`perTanRat_comp`; `dim (V ∩ fibre) ≤ 1` from "no member in `V`" (the fibre is a member); Theorem 4.1 for the frame
group: `Theorem41Vec2` when (NR) holds (always if `f ≥ 1`), Roy / `corner_falseV'` when `f = 0` (existing).
`hyperplaneKappa_of_iso2` = `hyperplaneKappa_of_iso` at `r ≤ 2`.

### 2.4 MXP bridge
`mxpIota : TanV 0 0 (n+n) 2 ≃ TXP r`; `lamGen`, `per`, `sub` checks adapted from `V5dMXGcm.lean`.

## 3. Files [planned]
| file | content |
|---|---|
| `W88/MStarCopyMXP.lean` | verbatim copy of `gmXP`, `Thm11KappaMXP` |
| `W88/V5d2Stmt.lean` | `Theorem41Vec2`, `HyperplaneKappaVec2` |
| `W88/V5d2Frame.lean` | frames for all `r`, `perTanRat_comp`, rationality lemmas |
| `W88/V5d2Main.lean` | engine: `hyperplaneKappaVec2_of`, `hyperplaneKappa_of_iso2` |
| `W88/V5dMXP*.lean` | MXP instance and CM inputs, `thm11KappaMXP_uncond` |
| `AuxFun/Prop21LatT.lean`, `AuxFunV/PropGVT.lean` | §2.1 |
| `W88/Prop61V2.lean`, `W88/Sec7V2Rat.lean`, `W88/Sec7V2.lean` | §2.1–2.2, `theorem41Vec2` |

## 4. Status (2026-10-31): **DONE** [Lean]

```
theorem LSG.W88.V5d.thm11KappaMXP_uncond : LSG.W88.MStarCopy.Thm11KappaMXP
theorem LSG.W88.theorem41Vec2 : LSG.W88.Vec.Theorem41Vec2
theorem LSG.W88.V5d.hyperplaneKappaVec2_uncond : LSG.W88.Vec.HyperplaneKappaVec2
```
`#print axioms`: `[propext, Classical.choice, Quot.sound]`. No sorry/axiom/native_decide. Checked against unmodified
lean_mstar (scratch file, deleted):
```lean
theorem checkMXP : CM4E.Gen.Thm11KappaMXP := fun h1 h2 h3 h4 r b hb =>
  LSG.W88.V5d.thm11KappaMXP_uncond h1 h2 h3 h4 r b
    ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
```

| file | lines | content |
|---|---|---|
| `W88/MStarCopyMXP.lean` | 80 | verbatim `TXP`, …, `gmXP`, `Thm11KappaMXP` |
| `W88/V5d2Stmt.lean` | 48 | `Theorem41Vec2`, `HyperplaneKappaVec2` |
| `W88/V5d2Frame.lean` | 343 | `ratPair_inf_ker`, `rational_comap_inr`, `rational_Vf`, **`exists_frame2`** (all `r`), `topV_tan2`, **`perTanRat_comp`**, `finrank_inf_fibreV_le_one`, `trans_premises2` |
| `W88/V5d2Main.lean` | 288 | `coreV2`, **`hyperplaneKappaVec2_of`** |
| `W88/V5d2Iso.lean` | 120 | `hyperplaneKappa_of_iso2` |
| `W88/V5dMXP.lean` | 98 | `mxpM`, `mxpIota`, `mxpM_mulVec0/1`, `mxpM_alg` |
| `W88/V5dMXPcm.lean` | 387 | `lamGenP_mem`, `perXP_le`, `block_caseP`, `sub_mxp`, **`thm11KappaMXP_of`** (`Theorem41Vec2 → Thm11KappaMXP`) |
| `AuxFun/Prop21LatTAux.lean` | 334 | `eval_eq_sum_lagBasis`, `y_bound`, `tGrid` (+ card/norm/Lagrange bounds), `grid_smallT`, `final_arith2'` |
| `AuxFun/Prop21LatT.lean` | 343 | **`prop21LatT`** |
| `AuxFunV/PropGVT.lean` | 389 | `eval_add_fibre_poly`, `exists_coordsVT`, `prop21_GVT_one`, **`prop21GVT_of_le_one`** |
| `W88/Prop61V2.lean` | 362 | `Prop21DegV`, `prop61V2_b` (`prop61V_b` with Prop. 2.1 as hypothesis) |
| `W88/Sec7V2Rat.lean` | 275 | `alg_mem_dataRat`, `dataTop`, `finrank_dataTop_le`, **`exists_subgroupDataV_rat2`** |
| `W88/Sec7V2.lean` | 325 | `Prop21GVT`, **`theorem41Vec2_of`** |
| `W88/V5dMXPMain.lean` | 43 | `prop21GVT`, `theorem41Vec2`, `hyperplaneKappaVec2_uncond`, `thm11KappaMXP_uncond` |

Notes.
* `prop61V2_b` and `theorem41Vec2_of` are verbatim copies of `prop61V_b` / `theorem41VecLA_of_ME` with the changed
  lines only (no existing file was edited except `LSG.lean`, `Axioms.lean`).
* The engine needs no swap presentation: `multEstVec` covers every `M`, and (NR) holds whenever `f ≥ 1`.
* `Theorem41Vec2` is restricted to `d₀ = 0` (all groups in the MXP engine have `d₀ = 0`); the repair's dichotomy
  uses `dim T_E/T′ ≤ 1`, i.e. `r ≤ 2`. A general-`r` version would need an iterated dichotomy (or descent).
