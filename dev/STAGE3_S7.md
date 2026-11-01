# Stage 3, node D4: W88 §7 — `Theorem41Abelian` from Prop. 6.1 and `MultEstAb`

Started 2026-10-31. Labels as in PLAN.md. Sources: W88 pp. 396–397 (`../schanuel/five_exp/ref/w88_pages/w88-12.png`),
`../schanuel/five_exp/pilot_epi2_mix/FALSITY_HUNT.md` §1. Inputs: `LSG.W88.prop61_b` (Prop. 6.1, Remark B),
`LSG.ME.MultEstAb` (statement in `LSG/ME/MultEstStmt.lean`, proof in progress elsewhere).

## 0. Target

```
theorem LSG.W88.theorem41Abelian_of (hME : LSG.ME.MultEstAb) : Theorem41Abelian
```
(no `MultEstAbHyp`: the coordinator fixed `MultEstAb` as the interface.)

## 1. The bridge (Prop 6.1 gap 1) — `Sec7Taylor.lean`, `Sec7Bridge.lean`

* `Ppoly μs p = Σ_l p_l · mono(μ_l)`, `mono μ = Π X_i^{α_i} Π Y_j^{β_j} Π_k Π_t X(e k (cidx t))^{γ_{k,t}}`
  (cone index of the `ellW` index `t`: `cidx = ![2,0,1]`, i.e. `(σ³, σ³℘, σ³℘′) ↦ (W, U, V)`).
  `eval (ellCoords x) (Ppoly μs p) = Psi Ls μs p x`, `ellCoords x = liftX ellV x` (a cone representative of `expG x`).
  `IsHomE (Ppoly μs p) D`; block degrees `≤ (Σα, Σβ, D)`.
* `P ∉ I_G`: `I_G = vanish univ` (`vanish_univ`), and `Psi ≢ 0`. We use `P' = P · Π_k W_k` (degree `D + 1 ≥ 1`
  in every elliptic block; `I_G` prime, `W_k ∉ I_G`; formal order only increases under multiplication).
* **Analytic VanishAlong ⇒ formal `OrdGt`** (`ordGt_of_vanishAlong`). Taylor map `tps f = Σ tco_j(f) zʲ` is a ring
  hom on germs analytic at `0`, commutes with `d/dz` and with polynomial evaluation (`tps_eval`). For the analytic
  lift `Γ(s) = liftX F (y + s w)` in the canonical charts at `expG y` (`F_k` = `(℘, ℘′, 1)` off the lattice
  [W-chart], the `V`-normalised lift of `exists_VLift` at lattice points [V-chart]), `Γ′ = dval(Γ)`, so
  `tps ∘ Γ` is a formal flow with initial value `coords (expG y) 1`; by uniqueness (`eq_fflow`) it is `fexp`.
  Homogeneity: `Psi(y + s w) = Π_k ellV_{ch_k}(y_k + s w_k)^D · P(Γ(s))` near `s = 0`, unit factor
  (`iteratedDeriv_eq_zero_of_mul`). Only the order needed (`n < T`) is used; no global identification.

## 2. Counting modulo `G′` — `Sec7Count.lean`

* `Htil grp = exp⁻¹(grp)`; **`exists_mul_mem_tan_add_per`**: for `u ∈ Htil grp` some `N ≥ 1` has
  `N u ∈ T_{G′} + Per`. Linear part by polynomials vanishing on `exp(T_{G′})` (linear forms `⊥ h₀`, characters
  `Y^{φ⁺}Z^{φ⁻} − 1`, `φ ∈ U ∩ ℤ^{d₁}`, then a finite-index argument for `ℤ^{d₁} → ℤ^{δ₁}`); abelian part by
  `exists_abelianTangent_Htil` (finitely many cosets of `t′ + Λ`, `t′ = t` by `ObstrData.lie`).
* Hence `rk (Y ⊓ Htil grp) = rk (Y ⊓ (T_{G′} + Per))`, and with generators `y_j` of `Y` there are
  `λ = rk Y − rk(Y ⊓ (T_{G′}+Per))` indices independent modulo `Y ⊓ Htil grp`: the points
  `expG(Σ_{i≤λ} h_i y_{j_i})`, `0 ≤ h_i ≤ M`, are pairwise inequivalent mod `grp`, `|F| = (M+1)^λ`.

## 3. `ℚ̄`-rationality of `h₀` — `Sec7Rat.lean` (no descent needed)

`h₀″ = span_ℂ {a ∈ h₀ : a algebraic}` is `RationalOverQbar` and `⊆ h₀`. Replacing `h₀` by `h₀″`:
`λ` unchanged (G_a-coordinates of `y ∈ Y` are algebraic, so `y ∈ T + Per ⇒ y ∈ T″ + Per`), `δ″ − τ″ ≥ δ − τ`
(`dim(W ∩ T″) ≥ dim(W ∩ T) − (dim h₀ − dim h₀″)`), `δ₁, δ₂` unchanged; `d₁ + 2m − κ > 0` by (NR). So the
W88 inequality and `δ > τ` transfer from `O` to the `SubgroupData` `H″`. Item 3 of the task is closed without
weakening `SubgroupData`.

## 4. The inequality — `Sec7Arith.lean`, `Sec7.lean`

Prop 6.1 with `b = 2`: `Δ^q = C S^e (log S)^{2d₀}` (`q = d − n`, `e = d₁ + 2m − κ`). MultEstAb with
`S′ = {expG(Σ h_j y_j) : h_j ≤ M = ⌊S/(d₀+d₁+m)⌋}` (`Σ(n)` of it lies in the grid `h ≤ S`), `T′ = ⌊Δ/(2 n log S)⌋`,
`D₀ = ⌊Δ/log² S⌋ + 1`, `D₁ = ⌊Δ/S⌋ + 1`, `D₂ = D + 1`. With `|F| = (M+1)^λ`, dividing by `D^{t}`:
`T′^τ (M+1)^λ ≤ C′ D₀^{δ₀} D₁^{δ₁} D₂^{δ₂}`, logs:
`A log S ≤ K + B log log S`, `A = q(λ + δ₁ + 2δ₂) − e(δ − τ)`, `B = 2d₀(δ − τ) + q(τ − 2δ₀)`, `|A|, |B|, K` bounded
independently of `S`. One `S` large enough gives `A ≤ 0` (else `log S ≤ K + B log log S`), and if `δ ≤ τ` then
`δ = τ = δ₀ ≥ 1`, `λ = δ₁ = δ₂ = 0`, `B = −qδ₀ < 0`, contradiction. No pigeonhole over `S` is needed.

## 5. Status (2026-10-31): **DONE, conditional on `MultEstAb`**

```
theorem LSG.W88.theorem41Abelian_of (hME : LSG.ME.MultEstAb) : Theorem41Abelian
```
`#print axioms`: [propext, Classical.choice, Quot.sound]. No sorry/axiom/native_decide. Build:
`lake build LSG.W88.Sec7` (≈ 2.5 min on top of the Stage-2/Prop-6.1 oleans). Not imported by `LSG.lean`.
Combined with `LSG.W88.thm11Kappa_of_theorem41`, lean_mstar's `hW` now follows from `MultEstAb` alone.

| file | lines | content |
|---|---|---|
| `W88/Sec7Taylor.lean` | 92 | `tps` (Taylor series at 0), ring-hom/derivative/evaluation lemmas, **`tps_eq_fflow`** |
| `W88/Sec7Bridge.lean` | 391 | `monoPoly`, `Ppoly`, `eval_Ppoly`, `isHomE_Ppoly`, `Ppoly_mem_FLE`, **`Ppoly_notMem_IG`**, `Wprod`, `exists_chartLift`, **`ordGt_of_vanishAlong`** |
| `W88/Sec7Count.lean` | 424 | `fst_mem_h0`, `chr_eq_one_of_mem_grp`, `exists_rat_torus`, `exists_nsmul_ab`, **`htil_le_span`**, `span_inf_eq`, `exists_indep_mod`, **`exists_inequiv_grid`** |
| `W88/Sec7Rat.lean` | 135 | `ratPart`, `ratData`, `inf_tanPer_eq`, `finrank_inf_add_le`, **`exists_subgroupData_rat`** |
| `W88/Sec7Arith.lean` | 164 | `eventually_log_big`, **`core_ineq`**, `log_delta61`, `log_succ_le_of_le`, `floor_ge_half` |
| `W88/Sec7Aux.lean` | 133 | `exists_gens`, `exists_periods`, `obstr_delta_pos`, **`log_count`** |
| `W88/Sec7.lean` | 325 | `gridPts`, `sig_gridPts`, **`theorem41Abelian_of`** |

Key statements:
* `ordGt_of_vanishAlong (Ls) (μs p W) (hv : VanishAlong (Psi Ls μs p) W T y) (hn : (n : ℝ) < T) :
  OrdGt (g2L Ls) (g3L Ls) W (Ppoly μs p) n (expG Ls y)` — the analytic/formal identification is done only through
  Taylor coefficients at one point (uniqueness of formal ODE solutions), no global analytic continuation.
* `htil_le_span O : u ∈ Htil Ls O.grp_sub → u ∈ span_ℚ (O.tan + Per)` — needs only the `ObstrData` fields
  (`grp_eq`, `lie`, `grp_closed`), so it holds for whatever obstruction `MultEstAb` returns.
* `exists_subgroupData_rat O W Y (hY : Y ⊆ Lam)`: item 3 closed **without weakening `SubgroupData`** (no descent).

Remark B: used with `b = 2`; the case `δ = τ` gives `B = −qδ₀ < 0` in `A log S ≤ K + B log log S`.
Remaining gap for the unconditional `Theorem41Abelian`: only `MultEstAb` (`LSG/ME/MainAbWIP.lean`, other agent).
