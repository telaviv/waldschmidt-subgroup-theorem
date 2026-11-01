# STAGE A5: lean_lsg's AbVar theorem from `MultEstB` (consumer side)

Owner: A3 agent. Started 2026-10-31. Companion notes: `STAGE_A5_PROP21.md` (the Tier-3 Prop 2.1 study, *not* on this
path), `REVIEW_TORINJ.md` §3 (why Tier 1′ suffices under TorInj), `STAGE_A4.md` §6 (the frozen `MultEstB`).

Labels as in STAGE_A3: [Proved] = in Lean, standard axioms; [Proof] = complete paper argument here; [Est] = line
estimate (calibration: elliptic chain AuxFun ≈ 7k, Prop61 ≈ 1.1k, Sec7 ≈ 2k, K5d ≈ 2.5k).

## 1. Targets

* **T1** `Theorem41AbVarPer` (`LSG/W88/StatementAbVar.lean`), assuming `LSG.MEB.MultEstB`.
* **T2** `HyperplaneKappaAbVar` (the §5d form with `TorInjA`), from T1-type results for subgroups. T2 is what the
  bridge (A6) consumes; T1 is the stepping stone, exactly as `theorem41Abelian_of` feeds `K5dMain`.

## 2. Design decisions

**D1. A generic consumer over `AbBlock`s plus an analytic package.** The consumer (Prop 6.1, Lemma U, §7) is written for
`G = G_a^{d₀} × G_m^{d₁} × ∏_k B_k`, `B : Fin m → AbBlock`, in MEB's own types (`Tan`, `GPt`, `liftB`, `Per`), so that
`MultEstB` is consumed with no type translation. What a block must supply beyond the frozen `AbBlock` fields is a
separate structure `AbBlockAn b` (new file, mine; nothing in `LSG/MEB` changes):
* `lat ≤ b.per` with an ℝ-basis (`lat` = the periods we count; for A: `latt`). `per ≤ ℚ·lat` then follows from
  `per_discrete` (§3, the finite-index bridge).
* order-2 growth of `θ`;
* quasi-periodicity on `lat` in exponential-affine form `θ (z + ω) = exp (a ω + L ω z) • θ z`, with
  `‖a ω‖ ≤ c (1 + ‖ω‖)²`, `‖L ω‖ ≤ c (1 + ‖ω‖)`;
* Taylor algebraicity at `0`: for algebraic directions `w`, `s ↦ θ_l(s w)/θ_{i₀}(s w)` satisfies `KS ι A B e δ` (A3's
  `ks_chart4F` at `z₀ = 0`, `i₀ = 4`).

For the A-block every field is already [Proved] (`thetaN_order2`, `fac_affine`/`norm_facN`/`facN_bound`,
`ks_chart4F`, `latBasis`, `latt_le_kerE`); the instance is ≈ 0.2k once γ's `aBlock` exists. The generic form also
serves the X7 E-blocks later (M3) at the cost of their package only.

**D2. Lemma U only needs Taylor data at the origin.** Every point of `LamA` has its `A`-parts in `latt`, so on the grid
`θ (ω + s w) = exp (a ω + s L ω w) • θ (s w)`. `P` is block-homogeneous, so
`Ψ(u + s w) = κ · exp (s λ) · F(s)` with `κ ≠ 0`, `λ = D₂ Σ_k L ω_k w_k`, and
`F(s) = P(x + s w₀, y e^{s w₁}, θ(s w₂)/θ_{i₀}(s w₂)) · Π θ_{i₀}(s w₂)^{D₂}`. If all derivatives of order `< k`
vanish, then `∂^k Ψ(u + s w)|₀ = κ θ_{i₀}(0)^{D₂ m} ∂^k F̃(0)`, `F̃` with algebraic Taylor coefficients. `log |κ|^{-1} ≤
c D₂ S²`, which is inside the `(D + 1) S²` term of the Lemma U budget. So Lemma U is the elliptic one with
`ks_chart4F` in place of the `℘`-chart data, run on the induction over `k` that the elliptic proof already uses.
[Proof]

**D3. Prop 2.1 is Tier 1′ (`prop21Lin`).** Under `TorInjA V`, ℤ-independent `ω_i ∈ V ∩ PerA` have ℚ-independent toric
parts in `2πiℚ^{d₁}`, hence are ℂ-independent (REVIEW_TORINJ §3b). The multiplier for the monomials of block degree
`D` is `Π_k facN(ω_k, z_k)^D` (`thetaN_monomial_qp`), bounded by `exp (D b (‖z‖ + ‖ω‖)²)`; `prop21Lin` needs
`D b r² ≤ a U`, which Prop 6.1's parameters supply (`D r² ≤ U`). No lattice-adapted coordinates, no Tier 3.
TorInjA is inherited by `V ∩ T_{H′}` and by the projections of D6, so the §5d engine can call T1-type results freely.

**D4. Monomials.** Per block the monomials are `θ_{i₀}^{D−a−b} θ_{is 0}^a θ_{is 1}^b` (`(D+1)(D+2)/2 ≍ D²/2 = D^g/2`
of them; for A: coordinates 4, 1, 8). Nonvanishing of `Ψ` for `p ≠ 0`: a polynomial in `(x, y, (θ_{i₀}, θ_{is}))_k`,
homogeneous per block, vanishing on the image is `0`, because the ratios `θ_{is}/θ_{i₀}` are a local
diffeomorphism at `0` (`coords_locInv`) and `exp` is open, so the dehomogenised polynomial vanishes on an open set.
Generic over `AbBlock`. [Proof]

**D5. The finite-index bridge `latt` ↔ `per` (= `kerE` in γ's instance).** A discrete subgroup containing the ℤ-span of
an ℝ-basis lies in its ℚ-span: `n ↦ fract (n ω)` takes values in `per ∩ (fundamental domain)`, which is finite.
Consequences, all generic: `span_ℚ PerL = span_ℚ Per`, `rk (Y ⊓ PerL) = rk (Y ⊓ Per)` (finite index of
`Y ∩ PerL` in `Y ∩ Per`), `IsRatSub per t ↔ IsRatSub lat t` (so `ObstrDataB.t_rat` gives `IsAbelianTangentA`), and
`htil` transfers with a larger `N`. So the consumer can use either period group; T1/T2 are stated with `latt`, MEB
with `per`. [Proof; §3 is the Lean part]

**D6. §5d engine without transport through CM.** The elliptic engine transports Theorem 4.1 to `H′ = H₀ × T_U × B`
through `LSG.CM.Transport`. For `A^r` with `A` simple use the **pivot projection** instead (STAGE_A4 §1.3): there is
`J ⊆ Fin r` with `t_B → (ℂ²)^J` an isomorphism, and `π_J : B → A^J` is an isogeny. Theorem 4.1 for `H′` is pulled back
from T1 for `G_a^{k₀} × G_m^{k₁} × A^{|J|}` (points: `π_J(LamA) ⊆ LamA`; periods: `π_J(Ω_{H′})` of finite index in
`Ω(A^J)` by D5; subgroups: preimages). Roy's Theorem 1 when `B = 0`, as now. **No `corner_false`**: under TorInjA,
`κ′ ≤ d₁′`, and the (NR) failure `κ′ ≥ d₁′ + 2d₂′ − 1` is impossible when `d₂′ ≥ 1` (REVIEW_TORINJ §3d). Simplicity
of `A` (`AbBlock.simple`) is the only CM input. [Proof sketch; the pivot lemma itself may come from β's subgroup layer,
to be checked before writing it.]

## 3. Work breakdown

| step | file(s) (new; `LSG/W88/AbVar*.lean` or `LSG/AuxFunA/`) | content | [Est] |
|---|---|---|---|
| A5.1 | `W88/AbVarPer.lean` | D5: finite-index lemma, `span_ℚ`/`rk`/`IsRatSub`/`htil` transfers; `kerE ≤ ℚ·latt` | 0.3k |
| A5.2 | `AuxFunA/Package.lean` | `AbBlockAn`, consequences (multiplier, growth of monomials) | 0.3k |
| A5.3 | `AuxFunA/MonoIndep.lean` | D4 nonvanishing (generic over `AbBlock`) | 0.3–0.4k |
| A5.4 | `AuxFunA/PropG.lean` | Prop 2.1 caller on `V` via `prop21Lin` + TorInjA ⇒ ℂ-independence | 0.5–0.7k |
| A5.5 | `AuxFunA/LemmaU*.lean` | D2: Lemma U (reuse `Sz`, `LemmaUArith`, `small_of_bounds`, Liouville) | 1.2–1.8k |
| A5.6 | `W88/AbVarProp61.lean` | `prop61_b` analogue (copy of the parameter chase) | 0.4–0.6k |
| A5.7 | `W88/AbVarSec7*.lean` | `MultEstB` application, `exists_inequiv_grid` with `htil`, `core_ineq`, rational part; `SubgroupDataA` | 1.0–1.5k |
| A5.8 | `W88/AbVarInst.lean` | A-block package from `ThetaData` (after γ's `aBlock`); T1 | 0.2–0.4k |
| A5.9 | `W88/AbVar5d*.lean` | D6: Lemmas 5.1/5.2 (reuse the generic K5d arithmetic), pivot transport, Roy; T2 | 1.5–2.5k |
| | | **total** | **≈ 5.7–8.5k** |

Order: A5.1 → A5.2/A5.3 → A5.4 → A5.5 → A5.6 → A5.7 → A5.8 (needs γ) → A5.9. A5.1–A5.7 need nothing from γ, α, β
beyond the frozen `Stmt.lean`.

## 4. How `MultEstB` is consumed (also recorded in STAGE_A4 §7.3)

* Instance: `d₀, d₁` as in the statement, `m = r`, `B = fun _ => aBlock` (γ). Nothing else from the core.
* `P = Σ_l p_l M_l · Π_k (stuff)`: block-homogeneous of degree `D₂` by construction (`IsHomB`), `P ∈ FLE (DfunB D₀ D₁ D₂)`
  by the degree bookkeeping of Prop 6.1, `P ∉ IGsem` from `notMem_IGsem_of_eval_ne` + D4.
* `OrdGtB W P (n T) σ` at `σ ∈ sigB S n` from `VanishAlong` of `Ψ = fun u => eval (liftB u) P` at the lift
  `u = Σ h_j y_j` (definitional, as STAGE_A4 §6.3 promises).
* Output used: `O.Proper`, the count inequality, `O.grp_eq`/`O.grp_sub`/`O.htil` (grid counting), `O.lie` and
  `O.t_rat` (→ `SubgroupDataA` via D5). Not used: `O.grp_closed`.

## 5. Status

* 2026-10-31: plan written (this file); consumer note in STAGE_A4 §7.3.
* **A5.1 done [Proved]**: `LSG/W88/AbVarPer.lean` (268 lines).
  - Generic: `IsNsmulIn L P`, `span_rat_eq_of_nsmul`, `rk_inf_eq_of_nsmul`, `isRatSub_iff_of_nsmul`,
    `IsNsmulIn.sup_nsmul`, `exists_nsmul_mem_zspan` / `isNsmulIn_closure_basis` (discrete group ⊇ ℤ-span of an
    ℝ-basis ⇒ ⊆ its ℚ-span).
  - MEB: `PerL d₀ d₁ B Λ`, `perL_le`, `isNsmulIn_perL`, `perAbL`, `isRatSub_perAb_iff`, `ObstrDataB.htil_perL`,
    `span_perL`, `rk_inf_perL`, `AbBlock.isNsmulIn_of_basis` (declared in namespace `LSG.MEB`, file is mine).
  - A: `discreteTopology_kerE`, `latt_eq_closure_basis`, **`isNsmulIn_latt_kerE : IsNsmulIn latt (kerE G)`**.
* **A5.3 done [Proved]**: `LSG/AuxFunA/Mono.lean` (295 lines), generic over `B : Fin m → AbBlock`.
  - `fidx`, `ratioMap`, `exists_ratio_ball` (inverse function theorem from `coords_locInv` + `θ_analytic`).
  - `MonoA`, `MonoA.eval/poly`, `PpolyA`, `PsiA`, `eval_PpolyA`, `isHomB_PpolyA`, `PpolyA_mem_FLE`.
  - **`exists_PsiA_ne_zero`**: injective `rexp` and `p ≠ 0` ⇒ `∃ u, PsiA μs p u ≠ 0`.
* **A5.2 done [Proved]**: `LSG/AuxFunA/Package.lean` (214). `structure AbBlockAn b`: `lat ≤ per`, `IsNsmulIn lat per`,
  growth `‖θ z‖ ≤ exp (c_W (1+‖z‖)²)`, quasi-periodicity `θ(z+ω) = (κ e^{L z}) • θ z` with `‖κ‖^{±1} ≤ exp (c_Q‖ω‖²)`,
  `‖L z‖ ≤ c_Q ‖ω‖ ‖z‖`. Consequences: `MonoA.differentiable_eval`, `exists_qp_monoA` (common multiplier,
  `‖mu‖ ≤ exp (m D c_Q (‖u‖+‖ω‖)²)` for `ω ∈ PerL`), `sum_norm_eval_le` (growth in W83 form).
* **A5.4 done [Proved]**: `LSG/AuxFunA/PropG.lean` (230).
  - `TorInjB V` (MEB form of `TorInjA`, relative to `span_ℚ Per`), **`linIndep_of_torInj`**: ℤ-independent periods in a
    toric-injective `V` are ℂ-independent.
  - **`prop21A`**, **`prop21A_deg`**: W83 Prop. 2.1 for the monomials on `V`, ℂ-independent `ω_i ∈ V ∩ PerL`, via
    `LSG.Aux.prop21Lin`; statement identical in shape to `LSG.Aux.prop21_G(_deg)`.
* **A5.5 done [Proved]**: Lemma U.
  - `LemmaUFac.lean` (179): `structure AbBlockTay b ι` (Taylor package: `KS ι A (c_B H_c) E (d_c δ)` for the ratios along
    algebraic directions; A-instance = `ks_chart4F` at `z₀ = 0`), `gA`, `FA`, `uA`, **`PsiA_line_eq`**
    (`Ψ(t + s v) = u(s) F(s)` at lattice points), **`ks_FA`** (via `KS.poly`).
  - `LemmaUBud.lean` (292): `budU` (the elliptic budget), `le_bud_A`, `le_bud_e`, `le_bud_unit`, `le_bud_cauchy`,
    `small_of_bud`.
  - `LemmaULine.lean` (345): **`lemmaU_line`** (Cauchy + Liouville + Leibniz on one line; constant `kLU`).
  - `LemmaUMain.lean` (222): `LUDataA`, `exists_theta_lower`, `contDiff_PsiA`, **`lemmaU_A`**: the exact analogue of
    `lemmaU_core` (same budget `c₀ (B + log(L+1) + (A₀+1) log(S+1) + (A₁+1) S + (D+1) S² + (T+1) log(T+2)) ≤ U`).
* **A5.6 done [Proved]**: `LSG/W88/AbVarProp61.lean` (360). `monoFamA` (block parts `θ_{i₀}^{D−Σa} Π θ_{is j}^{a_j}`,
  `a_j ≤ D'`, `D = (G+1) D'`, `G = Σ g_k`), `monoFamA_rexp_injective`, **`prop61A`**: `prop61_b` verbatim in shape
  with `m ↦ G` in `e = d₁ + 2G − κ`, `q = d₀ + d₁ + G − n`; inputs `Dt : LUDataA` (with `span Dt.w = W`) and
  ℂ-independent `ω_i ∈ V ∩ PerL`. Siegel count via `siegel61` with `x₂ = (G+1)(D'+1)` and `c₂' = c₂ (G+1)^G`.
* **CR1 (α, `Stmt.lean`)**: `MultEstB` now uses `n = d₀ + d₁ + Σ g_k` in `sigB` and in the order. Prop 6.1 is
  unaffected (it gives vanishing at all `Σ h_j y_j`, `h_j ≤ S`, to order `Δ/log S`); A5.7 takes the grid
  `M = ⌊S/n⌋` and `T′ = ⌊Δ/(2 n log S)⌋` with this `n`, exactly as `Sec7` does with its `nn`.
* **A5.7 done [Proved]** (A5′ agent, 2026-10-31): `theorem41B_of (hME : MEB.MultEstB) An (Tay : TayAll B) :
  Theorem41B An`, generic over block families; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
  - `W88/AbVarSec7Defs.lean` (106): `LamB d₀ d₁ An`, `AlgTanB`, `RationalOverQbarB`, `SubgroupDataB d₀ d₁ B` (fields
    `h0 U t h0_rat t_rat`, **`t_rat : IsRatSub (perAb B) t`** — full periods, so `ObstrDataB.t_rat` and `pivot` apply
    directly; `isRatSub_perAb_iff` converts to `perAbL`), `tan δ0 δ1 δ2 δ Proper`, **`Theorem41B An`** (counts with
    `PerL d₀ d₁ B (latF An)`, premise `TorInjB V`), `TayAll B`.
  - `W88/AbVarSec7Data.lean` (110): **`exists_LUDataA`**.
  - `W88/AbVarSec7Rat.lean` (235): `ratDataB`, `inf_tanPer_eqB`, **`exists_subgroupDataB`** (any period group `Pe` with
    zero `G_a`-parts), `finrank_{h0,U,t}_leB`, `finrank_blocks`, **`obstr_delta_posB`**, `gridPtsB`/`mem_gridPtsB`/
    `sig_gridPtsB`, `monoW` (= `Π_k X_{k,i₀}`), **`PW μs p = PpolyA μs p * monoW.poly`** with `isHomB_PW` (degree
    `D + 1`), `PW_mem_FLE`, `PW_notMem_IGsem` (via α's `IGsem_isPrime`), `ordGtB_PW` (Leibniz,
    `iteratedDeriv_mul_eq_zeroB`).
  - `W88/AbVarSec7.lean` (297): **`theorem41B_of`** (copy of `theorem41Abelian_of`, `m ↦ G`, `nn = d₀ + d₁ + G`).
* **A5.9, first half done [Proved]** (A5′, 2026-10-31): the generic §5d engine, with Theorem 4.1 for subgroups and the
  rationality of `W ∩ T_H` as explicit hypotheses (no axioms; `#print axioms hyperplaneKappaB_of`: standard three).
  - `W88/AbVar5dRank.lean` (371): `exists_span_rat_of_discrete` (discrete + `ℝ`-spanning in `ℂ^g` ⇒ in the `ℚ`-span
    of `2g` vectors), **`finrank_span_perAb_le`**, **`finrank_span_Per_le`** (`rk Ω ≤ d₁ + 2G`, plus the
    `FiniteDimensional` instance), `inTB`, `inAb`, `latTB`, `two_mul_le_finrank_latTB`, **`finrank_Per_inf_tan_ge`**
    (`rk(Ω ∩ T_H) ≥ d₁′ + 2d₂′`), `exists_toric_rat`, **`kappa_le_of_torInj`** (`TorInjB V`, `S ⊆ V ∩ Ω`, toric parts in
    `torusLie U` ⇒ `dim_ℚ S ≤ dim torusLie U`), `finrank_tanOf`, `finrank_tanB`, `isRatSub_top`,
    `rationalOverQbar_top`, `topSubB`, `topSubB_tan`.
  - `W88/AbVar5dCore.lean` (352): `OmB = span_ℚ MEB.Per`, `nPB`, **`Trans41B An H′`** (the conclusion of the elliptic
    `trans41`, for `V ⊂ T_{H′}` a toric-injective hyperplane, under `(NR) ∨ t′ = ⊥`), `arith_finalB`,
    `finrank_TanB`, `torInjB_mono`, **`coreB`** (`K5d.core` with `W ⊓ T_H` for `Wr` and the corner replaced by
    `kappa_le_of_torInj`), **`gmB d₀ d₁ An`** (`GroupModel`: `d₂ = G`, `alg = AlgTanB`, `lam = LamB`,
    `per = span_ℚ PerL`, `sub = SubgroupDataB.tan`), **`hyperplaneKappaB_of An (htr : ∀ H′, Trans41B An H′) (hrat :
    ∀ W H, RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan)) : HyperplaneKappaOn (gmB d₀ d₁ An) TorInjB`**.
* **A5.9 transport, stages 1 and 2a done [Proved]** (A5′, 2026-10-31; standard axioms):
  - `W88/AbVar5dTrans.lean` (≈ 390): `tanBB`, `SubgroupDataB.δBt`, **`Thm41SubAtB An k₀ k₁ t`** (statement as in §6.6
    (a)1, with premise `TorInjB V` and `(NR) ∨ t = ⊥`), `inAb_mem_OmB`, `mem_OmB`, `iotaB`, `piB`,
    `iotaB_inT_add_inAb`, **`trans41B An H′ (h41 : Thm41SubAtB An (dim h₀′) (dim annQ U′) H′.t) : Trans41B An H′`**.
  - `W88/AbVar5dRoy.lean` (≈ 480): `epsB`, `range_epsB`, `isRatSub_botB`, `span_lam_propB`, `span_per_propB`,
    `comap_span_perB`, `sub41ConclB_bot`, **`thm41SubAtB_bot An k₀ k₁ : Thm41SubAtB An k₀ k₁ ⊥`** (Roy, no (NR)).
  - Left: stage 2b (`Thm41SubAtB An k₀ k₁ t` for `t ≠ ⊥` from `Theorem41B` of the pivot subfamily) and (b) `hrat`.
* **A5.9 complete modulo one rationality hypothesis [Proved]** (A5′, 2026-10-31; standard axioms throughout):
  - `W88/AbVar5dPivot.lean` (337): **`thm41SubAtB_of An h41 k₀ k₁ t ht : Thm41SubAtB An k₀ k₁ t`** (Roy for `t = ⊥`,
    pivot transport otherwise; finite index `hfin` of `π_J(t ∩ perAb)` in `perAb (B ∘ e)` via
    `isNsmulIn_closure_basis` + `discreteTopology_perAb`), **`hyperplaneKappaB_of_41`**, **`hyperplaneKappaB_of_ME
    (hME) An (Tay : TayAll B) hrat : HyperplaneKappaOn (gmB d₀ d₁ An) TorInjB`**.
  - `W88/AbVar5dA.lean` (64): **`hyperplaneKappaAbVar_of_rat (hratA) : HyperplaneKappaAbVar`**, instantiating
    `multEstB_holds`, `aBlockAnF`, `tayAll_aBlockW` (types agree by `rfl`: `aBlock.g = 2`, `MEB.Tan … = TanA …`).
    Composed with `thm11KappaA5_of` (`AbVarMStar.lean`) this gives `Thm11KappaA 5 …` from `hratA` alone.
  - **The only open input is `hratA`** (§6.6 (b)): for `W ⊂ TanA` `ℚ̄`-rational and `H : SubgroupDataB` (so `H.t` is
    `IsRatSub (perAb)`), `W ⊓ H.tan` is `ℚ̄`-rational.
* Next: A5.7 (§7 against `MultEstB`: `LUDataA` from algebraic data, periods from `Y ∩ PerL` + `linIndep_of_torInj`,
  grid count with `htil_perL`, `core_ineq`, `ObstrDataB → SubgroupDataA`), A5.9 (§5d).

## 6. Continuation plan (written 2026-10-31 at checkpoint 3, context limit): A5.7 generic, then A5.9

Everything below is generic over `B : Fin m → AbBlock` with `An : ∀ k, AbBlockAn (B k)`; write `G = Σ_k (B k).g`,
`Λ = latF An`, `nG = d₀ + d₁ + G` (CR1). Namespace `LSG.W88` (qualify `MEB.Tan`, `MEB.Per`: `Tan`/`Per` alone are the
elliptic ones there). Files: `LSG/W88/AbVarSec7Defs.lean`, `AbVarSec7Data.lean`, `AbVarSec7Rat.lean`,
`AbVarSec7.lean` (each ≲ 500 lines).

### 6.1 Statement file `AbVarSec7Defs.lean` (≈ 150)
* `LamB An : AddSubgroup (MEB.Tan d₀ d₁ B)`: `AlgVec p.1`, `∀ i, IsAlgebraic ℚ (exp (p.2.1 i))`, `∀ k, p.2.2 k ∈ (An k).lat`
  (copy of `LamA`'s proof).
* `AlgTanB p`: `AlgVec p.1 ∧ AlgVec p.2.1 ∧ ∀ k j, IsAlgebraic ℚ (p.2.2 k j)`; `RationalOverQbarB W` as `RationalOverQbarA`.
* `structure SubgroupDataB An`: `h0` (`RationalOverQbar`), `U : Submodule ℚ (Fin d₁ → ℚ)`,
  `t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)` with `IsRatSub (perAbL Λ) t`; `tan := h0.prod ((torusLie U).prod t)`,
  `δ0 = d₀ − dim h0`, `δ1 = dim U`, `δ2 = G − dim t`, `δ`, `Proper`.
* `Theorem41B An : Prop` = `Theorem41AbVarPer` with `TanA → MEB.Tan d₀ d₁ B`, `2r → G`, `LamA → LamB An`,
  `PerA → PerL d₀ d₁ B Λ`, `TorInjA → TorInjB` (note `TorInjB` uses `span_ℚ Per`; equal to `span_ℚ PerL` by `span_perL`),
  `SubgroupDataA → SubgroupDataB An`. Target: **`theorem41B_of (hME : MultEstB) (An) (Tay : TayAll B) : Theorem41B An`**
  where `TayAll B := ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) k, AbBlockTay (B k) ι` (for the A-block the
  Taylor data are rational, so `TayAll` holds; that is A5.8's job).

### 6.2 `AbVarSec7Data.lean`: the Lemma U data (≈ 250)
`exists_LUDataA (An) (W) (hW : RationalOverQbarB W) (y) (hyL : ∀ j, y j ∈ LamB An) :
 ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ι) (τ) (Dt : LUDataA ι An μ τ), Dt.y = y ∧ span (range Dt.w) = W`.
Copy `LSG.W88.exists_LUData` (`Prop61Data.lean` l. 56ff.): basis of `W` from `St = {w ∈ W, AlgTanB w}`
(`exists_linearIndependent`), all coordinates (`(y j).1 i`, `exp (y j).2.1 i`, `(w r).1 i`, `(w r).2.1 i`,
`(w r).2.2 k i`) are algebraic, so they lie in one number field (the elliptic proof's `IntermediateField.adjoin`
step); `H`, `d` from `exists_den`/house bounds as there. Drop all `℘`/`X₀`/`γ₂`/`γ₃` parts. `hlat` is `(hyL j).2.2 k`.

### 6.3 `AbVarSec7Rat.lean`: from `ObstrDataB` to `SubgroupDataB` (≈ 250)
`exists_subgroupDataB (O : ObstrDataB d₀ d₁ B) (W) (Y) (hY : ∀ y ∈ Y, y ∈ LamB An)`: the conclusion of
`exists_subgroupData_rat` (`Sec7Rat.lean` l. 111) with `tanPer O := O.tan.toAddSubgroup ⊔ PerL`. Proof as there:
`h0 ↦ ratPart O.h0` (`Sec7Rat.ratPart`, `rationalOverQbar_ratPart`, `mem_ratPart`), `U`, `t` unchanged;
`t_rat` from `(isRatSub_perAb_iff hΛle hΛ O.t).mpr O.t_rat`; the rank equality uses that `Y`'s `G_a`-parts are
algebraic (`mem_ratPart`), exactly as in the elliptic proof; `finrank_tan_add`, `finrank_inf_add_le` reused.

### 6.4 `AbVarSec7.lean`: the assembly (≈ 400; copy `theorem41Abelian_of`, `Sec7.lean` l. 70–325)
1. `exists_gens Y`, `exists_periods (Y ⊓ PerL)` (generic, `Sec7Aux`), `ω` ℂ-independent by
   `linIndep_of_torInj hTor ω hωV (fun i => perL_le hΛle (hωZ i).2) hω`.
2. `exists_LUDataA` (6.2) with the `TayAll` instance at that `ι`; `prop61A 2 (by norm_num) An (Tay K ι) V W …`.
3. `hME d₀ d₁ m B` gives `C'`. Points `S′ = gridPtsB y M := univ.image (h ↦ expG (Σ h_j • y j))`, `M = ⌊S/nG⌋`,
   `T′ = ⌊Δ/(2 nG log S)⌋`, `D₀ = ⌊Δ/log²S⌋+1`, `D₁ = ⌊Δ/S⌋+1`, `D₂ = D` (`prop61A`'s `D ≥ 1`? if `D = 0`, use
   `D₂ = D + 1` and multiply by `Π_k X_{e k i₀}`: `IsHomB`/`FLE` for `PpolyA * Π_k X(e k i₀)` and
   `eval (liftB u) (Π_k X(e k i₀)) = Π θ_{k,i₀}(u_k)`, which is nonzero near `0`; this mirrors `Wprod` of
   `Sec7Bridge.lean`). Hypotheses: `IsHomB` (`isHomB_PpolyA`), `FLE` (`PpolyA_mem_FLE` + `FLE_mono`),
   `P ∉ IGsem` (`notMem_IGsem_of_eval_ne` + `eval_PpolyA` + `prop61A`'s `∃ x, PsiA ≠ 0`), and
   `OrdGtB W P (nG T′) σ` for `σ ∈ sigB S′ nG`: `σ = expG (Σ h_j y_j)` with `h_j ≤ nG M ≤ S` (copy `sig_gridPts`),
   lift `u = Σ h_j y_j`, and `OrdGtB` is definitionally `VanishAlong` of `u ↦ eval (liftB u) P` for `k ≤ nG T′`
   (`nG T′ < Δ/log S`); rewrite with `eval_PpolyA`.
4. Count: `exists_inequiv_grid_gen expG O.grp (zero) (O.tan.toAddSubgroup ⊔ PerL) hZ y M`, with
   `hZ u hu := mem_span_rat_of_nsmul hN (subset_span hNu)` from `O.htil_perL hΛ hu`. `rk` of the closure of `y` is
   `rk Y` (`span_closure_range`), and `rk (closure y ⊓ Z)` vs `rk (Y ⊓ Z)` as in `Sec7.lean`.
5. `log_count` (`Sec7Aux` l. 82, with its `m := G`, `t2 := finrank O.t`, `t0 := finrank O.h0`, `u := finrank O.U`) and
   `core_ineq` (`Sec7Arith` l. 59) with `nn := nG`; then 6.3. The constants `K0b`, `Kb`, `Bb`, `eventually_log_big`
   are copied verbatim with `m ↦ G`, `nn ↦ nG`.

### 6.5 A5.9 (§5d engine, ≈ 1.5–2.5k), after 6.1–6.4
* Target: `hyperplaneKappaB_of (h41 : ∀ B′ An′ (sub-families), Theorem41B An′) : HyperplaneKappaOn (gmB An) TorInjB`
  with `gmB An` the `GroupModel` of 6.1 (`lam = LamB`, `per = span_ℚ PerL`, `sub = SubgroupDataB.tan`).
* Copy `K5dMain.core` (l. 118–330): Lemma 5.1 (maximise `a/e`), Lemma 5.2, `arith_final'`, `Wr` (`ratT_inf_tan`
  analogue). Replace `trans41` (CM transport) by the **pivot transport**: for `H′ = H₀ × T_U × B′`, `t_{B′}` is
  `IsRatSub` and `simple` blocks give `J ⊆ Fin m` with `t → ⊕_{k∈J} ℂ^{g_k}` an isomorphism (ask β whether the pivot
  lemma exists in `LSG/MEB/Subgroup*`; otherwise prove it: induction on `m`, `p_m(t)` rational ⇒ `0` or `⊤` by
  `simple`, intersection of rational subspaces is rational). Pull `Theorem41B` back from the subfamily `B ∘ J`
  (points `π_J (LamB) ⊆ LamB`, periods `π_J(PerL ∩ T_{H′})` of finite index in `PerL(B∘J)` — `IsNsmulIn` again,
  subgroups by preimage). The toric part `T_U ≅ G_m^{d₁′}` via `K5dTrans`'s torus change of coordinates
  (`LSG.Subgroups.Torus`), the `G_a` part via `exists_algFrame` (`K5dAlg`).
* `B′ = 0`: Roy's Theorem 1 (`sub41Concl_bot`, `K5dRoy`), unchanged. **No `corner_false`**: under `TorInjB`,
  `κ′ ≤ d₁′` (toric parts of `ℤ`-independent periods are ℚ-independent: the argument of `linIndep_of_torInj`), so the
  (NR) failure `κ′ ≥ d₁′ + 2d₂′ − 1` with `d₂′ ≥ 1` is impossible; record this as a lemma `kappa_le_of_torInj`.

### 6.6 Continuation plan after A5′ (written 2026-10-31): what is left of A5.9

A5.7 and the engine are done (§5). Two hypotheses of `hyperplaneKappaB_of` remain to be discharged generically.

**(a) `htr : ∀ H′, Trans41B An H′`** (≈ 0.9–1.2k, three files `AbVar5dTrans*.lean`). Two stages, as in the elliptic
case (`K5d.trans41` + `CM.thm41SubAt_of`):
1. *Stage 1, `trans41B`* (copy `K5dTrans.trans41`, ≈ 300): `Trans41B An H′` from `Thm41SubAtB An k₀ k₁ H′.t`,
   `k₀ = dim h₀′`, `k₁ = dim annQ U′`, where (block part kept, as the elliptic `Thm41SubAt` keeps `E^m`)
   ```
   tanBB k₀ k₁ t := ⊤.prod (⊤.prod t) : Submodule ℂ (MEB.Tan k₀ k₁ B)
   SubgroupDataB.δBt H t := H.δ0 + H.δ1 + (finrank t − finrank H.t)
   Thm41SubAtB An k₀ k₁ t : Prop := ∀ V W Y, V ≤ tanBB k₀ k₁ t → finrank V < k₀ + k₁ + finrank t → W ≤ V →
     RationalOverQbarB W → Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamB k₀ k₁ An) → TorInjB V →
     (k₁ + 2k₀ + rk (Y ⊓ MEB.Per k₀ k₁ B) ≤ 2 finrank V ∨ t = ⊥) →
     ∃ H : SubgroupDataB k₀ k₁ B, H.t ≤ t ∧ H.δBt t ≠ 0 ∧ τ_H < H.δBt t ∧ (Thm41SubAt's inequality, `Per Ls ↦ MEB.Per`)
   ```
   `ι = iotaG`-analogue `(a, c, z) ↦ (A a, C c, z)` (`exists_algFrame`, `K11.exists_frame (annQ U′)`), block part the
   identity; `ι` preserves `LamB` (`algVec_cmK_mulVec`, `exp_cm_mulVec`), `MEB.Per` and toric injectivity (integral
   `C` with left inverse `D`). Use `rk` with `MEB.Per` (convert from `PerL` by `rk_inf_perL`/`span_perL`).
2. *Stage 2a, `t = ⊥`* (≈ 300): copy `K5dRoy.sub41Concl_bot` with `epsL : Roy.E k₀ k₁ → MEB.Tan k₀ k₁ B`,
   `x ↦ (x.1, x.2, 0)`; it uses only the `G_a`/`G_m` parts (`span_lam_prop`, `mem_omega_iff`, `comap_span_per`
   transfer verbatim; block parts are `0`).
3. *Stage 2b, `t ≠ ⊥`* (≈ 450): `Thm41SubAtB An k₀ k₁ t` from `Theorem41B (fun i => An (e i))` for the subfamily
   `B ∘ e`, `e = J.orderEmbOfFin rfl`, `J` from **`LSG.MEB.pivot t.t_rat`** (`π_J|_t` injective and onto). Map
   `π : (x, y, z) ↦ (x, y, (z (e i))_i)`, inverse on `tanBB t` by the pivot section. Facts needed:
   - `π(LamB) ⊆ LamB` (projection of `lat`), `π` injective on `tanBB t`, dims;
   - periods: `π(MEB.Per ∩ tanBB t) ⊆ MEB.Per(B∘e)` and **`IsNsmulIn (π(Per ∩ tanBB t)) (Per(B∘e))`**: `π(t ∩ perAb)`
     spans `∏_J ℂ^{g}` over `ℝ` (from `IsRatSub`), so contains an `ℝ`-basis, and `isNsmulIn_closure_basis` (A5.1) gives
     finite index; hence `rk` equalities and `TorInjB (π V)` from `TorInjB V`;
   - subgroups: `H_J ↦ H` with `H.t := t ⊓ π_J⁻¹(H_J.t)`; `IsRatSub (perAb B)` of it from the finite index again;
     `δ`, `τ`, `λ` transfer as in `trans41`.
   (NR) for `B ∘ e` is the hypothesis; `t ≠ ⊥` makes `J ≠ ∅` irrelevant (the empty family is allowed).

**(b) `hrat`** (≈ 0.2k): copy `K5dRat` (`ratT_inf_ker`, `ratT_inf_finsetInf`, `ratT_inf_comap`, `rational_torusLie`,
`ratT_inf_tan`) to `MEB.Tan`, with the block-family hypothesis
`RatTangents B := ∀ t, IsRatSub (perAb B) t → t = span ℂ {z | z ∈ t ∧ ∀ k j, IsAlgebraic ℚ (z k j)}`. For the
`A`-block `RatTangents` is the CM rationality (ask γ; A4 §2.1 `simple` uses the CM argument).

**(c) A5.8 then assembles** `HyperplaneKappaAbVar` from `hyperplaneKappaB_of` for `B = fun _ : Fin r => aBlock`:
`theorem41B_of hME An Tay` (for every subfamily, via (a)), the type translation `TanA d₀ d₁ r ≃ MEB.Tan d₀ d₁ B`
(`aBlock.g = 2` by `rfl`), `LamA ↔ LamB` (`lat = latt`), `PerA ↔ PerL`, `TorInjA ↔ TorInjB` (`span_perL`),
`SubgroupDataA ↔ SubgroupDataB` (`isRatSub_perAb_iff`), `gmLsgA ↔ gmB`.

### 6.7 `hratA` (the last input; written by A5′, 2026-10-31)

Split as (i) linear algebra and (ii) CM:
* (i) [≈ 0.15k, copy `K5dRat`] intersections of `ℚ̄`-rational subspaces of `MEB.Tan` are `ℚ̄`-rational
  (`ratT_inf_ker`, `ratT_inf_finsetInf`, `ratT_inf_comap` with `algT ↦ AlgTanB`); `tanOf h₀ U t` is rational when
  `h₀`, `torusLie U` (`K5d.rational_torusLie`) and `t` are. So `hratA` reduces to **`RatTangentsA`**: every
  `t ⊂ (ℂ²)^r` with `IsRatSub (perAb)` (equivalently `IsAbelianTangentA`, lattice `latt`) is spanned by vectors with
  algebraic coordinates.
* (ii) [Proof; ≈ 0.4–0.6k] `RatTangentsA`. Lattice points are `v_k = Σ_e n_{k,e} perVec e`, coordinates
  `v_{k,j} = c_j α_k(ζ^{j+1})` (`latt_repr`, `latt_coord`, `Simple.lean`), `α_k ∈ ℤ[X]`, `deg < 4`. Let
  `V_ℚ = span_ℚ(t ∩ latt^r) ⊂ ℚ(ζ)^r` (via `α`). `t` complex ⇒ `V_ℝ` is stable under `J = (i, i) ∈ ℚ(ζ) ⊗ ℝ ≅ ℂ × ℂ`
  (the two coordinates `j = 0, 1` are the CM embeddings `ζ ↦ ζ, ζ²`). The stabiliser of `V_ℝ` in `ℚ(ζ) ⊗ ℝ` is
  `F ⊗ ℝ` for the ℚ-algebra `F = Stab(V_ℚ) ∩ ℚ(ζ)`; `J ∉ ℚ(√5) ⊗ ℝ`, so `F = ℚ(ζ)` and `V_ℚ` is a `ℚ(ζ)`-subspace.
  Hence `t = t₀ ⊕ t₁` with `t_j = {z : (z_{k,j})_k ∈ c_j · σ_j(V_ℚ) ⊗ ℂ} = σ_j(V_ℚ) ⊗ ℂ` (scaling by the scalar `c_j`
  does not change a subspace), spanned by vectors with coordinates in `ℚ(ζ)`. An elementary route avoiding the
  stabiliser: `t` is spanned by lattice points `v`; `I·v ∈ t` is an `ℝ`-combination of lattice points; compare the
  two coordinate blocks as in `real_of_latt` to show `[ζ]v ∈ t` (`[ζ]` multiplies block `j` by `ζ^{j+1}`), then
  `t_j := pr_j(t) ⊆ t` and `t_j` is spanned by the `pr_j v`, whose coordinates are `c_j ×` algebraic, i.e.
  `t_j = span(pr_j v / c_j)`.
* **(ii) delivered by γ (2026-10-31) [Proved, standard axioms]** (`LSG/W88/AbVarQbar.lean`, `AbVarQbarB.lean`):
  - `def RatTangentsA : Prop := ∀ (r : ℕ) (t : Submodule ℂ (Fin r → Fin 2 → ℂ)), IsAbelianTangentA t →
    t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z}`, **`ratTangentsA : RatTangentsA`**;
  - `ratTangentsA_isRatSub (ht : IsRatSub (AddSubgroup.pi univ fun _ => latt) t) : t = span ℂ {z ∈ t | AlgVecA z}`;
  - **`ratTangents_aBlock (ht : IsRatSub (perAb (fun _ : Fin r => aBlock)) t) :
    t = span ℂ {z | z ∈ t ∧ ∀ k j, IsAlgebraic ℚ (z k j)}`**: exactly the `t_rat` field of `SubgroupDataB` (lattice
    `kerE`), via `isRatSub_perAb_iff`;
  - also `exists_alg_lam_ne` (an algebraic `z ∈ t` with `Σ b_j z_j(0) ≠ 0`, used by `thm11KappaAK5_of`).
  Proof: the elementary route above (`D₁ = diag(ζ − ζ⁴, ζ² − ζ³)`, `D₂ = diag(ζ² − ζ³, ζ⁴ − ζ)`, `I = c D₁ + d D₂` with
  `ℚ`-independent real `c, d`; a `ℚ`-functional `ℝ → ℚ` on period coordinates gives `D₁t, D₂t ⊆ t`, hence `pr₀ t ⊆ t`).


**Status of §6.7 (A5′, 2026-10-31): done; `HyperplaneKappaAbVar` is unconditional [Proved, standard axioms].**
* The statement agreed with γ (defined once, in γ's `LSG/W88/AbVarQbar.lean`):
  ```lean
  def RatTangentsA : Prop :=
    ∀ (r : ℕ) (t : Submodule ℂ (Fin r → Fin 2 → ℂ)), IsAbelianTangentA t →
      t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z}
  theorem ratTangentsA : RatTangentsA := fun _ _ ht => abTan_qbar ht   -- γ
  ```
* (i) `W88/AbVar5dRat.lean` (206), a copy of `K5dRat` in `TanA` coordinates: `RatA`, `ratA_iff`, `AlgFormA`,
  `algTanA_sub_smul`, `ratA_inf_ker`, `ratA_inf_finsetInf`, `ratA_inf_comap`, `flatA` (`(ℂ²)^r ≃ ℂ^{2r}`),
  `rational_flatA`, **`ratA_inf_tan (hRT : RatTangentsA) : RationalOverQbarA W → RationalOverQbarA (W ⊓ H.tan)`**,
  **`hratA_of`**, **`hyperplaneKappaAbVar_of_ratTangents (hRT : RatTangentsA) : HyperplaneKappaAbVar`**.
* `W88/AbVar5dFinal.lean` (26): **`hyperplaneKappaAbVar : HyperplaneKappaAbVar`** and
  **`thm11KappaA5 : MStarCopy.Thm11KappaA 5 2 (fun s => s + 1) MStarCopy.perA5 0`** (via `thm11KappaA5_of`).
  `#print axioms`: `[propext, Classical.choice, Quot.sound]` for both.
