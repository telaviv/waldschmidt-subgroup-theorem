# Stage 5: the analytic side for vector extensions (`LSG/AuxFunV/`, namespace `LSG.AuxV`)

Started 2026-10-31. Labels as in PLAN.md ([Lean] proved, standard axioms; [Design]; [Est] line estimate).
Inputs: `VECEXT.md` §3.3 (Prop 2.1/6.1 for the class `𝒞`), `VECEXT_SPIKE.md` (the model `X ⊂ ℙ⁴` of `E^♮`,
`expN`, `NLaw_expN_all`), `STAGE3_D2.md` / `STAGE3_D3.md` / `STAGE3_S7.md` (abelian analytic layer),
`LSG/W88/StatementVec.lean` (`TanV`, `LamV`, `PerV`, `fibreV`).

---------------------------------------------------------------------------------------------------------------------

## 1. Status: phase 1 DONE [Lean]

Seven files, 1851 lines. No `sorry`/`axiom`/`native_decide`. `#print axioms` of every main result:
`[propext, Classical.choice, Quot.sound]`. They compile without warnings. They are not imported by `LSG.lean`;
build with `lake build LSG.AuxFunV.PropGV LSG.AuxFunV.ChartN LSG.AuxFunV.DefectSizeMain`, which takes about
2 min on top of the existing oleans.

| file | lines | content |
|---|---|---|
| `AuxFunV/ExpCoordsN.lean` | 287 | `zetaS = σ²σ'`, `kapS`, **`ellN`** (the five entire coordinates of `exp_{E^♮}`), `ellN_eq_off`, **`ellN_add`**, `zetaS_add`, **`ellN_eq_smul_expN`**, `ellN_add_fib`, **`exists_ellN_growth`** |
| `AuxFunV/MonoV.lean` | 462 | `piT` (forget `s`), `piT_injOn`, **`fibF`** (fibre forms), `fibF_eq_off`, **`fibF_add_per`**, `MonoV`, **`MonoV.eval_add_per`**, **`exists_qp_monoV`**, `exists_fibF_growth`, **`exists_monoV_growth`**, **`exists_sum_monoV_le_exp`** |
| `AuxFunV/PropGV.lean` | 220 | **`exists_coordsVV`** (the risk-3 workaround), **`prop21_GV`**, **`prop21_GV_deg`** |
| `AuxFunV/AlgV.lean` | 304 | `NLaw_map`, `AlgPtN`, **`algPtN_add`**, **`isAlgebraic_zeta_defect`**, **`lamVSub`** (`Λ(G)` is an `AddSubgroup`) |
| `AuxFunV/ChartN.lean` | 86 | **`exists_chartN`** (the analogue of `Chart.lean`) |
| `AuxFunV/DefectSize.lean` | 200 | `zdef`, **`zeta_two_mul`** (ζ doubling formula), `zdef_eq_zero/_generic/_dbl`, `isRep_eq_of_notMem`, **`exists_defect_frac`** |
| `AuxFunV/DefectSizeMain.lean` | 292 | `Dsum`, `exists_defect_finset`, **`exists_defect_sizes`**, **`exists_defect_sizes_S`**, **`fibreValue_sum`** |

### 1.1 Entire coordinates of `exp_{E^♮}` (`ExpCoordsN`)
```
ellN L z w = (σ³℘, σ³℘', σ³, w σ³ − σ²σ', w σ³℘' + σ'²σ'' + σσ'σ''' − 2σσ''²)      -- all entire
ellN_eq_off  (z ∉ Λ) : ellN L z w = σ(z)³ • ptAff (℘ z) (℘' z) (w − ζ z)
ellN_add     (λ ∈ Λ) : ellN L (z + λ) (w + η λ) = sigmaMult λ z ^ 3 • ellN L z w
ellN_eq_smul_expN    : ∃ c ≠ 0, ellN L z w = c • expN L z w          -- for ALL z, w
exists_ellN_growth   : |ellN L z w k| ≤ (1 + |w|) e^{c(1+|z|)²}
```
This matches `VECEXT_SPIKE` §1–2. The fibre coordinate is `t = w − ζ(z)`. At `z = λ ∈ Λ` we get
`ellN = −2·sigmaMult(λ,0)³ • ptO(w − η(λ))`, so `w' = w − ζ(λ)` (Lean's `ζ(λ) = η(λ)`). Note `σ''(0) = 0`
(`deriv_deriv_sigma_zero`). Quasi-periodicity of `ellN` is proved like `ellW_add`: it holds off the lattice by
`sigma_add` and `zeta_add`, and extends by density and continuity. It has the **same multiplier as `ellW`**, while the
fibre coordinate shifts by `η(λ)`.

### 1.2 Monomials of the push-out `G₂` (`MonoV`) [Design + Lean]
* **Fibre forms**: `fibF i (z, s) = s_i Π_l σ_l³ − Σ_j M_ij σ_j²σ_j' Π_{l≠j} σ_l³`. This is the `ker M`-invariant
  `S_i = Σ_j M_ij T₁^{(j)} Π_{l≠j} W_l` of `VECEXT §3.2` for the **all-`W` choice**, written in `s = Mw`. Off the
  lattices it equals `Π σ_l³ · (s_i − (Mζ(z))_i)` (`fibF_eq_off`). It is entire, linear in `s`, and of degree one in every
  elliptic block.
* `fibF_add_per`: under `(λ, Mη(λ))` the multiplier is `Π_j sigmaMult_j³`, the same as for one `ellW` per block.
* `MonoV D`: `Π a^α Π e^{bβ} Π_j Π_t W_{j,t}^{γ_{j,t}} Π_i S_i^{φ_i}`, with `Σ_t γ_{j,t} + Σ φ = D` for every `j`, and
  `Σ φ ≤ D` (the second condition matters only when `m = 0`).
* `MonoV.eval_add_per`: `M(p + ω) = expMult(πω, πp)·M(p)` for `ω ∈ PerV`. This is **the abelian multiplier on the
  base**, so `norm_expMult_le` is reused unchanged.
* Growth: `|M(p)| ≤ (1+|p|)^{D₀+D} e^{D₁|p|} K^D e^{mDc(1+|p|)²}`. Compared with the abelian case the extra factors are
  `(1+|p|)^D K^D`: `fibF` is linear in `s`, and `K = 1 + Σ|M_ij|`.

### 1.3 Prop 2.1 with `V ∩ fibre = 0` (`PropGV`): risk 3 resolved
`exists_coordsVV`: if `V ⊓ fibreV = ⊥`, the projection `π = piT` is injective on `V`. `exists_coordsV` applied to
`π(V)` then gives `n` **non-fibre** coordinate forms restricting to `V ≃ ℂⁿ`. They send `ω ∈ PerV` to the
coordinates of `πω ∈ Per Ls` (`per_coord`), i.e. into the discrete groups `0, 2πiℤ, Λ_j`. `prop21_GV` and
`prop21_GV_deg` are `prop21_G` and `prop21_G_deg` verbatim (same hypotheses `c₁ r² log(R/r) ≤ U`, `D r² ≤ U`, κ-saving
`c₂U^{n+1} ≤ LΔr^κ log(R/r)ⁿ`). The fibre forms `s_i`, whose period images `Σ_j M_ij η_j(Λ_j)` need not be discrete,
are never used.
```
prop21_GV_deg Ls M V (hV : V ⊓ fibreV = ⊥) (hn : finrank V = n) ω (hωV) (hωP : ω i ∈ PerV Ls M) (hω : ℤ-indep) :
  ∃ c₁ c₂ cW K, … ∀ L D D₀ D₁ Δ U R r (μs : Fin L → MonoV d0 d1 m q D), Σα ≤ D₀ → Σβ ≤ D₁ → 1 ≤ L → 0 < Δ ≤ U →
    c₁ ≤ R/r → c₁ ≤ r → c₁ r² log(R/r) ≤ U → D r² ≤ U →
    log L + (D₀ + D) log(1+R) + D log K + D₁ R + m D cW (1+R)² ≤ U → c₂ U^{n+1} ≤ L Δ r^κ log(R/r)^n →
    ∃ p ≠ 0, |p_l| ≤ e^Δ, ∀ z ∈ V, ‖z‖ ≤ r → ‖Σ p_l M_l(z)‖ ≤ e^{−U}
```

### 1.4 Algebraic points and `Λ(G)` (`AlgV`)
* `NLaw_map`: the eight `(3,3)` laws commute with ring homomorphisms (22 component lemmas plus 40 cases).
* **`algPtN_add`**: if all coordinates of `expN(z₁,w₁)` and `expN(z₂,w₂)` are algebraic, so are those of
  `expN(z₁+z₂, w₁+w₂)`. One argument covers all configurations: `NLaw_complete` gives a nonzero law,
  `NLaw_expN_all` makes it proportional to the sum, and the law has entries in `ℚ̄` (`NLaw_map` with
  `ℚ̄ = algebraicClosure ℚ ℂ`). One normalises by entry 2 (affine) or entry 1 (over `O`).
* **`isAlgebraic_zeta_defect`**: for `z₁`, `z₂` lattice points or with `℘(zᵢ) ∈ ℚ̄`, `z₁ + z₂` is again such a point
  and `ζ(z₁) + ζ(z₂) − ζ(z₁+z₂) ∈ ℚ̄`. The proof applies `algPtN_add` to the points `(zᵢ, ζ(zᵢ))`, whose fibre coordinate
  is `0`.
* **`lamVSub`**: `LamV Ls M` is an `AddSubgroup` for algebraic `g₂, g₃, M` (`VECEXT §3.1`, item "LamV is an
  AddSubgroup", estimated 250 lines). The fibre condition uses `s + s' − Mζ(z+z') = (s − Mζz) + (s' − Mζz') + M·defect`.

### 1.5 Chart lower bound (`ChartN`)
`exists_chartN`: `∃ ρ₀ c, ∀ u, ∃ i : Fin 3 (a base coordinate U, V, W), ∀ z w, |z| ≤ ρ₀ →`
`e^{−c(1+|u|)²} ≤ |ellN(u+z, w)_i|` and `|ellN(u+z, w)_k| ≤ (1+|w|) e^{c(1+|u|)²} |ellN(u+z, w)_i|` for all
`k`. The lower bound is `LSG.Aux.exists_chart`, because the base coordinates of `ellN` are `ellV`. The domination
follows from `exists_ellN_growth`. For `G₂`, `fibF / Π_j X_{j,i_j} = s_i Π_j(W_j/X_{j,i_j}) + Σ_j M_ij
(ellN(z_j,0)_3 / X_{j,i_j}) Π_{l≠j}(W_l/X_{l,i_l})`. This is a polynomial in the per-block chart coordinates of
`ellN(·, 0)` and in `s`, so per-block charts suffice.

### 1.6 Sizes of the fibre coordinates (`DefectSize`, `DefectSizeMain`)
The fibre value of `exp_G` at `Σ_k h_k y_k` is
`Σ_k h_k (s_k − Mζ(z_k)) + M·(D_j(h))_j` (**`fibreValue_sum`**), where
`D(h) = Σ_k h_k ζ(z_k) − ζ(Σ_k h_k z_k)` per curve (`Dsum`).
* **Why not the eight laws.** Their bidegree `(3,3)` gives sizes `6^k = S^{log₂6} ≈ S^{2.58}` under balanced
  splitting. That breaks W83's `e^{cS²}`.
* **Route "base addition + ζ addition formula".** `D(h) = D(h₁) + D(h₂) + zdef(u₁,u₂)` (balanced splitting), with
  `zdef(u,v) = ζ(u) + ζ(v) − ζ(u+v)`:
  - `zdef = 0` if `u`, `v` or `u+v` is in `Λ`;
  - `zdef = −(V₁W₂ − V₂W₁)/(2(U₁W₂ − U₂W₁))` generically (`zeta_add_eq`);
  - `zdef = −(12U₁² − g₂W₁²)/(4V₁W₁)` if `u − v ∈ Λ`. This uses **`zeta_two_mul`**,
    `ζ(2u) = 2ζ(u) + (12℘² − g₂)/(4℘')`, newly derived from `NLaw_dbl` and `NLaw_expN_of_add`.

  In base representatives (from `exists_alg_points`) these fractions are forms of bidegree `≤ (2,2)`
  (`exists_defect_frac`, bound `16 G H₁²H₂²`, denominator `dg d₁² d₂²`).
* **`exists_defect_sizes_S`**: for `h_j ≤ S`, `δ·D(h) = N` with `δ ≠ 0` and `N, δ ∈ ι(K)` of house and common
  denominator `≤ e^{BS²}`. The fraction recursion is `s_f(k+1) ≤ 2 s_f(k) + 4·A·4^k + c`, which is geometric. A fraction
  is what Lemma U needs, since fibre values enter `Ψ` with degree `≤ D`: multiply by `δ^D`.

## 2. Gaps / remarks on phase 1
1. **The fibre forms are the all-`W` choice only.** If some `z_j ∈ Λ`, every `fibF` vanishes because of the factor
   `σ_j²`. This is harmless:
   - Prop 2.1 does not care.
   - In Lemma U, the chart rewriting `fibF/ΠX` (§1.5) is a polynomial that stays regular over `O`.
   - Non-vanishing of `P∘exp` is tested off the lattices.

   Other choices `S^{(k)}` (`k_j = V`: `V_j w_j + kapS_j` in block `j`) are entire too. They are needed only if the
   algebraic side insists on them; Philippon applies to any `P ∉ I_G`.
2. `exists_defect_sizes_S` is per curve, with base data in the `LUData` format (`IsRep`, `Sz`). The combination with
   `M`, the `s_k` and the `G_a`/`G_m` data is the identity `fibreValue_sum` plus `Sz` algebra over a common
   denominator `Π_j δ_j`. That algebra is left to `exists_LUDataV` (§3.2).
3. `prop21_GV` needs `V ∩ fibre = 0`. This is the premise of `Theorem41VecLA`, and it is automatic in the §5d engine
   (`VECEXT §2.2`). The full `Theorem41Vec` would need Masser's interpolation (risk R3, about 2.5k lines) or a reduction to
   `G/fibre`.
4. The growth hypothesis in `prop21_GV_deg` has the extra terms `D log(1+R) + D log K`. With `D ≤ Δ/S²`, `R = ν³S` they
   are `≤ Δ` up to constants, which `growth61`-type bookkeeping absorbs.

## 3. Phase 2: Lemma U and Prop 6.1 for `𝒞` — DONE (2026-10-31) [Lean]

Thirteen new files, 3023 lines. No `sorry`/`axiom`/`native_decide`. Every listed result has
`#print axioms = [propext, Classical.choice, Quot.sound]`, and `lake build LSG.W88.Prop61V LSG.AuxFunV.ChartN` is
warning-free, including the mathlib style linters. A build from the phase-1 oleans takes about 7 min; `LemmaUCoreV`
and `Prop61V` take about 1 min and 3 min.

| file | lines | content |
|---|---|---|
| `AuxFunV/SzInv.lean` | 104 | **`sz_inv`**: the inverse of a number of size `(A, d)` has house `≤ d(dA)^{deg}` and denominator `|N(dx)| ≤ (dA)^{deg}` (via `Ideal.absNorm_mem` and Liouville's `norm_norm_le_norm_mul_house_pow`) |
| `AuxFunV/KSTools.lean` | 143 | **`KS.eval_mvpoly`** (an integer polynomial at `KS` series), `differentiableAt_aeval`, `KS.mul_prod`, `zS` (the ζ-increment `ζ(z₀+cs) − ζ(z₀)`), **`ks_zS`** |
| `AuxFunV/FibreId.lean` | 204 | `Qhat`, `Phat`, `lamIdx`, `expN_add_lattice`, **`gT_eq`**, **`fibF_eq_ellN`** |
| `AuxFunV/FpolyV.lean` | 214 | `FctV`, `MonoV.expo`, `coordFV`, `PsiV`, `NW`, `GT`, `fibFac`, `gfacV`, `FpolyV`, `Wpar`, **`FpolyV_eq`**, `contDiff_PsiV` |
| `AuxFunV/KSFib.lean` | 205 | `FibP` (the fibre factor as an integer polynomial), `aeval_FibP`, `CF`, `NF`, **`ks_fibFac`**, `ks_fibVals`, `differentiableAt_fibFac` |
| `AuxFunV/LemmaUDirV.lean` | 275 | `AfacV`, `efacV`, `NfacV`, **`lemmaU_dirV`** |
| `AuxFunV/LemmaUArithV.lean` | 201 | `SzS` calculus (`add`, `mul`, `inv`, `sum`, `common`), `prod_efacV`, `sum_NfacV`, `prod_AfacV`, **`dominate`** |
| `AuxFunV/LemmaUFibC.lean` | 268 | **`LUDataV`**, `cstOf`, `Wpar_eq`, **`cstOf_eq`**, **`exists_fib_consts`** |
| `AuxFunV/LemmaUCoreV.lean` | 602 | `fib_extra_le`, `FamF`, **`lemmaU_coreV`** |
| `AuxFunV/MonoIndepV.lean` | 162 | `MonoV.rexp`, `MonoV.eval_off`, **`exists_PsiV_ne_zero`** |
| `W88/Prop61VData.lean` | 153 | **`exists_LUDataV`** |
| `W88/Prop61VArith.lean` | 74 | **`growth61V`** |
| `W88/Prop61V.lean` | 418 | `monoFamV`, `monoFamV_rexp_injective`, **`prop61V_b`**, **`prop61V`** (namespace `LSG.AuxV`) |

### 3.1 The statement
```
LSG.AuxV.prop61V_b (b) (hb : 1 ≤ b) (Ls) (M) (hg : g₂, g₃ algebraic) (hM : AlgMat M)
    (V W : Submodule ℂ (TanV d0 d1 m r)) (hWV : W ≤ V) (hW : RatSubV W) (hVf : V ⊓ fibreV = ⊥)
    (hn : finrank V < d0 + d1 + m + r) (y) (hyV : y j ∈ V) (hyL : y j ∈ LamV Ls M)
    (ω) (hωV) (hωP : ω i ∈ PerV Ls M) (hω : LinearIndependent ℤ ω) (hNR : d1 + 2 d0 + κ ≤ 2 finrank V) :
  ∃ C > 0, ∃ S₀, ∀ S ≥ S₀, ∃ D L (μs : Fin L → MonoV d0 d1 m r D) p,
    Σα ≤ Δ/(log S)^b ∧ Σβ ≤ Δ/S ∧ D ≤ Δ/S² ∧ (∃ x, PsiV Ls M μs p x ≠ 0) ∧
    ∀ h ≤ S, VanishAlong (PsiV Ls M μs p) W (Δ / log S) (Σ h_j • y_j)
  where Δ = delta61 C (d1 + 2(m+r) − κ) (b d0) (d0+d1+m+r − finrank V) S
```
`prop61V` is `b = 1`. This is the shape of `LSG.W88.prop61_b` with `d₂ = m + r`. `D` is the elliptic degree, which counts
the fibre forms, and the `VanishAlong` conclusion is the analytic one.

### 3.2 How Lemma U was done (deviations from the phase-1 plan)
* **No chart rewriting and no ζ-chord quotients.** The fibre forms go through the natural law `(κ, λ, W)` of `E^♮`
  (`gT_eq`):
  `NLaw(P̂, Q̂(s))₃ = 2λ(X′)·R(s)·ellN(t_k + c s, W_k)₃`, with
  - `P̂ = (X′, 0, 0)` (only `T_λ = 0` enters; `λ = W` if `X′_W ≠ 0`, else `V`),
  - `Q̂(s) = ptAff(℘, ℘′, −Z(s))(z₀+cs)`,
  - `R` the abelian unit,
  - `W_k = ζ(t_k+z₀) + ζ(z₀) − η(ω₁)`.

  This is uniform in all configurations, from `NLaw_expN_all`, and it involves no division by series. Then
  `fibF·ΠR = (cᵢ + vᵢs)·ΠN_W + Σ_j M_ij q_j G_j Π_{l≠j} N_W` (`FpolyV_eq`), so `F_t = ΠR^D·Ψ(t+sv)` with the
  **abelian unit**.
* **Constants as genuine algebraic numbers** (no fractions in Lemma U):
  - `cᵢ = Σ_k h_k τ_i(y_k) + Σ_j M_ij(D_j(h) − zdef(t_j+z₀, z₀))` (`cstOf_eq`);
  - `q_j = (2λ_j(X′_j))⁻¹`.

  Their sizes come from `sz_inv` applied to the fractions of `DefectSizeMain`/`exists_defect_frac`, and they are
  `e^{c_F S²}` (`exists_fib_consts`).
* **Fibre factor sizes without bookkeeping of explicit constants.** The fibre factor is `FibP` (an integer polynomial
  depending only on `m` and the law choices) evaluated at `KS` data. `KS.eval_mvpoly` gives `KS (CF·2^NF·A^NF)` with
  constants depending only on `m`.
* **The Liouville arithmetic reuses `lemmaU_arith` verbatim.** The vector quantity equals the abelian one times
  `(e_fib^{rD} 2^{rD} A_fib^{rD} 2^k)^{deg} ≤ e^E` (`dominate`, `fib_extra_le`), with
  `E = c_E((D+1)S² + (T+1)log(T+2))`. So `lemmaU_arith` applied with `U − E` suffices, and `c₀ = c₀(abelian) + c_E`.
* **Prop 6.1 changes:**
  - `monoFamV` has `a_j, φ_i ≤ D₂` and `D = (r+1)D₂`, so the count is `(D₂+1)^{m+r}`.
  - `siegel61` is applied with `m + r`, `x₂ = (r+1)(D₂+1)` and `c₂' = c₂(r+1)^{m+r}`.
  - `growth61V` absorbs `D log(1+R) + D log K` by putting `log K` into `ν`.
  - `budget61` and `lemmaU_coreV` are the abelian ones.

### 3.3 Gaps after phase 2
1. **§7 for `𝒞` is not started**, as instructed. It waits for the `E^♮` formal exponential (`LSG/MEV/`). The bridge needs:
   - `PpolyV`: monomials ↦ polynomials in the `E^♮` block variables, with `fibF ↦ S_i^{(W)}`;
   - `ordGt_of_vanishAlong` for the class, from the analytic `VanishAlong` of `prop61V_b`;
   - `P ∉ I_G` from `exists_PsiV_ne_zero`.
2. `prop61V` needs `V ∩ fibre = 0` (risk R3, inherited from `prop21_GV`), as `Theorem41VecLA` does.
3. `LUDataV` asks for `g₂, g₃` themselves to be in `K` (not only `g₂/2`), and also for the fibre values of the `y_j` and
   the entries of `M`. `exists_LUDataV` provides all of these.

## 4. Plan for the rest (§7 for `𝒞`, `W88/Sec7V*.lean`) [Est 2.0k]
* `PpolyV` in the `E^♮` block variables `(U, V, W, T₁, T₃)`, with `fibF ↦ S_i^{(W)}`, `ker M`-invariant by construction
  (≈ 300). `eval` at `ellN`-coordinates equals `PsiV` (`fibF_eq_ellN` with any lift `W`).
* `ordGt_of_vanishAlong` along `W̃`, using the MEV formal exponential of `E^♮` (`dt/dz = x`, `T₃/V = O(z³)`), with the
  same Taylor-series uniqueness argument as `Sec7Taylor`/`Sec7Bridge` (≈ 500).
* Counting modulo `G′` with the vector part (`htil_le_span` with `Γ`) (≈ 400).
* Rationality repair: the fibre part is rational since `r ≤ 1`; the `G_a`/graph part goes through `LiftAlg` (≈ 300).
* The inequality with `d₂ = m + r` (Prop 6.1 used with `b = 2`, as in `Sec7`) and assembly
  `theorem41VecLA_of (hME : MultEstVec)` (≈ 500).
