# STAGE5_MEV: the multiplicity estimate on `G̃ = G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮`

Written 2026-10-31 (phase 1). Labels: [Lean] proved in Lean (standard axioms), [Design], [Derived] (hand
computation, not in Lean), [Numerical], [Est] line estimate. Sources: VECEXT.md §3.2, VECEXT_SPIKE.md, STAGE2.md,
`LSG/ME/*`, `LSG/Elliptic/Natural*`.

All new code is in `LSG/MEV/` (namespace `LSG.MEV`), imports `LSG/ME/` and the spike files, edits nothing there,
and is not imported by `LSG.lean` (integrator's choice). Build: `lake build LSG.MEV.Chain LSG.MEV.TranslHF`.
No `sorry`/`axiom`/`native_decide`; every theorem listed below has `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.

## 1. Phase 1: what is done

| file | lines | content |
|---|---|---|
| `Group.lean` | 300 | `repB` (cone representative of `(P, t)`, any field), `exists_smul_repB`; `EVL L` (points of `E^♮` over `ℂ`), `cc`, `expV`, **`AddCommGroup (EVL L)`**, `repV_expV = expN`, **`NLaw_repV`**, `exists_NLaw_ne` |
| `Geom.lean` | 246 | `Var` (blocks `Fin 5`), `blk` (reuses `ME.Blk`), `GPtV`, `coords(Z)`, `vanish`, `zeros`, `gtransl`, density `eval_coordsZ_eq_zero`, relevance `IsRelevant`, `irrel`, `IdealRelevant`, `zeros_eq_empty_of_irrel` |
| `IGPrime.lean` | 497 | `isPrime_span_linear`, `C_dvd_of_C_dvd_linear_mul`, `V_nzd_mod_W_F`, `fgEquiv`, **`isPrime_span_FG`**, `isPrime_span_gensProdS` |
| `IG.lean` | 407 | `lG` (`YZ`, all `F_k`, all `G_k`), `IG`, `IGsub`, **`IG_isPrime`** (all `IGsub` with `T₃ ⊆ T₂`), **`height_IG`** (CI, `= d₁ + 2m`) |
| `IGNull.lean` | 172 | `IG_le_vanish`, `exists_coords_of_rel`, `blockPath`, **`vanish_univ`** (`I(G̃) = I_G̃`) |
| `LawMap.lean` | 125 | `NLaw_map` (laws commute with ring homs), `Fn_map`, `Gn_map`, `scw`, `isWH_of_scw`, `mem_FLE_of_isWH` |
| `Transl.lean` | 364 | `LC = Fin 2 × Fin 2 × Fin 2`, `lawPolyV_mem` (`FLE (single (e k) 3)`), `bmulV`/`tplE`, **`transl_mem_FLE`**, **`transl_IG`**, `eval_transl`, `exists_good`, `eval_transl_good` (`ν = λ³μ`), **`zeros_translI`** |
| `TranslHF.lean` | 173 | `HasData.comp_mul` (any factor `c ≥ 1`), **`hfun_le_transl`** (`8^m`, `t ↦ 3t`), **`hdim_vanish_gtransl`** |
| `FormalExp.lean` | 158 | `vfV`, `stu`, **`ExpBlock`**, **`Fn_ExpBlock`**, `Gn_ExpBlock`, `constantCoeff_ExpBlock`, `ExpBlock_fib`, `LieV`, `ExpV` |
| `PhOp.lean` | 375 | `CF`, **`CF_nlaw`**, `phPt`, `phSub`, `phOp`, **`phOp_mem_FLE`** (`tplE D` for every `κ`), **`phOp_IG`**, `eval_phOp` |
| `Chain.lean` | 178 | `LowZero`, **`OrdGt`**, `ordIdeal`, `IG_le_ordIdeal`, `sig`, `gensR2`, `Lr2`, `Lr2_mono`, `gensR2_mem_FLE`, **`transl_gensR2_mem_FLE`** (`FLE (9 • D)`) |
| **total** | **2995** | |

Key statements (exact text in the files):
* `isPrime_span_FG (h2 : (2:K) ≠ 0) (g₂ g₃ : R) : (Ideal.span {Fcone5 R g₂ g₃, Gcone5 R}).IsPrime` for every domain
  `K`-algebra `R` — **the spike's proof sketch of the primality of `(F, G)` is now a proof** (elementary, §2.2).
* `IG_isPrime`, `height_IG : (Ideal.ofList lG).height = lG.length` (`= d₁ + 2m`): `I_G̃` is a prime complete
  intersection, as `StrongSix`'s `bezout` needs.
* `vanish_univ : vanish univ = IG (g2L Ls) (g3L Ls)`.
* `zeros_translI g J : zeros (translI Ls g J) = {h | h + g ∈ zeros J}`.
* `hfun_le_transl D E g t : hfun (vanish E) t ≤ 8^m · hfun (vanish (gtransl g E)) (3t)`;
  `hdim_vanish_gtransl : (hdata (vanish (gtransl g E))).1 = (hdata (vanish E)).1`.
* `phOp_mem_FLE : Q ∈ FLE D → phOp Ls g w c c' κ Q ∈ FLE (tplE D)` (all `κ`); `phOp_IG`.

## 2. Design decisions and corrections

### 2.1 Points and the group law of `E^♮` (closes the spike's §8 gap over `ℂ`) [Lean]
A point is `⟨base, fib⟩` (`EVL L`): a Mathlib point of `E` and a fibre coordinate, the affine `t = w − ζ(z)` over
affine points and the regular `w' = T₃/V` over `O` (the `O`-fibre chart). The group law is
`(P, s) + (Q, t) = (P + Q, s + t − c(P, Q))` with `c(expE u, expE v) = ζ(u+v) − ζ(u) − ζ(v)`; `c` is defined with a chosen
preimage and is independent of it by quasi-periodicity (`cc_expE`, uses `eta_add` and `ζ(λ) = η(λ)`). The group axioms
are transported along the surjective map `expV(z, w) = (expE z, w − ζ z)` (`expV_add`), so no algebraic cocycle identity
is needed. Points exist only over `ℂ` (the final statement is over `ℂ`; `ℚ̄`-points are `ℂ`-points); the algebraic
layer (`repB`, ideals, primality, CI) is over any field.

### 2.2 Primality of `(F, G)` [Lean]
`R[U,V,W,T₁,T₃] ≅ A[T₁][T₃]` (`A = R[U,V,W]`); modulo the prime `(F) ⊂ A` the ideal becomes `(W̄ T₃ + (2Ū² − V̄ T₁))`
over the domain `S = (A/(F))[T₁]`. A linear polynomial `aT + e` over a domain is prime if `a ∣ eh → a ∣ h`
(pseudo-division + evaluation at `−e/a` in `Frac S`), and that condition reduces, by descending induction on the
`T₁`-degree, to "`V` is a non-zero-divisor modulo `(W, F)` in `A`", which holds because `F ≡ −4U³ (mod W)` and `U` is prime.
Disjoint blocks: `isPrime_span_gensProdS` (relation *sets* per block). The CI chain uses the generator order
`YZ`, all `F_k`, all `G_k`; the intermediate blocks need `(F)` prime in five variables (`isPrime_span_Fcone5`).

### 2.3 Nullstellensatz despite the irrelevant plane [Lean]
The cone over `X` contains `U = V = W = 0` (the boundary of `E^♮`). It still lies in the Zariski closure of the cone
representatives: `(0,0,0,a,b)` is the value at `τ = 0` of `τ · ptAff x₀ y₀ (a/τ)` (`y₀ = b/a`, `x₀` a root of a cubic) or of
`τ · ptO(b/τ)` (`blockPath`). So `vanish univ = I_G̃` holds exactly as in the abelian case.

### 2.4 Translations [Lean]
Laws `NLaw` (bidegree `(3,3)`), all eight per block (`LC`); multiplier `3` (`bmulV`, `tplE`), constant `8^m`. The law
degrees are proved by homogeneity (`scw` rescaling, `NLaw_map`, `NLaw_smul`), not by `fle_tac` (the fibre corrections
`κ` have up to 30 terms). The abelian `dblE`/`HasData.comp_two` are generalized to `tplE`/`HasData.comp_mul` (any `c`).

### 2.5 The formal exponential [Lean + Derived + Numerical]
`ExpBlock g₂ g₃ a b = (s : 1 : t : t u + 2s² : u)` with `(s, t, u)` the formal solution of
`s' = a(−½ − g₂st − (3/2)g₃t²)`, `t' = a(−6s² + (g₂/2)t²)`, `u' = b + a(2g₂s² + 3g₃st)`, `(s,t,u)(0) = 0`.
* [Lean] It lies on `X` (`Fn_ExpBlock`: the Lie derivative of the chart cubic vanishes identically; `Gn_ExpBlock`:
  `T₁ := tu + 2s²` makes `G ≡ 0`), starts at `ptO 0`, and is exactly `ptO(bz)` for `a = 0`.
* [Derived] `u = T₃/V = t_aff − 2x²/y` with `t_aff' = b + a℘`; the polynomial form of `u'` uses the curve equation
  `t = 4s³ − g₂st² − g₃t³`. [Numerical] For `a = 1, b = 0` the solution agrees with `℘/℘'`, `1/℘'`,
  `−(ζ + 2℘²/℘')` (Laurent expansions) through `z¹¹`; `u = g₂z³/6 + 3g₃z⁵/20 + O(z⁷)` (sympy, exact).
  The link "`ExpBlock` = Taylor expansion of the analytic `exp`" is not in Lean (as for the abelian `Exp`; it is a
  Stage 3 matter).

### 2.6 `OrdGt` built from the identity [Design]
`OrdGt Ls W Q n p := ∀ w ∈ W, ∀ c', LowZero n (Q(phPt p w c'))`, `phPt p w c' = law_{c'}(rep p, ExpV w)` (the formal point
`p + exp(zw)` built by the laws from the formal curve at the identity). The abelian code uses the flow through `p` in
canonical charts (`fexp`), which needs `E^♮` chart derivations through arbitrary points. Either definition needs §3.

## 3. Phase 2 (2026-10-31): the `E^♮` curve lemma and the chain — DONE

All items of the phase-1 gap are proved. New files (namespace `LSG.MEV`; no `sorry`/`axiom`/`native_decide`; every
listed theorem `#print axioms` = `[propext, Classical.choice, Quot.sound]`). Build: `lake build LSG.MEV.AVO`.

| file | lines | content |
|---|---|---|
| `FibreDefs.lean` | 72 | charts `Fin 2` (`biE`), `rhoh` (fibre field), `kapB`, `epsT`, **`fibE`** (base expression of the fibre identity) |
| `FibreId{00,01,10,11}.lean` | 4×188 | 32 generated identities `fibId_{ijk}_{ab}`: `fibE ∈ (F(P), F(Q))` (law `i`, moving chart `a`) |
| `FibreId.lean` | 60 | dispatcher **`fib_eq`** |
| `Prop.lean` | 157 | **`exists_common`** (all 8 laws, both orders, are multiples of one vector, char-0 field), **`nlaw_cross`** (cross identity over a char-0 domain via its fraction field) |
| `Flow.lean` | 140 | **`dvalB`** (chart derivation, degree `+2`, exactly tangent to `F`, `G`), **`IsBFlow`**, **`eq_of_isBFlow`**, `IsBFlow.base/.fib` |
| `Curve.lean` | 305 | `starA`, `psi_flow`, **`curve_block`** (the `E^♮` curve lemma), **`curve_all`** |
| `Canon.lean` | 198 | **`ExpBlock_isBFlow`**, `chartV`, **`ZB`** (canonical flow through a point), `flow_through`, **`laws_eq`** (formal associativity), `ExpBlock_eq` |
| `Assoc.lean` | 278 | `ZG` (canonical formal point), `sclV`, `IsHomV`, **`aeval_sclV`**, **`phPt_eq`**, `phPt_unit`, **`lawAt_eq`**, `lawAt_unit`, `GoodLaw` |
| `ChainV.lean` | 166 | **`ordGt_iff`**, **`zeros_phOp`**, `transl_phPt_eq`, **`ordGt_transl`**, **`Lr2_le_vanish_zero`** |
| `Flat.lean` | 275 | `card_Var`, **`hdim_IG`** (`d₀+d₁+3m`), `q0`, `hdim_ge_of_le_vanish_zero`, `const_ZG`, `hdim_Lr2_zero_lt`, **`exists_flat2`** (`r < d₀+d₁+2m`) |
| `DerivV.lean` | 241 | `dvV`, **`Dv ch w`** (derivation of `ℂ[Var]`), `Dv_add/smul`, **`Dv_comm`** (exact), `IsVFlow`, **`taylorV`**, **`ZG_isVFlow`**, **`polarize`** |
| `TwoBlock.lean` | 133 | `isBFlow_map`, **`two_block`** (two-parameter associativity over `ℂ⟦z⟧`) |
| `TwoParam.lean` | 154 | **`dv_words_of_ordGt`**, `sclG`, **`W2`** (two-parameter point), `W2_const`, **`W2_isVFlow`** |
| `AVO.lean` | 298 | `aeval_phOp_map`, `phSub_map_eq`, `lowZero_phOp`, **`ordGt_phOp`**, **`ordGt_transl_phOp`**, **`hAVO2`**, **`ordGt_iff_dv`**, `DLV`, **`words_of_ordGt`** |

Scripts: `scripts/mev_curve/` (`defs.py` parses the law/`κ` definitions from the Lean sources; `fibre_ids.py` computes
the 32 certificates by division w.r.t. `u` (moving point) and `Q₀`; `gen_fibre.py OUTDIR` writes the `FibreId*` files).
Cold compile of the four generated files ≈ 5 min.

### 3.1 How the curve lemma was proved [Lean]
* **Charts and flows.** A flow of `(ζ, β) = (2s, β)` normalized in chart `a ∈ {V, W}` satisfies the 5-component ODE
  `Y' = dvalB a (Y)`: base = abelian `s·c2_a`, chart fibre coordinate `T_a' = β + 2s ρ_a` (`ρ_V = 2g₂U²+3g₃UW`,
  `ρ_W = UW`), the other fibre coordinate from `δG = 0`. Correction to the §3 plan of phase 1: a degree-`+1` lift of the
  fibre direction does **not** exist in the 5-coordinate model (the missing section `T₂ = U t`); `dvalB` is the
  degree-`+1` derivation times the chart form, i.e. degree `+2`. It is exactly tangent to `F` and `G` (`dvalB_F`,
  `dvalB_G`) and the base field and fibre field commute exactly in a fixed chart (`dvalB_comm`), so `Dv ch w`,
  `Dv ch w'` commute (`Dv_comm`).
* **Base coordinates**: the base part of `NLaw` is `2λμ · law_i`, so its renormalization is that of `law_i`; the
  abelian `LSG.ME.tr_eq` and `LSG.ME.renorm_deriv` apply verbatim.
* **Fibre coordinate**: `U D(A_T) − A_T D(U) = 4μ²L²(λ D T_λ − T_λ D λ) − (U Dκ − κ DU)` (`starA`; the `T_μ(B)`-terms
  cancel identically), `λ D T_λ − T_λ D λ = λ²β + λ²·2sρ_a + ε_{a,λ}` along the flow (`psi_flow`), and the generated
  identity `fibE ∈ (F(P), F(Q))` gives `U D(A_T) − A_T D(U) = βU² + 2s ρ_b(A)`, which is the fibre ODE of `U⁻¹A`.
  This is the homogeneous form of `D_P c(P, Q) = x(P) − x(P + Q)`; only base variables occur (32 identities, 12–124
  cofactor terms).
* **All laws**: instead of 28 generated cross identities, `exists_common` (the spike's configuration table over a
  char-0 field) + the fraction field of `R⟦z⟧` (`nlaw_cross`).
* **Associativity**: the renormalized law-translate of a flow through `g` by `h` is a flow through `g + h`
  (`flow_through`); uniqueness (`eq_of_isBFlow`) identifies it with `ZB (g + h)` (`laws_eq`). Two parameters: the same
  over the base ring `ℂ⟦z⟧` (`two_block`), the initial value being identified by the one-parameter `laws_eq`.

### 3.2 Corrections / design notes
* `exists_flat2` gives `r < d₀ + d₁ + 2m` (chain length `= dim G̃`), since `hdim I_G̃ = d₀ + d₁ + 3m` and ideals vanishing
  at `0` have `hdim ≥ m`.
* `ordGt_phOp` uses the hypothesis "formal order `> N` at `y + σ`" (what `zeros_phOp` delivers), not "all words vanish";
  the words are produced inside the proof (`dv_words_of_ordGt`: Taylor along `ZG` + `polarize`).
* The core `lowZero_phOp` is stated for `Γ = sclV u (ZG y w)` with arbitrary `u`, which covers both `phPt y w c'` and the
  translates `τ_v^c` (`transl_phPt_eq`), so no homogeneity of `phOp` outputs is needed.
* Name clash fixed: my `GoodV` (law goodness) is now **`GoodLaw`**; `GoodV` belongs to `SubgroupLiftV.lean`.
* `ChartDerivV.lean` (subgroup-layer agent) defines `Dh` with the `V`-chart block field; it agrees with `dvalB 0`
  (`ζ = 2s`). The two can be merged later (`Dv (fun _ => 0) w` vs `Dh w`).

### 3.3 Still open in this layer
* **Homogenized words at all cone representatives** (the input format of the abelian `mem_VOg_mix` /
  `wustholz_cosets_sl`): `words_of_ordGt` gives the vanishing of all words in `Dv (chartsV p)` at the normalized
  representative `coords p 1`. The Wüstholz phase needs words in a homogenized, chart-glued derivation vanishing at every
  cone representative: homogenize `Dh = L_c² · D_lin + Σ_k (L_c²/L_k²) δ_k` (degree `+2` per block) and use
  `DV_scale`-type equivariance; ≈ 300 lines, best done together with the `E^♮` Wüstholz layer.
* `relevant` version of the pigeonhole (abelian `exists_flat_rel`, `exists_relevant_prime`, `component_rel` of
  `MainAbChain`) for the assembly (≈ 250 lines, mostly copy).
* `isHomV_phOp` (phOp of a homogeneous polynomial is homogeneous of degree `3d`), needed for `A ≤ VOg` in the Wüstholz
  step as in `PhOpHom` (≈ 100 lines).

## 4. What changes in the later phases (subgroups, Wüstholz, slices, assembly)

* **Push-out reduction** (VECEXT §3.2) [Design, confirmed by the code]: work on `G̃` with `ker M`-invariant
  polynomials. A point `(0, v) ∈ ker M ⊆ ℂ^m` acts on block `k` by `T₁ ↦ T₁ + v_k W`, `T₃ ↦ T₃ + v_k V`
  (`repB_add_fib`, `add_expV_fib`, spike `NLaw_fib_left/right`); translations and `phOp` commute with it, so the chain
  ideals are `ker M`-stable and the obstruction `G̃′ ⊇ ker M`, `G′ = G̃′/ker M`. Needed: a lemma "`τ_{(0,v)}` maps the chain
  into itself", and the exponent identity `t̃₂ − d̃₂ = t₂ − d₂`, `c̃ = c`.
* **Subgroups are not products** (VECEXT §1.2): connected subgroups of `G̃` are `T_U × (B̃^♮ + Γ)`, `Γ ⊆ ℂ^{d₀} × ℂ^m`
  rational, with possible graph parts mixing `G_a^{d₀}` and fibre directions (paper type E). Changes against
  `LSG/ME/Subgroup*`, `Product*`: `lieAlg ⊆ ℂ^{d₀} × ℂ^{d₁} × (ℂ²)^m`; `exp_G̃` surjective (from `expV_surjective`);
  `exp⁻¹(H)` contains the periods `(λ, η(λ))`; **`perTanId(t) ⊆ T′`** (if `(λ, s) ∈ T′` then `exp(0, s − η(λ)) ∈ H ∩ fibre`, a
  vector subgroup); the product decomposition `lieAlg_eq_prod` becomes `T′ = U^⊥ ⊕ (perTanId t + Γ)` with a graph
  `Γ₀ = graph(pr₀Γ → ℂ^m)` (VECEXT §2.2 "made explicit"); W88's projection exponents `t₀ = dim pr₀(T′)`, `t₁ = dim U^⊥`,
  `t₂ = dim T′ − t₀ − t₁` (counts base and fibre dimensions of the `E^♮` part).
* **Hilbert lower bound** (`hfun_H0_ge''`): on an `E^♮` block monomials `x^a y^b t^c` give `≳ D²` independent sections
  (`dim E^♮ = 2`); the free cone scalings are unchanged (one per block); the projection to `π_L(H⁰) × (E^♮)^{J₂}` needs the
  `E^♮` analogue of `SubgroupConeE`.
* **Wüstholz** (`WustAlg`, `WustCoset`, `WustTrans`, `WustId`): derivation words with the `E^♮` chart derivations of §3
  and `∂_w`; transversals for `E^♮` cosets (chart forms `V, W` plus the fibre coordinate); `Dh` homogenization with the
  product of chart forms as before.
* **Slices** (`Slice*`): `ℓ_k = V_k + α_k W_k` still kills the boundary (`ℓ` vanishes on `U = V = W = 0`); on `ℓ = 1`,
  `T₁ = W t′ + 2U²` (`slice_rel`), so the sliced block ring is `(sliced E ring)[t′]`, still a CI; `hfun_slIG_le` gets the
  extra variable `t′` with exponent `≤ D` (degree 6 per block instead of 3); `hdata_slIG`: `hdim (sl α I_G̃) = d₀ + d₁ + 2m`.
  Bézout applies unchanged.
* **Assembly** (`MainAb*`): constant with `3`'s and `9`'s in place of `2`'s and `4`'s (grading `9 • D` for Roy's `A`),
  `8^m` law choices, `hdim G̃ = d₀ + d₁ + 2m`; final arithmetic with `D₂^{t₂}` vs `D₂^{2m}` (before the push-out).

## 5. Size estimate for the remaining phases [Est]

Phases 1–2 (this agent): 3.0k + 3.23k (of which 0.75k generated) lines. Remaining after phase 2 and the subgroup phases S/S2:

| item | lines |
|---|---|
| homogenized words at all cone representatives, `isHomV_phOp`, relevant pigeonhole | 650 |
| subgroup layer rest (G1, G3 `finite_cosets_H0`, G4 Hilbert bound; see §6) | 1500 |
| Wüstholz for `E^♮` blocks | 1200 |
| slices (`Slice`, `SliceDim`, `SliceIG`, `SliceWust*`) | 1800 |
| push-out reduction + `MainVec` assembly + arithmetic | 1600 |
| **total** | **≈ 6.8k (±2.5k)** |

## 6. Subgroup layer, phase S (2026-10-31)

New files `LSG/MEV/Subgroup{Stab,Exp,Class,Push,AntiAff}.lean` (namespace `LSG.MEV`, 1378 lines, no
`sorry`/`axiom`/`native_decide`, all listed theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Build: `lake build LSG.MEV.SubgroupPush LSG.MEV.SubgroupAntiAff`. Not imported by `LSG.lean`.

| file | lines | content |
|---|---|---|
| `SubgroupStab.lean` | 206 | `IsZClosed`, `zeros_vanish`, `zcl`, `isZClosed_gtransl`, `gtransl_eq_of_subset`, **`stabG_isSubgroup`**, `stabIdeal`, **`stabG_eq_zeros`**, **`isZClosed_stabG`**, **`zcl_isSubgroup`** |
| `SubgroupExp.lean` | 265 | `TanG = TanV d₀ d₁ m m`, `expGV` (hom, onto), **`expGV_eq_zero_iff`** (kernel `= PerV Ls 1`), `Htil`, `per_le_Htil`, **`lieAlg`**, linear subgroup `inLin`, `HL`, **`HL_eq_prodSet`**, `expGV_of_lattice` |
| `SubgroupClass.lean` | 368 | `SubgroupPreV` (+`tan`, `toDataV`), `piZ`, **`mem_lieAlg_lin_iff`**, **`lin_mem_lieAlg_of_Htil`**, `eq_zero_of_lattice`, **`torus_mem`**, **`lieAlg_comap_torIncl`**, **`per_mem_lieAlg`**, **`perTan_map_le`**, `exists_perTanId`, **`lieAlg_eq_tan`**, **`exists_subgroupPreV`** |
| `SubgroupPush.lean` | 244 | `pushM`, `pushM_per`, `SubgroupPreV.push`, **`tan_push`**, `ratPair_map`, `fib_mem_lieAlg`, **`comap_map_pushM`**, `map_prA_tan`, `map_prB_tan`, **`finrank_tan_eq`** |
| `SubgroupAntiAff.lean` | 295 | `ηR` (ℝ-extension of `η`), `legC_pos`, **`pair_eq`** (Legendre, bilinear form), `EV`, `omegaV`, **`finrank_perTanId`** |

### 6.1 Statements (exact text in the files)
* `lieAlg Ls hH : Submodule ℂ (TanG d₀ d₁ m) := {v | ∀ c : ℂ, c • v ∈ Htil Ls hH}`. This is the complex-line
  definition. It equals the real linear part of `H̃` once the analytic `smul_mem_Htil` is ported (gap G2).
* `HL_eq_prodSet hH hc : HL Ls H = prodSet (linV (HL Ls H)) (latt (HL Ls H))`. `HL H = inLin⁻¹ H` is `H` inside the
  linear group `G_a^{d₀} × G_m^{d₁} × (fibres over O) ≅ G_a^{d₀+m} × G_m^{d₁}`. On the `O`-fibre the cone
  coordinates are `(0 : 1 : 0 : 0 : w)`, which are polynomial in `w`, so StrongSix's `classify` applies. This one
  algebraic input gives both the linearity of the vector part and the rationality of the torus part.
* `lieAlg_eq_tan hH hc hab : lieAlg Ls hH = ((lieAlg Ls hH).comap vecIncl).map vecIncl ⊔
  (torusLie (qspan (latt (HL Ls H)))).map torIncl ⊔ (perTan Ls 1 ((lieAlg Ls hH).map piZ)).map g2Incl`,
  where `hab : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ)`.
* `exists_subgroupPreV hH hc hab : ∃ S : SubgroupPreV Ls 1, S.tan = lieAlg Ls hH ∧ S.U = qspan (latt (HL Ls H)) ∧
  S.t = (lieAlg Ls hH).map piZ ∧ S.gam = (lieAlg Ls hH).comap vecIncl`.
* `SubgroupPreV.tan_push S M : (S.push M).tan = S.tan.map (pushM M)`, with `Γ ↦ (id × M) Γ` and `t, U` unchanged.
  `comap_map_pushM : (∀ v, M v = 0 → (0,0,0,v) ∈ T) → (T.map (pushM M)).comap (pushM M) = T`.
  `ratPair_map : AlgMat M → RatPair Γ → RatPair (Γ.map (id × M))`.
* `finrank_perTanId : IsAbelianTangent Ls t → finrank ℂ (perTanId Ls t) = 2 * finrank ℂ t`.
* `SubgroupPreV.finrank_tan_eq S : finrank S.tan = finrank (S.gam.map fst) + finrank (torusLie S.U) +
  finrank (S.tan ⊓ (ker prA ⊓ ker prB))`. Also `map_prA_tan : S.tan.map prA = S.gam.map fst` and
  `map_prB_tan : S.tan.map prB = torusLie S.U`. These hold for every `M`.

### 6.2 Design findings and corrections
* **The family of VECEXT §1.2 is correct**: the classification output is exactly `SubgroupDataV.tan`, minus the
  rationality of `Γ`. That rationality is not automatic over `ℂ`; it is the job of the §7 rationality repair.
* **`perTanId(t) ⊆ T′` needs no anti-affineness.** If `(a, 0, λ, s) ∈ T′` with `λ ∈ Λ`, then
  `(a, 0, 0, s − η(λ)) = (a, 0, λ, s) − (period)` is a vector of `H̃` inside the vector group. That vector group is a
  `ℂ`-subspace (`HL_eq_prodSet`), so the vector lies in `T′`, and hence `(0, 0, λ, η(λ)) ∈ T′`. The `a`-parts cancel,
  so there is no graph from the base to `G_a`.
* **Where anti-affineness really enters: the dimension count.** `finrank_perTanId` says the periods span all of
  `T(B^♮)` (dimension `2 dim t`). This follows from Legendre in the bilinear form
  `z ηR(z′) − z′ ηR(z) = −i c_L Im(z̄ z′)` with `c_L > 0`, plus positivity of `E(x, ix)` on the complex space `t`.
  The count is needed for the §5d engine (`rk(Ω ∩ T_{G′}) = d₁′ + 2 dim t`, `d₂′ = dim t + f′`), not for the
  classification itself.
* **Exponents.** W88's projection exponents for an obstruction `S` are `t₀ = finrank (S.gam.map fst)`
  (`= dim π₀ T′`, so `SubgroupDataV.δ0 = d₀ − t₀`) and `t₁ = finrank (torusLie S.U)`. For `δ1 = dim U = d₁ − t₁`,
  use `LSG.ME.finrank_torusLie`. Finally `t₂ = finrank (S.tan ⊓ (ker prA ⊓ ker prB)) = dim (perTan t + Γ_fib)`,
  which counts both the base and the fibre directions of `G′ ∩ G₂`.
* **Push-out.** The obstruction `G̃′ ⊇ ker M` (`fib_mem_lieAlg`) is recovered from `G′` (`comap_map_pushM`), and its
  datum pushes forward (`tan_push`). So the subgroup layer can be done entirely on `G̃` (`M = 1`).

### 6.3 Output form for the later assembly
For the stabiliser `H = stabG (zeros p)` (`stabG_zeros_isSubgroup`; `H ⊇ ker M`-fibres when `p` is `ker M`-stable):
`S := (exists_subgroupPreV hH hc hab).choose` gives `T̃′ = S.tan`; the assembly uses `S.push M` with
`(S.push M).tan = T̃′.map (pushM M)`, `t₀, t₁, t₂` as in §6.2, and `SubgroupPreV.toDataV` once `Γ` is made
rational (`ratPair_map` for the push-out). Still to be supplied by the analytic layer (gaps below):
`hdim (vanish H⁰) = finrank T̃′ + m` and the Hilbert lower bound with exponents `(t₀, t₁, t₂ + m)`.

### 6.4 Gaps (not done)
* **G1 (the only hypothesis of the classification)**:
  `isAbelianTangent_map_piZ : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ)` for `H` a Zariski-closed subgroup.
  This is the MEV analogue of `LSG.ME.isAbelianTangent_map_piA`, which is a transcendence-degree count needing
  `trdeg_H0`. No cheap reduction to the abelian layer was found: it would need `q(H) ⊆ G` closed for
  `q : G̃ → G`, i.e. Chevalley.
* **G2**: `isClosed_Htil` and `smul_mem_Htil` (real line ⇒ complex line). These need local analytic lifts of
  `expV` to the 5-dim cone: `(℘, ℘′, 1, w − ζ, ℘′(w − ζ) − 2℘²)` off `Λ`, times `(z − l)³` near `l ∈ Λ`. The last
  entry is analytic at `l` because `ζ(z) − 1/(z − l) − const = O((z − l)³)`.
* **G3**: `H⁰ = zcl(exp T̃′)`, its primality, `trdeg_H0`, `hdim_H0` (cone shift `m`, one per `E^♮` block),
  `finite_cosets_H0`, and `mem_TZ_iff` (Zariski tangent = `lieAlg`). These need the `E^♮` chart derivations of §3,
  item 1.
* **G4**: the Hilbert lower bound (`hfun_H0_ge''` analogue). Choose base coordinates `ι_z` with `t ↠ ℂ^{ι_z}` and
  fibre coordinates `ι_w` with `(perTanId t + Γ_fib) ↠ ℂ^{ι_z} × ℂ^{ι_w}`, so `|ι_z| + |ι_w| = t₂`. Then use cone
  monomials in the `ι_z` blocks, powers of `T₁`/`T₃` in the `ι_w` blocks, and free scalings elsewhere.

### 6.5 Phase S2 (2026-10-31): G2 done, G3 done except `finite_cosets_H0`

New files (namespace `LSG.MEV`; no `sorry`/`axiom`/`native_decide`; every listed theorem has
`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Build: `lake build LSG.MEV.SubgroupDimV`.

| file | lines | content |
|---|---|---|
| `SubgroupLie.lean` | 167 | **global entire lift** `liftV p μ` (from `LSG.AuxV.ellN`: `σ³`-coordinates, no local lifts needed), `liftV_eq`, `mem_iff_liftV`, **`isClosed_expGV_preimage`**, **`isClosed_Htil`**, `smul_mem_of_frequently`, **`smul_mem_Htil`**, **`restrictScalars_lieAlg`** (`lieAlg` = real linear part `linPart H̃`) |
| `ChartDerivV.lean` | 267 | block field `bField` (`V`-chart, degree `+2`, direction `(a, b)`), `bField_eq_zero_of_V`, derivation **`Dh Ls w`** (`D̂_w`), `eval_Dh`, `DV` (evaluated field), `DV_add/smul`, `DV_of_V`, **`DV_scale`**, **`DV_eq_zero_of_V`** |
| `SubgroupLiftV.lean` | 269 | `FVb`, `FV Ls p` (`V`-normalised lift), **`hasDerivAt_FVb`** (off `Λ` by `℘, ℘′, ζ` calculus; at `Λ` by continuity of the derivative), `hasDerivAt_FVb_line`, `GoodV`, `FV_eq_coords`, **`hasDerivAt_eval_FV`** (`d/dc Q(FV(p + c w)) = (D̂_w Q)(FV p)`) |
| `SubgroupTangentV.lean` | 452 | `scl`, `eval_Dh_scale`, `euler_eq_zero`, **`TZ`**, **`first_order`**, **`Dh_mem_vanish`**, **`TZ_subset_lieAlg`**, `lieAlg_subset_TZ`, **`TZ_eq_lieAlg`** |
| `SubgroupDimV.lean` | 468 | **`H0`**, `H0_isSubgroup`, `H0_subset`, **`lieAlg_H0`**, **`vanish_H0_isPrime`**, **`finrank_tangentSpace_zero_le`**, **`le_finrank_tangentSpace`**, **`trdeg_H0`**, **`hdim_H0`** |

Statements:
* `restrictScalars_lieAlg hH hc : (lieAlg Ls hH).restrictScalars ℝ = LSG.Subgroups.linPart (Htil Ls hH)`.
* `TZ_eq_lieAlg hH hc : TZ Ls H = lieAlg Ls hH`, where
  `TZ Ls H = {w | ∀ Q ∈ vanish H, eval (FV Ls 0) (Dh Ls w Q) = 0}` and `FV Ls 0 = (0, 1, 1, (0:1:0:0:0)_k)`.
* `trdeg_H0 hH hc : (Algebra.trdeg ℂ (MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish (H0 Ls hH))).toNat
  = finrank ℂ (lieAlg Ls hH) + m`.
* `hdim_H0 hH hc D hD : (StrongSix.M2.hdata blk D ℂ (vanish (H0 Ls hH))).1 = finrank ℂ (lieAlg Ls hH) + m`.

Design notes:
* **No local lifts.** The phase-1 analytic layer's `ellN` is an entire lift of `exp_{E^♮}` that
  represents it everywhere. Closedness and the real-to-complex step therefore reduce to the identity
  theorem on `ℂ` for the entire functions `c ↦ P(liftV(c v, μ))`.
* **No multihomogeneity.** The abelian layer works with `homogVanish`. Here every argument uses all block
  rescalings: `scl r` keeps `vanish H` stable, and `D̂_w` is rescaling-equivariant up to `∏ r_k²`
  (`DV_scale`). The Euler terms vanish because `Q` vanishes on all rescalings of a cone point of `H`
  (`euler_eq_zero`).
* **`D̂_w` vanishes identically at `2`-torsion fibres.** The block field is `0` at points of `X` with
  `V = 0`, `W ≠ 0`, by `F = G = 0` (`bField_eq_zero_of_V`), so no Euler argument is needed there.
* **The chart derivation** is my own minimal version (`ChartDerivV.lean`). It is the same block field as
  `Flow.lean`'s `dvalB 0` up to the parametrisation `ζ = 2s`. That file is a vector function, not a
  derivation of `ℂ[Var]`, so it could not be reused directly.
* **Lower bound.** It uses `LSG.ME.exists_smooth_point` with `h = ∏ V_k`, `IGNull.exists_coords_of_rel`,
  and injectivity via `LSG.ME.chartVf_ne_zero`.

Still open:
* **G3 rest: `finite_cosets_H0`** (`H` is a finite union of cosets of `H⁰`). This needs the
  components / translation-of-components layer (`LSG.ME.SubgroupComp`: `exists_components`,
  `vanish_gtransl_isPrime`) ported to `GPtV`, plus `trdeg_le_of_subset`.
* **G1 (`IsAbelianTangent Ls ((lieAlg Ls hH).map piZ)`), plan.**
  1. Let `K = zcl_G(q(H⁰))` in the abelian group `G` (ME layer). A `G`-polynomial vanishes on `q(H⁰)`
     iff it vanishes on `H⁰` as an MEV polynomial (the `T`-variables are not involved). Hence
     `ℂ[G]/I(K) ↪ ℂ[Var]/vanish H⁰`, and `K = H0_ME(K)` is irreducible with
     `trdeg = dim lieAlg_ME K + m` (ME `trdeg_H0`).
  2. Show that a coordinate transcendence basis of `K` together with `dim(T′ ∩ fibre)` fibre variables
     is algebraically independent mod `vanish H⁰`. Use `T₁_k` on blocks whose base is generically
     affine on `H⁰`, and `T₃_k` on blocks whose base is `O` on `H⁰`; this is a sweep along the fibre
     directions of `T′`, with `eq_zero_of_eval_elim` and a density step through the entire `σ³`-lift.
  3. Then `dim lieAlg_ME K ≤ dim q_*T′`, so `q_*T′ = lieAlg_ME K`. Its abelian part is an abelian
     tangent (ME `lieAlg_eq_prod`, `isAbelianTangent_comap_inAbL`), and it equals `π_Z(T′)`.
  This discharges the hypothesis `hab` of `exists_subgroupPreV` (§6.1).
* **G4 (Hilbert lower bound)**: as in §6.4, with `hdim_H0` now available for the matching upper exponent.

## 8. Slice layer (2026-10-31, slice agent)

New files `LSG/MEV/Slice{,IG,Dim,Coset}.lean` (namespace `LSG.MEV`, 1585 lines, no
`sorry`/`axiom`/`native_decide`; every listed theorem has `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). Build: `lake build LSG.MEV.SliceCoset` (imports the other
three). Not imported by `LSG.lean`. No committed or other agents' files were edited.

| file | lines | content |
|---|---|---|
| `Slice.lean` | 308 | `wtV` (multigrading by `E^♮` blocks), **`isHomV_iff_wtV`**, `lsl α k = V_k + α_k W_k`, **`sl α I`**, `lval`, `nrm`, `vanishS`, `sl_vanish_le`, `coords_mul`, `eval_coords_eq_zero_iff`, **`hom_mem_vanish_of_mem_sl`**, **`hfun_le_of_hom`**, **`hfun_le_sl`** |
| `SliceIG.lean` | 494 | standard monomials `IsStdV`, **`hfun_slIGV_le`**, `lGsV`, `slIGV_eq_ofList`, `slIGV_ne_top`, `polIGV`, **`hdata_slIGV`**, **`height_slIGV`** (any field, `2 ≠ 0`) |
| `SliceDim.lean` | 388 | partial slices `nscal`, **`vanishP s α E`**, `homP` + **`eval_homP`**, **`vanishP_isPrime`**, `vanishP_mono/antitone`, `lsl_sub_one_(not)Mem_vanishP`, **`hdim_vanishP_add_le`**, `hom_mem_vanish_of_mem_vanishP`, `sl_vanish_le_vanishP`, `vanishP_univ_eq_vanishS`, `Zs`, **`exists_coords_of_IGV`**, **`radical_sl`** |
| `SliceCoset.lean` | 395 | `comp_mem_vanish`, `exists_homog`, `exists_homogVanish_ne`, **`exists_good_alpha`**, `point_of_lsl_notMem`, `vanishP_biUnion_eq_inf`, **`hdim_vanishP_cosets_le`**, **`hfun_sum_cosets_P`**, **`hfun_P_transl_ge`**, **`hfun_cosets_ge`**, `hfun_P_coset_ge_H0`, `exists_reps_GV`, `not_gtransl_subset_of_sub_notMem` |

### 8.1 Design: how the fibre coordinates enter [Lean]
* One slice form per block, on the **base** coordinates only: `ℓ_k = V_k + α_k W_k`; `T₁, T₃` are not
  sliced. `ℓ_k` vanishes on the irrelevant plane `U = V = W = 0`, so every zero of `sl α I` (`I_G̃ ≤ I`)
  has nonzero base parts and is a cone representative (`exists_coords_of_IGV`, via
  `exists_smul_repB`: the fibre coordinate is then determined by the point of `E^♮`).
* The sliced block ring is `(sliced E ring)[t′]`; in Lean this is seen by standard monomials in the
  original coordinates. Reductions (block degree non-increasing): `YZ → 1`, `V → 1 − αW`,
  `U³ → ¼(V²W + g₂UW² + g₃W³)`, **`W T₃ → V T₁ − 2U²`** (from `G`), measure
  `Σ (Y + Z + U + V + 3 T₃)`-exponents (strictly decreasing for all four rules). Standard monomials: no
  `V`, `U ≤ 2`, `min(W, T₃) = 0`, `min(Y, Z) = 0`; injection into `Fin 3 × Fin (N+1) × Fin (2N+1)` per
  block via `(U, T₁, N + W − T₃)`. (On the slice, `W T₃ ≡ T₁ − α W T₁ − 2U²` is the top-degree form of
  `slice_rel`, so `T₁` is *not* eliminated; `t′` is implicit.)
* No localisation / dehomogenisation isomorphism: primality of partial slices is by homogenisation
  with powers of `ℓ_k` (`homP`), exactly as in the abelian layer.

### 8.2 Statements (exact text in the files)
* `hfun_slIGV_le g₂ g₃ h2 α D t : hfun blk D K (sl α (IG g₂ g₃)) t ≤
  (t * D .x + 1) ^ d₀ * (2 * (t * D .yz) + 1) ^ d₁ * ∏ k, 3 * ((t * D (.e k) + 1) * (2 * (t * D (.e k)) + 1))`.
* `hdata_slIGV g₂ g₃ h2 α hD : (hdata blk D K (sl α (IG g₂ g₃))).1 = d₀ + d₁ + 2 * m ∧
  (hdata blk D K (sl α (IG g₂ g₃))).2 ≤ ((d₀ + d₁ + 2 * m)! * D .x ^ d₀ * (2 * D .yz) ^ d₁ * ∏ k, 6 * D (.e k) ^ 2 : ℕ)`.
* `height_slIGV g₂ g₃ h2 α : (Ideal.ofList (lGsV g₂ g₃ α)).height = (lGsV g₂ g₃ α).length` (`= d₁ + 3m`), with
  `slIGV_eq_ofList : sl α (IG g₂ g₃) = Ideal.ofList (lGsV g₂ g₃ α)` — the form `bezout` needs.
* `hfun_le_sl α hp hℓ D t : hfun blk D ℂ (vanish E) t ≤ (∏ k, (t * D (.e k) + 1)) * hfun blk D ℂ (sl α (vanish E)) t`
  (`vanish E` prime, `∀ k, lsl α k ∉ vanish E`); `hfun_le_of_hom` for any `I` whose `wtV`-homogeneous
  elements lie in `vanish E` (e.g. `vanishP univ α E`).
* `radical_sl α (hI : IG (g2L Ls) (g3L Ls) ≤ I) : (sl α I).radical = vanish' (nrm α) (Zs α I)`.
* `vanishP_isPrime hp hℓ hg₀ hs₀ : (vanishP s α E).IsPrime`;
  `hdim_vanishP_add_le D hD hp hℓ hg₀ hs₀ s : (hdata blk D ℂ (vanishP s α E)).1 + s.card ≤ (hdata blk D ℂ (vanish E)).1`.
* `exists_good_alpha (hV : V.Nonempty) R : ∃ α, ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V)`.
* `hdim_vanishP_cosets_le D hD hV hp R hα hne : hdim (vanishP univ α (⋃ a ∈ R, gtransl a V)) + m ≤ hdim (vanish V)`.
* `hfun_sum_cosets_P D hD α hV hp R hα hdist : ∃ c, ∀ t, ∑ a ∈ R, hfun (vanishP univ α (gtransl a V)) t ≤
  hfun (vanishP univ α (⋃ a ∈ R, gtransl a V)) (t + c)` (`hdist`: translates pairwise non-nested).
* **Per-coset lower bound** `hfun_P_transl_ge D hV hp a α hℓ L hL t : L t ≤ 24 ^ m * hfun blk D ℂ
  (vanishP univ α (gtransl a V)) (3 * t)` from `hL : ∀ t, L t * ∏ k, (t * D (.e k) + 1) ≤ hfun blk D ℂ (vanish V) t`.
  `hfun_cosets_ge` (same `L`, distinct translates): `∃ c, ∀ t, R.card * L t ≤ 24 ^ m * hfun blk D ℂ
  (vanishP univ α (⋃ a ∈ R, gtransl a V)) (3 * t + c)`. `hfun_P_coset_ge_H0`: `V = H0 Ls hH`.
  Constant: `8^m` (translation, `hfun_le_transl`) × `3^m` (`∏ (3tD_k+1) ≤ 3^m ∏ (tD_k+1)`).

### 8.3 Gaps / interface notes
* **G4 not landed** (no Hilbert lower bound for `vanish (H0 Ls hH)` in `Subgroup*.lean` yet). The input
  needed is exactly `hL` above: `L(t) · ∏_k (tD_k + 1) ≤ H(vanish H⁰; t)` with `L` a polynomial-type bound
  of degree `t₀ + t₁ + t₂` (`t₂` counting base and fibre directions of `T′ ∩ (E^♮ part)`); the factor
  `∏ (tD_k + 1)` is the free cone scaling per block, which slicing removes.
* Coset primality uses the subgroup agent's `vanish_gtransl_isPrime` (`SubgroupCompV.lean`, imported,
  not edited); `finite_cosets_H0` + `exists_reps_GV` + `not_gtransl_subset_of_sub_notMem` give the distinct
  cosets for `hfun_cosets_ge`.
* For the sliced Wüstholz agent: import `LSG.MEV.Slice` (`lsl`, `sl`, `wtV`, `isHomV_iff_wtV`,
  `hom_mem_vanish_of_mem_sl`); `sl α I = I ⊔ span (ℓ_k − 1)` as in the abelian layer.
* Not ported (assembly pieces, need the MEV phOp/zeros layer): `Zs_subset_transl` (normalised zeros of
  Roy's `A` lie in `{h | h + V ⊆ Z(L_r)}`), `biUnion_gtransl_cover`, the final arithmetic.
* Degree bound for `sl α I_G̃` uses leading coefficient `6 D_k²` per block (an upper bound; the true
  degree of `X ⊂ ℙ⁴` is `6`, i.e. leading term `3 D_k²`).

### 6.6 Phase S3 (2026-10-31): G1, G3 rest, G4 done — the subgroup layer is complete

New files (namespace `LSG.MEV`; no `sorry`/`axiom`/`native_decide`; every listed theorem has
`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Build:
`lake build LSG.MEV.SubgroupHilbV3` (imports all of them). Not imported by `LSG.lean`.

| file | lines | content |
|---|---|---|
| `SubgroupCompV.lean` | 402 | `IsZClosed.inter`, `evPt`, **`vanish_singleton_isPrime`**, **`exists_components`**, **`vanish_gtransl_isPrime`** (laws `nlawc`, multiplier `λ³`), **`finrank_tangentSpace_zero_le'`** (for `vanish H`), **`trdeg_le_of_subset`**, **`finite_cosets_H0`** |
| `SubgroupAbV.lean` | 418 | `coords_expGV_e/_y`, `expN_base`, `ellN_base`, `actB`, **`exists_avoid`** (Mathlib's `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`), `countable_line_lattice`, **`dens_ME`**, `decV`, `rhoV`, `mvV`, **`isAbelianTangent_map_piZ`** (G1), **`exists_subgroupV`**, `lieAlg_eq_tanV` |
| `SubgroupHilbV.lean` | 320 | `repV_base`, `ιLV`, `linPtG`, `monoPV`, **`coeff_sep`**, `L0V`, `FibV`, **`exists_H0_pointV`**, **`indep_coreV`**, `d1_sub_U0`, **`finrank_T2`**, **`t0_add_t1_add_t2`** |
| `SubgroupHilbV2.lean` | 276 | `fcI`/`svI` (fibre coordinate `T₁`/`T₃` and its coefficient `W`/`V`), `coordsZ_fibshift`, `eval_P0`, **`sepA`**, `exists_sv_point`, block-degree helpers |
| `SubgroupHilbV3.lean` | 194 | **`hfun_H0_ge_genV`**, **`hfun_H0_geV`**, **`hdim_H0_eq_exps`** |

Statements (`T′ = lieAlg Ls hH`, `H` a Zariski-closed subgroup):
* `finite_cosets_H0 hH hc : ∃ R : Finset (GPtV d₀ d₁ Ls), (∀ h ∈ R, h ∈ H) ∧ H ⊆ ⋃ h ∈ R, gtransl h (H0 Ls hH)`.
* `isAbelianTangent_map_piZ hH hc : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ)` (**G1**), hence
  `exists_subgroupV hH hc : ∃ S : SubgroupPreV Ls 1, S.tan = T′ ∧ S.U = qspan (latt (HL Ls H)) ∧
  S.t = T′.map piZ ∧ S.gam = T′.comap vecIncl` with **no hypothesis** (and `lieAlg_eq_tanV`).
* `hfun_H0_geV hH hc D₀ D₁ D₂ t : (t*D₀/t₀ + 1)^t₀ * (t*D₁/t₁ + 1)^t₁ * (t*D₂/2 + 1)^(t₂ + m) ≤
  hfun blk (LSG.ME.Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH)) t`, where
  `t₀ = finrank ((T′.comap vecIncl).map fst)` (= `finrank (S.gam.map fst)`, §6.2),
  `t₁ = finrank (T′.comap torIncl)` (= `finrank (torusLie S.U)`),
  `t₂ = finrank (T′ ⊓ (ker prA ⊓ ker prB))` (the §6.2 convention).
* `hdim_H0_eq_exps : (hdata blk D ℂ (vanish H⁰)).1 = t₀ + t₁ + t₂ + m`: **the bound has the full degree**.
* `finrank_T2 : t₂ = finrank (T′.map piZ) + finrank (FibV Ls hH)`, `FibV = {w | (0,0,0,w) ∈ T′}`;
  `hfun_H0_ge_genV : H(L0V; tD₀, tD₁) · (⌊tD₂/2⌋+1)^(dim t + dim FibV + m) ≤ H(vanish H⁰; tD)`.

Design notes / findings:
* **G1 proof** = the §6.5 plan, with two simplifications. (a) Fibre coordinates: `T₁` on blocks where
  `t` is not identically `0` (`actB`; the base of a *generic* point is affine there), `T₃` on the other
  blocks (base `O`). (b) Genericity (`z_k ∉ Λ` on active blocks) is handled on the abelian side only
  (`dens_ME`): a vector `v ∈ t` nonzero on active blocks, the entire lift `ellN`, and a countable bad set
  on the line `z + c v` (no identity theorem needed, `Continuous.ext_on` with a dense co-countable set).
  The abelian subgroup is `B = zcl_G(exp(0 × 0 × t))` exactly as in `ProductRat`.
* **G4: exact exponents.** With `ι_z` coordinates for `t` (`|ι_z| = dim t`) and `ι_w` coordinates for
  `FibV`: cone monomials in the `ι_z` blocks contribute `2 dim t`, fibre powers in the `ι_w` blocks
  `dim FibV`, coefficient powers ("free scalings") in the `m − dim t` other blocks `m − dim t`; total
  `dim t + dim FibV + m = t₂ + m`. **No anti-affineness is needed** (`finrank_perTanId` is not used):
  `T′ ∩ ker π₀ ∩ ker π₁ → t` is onto with kernel `FibV` (which contains the fibre half of `perTanId t`).
* **The free scaling variable is `S_k = W_k` on active, `V_k` on inactive blocks**, the same as the
  coefficient of the fibre coordinate under fibre translation (`T₁ ↦ T₁ + wW`, `T₃ ↦ T₃ + wV`). So
  `sepA` works at *every* point of `H⁰` (no genericity): where some `S_k = 0` the product `∏ S_k`
  kills the identity, elsewhere the fibre parameters are reparametrised (`σ′ = λ(τ + σ S)`) and the
  scalings separated (`coeff_sep`). Primality of `vanish H⁰` and one point with all `S_k = 1`
  (`exists_sv_point`, a generic `exp(u)`) remove `∏ S_k`.
* **Constant.** The block-degree budget `tD₂` is split between base/scaling and fibre (`n = ⌊tD₂/2⌋`),
  so the `E^♮` factor is `(⌊tD₂/2⌋ + 1)^{t₂+m}` instead of the abelian `(tD₂+1)^{…}`: a loss
  `≤ 2^{t₂+m}` in the constant, not in the degree.
* The linear part uses `L0V = π₀(Γ) × T_{lsat U₀}`, `U₀ = qspan Λ(HL H⁰)` (torus points come from the
  linear subgroup of `H⁰`, `HL_eq_prodSet`); `d₁ − dim U₀ = t₁` by `lieAlg_comap_torIncl` for `H⁰`.

Still open in the subgroup layer: nothing (G1–G4 done). Remaining for the assembly: the `ℚ̄`-rationality
of `Γ` (§7 rationality repair) and the push-out bookkeeping (`tan_push`, §6.3).

## 9. Chain gaps (§3.3) and the Wüstholz layer for `E^♮` (2026-10-31, chain/Wüstholz agent)

All items of §3.3 and the Wüstholz layer (VECEXT §4 "Wüstholz") are proved. New files (namespace `LSG.MEV`; no
`sorry`/`axiom`/`native_decide`; every listed theorem has `#print axioms` = `[propext, Classical.choice, Quot.sound]`;
not imported by `LSG.lean`). Build: `lake build LSG.MEV.HomPhOp LSG.MEV.RelChain LSG.MEV.WustTrans`
(`WustTrans` imports `HomWords`, `HomDeriv`, `WustPair`, `WustCoset`). Generic pieces are reused by import:
`LSG.ME.glue`, `wustholzM'`, `glued_mem_VOg`, `DL_glued_mem`, `VOg` (`LSG.ME.WustAlg`, `LSG.ME.Order`),
`LSG.ME.hfun_inter_ge` (`LSG.ME.WustCoset`), `StrongSix.M2.exists_biorth`, `exists_c0'`.

| file | lines | content |
|---|---|---|
| `HomPhOp.lean` | 232 | `isWH_aeval_mul`, **`isHomV_transl`**, `CW` (coefficientwise homogeneity), `CW_aeval`, `CW_nlaw`, **`isHomV_phOp`** |
| `RelChain.lean` | 198 | `relI`, `le_relI`, `relI_mono`, `relI_le_vanish_zero`, **`exists_flat_rel`**, **`exists_relevant_prime`**, **`component_rel`**, **`zeros_transl_subset`** |
| `HomDeriv.lean` | 364 | `Lcv`, `Lov`, `facV`, `dvh`, **`Dhc ch w`** (homogenised chart derivation, charts `Fin m → Fin 2`, directions `LieV`), `Dhc_add/smul`, **`isHomV_Dhc`**, `isHomV_DLc`, `eval_coords_isHomV`, **`Dhc_IG`**, `DLc_IG`, `psiB`, **`cc_blk`**, `aeV`, `chg_varV`, **`chgV`** |
| `HomWords.lean` | 256 | `chartIdeal`, `map_chartIdeal`, `Dhc_sub_Dv_mem`, **`DL_Dhc_sub_DL_Dv`**, `eval_DL_Dhc_chartsV`, `DL_eq_DLV`, **`vanCan_of_ordGtV`**, `satV`, **`Dhc_mem_VOV_chart`**, `DmixV`, `WmixV`, `DLmix_mem_VOV`, **`mem_VOg_mixV`**, `IG_le_VOg_mixV` |
| `WustPair.lean` | 317 | `toTan`, `lieAlgL`, `coords_zero_eq_FV`, **`eval_Dv_zero`**, **`Dhc_V_eq_Dh`** (merge with `ChartDerivV.Dh`), `const_sclV_ZG`, **`coeff_one_sclV_ZG`**, `transl_mem_vanish_gtransl`, **`mem_lieAlgL_of_ker`**, `eval_Dv_zero_of_mem`, `pairV` |
| `WustTrans.lean` | 247 | `exists_dual`, **`exists_dirs`**, **`exists_coset_data`**, **`exists_transversalsV`**, **`wustholz_cosetsV`** |
| `WustCoset.lean` | 129 | `vanish_unionV`, `mem_vanish_biUnionV`, `exists_sep_projV`, `not_gtransl_subsetV`, **`hfun_sum_cosets_geV`**, **`hfun_cosets_ge_projV`**, **`hfun_cosets_ge_subgroupV`** |
| **total** | **1743** | |

### 9.1 Statements (exact text in the files)
* `isHomV_phOp g w c c' κ (hQ : IsHomV Q d) : IsHomV (phOp Ls g w c c' κ Q) (fun k => 3 * d k)` (every `κ`);
  `isHomV_transl (hQ : IsHomV Q d) v c : IsHomV (τ Ls v c Q) (fun k => 3 * d k)`.
* `exists_flat_rel D hD (hP : IsHomV P d) (hS : 0 ∈ S) (hPI : P ∉ I_G̃)
  (hlast : Lr2 Ls W S P T (d₀ + d₁ + 2 * m) ≤ vanish {0}) :
  ∃ r < d₀ + d₁ + 2 * m, hdim (relI Ls (Lr2 … (r + 1))) = hdim (relI Ls (Lr2 … r))`; `exists_relevant_prime`,
  `component_rel`, `zeros_transl_subset`: verbatim analogues of `LSG.ME.MainAbChain` (`relI Ls L = vanish (zeros L)`).
* `Dhc Ls ch w = mkDerivation (v ↦ facV ch v · dvV Ls ch w v)`, `facV = ∏ₖ L_k²` on linear variables and
  `∏_{k' ≠ k} L_{k'}²` on block `k`, `L_k = X_{e k (bi (ch k))}`.
  `isHomV_Dhc : IsHomV x d → IsHomV (Dhc Ls ch w x) (fun k => d k + 2)`.
* `chgV ch₀ ch w (hx : IsHomV x d) : Lcv ch₀ · Dhc ch w x − Lcv ch · Dhc ch₀ w x − Σₖ aeV ch₀ ch w k · (d k • x) ∈ I_G̃`.
* `mem_VOg_mixV W (hx : IsHomV x d) (hv : ∀ g ∈ E, OrdGt Ls W x n g) : x ∈ VOg (DmixV Ls) (WmixV W) (vanish E) n`
  (analogue of `LSG.ME.mem_VOg_mix`; `DmixV (ch, w) = Dhc ch w`, `WmixV W = {p | p.2 ∈ W}`).
* `mem_lieAlgL_of_ker hH hc a (hw : ∀ P ∈ vanish (gtransl a (H0 Ls hH)),
  eval (coords a 1) (Dv Ls (chartsV a) w P) = 0) : w ∈ lieAlgL Ls hH`
  (`lieAlgL hH = (lieAlg Ls hH).comap toTan`), for **every** `a`.
* `exists_transversalsV hH hc W R (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a − b ∉ H0 Ls hH) : ∃ w B Q M,
  (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish E) ∧
  (∀ i j, (Σ_{a ∈ R} B a • Dhc Ls (chartsV a) (w i)) (Q j) − δᵢⱼ M ∈ vanish E) ∧ (∀ x, M x ∈ vanish E → x ∈ vanish E)`,
  `E = ⋃_{a ∈ R} gtransl a (H0 Ls hH)`, `w : Fin ℓ → LieV`, `ℓ = finrank W − finrank (W ⊓ lieAlgL Ls hH)`.
* `wustholz_cosetsV hH hc W R hdist D hD : ∃ c0, ∀ A S0 k, ℓ * k ≤ S0 →
  A ≤ VOg (DmixV Ls) (WmixV W) (vanish E) S0 → ∀ t, (k+1)^ℓ · hfun blk D ℂ (vanish E) t ≤ hfun blk D ℂ A (t + S0 * c0)`.
* `hfun_cosets_ge_projV D hD (hV : IsZClosed V) (hp : (vanish V).IsPrime) R hdist : ∃ c, ∀ t,
  R.card · hfun (vanish V) t ≤ 8^m · hfun (vanish (⋃_{a ∈ R} gtransl a V)) (3t + c)`; `hfun_cosets_ge_subgroupV`
  (`a − b ∉ V` form). (`LSG.MEV.hfun_cosets_ge` is the slice agent's sliced version in `SliceCoset.lean`.)

### 9.2 Design findings and corrections
* **Homogenisation with squared chart forms.** `Dv ch w` has degree `+2` on block variables and `0` on linear ones,
  so the factors are `L_k²`. `isHomV_Dhc` is exact (`IsHomV`), consistent with the `sclV`/`IsHomV` design.
* **The chart change is polynomial** although the cone over `X` is not normal (it is singular along
  `U = V = W = 0`): `W² dvalB_V − V² dvalB_W − ψ · P ∈ (F, G)` with `ψ = s V W (g₂ W² − 12 U²)` and explicit
  cofactors (`cc_blk`, found with `sympy`): `−3VWs·F` (`U`), `0` (`V`, `W`), `(g₂W³ − 12U²W)s·G − 6UWs·F` (`T₁`),
  `(12U²V − g₂VW²)s·G + 6UVs·F` (`T₃`).
* **Canonical homogenised words equal plain words at the normalised point, without homogeneity.** `Dv ch w` and
  `Dhc ch w` kill their own chart forms exactly (`dvalB_bi`: normalised flows keep `L = 1`), so both preserve
  `chartIdeal ch = (L_k − 1)_k` and agree modulo it; hence every word agrees modulo `chartIdeal`
  (`DL_Dhc_sub_DL_Dv`), and `chartIdeal (chartsV g)` vanishes at `coords g 1`. Combined with `words_of_ordGt` and
  homogeneity of `Dhc`-words this gives `vanCan_of_ordGtV`; no commutator identity is needed. (§3.3 estimated
  ≈ 300 lines for this item; with the chart change it is ≈ 600.)
* **No transport by translation identities.** Instead of the abelian `transport` (`tr_id` for derivations), the
  transversal data are built at each coset `a + H⁰` directly. The pairing
  `π_a(w, P) = (Dv_{chartsV a} w P)(coords a 1)` has left kernel in `lieAlg H` for every `a`
  (`mem_lieAlgL_of_ker`). Proof: for `Q ∈ I(H⁰)` the formal identity `transl_phPt_eq` (associativity, chain layer)
  gives `(τ_{−a} Q)(sclV u′ (ZG a w)) = Q(sclV u (ZG 0 w))`; taking `[z¹]` (`coeff_one_sclV_ZG`; the `U′(0)`-terms
  are block-Euler terms, `euler_eq_zero`) yields `π_a(w, scl u′(0) τ_{−a}Q) = π_0(w, scl u(0) Q)`, and `π_0` is the
  subgroup layer's pairing (`eval_Dv_zero`), so `TZ_eq_lieAlg` + `lieAlg_H0` conclude. The directions `w₁..w_ℓ` are
  chosen once (`exists_dirs`, biorthogonal at the identity), the dual polynomials at each coset by linear algebra
  (`exists_dual`), then adjugate (`exists_coset_data`) and `glue`. No homogeneous lifts (`exists_hom_lift`) are
  needed.
* **Charts at cosets.** The chart at `a + H⁰` is `chartsV a` (`V` at `O`, `W` elsewhere), so the `2`-torsion
  degeneracy of the `V`-chart `D̂` (`DV_eq_zero_of_V`) does not occur; `Lcv (chartsV a)` is `1` at `coords a 1`.
* **Merge.** `Dhc_V_eq_Dh : Dhc Ls (fun _ => 0) w = Dh Ls (toTan w)`: the subgroup layer's `D̂` is exactly the
  `V`-chart homogenised chain derivation (`bField a b = dvalB 0 (a/2) b`).

### 9.3 Interface for the assembly / still open
* Roy's `A` (generators `τ_v^c (phOp σ w c₁ c₂ κ P)`, `P` homogeneous) satisfies
  `A ≤ VOg (DmixV Ls) (WmixV W) (vanish SG) T` from `hAVO2` + `isHomV_transl (isHomV_phOp …)` + `mem_VOg_mixV` +
  `IG_le_VOg_mixV`, exactly as in `MainAb` step 2; then `wustholz_cosetsV` with `R`, `hdist` from
  `finite_cosets_H0` and `exists_reps_GV` (slice agent).
* `ℓ` is stated with `lieAlgL = (lieAlg).comap toTan`; `toTan : LieV → TanG` is a linear bijection (not packaged as
  a `LinearEquiv`; one line if needed for `finrank` transport).
* Not done here (other layers): the **sliced** Wüstholz (`wustholz_cosets_sl` analogue on `sl α I(E)`, `sl α A`),
  whose abelian proof only adds slice bookkeeping on top of `wustholz_cosets`; the push-out bookkeeping; `MainVec`.

## 10. `MultEstVec` assembly (2026-10-31, assembly agent) — statement finding and status

### 10.1 Statement finding: `MultEstVec` for non-onto `M` is a refined (4-block) estimate [Design]
`MultEstVec` (`MultEstStmtV.lean`) grades the `r` trailing additive coordinates with `D₂` (`TrailDeg`,
right side `D₀^{d₀} D₂^{2m+r}`, `t0`/`t2` with `prLead`). Every MEV layer is graded with the 3-block
function `blk` (`.x` = **all** `d₀ + r` additive coordinates, `.yz`, `.e k`): `hfun_slIGV_le`/`hdata_slIGV`
(degree `D_x^{d₀+r}`), `hfun_H0_geV` (exponent `t̃₀ = dim prA T̃′` over all additive coordinates, from
StrongSix's 2-block `hfun_prodSet_ge`), `hfun_le_transl`, `wustholz_cosetsV`, the slice layer.
* **Onto `M`** (`Function.Surjective M.mulVec`; includes `r = 0`): the layers suffice. The 3-block
  estimate on `G̃_r` gives `T^c |F| D₀^{t̃₀} D₁^{t₁} D₂^{t̃₂} ≤ C D₀^{d₀+r} D₁^{d₁} D₂^{2m}`; with
  `K_M ⊆ T̃′` and `M` onto, `prA T̃′ = prLead T̃′ × ℂ^r` and `T̃′ ∩ ker prLead ∩ ker prB ↠ ℂ^r` with kernel
  `T̃′ ∩ ker prA ∩ ker prB`, so `t̃₀ = t0 + r`, `t̃₂ = t2 − r`, which is exactly the `MultEstVec` inequality
  (multiply by `D₂^r`, cancel `D₀^r`). `TrailDeg` is not even needed.
* **Non-onto `M`** (in `Theorem41VecLA`: `r = 1`, `M = 0`): `G = G_a^{d₀} × G_a × G_m^{d₁} × E^m` with the
  extra `G_a` in degree `D₂`. The 3-block estimate only gives `D₀^{d₀+1}` on the right; no reduction to the
  onto case was found (`E₁^♮ × E₂ × ⋯` is not `E^m × G_a`, and `K_M`-invariant polynomials do not transfer).
  Proving it needs a second additive block in: `hfun_slIGV_le`/`hdata_slIGV`, `hfun_H0_geV` (and a 3-block
  version of StrongSix's linear `hfun_prodSet_ge`, which cannot be edited), `hfun_le_transl`,
  `hfun_le_sl`/`hfun_le_of_hom`, `wustholz_cosetsV`, `hfun_cosets_ge`, `hdim_vanishP_add_le`
  (est. 1.5–2.5k lines of re-proofs with a new block type).
* **Needed change (one of)**: (A) add `Function.Surjective M.mulVec` (or `M.rank = r`) to `MultEstVec`
  (minimal; the §7 consumer then needs another route for `r = 1, M = 0`); or (B) keep `MultEstVec` and
  budget the 4-block layer re-proofs above. **The statement file was not changed.** What is proved instead
  is the onto case, `multEstVec_of_surj` (status below).

### 10.2 Status: done (sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`)
Build: `lake build LSG.MEV.MainVecLe` (imports everything below). Not imported by `LSG.lean`.

| file | lines | content |
|---|---|---|
| `SliceWustV.lean` | 314 | `LslV`, `lpowV`, `exists_hom_slV`, **`nzd_slV`**, `EulV`, `EulV_mem_vanish`, **`EulV_Dhc`** (`[Eul_k, Dhc] = 2 Dhc`), `eul2_mem_VOg`, `DslV`, **`wustholz_sl_of_dataV`** |
| `SliceWustVCoset.lean` | 330 | `compV_mem_vanish` (multigraded components stay in `I(E)`), `isWH_det`, `lchV`/`eval_Dhc_mul_sub_one` (homogenisation by the chart forms of `a`), **`exists_coset_data_hom`**, **`exists_transversals_slV`**, **`wustholz_cosets_slV`** |
| `MainVecInv.lean` | 237 | `vtr`, `vsub`, `coords_add_vtr`, `aeval_vsub_phPt` (vector translations = linear substitution, also on `phPt`, via `NLaw_fib_left`), **`ordGt_add_vtr`**, `zeros_Lr2_add`, **`le_lieAlg_stabG`** (finite-orbit + divisibility argument) |
| `MainVecAux.lean` | 207 | `biUnion_gtransl_coverV`, `Zs_subset_translV`, `hfun_cosets_ge_c`, `lower_deg3`, `CstV`, `final_arith_v` |
| `MainVec.lean` | 362 | `ex0/ex1/ex2`, **`multEstG`** (3-block estimate on `G̃`, with a subspace `Kv` of symmetries ⇒ `Kv ⊆ lieAlg H`) |
| `MainVecPush.lean` | 240 | `finrank_map_prA_eq`, `finrank_t2_eq`, `finrank_inf_lieAlgL`, **`MultEstVecSurj`**, **`multEstVec_of_surj`** |
| `MainVecLe.lean` | 272 | `exists_jV` (trailing defect `j`), **`MultEstVecLe`**, **`multEstVec_of_le`** (any `M`, `D₀ ≤ D₂`), **`MultEstVecGap`** (`M` not onto, `D₂ < D₀`), **`multEstVec_of_gap : MultEstVecGap → MultEstVec`** |

Statements: `multEstG Ls W S P T D₀ D₁ D₂ Kv … : ∃ H hH, IsZClosed H ∧ Kv ≤ lieAlg Ls hH ∧ lieAlg Ls hH ≠ ⊤ ∧ ∀ F ⊆ S,
(inequivalent mod H⁰) → T^{dim W − dim(W ⊓ lieAlgL)} |F| D₀^{ex0} D₁^{ex1} D₂^{ex2} ≤ CstV d₀ d₁ m · D₀^{d₀} D₁^{d₁} D₂^{2m}`.
`MultEstVecSurj` / `MultEstVecLe` / `MultEstVecGap` are `MultEstVec` with the extra hypothesis `Surjective M.mulVec`
/ `D₀ ≤ D₂` / (`¬ Surjective M.mulVec` and `D₂ < D₀`). Constant `C = CstV (d₀ + r) d₁ m`.
Design notes: the sliced Wüstholz multiplier is made multihomogeneous by homogenising the dual polynomials with the
chart forms of `a` (value `1` at `coords a 1`, so the first-order pairing is unchanged) — no `exists_hom_lift` needed;
`K_M ⊆ T̃′` comes from `K_M`-invariance of the chain zero sets plus `component_rel` (no topology). `TrailDeg` is unused.

### 10.3 Gap: `MultEstVecGap` (= `M` not onto, `D₂ < D₀`; in §7: `r = 1, M = 0`, where `D₀ ≫ D₂`)
`multEstG` (all `d₀ + r` additive coordinates in the block `.x`) loses `(D₀/D₂)^{r − j}`. Plan for a 4-block
(`lead x | trail x | yz | e k`) version `multEstG4`, with what transfers for free:
* **free**: every Hilbert *dimension* (hdim is grading-independent: StrongSix `hdim_add_height_eq` gives
  `hdim = card σ − height` for any `β, D`), so the chain, `exists_relevant_prime`, `component_rel`,
  `radical_sl`, `hdim_vanishP_cosets_le`, `hdim_H0` transfer by one lemma; Bézout, `wustholzM'`, `exists_c0'`,
  `deg_le_of_hfun'`, `lower_deg3` are generic in `β`; the transversal data of `exists_transversals_slV` are
  grading-free (only `exists_c0' blk4` changes).
* **cheap**: generators of Roy's `A` in `FLE blk4`: `τ_v` and `phOp` substitute `x ↦ x + const (+ series)`, so the
  trailing degree is non-increasing (`TrailDeg D₂ P ⇒ TrailDeg D₂ (τ (phOp P))`, ≈ 100 l.); lead degree ≤ total.
* **re-proofs with `blk4`** (copy + local changes): `hfun_slIGV_le`/`hdata_slIGV` (x-count splits into
  `(tD₀+1)^{d₀}(tD₂+1)^r`, ≈ 350 l.); `hfun_le_transl` (≈ 120), `hfun_le_of_hom` (≈ 90), `hfun_sum_cosets_P`
  (≈ 60); **the H⁰ lower bound** `hfun_H0_geV` with exponents `(t0 lead, t₁, t₂ incl. trailing)`: in the vector-part
  construction choose lead coordinates for `prLead Γ` (degree `D₀`) and trailing/fibre coordinates for
  `Γ ∩ ker prLead` (degree `D₂`); needs a 3-block copy of StrongSix's linear `hfun_prodSet_ge`
  (≈ 800–1000 l.). Then `multEstG4` = `multEstG` verbatim with `blk4`, and `MultEstVecGap` follows as in
  `multEstVec_of_surj` with `j` replaced by the exact trailing exponent (≈ 150 l.). Total ≈ 1.8–2.3k lines.
* `MultEstVec` itself needs **no change**.

### 10.4 `MultEstVecGap` done — **`MultEstVec` and `Theorem41VecLA` are proved** (2026-10-31, 4-block agent)
All of §10.3 is in Lean, sorry-free; every listed theorem has `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. Build: `lake build LSG.W88.MainVec` (imports everything below).
No committed file was edited; not imported by `LSG.lean`.

| file | lines | content |
|---|---|---|
| `MEV/Blk4.lean` | 306 | `Blk4` (`xl \| xt \| yz \| e k`), `blk4 a` (cutoff `a`: `x i` leading iff `i < a`), `D4f`, `b4to3`, **`fle4_of_fle`** (transfer from `blk`), **`hdim4_eq`** (hdim grading-free, via `hdim_add_height_eq`), `bmul4`/`tpl4`, `CF4`, **`phOp_mem_FLE4`**, `translVar_mem4`, **`transl_mem_FLE4`**, **`transl_gensR2_mem_FLE4`** (τ and phOp never raise lead/trail/yz degrees) |
| `MEV/Blk4SliceIG.lean` | 407 | **`hfun_slIGV_le4`** (copy of the standard-monomial count, `x`-factor `∏ᵢ (tD(blk4 a (x i)) + 1)`), `polIGV4`, **`hdata_slIGV4`** (`hdim = d₀+d₁+2m`, `deg ≤ n! ∏ᵢ D(xᵢ) (2D_yz)^{d₁} ∏ 6D_k²`) |
| `MEV/Blk4Hilb.lean` | 397 | `bdeg4_e_eq_weight`, `Dcut4`, `comp_mem_FLE4`, `lsl_mem_FLE4`, `tpl4_le`; copies with `blk4 ct`: **`hfun_le_of_hom4`**, **`hfun_le_transl4`**, `prod_three_le4`, **`hfun_sum_cosets_P4`**, `hfun_P_transl_ge_c4`, **`hfun_cosets_ge_c4`**, `wustholz_sl_of_dataV4`, **`wustholz_cosets_slV4`** |
| `MEV/Blk4Lin.lean` | 218 | `leadL` (= `funLeft castAdd`), `exists_lin_surj` (leading coordinates of `leadL h₀` + trailing coordinates of `h₀ ∩ ker leadL`, jointly onto on `h₀`), `prod_pow_mem4`, **`exists_lin_family4`** (3-block copy of StrongSix's `exists_indep_restr`: `(N₀/t₀+1)^{t₀}(N₂/j+1)^j(N₁/s+1)^s` monomials × torus characters, independent mod `I(h₀ × T_U)`; Dedekind) |
| `MEV/Blk4H0.lean` | 209 | **`hfun_H0_ge_gen4`** (copy of `hfun_H0_ge_genV` for any family `A` on the linear group), `h0V`, **`hfun_H0_geV4`** |
| `MEV/MainVec4Aux.lean` | 200 | `ex0L`, `ex2L`, **`exps4`** (`dim leadL h₀ = ex0L`, `ex2L = ex2 + j`, `ex0 = ex0L + j`), **`fle4_of_trail`**, `prod_blk4_x`, `CstV4`, **`final_arith4`** |
| `MEV/MainVec4.lean` | 378 | **`multEstG4`** |
| `MEV/MainVec4Gap.lean` | 82 | **`multEstVec_blk4 : MultEstVec`** (all `M`, all degrees), **`multEstVecGap : MultEstVecGap`** |
| `W88/MainVec.lean` | 29 | **`LSG.MEV.multEstVec : MultEstVec := multEstVec_of_gap multEstVecGap`**, **`LSG.W88.theorem41VecLA : LSG.W88.Vec.Theorem41VecLA := theorem41VecLA_of_ME multEstVec`** |
| **total** | **2226** | |

Statements (exact text in the files):
* `multEstG4 Ls W S P T D₀ D₁ D₂ Kv hS (hPh : IsHomV P (fun _ => D₂)) (hPD : P ∈ FLE ℂ (blk4 d₀) (D4f D₀ D₂ D₁ D₂)) hPI … hvan hK :
  ∃ H hH, IsZClosed H ∧ Kv ≤ lieAlg Ls hH ∧ lieAlg Ls hH ≠ ⊤ ∧ ∀ F ⊆ S, (inequivalent mod H⁰) →
  T^{dim W − dim(W ⊓ lieAlgL)} |F| D₀^{ex0L T′} D₁^{ex1 T′} D₂^{ex2L T′} ≤ CstV4 d₀ r d₁ m · D₀^{d₀} D₁^{d₁} D₂^{2m+r}`
  on `G̃_r` (`Var (d₀ + r) d₁ m`), `ex0L T = finrank (T.map prLead)`, `ex2L T = finrank (T ⊓ (ker prLead ⊓ ker prB))`.
* `hfun_H0_geV4 hH hc D₀ D₁ D₂ t : (tD₀/t₀+1)^{t₀} (tD₂/j+1)^j (tD₁/t₁+1)^{t₁} (⌊tD₂/2⌋+1)^{ex2 + m} ≤
  hfun (blk4 d₀) (D4f D₀ D₂ D₁ D₂) ℂ (vanish (H0 Ls hH)) t`, `t₀ = finrank (leadL h₀)`, `j = finrank (h₀ ⊓ ker leadL)`.

Design notes:
* **Only the degree steps change.** Steps 1–8 of `multEstG` (chain, relevant prime, symmetries, component step,
  `hdim (sl α A) ≤ dim T′`) are run verbatim in the 3-block grading; the dimension is moved to `blk4` by
  `hdim4_eq`. Exponent of `D₂` is `ex2L = ex2 + j` (`exps4`, from `exists_jV`), so the lower-bound polynomial is
  still `lin3` with `t₂ := ex2L`; `κ = t₀^{t₀} j^j t₁^{t₁} ≤ d₀^{d₀}(d₀+r)^{d₀+r}d₁^{d₁}`.
* **The generators' degrees** come from the 3-block lemmas by transfer (`fle4_of_fle`: `yz` and `E^♮` factors of
  `phSub`/`translVar`, the laws `lawPolyV`, `CF_nlaw`); only the `x` case is reproved (`X + const`). This is the
  "τ and phOp never raise trailing degree" lemma.
* **The linear lower bound** uses actual coordinates (`LSG.ME.exists_coord_surj` for `leadL h₀ ⊆ ℂ^{d₀}` and for
  `h₀ ∩ ker leadL`); the trailing indices are automatically `≥ d₀`. The `E^♮`-part of `hfun_H0_ge_genV` is reused
  unchanged (degrees transferred with `fle4_of_fle`).
* `multEstVec_blk4` proves `MultEstVec` for **all** `M` and degrees directly (`TrailDeg` is now used, via
  `fle4_of_trail`); `multEstVec_of_surj`/`multEstVec_of_le` are no longer needed but are kept (`multEstVec` is
  stated as requested, `multEstVec_of_gap multEstVecGap`).
