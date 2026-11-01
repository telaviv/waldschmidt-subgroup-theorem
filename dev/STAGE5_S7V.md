# STAGE5_S7V: W88 §7 for the vector-extension class (`Theorem41VecLA` from `MultEstVec`)

Started 2026-10-31. Labels as in PLAN.md. Inputs: STAGE5_AUXV.md §3–4 (`prop61V_b`, `PsiV`, `fibF_eq_ellN`),
STAGE5_MEV.md (model `G̃`, `OrdGt`, `ExpV`, subgroup layer), STAGE3_S7.md (abelian §7, reused where generic).

## 0. Targets
* `LSG/MEV/MultEstStmtV.lean`: `ObstrDataV`, **`MultEstVec`**.
* `LSG/W88/Sec7V*.lean`: **`LSG.W88.theorem41VecLA_of_ME (hME : MultEstVec) : Theorem41VecLA`**
  (the name `theorem41VecLA_of` is taken in `LSG.W88.Vec`).

## 1. Design of `MultEstVec` [Design]
* **Model of the push-out.** `G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂ = ((E^m)^♮ × G_a^r)/{(0, v, −Mv)}`. So
  `G = G̃_r / K_M`, `G̃_r = G_a^{d₀+r} × G_m^{d₁} × ∏ E_k^♮` (the MEV model with `d₀ + r` additive
  coordinates, the last `r` being the vector part of `G₂`), `K_M = {(0, −Mv; 0; 0, v)}` (`kerK M`). This covers
  every `M` (also non-onto `M`, e.g. `M = 0`, where `G₂ = E^m × G_a` is **not** a quotient of `(E^m)^♮`).
* Polynomials on `G` = `K_M`-invariant polynomials on `G̃_r` (`InvarK`, stated on cone points).
* **Degrees (W88's multidegree).** The `r` trailing additive coordinates belong to `G₂`, so they carry the
  elliptic degree `D₂` (`TrailDeg`), and in the conclusion they count in the `D₂`-exponent:
  `t₀ = dim pr_{G_a^{d₀}} T̃′`, `t₂ = dim (T̃′ ∩ ker pr_{G_a^{d₀}} ∩ ker pr_{G_m})`, right side `D₂^{2m+r}`.
  For onto `M` this is equivalent to the plain MEV statement (all `x` in `D₀`): `K_M` projects onto the trailing
  coordinates, so `t̃₀ = t₀ + r`, `t̃₂ = t₂ − r`. For `M = 0` it is a genuinely refined (4-block) estimate.
* Obstruction `ObstrDataV`: a `SubgroupPreV` datum `S` of `G̃_r` (`U, t, Γ`, no rationality), the subgroup
  `grp = zcl (exp T̃′)`, `T̃′ = S.tan`, closed, Lie algebra `T̃′`, and `K_M ⊆ T̃′`. Inequivalence `g − g′ ∉ grp`.
* `Σ(n)` and order `n T` with `n = dim G̃_r = d₀ + r + d₁ + 2m`.

## 2. Bridge [Design → Lean]
* `liftT (a, b, z, s) = ((a, s), b, z, 0)`, `pushT (x, b, z, w) = (x_{<d₀}, b, z, x_{≥d₀} + Mw)`;
  `pushT ∘ liftT = id`, `ker pushT = K_M`.
* `PpolyV`: monomials with `fibF_i ↦ S_i = x_{d₀+i} Π_l W_l + Σ_j M_ij T₁^{(j)} Π_{l≠j} W_l`; evaluation at
  `ptV x = (a, s; e^b; e^{-b}; ellN(z_k, 0))` is `PsiV x` (`fibF_eq_ellN` with `W = 0`); `ptV x` is a cone
  representative of `exp(liftT x)`. Times `Π W_k` (degree `D + 1 ≥ 1`, `∉ I_G̃`).
* `ordGt_of_vanishAlongV`: via the definition of `OrdGt` (law translate of the formal exponential `ExpV`):
  (i) `ExpV` = Taylor series of the `V`-normalised analytic lift at the identity (`FVb`, `bField = dvalB 0`,
  uniqueness of formal flows); (ii) laws commute with Taylor series (`NLaw_map` on a generic polynomial);
  (iii) analytically the law value is a scalar multiple of `ellN` at `exp(y + c w)` (`NLaw_repV`,
  `NLaw_smul`), the scalar is analytic near `0`; (iv) homogeneity and `VanishAlong`.
* Counting: `exp⁻¹(grp) ⊆ span_ℚ(T̃′ + Ω̃)` (G_a/vector part via `HL = V × T_Λ`; torus via characters;
  base via `B = zcl exp(0 × 0 × t)` and the abelian finiteness `exists_abelianTangent_Htil`); grid as abelian.
* Rationality repair on `T′ = pushT T̃′ = Γ′ + U^⊥ + perTan t`: `Γ″ = span_ℂ` of the algebraic vectors of
  `Γ_full = T′ ∩ (vector group)`; `r ≤ 1` ⇒ fibre part unchanged ⇒ `δ₂″ = δ₂`; `LiftAlg` ⇒ `λ″ = λ`.
* Inequality: `log_count`/`core_ineq` reused verbatim (`m ↦ 2m + r`, `e = d₁ + 2(m + r) − κ`).

## 3. Status (2026-10-31): **DONE, conditional on `MultEstVec`** [Lean]

```
theorem LSG.W88.theorem41VecLA_of_ME (hME : LSG.MEV.MultEstVec) : LSG.W88.Vec.Theorem41VecLA
```
`#print axioms`: `[propext, Classical.choice, Quot.sound]`. No sorry/axiom/native_decide; warning-free under
`lake build LSG.W88.Sec7V` (style linters included). Not imported by `LSG.lean`.

| file | lines | content |
|---|---|---|
| `MEV/MultEstStmtV.lean` | 173 | `toLie`, `kvec`, `kerK`, `InvarK`, `TrailDeg`, `prLead`, `ObstrDataV` (`tan`, `Proper`, `t0`, `t2`), **`MultEstVec`** |
| `W88/Sec7VPoly.lean` | 562 | `liftT`, `pushT`, `ker_pushT`, `fibPoly`, `monoPolyV`, `PpolyV`, `WprodV`, `ptV`, **`eval_PpolyV`**, `ptV_eq_coords`, `isHomV_PpolyV`, `PpolyV_mem_FLE`, `trailDeg_PpolyV`, **`invarK_PpolyV`**, `PV_notMem_IG` |
| `W88/Sec7VTaylor.lean` | 363 | `bField_eq_dvalB`, **`tps_FVb_ray`** (`ExpBlock` = Taylor series of the analytic lift), `tps_law`, `exists_law_unit`, `eval_sclE`, `PhiV`, `tps_PhiV`, **`ordGt_of_vanishAlongV`** |
| `W88/Sec7VBase.lean` | 243 | **`lieAlg_zclB_eq`** (the transcendence count of `isAbelianTangent_map_piZ`, reproduced to export `lieAlg B = 0 × 0 × π_Z T′`) |
| `W88/Sec7VCount.lean` | 492 | `fst_mem_tanV`, `chr_eq_one_of_mem_grpV`, `Z0`, **`base_partV`**, **`htilV_le_span`**, `tanG`, **`htilG_le_span`**, `exists_inequiv_grid_gen` |
| `W88/Sec7VRat.lean` | 398 | `t0_eq`, `t2_eq`, `tau_eq`, `decomp_tanG`, `preG_tan`, `gamRat`, `dataRat`, `fib_mem_gamRat` (`r ≤ 1`), `mem_dataRat_of_lam` (`LiftAlg`), **`exists_subgroupDataV_rat`** |
| `W88/Sec7V.lean` | 411 | `gridPtsV`, `sig_gridPtsV`, `t2G_le`, `delta_pos`, **`theorem41VecLA_of_ME`** |

### 3.1 Notes
* The bridge `OrdGt ⇐ VanishAlong` uses the definition of `OrdGt` (law translates of `ExpV`), so no chart lift at
  the grid points is needed (2-torsion points are harmless): only the `V`-normalised lift at the identity
  (`FVb`, `SubgroupLiftV`) and `NLaw_repV`/`NLaw_smul`.
* Counting: the base part needs `lieAlg (zcl exp(0 × 0 × t)) = 0 × 0 × t`, which is internal to the proof of
  `isAbelianTangent_map_piZ`; `Sec7VBase.lean` reproduces that argument (≈ 190 lines). If `SubgroupAbV.lean`
  exports it later, `Sec7VBase` can be deleted.
* `MultEstVec` vs. the subgroup/assembly layer: `ObstrDataV` is what `exists_subgroupV`, `H0`, `lieAlg_H0` give
  for `grp = H⁰` (field `lie` from `mem_lieAlg` + `lieAlg_H0`), plus `ker_le` (`K_M ⊆ lieAlg(stab)`, from the
  `K_M`-invariance of the chain, STAGE5_MEV §4).

### 3.2 Gap / caveat for the assembly agent
* For **onto `M`** (incl. `r = 0`) the refined statement follows from the plain MEV statement on `G̃_r` (all `x` in
  the `D₀` block): `K_M ⊆ T̃′` projects onto the trailing coordinates, so `t̃₀ = t₀ + r`, `t̃₂ = t₂ − r` and the
  two inequalities coincide (not formalised). For **`M = 0`, `r = 1`** (`G₂ = E^m × G_a`, needed by the §5d
  engine when `ν = 0`) it is a genuine 4-block refinement (the trailing `G_a` in the `D₂` block); the plain
  estimate loses `(D₀/D₂)^{1−ε}` and does not suffice. Neither is proved; `MultEstVec` is the only hypothesis.
