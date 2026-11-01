# STAGE A4 / agent γ: A-block certificates (`LSG/JacBlock/`, `scripts/jacblock/`)

Written 2026-10-31. No git state changed. Nothing added to `LSG.lean` / `Axioms.lean`. All theorems below print
`[propext, Classical.choice, Quot.sound]` (scratch audit; no `sorry`, `axiom`, `native_decide`, no `decide +kernel`
needed: every certificate is small enough for `ring` / `linear_combination`).

## 1. Task 1: `SurjFacts` discharged [Proved]

**Deliverable** `LSG/JacBlock/SurjFactsInst.lean`:
* `surjFactsOf (A : A1Facts) (hOnQ : A.OnQ = OnQ) (hlaw0 : A.law0 = lawPt 0) (hneg : A.negP = negP)
  (hW4 : A.W4 = W4G) (hW8 : A.W8 = W8G) : SurjFacts A` (`W4G j X i = W4n X j i / 4`, `W8G` likewise, i.e. A1's
  `W4C`, `W8C`);
* **`surjFacts : SurjFacts a1Facts`** (all five equalities `rfl`);
* `surjFactsMk … : SurjFacts (mkA1Facts …)`.

Field statements are exactly those of `LSG/JacAn4/SurjFacts.lean` (version of 17:02). Plug-in for `AbBlock.surj`:
`D.surjA surjFacts X hX ((onQ_iff_gens X).mpr ((gensMv_eval_iff X).mp hgens))`.

| field | Lean source | certificate |
|---|---|---|
| `affine_chart` | `Affine.affine_chartG` | `X_i − grantJ_i(p)` (`i = 1,4,5,8`), `chartR1J p`, `chartR0J p` ∈ `I_A + (X₀ − 1)`: homogenise, solve over the 12 generators, divide the rest by `X₀ − 1`; `linear_combination` |
| `anchor` | `Anchor.anchorG` | `2D₀ = (21α/2, −6α², 99α⁴/2, 53)` (exact Cantor in `ℚ(α)`, `anchor_calc.py`); `law0(grantJ m₂, negP P₀) = 54872 α⁴ · P₀` (9 coordinates, A1's law data, cofactors of `α⁵ − 2`); points `x = (s₁ ± δ)/2`, `δ² = 537α²/4`; `y_i ≠ 0` from `b₀² + s₁b₀b₁ + s₂b₁² = −1807/2`. Any `α` with `α⁵ = 2`; `special_hP₀` part via A1's `law0_P0_four` |
| `gensI`, `gensI_diff`, `gensI_iff` | `Gens.gensA`, `gensA_diff`, `onQ_iff_gens` | cubics `C₀ = 4X₀X₁X₂ + 4X₁X₃² − X₀X₅X₇ + 2X₀X₃X₈`, `C₁ = 2X₂³ − X₀²X₃ + 2X₁X₂X₃ − X₀X₅X₆`, `C₂ = 4X₂X₃² − X₀X₆X₇ + 2X₀²X₈` (span `I₃/(Q)₃`, weights 0, 2, 8; `find_cubics.py`); 27 identities `X_k C_j ∈ (Q)₄` |
| `tanC4/8`, `_cont`, `gensI_tan4/8` | `Tan4T`/`Tan8T` (tables), `Tan{4,8}_{0,1}`, `gens_tan4/8` | `D_{W_j} G_i = Σ_k t_{jik} G_k` as polynomial identities (all `X`); `fderiv_gensA` identifies formal partials with `fderiv` |
| `exit4` | `Exit.exit4G` | `X₄⁴ ∈ (Q) + (X₀, D₀³X₀)`: always `v = e₀`, `k = 3` |
| `exit8` | `Exit.exit8G` | `X₈⁵ ∈ (Q) + (X₀, D₀X₀, D₀²X₀, D₀³X₀, D₁³X₀)`: `v ∈ {e₀, e₁}` |

Extras: `exitWord_W4G_k`, `exitWord_W8G_k` (`k = 1,2,3`, all `v`): explicit polynomial forms of the exit words;
`exitWord_W{4,8}G_differentiable (hk : k ≤ 3)`.

`special_hP₀` was already done by A1 (`LSG/Jac/Special.lean`); not duplicated.

## 2. Task 2

**Reassigned by the coordinator to A1 (`LSG/Jac/B56*.lean`).** Done before the reassignment:
* **B6 [Proved]**, `LSG/JacBlock/Hilb.lean`: **`hilbA : M.IsHomogeneous 14 → M ∈ JA`**, with
  `JA = Ideal.span {Q | Q ∈ gensMv} ⊔ Ideal.span (range fun a => X (yA a))`, `yA = ![0, 4, 8]`. This is the `hilb`
  field verbatim with `hilb_y = yA` and `hilb_deg = 14`. Route: `X_v^{e_v} ∈ JA` for `e = (1,3,3,3,1,4,3,3,1)`
  (6 identities, `MvPolynomial.funext` + `ring`), then pigeonhole (`Σ (e_v − 1) = 13`) on monomials. `hilb_deg = 14`
  instead of 4 changes only the Hilbert constant (`hilb_deg` is a free field). **A1 does not need to redo B6.**
* `LSG/JacBlock/GensMv.lean`: `gensMv : List (MvPolynomial (Fin 9) ℂ)` (the 12 generators, built from
  `mon c l = C c · ∏ X_l`), `gensMv_get`, **`gensMv_eval_iff`** (`(∀ Q ∈ gensMv, eval x Q = 0) ↔ ∀ i, gensA i x = 0`),
  **`gensMv_hom`** (the `gens_hom` field).
* B5 exploration (untrusted, for A1): `F` = 6 of the 9 *quadrics* (sparse) works. For each of the 84 subsets,
  `((F):I_A)₃` has exactly one weight-homogeneous class outside `I_A` (`b5_modp.out`), with sparse exact
  representatives (2–10 terms; `b5_cover.py` → `b5_S.pkl`, `b5_cover.out`; e.g. `F = Q₀..Q₅`: `S = X₀(X₄X₆ − X₅²)`).
  With all 84, `X_v³ ∈ I_A + (S)` for `v ≠ 8` and `X₈⁴`; a greedy minimal set keeping these degrees has 57
  systems. Fewer systems with higher `e` was not finished (`b5_greedy.py`, stopped at reassignment). With sparse `F`
  and weight-homogeneous `S`, the (M) identities are small; `ring` may suffice instead of the P2 kernel format.
* A1's P2 "deep recursion": fixed (`set_option maxRecDepth 100000` in the regenerated `Cert/P2_*`, built 17:31).

## 3. Timings and memory (Windows, `lake env lean`, `scripts/jac/runwatch.ps1`)

Baseline (a file importing `LSG.JacBlock.Gens` and nothing else): 20 s, **3.15 GB** (Mathlib + `LSG.Jac` oleans).
| file | wall | peak |
|---|---|---|
| `Gens` | 33 s | 3.65 GB |
| `Tan4_0`, `Tan4_1` | 35 s each | 3.66, 3.68 GB |
| `Tan8_0`, `Tan8_1` | 42 s each | 3.98, 3.97 GB |
| `Anchor` | 28 s | 3.45 GB |
| `Affine`, `Exit`, `GensMv`, `Hilb`, `SurjFactsInst`, `Tan4/8T`, `Tan4/8` | 14–80 s (lake, parallel) | not measured; light |

No kernel-heavy checks. (An unsplit `Gens` with both tangency families peaked at 5.2 GB, hence the split.)
Cold build of `LSG/JacBlock` ≈ 2 min wall with lake's parallelism.

## 4. Files

`LSG/JacBlock/`: `Gens`, `Tan4T`, `Tan4_0`, `Tan4_1`, `Tan4`, `Tan8T`, `Tan8_0`, `Tan8_1`, `Tan8`, `Exit`, `Affine`,
`Anchor`, `SurjFactsInst`, `GensMv`, `Hilb`, `WMv` (generated), and hand-written `SurjFactsInst`, `Simple`, `LawMv`,
`ABlock`.
`scripts/jacblock/` (untrusted): `jb_common.py` (data, weight-blocked exact ideal membership), `find_cubics.py`,
`gen_gens.py` (→ Gens, Tan*), `gen_exit.py`, `anchor_calc.py` (→ `anchor.json`), `gen_affine_anchor.py`,
`gen_hilb.py` (→ GensMv, Hilb), `gen_wmv.py` (→ WMv), `sizes.py`, `exit_try.py`, `b6_try.py`, B5 exploration `b5_modp.py`, `b5_cover.py`,
`b5_pick.py`, `b5_greedy.py`, `b5_explore.py` (slow exact version, superseded).

## 5. A4.6: the A-block instance [Proved, B5 data as arguments]

`LSG/JacBlock/ABlock.lean`: **`aBlockOf (D : ThetaData G) lci_s lci_S lci_F lci_len lci_F_le lci_mem lci_cover :
LSG.MEB.AbBlock`**, for any base, any `G : GermRad a1Facts hp hx` and any `D`. The seven B5 arguments have exactly the
types of the frozen `lci_*` fields (with `gens = gensMv`, `N = 9`, `g = 2`); A1's B5 (`LSG/Jac/B56*`, not landed yet)
plugs in directly. `stdPkg : ThetaPkg` is a fixed choice of base/germ/`D` (from `exists_anchored_base`,
`exists_thetaData`).

A5 constraints, checked by `rfl` in the file: `.g = 2`, `.N = 9`, `.θ = D.thetaN`, `.per = kerE G`,
`.i₀ = (4 : Fin 9)` (a bare numeral `4 : Fin aBlock.N` does not elaborate; see STAGE_A4 §6.5).

| field | source |
|---|---|
| `gens`, `gens_hom` | `gensMv`, `gensMv_hom` (`GensMv.lean`) |
| `θ`, `θ_analytic`, `θ_ne`, `θ_model` | `D.thetaN`, `analyticAt_thetaN`, `thetaN_ne_zero`, `thetaN_onQ` + `onQ_iff_gens` + `gensMv_eval_iff` |
| `per`, `per_discrete`, `per_span` | `kerE G`, `W88.discreteTopology_kerE`, `per_span_kerE` (`latBasis ⊆ latt ≤ kerE`) |
| `θ_per`, `θ_ker` | `theta_per` (`expP_periodic_of_ker` + `expP_eq_thetaN`), `theta_ker` (laws: `θ w ∥ θ z ⇒ θ(w−z) ∥ θ 0`) |
| `surj` | `ThetaData.surjA surjFacts` |
| `nL`, `law`, `law_hom`, `law_eq`, `law_complete` | `9`, `law m k = spMv (Data.law k m)` (`LawMv.lean`: `eval_spMv`, `spMv_isWeightedHomogeneous` + A1's `law_deg`), `ThetaData.laws_eq`/`laws_complete` |
| `charts`, `chart_cover` | `{0, 4, 8}`, `quadA_cover` |
| `W`, `W_hom`, `W_chart`, `θ_flow` | `Wmv` (`WMv.lean`: `flowW`, `W4C`, `W8C`, speed 1), `theta_flow` (`theta_PF0`, `theta_PF4`, `theta_PF_of_rel` for chart 8 with `θ₈ ≠ 0` found via `surjA` at `(0,…,0,2,1)`; `PFAt.of_eventually_smul` from `θ` to `θ_N`) |
| `i₀`, `is`, `θ_i₀`, `coords_locInv` | `4`, `(1, 8)`, `theta_zero`, `coords_locInv` with `f' = germDerEquiv a1Facts` (quotient rule at `0` + chart-4 PF) |
| `simple` | `simple_kerE` (`Simple.lean`, below) |
| `hilb_y`, `hilb_deg`, `hilb` | `yA = (0,4,8)`, `14`, `hilbA` |
| `lci_*` | arguments |

**`Simple.lean`** (new proof, about 240 lines): `real_of_latt`: a complex ratio of two lattice points is rational.
`a_j = c_j α(ζ^{j+1})`; `P = β·α(X²) − β(X²)·α ∈ ℚ[X]` vanishes at `ζ`, hence at `ζ²` and `ζ⁴` (minimal polynomial
`Φ₅`, `cyclotomic_eq_minpoly_rat`). `α` has no primitive 5th root as a root (degree `< 4`), so `β = cα` at all four
roots, so `c = mₑ/nₑ`. Then `simple_latt` (a rational complex line would lie in `ℝ a`), and `simple_kerE` through
`isRatSub_iff_of_nsmul`.

Memory (runwatch): `ABlock` 22 s / 3.26 GB, `Simple` 22 s / 3.20 GB, `LawMv` 19 s / 3.13 GB, `WMv` 22 s / 3.25 GB
(baseline about 3.1 GB).

Audit: `aBlockOf`, `stdPkg`, `simple_kerE`, `coords_locInv`, `theta_flow`, `theta_ker` print
`[propext, Classical.choice, Quot.sound]`.

**Complete instance** (`LSG/JacBlock/ABlockInst.lean`, after A1's B5 landed in `LSG.Jac.B56`):
`aBlockD D := aBlockOf D 4 lciS lciF lciA_len lciA_F_le lciA_mem lciA_cover` (any `θ`-datum `D` over `a1Facts`), and
**`aBlock := aBlockD stdPkg.D`**. Both are audited: `[propext, Classical.choice, Quot.sound]`. The A5 constraints are
checked by `rfl` there (`.g = 2`, `.N = 9`, `.θ = D.thetaN`, `.per = kerE G`, `.i₀ = (4 : Fin 9)`). Build: 13 s.

## 6. A5.8 packages [Proved]

`LSG/JacBlock/Packages.lean`, `LSG/JacBlock/PackagesW88.lean` (all audited `[propext, Classical.choice, Quot.sound]`;
Packages 23 s / 3.25 GB):
* **`aBlockAnD D : AbBlockAn (aBlockD D)`**, `aBlockAn : AbBlockAn aBlock`, `aBlockAnF m` (constant family):
  `lat = latt` (`latt_le_kerE`, `isNsmulIn_latt_kerE`); `growth` from `thetaN_order2` (`c_W = max a 0 + max C 0`);
  `qp` with `κ_ω = facN ω 0`, `L_ω = Lf ω`, `c_Q = ‖Lext‖` (`thetaN_add`, `fac_affine`, `norm_facN`, `ext_agree`).
* **`aBlockTayD D K ι : AbBlockTay (aBlockD D) ι`** for every number field `K` (and `aBlockTay`): `ks_chart4F` at
  `z₀ = 0`; `θ(0) = a e₄`, so `normalize 4 θ(0)` has entries `0, 1` (`A = E = 1`); `c_B = 81·2·W4H/W4den = 1296`,
  `δ = W4den = 4`; `ratio_eq_normalize`: `θ_N(z)_l/θ_N(z)_4 = normalize 4 (θ z) l`.
* **`tayAll_aBlockW m : LSG.W88.TayAll (fun _ : Fin m => aBlock)`** (STAGE_A5 §6.1).

## 7. A6 bridge prep

### 7.1 `LSG/W88/MStarCopyAbVar.lean` [verbatim copy, checked]
lean_mstar HEAD **`9b8d03680726333fdf242a2ce955034ebe495a6d`** (2026-10-31 16:25). Copied: `HyperplaneKappaOn`
(Waldschmidt), `TorInj` (Gen/Frame), `thetaD`, `KspanD`, `IsAdaptedBasisD` (AbVar/Basis), `zetaN`, `thetaA`, `perAgen`,
`algA`, `gmA`, `Thm11KappaA` (AbVar/ThmA), `twistA`, `lamAK`, `gmAK`, `Thm11KappaAK` (AbVar/MGAK), with the source
`variable` contexts. Dependencies already in `MStarCopy`/`MStarCopyMX`/`MStarCopyMGn` (`GroupModel`, `Rational`,
`HyperplaneKappa`, `TF`, `tor1/2`, `qv`, `algF`, `lamGen`, `perGen`, `torSub`, `gmF`, `PsiG`, `gmF2`, `dotL`) were
re-compared with this HEAD: whitespace-normalised text identical for all 22.
Check: a scratch file in lean_mstar's root (`lake env lean`, deleted afterwards; lean_mstar `git status` clean)
re-declared the new definitions in a fresh namespace over lean_mstar's own dependencies and proved
`@Copy.X = @CM4E.….X := rfl` for all 14 definitions (`HyperplaneKappaOn`, `TorInj`, `thetaD`, `KspanD`, `zetaN`,
`thetaA`, `perAgen`, `algA`, `gmA`, `Thm11KappaA`, `twistA`, `lamAK`, `gmAK`, `Thm11KappaAK`), and
`IsAdaptedBasisD ↔` lean_mstar's (field-by-field, a structure is a new type).
Note: lean_mstar's `HyperplaneKappaOn` takes `good V` *before* `finrank V + 1 = …`; `LSG.W88.HyperplaneKappaOn`
(StatementAbVar) takes it after `G.Rational W`. Trivial reorder.

### 7.2 Plan: `gmA 5 2 κ P 0 b` / `gmAK …` ← lean_lsg's generic §5d over `fun _ : Fin r => aBlock`
Target theorems (file `LSG/W88/AbVarMStar.lean`, ≈ 0.5–0.8k), assuming A5′'s generic statement, written here as
`HKB r := HyperplaneKappaOnB (B := fun _ : Fin r => aBlock) (aBlockAnF r) TorInjB` (name to be fixed when
`AbVar5d*.lean` lands; it is §5d for `G_a^{d₀} × G_m^{d₁} × A^r` with `lam = LamB`, `per = span_ℚ PerL`,
`sub = SubgroupDataB.tan`):
* `thm11KappaA_of (h : ∀ d₀ d₁ r, HKB …) : MStarCopy.Thm11KappaA 5 2 ![1, 2] Pms 0` with
  `Pms s = (1 − ζ^{s+1}) B((s+1)/5, (s+1)/5)` (lean_mstar's instance), and the same for `Thm11KappaAK` with `LA` = slot
  tuples of logarithms of algebraic points (needs `LamB` to contain them: see the last bullet).

Steps, in the pattern of `hyperplaneKappa_of_iso` (V5dIso) + `hyperplaneKappaOn_spanLam` (StatementAbVar) +
`lam_ne_zero_of_abelian` (AbVarSub):
1. **The iso** `ιA : MEB.Tan 0 (8r) B ≃ₗ[ℂ] TF (Fin r × Fin 4) (Fin 2 × Fin r → ℂ)` (`Nat.totient 5 = 4`, `n = 4r`,
   `d₁ = 2n`): toric part by `torL`-type reindexing `Fin (2·(r·4)) ≃ (ι ⊕ ι)` (as `V5dMGnGen.torL`), `G_a` part empty,
   and on the `A`-part `q (s, j) = c_s⁻¹ · z_j s` with **`c_s = (−1)^s/5`**: lean_lsg's `perVec e s = cJ s ζ^{(s+1)e}`
   (`Rank4.perVec_eq`) and lean_mstar's periods are `ζ^{κ s e} P s` with `κ = (1, 2)`, `P s = 5(−1)^s cJ s`. The scaling is
   rational, so (i) algebraic vectors correspond (`algF (algA 2)` ↔ `AlgTanB`), and `perAgen (j, e) ↦ perVec e` in copy `j`.
2. **Dimensions**: `G.d₁ = 2·card ι = 8r = d₁`, `G.d₂ = finrank (Fin 2 × Fin r → ℂ) = 2r = Σ_k aBlock.g`.
3. **`lam`**: `gmA.lam = span_ℚ lamGen`; generators map into `LamB` (toric `tor_i x` with `e^x ∈ ℚ̄`: `G_m`-part; `qv q`,
   `q ∈ perAgen`: `A`-part `perVec e ∈ latt = (aBlockAn).lat`). Then `hyperplaneKappaOn_of_scale` (common
   denominators) reduces `lam = span_ℚ …` to the subgroup `LamB`.
4. **`per`**: `span_ℚ perGen ↦ span_ℚ PerL (latt)` (generators to generators), so `κ_G ≤ κ_B` (only strengthens (5.4)).
5. **`TorInj`**: for `V` with `TorInj gmA V`, `V' = ιA⁻¹ V` satisfies `TorInjB` since `span_ℚ Per_B` (A-parts in
   `kerE`) maps into `span_ℚ perGen`: `kerE ⊆ ℚ·latt` (`isNsmulIn_latt_kerE`, `span_perL`), and the toric parts agree.
6. **`sub`**: a nonzero `H : SubgroupDataB 0 (8r) B` gives `ιA(H.tan) = (torSub L).prod h` with
   `L = (K11.annQ H.U).map torLQ` (`V5dMGnGen.torus_eq`), `h = ιA(H.t)`; and `h = ⊥ ∨ ∃ x ∈ h, λ x ≠ 0` with
   `λ = dotL (thetaA 2 0 b)`: `λ(ιA z) = 5 Σ_j b_j z_j 0`, and `lam_ne_zero_of_abelian` (needs
   `IsAbelianTangentA t` = `IsRatSub (perAbL (fun _ => latt)) t`, from `t_rat` + `isRatSub_perAb_iff`, and
   `LinearIndependent ℚ (ζ^e b_j)` = `IsAdaptedBasisD.indep`, with `MStarCopy.zetaN 5 = JacAn.zetaN 5` by `rfl`).
   If `H.t = ⊥` but `H.tan ≠ ⊥`, the toric part is nonzero and `h = ⊥`: `gmF.sub` holds with `h = ⊥`.
7. **Hyperplane bookkeeping**: `finrank` transport and `Rational` transport exactly as in `hyperplaneKappa_of_iso`
   (lines 1–80 of its proof, with `TanV` replaced by `MEB.Tan`).
8. **`gmAK`** (frame `gmF2`, `sub = ⊥ ∨ ∃ x ∈ S, algF x ∧ PsiG … x ≠ 0`, `d₂ = finrank Q`, `μ = 0`,
   `θ = thetaD ζ 4 b`): `PsiG θ 0 λ x = (θᵀx₁, θᵀx₂ + λ(q))`. For `S = ιA(H.tan) ≠ ⊥`: an algebraic `x ∈ S` with
   `PsiG x ≠ 0` exists (toric part: a rational vector of `torSub L` with `θᵀ ≠ 0` by `ℚ`-independence of `θ`; `A` part:
   an algebraic lattice-spanned vector via step 6). Logarithms `twistA j e v`, `v ∈ insert P LA`: `v = P` gives
   `perVec` (step 3); for `v ∈ LA` (logarithms of algebraic points) lean_lsg's `LamB` currently allows only `latt`
   `A`-parts, so **`Thm11KappaAK` needs `LA ⊆ ℚ·latt`-type hypotheses or a `LamB` with algebraic-point logarithms**
   (the latter needs `A(ℚ̄)` algebraicity of `θ`, STAGE_A3 §9.2). `Thm11KappaA` (`LA = ∅` form) needs nothing extra.
Estimate: 0.5–0.8k for `Thm11KappaA`; `Thm11KappaAK` blocked on the `LamB` extension above.

## 8. A6: `LSG/W88/AbVarMStar.lean` [Proved for `Thm11KappaA`; `Thm11KappaAK` needs one CM lemma]

**`thm11KappaA5_of (h : HyperplaneKappaAbVar) : MStarCopy.Thm11KappaA 5 2 (fun s => s + 1) MStarCopy.perA5 0`**
(standard axioms; file 21 s / 3.28 GB). `MStarCopyAbVar` now also copies `betaG` (Fermat7) and `perA5` (ThmA l.352).
Checked from lean_mstar (scratch file, deleted, `git status` clean): all 16 copied definitions `rfl`-equal to the
originals, and the statements `Thm11KappaA 5 2 (·+1) perA5 0`, `Thm11KappaAK 5 2 (·+1) perA5 0 ∅` unfold to
lean_mstar's own.
* `hkOn_transport`: generic transport `LSG.W88.HyperplaneKappaOn G' good' → MStarCopy.HyperplaneKappaOn G good` along
  `ι : Vs ≃ₗ[ℂ] Vt` (algebraic vectors, `lam ⊆ ι(span_ℚ L)` with common denominators, `per`, `d₁ = d₁'`, `d₂ = d₂'`,
  nonzero `sub` members, `good`).
* `iotaA r : TanA 0 (2|ι|) r ≃ₗ[ℂ] TF ι (Fin 2 × Fin r → ℂ)`, `ι = Fin r × Fin φ(5)`; `A`-part `q (s, j) = 5(−1)^s z_j s`.
* **Period scaling verified** (`perA5_scale`): `ζ^{(s+1)e} perA5 s = 5(−1)^s · perVec e s`, i.e. `perA5 s = 5(−1)^s cJ s`
  (from `perVec_eq`, `cJ`, `betaG_eq`). `perVec_mem_latt`: `perVec e ∈ latt` for all `e`.
* `sub`: `ι(H.tan) = (torSub ((annQ U).map torAQ)).prod (t.map abA)` (`torusA_eq`, the `V5dMGnGen.torus_eq` proof),
  and `λ(abA z) = 5 Σ_j b_j z_j 0 ≠ 0` by `lam_ne_zero_of_abelian` (with `IsAdaptedBasisD.indep` reindexed along
  `φ(5) = 4`).
* `TorInj → TorInjA`: `ι(PerA) ⊆ span_ℚ perGen` (toric part as integer combinations of `tor1/2 i (2πi)`, `A`-part as
  integer combinations of the generators via `latt_repr'`).
No change to `StatementAbVar` was needed for `Thm11KappaA`.

**`Thm11KappaAK 5 2 (·+1) perA5 0 ∅`: not done; one missing lemma.** `gmAK`'s family is
`sub S := S = ⊥ ∨ ∃ x ∈ S, algF (algA 2) x ∧ PsiG θ 0 λ x ≠ 0` (frame `gmF2`): it needs an **algebraic** vector. Everything
else (`d₁`, `d₂ = finrank Q`, `lamAK` with `LA = ∅` = toric logs + `twistA j e P` = the `perAgen` generators, `per`,
`TorInj`) is the same as for `gmA`. For `S = ι(H.tan) ≠ ⊥`:
* torus part `≠ 0`: a rational `l ∈ L ∖ 0` gives `PsiG ((l₁, l₂), 0) = (θᵀl₁, θᵀl₂) ≠ 0` (`ℚ`-independence of `θ`). Fine.
* torus part `= 0`, `t ≠ 0`: needs **`∃ z ∈ t, AlgVecA z ∧ Σ_j b_j z_j 0 ≠ 0`** for a nonzero abelian tangent `t`.
  `IsAbelianTangentA` (lattice-spanned) does not obviously give this. It is the CM fact that `t` is defined over
  `ℚ̄` (equivalently, `t` is stable under the projection onto the `s = 0` eigen-coordinates: then `cJ₀⁻¹ P₀ w` is
  algebraic for a lattice point `w ∈ t` with `λ(w) ≠ 0`).
  - Proof sketch [Proof]: let `S(v) = (s₁v, …, s₄v)` (the four embeddings of the integer coefficients) and
    `X = S(A ⊗ ℚ(ζ))`, `A = ℚ`-span of the lattice points of `t`.
  - The complex structure of `t` gives `π₁₂ X ⊆ X`: for `v ∈ A ⊗ ℝ` take `v'` with `S₁₂ v' = i S₁₂ v`; then
    `S₃₄ v' = −i S₃₄ v`, and `S((v − iv')/2) = (S₁₂ v, 0)`.
  - The Galois twist `ζ ↦ ζ²` (blocks `k ↦ 2k`) turns this into `π₂₄ X ⊆ X`.
  - Hence `π₂ = π₁₂π₂₄` preserves `X`, and by conjugation so does `π₁`.
  - Estimate 0.4–0.7k (it needs "`ℂ`-span ∩ `K^n` = `K`-span" for `K = ℚ(ζ)` and the semilinear twist).
  - Alternative: add `t_qbar : t = span ℂ {z ∈ t | AlgVecA z}` to `SubgroupDataA` (sound: abelian subvarieties
    are defined over `ℚ̄`). This only moves the same lemma to whoever derives `HyperplaneKappaAbVar` from the ME.

### 8.1 Update (2026-10-31): the CM lemma and `Thm11KappaAK` [Proved]
* `LSG/W88/AbVarQbar.lean` (20 s / 3.27 GB): **`abTan_qbar`** / **`ratTangentsA : RatTangentsA`** (every abelian tangent
  of `A^r` is spanned by algebraic vectors: "abelian subvarieties of `A^r` are defined over `ℚ̄`", tangent form),
  `ratTangentsA_isRatSub` (`IsRatSub (latt^r)` form), **`exists_alg_lam_ne`**. Proof: `D₁, D₂` (multiplication by
  `ζ − ζ⁴`, `ζ² − ζ³` in the eigen-coordinates) preserve `latt`; `I = c D₁ + d D₂` with real `c, d`, `ℚ`-independent
  (`cd_indep`, via `1, ζ, ζ², ζ³` independent); `mem_of_split` (a `ℚ`-linear `λ : ℝ → ℚ` applied to period
  coordinates) gives `D₁t, D₂t ⊆ t`; `P₀ ∈ span_ℂ{D₁, D₂}`; a lattice point is `cJ₀ a₀ + cJ₁ a₁` with `a_s ∈ t`
  algebraic.
* `LSG/W88/AbVarQbarB.lean` (19 s / 3.21 GB): **`ratTangents_aBlock`** in the `IsRatSub (perAb (fun _ => aBlock))`
  form (`SubgroupDataB.t_rat`), for A5′'s `hratA` (STAGE_A5 §6.7, noted there).
* `LSG/W88/AbVarMStarK.lean` (21 s / 3.21 GB): **`thm11KappaAK5_of (h : HyperplaneKappaAbVar) :
  MStarCopy.Thm11KappaAK 5 2 (fun s => s + 1) MStarCopy.perA5 0 ∅`**. Its statement was `rfl`-checked against lean_mstar
  in the §8 scratch run.
All audited `[propext, Classical.choice, Quot.sound]`.
