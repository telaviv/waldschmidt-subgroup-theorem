# Referee report: the M2 statements (`A^♮`): `AbVarVStmt.lean`, `AbVarV5dHyp.lean`, `MultEstV`, and the lean_mstar bridge

Date: 2026-11-01.

**Scope.** Do the **statements** below say what they claim, and are they non-vacuous? The claim is W88 Thm 4.1
(pp. 385–386) and W88 §5d (5.4) (pp. 394–395) for G = G_a^{d₀} × G_m^{d₁} × Q, where Q is the push-out along an onto
algebraic M : ℂ^m → ℂ^r of (A_σ̄^♮)^m. Here A = Jac(y⁵ = x(1 − x)) (Lean model Y² = 4X⁵ + 1), and A_σ̄^♮ is the
G_a-extension of A whose class is the σ̄-eigenline (`[X³dX/Y] = −(1/5)[dx/y]`). The statements carry the stated
restrictions: TorInj, base A-parts in the lattice, r ≤ 1, M onto and algebraic. I did not check the proofs; Lean did.
Same format as `REVIEW_STATEMENT_ABVAR.md`, `REVIEW_STATEMENT_VEC.md` and `REVIEW_TORINJ.md`.

**Statements reviewed:**
* `LSG/W88/AbVarVStmt.lean`: `LamAV`, `AlgTanAV`, `RationalOverQbarAV`, `vecInclA`/`torInclA`/`g2InclA`, `fibreAV`,
  `perTanA`, `SubgroupDataAV` (`tan`, `δ0`, `δ1`, `δ`, `δ2`, `Proper`), `Concl41AV`, `Theorem41AbVarVPer`, `TayAllV`,
  `FibOK`, `PerTanFib`, `gmLsgAV`, `HyperplaneKappaAbVarV`.
* The objects they use:
  - `TanAV`, `etaB` (blockwise η), `PerAVg`/`PerAV`/`PerAVf` (`LSG/AuxFunAV/Mono.lean`);
  - `sPart` (`LemmaUFac.lean`), `TorInjAV` (`PropG.lean`), `VBlockAn` (`Package.lean`);
  - `VBlock`, `perV`, `perTanId`, `perBase` (`LSG/MEBV/Block.lean`, `Stmt.lean`).
* `LSG/W88/AbVarV5dHyp.lean`: `PerTanPiv`, `RatTangentsV`, `Thm41FamV`. Their instances are in
  `LSG/JacBlockV/PerTanFib{,2,3}.lean`.
* The aBlockV fibre data: `ThetaData.fibT`, `ellK`, `etaB` (`LSG/JacAnV/Fibre.lean`), `kQ` (`KAlg.lean`), and
  `etaB_perVec`, `etaB_perVec_nat'` (`FibrePeriod.lean`, `JacBlockV/EtaPer.lean`).
* The frozen core `LSG/MEBV/Stmt.lean` `MultEstV` (with `Geom.lean`).
* The bridge: `LSG/W88/AbVarMStarN.lean`, `AbVarMStarNK.lean`, `MStarCopyAbVarN.lean`, `MStarCopyAbVarNOn.lean`.

**Sources compared:**
* W88 pages in `schanuel/five_exp/ref/w88_pages/`, as read in `REVIEW_STATEMENT_VEC.md` §3 (Thm 4.1, δ…τ, (5.4)).
* lean_mstar at **4d36ee3** (HEAD; the working tree has only an unrelated untracked `DeadCode.lean`):
  - `CM4E/AbVar/ThmAn.lean`, `MGAK.lean` (section `MGAn`), `ThmA.lean` (`perA_poly`, `perA_inj`);
  - `CM4E/Gen/Frame.lean`, `Frame2.lean`, `FrameW.lean`, `CM4E/Waldschmidt.lean`;
  - lean_mstar `TRUST.md` (rows for `Thm11KappaAn`, `AnK`).
* `M2.md` §0–§2, §M2.4a, §M2.6–M2.8; `INTERFACE.md` (last section); `REVIEW_TORINJ.md`; `REVIEW_STATEMENT_ABVAR.md`.

Labels: [Proved] (a complete argument, here or in Lean), [Proof sketch], [Heuristic], [Lit].

## Verdict

**No FATAL or MAJOR issue in any Lean statement.**
* Every definition matches W88 for this G. `SubgroupDataAV` is exactly the family of connected algebraic subgroups, and
  the `FibOK` conjunct of `gmLsgAV.sub` is automatic for the instance (Lean, §6). The fibre periods are the
  second-kind periods `η̄([ζ^e]γ) = (3/5)ζ^{4e}P̄` (Lean).
* The copies are verbatim. lean_lsg's `Thm11KappaAnOn` is exactly the M2.md §1.6 narrowing. It is implied by lean_mstar's
  current `Thm11KappaAn` (Lean).
* **New in this review:** I proved M2.md §1.2's `perAn_inj` in a scratch file in Lean. I then re-ran all three
  lean_mstar consumers under the narrowed hypotheses:
  - `fourExpAt_An` via `frame_false_on`;
  - `transcendental_div_pi_of_thm11KappaAn` via `frameW_false` with `good = TorInj`;
  - `mgAn_K` via `frame2_false_K_on`.

  All three compile. So lean_mstar's frame hyperplanes are toric-injective [Proved, Lean]. Also
  `two_three_beta5' (thm11KappaAn5)` and `WuestholzB5` hold with standard axioms only, against unmodified lean_mstar
  4d36ee3 (§4).
* The caveats are about scope, status and documentation:
  - The final lean_lsg theorems target a narrowing that **lean_mstar has not adopted yet** (C2).
  - The paper claim must state the restrictions (C1).
  - Some docstrings omit restrictions (m1, m2), and some docs are stale (m3).

| Prop / definition | Verdict | Status in the repo |
|---|---|---|
| `TanAV`, `AlgTanAV`, `RationalOverQbarAV` (ℚ̄-structure) | CORRECT [Proof sketch for the fibre coordinate, §1] | — |
| `etaB` / `aBlockV.η`, `etaB_perVec_nat'` | CORRECT: −3 × the periods of `X³dX/Y`, i.e. the σ̄ second-kind periods | proved |
| `PerAV`, `PerAVf` | CORRECT: `PerAVf` = Ω(G), `PerAV` of finite index; index-insensitive uses (as M1 §1) | — |
| `LamAV` | CORRECT: logarithms of algebraic points with A-component 0 (fibre part free), a deliberate restriction (C1) | — |
| `SubgroupDataAV`, `tan`, `δ0`, `δ1`, `δ`, `δ2`, `Proper` | CORRECT: exactly the connected algebraic subgroups (§2) | — |
| `Concl41AV` | CORRECT (verbatim p. 386, d₂ = Σg_k + r) | — |
| `Theorem41AbVarVPer` | CORRECT WITH CAVEATS (C1; m2: a W88 instance only for algebraic M) | **proved** (`theorem41AbVarVPer`, for onto algebraic M, r ≤ 1, any `VBlock` family with `An`, `TayAllV`) |
| `FibOK` | CORRECT: "positive-dimensional abelian part ⇒ contains the fibre", not "every nonzero subgroup" | — |
| `PerTanFib` | CORRECT; true for `aBlockV` with adapted `b`, false for some other `M` (m2) | proved for the instance (`perTanFib_aBlockV_of_adapted`) |
| `gmLsgAV` | CORRECT (sound model; `sub` = the exact family for the instance) | — |
| `HyperplaneKappaAbVarV` | CORRECT WITH CAVEATS (C1, m1, m2) | **proved** for the instance (`hyperplaneKappaAbVarV_aBlockV`) |
| `PerTanPiv`, `RatTangentsV`, `Thm41FamV` | CORRECT: engine hypotheses, true for A_σ̄^♮, all discharged; they occur in no final statement | proved for the instance |
| `MultEstV` | CORRECT: a sensible (weakened-form) Philippon estimate; not vacuous (§3) | **proved** (`multEstV_holds`) |
| `MStarCopyAbVarN` / `MStarCopyAbVarNOn` copies | CORRECT: textually identical and Lean-equivalent to 4d36ee3 (§4) | — |
| `Thm11KappaAnOn`, `Thm11KappaAnKOn` | CORRECT: = M2.md §1.6; weaker than the current lean_mstar hypotheses (Lean) | not in lean_mstar yet (C2) |
| `thm11KappaAn5`, `thm11KappaAnK5 (LAn = ∅)` | CORRECT | **proved**, standard axioms |

## 1. Coordinates, ℚ̄-structure, fibre periods, `LamAV`, `PerAV`

**The block A_σ̄^♮** [Proved in Lean for the analytic facts; the identification is Lit, §5].
* Lean's lift is `(z, w) ↦ (θ_N(z), T(z, w))`, with `T_k = θ_k(z)(w + ℓ(z)) − ⅓∂₀θ_k(z)` (`fibT`).
  - `ℓ(z) = ⅓(K₀₀z₀ + K₁₀z₁)` uses the Lemma-K♮ constants `kK`. These constants may be transcendental.
  - `ℓ` is chosen so that `∂_jζ̄ = −℘_{j0}` holds exactly.
* The model is defined over ℚ:
  - the base quadrics and cubics, the Plücker quadrics `plk = −⅓W`, and the `pderiv`-laws `lawVV` all have rational
    coefficients;
  - so do the fibre flows `WT t j = ⅓ kQ (fc t) j 0` (`kQ`, `KAlg.lean`).
* **The ℚ̄-structure is right** [Proof sketch]. The invariant derivations act on the model by ℚ-polynomials:
  - `∂_w` acts as `T_c ↦ X_c`;
  - `∂_{z_j}` acts through `θ_flow` (rational `W`) and `T_flow` (rational `WT`).

  So the basis `(∂_{z₀}, ∂_{z₁}, ∂_w)` of Lie(A_σ̄^♮) is ℚ-rational, and the coordinates `(z, w)` are ℚ̄-rational,
  whatever the nature of `kK`. Together with M1's base coordinates (`REVIEW_STATEMENT_ABVAR.md` §1) and the push-out
  `s = Mw` with M algebraic (`REVIEW_STATEMENT_VEC.md` §1), `AlgTanAV` is the ℚ̄-structure of T_G.
* The identity is a ℚ̄-point. `θ(0) = origin9`, `T₄(0,0) = 0` (`fibT_four_origin`), and the other `T_l(0,0)` follow from
  the Plücker relations with rational `plk`.

**The fibre periods are the σ̄ second-kind periods** [Proved in Lean].
* `aBlockV.η = stdPkg.D.etaB` (definitional). `etaB_perVec_nat'` states `η̄(perVec e) = (3/5)ζ^{4e}P̄`, with
  `P̄ = (1 − ζ⁴)B(4/5, 4/5)` (lean_mstar's `perB5`; equal by `rfl`, scratch §4).
* With `period_omega3` (`∫_{γ_e} X³dX/Y = −ζ^{4e}P̄/5`), this says that η̄ is exactly −3 × the period map of
  `X³dX/Y`, with no ℂ-linear correction.
* `X ↦ ζX` multiplies `X³dX/Y` by ζ⁴ = σ̄(ζ), so the extension class is the σ̄-eigenline.
* It is non-split: `span_perV` (`aBlockVAn`, `perV3_linInd`) gives the anti-affine rank-3 period matrix of M2.md N6.
* `η` is additive on `kerE` (`η_add`), and `kerE ⊆ ℚ·latt`, so the values on `perVec e` determine it.
* Lean scratch `scratch_eta_ne`: `η̄(perVec 0) ≠ 0`. So `PerTanPiv` and `PerTanFib` are not trivially true via η = 0.

**`PerAV` vs Ω(G)** [Proved].
* `PerAVf = 0 × 2πiℤ^{d₁} × {(λ, Mη(λ)) : λ ∈ ∏ kerE}` is ker exp_G for the push-out, as in REVIEW_STATEMENT_VEC §1
  with E replaced by A_σ̄^♮.
* `PerAV` (λ ∈ ∏ latt) has finite index in it (`perAVf_nsmul`). Every use is index-insensitive:
  - `per` and `TorInjAV` use ℚ-spans, and `span_ℚ PerAV = span_ℚ PerAVf`;
  - κ: a `y ∈ Y ⊆ LamAV` has `z ∈ latt`, so `Y ∩ PerAVf = Y ∩ PerAV` exactly;
  - λ: if `y = t + ω` with `ω ∈ PerAVf`, then `Nω ∈ PerAV`.

**`LamAV`** [Proof sketch]. Its conditions are: `a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`, `z_k ∈ latt`, and
`s − Mη(z) ∈ ℚ̄^r` (`sPart`).
* For `z ∈ latt` one has `exp(0,0,z,s) = exp(0,0,0,s − Mη(z))`. This is a fibre point, which is algebraic iff
  `sPart ∈ ℚ̄^r`, because the fibre translation `T ↦ T + cX` is ℚ-rational. So `LamAV ⊆ Λ(G)`.
* The restriction is that **the A^m-component of every point is 0** (torsion after `span_ℚ`, as M1's C1).
* Unlike M1, the G₂-component may be a non-torsion point of the fibre `ker(Q → A^m) ≅ G_a^r`. Lean scratch
  `scratch_fibre_lam`: `(0,0,0,1) ∈ LamAV` already for d₀ = d₁ = 0.
* `sPart_add`/`sPart_neg` are applied only on periods, where η is additive. So the junk values of η off `per` never enter.

## 2. `SubgroupDataAV`, `FibOK`, `PerTanFib`: the subgroup family

**Completeness** [Proved, given standard facts]. Let G′ ⊆ G be a connected algebraic subgroup, over ℚ̄ as in W88.
* By Goursat, G′ = T_U × H. Here Hom(G_m, ·) and Hom(·, G_m) vanish against extensions of abelian varieties by vector
  groups.
* Let H ⊆ G_a^{d₀} × Q, and let B ⊆ A^m be the image of H. Then B is an abelian subvariety, with `t = T(B)` IsRatSub.
* H → B has connected kernel `H ∩ (G_a^{d₀} × fibre)`, with Lie algebra Γ, which is ℚ̄-rational.
* So π₁(H) → π₁(B) is onto: every λ ∈ t ∩ per lifts to a period of H. The fibre has no periods, so the only period of
  G over λ is (λ, Mη(λ)). Hence `perTanA M t ⊆ Lie H`.
* Next, `perTanA M t + Γ` projects onto t and contains Γ, so its dimension is at least dim t + dim Γ = dim H. Therefore
  **Lie H = Γ + perTanA M t**, the `SubgroupDataAV` form.

**Soundness** [Proved, given Lit]. Every datum `(U, t, Γ)` is the Lie algebra of T_U × (H₀ + Γ).
* H₀ is the image of the universal vector extension E(B) → G₂ given by the universal property.
* Lie E(B) is the ℂ-span of its periods (de Rham: H₁(B, ℂ) = H¹_dR(B)^∨). Its periods map to the periods (λ, η(λ)).
* So Lie H₀ = `perTanA M t`. H₀ is algebraic, connected, and defined over ℚ̄.

So `SubgroupDataAV` is exactly the family. The representation is not unique (Γ may or may not contain the vector part
of H₀). This is harmless, since every quantity depends only on `tan` (as REVIEW_STATEMENT_VEC §2).

**Codimensions** [Proved]. They are as in REVIEW_STATEMENT_VEC §2:
* δ₀ = d₀ − dim fst(Γ), because `torInclA` and `g2InclA` have first component 0;
* δ₁ = dim_ℚ U = d₁ − dim U^⊥;
* δ = codim, and δ₂ = δ − δ₀ − δ₁.

Every ℕ-subtraction is exact: `tan ⊆ fst Γ × U^⊥ × ℂ^{Σg+r}` gives δ ≥ δ₀ + δ₁. `Proper` ⇔ G′ ≠ G.

**`FibOK H := H.t ≠ ⊥ → fibre ⊆ H.tan`** is the right property. The literal claim "every nonzero subgroup contains the
fibre" is false: T_U and Γ ⊆ G_a^{d₀} are nonzero subgroups that need not contain it. The correct statement is that
every member with a positive-dimensional abelian part contains the fibre.
* For d₀ = 0 and r = 1, the Q-part of a member is therefore 0, the fibre, or B̃ ⊇ fibre (M2.md §2.1).
* **For the instance, `FibOK` is automatic**: `fibOK_of_perTanFib` together with `perTanFib_aBlockV_of_adapted`. The
  scratch lemma `scratch_sub_eq` proves the equivalence
  `(gmLsgAV d₀ d₁ (AnN5 r) (MN5 b)).sub S ↔ ∃ H, S = H.tan`.

  So the conjunct restricts nothing. `gmLsgAV.sub` is exactly the family, hence sound and complete.

**`PerTanFib B M`** says: for every rational t ≠ 0 and every x, `(0, x) ∈ perTanA M t`.
* For `aBlockV` with M = bᵀ and θ(j, e) = ζ^e b_j ℚ-independent, it is proved in Lean (`perTanFib_aBlockV`). The proof
  takes a ℤ[ζ]-combination of three twisted periods, which leaves `(0, κηw)` with κ = 2ζ³ − 1 − ζ ≠ 0. The F-independence
  of b then gives `M(ηw) ≠ 0`.
* This is the paper argument of M2.md §2.1 ("Σ_j b_j σ̄(m_j) ≠ 0 on S ∖ 0").
* It is not true for arbitrary M. If b has an F-linear relation, some nonzero B̃ has fibre image 0. See m2 for what that
  means for the generic Prop.

**The engine hypotheses** (`AbVarV5dHyp.lean`) [Proved for the instance in Lean; true for the genuine group by the CM
argument in the module docstring]:
* `PerTanPiv`: on a rational t with pivot e, `η(λ) = Aη(λ ∘ e)` with A algebraic, namely A = σ̄(α_{ki}) for the CM
  endomorphisms α_{ki} that define the graph.
* `RatTangentsV`: this is M1's `ratTangentsA`.
* `Thm41FamV`: derived from `theorem41AbVarVPer`.

None of them appears in a final statement. They are hypotheses of the engine lemma `hyperplaneKappaAbVarV_of`, all
discharged by `hyperplaneKappaAbVarV_aBlockV`. They do not make anything vacuous, because the fibre data are the
genuine nonzero second-kind periods (§1).

## 3. `Theorem41AbVarVPer`, `HyperplaneKappaAbVarV`, `MultEstV`

**`Theorem41AbVarVPer An M`** is `Theorem41VecLAOnto`'s shape (REVIEW_STATEMENT_VEC) with the following changes:
* `Tan → TanAV` and `Lam → LamAV`;
* d₂ = Σ_k g_k + r = dim G₂, which is maximal because M is onto;
* the premises are `TorInjAV M V` and (NR) `d₁ + 2d₀ + κ ≤ 2 dim V`, which is the documented weakening of
  `REVIEW_STATEMENT.md` M2.

The inequality `(λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ)` is verbatim p. 386, with the same casts as `Concl41`.
* The ℤ-subtractions cannot truncate.
* κ ≤ rk Ω = d₁ + 2Σg.

The Prop itself fixes an arbitrary M. The proved theorem `theorem41AbVarVPer` (`AbVarVSec7.lean`) needs:
* `Function.Surjective M.mulVec`, `AlgMat M` and `r ≤ 1`;
* the packages `An`, `TayAllV B`.

For non-algebraic M the coordinates `s = Mw` are not ℚ̄-rational, so the Prop is then not a W88 instance (m2). For the
proved cases it is a special case of W88 Thm 4.1 [Lit].

**`HyperplaneKappaAbVarV An M = ∀ d₀ d₁, HyperplaneKappaOnLsg (gmLsgAV d₀ d₁ An M) (TorInjAV M)`.**
* `gmLsgAV` has:
  - d₁, and d₂ = Σg + r;
  - `alg = AlgTanAV`, `lam = LamAV ⊆ Λ(G)`, `per = span_ℚ PerAV = ℚ ⊗ Ω(G)`;
  - `sub` = the family, for the instance (§2).
* `TorInjAV V`: no nonzero element of V ∩ ℚ ⊗ Ω(G₂) has zero toric part. This is REVIEW_TORINJ's `TorInj`, with `per`
  the full ℚ-period space, so REVIEW_TORINJ M1 is resolved again, via `perAVf_nsmul`.
* It is W88 §5d (5.4) for this G [p. 394, read with rk Y as in REVIEW_STATEMENT_VEC §3], restricted to:
  1. toric-injective V;
  2. A-components of the y_i in the lattice;
  3. r = 1 and M = bᵀ with b adapted.
* Each restriction only weakens the statement, so it is implied by W88 [Lit]. It is proved
  (`hyperplaneKappaAbVarV_aBlockV`, standard axioms).
* There is no (NR): under TorInj, κ ≤ d₁ (REVIEW_TORINJ §3(d)).

**`MultEstV` (frozen core) is a sensible multiplicity estimate** [Proved: well-formed and non-vacuous; [Lit] for the
Philippon comparison].
* The model is G = G̃_r/K_M with `G̃_r = G_a^{d₀+r} × G_m^{d₁} × ∏B_k^♮`. Polynomials on G are the `K_M`-invariant
  ones (`InvarKV`, on the exact lift).
* The constant C depends only on (d₀, r, d₁, m, B, M), uniformly in W, S, P, T, D. This is the correct quantifier order.
* Hypotheses on P: multihomogeneous of degree D₂ in every block, filtered degree (D₀, D₁, D₂), trailing degree ≤ D₂,
  `P ∉ IGsem`, and analytic order > nT along W on Σ(n).
  - The order is "at some lift". This is lift-independent: lifts differ by periods, which rescale every block by a
    nonzero entire factor (`lift_per`); the torus coordinates are periodic; and `InvarKV` covers K_M.
  - The consumer satisfies all the hypotheses jointly with `PWV` (`invarKV_PWV`, `PWV_notMem_IGsem`, `isHomV_PWV`,
    `PWV_mem_FLE`, `trailDeg_PWV`, `ordGtV_PWV`).
* Hypothesis weakenings, all in the safe direction:
  - n = dim G̃_r rather than dim G (the CR1 lesson). This is a larger n, so the hypothesis is stronger.
  - D₀^{t₀}D₁^{t₁}D₂^{t₂} lower-bounds Philippon's H(G′; D) term by term. So the conclusion is weaker than Philippon's.
  - t₂ counts K_M (dimension m), and dividing by D₂^m gives W88's D₂^{d₂}.
* **The conclusion cannot be met trivially.** `O.Proper` (`tan ≠ ⊤`) and the field
  `lie : (∀ c, exp(cv) ∈ grp) ↔ v ∈ tan` together forbid `grp` = everything. That would be the only way to make every F
  a singleton.
  - `grp_eq` ties `grp` to `zcl(exp tan)`, so a non-algebraic `tan` is excluded.
  - `htil` is W88's `exp⁻¹(G′) ⊆ ℚ ⊗ (T_{G′} + Ω)`.
  - A codimension-1 obstruction still forces T^c|F| ≲ D₂, which is the genuine content.
* `VBlock` is satisfiable (`aBlockV`, `pointVBlock`). Since `multEstV_holds` is a theorem, `MultEstV` is no longer an
  assumption. Through the chain of §4 it is load-bearing for a genuine transcendence statement [Heuristic: the ME is
  the only place in Waldschmidt's method where the obstruction subgroup appears].

## 4. The bridge, and the end-to-end check

**The copies** (`MStarCopyAbVarN.lean`: `perAngen`, `algAn`, `gmAn`, `Thm11KappaAn`, `perB5`; `MStarCopyAbVarNOn.lean`:
`twistAn`, `lamAnK`, `gmAnK`):
* They are **textually identical** to lean_mstar 4d36ee3 (`diff` of `ThmAn.lean` l. 41–58 and 210–211, and of
  `MGAK.lean` l. 301–317, is empty).
* They are also Lean-equivalent for **general** parameters (scratch §1):
  - `Thm11KappaAn ↔ MStarCopy.Thm11KappaAn`, both directions, repackaging `IsAdaptedBasisD`;
  - `Thm11KappaAnK → MStarCopy.HyperplaneKappa (MStarCopy.gmAnK …)`;
  - `perB5`, `perAngen` and `lamAnK` are equal by `rfl`.
* The variable contexts agree.

**The narrowing.** `MStarCopy.Thm11KappaAnOn` and `Thm11KappaAnKOn` are not copies, because lean_mstar has no such
definitions. In scratch §2 I defined the §1.6 bodies over lean_mstar's own definitions (`Thm11KappaAnOn'`,
`Thm11KappaAnKOn'`) and checked the following in Lean:
* **only a weakening**: `Thm11KappaAn → Thm11KappaAnOn'` and `Thm11KappaAnK → Thm11KappaAnKOn'`, by
  `fun r b hb => (h r b hb).on`;
* lean_lsg's `Thm11KappaAnOn` is equivalent to `Thm11KappaAnOn'` (both directions); `Thm11KappaAnKOn` implies
  `Thm11KappaAnKOn'`;
* the INTERFACE adapters `thm11KappaAn5_check` and `thm11KappaAnK5_check` typecheck.

**lean_mstar's frame hyperplanes are toric-injective** [Proved, Lean, scratch §3–4]. M2.md §1.2 asked for this on
paper; it is now in Lean.
* `perAn_poly'`: `q ∈ span_ℚ perAngen` has `q.1(s, j) = P_s f_j(ζ^{κ_s})` and `q.2 = P̄ Σ_j b_j f_j(ζ^{N−1})`, with the
  same `f_j ∈ ℚ[X]` in both.
* `perAn_inj'` (N ≥ 2, adapted b, `hκN`, P̄ ≠ 0): `snd` is injective on `span_ℚ perAngen`. The proof applies
  `perA_inj`'s reduction to `f_j ∘ X^{N−1}`. It then uses `cyclotomic_eq_minpoly_rat` for the primitive root ζ^{N−1}
  (gcd(N − 1, N) = 1) to get Φ_N | f_j.
* Re-runs of all three consumers, each with exactly the M2.md §1.6 edits:
  - `fourExpAt_An_on` (`frame_false_on` with `perAn_inj'`, where P̄ ≠ 0 comes from `hT`);
  - `transcendental_div_pi_on` (`frameW_false` with `good = TorInj`, `hgood = torInj_ker_phiW … perAn_inj'`);
  - `mgAn_K_on` (`frame2_false_K_on` with `hper0` from `perAn_inj'` and `snd_mem_span_perQ`).

  Each needs only the new premise `hκN`, which is `by decide` at N = 5, κ = (1, 2).
* The instance chain `wuestholzB5_on`, `fourExpAt_beta5_on`, `two_three_beta5_on` is lean_mstar's text with the
  hypothesis renamed.

**The transport** (`thm11KappaAn5`, `thm11KappaAnK5`, one `hkOn_transport` each) is sound in every component.
* ι is `(a, t, z, s) ↦ (torA t, (abA z, (5/3)s₀))`. The scalings `cA s = 5(−1)^s` and 5/3 are algebraic, so `halg`
  holds (`algN5`).
* `iotaN5_pvN5`: ι maps lean_lsg's period of `[ζ^e]γ` in copy j onto lean_mstar's generator (j, e), because
  `(5/3)·b_j(3/5)ζ^{4e}P̄ = b_jζ^{(5−1)e}P̄`.
* So `hper` gives `G.per ⊆ ι(span PerAV)`, hence κ_mstar ≤ κ_lsg, which is the safe direction. `hlam` holds for
  `lamGen` and for `lamAnK … ∅`.
* `hd2`: dim Q″ = 2r + 1 = Σg + 1.
* `hsub`, case `t ≠ ⊥`: `FibOK` puts the fibre in T_H.
* `hsub`, case `t = ⊥`: T_H has Q-part ⊆ fibre. For gmAnK, an algebraic Γ-vector or a rational toric vector with
  `PsiG ≠ 0` is used (M1's argument).
* `hgood`: ι(span_ℚ PerAVf) ⊆ lean_mstar's `span_ℚ perGen` (`iotaN5_spanPerAVf`), and "toric part = 0" is preserved.
  So lean_mstar's TorInj implies lean_lsg's TorInjAV, which is the safe direction.

**End-to-end output** (scratch run with `lake env lean` from lean_mstar's root, about 40 s; lean_mstar and LSG oleans
up to date, `lake build --no-build`):

```
'CM4E.AbVar.mgAn_K_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'CM4E.AbVar.thm11KappaAn5_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'CM4E.AbVar.thm11KappaAnK5_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'CM4E.AbVar.perAn_inj'' depends on axioms: [propext, Classical.choice, Quot.sound]
'CM4E.AbVar.scratch_wuestholzB5_M2' depends on axioms: [propext, Classical.choice, Quot.sound]
'CM4E.AbVar.scratch_two_three_M2' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.thm11KappaAn5' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.thm11KappaAnK5' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.MEBV.multEstV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.theorem41AbVarVPer' depends on axioms: [propext, Classical.choice, Quot.sound]
'LSG.W88.hyperplaneKappaAbVarV_aBlockV' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `scratch_two_three_M2 : ¬ (2^t ∈ ℚ̄ ∧ 3^t ∈ ℚ̄)` at t = B(1/5, 1/5) is `two_three_beta5_on thm11KappaAn5_check`.
* `scratch_wuestholzB5_M2 : Transcendental ℚ (perB5/π)` is Wüstholz's theorem.

## 5. What is identification, and what Lean proves

The final theorems `thm11KappaAn5`, `thm11KappaAnK5`, and lean_mstar's `two_three_beta5'` after adoption, are
statements about explicit numbers: ζ₅, `perA5`, and `perB5 = (1 − ζ⁴)B(4/5, 4/5)`. They depend on no modelling
identification, exactly as in REVIEW_STATEMENT_ABVAR §5. The identification matters only for the *name*: "W88 §5d for
G_a^{d₀} × G_m^{d₁} × ((A_σ̄^♮)^m pushed out along bᵀ)".

To M1's (I1)–(I4) it adds:
* **(I5)** [Lit]: the ℚ-model in ℙ¹¹ is a commutative group variety ℚ̄-isomorphic to A_σ̄^♮. The model consists of
  the Grant variety plus `T₀, T₄, T₈`, the Plücker quadrics and the 81 (3,3) laws, and Lean proves `lawV_eq`,
  `lawV_complete` and `surjV` off `{X = 0}`. A_σ̄^♮ is the G_a-extension of A with class `[X³dX/Y]`.
  - Lean proves the analytic content: the cocycle `fibT_add` with the same multiplier as θ_N, rational fibre flows,
    the η values, and anti-affineness (`span_perV`).
  - What is not formalised: the cone Nullstellensatz at `{X = 0}`, and "this group *is* the extension with that class"
    (the classical correspondence of extensions with periods of second-kind differentials).

## 6. Degenerate witnesses: none found

* **`FibOK` cannot hide anything.** For the instance it is automatic (`scratch_sub_eq`), so `sub` is exactly the family.
  It contains no non-algebraic subspaces: a generic hyperplane contains no nonzero rational torus, ℚ̄-rational vector
  subspace, or `perTanA t`.
* **TorInj is not unsatisfiable.** All three lean_mstar frame hyperplanes satisfy it, in Lean (§4).
* **The hypothesis is not trivially true.** It implies Wüstholz's P̄/π ∉ ℚ̄ and `two_three_beta5'` (§4).
* **`PerTanFib` and `PerTanPiv` are not trivial via η = 0**: η̄(perVec 0) ≠ 0 (`scratch_eta_ne`).
* **`MultEstV` cannot be satisfied by a trivial obstruction** (§3: `lie` together with `Proper`).
* **ℕ-subtraction.** The ℕ-subtractions in `SubgroupDataAV` are exact (§2). `Concl41AV` and `HyperplaneKappaOnLsg` cast
  to ℤ before subtracting.
* **Empty-type corners:**
  - **d₀ = d₁ = 0 (G = Q alone): not empty, unlike M1's m6.** `LamAV` contains non-torsion fibre points
    (`scratch_fibre_lam`), and the fibre direction is TorInj, since its ℚ-periods are 0. A rational V ∋ (0,0,0,1) with
    W = V meets (5.4) with rk Y = 1, and the conclusion is the fibre G_a. This is consistent.
  - r = 0: there is no push-out direction. `PerTanFib` is then vacuous in x, and `FibOK` holds trivially. This is
    outside the proved instance (M onto with r = 1).
  - m = 0: the adapted basis has r_mstar ≥ 1 (1 ∈ K), so m ≥ 1 in the instance.
* **Representation.** Non-unique Γ is harmless (§2).
* **The package parameter `An`.** The Props depend on `An` through `lat` only. For the instance `lat = latt`, of finite
  index in `kerE`. A smaller `lat` would only weaken the statement.

## Issues

**C1 — scope of the claim (MINOR for the Lean statements; it matters for every citation).** The proved §5d statement is
W88 (5.4) for G = G_a^{d₀} × G_m^{d₁} × Q, where Q is the push-out of (A_σ̄^♮)^m along bᵀ, under all of the following:
1. V toric-injective: V ∩ (ℚ ⊗ Ω(Q)) = 0;
2. the y_i have A^m-component 0, i.e. their abelian coordinates are periods. The G_a^{d₀}, G_m^{d₁} and *fibre*
   components are arbitrary algebraic. So Γ ⊆ G_a^{d₀}(ℚ̄) × G_m^{d₁}(ℚ̄) × (ker(Q → A^m))(ℚ̄), up to torsion;
3. a one-dimensional push-out (r = 1), M = bᵀ with b adapted (θ(j, e) = ζ^e b_j ℚ-independent). This is what makes
   `FibOK` hold.

The Thm 4.1 form holds for any VBlock family with packages, any onto algebraic M with r ≤ 1, under TorInj, the
lattice restriction on the base parts, and (NR).
* **Fix:** use the wording below. lean_mstar's TRUST row for MG♮-A must carry restrictions 1–2 when it adopts the
  narrowing, as M1's row does.

**C2 — status: the final theorems target a narrowing that lean_mstar has not adopted (MINOR; process).**
* `thm11KappaAn5 : MStarCopy.Thm11KappaAnOn …` is not yet lean_mstar's `Thm11KappaAn`. At 4d36ee3 that is still the
  unrestricted `HyperplaneKappa (gmAn …)`, which lean_lsg does not prove. So lean_mstar's `two_three_beta5'` is **not**
  unconditional today.
* The scratch file shows that adoption works: the three consumer edits compile, `perAn_inj` is about 50 lines, and the
  instances need `(by decide)` only.
* lean_mstar's TRUST.md currently says `Thm11KappaAnK` is "unchanged" (not narrowed). §1.6 narrows it too.
* **Fix:** land M2.md §1.6 in lean_mstar. The scratch §3–4 can serve as a template; it was not edited into lean_mstar
  here. Then do the following:
  - re-sync `MStarCopyAbVarNOn.lean` as verbatim copies. lean_mstar will probably redefine `Thm11KappaAn` itself, as
    M1 did, so the lean_lsg name `Thm11KappaAnOn` should become a copy of `Thm11KappaAn`;
  - re-run the `rfl` and adapter check.

  Until then, say "pending the lean_mstar narrowing" next to any M2 claim.

  *Post-review note (2026-11-05): closed. lean_mstar `8458732` landed the narrowing, the copies are re-synced, and the
  template `scripts/m2_lean_mstar_template/` was deleted as superseded by lean_mstar's `CM4E/Bridge/AbVar.lean`.*

**m1 — MINOR: docstrings omit restrictions.**
* `HyperplaneKappaAbVarV` ("The W88 §5d hypothesis for the vector-extension class (toric-injective hyperplanes)") and
  `hyperplaneKappaAbVarV_aBlockV` omit restriction 2 (`lam = LamAV`, base parts in `lat`). The module header has it.
* `Theorem41AbVarVPer`'s docstring omits it too.
* `HyperplaneKappaAbVarV` is called "hypothesis" although it is proved for the instance.
* **Fix:** add "with A^m-components of the logarithms in the period lattice (`LamAV`)".

**m2 — MINOR: the generic Props are W88 instances only under conditions that are not in the Prop.**
* `HyperplaneKappaAbVarV An M` for an M with `¬ PerTanFib B M` has a `sub` that is too small. For example, take b with
  an F-linear relation. Then a member with t ≠ 0 not containing the fibre is a genuine subgroup that `sub` excludes.
  W88 does not imply that form.
* `Theorem41AbVarVPer An M` for non-algebraic M uses the wrong ℚ̄-structure.
* Neither is a defect, because they are proved only under `PerTanFib`/`AlgMat` (resp. `AlgMat`, onto, r ≤ 1). But the
  docstrings present them as "W88 for the class".
* **Fix:** say "a W88 consequence when M is algebraic (and, for §5d, `PerTanFib B M`)".

**m3 — MINOR: stale documentation.**
* `README.md` l. 298–300 and `TRUST.md` §6 (row "other CM abelian-variety hypotheses (`AbVar.Thm11KappaAn`,
  `Thm11KappaAnK`, …) | — | not covered") predate M2.
* The README review list (l. 272, l. 308) does not list this review.
* `MEBV/Block.lean` l. 27 still says `hilb_deg = 33`. The certified value is 41 (M2.md §M2.4b); this is not an interface
  change.
* **Fix:** add rows "`AbVar.Thm11KappaAn 5 2 (·+1) perA5 perB5`, `Thm11KappaAnK … ∅` (narrowed form, pending lean_mstar
  §1.6) | `LSG.W88.thm11KappaAn5`, `thm11KappaAnK5` | unconditional"; add (I5) to TRUST §9; fix the docstring.

**m4 — MINOR (scope): `Thm11KappaAnK` is covered only for LAn = ∅.**
* Logarithms of non-torsion points of A^♮ have base parts outside `latt`, so `LamAV` excludes them.
* lean_mstar has no consumer instance of `mgAn_K` anyway.
* **Fix:** state "LAn = ∅", as M1 does for `LA`.

**m5 — COSMETIC.**
* `LSG.AuxAV.etaB` (blockwise η) and `ThetaData.etaB` (the fibre period) share a short name.
* `MStarCopyAbVarN.lean`'s header "Pending narrowing … copied here as is" is accurate, but the copied unrestricted
  `MStarCopy.Thm11KappaAn` is used by nothing except the copy check. Keep it for the `rfl` check, or note this.

## Paper wording (suggested)

> For Theorem MG♮-A at `B(1/5,1/5)` (the headline `2^t, 3^t` with `t = Γ(1/5)²/Γ(2/5)`) the formal development proves
> the following special case of W88 §5d. Let `A = Jac(y⁵ = x(1 − x))`, and let `A_σ̄^♮` be the extension of `A` by
> `G_a` whose class is that of the differential of the second kind `dx/y`. Let `Q` be the push-out of `(A_σ̄^♮)^m`
> along `bᵀ`, for `b` an adapted basis of a number field containing `ℚ(ζ₅)`. The case proved is W88 §5d for
> `G = G_a^{d₀} × G_m^{d₁} × Q`, restricted to:
> * hyperplanes `V` that are *toric-injective* (`V` contains no nonzero rational period of `Q`);
> * subgroups `Y` whose points have trivial `A^m`-component (their `G_a`, `G_m` and fibre components are arbitrary
>   algebraic points).
>
> This is implied by W88. The Lean proof, which goes through Philippon's multiplicity estimate, is unconditional. The
> hypothesis of Theorem MG♮-A is used only at three frame hyperplanes, and each of them is toric-injective. This is
> proved in Lean from the `F`-independence of `b` and the fact that the fibre character `ζ ↦ ζ⁴` is a field embedding.
> The group `A_σ̄^♮` is presented in Lean by an explicit projective model over `ℚ` and an entire uniformisation built
> from theta functions. Its fibre periods are computed in Lean to be `(3/5)ζ^{4e}(1 − ζ⁴)B(4/5, 4/5)`, i.e. `−3` times
> the periods of `X³dX/Y`. The identification of this model with the extension of `Jac(C)` is classical and not
> formalised. The final four-exponentials statement concerns explicit numbers and does not depend on it.

Until lean_mstar adopts the narrowing (C2), add: "lean_mstar's hypothesis `Thm11KappaAn` must first be narrowed to
toric-injective hyperplanes (a weakening); a scratch check confirms the narrowed consumers compile."

## Appendix: scratch files (in the session scratchpad; never placed in either repository)

* `M2E2E.lean`
  (470 lines). It contains:
  - §1, the copy checks, and §2, the narrowed definitions `Thm11KappaAnOn'`/`Thm11KappaAnKOn'`, the weakening, and the
    adapters;
  - §3, `perAn_poly'` and `perAn_inj'`;
  - §4, `fourExpAt_An_on`, `transcendental_div_pi_on`, `wuestholzB5_on`, `fourExpAt_beta5_on`,
    `two_three_beta5_on`, `mgAn_K_on`. These are generated from lean_mstar's source text by the textual substitutions
    listed in §4: the hypothesis name, `frame_false → frame_false_on` plus `perAn_inj'`, `good := TorInj` plus
    `torInj_ker_phiW`, and `frame2_false_K → frame2_false_K_on` plus `hper0`;
  - §5, the end-to-end theorems and `#print axioms`.

  It was compiled with `lake env lean <path>` from lean_mstar's root, exit 0, no errors.
* `M2Degen.lean`:
  `scratch_sub_eq`, `scratch_fibre_lam`, `scratch_eta_ne`. All use standard axioms.

The key statements, verbatim:

```lean
def Thm11KappaAnOn' (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (Pb : ℂ) : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmAn N g κ P Pb b) (TorInj (gmAn N g κ P Pb b))

example (N g κ P Pb) (h : Thm11KappaAn N g κ P Pb) : Thm11KappaAnOn' N g κ P Pb := fun r b hb => (h r b hb).on

lemma perAn_inj' {N g : ℕ} (κ : Fin g → ℕ) (P : Fin g → ℂ) (Pb : ℂ) {r : ℕ} {b : Fin r → ℂ}
    (hN : 2 ≤ N) (hb : IsAdaptedBasisD (zetaN N) N.totient b) (hκN : ∀ s, (κ s).Coprime N) (hPb : Pb ≠ 0) :
    ∀ q ∈ Submodule.span ℚ (perAngen N g κ P Pb b), LinearMap.snd ℂ _ ℂ q = 0 → q = 0

theorem thm11KappaAn5_check : Thm11KappaAnOn' 5 2 (fun s => (s : ℕ) + 1) perA5 perB5 := fun r b hb =>
  LSG.W88.thm11KappaAn5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

theorem scratch_two_three_M2 :
    ¬ (IsAlgebraic ℚ (Complex.exp (betaIntegral (1 / 5) (1 / 5) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp (betaIntegral (1 / 5) (1 / 5) * Complex.log 3))) :=
  two_three_beta5_on thm11KappaAn5_check
```

No file in either repository was edited, apart from writing this report, and no git state was changed. lean_lsg's
only untracked file (`scripts/jac/memwatch.ps1`) and lean_mstar's (`DeadCode.lean`) predate this review.
