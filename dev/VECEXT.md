# VECEXT: W88 Theorem 4.1 for vector extensions — design

Written 2026-10-31. Labels as in PLAN.md ([Lit] read in a source, [Design] my choice, [Est] line estimate).
Statement file: [`LSG/W88/StatementVec.lean`](LSG/W88/StatementVec.lean) (compiles with `lake env lean`; not imported by
`LSG.lean`; only trivial proofs). Sources read: PLAN.md, STAGE2.md, STAGE3_D2/D3/S7.md, INTERFACE.md,
`LSG/W88/{Statement,Main,Thm11Kappa,K11Sub,MStarCopy}.lean`, `LSG/Weierstrass/*`, `LSG/ME/MultEstStmt.lean`;
lean_mstar `CM4E/{Waldschmidt,MX,MainNat,Lattice}.lean`, `CM4E/Gen/{MGn,MGnK,MXGen,Frame,Frame2,CMLattice,Instances}.lean`,
`TRUST.md`; paper `schanuel/five_exp/pilot_thmM/paper/paper.tex` §§2, 3, 5; W88 pp. 392–395 (`ref/w88_pages/w88-10,11.png`).

---------------------------------------------------------------------------------------------------------------------

## 0. Decisions in one paragraph

Class 𝒞 = `G_a^{d₀} × G_m^{d₁} × G₂`, **`G₂` = push-out of `(E₁ × ⋯ × E_m)^♮` along an algebraic matrix
`M : ℂ^m → ℂ^r`** (arbitrary curves with algebraic `g₂, g₃`; `M` need not be onto). Quotients by abelian-type subgroups
(`Q″ = (E^♮)^n/(B^♮_{ker φ} + {θᵀw = 0})`) are **not** in the class: they are handled by an explicit isogeny in the
bridge (a coordinate complement `J` of `ker φ`). Subgroups are **not products**: `G' = T_U × (B̃ + Γ)` with `Γ` a rational
subspace of the vector group `G_a^{d₀} × (fibre)`, W88's projection-based `δ₀, δ₁`. Three statements:
`Theorem41Vec` (faithful target), `Theorem41VecLA` (premises `r ≤ 1`, `LiftAlg`, `V ∩ fibre = 0`; first proof target,
enough for all four bridges), `HyperplaneKappaVec` (W88 §5d for the class, the generic engine; the bridges are then
coordinate checks + a subgroup classification). The multiplicity estimate for a push-out is reduced to the one for the
product `G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮` applied to `ker M`-invariant polynomials. Total ≈ 26k lines [Est].

## 1. The target statement

### 1.1 Coordinates [Design; conventions = lean_mstar `LogNat`, paper §5 "Set-up"]
`T_G = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r ∋ (a, b, z, s)` (`TanV d0 d1 m r`). On `(E^m)^♮` the coordinates are `(z, w)`, base
`z` dual to `dx/y`, fibre `w` dual to `−x dx/y`, `exp(z, w) = ((℘_j(z_j), ℘_j′(z_j))_j, w − ζ(z))` (`ζ` coordinatewise,
`LSG.Weierstrass.zeta`), and `s = M w`. These are `ℚ̄`-rational coordinates of `Lie G` (de Rham `H¹_dR(E)^∨`).
* **`Λ(G)` = `LamV Ls M`**: `a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`, each `z_j ∈ Λ_j` or `℘_j(z_j) ∈ ℚ̄`, and `s − Mζ(z) ∈ ℚ̄^r`.
  No case split at lattice points: Lean's `ζ(0) = 0` (all series terms vanish), so `ζ(λ) = η(λ)` on `Λ`
  (`zeta_of_mem_lattice`, proved in the file from `zeta_add`). This is lean_mstar's `LogNat` with `ζ* = ζ`.
* **`Ω(G)` = `PerV Ls M`** (an `AddSubgroup`, proved): `0 × 2πiℤ^{d₁} × {(λ, Mη(λ)) : λ ∈ Λ₁ × ⋯ × Λ_m}`.
* Rationality `RatSubV`, `RatPair`: spanned by vectors with algebraic coordinates.
* Not used: the conjugate-eigen coordinate `w − κ₁z`. For the bridges' lattices `κ₁ = 0` (§2.6), so `ζ* = ζ`.

### 1.2 Subgroups [Design; classification argument = paper §5 Step 3, generalised]
`SubgroupDataV`: `U ⊂ ℚ^{d₁}`, `t ⊂ ℂ^m` with `IsAbelianTangent Ls t` (reused from `Statement.lean`), and
`Γ ⊂ ℂ^{d₀} × ℂ^r` with `RatPair Γ`. Tangent space
`T_{G'} = vecIncl(Γ) + torIncl(U^⊥) + g2Incl(perTan t)`, `perTan t = (id × M)(perTanId t)`,
`perTanId t = span_ℂ {(λ, η(λ)) : λ ∈ t ∩ Λ}`.
* **Truth.** Each datum is the connected algebraic subgroup `T_U × (B̃ + Γ)` over `ℚ̄`: `B ⊂ ∏E_j` the abelian subvariety
  with tangent `t`, `B^♮ ↪ (E^m)^♮` its universal vector extension (injective because `H¹(A,O) → H¹(B,O)` is onto),
  `B̃` its image in `G₂`, `Γ` a rational vector subgroup. `T(B^♮) = perTanId t`: every `λ ∈ t ∩ Λ` has exactly one lift
  `(λ, η(λ))` in `Ω((E^m)^♮)`, and the period lattice of the anti-affine group `B^♮` spans `T(B^♮)` over `ℂ`
  (dimension `2 dim t`; for `t = ℂ^m` this is Legendre, `legendre_ne_zero`). [Lit: standard, paper §5 Step 3]
* **Completeness** (needed only inside the proof, §3.2): every connected algebraic subgroup `K` is of this form.
  `Hom(G_m, G₂) = 0` and no subgroup of `G₂` has a torus quotient, so `K = T_U × K'`. `K'` is an extension of
  `B = image in A` by the vector group `K' ∩ (G_a^{d₀} × fibre)`, hence receives a homomorphism from `B^♮` over `B`; two
  lifts `B^♮ → G` over `B` differ by an element of `Hom(B^♮, vector group) = 0`, so `K' ⊇ B̃` and `K' = B̃ + Γ`.
* **Codimensions** (W88 p. 392: `d₀' = dim π₀(G')`, `d₁' = dim π₁(G')`, `d₂' = d' − d₀' − d₁'`):
  `δ₀ = d₀ − dim pr₀Γ`, `δ₁ = dim U`, `δ = d − dim T_{G'}`, `δ₂ = δ − δ₀ − δ₁`. For products these agree with
  `Statement.lean`. Paper type E (`{s₁ = μ s₂}` in `G_a × G_ℓ`) is `U = ⊤, t = 0, Γ = ℂ(μ, 1)`: `δ₀ = 0`, `δ₂ = 2n+1`.
* `d₂ = m + r` in the inequality. A non-onto `M` makes `d₀` non-maximal; W88 Thm 4.1 allows that (paper Thm 2:
  "`d₀, d₁` need not be maximal").

### 1.3 The three statements
* `Theorem41Vec`: exactly the shape of `Theorem41Abelian` (`Concl41`, (NR) `d₁ + 2d₀ + κ ≤ 2N`), class 𝒞. TRUE by
  W88 Thm 4.1 [Lit]. `r = 0` recovers `Theorem41Abelian` up to `Tan d0 d1 m ≅ TanV d0 d1 m 0` (bridge ≈ 300 l., optional).
* `Theorem41VecLA` = `Theorem41Vec` + `r ≤ 1` + `LiftAlg Ls` + `V ⊓ fibreV = ⊥`. `theorem41VecLA_of` (trivial) is in the
  file. Why each premise (all automatic where it is used, §2):
  - `V ∩ fibre = 0`: lets Prop 2.1 (Tier 2) use only non-fibre coordinate forms (risk R3 of STAGE3_D2 resolved, §3.3);
  - `r ≤ 1`: the fibre part `Γ ∩ (0 × ℂ^r)` of the obstruction is automatically rational (`0` or `ℂ`); for `r ≥ 2` this
    needs `ℚ̄`-descent of the stabiliser (R4);
  - `LiftAlg Ls` (every algebraic point of `B` lifts to an algebraic point of `B^♮`; TRUE for all curves over `ℚ̄`):
    makes the `Sec7Rat` trick work for the `G_a`/graph part of `Γ` (an irrational type-E graph is replaced by `Γ = 0`
    without changing `λ`, §3.4).
* `HyperplaneKappaVec`: W88 §5d with `d₂ = m + r`, premises `r ≤ 1`, `LiftAlg`, `PerTanRat` (`T(B^♮)` rational; TRUE
  for all curves over `ℚ̄`). Conclusion: `∃ H, H.tan ≠ ⊥ ∧ H.tan ≤ V`.

### 1.4 (NR) in the lean_mstar uses [checked]
For a hyperplane in `G` with `d₂ = g + f` (`g` abelian dim, `f` vector part of `G₂`), (NR) ⇔ `κ ≤ d₁ + 2d₂ − 2`, and
`κ ≤ rk Ω = d₁ + 2g`. So (NR) holds **for every configuration** as soon as `f ≥ 1`:
MG♮ `5n ≥ 2n + κ` (`κ ≤ 3n`), MX `4n + 2 ≥ 2 + κ` (`κ ≤ 4n`), MX′ `4n + 2 ≥ κ` (`κ ≤ 4n`) — matches TRUST.md
("Lemma U's range covers every configuration" for `gmQ, gmMGn, gmMGnK, gmXG, gmXP`).
For the second application in §5d (to a subgroup `G'`, projection-based `d'`), (NR) fails only when `G' ∩ G₂` is an
abelian variety (`f' = 0`) and `κ' ≥ d₁' + 2g' − 1`. Those corners are handled in the engine (§3.6).

## 2. Bridges

### 2.1 Architecture [Design]
```
Theorem41VecLA ──(§5d engine, generic)──> HyperplaneKappaVec
HyperplaneKappaVec + CM toolkit ──(hyperplaneKappa_of_iso + per-model checks)──> Thm11KappaMXG / MGn / MGnK / Nat
```
`hyperplaneKappa_of_iso` (LSG, against the verbatim `MStarCopy.GroupModel`/`HyperplaneKappa`, already present): for a
model `G` on `Vt`, a class-𝒞 group and a `ℂ`-linear iso `ι : TanV → Vt` with
(i) `ι`, `ι⁻¹` preserve algebraic vectors; (ii) `∀ y ∈ G.lam, ∃ N ≥ 1, N • ι⁻¹ y ∈ AddSubgroup.closure(ι⁻¹ lamGen) ⊆ LamV`
(a common denominator replaces division points; `LamV` is closed under `+` by the ζ addition theorem);
(iii) `ι⁻¹(G.per) ⊆ span_ℚ PerV` (so our `κ ≥` theirs, which only strengthens (5.4));
(iv) `G.d₁ = d₁`, `G.d₂ = m + r`; (v) for every nonzero `SubgroupDataV` `H`, `G.sub (ι(T_H))`
⇒ `HyperplaneKappa G`. Proof = `HyperplaneKappaVec` + rank/κ bookkeeping as in `Thm11Kappa.lean` (`span_closure_eq`,
`span_inf_addSubgroup`). [Est 400]

### 2.2 The §5d engine `Theorem41VecLA → HyperplaneKappaVec` [Design; W88 pp. 392–395]
As `Thm11Kappa.lean`: assume no nonzero `T_H ⊂ V`; Lemma 5.1 (maximise `a/e`, `a(G') = rk(Y ∩ (T_{G'}+Ω)) − κ + d₁' + 2d₂'`,
`e = dim G' − dim(W ∩ T_{G'})` over `SubgroupDataV`, a finite set of values); Lemma 5.2 via
`rk Ω − rk(Ω ∩ T_{G'}) ≤ (d₁ + 2d₂) − (d₁' + 2d₂')` (holds: `rk(Ω ∩ T_{G'}) = d₁' + 2 dim t`, `d₂' = dim t + f'`, `f' ≤ r`);
then Thm 4.1 on `G'` with `V' = V ∩ T_{G'}`, `W ∩ T_{G'}`, `Y ∩ T_{G'}`. Note `V ⊉ fibre` automatically (the fibre line is
the member `U = ⊤, t = 0, Γ = 0 × ℂ`), so every `Theorem41VecLA` call has `V' ∩ fibre = 0`.
**Thm 4.1 on a member `G' = T_U × (B̃ + Γ)`** by transport from a class-𝒞 group
`G_H = G_a^{d₀'} × G_m^{d₁'} × ((E^J)^♮ pushed along ν)`:
* `G_a`/graph part: `Γ = Γ₀ ⊕ Γ_fib`, `Γ₀ = graph(g : pr₀Γ → ℂ^r)` rational; `(a, q) ↦ (a, q + g(a))` is an isomorphism
  `G_a^{d₀'} × (G' ∩ G₂) → G'` over `ℚ̄` (this is W88's silent "G' = π₀ × π₁ × G₂'" — made explicit).
* torus: `ℤ`-basis of `U^⊥ ∩ ℤ^{d₁}` (as `K11Sub`'s frame `C, D`).
* `G' ∩ G₂ = B̃ + Γ_fib`: choose `J` with `t ⊕ ℂ^{J^c} = ℂ^m` (so `p_J : B → E^J` is an isogeny and `B^♮ → (E^J)^♮`,
  the restriction of the coordinate projection `(z, w) ↦ (z_J, w_J)`, is an isogeny — no isogeny theory of `ζ` needed);
  `ν := M ∘ (fib(B^♮) ≅ ℂ^J)⁻¹ : ℂ^J → V_f := fib(B̃) + Γ_fib`; tangent map `Φ(z, s) = (z_J, s − Mκ_t(z))`, where
  `κ_t(z)` is the unique `w` with `(z, w) ∈ perTanId t`, `w_J = 0`.
* Checks: `Φ` rational (`PerTanRat`); `Φ(Λ(G) ∩ T_{G'}) ⊆ Λ(G_H)` (`LiftAlg` + linear algebra over `ℚ̄`: an `x` in the
  rational space `fib(B^♮)` with `Mx ∈ ℚ̄^r` is algebraic modulo `ker M`); periods: `p_J(t ∩ Λ)` has finite index in `Λ^J`,
  so ranks agree; members of `G_H` map to members of `G` inside `G'` with the same `δ₀, δ₁, δ₂, τ, λ`.
* `r_H = dim V_f ≤ r ≤ 1`, curves of `G_H` ⊂ curves of `G` (so `LiftAlg`, `PerTanRat` inherited).
[Est: transport 2.0k, Lemmas 5.1/5.2 0.6k, corners 0.7k (§3.6) → 3.3k]

### 2.3 `Thm11KappaMXG` (G_a × G_ℓ) [checked against `CM4E/Gen/MXGen.lean`]
* Group: **directly in 𝒞**, no isogeny: `d₀ = 1`, `d₁ = 0`, curves `Ls = (E_i)×n ++ (E_ρ)×n` (`m = 2n`), `r = 1`,
  `M = (θᵀ, θᵀ)`. `ι : TanV 1 0 (2n) 1 ≅ TXG r` = reindexing `Fin (2n) ≃ (Fin r × Fin 2) ⊕ (Fin r × Fin 2)`.
  Their `d₂ = 2·card + 1 = m + r` ✓, `d₁ = 0` ✓, `algXG` = `AlgVecV` ✓.
* lam: `gXI h z w` ↦ `(0, z e_h, θ_h w)`: `s − Mζ(z) = θ_h(w − ζ(z))` (other coordinates `ζ(0) = 0`), algebraic by
  `LogNat` once `etaLem m n = η_LSG(mϖ + niϖ)` and `etaR m n = η_LSG(…)` (CM toolkit) and
  `CM4E.Ext.Weierstrass.zeta = LSG.Weierstrass.zeta` (verbatim copy; check by `rfl`/`unfold` as for `MStarCopy`).
  `gXA h a t` ↦ `(θ_h a, 0, θ_h t)` ✓. per: `GX1 … HX2` are periods `(λ e_h, θ_h η(λ))` ✓.
* sub `S = ⊥ ∨ ∃ x ∈ S, algXG x ∧ Ψ''x ≠ 0`: for a nonzero member, `T_H` is rational (`PerTanRat` for `E_i^n × E_ρ^n`) and
  `T_H ⊄ ker Ψ''` (paper §5 Step 3/Remark "The count"): `Γ ⊂ ker Ψ''` forces `Γ = 0`; `t = ℂS_i × ℂS_ρ` (splitting lemma),
  `perTan t = {(z, θᵀw_i + θᵀw_ρ) : z ∈ ℂS, w ∈ ℂS̄}` inside `ker Ψ''` forces `ψ(S_•) = φ(S_•) = 0`, so `S = 0` (Lemma K).
* Premises `hg₂, hg₃` of both lattices are premises of `Thm11KappaMXG` ✓. No mismatch. [Est 1.05k incl. 250 copied lines]

### 2.4 `Thm11KappaMGn L` (G_m^{2n} × Q″) [checked against `CM4E/Gen/MGn.lean`, `Frame.lean`]
* Group: `Q″` is **not** in 𝒞. Isogeny: pick `J ⊂ Fin r × Fin 2`, `|J| = n/2`, with `k^J ⊕ ker φ = k^n` (basis exchange
  on a `k`-basis of `ker φ`; `ker φ` has `k`-dim `n/2` by Lemma K). Class-𝒞 group `G = G_m^{2n} × ((E^J)^♮ pushed along
  θ_Jᵀ)`, `ι(x, y, z_J, s) = ((x, y), ([incl z_J], s))`; iso since `ℂ^n = ℂ^J ⊕ ℂ·ker φ`; `ι⁻¹` rational (`Wphi` is
  spanned by `k`-vectors). `d₂ = finrank Qn = n/2 + 1 = m + r` ✓.
* per: `ι⁻¹([ω e_j], θ_j η₀) = (ω a, θ_j η₀)` with `e_j = a + b`, `a ∈ k^J`, `b ∈ ker φ`; with `N a ∈ ℤ[α]^J`,
  `N(ωa, θ_jη₀)` is the period `(λ, θ_Jᵀη(λ))`, `λ = Nωa`, because `η(Nωa_l) = N ā_l η₀` (`κ₁ = 0`, `η₀ = η(ω)`) and
  `θ_Jᵀā = θ_j` ⇔ `φ(e_j − a) = 0` ✓. lam = toric logs + these periods ✓.
* sub (`gmF`): `ι(T_H) = torSub L × h` with `L = annQ U` (`K11Lin.annC_eq_cspan`); if `h ≠ 0` it has a vector with
  fibre coordinate `≠ 0`: `Γ = ℂ`, or `t = ℂS_J ≠ 0` and `φ` is injective on `k^J` ✓.
* **Mismatch**: `Thm11KappaMGn L` quantifies over all `CMLattice`s, whose `η₀` is only tied to the lattice by Legendre.
  The bridge needs `κ₁ = 0` (then `η = η*` is conjugate-linear and Legendre with `Im α > 0` forces `η₀ = η(ω)`). Result:
  `Theorem41VecLA → ∀ L, KappaOneZero L → Thm11KappaMGn L`. lean_mstar uses only `latI` (`kappaOneZero_latI` exists, for its
  copy of `ζ`) and `latRho` (`KappaOneZero latRho` is **not** in lean_mstar; the CM toolkit proves it, `ρΛ = Λ`, `|ρ| = 1`).
  Recommended: lean_mstar adds the premise `KappaOneZero L` to `Thm11KappaMGn` (as it already did for `MGnK`). General `L`
  would need `κ₁ ∈ ℚ̄` (Masser's `s₂` algebraicity) — not planned. [Est 1.0k incl. 300 copied]

### 2.5 `Thm11KappaMGnK L` and `Thm11KappaNat`
* MGnK (`gmF2`, premise `KappaOneZero L` already present ✓): same `ι` as MGn. New lam generators
  `([u e_i], θ_i w)`, `LogNat L.pp (etaL L) u w`: `ι⁻¹ = (u a, θ_i w)`, `a ∈ k^J`; in `LamV` because
  `℘(a_l u) ∈ ℚ̄` and `ζ(a_l u) − ā_l ζ(u) ∈ ℚ̄` (CM toolkit) and `θ_Jᵀā = θ_i`. sub: `T_H` rational and `⊄ ker Ψ''` ✓. [Est 0.3k]
* Nat (`gmQ`, `n = 4`, `θ = (1, i, √2, i√2)`, coordinates `(ℓ_{τ₁}(z), ℓ_{τ₂}(z), θᵀw)` on `T(Q″)`): `ι` = (MGn's `ι` with
  explicit `J`) composed with the explicit linear iso to these coordinates; lam = toric logs + `perQ` ✓; sub
  `h = ⊥ ∨ e₂ ∈ h`: a nonzero `T_H`-part contains the fibre (`Γ = ℂ`, or `t ≠ 0` and `perTan t ∋ (0, θᵀw̄) ≠ 0`) ✓. [Est 0.5k]

### 2.6 CM toolkit (shared by the bridges) [Est 2.1k]
For a period pair with `αΛ = Λ` and `ζ(αz) = ᾱζ(z)` (`κ₁ = 0`; LSG's `ζ`): `℘(αz) = (ᾱ/α)℘(z)` (differentiate),
`η(αλ) = ᾱη(λ)`, `η(mω) = m̄η(ω)` on `ℤ[α]ω`; Legendre ⇒ `η(ω) = η₀` for lean_mstar's `η₀`, and the explicit values
`etaLem`, `etaR`, `etaRho` (≈ 400). `KappaOneZero` for `latRho` (≈ 150). Abelian tangents of `E^n` are `ℂ·S`, `S ⊂ k^n` a
`k`-subspace (INTERFACE's promised lemma; ≈ 400). `perTanId(ℂS) = ℂS × ℂS̄` ⇒ `PerTanRat` (≈ 350). `LiftAlg`: pivot
basis of `S`, `w := Σ_l ζ(z_{j_l}) v̄_l`; needs `ζ(u + u′) − ζ(u) − ζ(u′) ∈ ℚ̄`, `ζ(αu) = ᾱζ(u)`, `ζ(u/N) − ζ(u)/N ∈ ℚ̄`
(`isAlgebraic_of_intCast_mul` for `℘`) (≈ 500). Splitting `t = t_i × t_ρ` for `E_i^n × E_ρ^n` (a `ℂ`-linear map sending
`ϖk^a` into `Ω_ρ k′^a ⊗ ℚ` would put `i ∈ ℚ(ρ)`; ≈ 250). Lemma K (`(ψ, φ) : k^n ≅ K × K`, `ker ψ ∩ ker φ = 0`) (≈ 300;
lean_mstar's version cannot be imported, the dependency goes the other way).

### 2.7 Where the bridge code lives
LSG exports `Theorem41VecLA`, `HyperplaneKappaVec`, `hyperplaneKappa_of_iso`, the CM toolkit. The per-model checks need
lean_mstar's model definitions: either verbatim copies in LSG (MStarCopy pattern, ≈ 900 copied lines, re-sync risk) or
files in lean_mstar after it depends on LSG (no copies). Recommended: the latter; estimates above include either.

## 3. Proof plan for `Theorem41VecLA` (reuse of the abelian machinery)

### 3.1 E^♮ library (`LSG/Weierstrass/`, `LSG/Elliptic/`) [Est 1.75k]
ζ addition theorem `ζ(u+v) − ζ(u) − ζ(v) = ½(℘′(u) − ℘′(v))/(℘(u) − ℘(v))` and its degenerate cases (doubling
`℘″/(2℘′)`, `u + v ∈ Λ`, `u ∈ Λ`; via `weierstrassP_add` + derivative comparison) (600); `ζ(nu) − nζ(u)` and division
(300); `LamV` is an `AddSubgroup` for algebraic `M` (250); points of `E^♮` = (Mathlib point, `t`) with the cocycle law,
`exp_{E^♮}` a homomorphism with kernel `{(λ, η(λ))}` (600).

### 3.2 Multiplicity estimate `MultEstVec` (Stage 2 extension) [Est 11.4k, uncertainty ±40%]
* **Push-out ⇒ product** [Design]: work on `G̃ = G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮` with `ker M`-invariant
  polynomials (`P̃ = P ∘ q`). Translations by lifted points and Philippon operators along `W̃ = q⁻¹W` preserve invariance,
  so every chain ideal is `ker M`-stable and the stabiliser `G̃' ⊇ ker M`; `G' = G̃'/ker M`. The exponents match:
  `t̃₂ − d̃₂ = t₂ − d₂`, and `c̃ = dim W̃ − dim(W̃ ∩ T_{G̃'}) = c`. (700)
* **`E^♮` block** [Design]: variables `(U, V, W, T₁, T₃)`, `T₁ = W t`, `T₃ = W(y t − 2x²)` (a section of the same bundle
  as `U, V, W`: the pole of `t = w − ζ` cancels; at `O`, `T₃/V → w`), ideal `(F, W T₃ − V T₁ + 2U²)`: a complete intersection
  of the right dimension whose zeros are `(E∖O) × 𝔸¹` plus the fibre over `O` (`U = W = T₁ = 0`, `T₃/V = w`), plus the
  irrelevant locus `U = V = W = 0` (excluded by slicing, as in STAGE2 §11). Fibre translation by `v` is linear:
  `T₁ ↦ T₁ + vW`, `T₃ ↦ T₃ + vV`, so `ker M`-invariants are spanned by `E`-polynomials times the forms
  `S_i^{(k)} = Σ_j M_ij T^{(k_j)}_j Π_{l≠j} X^{(k_l)}_l`. Geometry, primality, relevant primes (1.5k).
* Addition laws for `E^♮` blocks: complete system of bihomogeneous laws of bounded degree (computer-algebra search,
  verified in Lean by `linear_combination` modulo the ideal, like `AdditionLaws*.lean`), translations, `zeros (τ_g J)` (2k).
* Invariant derivations: `∂_w` (`T₁ ↦ W`, `T₃ ↦ V`, degree 0) and chart derivations `∂_z` extended to `T`-variables
  (`dt/dz = x`); formal exponential (ODE with `t′ = x`); `phOp` degree bound (1.2k).
* Subgroup layer for `G̃`: stabiliser, Lie algebra, `T′ = U^⊥ + perTanId(t) + Γ̃` (`perTanId t ⊂ T′`: if `(λ, s) ∈ T′`
  then `exp(0, s − η(λ)) ∈ G̃′ ∩ fibre`, a vector subspace, so `(0, s − η(λ)) ∈ T′`), `hdim H⁰ = dim T′`, Hilbert lower
  bound with fibre degrees (3k).
* Slices: on `ℓ = V + αW = 1` the block ring is `(sliced E ring)[t′]`, `t′ = T₃ + αT₁` (`T₁ = W t′ + 2U²`,
  `T₂ = U t′ + ½(V² + g₂UW + g₃W²) − V/2`), still a complete intersection, so `bezout` and the S3 bound carry over;
  sliced Wüstholz with `∂_w` (2k). Assembly `MainVec` adapting `MainAb` + final arithmetic (1k).
* Engineering: Stage 2 hard-codes elliptic blocks `(U, V, W)`; either an abstract block interface (refactor) or
  parallel `E^♮` files. Decide after reading `Geom`/`Transl`/`PhOp` (risk R2).

### 3.3 Auxiliary function (Prop 2.1 / Prop 6.1) [Est 2.1k]
* Functions on `T_G`: monomials in `σ_j³, σ_j³℘_j, σ_j³℘_j′` and `Π_l σ_l³ · (s_i − Σ_j M_ij ζ_j(z_j))` (entire:
  `σ³ζ = σ²σ′`), QP for periods `(λ, Mη(λ))` (`t` is period-invariant; `exists_qp_mono` extended), order-2 growth (600).
* `prop21_G` coordinates: since `V ∩ fibre = 0`, `V` projects injectively to the non-fibre coordinates, so `N` coordinate
  forms among `(a, b, z)` restrict to a basis of `V*`; they send periods into `0`, `2πiℤ`, `Λ_j`: **Tier 2 verbatim**.
  (The fibre forms, whose period images `Σ_j M_ij η_j(Λ_j)` are not discrete for `m ≥ 3`, are never needed.) (300)
* `prop61_b`: unknown count `≥ c D^{m+r}` from the invariant forms, heights of values at algebraic points (fibre values
  algebraic), Lemma 2.2 lower bound for `σ` unchanged, Lemma U (1.2k).

### 3.4 W88 §7 for 𝒞 (`Sec7*` analogues) [Est 1.8k, ~70% reuse]
`Ppoly` in `G̃`-variables (invariant by construction), `ordGt_of_vanishAlong` along `W̃`, counting modulo `G'`
(`htil_le_span` with the vector part), the inequality with `d₂ = m + r`. **Rationality repair** (replaces `Sec7Rat`):
fibre part of `Γ` rational since `r ≤ 1`; for the `G_a`/graph part replace `Γ` by its rational part: `λ` is unchanged
because for `y ∈ Y ∩ (T′ + Ω)` the vector component is algebraic (its `a`-part is `y`'s; its `s`-part is algebraic by
`LiftAlg` when `B̃` is a splitting, and can be chosen so otherwise), `δ − τ` does not decrease, `δ₂` is unchanged.

### 3.5 Classification inside the proof (§1.2 completeness) [Est 0.8k]
Product with the torus (as `ProductGraph`), `T′ = U^⊥ + perTan t + Γ`, `Γ = T′ ∩ (ℂ^{d₀} × ℂ^r)`.

### 3.6 (NR) corners in the §5d engine [Est 0.7k]
For `G'` with `f' = 0` and `κ' ≥ d₁' + 2g' − 1`: `V'` contains a real-codimension-≤1 part of `span_ℝ Ω(G')`, hence
`T_{B̃} ⊂ V` (if `g' ≥ 1`; a nonzero member in `V`, contradiction) or `≥ d₁' − 1` rational toric periods (a rational toric
line in `V` if `d₁' ≥ 2`). Left: `G' = G_a^{a}` (trivial: `G'' = rational hull of Y + W`) and `G' = G_a^{a} × G_m` with
`κ' = 0` — a Gel'fond–Schneider-type statement with `V'` a hyperplane, outside (NR) for every `a`; use
`StrongSix.Roy.waldschmidtTheorem1` (linear groups, with κ, no (NR)) converted to the Cor. 5.3 form. New compared with
`Thm11Kappa.lean` (there `d₀ = 0`, so this corner had `V' = 0`).

## 4. Risks (ordered)
1. **R-model (E^♮ embedding, addition laws, Philippon's c₁)** — PLAN's R2. The CI model `(U,V,W,T₁,T₃)` must carry a
   complete system of bounded-degree addition laws; unverified. Fallback: more fibre coordinates (`T₂`), losing CI
   globally but keeping it on slices (the only place `bezout` is used).
2. **R-size (Stage 2 genericity)**: 11k ±40% depending on how block-specific `LSG/ME` is.
3. **R-Λ (Prop 2.1 with fibre forms)**: avoided by the premise `V ∩ fibre = 0` (automatic in the §5d engine). The full
   `Theorem41Vec` needs Masser's interpolation (W83 Lemma 2.3, several variables; ≈ 2.5k) or a reduction to `G/fibre`
   whose (NR) bookkeeping has corners.
4. **R-rat (ℚ̄-rationality of `Γ`)**: `r ≤ 1` + `LiftAlg`. `r ≥ 2` (Theorem MX′, `Thm11KappaMXP`, `r = 2`) needs
   `ℚ̄`-descent of the stabiliser — so `Thm11KappaMXP` is **not** covered by `Theorem41VecLA`.
5. **R-κ₁**: `LiftAlg`/`PerTanRat` are proved only for `κ₁ = 0` CM lattices; `Thm11KappaMGn` needs the extra premise
   `KappaOneZero L` (§2.4). General curves need the isogeny theory of `ζ` (`κ ∈ ℚ̄` for isogenies; Masser).
6. **R-corner**: the `G_a^a × G_m`, `κ' = 0` corner needs the StrongSix linear theorem (form conversion untested).
7. **R-copy**: verbatim copies of lean_mstar models drift; prefer bridges in lean_mstar (§2.7).

## 5. Estimate and order of work [Est]
| layer | lines |
|---|---|
| statement (done) | 0.25k |
| §3.1 E^♮ library | 1.75k |
| §3.2 MultEstVec | 11.4k |
| §3.3 Prop 2.1/6.1 | 2.1k |
| §3.4–3.5 §7 + classification | 2.6k |
| §2.2 + §3.6 §5d engine | 3.3k |
| §2.6 CM toolkit | 2.1k |
| §2.1, 2.3–2.5 bridges | 3.25k |
| **total** | **≈ 26.5k (20–35k)** |

Order: (a) CM toolkit + E^♮ library (independent, small, de-risk `LiftAlg`); (b) R-model spike: find and verify the
`E^♮` addition laws (decides §3.2's shape); (c) §5d engine + `hyperplaneKappa_of_iso` + MXG bridge **against the
statement** (conditional on `Theorem41VecLA`, like `thm11Kappa_of_theorem41`) — validates the statement before the long
part; (d) MultEstVec; (e) Prop 2.1/6.1, §7; (f) MGn/MGnK/Nat bridges.
