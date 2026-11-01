# Interface: the unconditional W88 Thm 4.1 from `lean_lsg/` (for `lean_cm4e/` and other users)

Status 2026-10-30: **statement fixed, proof in progress** (Stage 1 of `PLAN.md` running). Nothing here is proved yet
except that the statement file compiles.

## The declaration to target

`LSG.W88.Theorem41Abelian : Prop` in [`LSG/W88/Statement.lean`](LSG/W88/Statement.lean) (Lean 4.35 / Mathlib v4.35.0,
compiles). It is W88 Thm 4.1 under hypothesis (NR) `2N ≥ d₁ + 2d₀ + κ`, for

  G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m,  E_j given by Mathlib `PeriodPair`s with algebraic g₂, g₃.

The eventual proof will be `LSG.W88.theorem41Abelian : LSG.W88.Theorem41Abelian`. A later version adds vector
extensions (for MG♮, MX, MX′) as `Theorem41` with the abelian case as a corollary; `Theorem41Abelian` will stay as is.

## Conventions (so that a hypothesis like `WaldschmidtGmE` can be discharged by `Theorem41Abelian`)

* Tangent space `Tan d0 d1 m = (Fin d0 → ℂ) × (Fin d1 → ℂ) × (Fin m → ℂ)`; exp is
  `(a, b, z) ↦ (a, e^b, (℘_j(z_j), ℘_j′(z_j)))`.
* `Lam Ls` = logarithms of algebraic points: `a` algebraic, every `e^{b_i}` algebraic, every `z_j` in `Λ_j` or with
  `℘_j(z_j)` algebraic.
* `Per Ls` = periods `0 × 2πiℤ^{d₁} × Λ₁ × ⋯ × Λ_m` (an `AddSubgroup`).
* `Y : AddSubgroup (Tan d0 d1 m)`, finitely generated, `Y ⊂ V ∩ Lam`; ranks are `finrank ℚ (span ℚ Y)` (`LSG.W88.rk`);
  κ = `rk (Y ⊓ Per Ls)`.
* `W` is ℚ̄-rational (`RationalOverQbarTan`: spanned by vectors with all coordinates algebraic), `W ≤ V`, `dim V < d`.
* Conclusion: a `SubgroupData` (G′ = H₀ × T_U × B: `h0` ℚ̄-rational, `U ⊂ ℚ^{d₁}` with Lie algebra `U^⊥`, `t ⊂ ℂ^m`
  whose intersection with Λ₁ × ⋯ × Λ_m spans it over ℝ), proper, with δ > τ and
  `(λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2m − κ)` in ℤ, λ = `rk Y − rk (Y ⊓ (T_{G′} + Per))`,
  τ = `dim W − dim (W ⊓ T_{G′})`.

For the CM curve E_i = `y² = 4x³ − 4x` one takes the period pair (ϖ, iϖ); "T_{G′} for an abelian subvariety of E_iⁿ"
is then C·σ(S) for a Q(i)-subspace S ⊂ Q(i)ⁿ (a lemma we will provide: `t ∩ Λⁿ` spans t over ℝ ⇔ t = C·S).

Users who prefer Roy's "surjective linear map s" form (as in StrongSix's `WaldschmidtTheorem1`): take s = the quotient by
T_{G′}; we will add that reformulation on request.

## Matching `lean_mstar/` (read 2026-10-30)

`lean_mstar` (repo of the MX session; library `CM4E`) assumes `hW : CM4E.Waldschmidt.Thm11Kappa L d₁` — W88 §5d
((5.4): Thm 1.1 with κ) for G_m^{d₁} × E — plus `hg₂ : IsAlgebraic ℚ lemniscatic.g₂` and `hS : Irrational (varpi / π)`.
Plan on our side:
* `Thm11Kappa` will be derived from `LSG.W88.Theorem41Abelian` (d₀ = 0, m = 1): the §5d deduction (any G′ allowed by
  the Thm 4.1 inequality under the hypothesis m > (d₁ + 2 − κ)(d₁ − dim W) has T_{G′} ⊂ V). Bridge file:
  `LSG/W88/Thm11Kappa.lean`, statement copied verbatim from `lean_mstar/CM4E/Waldschmidt.lean` so that `lean_mstar` can
  discharge `hW` by one `exact` once it depends on `lean_lsg`. (NR) holds there: 2d₁ ≥ d₁ + κ since κ ≤ … — to be
  checked when writing the bridge; if (NR) fails in a corner, that corner is handled separately.
* `hS` is implied by our Stage 1 target `LSG.Schneider.period_div_pi_transcendental` (ϖ/π transcendental) applied to
  the period ϖ of the lattice ϖℤ[i] — provided `hg₂` holds, which Schneider's theorem needs anyway.
* `hg₂` (g₂(ϖℤ[i]) = 4) is not on our path; it needs the Γ-formula for ϖ.

## Update 2026-10-30: Stage 1 done
* `LSG.Schneider.period_div_pi_transcendental (hg₂ hg₃) (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) : Transcendental ℚ (ω / (Real.pi : ℂ))`
  and `period_transcendental` are proved, standard axioms only (`LSG/SchneiderMain.lean`).
* For lean_mstar: `hS : Irrational (varpi / π)` follows from `period_div_pi_transcendental` at L = `CM4E.lemniscatic`,
  ω = ϖ (= `ω₁_mem_lattice`), with `hg₂` from `LSG.Lemniscate.g₂_isAlgebraic_of lemniscatic rfl rfl` (currently a
  local-only port, being rewritten independently) and `hg₃` from lean_mstar's `g₃_lemniscatic_isAlgebraic`
  (transcendental ⇒ irrational). So both `hg₂` and `hS` are discharged once lean_mstar depends on lean_lsg; only `hW`
  (W88 Thm 4.1) remains.

## Update 2026-10-30: `hg₂` and `hS` are proved (independent proof)
`LSG/Bridge/Lemniscatic.lean`, standard axioms only:
* `LSG.Bridge.isAlgebraic_g₂ (L : PeriodPair) (h₁ : L.ω₁ = (varpi : ℂ)) (h₂ : L.ω₂ = I * varpi) : IsAlgebraic ℚ L.g₂`
* `LSG.Bridge.irrational_varpi_div_pi_of (L) (h₁) (h₂) : Irrational (varpi / Real.pi)`
with `varpi := LSG.LemniscateIndep.varpi = Real.Gamma (1/4)^2 / (2 * Real.sqrt (2*π))` (same body as `CM4E.varpi`).
In lean_mstar: `hg₂ := LSG.Bridge.isAlgebraic_g₂ CM4E.lemniscatic rfl rfl` (checked against a verbatim copy of the
definitions), and `hS` from `irrational_varpi_div_pi_of CM4E.lemniscatic rfl rfl` after `CM4E.varpi = LSG.LemniscateIndep.varpi`
(by `rfl`/`unfold`). The earlier ported proof (licence problem) is gone.

## Update 2026-10-31: bridge for `hW`
`LSG.W88.thm11Kappa_of_theorem41 (h : Theorem41Abelian) (L : PeriodPair) (d₁ : ℕ) : MStarCopy.Thm11Kappa L d₁`
(`LSG/W88/Thm11Kappa.lean`, axiom-clean). `MStarCopy` is a byte-for-byte copy of lean_mstar's `CM4E.Waldschmidt` block;
checked that `exact LSG.W88.thm11Kappa_of_theorem41 h L d₁` typechecks against the unmodified
`CM4E.Waldschmidt.Thm11Kappa L d₁`. Proof follows W88 §5 (Lemma 5.1 maximal G′, Thm 4.1 applied to G′, Lemma 5.2);
(NR) corners (κ′ ≥ d₁′ + 2b′ − 1, incl. κ = 5, d₁ = 4) handled inside the proof, no extra hypothesis.
So: once `LSG.W88.theorem41Abelian : Theorem41Abelian` is proved, lean_mstar's hW, hg₂, hS are all discharged.

## Update 2026-10-31: **`LSG.W88.theorem41Abelian : Theorem41Abelian` is proved** (standard axioms only)
`LSG/W88/Main.lean`: `theorem41Abelian` (= W88 §7 `theorem41Abelian_of` + `LSG.ME.multEstAb`) and
`thm11Kappa (L) (d₁) : MStarCopy.Thm11Kappa L d₁`. For lean_mstar, once it depends on lean_lsg:
* `hW := LSG.W88.thm11Kappa CM4E.lemniscatic 4` (statement verbatim);
* `hg₂ := LSG.Bridge.isAlgebraic_g₂ CM4E.lemniscatic rfl rfl`;
* `hS` from `LSG.Bridge.irrational_varpi_div_pi_of CM4E.lemniscatic rfl rfl`.
Q̄-rationality of h₀ was handled inside §7 (h₀ replaced by its algebraic part; inequality preserved), so
`SubgroupData` keeps `h0_rat`. Statement-fidelity review of `LSG/W88/Statement.lean` in progress.

## Update 2026-10-31: general §5d bridge (lean_mstar `HypStdCM`, `HypStdCMAt`)
`LSG/W88/K5dMain.lean` (standard axioms): `hypStdCM (L) : MStarCopy.HypStdCM L`, `hypStdCMAt (L) (d)`,
`hypStdCMAt_zero (L)` — verbatim lean_mstar statements (`MStarCopyStd.lean`, from lean_mstar 5026ff8, 95ddbfa), checked
against lean_mstar's unmodified files by `example : CM4E.Bridge.HypStdCM L := LSG.W88.hypStdCM L`. No CM hypothesis.
`hypStd_of_rat (hrat)` for mixed curves (hrat: abelian tangents ℚ̄-rational; proved for one repeated curve).
Ingredients: `LSG.CM.thm41Sub` (Thm 4.1 for G_a × G_m × B, B any abelian subvariety of ∏E_j), `K5dRoy` (StrongSix Roy
Theorem 1 ⇒ Thm 4.1 for linear groups without (NR)), `K5dTrans`, `K5dModel` (NR corners ⇒ 0 × 0 × B ⊆ V).

## Update 2026-10-31: vector-extension bridges are unconditional (commit 0ed4c24)
`LSG/W88/V5dOnto*.lean`, standard axioms only:
* `LSG.W88.theorem41VecLA_onto : Theorem41VecLAOnto` (Theorem 4.1 for vector extensions when `M.mulVec` is onto);
* `LSG.W88.V5d.hyperplaneKappaVec_uncond : HyperplaneKappaVec` (via the r = 0 presentation: the G_a fibre is swapped
  into d₀, so only the onto case is needed);
* `thm11KappaMXG_uncond`, `thm11KappaMGn_uncond L`, `thm11KappaMGnK_uncond L`, `thm11KappaNat_uncond`.
Checked against unmodified lean_mstar (verbatim lines):
```lean
def adaptL (L : CM4E.Gen.CMLattice) : LSG.W88.MStarCopy.CMLattice :=
  ⟨L.pp, L.ω, L.α, L.η₀, L.p, L.q, L.hω₁, L.hω₂, L.hquad, L.him, L.legendre⟩
example : CM4E.Gen.Thm11KappaMXG := fun h1 h2 h3 h4 r b hb =>
  LSG.W88.V5d.thm11KappaMXG_uncond h1 h2 h3 h4 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
example (L) : CM4E.Gen.Thm11KappaMGn L := fun hk h2 h3 r b hb =>
  LSG.W88.V5d.thm11KappaMGn_uncond (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
-- MGnK: same shape with thm11KappaMGnK_uncond
example : CM4E.MainNat.Thm11KappaNat := LSG.W88.V5d.thm11KappaNat_uncond
```
Not yet: `Thm11KappaMXP` (r = 2, needs the full `Theorem41Vec`; waits for `MultEstVecGap`).

## Update 2026-10-31: `LSG.W88.theorem41VecLA : Theorem41VecLA` proved (commit 4edd2d7)
`LSG.MEV.multEstVec : MultEstVec` (vector-extension multiplicity estimate, all `M`, all degrees; 4-block grading) and
`LSG.W88.theorem41VecLA` (`LSG/W88/MainVec.lean`), standard axioms. Remaining for lean_mstar: MXP (r = 2; in progress),
SMGn (needs the `KappaOneZero` premise in lean_mstar, requested; bridge in progress), AbVar (design note `ABVAR.md` in progress).

## Update 2026-10-31: SMGn bridge (commit below)
`LSG.W88.V5d.thm11KappaSMGn_uncond (L) : MStarCopy.Thm11KappaSMGn L` (`LSG/W88/V5dSMGn.lean`, standard axioms), in the
premised form adopted by lean_mstar 1635927. Checked against the real lean_mstar files:
```lean
example (L : CM4E.Gen.CMLattice) : CM4E.Gen.Thm11KappaSMGn L := fun hk h2 h3 r b hb =>
  LSG.W88.V5d.thm11KappaSMGn_uncond (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
```

## Update 2026-10-31: `Thm11KappaMXP` (Theorem MX′, `r = 2`) is unconditional (commit 4f27015)
`LSG/W88/V5dMXPMain.lean` (design and file list: `STAGE6_MXP.md`), standard axioms only:
* `LSG.W88.theorem41Vec2 : Theorem41Vec2` (Theorem 4.1 for `d₀ = 0`, `r ≤ 2`, `dim (V ∩ fibre) ≤ 1`: Prop. 2.1 with a
  polynomial fibre direction, `prop21LatT`; rationality repair by the `T_S`/`T_E` dichotomy);
* `LSG.W88.V5d.hyperplaneKappaVec2_uncond : HyperplaneKappaVec2`;
* `LSG.W88.V5d.thm11KappaMXP_uncond : MStarCopy.Thm11KappaMXP` (verbatim copy `MStarCopyMXP.lean`).
Checked against unmodified lean_mstar:
```lean
example : CM4E.Gen.Thm11KappaMXP := fun h1 h2 h3 h4 r b hb =>
  LSG.W88.V5d.thm11KappaMXP_uncond h1 h2 h3 h4 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
```

## Update 2026-10-31: `HypStd` for equal-or-non-isogenous curves; the standard model with an `E^♮` factor
Standard axioms only (`Axioms.lean`). Not committed.

**`LSG/W88/K5dNonIsog.lean`** (`G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, lean_mstar's `gmStd`):
```lean
def LSG.W88.NonIsog (L L' : PeriodPair) : Prop := ∀ α : ℂ, α ≠ 0 → ¬ ∀ ω ∈ L.lattice, α * ω ∈ L'.lattice
theorem LSG.W88.hypStd_of_nonIsog (Ls : Fin m → PeriodPair)
    (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hni : ∀ j k, Ls j = Ls k ∨ NonIsog (Ls j) (Ls k)) (d0 d1 : ℕ) :
    MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 Ls)
theorem LSG.W88.hypStd_of_pair (Ls : Fin m → PeriodPair) {L L' : PeriodPair}
    (hLs : ∀ j, Ls j = L ∨ Ls j = L') (hg : IsAlgebraic ℚ L.g₂ ∧ IsAlgebraic ℚ L.g₃)
    (hg' : IsAlgebraic ℚ L'.g₂ ∧ IsAlgebraic ℚ L'.g₃) (h : NonIsog L L') (h' : NonIsog L' L) (d0 d1 : ℕ) :
    MStarCopy.HyperplaneKappa (MStarCopy.gmStd d0 d1 Ls)
theorem LSG.W88.nonIsog_of_tau (hL : L.ω₂ = τ * L.ω₁) (hL' : L'.ω₂ = τ' * L'.ω₁)
    (h : ∀ a b c d : ℤ, τ * (a + b * τ') = c + d * τ' → a = 0 ∧ b = 0) : NonIsog L L'
theorem LSG.W88.nonIsog_I_rho (hL : L.ω₂ = I * L.ω₁) (hρ : ρ ^ 2 + ρ + 1 = 0) (hL' : L'.ω₂ = ρ * L'.ω₁) :
    NonIsog L L'
theorem LSG.W88.nonIsog_rho_I (hρ : ρ ^ 2 + ρ + 1 = 0) (hL : L.ω₂ = ρ * L.ω₁) (hL' : L'.ω₂ = I * L'.ω₁) :
    NonIsog L L'
```
Proof: in a chart of an abelian tangent `t`, `x = lift(e_k)_j` has `n ω₁ x, n' ω₂ x ∈ Λ_j` (periods of `E_{ι k}`):
equal curves give the one-curve quadratic, non-isogenous ones give `x = 0`. Also
`K5d.abTan_rat_nonIsog` (abelian tangents are `ℚ̄`-rational) and `K5d.mul_mem_of_blockConst` (`t` splits along the
equal-curve blocks).

**`LSG/W88/StdVec.lean`**: the model `LSG.W88.MStarCopy.gmStdVec d0 d1 Ls M : GroupModel (Vec.TanV d0 d1 m r)` of
`G_a^{d₀} × G_m^{d₁} × ((∏E_j)^♮ pushed out along M)`, with `d₁ = d1`, `d₂ = m + r`, `alg = AlgVecV`,
`lam = LamV Ls M`, `per = span_ℚ PerV Ls M` and `sub = {H.tan | H : SubgroupDataV Ls M}`. This is new and is not
copied from lean_mstar: lean_mstar should copy its body verbatim, using its own `GroupModel`.
```lean
theorem LSG.W88.hyperplaneKappa_gmStdVec (h : r ≤ 1) (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hM : AlgMat M) (hLA : LiftAlg Ls) (hPT : PerTanRat Ls) : MStarCopy.HyperplaneKappa (gmStdVec d0 d1 Ls M)
theorem LSG.W88.hypStdVecCM (L : MStarCopy.CMLattice) (hκ : MStarCopy.KappaOneZero L)
    (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃) (d0 d1 : ℕ) (M : Matrix (Fin r) (Fin m) ℂ)
    (hr : r ≤ 1) (hM : AlgMat M) : MStarCopy.HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin m => L.pp) M)
def LSG.W88.StdVec.eOne (m : ℕ) : Matrix (Fin 1) (Fin (m + 1)) ℂ := Matrix.of fun _ j => if j = 0 then 1 else 0
theorem LSG.W88.hypStdVecCM_eOne (L) (hκ) (hg₂) (hg₃) (d0 d1 m : ℕ) :
    MStarCopy.HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin (m + 1) => L.pp) (StdVec.eOne m))   -- G_a^{d₀} × G_m^{d₁} × E^♮ × E^m
```
Not done: `LiftAlg`/`PerTanRat` for mixed families of non-isogenous CM curves. The block splitting reduces both to
single blocks, but `LSG.CM.liftAlg_block` is stated for a constant family on `Fin p`, and that reindexing was not
written. So `E^♮` with several non-isogenous curves is not yet covered.

Checked against unmodified lean_mstar with a scratch file at its root (`lake env lean`; the scratch file has been
deleted). It imports `CM4E.Bridge.Std`, `CM4E.Bridge.Vec`, `CM4E.MX`, `LSG.W88.K5dNonIsog`, `LSG.W88.StdVec`, and
uses `open CM4E`:
```lean
example (hg : IsAlgebraic ℚ lemniscatic.g₂ ∧ IsAlgebraic ℚ lemniscatic.g₃)
    (hg' : IsAlgebraic ℚ MX.equianharmonic.g₂ ∧ IsAlgebraic ℚ MX.equianharmonic.g₃) :
    CM4E.Waldschmidt.HyperplaneKappa
      (CM4E.Bridge.gmStd 2 0 ![lemniscatic, lemniscatic, MX.equianharmonic]) :=
  LSG.W88.hypStd_of_pair _ (by intro j; fin_cases j <;> simp) hg hg'
    (LSG.W88.nonIsog_I_rho rfl (by linear_combination MX.rho_sq) rfl)
    (LSG.W88.nonIsog_rho_I (by linear_combination MX.rho_sq) rfl rfl) 2 0
example {m : ℕ} (Ls : Fin m → PeriodPair) (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hni : ∀ j k, Ls j = Ls k ∨ LSG.W88.NonIsog (Ls j) (Ls k)) (d0 d1 : ℕ) :
    CM4E.Waldschmidt.HyperplaneKappa (CM4E.Bridge.gmStd d0 d1 Ls) :=
  LSG.W88.hypStd_of_nonIsog Ls halg hni d0 d1
-- lean_mstar's copy of the model (body verbatim from LSG.W88.MStarCopy.gmStdVec):
noncomputable def gmStdVec (d0 d1 : ℕ) {m r : ℕ} (Ls : Fin m → PeriodPair)
    (M : Matrix (Fin r) (Fin m) ℂ) : CM4E.Waldschmidt.GroupModel (LSG.W88.Vec.TanV d0 d1 m r) where
  d₁ := d1
  d₂ := m + r
  alg := LSG.W88.Vec.AlgVecV
  lam := LSG.W88.Vec.LamV Ls M
  per := Submodule.span ℚ
    (LSG.W88.Vec.PerV (d0 := d0) (d1 := d1) Ls M : Set (LSG.W88.Vec.TanV d0 d1 m r))
  sub := fun S => ∃ H : LSG.W88.Vec.SubgroupDataV (d0 := d0) (d1 := d1) Ls M, S = H.tan
example (L : CM4E.Gen.CMLattice) (hk : CM4E.Gen.KappaOneZero L) (h2 : IsAlgebraic ℚ L.pp.g₂)
    (h3 : IsAlgebraic ℚ L.pp.g₃) (d0 d1 m : ℕ) :
    CM4E.Waldschmidt.HyperplaneKappa
      (gmStdVec d0 d1 (fun _ : Fin (m + 1) => L.pp) (LSG.W88.StdVec.eOne m)) :=
  LSG.W88.hypStdVecCM_eOne (CM4E.Bridge.adaptL L) hk h2 h3 d0 d1 m
example (L : CM4E.Gen.CMLattice) (hk : CM4E.Gen.KappaOneZero L) (h2 : IsAlgebraic ℚ L.pp.g₂)
    (h3 : IsAlgebraic ℚ L.pp.g₃) (d0 d1 m r : ℕ) (M : Matrix (Fin r) (Fin m) ℂ) (hr : r ≤ 1)
    (hM : LSG.W88.Vec.AlgMat M) :
    CM4E.Waldschmidt.HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin m => L.pp) M) :=
  LSG.W88.hypStdVecCM (CM4E.Bridge.adaptL L) hk h2 h3 d0 d1 M hr hM
example (h2 : IsAlgebraic ℚ CM4E.Gen.latI.pp.g₂) (h3 : IsAlgebraic ℚ CM4E.Gen.latI.pp.g₃) :
    CM4E.Waldschmidt.HyperplaneKappa
      (gmStdVec 1 0 (fun _ : Fin 2 => CM4E.Gen.latI.pp) (LSG.W88.StdVec.eOne 1)) :=
  LSG.W88.hypStdVecCM_eOne (CM4E.Bridge.adaptL CM4E.Gen.latI) CM4E.Gen.kappaOneZero_latI h2 h3 1 0 1
```

## Update 2026-10-31: M1 — lean_mstar's AbVar hypotheses for `y⁵ = x(1 − x)` unconditional
`LSG.W88.thm11KappaA5 : MStarCopy.Thm11KappaA 5 2 (·+1) perA5 0` and
`LSG.W88.thm11KappaAK5 : MStarCopy.Thm11KappaAK 5 2 (·+1) perA5 0 ∅` (`LSG/W88/AbVarFinal.lean`), standard axioms, from
`hyperplaneKappaAbVar` (W88 §5d for `G_a^{d₀} × G_m^{d₁} × A^r`, `A = Jac(y² = 4x⁵ + 1)`, on toric-injective hyperplanes).
Checked against unmodified lean_mstar 9b8d036 (copies in `MStarCopyAbVar.lean`):
```lean
theorem m1A : CM4E.AbVar.Thm11KappaA 5 2 (fun s => (s : ℕ) + 1) CM4E.AbVar.perA5 0 := fun r b hb =>
  LSG.W88.thm11KappaA5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
-- same shape for Thm11KappaAK … ∅ with LSG.W88.thm11KappaAK5
example : ¬ (IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1/5) (1/5) / Real.pi * Complex.log 2)) ∧
    IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1/5) (1/5) / Real.pi * Complex.log 3))) :=
  CM4E.AbVar.two_three_beta5 m1A   -- [propext, Classical.choice, Quot.sound]
```

## Update 2026-11-01: M2 — `Thm11KappaAn` (A^♮, headline t = B(1/5,1/5)) in the TorInj-narrowed form
`LSG.W88.thm11KappaAn5 : MStarCopy.Thm11KappaAnOn 5 2 (·+1) perA5 perB5` and
`LSG.W88.thm11KappaAnK5 : MStarCopy.Thm11KappaAnKOn 5 2 (·+1) perA5 perB5 ∅` (`LSG/W88/AbVarMStarN*.lean`), standard
axioms, where `Thm11KappaAnOn` is exactly the narrowing proposed in M2.md §1.6 (`HyperplaneKappaOn (gmAn …) (TorInj (gmAn …))`).
Checked from lean_mstar 4d36ee3 against a scratch definition of the narrowed form over lean_mstar's own definitions:
```lean
theorem thm11KappaAn5_check : Thm11KappaAnOn 5 2 (fun s => (s : ℕ) + 1) perA5 perB5 := fun r b hb =>
  LSG.W88.thm11KappaAn5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩
```
Once lean_mstar narrows `Thm11KappaAn` (with `perAn_inj`, `hκN`), `two_three_beta5'` follows with this adapter.

## Update 2026-11-05: M2 narrowing landed (lean_mstar `8458732`)
`Thm11KappaAn`, `Thm11KappaAnK` are narrowed in lean_mstar and proved in `CM4E/Bridge/AbVar.lean` from `thm11KappaAn5`,
`thm11KappaAnK5`. The copies are re-synced: the names `Thm11KappaAnOn`, `Thm11KappaAnKOn` above are gone, now
`MStarCopy.Thm11KappaAn`, `MStarCopy.Thm11KappaAnK`. lean_mstar `b4f8018` removed `CM4E/Ext` and imports `LSG.Weierstrass`,
`LSG.Schneider` etc. directly, so renaming those lean_lsg modules breaks lean_mstar.
