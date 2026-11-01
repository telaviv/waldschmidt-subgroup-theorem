# Fidelity review: the TorInj narrowing of `Thm11KappaA` / `Thm11KappaAK` (lean_mstar ec4a5ab)

Reviewer: adversarial fidelity referee, 2026-10-31. I edited no files in either repo and changed no git state. I ran one
scratch check (`lake env lean`, in the session scratchpad, deleted afterwards). lean_mstar's working tree has unrelated
uncommitted SE₀ changes from another session; I left them alone.

**Overall verdict: CORRECT. No FATAL or MAJOR issue.** Three MINOR notes, all on the lean_lsg side, and two COSMETIC
notes, listed in §5.

---

## 1. Soundness of the narrowing — OK

**What changed.** `git show ec4a5ab` is the only commit involved; HEAD is ec4a5ab. Its changes:

* `Waldschmidt.lean` adds `HyperplaneKappaOn G good`. It is `HyperplaneKappa` verbatim, with the premise `good V`
  inserted after the quantifiers, and the lemma `HyperplaneKappa.on : HyperplaneKappa G → HyperplaneKappaOn G good`
  (`fun V W m y _ => h V W m y`). `HyperplaneKappa` itself is unchanged.
* `Gen/Frame.lean`:
  - `frame_false` is now a wrapper of the new `frame_false_of_good` with `good = fun _ => True`, via `hW.on`. Its
    statement is byte-identical to the old one, so the other consumers (MG, MGn, …) are unaffected.
  - New: `TorInj`, `snd_mem_span_perQ`, `torInj_ker_phiF`, `frame_false_on`.
* `Gen/Frame2.lean`: the same pattern. `frame2_false_K` keeps its statement; new `frame2_false_K_of_good`,
  `torInj_ker_phiG`, `frame2_false_K_on`.
* `AbVar/ThmA.lean`:
  - Only the body of `Thm11KappaA` changes. `gmA`, `perAgen`, `algA` and `thetaA` are untouched.
  - New lemmas `perA_poly` and `perA_inj`.
  - `fourExpAt_A` gains `hκN` and calls `frame_false_on`.
  - In the instances, the only change is that `(by decide)` is added at the call. The statements of
    `fourExpAt_beta5/7`, `two_three_beta5` and `fourExpAt_pi_div_beta5` are unchanged; they show only the hypothesis
    name, whose meaning narrowed.
* `AbVar/MGAK.lean`: only the body of `Thm11KappaAK` changes (`gmAK` is untouched). `mgA_K` gains `hκN` and calls
  `frame2_false_K_on`. `Thm11KappaAnK` is unchanged.
* `AbVar/CorA2.lean`: `corA2` gains `hκN`, and `corA2_beta5` passes `(by decide)`.
* `TRUST.md`: rows updated (accurate).

**Weaker, hence still a W88 consequence.** For every `r, b`, the new hypothesis is implied by the old one
(`HyperplaneKappa (gmA …)`, resp. `(gmAK …)`). I checked this in Lean:
`example … (h : ∀ r b, IsAdaptedBasisD … b → HyperplaneKappa (gmA N g κ P s₀ b)) : Thm11KappaA N g κ P s₀ :=
fun r b hb => (h r b hb).on` compiles, and so does the same for `Thm11KappaAK`. REFEREE_HYP_A and REFEREE_HYP_AK
already accepted the old statements as W88 §5d consequences for the genuine instances: `B(1/5,1/5)` (N = 5, g = 2,
κ = (1, 2)), `B(1/7,1/7)` (N = 7, g = 3, κ = (1, 2, 3)), and Cor A2 with `LA = ∅`. So the narrowed statements are also
true there. No model data changed, so no soundness fact in TRUST.md needs re-examination.

**Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of: `fourExpAt_beta5`,
`fourExpAt_beta7`, `two_three_beta5`, `fourExpAt_pi_div_beta5`, `corA2_beta5`, `perA_inj`, `frame_false_on` and
`frame2_false_K_on`. The `#print` of `Thm11KappaA`, `Thm11KappaAK`, `TorInj` and `HyperplaneKappaOn` matches the agreed
interface (PLAN.md, "lean_mstar TorInj interface") exactly.

## 2. Non-vacuity — OK

**(a) The concrete V″ satisfies TorInj, for the right V″ and the right `per`.**
* `frame_false_of_good` applies the hypothesis at exactly one site (Frame.lean, l. 399), with `good` discharged by
  `hgood`:
  `hW (LinearMap.ker (phiF θ lam s)) W _ y' hgood …`
* In `frame_false_on`, `hgood := torInj_ker_phiF θ algQ perQ lam s hper0`. Its type is
  `TorInj (gmF algQ perQ lam) (ker (phiF θ lam s))`.
* In `fourExpAt_A` this is instantiated with `algQ = algA g`, `perQ = perAgen N g κ P` and `lam = dotL (thetaA g s₀ b)`.
  That is definitionally `gmA N g κ P s₀ b`, which the kernel checked.
* `per` is `gmF.per = span_ℚ (perGen perAgen)`: `2πi` in each of the `2n` toric slots, plus `qv ''` the copies
  `[ζ^e]γ`. By ABVAR.md §1.2, for the genuine instances (`2g = φ(N)`, `H₁(A,ℚ) = F·γ`) this is the whole of
  `ℚ ⊗ Ker exp_G`.
* The MGAK side is the same. Frame2.l. 289 applies `hW (ker (phiG θ μ lam s)) … hgood`; `torInj_ker_phiG` is fed by
  `hper0`, and `mgA_K` proves `hper0` from `perA_inj` and `snd_mem_span_perQ`, with `μ = 0`. Here `per` is
  `span_ℚ (perGen perAgen)` again.

The mathematics is also right. A vector of `V″ ∩ per` with zero toric part is `qv q` with `q ∈ span_ℚ perAgen` and
`λ(q) = 0`; this holds for every `s`, since the `s`-term involves only the toric part.
* `perA_poly` writes `q(s, j) = P_s f_j(ζ^{κ_s})` with `f_j ∈ ℚ[X]`.
* `λ(q) = P_{s₀} Σ_j b_j f_j(ζ) = 0`, together with `P_{s₀} ≠ 0`, the reduction mod `Φ_N`, and the ℚ-independence of
  `θ(j, e) = ζ^e b_j`, gives `Φ_N | f_j`.
* Then `f_j(ζ^{κ_s}) = 0`, because `ζ^{κ_s}` is a primitive `N`-th root (`hκN`).

This is the `F`-independence argument of the `gmA` soundness note, and the Lean proof is sorry-free.

**(b) The hypothesis is genuinely used, not discharged trivially.** After `obtain ⟨S, …, hne, hle⟩`, both deductions
derive `False` from the conclusion. In the `T_L × 0` case a rational vector in V″ forces `s ∈ ℚ̄`; in the other case
`λ ≠ 0` (resp. `Ψ'' ≠ 0`) on `S ≤ V″`. The other premises at V″ are discharged from the counterfactual data:
* `finrank V″ + 1 = d` (`phiF` / `phiG` is onto);
* `W ≤ V″`, `W` is ℚ̄-rational;
* `y' ∈ V″ ∩ lam`: the `n` period lifts `tor1 h (2πi) + qv (qh h)` and the `2n` data lifts from `(X_k, sX_k)`;
* the count, with `κ ≥ n` from the period lifts and `d − 1 − t ≤ 1`.

So the hypothesis is applied at a hyperplane that satisfies `good` and all of `HyperplaneKappa`'s other premises; the
period lifts all have nonzero toric part, consistent with TorInj. TorInj is not contradictory with the remaining
premises: V″ is a hyperplane satisfying it, and `HyperplaneKappaOn G TorInj` is not of the form
`HyperplaneKappaOn G (fun _ => False)`. As with every W88 hypothesis here, the premises at V″ can hold only in the
counterfactual. That is expected and is not vacuity.

**(c) Is TorInj too strong for V″ anywhere? No. `hκN` is necessary for the Lean proof, and harmless.**
* Necessity [Proved, by hand]. Suppose `d = gcd(κ_s, N) > 1` for some `s` with `P_s ≠ 0` (this includes
  `κ_s ≡ 0 mod N`). Then `ζ^{κ_s}` is a primitive `N/d`-th root, so `Φ_N(ζ^{κ_s}) ≠ 0`. For `κ_s ≡ 0`,
  `Φ_N(1) ∈ {1, p} ≠ 0` for `N ≥ 2`. Take `q = Φ_N([ζ])γ` in copy `j`, i.e. `f_j = Φ_N`, which lies in
  `span_ℚ perAgen`. Then:
  - `λ(q) = P_{s₀} b_j Φ_N(ζ) = 0`, so `qv q ∈ V″` for every `s`;
  - `qv q ∈ per`, with toric part 0;
  - `q(s, j) = P_s Φ_N(ζ^{κ_s}) ≠ 0`.

  So TorInj(V″) fails. The claim in the brief is right.
* Harmless. For a genuine CM type, `[ζ]` acts on `T₀(A)` through embeddings `σ_k : ℚ(ζ_N) → ℂ`, which forces
  `k ∈ (ℤ/N)^×`. Equivalently, `Φ_N([ζ]) = 0` in `End⁰(A)` forces `P_s Φ_N(ζ^{κ_s}) = 0`, and `P_s ≠ 0`. So every
  genuine CM type satisfies `hκN`, and the instances discharge it by `decide`: `{1, 2}` for 5, `{1, 2, 3}` for 7. For
  non-genuine parameters the model was already unsound and the generic theorem possibly vacuous (REFEREE_HYP_A #5), so
  `hκN` costs nothing.
* The other ingredients, `P_{s₀} ≠ 0` (from `hT`) and `hb`, are already premises. TorInj(V″) does not depend on `s`,
  `X_k`, `Y_k` or `LA`.

## 3. lean_lsg's planned proof under TorInj — OK at [Proof sketch] level, with MINOR interface notes

**(a) Inheritance [Proved, trivial].**
* TorInj is a property of the top-level `V`: the toric projection `π_T` is injective on `V ∩ per`.
* The engine reaches Prop 2.1 only through `Sec7*.lean` / `Prop61*.lean`, which take `ω` from `Y ∩ Per`. Here `Y` is the
  ℤ-span of the `y_i`, `Y ⊂ V`, and in Theorem 4.1 for `H′` the space is `Y′ = Y ∩ T_{H′}` (Sec7.l. 85;
  `exists_periods (Y ⊓ Per Ls)`).
* So every `Ω′` fed to Prop 2.1 is a subgroup of `V ∩ T_{H′} ∩ Per ⊂ V ∩ per`, and injectivity restricts.
* The transports to a standard model (`K5dTrans` pattern) are block-diagonal, with the torus `T_L ≅ G_m^{d₁′}` and
  `B ∼ A^s`. They map ℚ-periods bijectively and preserve "toric part = 0", so TorInj survives them.
* `κ` counts `Y ∩ per`, not `V ∩ per`. That is the smaller set, so it causes no gap.

**(b) ℂ-independence [Proved].**
* ℤ-independent `ω₁…ω_κ ∈ V ∩ per` are ℚ-independent, so their toric parts are ℚ-independent in `2πi ℚ^{2n}`.
* ℚ-independent rational vectors are ℂ-independent (rank is field-independent), so the `ω_i` are ℂ-independent in `V′`.
* Then `LSG.Aux.prop21Lin` (Tier 1′) applies with any linear coordinates on `V′`.
  - Its only period hypothesis is a common multiplier under shifts by `Σ k_i ω_i`.
  - For genuine periods of `G_m^{d₁′} × A^s` this is the usual theta automorphy factor, which is needed anyway (ABVAR
    §2, `QuasiPeriodicB`).
* **No form needs a discrete image on Ω′.** I grepped the lattice-adapted machinery (`exists_coordsV`, `per_coord`,
  `latA`, `prop21Lat`). It is used only in the Prop 2.1 layer: `PropG`, `PropGV`, `PropGVT`, `MonoV`, `Prop21Lat*` and
  `Prop21Gen*`. `Sec7*`, `LemmaU*` and `K5d*` do not use it. So the Tier-3 obstruction of STAGE_A5 §2 does not arise.

**(c) The parameter regime is compatible.** `prop21Lin` needs `r² log(R/r) ≤ U` and `b r² ≤ aU`. The current caller
(`Prop61`, with `r = ν²S` and `U = ν⁶Δ`) already supplies `c₁ r² log(R/r) ≤ U` and `D r² ≤ U` for `prop21_G`, so Tier 1′
asks for nothing more. STAGE_A5 R2 cites W83's Remark `U ≥ r log(R/r)`; that is `prop21B`'s form in adapted coordinates.
The coordinate-free `prop21Lin` uses `r²`, which is still fine (cosmetic).

**(d) A bonus for the engine [Proof sketch].** Under TorInj, `κ′ = rk(Ω′) ≤ dim_ℚ(Lie T_L ∩ 2πiℚ^{2n}) = d₁′`. So the
"(NR) fails" branch of the elliptic engine (`κ′ ≥ d₁′ + 2d₂′ − 1`, handled there by `corner_false`) cannot occur when
`B ≠ 0`, because `d₂′ ≥ 1`. The AbVar engine therefore needs no `corner_false` analogue for A-blocks. This is conditional
on the AbVar (NR) having the same shape.
* When `B = 0`, Roy's Theorem 1 is used, as now.
* When `H′ ⊂ 0 × A^r` (no torus), `κ′ = 0` and Prop 2.1 has no periods.

**MINOR notes:**
* **M1 (the bridge must match `per`).** TorInj is stated for the *model* `per = span_ℚ(perGen perAgen)`. lean_lsg's
  engine takes `ω ∈ Y ∩ Per_lsg`, where `Per_lsg` is its own period lattice (e.g. `ker exp` of the Mumford-chart `A`).
  The bridge must therefore either
  - prove `Per_lsg ⊂ ℚ·perAgen`: `ker exp` has rank `2g = φ(N)` and contains `ℤ[ζ]γ` of the same rank, so the ℚ-spans
    agree; or
  - run the engine with the period subgroup `Y ∩ gmA.per` throughout. That is legitimate, since a smaller period group
    only lowers κ, and the quotient counts `κ − κ″ ≤ rk(periods of G/H″)` hold for any subgroup of genuine periods.

  Without one of these, TorInj does not transfer. This is not a flaw in the lean_mstar statement.
* **M2 (only Theorem A and Cor A2 are covered).** The narrowing covers only `Thm11KappaA` and `Thm11KappaAK`.
  - `Thm11KappaAn` and `Thm11KappaAnK` (M2, `A^♮`) and `Thm11KappaX7` still quantify over all `V`.
  - The TorInj test for `gmAn` has not been run. There the fibre coordinate enters `λ`, so injectivity on the periods of
    `Q″` is a different statement (STAGE_A5 R3.3).
  - X7 provably fails Tier 2 (R2 T3).
* **M3 (verbatim copies).** If lean_lsg keeps verbatim `MStarCopy*` copies, rather than importing lean_mstar directly,
  `HyperplaneKappaOn` and `TorInj` must be copied verbatim too, with the `good V` premise in the same position.

## 4. Paper wording (suggested)

> For Theorem A (at `B(1/5,1/5)` and `B(1/7,1/7)`) and Corollary A2, the Lean development does not assume W88 §5d in
> full. It assumes W88 §5d for `G″ = G_m^{2n} × A^r` restricted to the hyperplanes `V` that are *toric-injective*: no
> nonzero element of `V ∩ (ℚ ⊗ Ker exp_{G″})` has zero `G_m^{2n}`-component, i.e. `V` contains no nonzero period of
> `A^r`. This is a special case of W88 §5d, so it is implied by the published theorem; nothing beyond W88 is assumed.
> It is also all the proofs use. The only hyperplane to which the hypothesis is applied is the frame hyperplane
> `V″ = Ψ″⁻¹(ℂ(1, s))`, and `V″` is toric-injective. This is proved in Lean from the `F`-linear independence of the
> basis `b` and the fact that each CM character `ζ ↦ ζ^{κ_s}` is a field embedding, which is the condition
> `gcd(κ_s, N) = 1`. The restriction is made because, for toric-injective `V`, every lattice of periods that occurs in
> Waldschmidt's argument is ℂ-linearly independent. So W83's Prop. 2.1 is needed only in its ℂ-independent form, and
> the several-variable interpolation estimate (Masser's Théorème A) is avoided in the formal proof of the hypothesis.

Do not phrase it as "we assume W88 §5d" without qualification next to the Lean theorem names: it is true but
over-claims what is assumed. The conservative direction would also be to say "we assume a special case of W88 §5d".

## 5. Issue list

| # | Severity | Item | Finding |
|---|---|---|---|
| 1 | OK | soundness | Only the two hypothesis bodies changed. They are weaker (`HyperplaneKappa.on`, Lean-checked), models and instance statements are unchanged, axioms are standard |
| 2 | OK | V″ ⊨ TorInj | `torInj_ker_phiF` / `torInj_ker_phiG` plus `perA_inj`, for exactly `gmA` / `gmAK`, with `per` = full ℚ-period span (genuine instances) |
| 3 | OK | non-vacuity | Unique `hW` application per frame, at V″ with `hgood`. Conclusion used for `False`; other premises from the counterfactual data |
| 4 | OK | `hκN` | Necessary: `gcd(κ_s, N) > 1` gives `qv(Φ_N([ζ])γ) ∈ V″`, nonzero with zero toric part. Satisfied by every CM type and discharged by `decide` |
| 5 | OK [Proof sketch] | lean_lsg plan | Inherited by every `V ∩ T_{H′}` and transports. Gives ℂ-independent `Ω′`, so Tier 1′ `prop21Lin`. Parameters compatible. (NR) corner case vacuous for `B ≠ 0` |
| 6 | MINOR | bridge | TorInj is relative to the model `per`. The lean_lsg bridge must show `Per_lsg ⊂ ℚ·perAgen` (rank argument) or run the engine on `Y ∩ gmA.per` |
| 7 | MINOR | scope | `Thm11KappaAn`, `AnK` and `X7` are not narrowed; `gmAn` TorInj not yet tested |
| 8 | MINOR | copies | Any `MStarCopy` of the A/AK hypotheses must include `HyperplaneKappaOn` and `TorInj` verbatim |
| 9 | COSMETIC | `Waldschmidt.lean` docstring | "Every conditional theorem of this project assumes `HyperplaneKappa G`" is now inexact for A/AK, which assume `HyperplaneKappaOn … TorInj` |
| 10 | COSMETIC | STAGE_A5 R2 | Tier 1 is cited with `U ≥ r log(R/r)`; the coordinate-free `prop21Lin` needs `r² log(R/r)`, which the engine already supplies |
