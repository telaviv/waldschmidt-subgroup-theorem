# Stage A4, Bézout layer: local-complete-intersection Bézout (B1–B4 done)

Implements B1–B4 of `ABVAR.md` §A0.5. Status (2026-10-31): **built, no sorry / axiom / native_decide;
axioms are `propext`, `Classical.choice`, `Quot.sound` only.** Nothing is committed yet.

## Files: new files in StrongSix only

The three files are in `schanuel/six_exp/lean/StrongSix/M2/`. No existing StrongSix file was edited, and none of
them is imported by `StrongSix.lean`, so StrongSix's main theorems and default build are unchanged.

Build: `lake build StrongSix.M2.LCIBlocks`. It is about 1 min warm. It builds the other two files as well.

| file | lines | content |
|---|---|---|
| `BezoutUnmixed.lean` | 245 | B1, the height lemma B1 needs, and `bezout` as a corollary |
| `LCI.lean` | 277 | `LocGen`, `LocCI`, B2, B3, and `bezout_locCI` |
| `LCIBlocks.lean` | 111 | B4: block assembly, height from `hdim`, `bezout_blocks` |

Axiom audit: a scratch file with `import StrongSix.M2.LCIBlocks` and `#print axioms` on every main theorem. Every
theorem printed `[propext, Classical.choice, Quot.sound]`.

## Statements

Notation: `A = MvPolynomial σ K`, and `hdata β D K I = (hdim, deg)`. Everything is in namespace `StrongSix.M2`
except the `Ideal.*` lemmas.

**B1** (`BezoutUnmixed.lean:134`):
```lean
theorem bezout_unmixed [Infinite K] (hD : ∀ i, 1 ≤ D i) {I₀ : Ideal A}
    (hU : ∀ l : List A, (I₀ ⊔ Ideal.ofList l).height = I₀.height + l.length →
      (I₀ ⊔ Ideal.ofList l).IsUnmixed)
    {F : Set A} (hFD : F ⊆ FLE K β D) (hJ : I₀ ⊔ Ideal.span F ≠ ⊤) :
    (hdata β D K (I₀ ⊔ Ideal.span F)).2 ≤ (hdata β D K I₀).2
```
* `bezout_of_bezout_unmixed` (`:236`) re-proves StrongSix's `bezout`, with its exact statement, from B1. This is the
  sanity check.
* **Gap in §A0.5, now filled.** "Generalise `height_append`" is not only bookkeeping. The original proof gets
  `ht(I_k + (P)) ≤ ht I_k + 1` from Krull's bound on the number of generators, and that bound is unavailable for
  `I₀ + (rs)`. The replacement is a CM-ring lemma:
  - `Ideal.height_le_height_add_one_of_mem_minimalPrimes_sup` (`:38`): if `p` is minimal over `q + (f)` with `q`
    prime, then `ht p ≤ ht q + 1`. The proof works in `R_p` and uses `primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim`
    from StrongSix's CM library, plus Mathlib's `map_height_le_one_of_mem_minimalPrimes`.
  - `Ideal.height_sup_span_singleton_le_of_isUnmixed` (`:76`) applies this to unmixed ideals.
  - `Ideal.height_sup_span_singleton_of_isUnmixed` (`:114`) gives equality when `f` avoids the minimal primes.

  It took about 90 lines. The plan itself is unaffected.

**Definitions** (`LCI.lean:43, 48`; any commutative ring):
```lean
def LocGen (J : Ideal R) (r : ℕ) : Prop :=
  ∀ p : Ideal R, p.IsPrime → J ≤ p → ∃ s ∉ p, ∃ l : List R, Ideal.ofList l ≤ J ∧
    (∀ x ∈ J, s * x ∈ Ideal.ofList l) ∧ l.length ≤ r
def LocCI (J : Ideal R) : Prop := ∃ r : ℕ, LocGen J r ∧ (r : ℕ∞) ≤ J.height
```
This differs from §A0.5, which quantifies over maximal ideals and requires `length = ht J`. It is equivalent, but
easier to use:
* Primes, because comaps of primes are primes (needed for `LocGen.map`). `LocGen.of_maximal` (`:57`) recovers the
  maximal-ideal form.
* `≤ r` with a separate `r ≤ ht J`, so that B5 can establish `LocGen` *before* the height is known.
  `LocGen.height_le` (`:150`, a local Krull bound) gives `ht J ≤ r` for free.

**B2** (`LCI.lean:174`, alias `unmixed_of_localCI` at `:240`):
```lean
theorem LocCI.isUnmixed [IsNoetherianRing R] [IsCohenMacaulayRing R] {J : Ideal R} (h : LocCI J) : J.IsUnmixed
```
* The proof follows the pattern of StrongSix's `isCohenMacaulayRing_iff_unmixed` (CM/Unmixed.lean). At an associated
  prime `p`, `J R_p = (l) R_p` has height `length l`; `l` is regular in the CM local ring `R_p`; associated primes of
  the CM quotient are minimal; hence `ht p = ht J`.
* Mathlib already had everything for associated primes under localisation, so the ≈150-line contingency in §A0.5 was
  not needed.

**B3** (`LCI.lean`):
* `LocGen.sup_ofList` (`:143`): `LocGen J r → LocGen (J ⊔ ofList l) (r + l.length)`.
* `LocCI.sup_ofList` (`:246`): `LocCI J` and `ht(J ⊔ ofList l) = ht J + l.length` imply `LocCI (J ⊔ ofList l)`.
* `hU_of_locCI` (`:253`): `LocCI I₀ →` the hypothesis `hU` of `bezout_unmixed`.
* `bezout_locCI` (`:272`): `LocCI I₀ → deg_D (I₀ ⊔ span F) ≤ deg_D I₀`.

**Closure and certificate lemmas** (`LCI.lean`):
* `locGen_ofList` (`:80`), `LocGen.sup` (`:88`, additive, with no disjointness needed), `LocGen.biSup` (`:104`, finite
  sums), `LocGen.map` (`:124`, along any ring hom, e.g. `rename`), `LocGen.mono`.
* **`LocGen.of_cover`** (`:66`):
  - Given local systems `(s i, l i)` with `ofList (l i) ≤ J`, `s i • J ⊆ (l i)` and `length ≤ r`, and given
    `J ⊔ span (range s) = ⊤`, conclude `LocGen J r`.
  - This is exactly the shape of the B5 certificates.

**B4** (`LCIBlocks.lean`): the form the ME consumes. Here `I = ofList l ⊔ ⨆ k ∈ t, (J k).map (rename (e k))`, where
the `J k ⊆ K[τ k]` are the block ideals and `l` collects the CI generators (G_a/G_m/E parts, slicing forms).
* `locGen_blocks` (`:43`): `(∀ k ∈ t, LocGen (J k) (r k)) → LocGen I (l.length + ∑ k ∈ t, r k)`.
* `LocGen.height_eq_of_hdim` (`:53`): `LocGen I r`, `I ≠ ⊤`, and `hdim I + r ≤ card σ` imply `ht I = r` and
  `hdim I + r = card σ`.
* `locCI_of_hdim` (`:67`) and `locCI_blocks` (`:75`): `I` is LocCI, with `ht I = l.length + Σ r k`, i.e. heights add.
* `bezout_locGen` (`:91`) and **`bezout_blocks`** (`:100`): `deg_D (I ⊔ span F) ≤ deg_D I`, given `hdim I + (l.length
  + Σ r k) ≤ card σ`, `F ⊆ FLE`, and `I ⊔ span F ≠ ⊤`.

How heights add: there is no separate lemma "heights add over disjoint variables". The ME already proves `hdim(sl α
I_G) ≤ Σ dim` from its product Hilbert-function bound (`hdata_slIG`, `hfun_slIG_le`). `LocGen.height_le` replaces the
global Krull bound (`hlow`, i.e. `ht ≤ #generators`), and the two together give `ht = r` and `hdim = card σ − r`. Check
for the abelian-surface case: `hdim ≤ d₀ + d₁ + m_E + 2m_A` and `r = d₁ + 2m_E + 7m_A`, so `hdim + r = d₀ + 2d₁ + 3m_E
+ 9m_A = card σ`.

## What B5–B7 still need

* **B5 `locGen_slA : LocGen (sl α I_A) 7`** in the 9 slice variables, via `LocGen.of_cover`, with `l i = [F_{i,1..6},
  ℓ − 1]`. Inputs:
  - membership certificates `S_i·Q_j ∈ (F_i)` and `S_i·C_j ∈ (F_i)` (`loc_ci_modp.py`; cofactors of degree 3–4 for
    about 3 choices of `F_i`), checked by `linear_combination` or a kernel checker;
  - `s i = S_i`, plus a cover certificate `sl α I_A ⊔ span{S_i} = ⊤`.

  The cover is cleanest in projective form, `x_v^N ∈ I_A + (S_i)` for every coordinate `v`. A generic lemma
  (≈100–150 lines) is then needed: on the slice `ℓ = 1`, `ℓ^M ∈` the ideal generated by the `x_v^N`, so `1 ∈ sl α I_A
  + (S_i)` for every α. This keeps the certificates independent of α.

  Dehomogenisation of the membership identities follows `Slice.hom_mem_vanish_of_mem_sl` and `SliceDim.homP`.
  Estimate: **300–550 lines + generated data**, unchanged apart from the cover lemma.
* **B6 `hfun_slA_le`, `hdata_slA`**: unchanged, **400–700 lines**.
  - Only the *upper* bound on `hfun` (standard monomials over a Gröbner basis of `I_A`) is needed, which gives
    `hdim ≤ 2` per block.
  - The `hdim ≥ 2` direction no longer needs a separate Krull argument: `LocGen.height_eq_of_hdim` supplies it from B5.
* **B7, MainAb / BlockData adaptation**: **100–200 lines** (unchanged).
  - Write `sl α I_G` in the block form `ofList l ⊔ ⨆ k, (sl-block k).map (rename (e k))`.
  - Replace `StrongSix.M2.bezout … (height_slIG …)` by `bezout_blocks` (or `bezout_locGen`).
  - Replace `hdata_slIG`'s Krull lower bound `hlow` by `LocGen.height_le`.
  - The E/G_m blocks enter through `locGen_ofList`, so the existing `lGs` lists reuse as is.
  - lean_lsg imports `StrongSix.M2.LCIBlocks` directly, since it is not in `StrongSix.lean`.
* **Revised B-layer total.**
  - B1–B4 came to 633 lines, against the 1050–1700 estimated.
  - B5–B7 remain at **800–1450 lines + B5 data**.
  - The whole B layer is ≈ 1.45–2.1k, inside the 1.9–3.2k of §A0.5 or below it.
