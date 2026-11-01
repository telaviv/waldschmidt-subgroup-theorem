# STAGE A1 / A1c: the algebraic Jacobian of `C : y² = 4x⁵ + 1` (genus 2) in Lean

Written 2026-10-31. Companion to `ABVAR.md` §2.2 a1, §5 and the "A0 results" section; coordinates with `STAGE_A2.md`
(§5 of that file is answered in §6 below). Labels as in ABVAR: [Proved] = Lean, standard axioms; [Numerical] =
exact/mod-p computer algebra outside Lean; [Design].

**Status (checkpoint 3 = §9: W4rel, law0_neg, dup_origin, dup_onQ, glue, mkA1Facts; E1/E2 and P2 pending. Checkpoint 2, 2026-10-31; checkpoint 1 = commit 872f3dc; nothing added to `LSG.lean`/`Axioms.lean`):**
* **New since checkpoint 1** (details in §8):
  - **F1 certified** (`Flow.lean`, `flow_inv`: 18 flow-invariance identities), with the formal partial derivatives
    `dXsp`/`dYsp` and their calculus meaning **`hasDerivAt_evalSP`** (+ `law_decOK`) in `Deriv.lean`.
  - **V1 memory fixed**: peak 9 GB → **3.2 GB** (recursor-based checker, −40% memory and ≈ 3× faster; identities
    with more than 3 products split over two declarations, `CheckerSplit`/`SplitSound`). Every heavy check is now
    ≤ 3.3 GB (§8.3).
  - **S1, S2 certified** (`Sym.lean`: `law_S1`, `law_S2`, all 81 coordinates, exact data identities).
  - Checker generalised to **two tables** (`sound2`, `sound2V`: different `X`- and `Y`-side tables, needed for
    bidegree (5,4)).
  - `A1Facts` (STAGE_A2 §7): field status and plan in §8.4; **P2 (`dup_ne_zero`) assessment in §8.5**.
* Checkpoint 1 items (unchanged): A1c checker + soundness, 64 V2′ + 9 V1 certified, Mumford chart, Grant map into
  `V(Q)`, quadrics, `[−1]`, `μ₁₀`, origin, `law0_origin`, `dup`. G1 measured and replaced by the flow route (§4).
* All audited theorems print `[propext, Classical.choice, Quot.sound]` (or fewer); no `sorry`, `axiom`,
  `native_decide`; kernel checks by `decide +kernel` only.

---------------------------------------------------------------------------------------------------------------------

## 1. Files (`LSG/Jac/`, namespace `LSG.Jac`)

| file | lines | content |
|---|---|---|
| `Kron.lean` | 108 | signed-digit uniqueness `digits_eq_zero`, `kron_zero`, `sum_fiber` (generic, Mathlib) |
| `Checker.lean` | 194 | **computational part only** (imports just `Mathlib.Tactic.Linter.Header`, so kernel checks run without Mathlib in memory): codes, `Leaf`/`T` table, `SP`, `Term`, signed Nat pairs, accumulator tree `AT`, `yprod`, `addRow`, `prodNF`, `evalO`, `wsum`, `pairOK`, `termOK`, `SP.wf`, `leafOK`; NF-certificate checker `nfTerms`, `nfPack`, `nfEntryOK`, `nfAllOK` |
| `CheckerSound.lean` | 577 | semantics (`xmono`, `evalRow`, `evalNF`, `evalSP`, `evalTerms`), the formal expansion `G`, and **`sound_bidegree`** |
| `NFSound.lean` | 132 | **`nfEntry_sound`, `nfValid_of_check`**: a checked table is a valid normal form on `V(Q)` |
| `TableFacts.lean` | 48 | kernel checks of the generated degree-4 table: `leaves_ok`, `nf_ok`; `Qe`, `OnQ`, **`nfValid`** |
| `Laws.lean` | 54 | `A32 k m x y = 32·A_k^{(m)}(x,y)`, `lawPt`, `dup`, `natCast_isUnit`, **`identity_of_check`** |
| `Model.lean` | 212 | explicit `quad`, `Qe_eq`, `onQ_iff`, `origin`, `negP`, `muP`; chart `chartR1/0`, `OnChart`, `fC`, `aPoly`, `bPoly`, `mumford_div`, **`mumford_dvd_iff`**, `grantZ`, **`grantZ_onQ`**, `grant`, `grant_onQ`, `grant_zero`, `grant_chart`, `negC`, `muC` (+ invariance lemmas) |
| `Origin.lean` | 96 | `ySlice`, `originOK`, `evalSP_origin`, **`law0_origin`**, `lawPt0_origin` |
| `V2.lean` (generated) | 506 | `rank_one_k_m` (64) and **`rank_one`** |
| `V1.lean` (generated) | 120 | `law0_quad_j` (9) and **`law0_onQ`** |
| `Cert/V2k1..8.lean` (generated) | 8 × 86 | raw kernel checks `v2_k_m_{O,B,T}` (core-only imports) |
| `Cert/V1.lean` (generated) | 95 | raw kernel checks `v1_j_{O,B,T}` |
| `Data/Table.lean` (generated) | 1094 | 495 leaves (key, idx, NF row scaled by 23040, packing `ky`), `stdc`, `keys`, `deg2`, `Qd`, `kb = 79`, `rowM` |
| `Data/NFCert.lean` (generated) | 542 | 495 cofactor certificates (9.3k terms) |
| `Data/Laws.lean` (generated) | 3108 | the 81 law coordinates (8235 terms), `law k m` |

Hand-written Lean: ≈ 1.42k lines. Generated: 0.63k semantic + 0.78k raw checks + 4.7k data.

Generators (untrusted Python, `scripts/jac/`): `gen_jac_data.py` (table, certificates, laws; reads
`scripts/abvar_spike/{ideal,laws_Q}.json`), `gen_jac_ids.py` (raw check files + `V1.lean`/`V2.lean`),
`chart_cofactors.py` (cofactors used in `Model.lean`), `sim_checks.py` (Python mirror of the NF check),
`g1_measure.py`, `e1_check.py` (§4 measurements), `build_certs.sh` (builds the raw checks two at a time),
`runwatch.ps1` (time + peak memory of one `lake env lean`).

Build: `export PATH="$HOME/.elan/bin:$PATH"; lake build LSG.Jac.V2 LSG.Jac.V1 LSG.Jac.Origin LSG.Jac.Model`
(use `scripts/jac/build_certs.sh` first to keep at most two heavy checks running; see §2.4 for memory).

---------------------------------------------------------------------------------------------------------------------

## 2. The checker (A1c) [Proved]

### 2.1 Encoding
* Monomial `X^e` (9 variables, `e_i < 8`) ↔ code `Σ e_i 8^i`; `xmono x c = ∏ x_i^{digit c i}`;
  `nocarry a b` (decidable) ⇒ `xmono x (a+b) = xmono x a * xmono x b` (`xmono_add`).
* `SP` = rows `(α, [(β, |c|, sign)])` = `Σ_α X^α Σ_β ±c Y^β`, plus a list `yc` of the `Y`-codes (`SP.wf`).
* Table leaf: `key` (degree-4 code), `idx`, `row` = `δ·NF(X^key)` as `[(std slot s < 144, |v|, sign)]`
  (`δ = 23040`), `ky = Σ ±v 2^{b s}` (`b = kb = 79`).

### 2.2 The computation (`evalO`)
For an identity `Σ_q ±c_q a_q(X,Y) b_q(X,Y)` of bidegree (4,4): for every pair of rows `(α, α')`, the inner loop
`yprod` computes `Σ_{β,β'} ±c c' ky(β+β')` (the `Y`-side normal form packed into one 11.4-kbit integer), and `addRow`
adds `±c_q · NF(α+α')_s · inner` to slot `s` of an accumulator tree `AT` (256 slots, depth 8). The check is
`(evalO nfTree ps).allZero = true`. The `X`-side is **not** packed: an earlier fully packed variant (ABVAR's two-level
Kronecker, 1.7-Mbit numbers) needed 6.1 GB per identity; the slot tree keeps every intermediate at `N·b` bits.

### 2.3 Soundness
```
theorem sound_bidegree (tr : T) (stdc : List ℕ) (N b M δ : ℕ) (hN : N ≤ 2 ^ 8)
    (hleaf : ∀ l ∈ tr.leaves, leafOK N b M l = true) (ps : List Term)
    (hO : (evalO tr ps).allZero = true) (hB : wsum ps * M ^ 2 < 2 ^ b)
    (hT : ∀ q ∈ ps, termOK tr q = true ∧ q.a.wf = true ∧ q.b.wf = true)
    (x y : Fin 9 → R) (hx : NFValid tr stdc δ x) (hy : NFValid tr stdc δ y) :
    (δ : R) ^ 2 * evalTerms x y ps = 0          -- any commutative ring R
```
Proof: both the slot values and `δ²·value` are images of one formal expansion `G` over the flat list of term products;
slot `s` equals `Σ_t D_{s,t} 2^{bt}` with one integer matrix `D` and `|D_{s,t}| ≤ wsum·M² < 2^b`, so `D = 0` by
`digits_eq_zero`; the value is `Σ_{s,t} D_{s,t} x^{std s} y^{std t}`.
`nfValid_of_check` + `nf_ok` give `NFValid` at every point of `V(Q)` (over any commutative ring); the certificate for
leaf `μ` is `δX^μ − NF(μ) − Σ_j c_j Q_j = 0`, checked by packing over the leaf index (`B = 32` bits, 495 slots).
`identity_of_check` packages this for `ℚ`-algebras (`δ²` is a unit). Taking `R = ℚ[X,Y]/(I(X) + I(Y))` turns every
certified identity into ideal membership, so the ideal-theoretic and pointwise statements are the same theorem.

### 2.4 Timings and memory (Windows, 32 threads, shared machine, ±20%) — checkpoint 1; superseded by §8.2–8.3
| item | wall | peak RSS |
|---|---|---|
| `Data/*.lean` (elaboration; data are `noncomputable def`: the compiler otherwise takes > 10 min) | 17–43 s each | < 1 GB |
| `TableFacts` (`leaves_ok` + `nf_ok`) | 104–112 s | not measured (small checks; Mathlib loaded) |
| one V2′ identity (`_O`, `_B`, `_T`), raw file | 22 s alone; 29–35 s with 2 files in parallel | **3.3 GB** |
| `Cert/V2k*` (8 identities each), 2 files in parallel | 232–279 s per pair | ~3.3 GB each |
| `Cert/V1` (9 identities, 3–5 products each, 36 products) | 607 s | **≈ 9 GB** (over budget) |
| semantic files `V1`, `V2`, `Origin`, `Model` | 30–45 s each | ~3 GB |
Cold build of `LSG/Jac` ≈ 30 min wall with two parallel checks, ≈ 55 CPU-min (ABVAR estimated 45–55 CPU-min).
Memory scales with the number of products per declaration (≈ 1.5 GB/product). **Fixes** (measured): defining
`T.find` and the folds through recursors instead of structural recursion saves 30–40% memory and ≈ 30% time
(scratch test); for `V1`, split each identity into declarations of ≤ 2 products (intermediate accumulator as a
literal), or drop `V1` altogether, since the route recommended in §4 does not use it.
A false claim is rejected: `(evalO nfTree [⟨1, false, L41, L00⟩]).allZero = false` is provable (scratch).

---------------------------------------------------------------------------------------------------------------------

## 3. What is proved [Proved]

All over an arbitrary commutative ring `R` unless stated; "`ℚ`-algebra" means `[CommRing R] [Algebra ℚ R]`.

* **`rank_one`** (`V2.lean`): `∀ k m : Fin 9, OnQ x → OnQ y → A32 k m x y * A32 0 0 x y = A32 k 0 x y * A32 0 m x y`
  (ℚ-algebras). 64 kernel checks + trivial cases.
* **`law0_onQ`** (`V1.lean`): `OnQ x → OnQ y → OnQ (lawPt 0 x y)` (ℚ-algebras). 9 kernel checks.
* **`law0_origin`** (`Origin.lean`): `A32 k 0 x origin = -8 * x 0 * x k`, identically (so `A^{(0)}(x, O) = −(x₀/4)x`).
* **Model** (`Model.lean`): `Qe_eq` (data quadrics = explicit `quad`), `onQ_iff`, `origin_onQ`, `negP_onQ`,
  `muP_onQ` (`t¹⁰ = 1`), **`mumford_div`** (`f − b² = a·q + (r₁x + r₀)`), **`mumford_dvd_iff`** (fields:
  `aPoly p ∣ fC − bPoly p ^ 2 ↔ OnChart p`), **`grantZ_onQ`** (chart ⊂ model, integer form `4·X(p)`),
  `grant_onQ` (`[Field K] [CharZero K]`, `X₀ = 1`, `grant_zero`), `grant_chart` (`s₁ = X₃`, `s₂ = −X₂`, `b₁ = X₇`,
  `b₀ = X₆`), `negC_onChart`, `grantZ_negC` (S-neg), `muC_onChart`, `grantZ_muC`.
* `dup x = lawPt 4 x x` (definition only).

Not yet in Lean: (S1) `A_k^{(m)}(X,[−1]Y) = A_m^{(k)}(X,Y)` and (S2) as data identities (planned: a `flipY` on `SP` +
`decide`, ≈ 0.2k lines); the boundary `X₀ = 0` ↔ degree `< 2`; "affine part of `V(Q)` = image of the chart".

---------------------------------------------------------------------------------------------------------------------

## 4. G1: measurement, and the recommended replacement

### 4.1 G1 as specified (law 0 vs Cantor on chart × chart) [Numerical, `g1_measure.py 1`, `g1_part1.out`]
Cantor sum `R = P + Q` (CRT cubic, one reduction), compared with `A_k^{(0)}(X(P), X(Q))` (`k = 3, 2, 7, 6`):

| coordinate | Cantor num / den (terms, unreduced) | identity `E` (terms, total degree) | term-pairs to form `E` |
|---|---|---|---|
| `s₁` | 88 / 34 | 5,696 (15) | 24,212 |
| `s₂` | 115 / 34 | 7,232 (16) | 31,116 |
| `b₁` | 3,902 / 1,043 | 84,184 (23) | 1,054,036 |
| `b₀` | 4,920 / 1,043 | 103,308 (24) | 1,287,840 |

Pulled-back law 0: 160–480 terms per coordinate (`g1_proxy` said 160–722). All four `E` vanish at random chart pairs
mod p. These are identities **modulo the chart ideal in 8 variables**, so they also need cofactor certificates and a
different (8-variable) checker; dense Kronecker packing in 8 variables is infeasible (10⁶–10⁷ slots). **Verdict:
`s₁, s₂` feasible, `b₁, b₀` not at reasonable cost.** (With `s₁, s₂` alone plus V1, the `b`'s of the law-0 output
are determined only up to the four sign choices `±y₁, ±y₂`.)

### 4.2 Replacement: flow / equivariance identities [Numerical, `g1_part2.out`, `e1_check.py`]
The invariant vector fields `∂/∂z_j` (A2's `odeVF`, `z₀, z₁` = Grant's `u₁, u₂`) act on Grant's affine coordinates by
`∂_j X̂_i = W_{ji}(X̂)` with **quadratic** `W` (interpolated mod p, rationally reconstructed, `flow_W.json`):

| `i` | `W_{1i}` | `W_{2i}` |
|---|---|---|
| 1 | `X₀X₄` | `X₀X₅` |
| 2 | `X₀X₅` | `X₀X₆` |
| 3 | `X₀X₆` | `X₀X₇` |
| 4 | `−3X₀X₃ + 6X₁²` | `−X₀² + 6X₁X₂` |
| 5 | `−X₀² + 6X₁X₂` | `4X₀X₈ + 6X₁X₃` |
| 6 | `4X₀X₈ + 6X₁X₃` | `−2X₀X₁ + 6X₂X₃` |
| 7 | `−2X₀X₁ + 6X₂X₃` | `4X₀X₂ + 6X₃²` |
| 8 | `−3X₁X₆ + 3X₂X₅` | `−½X₀X₄ − (3/2)X₁X₇ + (3/2)X₂X₆` |

(`W₂₇` is A2's `∂b₁/∂z₁ = 6s₁² − 4s₂`: consistent.) Two families of identities on `A × A`, all verified at random
pairs mod p:
* **(F1) flow invariance**, bidegree **(4,4)**, 18 identities (`j = 1,2`, `l = 0..8`):
  `B·G_{jl} − 3·G_{B,j}·A_l^{(0)} ∈ I(X) + I(Y)`, `G_{jl} = Y₀ Σ_i ∂A_l/∂X_i W_{ji}(X) − X₀ Σ_i ∂A_l/∂Y_i W_{ji}(Y)`,
  i.e. `A_l^{(0)}(X̂,Ŷ)/B³` is constant along `(u,v) ↦ (u + t e_j, v − t e_j)`. Sizes: `G_{jl}` 198–377 terms,
  `G_B` 6 terms: ≈ 2k term-pairs per identity if `G_{jl}` is stored as data (then its relation to `A_l`, `W` needs
  its own exact check), ≈ 15–20k if expanded in the kernel as `Σ_i (B·Y₀·W_{ji}(X))·∂A_l/∂X_i − …` (≈ one V2′).
  Same checker, same table.
* **(E1) equivariance in the first argument**, bidegree **(5,4)**, 16 identities (`j = 1,2`, `l = 1..8`):
  `A_0 D_jA_l − A_l D_jA_0 = X₀ W_{jl}(A^{(0)})` with `D_j = Σ_i W_{ji}(X) ∂/∂X_i`, i.e. `∂_u Ẑ(u,v) = W(Ẑ)` for
  `Ẑ = A^{(0)}/A_0^{(0)}`. ≈ 20–25k term-pairs + `W(A)` per identity (≈ 2× V2′); needs a degree-5 normal-form table on
  the `X`-side (1287 monomials, 225 standard; the tree has 256 slots, so the checker is unchanged).

**How they replace G1.**
* *Global (A3, the ψ-argument of ABVAR §A0.3):* with `θ` the entire lift, (F1) says `[A^{(0)}(θ(u),θ(v))]` is
  constant along antidiagonals, so it equals its value at `v = 0`, which is `[θ(u+v)]` by **`law0_origin`**. This is
  exactly "column 0 ∝ θ(u+v)", the only use of G1 in §A0.3; `rank_one` then gives every column, and `dup ∝ θ(2u)`
  follows on the diagonal by the identity theorem. V1 is not needed.
* *Local (A2, a4) [Heuristic]:* (E1) + A2's `localExp_ode` + uniqueness of ODE solutions should give
  `law0(Ψ(u+w), P) ∝ Ψ'(z'+w)` for the local exponentials `Ψ, Ψ'` (law 0 is translation-equivariant), with no Cantor
  and no Abel step. Not checked in detail; A2 to confirm.
* Recommended order: (F1) first (cheap; needs `SP` products and formal partial derivatives with their semantics,
  ≈ 0.4–0.6k lines, ≈ 10 CPU-min of checks), (E1) if A2 keeps the local design (degree-5 table ≈ 0.3k lines + data,
  ≈ 20–30 CPU-min).

---------------------------------------------------------------------------------------------------------------------

## 5. Model facts, and the primality checkpoint [Design]

* §A0.1 dimension facts (`dim S_d/I_d = 9d²`, `(Q)_4 = I_4`) stay [Proved by computer algebra] outside Lean. The
  Lean table gives, as a by-product, the **upper bound** `dim (S/(Q))_4 ≤ 144` (every degree-4 monomial reduces to the
  144 standard ones, `nf_ok`). That is the `d = 4` case of the Hilbert-function bound B6 needs (`H ≤ 9(tD)² + O(t)`);
  general `d` needs a Gröbner basis (quadrics + 3 cubics) and belongs to A4/B6.
* **Primality of the P⁸ ideal: not needed in Lean; do not prove it.** The ME of A0.5 uses (i) an upper bound for
  the Hilbert function of the sliced ideal (B6), (ii) local complete intersection (B5) for unmixedness, (iii) the
  identification of points `V(I) = exp(ℂ²)` (A2 surjectivity + the boundary computation). [Heuristic] Unmixedness
  plus (iii) give everything primality would (the top-dimensional components are the translates the ME counts); to be
  confirmed against the A4 Bézout write-up. Replace the ABVAR
  checkpoint "P⁸ ideal prime, chart ⊂ model" by **"chart ⊂ model (`grantZ_onQ`) + Hilbert upper bounds + points =
  exp(ℂ²)"**.
* Still to do for (iii): every point of `V(Q, cubics)` with `X₀ ≠ 0` is `grant p` of a chart point (needs the 3 cubics,
  since the quadrics alone determine `X₁` only where `X₅ + X₂X₇ ≠ 0`), and the `X₀ = 0` points are classes of degree
  `< 2`.

---------------------------------------------------------------------------------------------------------------------

## 6. Interface for A2 (answers `STAGE_A2.md` §5)

| A2 asks | A1 provides |
|---|---|
| `grantEmb : (Fin 4 → ℂ) → (Fin 9 → ℂ)`, `X₀ = 1` | `LSG.Jac.grant` (`[Field K] [CharZero K]`), `grant_zero`, `grant_chart`; integer form `grantZ = 4·grant` |
| `chartRel m ↔ (X² − C s₁ X + C s₂) ∣ f₅ − (C b₁ X + C b₀)²` | `OnChart p` (`chartR1 p = 0 ∧ chartR0 p = 0`), `mumford_dvd_iff : aPoly p ∣ fC - bPoly p ^ 2 ↔ OnChart p` with `aPoly p = X^2 - C (p 0) * X + C (p 1)`, `bPoly p = C (p 2) * X + C (p 3)`, `fC = C 4 * X ^ 5 + 1` (A2's `f₅ = C 4 * X^5 + C 1`; `C 1 = 1` by `map_one`) |
| `quad j (grantEmb m) = 0` | `quad X j` (argument order `X` first), `grant_onQ : OnChart p → OnQ (grant p)`, `onQ_iff : OnQ x ↔ ∀ j, quad x j = 0` |
| `law`, `dup`, `neg` | `A32 k m x y` (= 32·A_k^{(m)}), `lawPt m x y : Fin 9 → R`, `dup x = lawPt 4 x x`, `negP` |
| S-neg | `grantZ_negC : grantZ (negC p) = negP (grantZ p)` |
| S-Cantor, S-G1, S-dup | **not provided**; see §4: replaced by `law0_origin` + `rank_one` + (F1)/(E1) (next step) |
| analyticity of the polynomial maps | `evalSP` is a finite sum of monomials `∏ x_i^{d_i}`; a one-line `AnalyticAt` lemma per use (not yet written) |

---------------------------------------------------------------------------------------------------------------------

## 7. Revised estimates

| item | ABVAR A0.6 | now |
|---|---|---|
| A1c checker + soundness + table | 1.5–2.5k + data | **done: 1.06k hand-written** (Kron, Checker, CheckerSound, NFSound, TableFacts) + 4.7k data; 64 V2′ + 9 V1 certified |
| A1 done so far | — | 0.36k (Model, Origin, Laws) + 0.63k generated semantics |
| A1 remaining | 5–8k total | **2–3.5k**: (F1) 0.4–0.6k; (E1) 0.3–0.5k + data; (S1)/(S2) 0.2k; affine part of `V(Q)` = chart (cubics) 0.3–0.6k; boundary `X₀ = 0` 0.5–1k; analyticity glue 0.1k; recursor-based checker (memory) 0.2k |
| G1 | 4 × ~60 s (guess) | 4 identities of 24k–1.3M term-pairs **mod an 8-variable ideal**: replaced by (F1) 18 × ~5 s, or (E1) 16 × ~60 s |
| CPU | 45–55 min | 55 CPU-min measured for V2′ + V1 + table; +10–30 min for (F1)/(E1) |

**Next concrete steps:** (1) (F1) certificates: `SP` product and formal `∂/∂X_i`, `∂/∂Y_i` with evaluation lemmas,
generator from `flow_W.json`; (2) recursor-based `T.find`/folds and splitting of `Cert/V1` to get every check under
4 GB; (3) (S1)/(S2) by `decide` on data; (4) (E1) with a degree-5 table if A2 confirms the local design.

---------------------------------------------------------------------------------------------------------------------

## 8. Checkpoint 2 (F1, V1 memory, S1/S2, two-table checker; A1Facts plan; P2)

### 8.1 New and revised files (`LSG/Jac/`)
| file | lines | content |
|---|---|---|
| `Checker.lean` (rev.) | 215 | hot functions via recursors + `cond`/`Nat.blt`/`Nat.beq` (`lfold`, `T.find`, `AT.get/addAt/allZero`); two tables: `evalFrom trX trY`, `evalO2`, `termOK2`, `leafOKX`; `evalO tr = evalO2 tr tr` |
| `CheckerSound.lean` (rev.) | 667 | equation lemmas (`lfold_eq`, `T.find_node`, `AT.get_node`, …), **`sound2V`** (hypothesis: all slots zero), **`sound2`**, `sound_bidegree` (one table, as before) |
| `CheckerSplit.lean` / `SplitSound.lean` | 30 / 84 | split certificates: `slotsEq (evalO2 … ps₁) L`, then `(evalFrom … (AT.ofList L) ps₂).allZero`; **`evalO2_split`**, `evalFrom_spec` |
| `CheckerDeriv.lean` / `Deriv.lean` | 42 / 176 | `dXsp`, `dYsp`, `decOK`; **`hasDerivAt_xmono`, `hasDerivAt_evalSP`** (along curves in `𝕜⁹`, any nontrivially normed field), `evalSP_dX`, `evalSP_dY`, **`law_decOK`** |
| `CheckerSym.lean` / `Sym.lean` | 45 / 105 | `flat`, `s1OK`, `s2OK` (structural insertion sort); **`law_S1`**: `A32 k m x (negP y) = A32 m k x y`; **`law_S2`**: `A32 k m x y = (if lawEps m then −1 else 1) * A32 k m y x` (`ε_m = +1` iff `m ∈ {4,…,7}`); any commutative ring |
| `Laws.lean` (rev.) | 73 | + `identity_of_check_split` |
| `Data/Flow.lean`, `Cert/F1j0.lean`, `Cert/F1j1.lean`, `Flow.lean` (generated by `scripts/jac/gen_jac_flow.py`) | 49 / 250 / 250 / 399 | F1 data (`B·Y₀·Wn(X)`, `B·X₀·Wn(Y)`, `G_B`), 18 raw checks, **`flow_inv`** |
| `Cert/V1.lean` (regenerated) | 136 (2.3 MB) | Q₃ split 2+2, Q₅–Q₈ split 3+2, with literal intermediate slot lists (`scripts/jac/slots.py`) |

```
theorem flow_inv (j : ℕ) (hj : j < 2) (l : Fin 9) (x y : Fin 9 → R) (hx : OnQ x) (hy : OnQ y) :
    Bf x y * (y 0 * ∑ i ∈ range 9, Wn x j i * evalSP x y (dXsp i (law l 0)) -
      x 0 * ∑ i ∈ range 9, Wn y j i * evalSP x y (dYsp i (law l 0))) = 3 * GBf x y j * A32 l 0 x y
```
(ℚ-algebras; `Wn = 2W`, `j = 0, 1` = A2's `flowW 0, 1`.)

### 8.2 Recursor-based kernel functions (one V2′ identity)
| variant | wall | peak |
|---|---|---|
| structural recursion, `ite`/`Decidable` (checkpoint 1) | 26 s | 3.35 GB |
| recursors (`T.rec`, `List.rec`, `AT.rec`) | 15 s | 2.06 GB |
| + `cond`, `Nat.blt`, `Nat.beq` (adopted) | 13.7 s | 1.80 GB |

Each `Cert/V2k*` file (8 identities) now takes 77–115 s (was 232–279 s), peak 1.97 GB. The peak is per declaration,
not cumulative over a file.

### 8.3 Memory of every heavy check
| file | wall | peak |
|---|---|---|
| `Cert/V2k*` | 77–115 s | ≤ 2.0 GB |
| `Cert/V1` (split) | 200 s | **3.21 GB** (was ≈ 9 GB) |
| `Cert/F1j0`, `F1j1` | 60 s | 1.60 GB |
| `TableFacts`, `Sym`, `Deriv` | ≤ 110 s | small |

Rule of thumb: ≈ 0.75 GB per 10⁴ term-pairs inside one declaration, plus 0.33 GB base; split above ≈ 4·10⁴.

### 8.4 `A1Facts` (STAGE_A2 §7, `LSG/JacAn/A1Facts.lean`): field status and plan
Instantiation plan: `law0 := lawPt 0`, `dup := dup`, `negP := negP`, `OnQ := OnQ` (over `ℂ`);
`dlaw0 i X Y l := evalSP X Y (dXsp i (law l 0))`; `ddup i X l := evalSP X X (dXsp i (law l 4)) + evalSP X X (dYsp i
(law l 4))`. A final file `LSG/Jac/A1FactsInst.lean` will build `LSG.JacAn.A1Facts` from the certified facts (it
imports `LSG.JacAn.A1Facts`; no `LSG/JacAn` file is edited).

| field | status | how |
|---|---|---|
| `law0_onQ` | **done** (`law0_onQ`) | V1 |
| `negP_onQ`, `origin_onQ`, `grantJ_onQ` | **done** (`negP_onQ`, `origin_onQ`, `grant_onQ`; `grantJ = grant` on A2's side) | |
| `law0_origin` | **done** (`lawPt0_origin`) | |
| `law0_swap`, `swapSign` | **done** (`law_S2` with `m = 0`: `swapSign = −1`) | S2 |
| `hasFDerivAt_law0`, `hasFDerivAt_dup` | partly: the curve form `hasDerivAt_evalSP` is done; the Fréchet form is ≈ 60 lines | glue |
| `law0_analytic`, `dup_analytic`, `law0_smul_*`, `dup_smul`, `onQ_smul` | to do, ≈ 0.1k | glue; degree check on the data |
| `E1_0`, `E1_4` | to do | bidegree (5,4). Merged data `D_jA_l = Σ_i W_{ji}(X) ∂A_l/∂X_i`, checked exactly by the same checker with identity tables (bidegree (3,2)); then `A_c·D_jA_l − A_l·D_jA_c − X₀·W^{[c]}_{jl}(A) ∈ I` with a degree-5 `X`-table. 2 × 16 identities |
| `E2_4` | to do | E1 for law 4 with chart-4 input and output, in `X` (bidegree (5,4)) and in `Y` (bidegree (4,5)), added on the diagonal (`ddup = ∂_X + ∂_Y`). The single-copy degree-9 form is not certified directly (a degree-9 table has 24,310 monomials) |
| `W4`, `W4_four`, `W4_smul`, `W4_contDiff` | to do (data from `scripts/jac/w4_check.py` → `flow_W4.json`) | trivial once the data are fixed |
| `W4rel` | to do | single-copy cubic: `linear_combination` with linear cofactors (16 identities) |
| `W4_origin` | to do | evaluation |
| `law0_neg` | to do | by `law_S1`, `A32 k 0 X (negP X) = A32 0 k X X`; certify `A_0^{(k)}(X, X) ∈ I` (single copy, degree 4) with the checker: `X`-table degree 4, `Y`-table the degree-0 identity table |
| `dup_origin` | to do | evaluation (the `X₄²Y₄²` coefficients) |
| `dup_onQ` | to do | V1 for law 4 (bidegree (4,4), 9 identities, split like V1), restricted to the diagonal |
| `dup_ne_zero` (P2) | **assessed, §8.5** | |

Cost of E1/E2: the main products are `A` (≈ 100 terms) × `D A` (≈ 200 terms, `X`-degree 3), ≈ 2·10⁴ term-pairs each,
about 3 products per identity, i.e. ≈ 3–5 GB per declaration with the current checker. Plan: split each identity over
two declarations (§8.3 rule), keeping every declaration ≤ 3.5 GB.

### 8.5 P2 `dup_ne_zero` (completeness of law 4 on the diagonal): assessment
* [Numerical, `scripts/jac/p2_rank.py`, mod p] `(dup₀, …, dup₈)_N + I_N = S_N` holds first at **N = 7**. The rank of
  `(dup)_N` in `(S/I)_N` is 81/225 at N = 5, 320/324 at N = 6, 441/441 at N = 7 and 576/576 at N = 8. So there is a
  Nullstellensatz certificate `X_i^7 ≡ Σ_k c_{ik} dup_k mod I` with `c_{ik}` of degree 3.
* Kernel cost of certifying it:
  - a degree-7 single-copy normal-form table (6,435 monomials, 441 standard ones, so the accumulator tree needs depth
    9) with its own cofactor certificates (degree-5 cofactors): ≈ 2–5 MB of data, 10–30 CPU-min to check;
  - then 9 identities `X_i^7 − Σ_k c_{ik} dup_k ∈ I`, ≈ 10⁵ term-pairs each, split over ≈ 3 declarations.
  - Estimate **0.5–1k lines + data, ≈ 1 h CPU**. Feasible, but the largest single item left.
* Alternative: the A3 ψ-argument gives it for free (`dup(θ(u)) = ψ θ₄(0) θ(2u)` with `θ` nowhere zero and `ψ` a
  nonzero constant).
* **Recommendation**: keep `dup_ne_zero` a named hypothesis for now; certify it after E1/E2 if A3 is not imminent.

### 8.6 W4 data, and a correction to the field `W4_origin`
* [Numerical, `scripts/jac/w4_check.py` → `scripts/jac/flow_W4.json`] The chart-4 quadratics exist: for every
  `j, i` there is a quadratic form `W4_{ji}` with `X₀·W4_{ji} ≡ X₄·W_{ji} − X_i·W_{j4}` on `A` (16 forms, interpolated
  mod p over the 36 standard degree-2 monomials, rationally reconstructed). Same relation as A2's `W4rel`
  (`X₄ W_l = X₀ W4_l − X_l W4_0`), with `W4_{j0} = −W_{j4}` on `A` and `W4_{j4} = 0`.
* **`W4_origin` as stated in `A1Facts` is false.** On `A`, `W4_{j0} = −W_{j4}`, and `W_{14}(e₄) = (−3X₀X₃ + 6X₁²)(e₄) = 0`,
  `W_{24}(e₄) = (−X₀² + 6X₁X₂)(e₄) = 0`. So `W4 0 e₄ 0 = W4 1 e₄ 0 = 0`. Reason: `X₀ ∈ H⁰(3Θ)` vanishes to order 3
  along `Θ`, so `X₀/X₄` has zero gradient at `O`. What does hold: `W4 0 e₄ 1 = −1/2` (from `−½X₄²` in `W4_{11}`) and
  `W4 1 e₄ 8 = 1` (from `X₄²` in `W4_{28}`), so the flow moves `X₁/X₄` and `X₈/X₄` at `O`. **A2: please restate
  `W4_origin`** (e.g. `W4 0 e₄ 1 ≠ 0`), or say which coordinate the homomorphism step needs transversal.
* [Numerical, `w4_check.py`, finished after the checkpoint-2 report] The equivariance identities
  `A_c·D A_l − A_l·D A_c = X_c·W^{[c]}_{jl}(A)` vanish at random pairs mod p for: law 0, chart 0, `X`-flow (16/16);
  law 0, chart 4 with chart-4 input field `W4` (16/16); law 4, chart 0, `X`- and `Y`-flow (16/16 each); law 4,
  chart 4, `X`- and `Y`-flow (16/16 each). So the inputs for `E2_4` (law 4, chart 4, both arguments) are confirmed.
  A2's `E1_4` (input field `W`, output chart 4, factor `X₀`) is a different mixed form and still has to be checked
  numerically before certification.
* [Numerical, `scripts/jac/e14_check.py`] A2's mixed `E1_4` (law 0, input field `W`, output chart 4, factor `X₀`,
  with the `flow_W4.json` representatives) vanishes at random pairs mod p: 16/16. **No E1 variant fails.**
* [Numerical, `e14_check.py 40`] The new field `E1_40` (law 0, input field `W4`, output chart 0, factor `X₄`) vanishes
  at random pairs mod p: 16/16. `E1_44` is the "law 0, chart 4" line above (16/16). All E1 forms of the current
  `A1Facts` (`E1_40`, `E1_44`, `E1_4`) and the inputs of `E2_4` pass.

---------------------------------------------------------------------------------------------------------------------

## 9. Checkpoint 3 (queue items 1–4 of the coordinator; checkpoint 2 = commit 76ac812)

### 9.1 Item 1: numerical checks of every E1 form (all pass, mod p, random pairs)
`w4_check.py`: law 0 chart 0 `X`-flow; law 0 chart 4 with input `W4`; law 4 charts 0 and 4, `X`- and `Y`-flow: 16/16
each. `e14_check.py`: `E1_4` (input `W`, output chart 4, factor `X₀`) 16/16; `E1_40` (input `W4`, output chart 0,
factor `X₄`) 16/16. Nothing fails.

### 9.2 Item 2: `W4rel` [Proved] (`W4.lean`, generated by `scripts/jac/gen_jac_w4.py`)
* `W4n x j i = 4 W^{(4)}_{j+1,i}(x)` (integer quadratics from `flow_W4.json`; `W4n x j 4 = 0`).
* **`W4rel (j) (hj : j < 2) (l : Fin 9) (x : Fin 9 → K) (hx : OnQ x) :
  x 4 * (2 * Wn x j l) = x 0 * W4n x j l - x l * W4n x j 0`** over a field of characteristic 0 (this is `A1Facts.W4rel`
  times 4, with `flowW = Wn/2`, `W4 = W4n/4`).
* Note: 14 of the 18 cases are in `(Q)₃` (linear cofactors). Four (`(j,l) = (0,1), (0,8), (1,3), (1,8)`) are **not**:
  `(Q)₃ ≠ I₃` (the 3 extra cubics of ABVAR A0.1). For those, each `x_k · relation` is in `(Q)₄ = I₄` (quadratic
  cofactors), and one cancels a nonzero `x_k`; hence the field hypothesis.
* `W4_origin` was removed by A2 (STAGE_A2 §7.1); nothing to certify.

### 9.3 Item 3: `law0_neg`, `dup_origin`, `dup_onQ` [Proved]
* **`law0_neg`** (`Pointwise.lean`): `OnQ x → k ≠ 4 → lawPt 0 x (negP x) k = 0` (ℚ-algebras). Via `law_S1` it is
  `A_0^{(k)}(x, x) = 0`, a single-copy degree-4 identity checked by the bidegree checker with `Y`-table `T0` (the
  degree-0 identity table) on `diagSP (law 0 k)` (`CheckerDiag.lean`, `Diag.lean`: `single_of_check`,
  `evalSP_diagSP`; raw checks `Cert/Neg.lean`, 8 identities, 3 s). Negative control: for `k = 4` the check returns
  `false` (provably).
* **`dup_origin`** (`Diag.lean`): `dup e₄ = (−8) • e₄` (any commutative ring; `c = −8 ≠ 0`).
* **`dup_onQ`** (`V1L4.lean`, `Cert/V1L4.lean`, generated by `scripts/jac/gen_jac_v1m.py 4`): V1 for law 4,
  `law4_onQ : OnQ x → OnQ y → OnQ (lawPt 4 x y)`, hence `dup_onQ`. Products are chunked by at most 2 per declaration
  (`identity_of_check_split3`, new three-part split `evalO2_split3`).

### 9.4 Item 4: glue [Proved] (`Glue.lean`)
* `hasFDerivAt_xmono`, **`hasFDerivAt_evalSP_left`** (Fréchet derivative of `X ↦ evalSP X Y p` is
  `Σ_i evalSP X Y (dXsp i p) • proj i`), **`hasFDerivAt_evalSP_diag`** (of `X ↦ evalSP X X p`:
  `Σ_i (evalSP X X (dXsp i p) + evalSP X X (dYsp i p)) • proj i`), under `decOK` (`law_decOK`).
* **`analyticAt_evalSP`**: `z ↦ evalSP (F z) (G z) p` is analytic for analytic `F, G` (any normed space `E`).
* **`lawPt_smul_left/right`**, **`dup_smul`** (degree check `law_deg`), **`onQ_smul`**.
* With these, `A1Facts.hasFDerivAt_law0` (`dlaw0 i X Y := fun l => evalSP X Y (dXsp i (law l 0))`),
  `hasFDerivAt_dup` (`ddup i X := fun l => evalSP X X (dXsp i (law l 4)) + evalSP X X (dYsp i (law l 4))`),
  `law0_analytic`, `dup_analytic`, `W4_analytic`, `W4_contDiff`, `law0_smul_*`, `dup_smul`, `onQ_smul` are one-line
  instantiations (done in `A1FactsInst.lean`, item 6).

### 9.5 Item 5 (E1_40, E1_44, E1_4, E2_4): design after measurements
* Forms: law `m`, input field `W_in` on side `S`, output chart `c`, factor `S_f`:
  `A_c D A_l − A_l D A_c = S_f · W_out(A)_l`. Instances: `E1_40` (m 0, X, W4 → chart 0, X₄), `E1_44` (m 0, X, W4 →
  chart 4, X₄), `E1_4` (m 0, X, W → chart 4, X₀), and for `E2_4` law 4 with W4, chart 4, in `X` (bidegree (5,4)) and
  in `Y` (bidegree (4,5)). 5 × 16 = 80 identities.
* Merged derivative data `D A_l = Σ_i W_{in,ji} ∂A_l` (72 SPs, ≈ 200 terms) checked exactly by the same checker with
  identity tables (degrees 3 and 2, `δ = 1`), then the main identities with a degree-5 normal-form table.
* Memory measurements (one V2′ identity, 1.80 GB): restricting the `Y`-packing to a third of the slots: 1.73 GB (so
  memory is not the size of the big integers); restricting the accumulator updates to a third of the `X`-slots:
  1.31 GB. Hence ≈ 0.37 GB per 10⁴ term-pairs for the inner loop and ≈ 0.37 GB per 10⁴ for the slot updates.
* An E1 identity is ≈ 6·10⁴ term-pairs (≈ 4.5 GB unsplit). Literal-intermediate splits would cost ≈ 0.8 MB of
  literal per split (degree-5 side), ≈ 100+ MB in total: rejected. **Plan: `X`-slot-range splitting** (each
  declaration recomputes the inner loop but updates only the slots in its range and checks them zero; the ranges
  cover all slots; no literals): 3 ranges per identity, ≈ 2.3 + 0.33 + 0.8 ≈ 3.4 GB each, ≈ 30 s each, ≈ 2 CPU-h for
  all 80 identities. Not started yet.

### 9.6 Item 6 (partial): `A1FactsInst.lean` [Proved]
* **`mkA1Facts`** builds `LSG.JacAn.A1Facts` from A1's certified facts. Its only hypotheses are the not-yet-certified
  fields, stated exactly as in `A1Facts`: `E1_40`, `E1_44`, `E1_4`, `E2_4` and `dup_ne_zero`. Every other field is
  discharged, including the new `W4_origin_indep` (`W4 0 e₄ 1 · W4 1 e₄ 8 − W4 0 e₄ 8 · W4 1 e₄ 1 = −1/2 ≠ 0`).
* Instantiation: `OnQ := OnQ`, `law0 := lawPt 0`, `dup := dup`, `negP := negP`, `dlaw0 = dlaw0C`, `ddup = ddupC`,
  `W4 j X i = W4n X j i / 4`, `swapSign = −1`.

### 9.7 P2 (`dup_ne_zero`), now required (coordinator, after A2 found the A3 cycle)
* Statement certified will be exactly the `A1Facts` field:
  `∀ X : P9, OnQ X → X ≠ 0 → dup X ≠ 0` (over `ℂ`; the Lean theorem will be over any field of characteristic 0).
* Method (§8.5): the degree-7 Nullstellensatz `X_i^7 ≡ Σ_k c_{ik} dup_k mod I` (`c_{ik}` of degree 3), checked as
  single-copy identities with a degree-7 normal-form table (6,435 monomials, 441 standard, accumulator depth 9) and
  split declarations ≤ 3.5 GB. If `dup X = 0` then every `X_i^7 = 0`, so `X = 0`.
* Order: after E1/E2 (item 5), as the coordinator allows; or earlier if convenient.

### 9.8 Measurements of the new heavy checks
| file | wall | peak |
|---|---|---|
| `Cert/V1L4` (chunks of ≤ 2 products) | 211 s | **3.45 GB** (3+2 chunks: 3.83 GB) |
| `Cert/Neg` | 3 s | small |


## 10. Checkpoint 4 (in progress)

### 10.1 `special_hP₀` (P3) [Proved] (`LSG/Jac/Special.lean`, 2026-10-31)
For any `α` with `α⁵ = 2`: `grantJ (mumfordPts' 0 (−1) α 3) = (1, α³, 0, α, −2α², α, −1, 2α⁴, −α⁴)` and
`X₄(law0 P₀ [−1]P₀) = 128 α ≠ 0` (the other eight coordinates are 0, computed in `ℚ[α]/(α⁵ − 2)` by
`scripts/jac/jacA1_p0.py`; only `X₄` is proved in Lean). `α` comes from `IsAlgClosed.exists_pow_nat_eq`.
`A1FactsInst.mkA1Facts` now fills the field with `special_hP0`; no new hypothesis. The value is nonzero, so no
change is needed on A2's side.

### 10.2 Degree-5 table, identity tables, X-range splitting [Proved / kernel-checked]
* `Data/Table5.lean`: degree-5 NF table mod `I` (1287 keys, 225 standard monomials, `δ = 691200`, `Y`-packing width
  `kb5 = 92`), checked in 35 chunks (`Cert/T5_<k>.lean`, `nfRangeOK`, ≤ 3.3 GB each) + `Cert/T5base.lean`;
  `TableFacts5.nfValid5`. `Data/Table4b.lean`: the degree-4 table repacked at width 92 (`sameRows` with `nfTree`).
  `Data/IdTab.lean`: identity tables of degrees 2, 3 (exact checks).
* `RangeSound.zeros_of_ranges`: the `allZero` check may be split into `X`-slot ranges (`T.mapRows (rowsIn lo hi)`).
  Bridges `E1Bridge.identity_X5/Y5` (bidegree (5,4)/(4,5)), `identity_exact32/23`.
* `Cert/DA_<fam>.lean` + `E1DA.lean`: the merged derivatives `DA = Σ_i W_{ji} ∂A_l/∂S_i`, exact.
* Memory model (measured on F4X, 2026-10-31): the peak of a range declaration is ≈ `0.6 GB + 4.8e-5 · cost`, with
  `cost = Σ_{X-pairs whose NF row meets the range} (#Y-products) + #slot updates` (`scripts/jac/e1_cost.py`; fit on
  12 measured declarations, error ≲ 0.1 GB). Equal-width ranges were too coarse (9 ranges for F4X: up to 5.0 GB);
  ranges are now chosen per identity, greedily, with budget 50000 (`X`-flow families, ≈ 3.0 GB; heaviest E44 range
  measured 3.12 GB) and 42000 (F4Y, `Y`-packing 225 slots; heaviest at 33000 measured 2.47 GB). Restricting the
  `Y`-side or pre-splitting the `X` rows as data did not help (6+ GB / −7%).
  About 1300 range declarations in total (`Cert/E1_<fam>_<j>.lean`), ≈ 4.5 CPU-hours.
* `E1Sem_<fam>.lean`: the identities in explicit form; `E1Final.lean`: `E1_40C`, `E1_44C`, `E1_4C`, `E2_4C` in the
  exact `A1Facts` forms, and `a1Facts : A1Facts` with no hypotheses (pending the builds).

### 10.3 P2 (`dup_ne_zero`) — exact degree-7 identities [Proved, pending build of `Cert/P2_<i>`]
* Certificate (`scripts/jac/gen_jac_p2.py` → `p2_cert.json`, untrusted): for each `i`,
  `D_i X_i⁷ = Σ_k C_ik(X) dup_k(X) + Σ_j H_ij(X) Q_j(X)` exactly, `deg C = 3`, `deg H = 5`, integer coefficients
  (≤ 48 bits); `D_i` ∈ {45000, …, 3240000000}; ≈ 43 `C` and ≈ 480 `H` monomials per `i`, ≈ 6000 products.
* Kernel check (`CheckerP2.lean`, `Data/P2Tab.lean`, `Data/P2.lean`, `Cert/P2_<i>.lean`): single copy (`Y`-table
  `T0`), `X`-side the degree-7 identity table (6435 leaves, `idSeqOK`, no `getD`), accumulator with `2^13` slots
  (`evalOd 13`). Soundness `P2Sound.exact_of_idSeq` (`sound2Vd` = `sound2V` with `2^d` slots), semantics
  `evalTerms_p2` (on `V(Q)` with `dup x = 0` the identity reads `D_i x_i⁷ = 0`).
* `P2.eq_zero_of_dup` (any domain of characteristic 0) and `P2.dup_ne_zeroC : ∀ X : Fin 9 → ℂ, OnQ X → X ≠ 0 →
  dup X ≠ 0`, which is the `A1Facts` field verbatim (`dupC = dup`).

### 10.4 New `A1Facts` fields (A2/A3 batch, 2026-10-31) [Proved] (`A1FactsInst.lean`)
`onQ_closed` (`onQ_closedC`: preimages of 0 under the 9 quadrics), `negP_eq` (rfl), `lawK := A32` with
`law0_lawK` (rfl), `lawK_S1` (`Sym.law_S1`), `rank_one` (`V2.rank_one`), `lawK_smul_left/right`
(`Glue.lawPt_smul_left/right`), `lawK_analytic` (`analyticAt_evalSP`), and `W4_negP`. **`W4_negP` is true, even
without `OnQ`**: every monomial of `W4n_{j,i}` has odd degree in `X₄..X₇` iff `i ∈ {4..7}` (checked on the data,
0 violations; proved by `W4C_negP`, `fin_cases` + `ring`). `A1FactsInst` builds again; `mkA1Facts` takes only
`E1_40, E1_44, E1_4, E2_4, dup_ne_zero`, which `E1Final.a1Facts` supplies (pending the E1 certificate builds).

### 10.5 Taylor-coefficient fields (STAGE_A3 §8 batch, 2026-10-31) [Proved]
* `onQ_quad` (`WTables.onQ_quadC`, = `onQ_iff`; `quadA` is literally A1's `quad`).
* `W4num/W4den/W4H/W4num_bound/W4_table`: `W4den = 4`, `W4num` = the integer table of `W4n = 4 W⁽⁴⁾`, upper
  triangular in `(a, b)`, `W4H = 32` (`decide +kernel`); `W4_table` by `fin_cases` + `Fin.sum_univ_succ` + `ring`.
* Chart 8: `scripts/jac/w8_check.py` (interpolation mod p; untrusted) → `flow_W8.json`: `W⁽⁸⁾` is quadratic, with
  denominators 4. `W8.lean` (generated by `gen_jac_w8.py`, the chart-8 copy of `gen_jac_w4.py`): `W8n = 4 W⁽⁸⁾`,
  `W8rel` proved on `V(Q)` over any field of char 0 (14 relations with linear cofactors in `(Q)₃`, 4 via `x_k ·`
  multipliers in `(Q)₄`). `WTables.lean` (generated by `gen_jac_wtab.py`): `W8C = W8n / 4`, `W8num` (`W8den = 4`,
  `W8H = 48`), `W8_table`, `W8_eightC`. Field `W8rel` from `W8rel` and `flowW = Wn / 2`.
* `A1FactsInst` builds with all fields of the current `A1Facts`; the only hypotheses of `mkA1Facts` are still
  `E1_40, E1_44, E1_4, E2_4, dup_ne_zero`.

---------------------------------------------------------------------------------------------------------------------

## Requests from the A3 agent for A4.1b, surjectivity (2026-10-31; relayed by the coordinator)

These are proposed `A1Facts` fields. **None has been added to `A1Facts.lean` yet**: the coordinator schedules the batch.
Context: STAGE_A4 §2.3 and STAGE_A3 §11. The goal is `∀ X ≠ 0, OnQ X → ∃ z c, X = c • θ_N z`.

**S-a, the affine chart (pointwise).** These follow from the certificates `X_i − grantᵢ(p)` (`i = 1, 4, 5, 8`),
`chartR1 p`, `chartR0 p ∈ I_A + (X₀ − 1)`; the cubics are needed for them.

```
affine_chart : ∀ X : P9, OnQ X → X 0 = 1 →
  X = grantJ ![X 3, -X 2, X 7, X 6] ∧ chartR1J ![X 3, -X 2, X 7, X 6] = 0 ∧ chartR0J ![X 3, -X 2, X 7, X 6] = 0
```

**S-b, the anchor `P₀ ∈ E(ℂ²)`.**
* Why it is needed: the path-following of A2 (`follow_par`) only gives *translates*. Every generic divisor `D`
  satisfies `D ∥ law0(θ(c), P₀)`, and `θ(c) ∥ law0(D, negP P₀)`.
* One explicit generic divisor with `D ⊖ P₀ = P₀` is enough. Take `D₂ = 2D₀`, `D₀ = (0,−1) + (α,3)`.
  - Cantor in `ℚ(α)`, numerically with `α = 2^{1/5}`: `U = x² − 12.0613327275x − 7.91704746464`,
    `V = 86.1845057663x + 53` (exactly `b₀ = 53`).
  - Its points are `x ≈ −0.62411`, `y ≈ −0.78820` and `x ≈ 12.68544`, `y ≈ 1146.288`. `D₂` is generic: distinct
    `x`, `y ≠ 0`.
  - Script: scratchpad `cantor2n.py`.
* Requested field. The same `α` must also satisfy `special_hP₀`'s condition, so it is bundled; `m₂ ∈ ℚ(α)⁴` are the
  Mumford coordinates of `2D₀`:

```
anchor : ∃ α : ℂ, α ^ 5 = 2 ∧
  law0 (P₀ α) (negP (P₀ α)) 4 ≠ 0 ∧
  ∃ x₁ y₁ x₂ y₂ : ℂ, y₁ ^ 2 = 4 * x₁ ^ 5 + 1 ∧ y₂ ^ 2 = 4 * x₂ ^ 5 + 1 ∧ x₁ ≠ x₂ ∧ y₁ ≠ 0 ∧ y₂ ≠ 0 ∧
    ∃ lam : ℂ, lam ≠ 0 ∧ law0 (grantJ (mumfordPts' x₁ y₁ x₂ y₂)) (negP (P₀ α)) = lam • P₀ α
-- P₀ α := grantJ (mumfordPts' 0 (-1) α 3)
```

* How A1 can discharge it: the `law0` evaluation needs only `m₂ ∈ ℚ(α)⁴`, as for `special_hP₀`. The points come from
  the quadratic formula, and genericity from the evaluation.

**S-c, flow exit at the boundary `X₀ = 0`.**
1. **Generators and tangency (ideal form).** These are needed for invariance of `V(Q)` under the real-time chart-4 and
   chart-8 flows, via a linear ODE for the generator values:

```
gensI : Fin 12 → P9 → ℂ                       -- the 9 quadrics + 3 cubics, as functions
gensI_diff : ∀ i, Differentiable ℂ (gensI i)
gensI_iff : ∀ X, OnQ X ↔ ∀ i, gensI i X = 0
tanC4 tanC8 : Fin 2 → Fin 12 → Fin 12 → P9 → ℂ  -- polynomial cofactors
tanC4_cont tanC8_cont : continuity
gensI_tan4 : ∀ j i X, fderiv ℂ (gensI i) X (W4 j X) = ∑ k, tanC4 j i k X * gensI k X
gensI_tan8 : ∀ j i X, fderiv ℂ (gensI i) X (W8 j X) = ∑ k, tanC8 j i k X * gensI k X
```

2. **Exit words.** These are the semantic form of the certificate `X_c^N ∈ I_A + (X₀, D-words of X₀ of order ≤ 3)`,
   with `N = 4` for chart 4 and `N = 5` for chart 8 (STAGE_A4 spike `boundary_flow_modp.out`). Define, in
   `A1Facts.lean`:
   `derivW W v h X := fderiv ℂ h X (v 0 • W 0 X + v 1 • W 1 X)` and `exitWord W v k := (derivW W v)^[k] (· 0)`.
   - Symmetrised mixed words are combinations of pure words at the directions `e₀, e₁, e₀ ± e₁, e₀ + 2e₁`, by
     polarisation.

```
exit4 : ∀ X, OnQ X → X 0 = 0 → X 4 ≠ 0 → ∃ v : Fin 2 → ℂ, ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ exitWord W4 v k X ≠ 0
exit8 : ∀ X, OnQ X → X 0 = 0 → X 8 ≠ 0 → ∃ v : Fin 2 → ℂ, ∃ k, 1 ≤ k ∧ k ≤ 3 ∧ exitWord W8 v k X ≠ 0
```

* If a different but equivalent form is easier for A1 (e.g. words given as explicit polynomials with formal partials,
  as for `dlaw0`), I will adapt.

### 10.6 Checkpoint 4 result: `A1Facts` with no hypotheses [Proved] (2026-10-31)
* **`LSG.Jac.a1Facts : A1Facts`** (`E1Final.lean`) `:= mkA1Facts E1_40C E1_44C E1_4C E2_4C dup_ne_zeroC`.
  `#print axioms LSG.Jac.a1Facts`: `[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom` or
  `native_decide` in `LSG/Jac/`.
* E1/E2: `E1_40C`, `E1_44C`, `E1_4C`, `E2_4C` in the exact field forms (`E2_4C` = F4X + F4Y at `Y = X`).
* P2: `P2.dup_ne_zeroC` (9 exact degree-7 identities, `Cert/P2_<i>`, 12 s and ≈ 1.4 GB each).
* Builds (two at a time): E1 certificates 10 files, 1319 range declarations, wall ≈ 2.4 h
  (E40 934 s, F4Y 1198 s, E04_0/F4X_0 1646 s, E04_1/F4X_1 2296 s, E44 2682 s, per pair).
* Memory. Isolated range declarations at the budget measure ≤ 3.12 GB (heaviest E44 range; F4Y 2.47 GB). The
  **whole-file process peaks are higher** because one `lean` process checks 86–200 declarations and its working set
  creeps up: E40 3.77/3.85, F4Y 3.36/3.43, F4X 4.27/3.79, E04 4.51/4.05, E44 4.81/4.96 GB. If a ≤ 3.5 GB
  per-process cap is needed, split each `Cert/E1_<fam>_<j>.lean` into one file per identity (generator change
  only, then a rebuild of ≈ 4.5 CPU-hours).
* Process note: during this run I accidentally started a second `lake build` that rebuilt `E1_E04_1`/`E1_F4X_1`
  in parallel with the queue for ≈ 30 min (4 heavy `lean` processes at once, ≤ 3.5 GB each); it finished by itself.

## 11. B5 (taken over from γ, 2026-10-31): the `lci_*` fields of the A-block [Proved]

**For γ (`AbBlock` with `g = 2`, `N = 9`, `gens = LSG.JacBlock.gensMv`)** — `import LSG.Jac.B56`, namespace `LSG.Jac`:
```lean
lci_s := 4
lci_S := lciS            -- lciS : Fin 4 → MvPolynomial (Fin 9) ℂ   (cubics)
lci_F := lciF            -- lciF : Fin 4 → List (MvPolynomial (Fin 9) ℂ)  (six of gQ0..gQ8 each)
lci_len := lciA_len      -- ∀ i, (lciF i).length + 2 + 1 = 9
lci_F_le := lciA_F_le    -- ∀ i, Ideal.ofList (lciF i) ≤ Ideal.span {Q | Q ∈ gensMv}
lci_mem := lciA_mem      -- ∀ i, ∀ Q ∈ gensMv, lciS i * Q ∈ Ideal.ofList (lciF i)
lci_cover := lciA_cover  -- ∀ v : Fin 9, ∃ e, X v ^ e ∈ Ideal.span {Q | Q ∈ gensMv} ⊔ Ideal.span (Set.range lciS)
```
All four: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

* Systems: `F_i` = quadrics `{0,1,2,5,6,7}`, `{2,3,4,6,7,8}`, `{1,4,5,6,7,8}`, `{1,2,3,5,6,8}`, `S_i` the unique cubic
  of `((F_i) : I_A)₃` outside `I_A` (γ's `scripts/jacblock/b5_S.pkl`, primitive integer form). Cover set found from
  γ's greedy run (6 systems) pruned by `scripts/jacblock/jacA1_b5prune.py`: dropping the first two still covers with
  `e ≤ 7` ([Numerical], mod p; then exact).
* Identities (`scripts/jac/gen_jac_b5.py`, exact `fmpq` cofactors via γ's `member`; untrusted):
  (M) `D · S_i · G = Σ_k h_k F_{i,k}` for the 6 generators `G ∉ F_i` (24, degrees 5/6, `D ∈ {1, 2, 4}`);
  (C) `D_v · X_v⁷ = Σ_j H_j G_j + Σ_i C_i S_i` (9, degree 7, `D_v` up to ≈ 6·10¹⁶).
* Kernel checks (`Cert/B5M_<i>`, `Cert/B5C_<v>`, `Cert/B5base`): P2 format (`idTerms`, `CheckerP2.evalOd`,
  identity tables of degree 5/6 `Data/B5Id5`, `Data/B5Id6` and 7 `Data/P2Tab`), ≈ 6 s and ≤ 0.5 GB each.
* Reading in `MvPolynomial (Fin 9) ℂ` (`B56Sound.mem_of_idTerms` at `x = X`): the checks give exact polynomial
  identities in any commutative ring; `gRow_k : evalRow X (gRows.getD k []) = gQk / gCk` identifies the data rows with
  `gensMv`.
* Files: `LSG/Jac/B56Check.lean` (core), `B56Sound.lean`, `B56.lean` (generated by `scripts/jac/gen_jac_b56sem.py`),
  `Data/B5*.lean`, `Cert/B5*.lean`. B6 stays γ's (`LSG/JacBlock/Hilb.lean`, `hilb_deg = 14`).

## 12. M2 (`A^♮`, model in `ℙ¹¹`): B6 and the Wronskian cocycle [Proved] (2026-10-31)

**For the future `aBlockV`** — `import LSG.Jac.B6V`, namespace `LSG.Jac`; variables `X₀..X₈ = 0..8`,
`T₀, T₄, T₈ = 9, 10, 11`, `R12 = MvPolynomial (Fin 12) ℂ`:
```lean
ι9 : Fin 9 → Fin 12 := Fin.castLE _            -- the X-variables
P04V := X 0 * X 10 - X 4 * X 9 + 2 * X 1 ^ 2 - X 0 * X 3
P08V := X 0 * X 11 - X 8 * X 9 + X 2 * X 5 - X 1 * X 6
P48V := X 4 * X 11 - X 8 * X 10 - 2 * X 1 * X 2 + C (1/4) * X 5 * X 7 - C (1/2) * X 3 * X 8
gensV : List R12 := gensMv.map (rename ι9) ++ [P04V, P08V, P48V]     -- the 15 generators of J_V (M2.1.1)
lformV (l : Fin 12 → ℂ) : R12 := ∑ i, C (l i) * X i
hilbL : Fin 4 → Fin 12 → ℂ := ![Pi.single 9 1, Pi.single 10 1, Pi.single 11 1, 𝟙{0,4,8}]   -- T₀, T₄, T₈, X₀+X₄+X₈
theorem hilbV (M : R12) (hM : M.IsHomogeneous 41) :
    M ∈ Ideal.span {Q | Q ∈ gensV} ⊔ Ideal.span (Set.range fun a => lformV (hilbL a))
theorem kappaV : X 0 * P48V - X 4 * P08V + X 8 * P04V =
    -(C (1/2) * X 5 * rename ι9 gQ1) - X 1 * rename ι9 gQ5 - C (3/4) * rename ι9 gC0
```
(`lformV_single`, `lformV_ell` evaluate the forms.) Both: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
So the `VBlock` hilb field should read `hilb_l := hilbL`, `hilb_deg := 41`, `hilb := hilbV` if it uses
`lform l = Σ C (l i) * X i` (otherwise a one-line conversion).

* **Degree 41, not 33.** The certificate is the spike's: `D_v X_v⁵ = Σ_k c_k sub(G_k)` for the 8 variables `v ≠ 4`,
  `sub : X₄ ↦ −X₀ − X₈`, `G` = `gensMv` and the `T = 0` parts of `P04, P08, 4·P48` (`scripts/jac/gen_jac_b6v.py`, the
  `X₀+X₄+X₈` choice of `m2_b6tri.py`; 3311 cofactor terms, `D_v ≤ 6.8·10⁶`). In Lean, `X_v⁵ ∈ J_V + (y)` follows
  (`sub(G) ≡ G mod (ℓ)` through the quotient map), then `X₄⁹ ∈ J_V + (y)` (binomial theorem on `X₄ ≡ −X₀ − X₈`), and
  pigeonhole with `e = (5,5,5,5,9,5,5,5,5,1,1,1)`, `Σ(e − 1) = 40`. The spike's 33 needs the finer pigeonhole on
  `sub(M)` (multinomial expansion); only the constant `n₁^N` changes, so I did not do it.
* Kernel checks `Cert/B6V_<v>` (degree 5, `Data/B5Id5`): ≈ 3 s each. Files: `Data/B6V.lean`, `Cert/B6V_*.lean`,
  `B6V.lean` (generated by `scripts/jac/gen_jac_b6vsem.py`, 486 lines).
* **Not done:** the `τ₀` identity (M2.1.7) — it is a statement about the `(3,3)` T-laws, which do not exist in Lean
  yet; it should be stated against their `pderiv` definition once M2.4b writes it (≤ 10 cofactor terms per case, by
  `linear_combination` after `MvPolynomial.funext`). The `X_cF ∈ J_V` facts (optional) are also not done.
