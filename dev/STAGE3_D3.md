# Stage 3, nodes D1 + D3: W88 Prop. 6.1 under (NR) (Lemma U) — plan and status

Started 2026-10-30. Labels as in PLAN.md. Sources: `../schanuel/five_exp/pilot_epi2_mix/W_UPGRADE.md` (Lemma U),
W83 Prop. 2.4 (pp. 637–642), W88 Prop. 6.1 (`w88-11.png`, `w88-12.png`). Input from D2: `LSG.Aux.prop21_G_deg`.

---------------------------------------------------------------------------------------------------------------------

## 0. Target

```
LSG.W88.VanishAlong Φ W T y :=  ∀ w ∈ W, ∀ k : ℕ, (k : ℝ) < T → iteratedDeriv k (fun s : ℂ => Φ (y + s • w)) 0 = 0
LSG.W88.prop61 : for G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m (g₂, g₃ algebraic, m ≥ 1), V ⊆ T_G, dim V = n < d,
  W ≤ V ℚ̄-rational, y : Fin μ → V ∩ Λ(G), ω : Fin κ → V ∩ Ω(G) ℤ-independent, (NR) d₁ + 2d₀ + κ ≤ 2n:
  ∃ C > 0, ∃ S₀, ∀ S ≥ S₀, with Δ = (C S^{d₁+2m−κ} (log S)^{d₀})^{1/(d−n)} there is
  P = Σ_l p_l M_l (p_l ∈ ℤ, M_l distinct `Mono`s of elliptic degree D ≤ Δ/S², Σα ≤ Δ/log S, Σβ ≤ Δ/S) with
  (∃ x, P(exp x) ≠ 0) and VanishAlong (P ∘ exp) W (Δ / log S) (Σ h_j y_j) for all 0 ≤ h_j ≤ S.
```
(W88's a = b = 1. Multiplicity is the analytic one, along every direction of W; the algebraic multi-cone
`VanishesAlong` of `LSG/ME/Deriv.lean` is not bridged yet.)

## 1. Design decisions (deviations from W83/W_UPGRADE, all simplifications)

* **No 𝒯, no F, no Step 3′.** W83 needs 𝒯 (points near which the fixed theta coordinate ψ₀ is ≥ e^{−cS²}) and then
  translates by F′ with products of addition laws. For E^m we choose the chart **per point**: for every u ∈ ℂ some
  coordinate i of ellW(u) = (σ³, σ³℘, σ³℘′) satisfies |ellW_i(u + z)| ≥ e^{−c(1+|u|)²} for all |z| ≤ ρ₀ (quasi-periodicity
  + compactness of a fundamental domain, `Chart.lean`). Then Step 2′ works at every t ∈ Y(S), and P = Q_S (W83's
  polynomial itself).
* **Translation to a fixed base point z₀ = ω₁/2** (instead of 0): the second argument of the addition law is
  ξ(u) = (℘(z₀+u), ℘′(z₀+u), 1), analytic near u = 0, whose Taylor coefficients satisfy the recursion of
  ℘″ = 6℘² − g₂/2 with ℘(z₀) = e₁ algebraic, ℘′(z₀) = 0 (no σ-series, no removable singularities). The first
  argument is X′ = law(X(h), (e₁ : 0 : 1)), representing exp(t − z₀) (2-torsion). Referee F1 is respected: no
  derivatives are taken at γ = exp(t).
* **One variable only.** Vanishing along W is reduced to lines s ↦ t + s·w, w = Σ c_i w_i with c ∈ {0..k}^τ
  (Liouville per line), then polarization (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`) gives all w ∈ W.
* **Sizes = house + denominator** in an abstract number field K with an embedding ι : K →+* ℂ (Liouville via
  `LSG.SL.one_le_norm_mul_house_pow`), not Weil heights. Majorants for Taylor coefficients: house(tc_j) ≤ A·B^j,
  denominators e·δ^j·j!; products of N factors keep the geometric shape with constants 2^N (`TaylorK.lean`).
* **Algebraic points (D1)** by balanced splitting h = ⌈h/2⌉ + ⌊h/2⌋ with law₁/law₂ (whichever is nonzero,
  `LSG.Elliptic.law_complete`): size(X(h)) ≤ 4^k(M₁ + c) − c for h ≤ 2^k, i.e. log house, log den ≤ c S².
  House bound of a law by homogeneity + compactness; denominators by weighted homogeneity (weights U:2, V:3, W:0,
  g₂:4, g₃:6).
* **Monomials (D3c)**: only (σ³)^{D−a}(σ³℘)^a per block. Nonvanishing of P∘exp: off the lattices P∘exp =
  Π σ_j^{3D}·Q(a, e^b, ℘(z)), and Q vanishes on a product of infinite sets (`infinite_image_weierstrassP`), so Q = 0.

## 2. Files (namespace `LSG.Aux`; `VanishAlong` in `LSG.W88`), status

All files below compile, no sorry/axiom/native_decide; `#print axioms` of the main results:
[propext, Classical.choice, Quot.sound]. None is imported by `LSG.lean` (build by module name, e.g.
`lake build LSG.AuxFun.LemmaUMain LSG.AuxFun.MonoIndep`).

| file | lines | content |
|---|---|---|
| `AuxFun/NFSize.lean` | 175 | `Sz ι A d z` (z = ι x, house x ≤ A, d·x integral); closure; Liouville **`Sz.one_le_norm_mul`** |
| `AuxFun/TaylorK.lean` | 197 | `tco j f`; Leibniz `tco_mul`; `KS` predicate, asymmetric product `KS.mul_basic`; Cauchy `norm_tco_le`; unit transfer `iteratedDeriv_eq_zero_of_mul` |
| `AuxFun/WpSeries.lean` | 196 | ℘(z₀+cs), ℘′(z₀+cs) at z₀ = ω₁/2: recursion, **`ks_wpSeries`** |
| `AuxFun/LawSize.lean` | 233 | `lawk_map`, `lawk_wt` (weights), `lawk_quad`, `exists_lawk_bound`, **`sz_lawk`** |
| `AuxFun/AlgPoints.lean` | 252 | D1: `IsRep`, **`exists_alg_points`** (balanced splitting), `exists_alg_points_S` (house, den ≤ e^{A S²}) |
| `AuxFun/Chart.lean` | 220 | D3a: `ellV`, **`isRep_ellV`**, **`exists_chart`** (replaces Lemma 2.2 / 𝒯), `isRep_xi`, `isRep_half` |
| `AuxFun/Polarize.lean` | 104 | **`iteratedDeriv_line_eq_zero_of_grid`**, `…_of_span` |
| `AuxFun/LemmaUAlg.lean` | 141 | `KS.prod_pow`, **`KS.poly`**, basic factors `ks_lin`, `ks_expm`, `ks_quad` |
| `AuxFun/LemmaUId.lean` | 168 | `Fct`, `Mono.expo`, `gfac`, `Fpoly`, `Psi`; **`Fpoly_eq`** (F_t = Π R_k^D Ψ(t+sv)); `tco_eq_zero_of_small` |
| `AuxFun/LemmaUFac.lean` | 180 | **`ks_gfac`**, `exists_xi_bound`, `differentiableAt_Fpoly` |
| `AuxFun/LemmaUBounds.lean` | 178 | elementary bounds, `Nfac`, `prod_Afac_pow`, `contDiff_Psi`, `sz_natComb`, `sz_expComb` |
| `AuxFun/LemmaU.lean` | 90 | `LSG.W88.VanishAlong`, `LUData`, `small_of_bounds` |
| `AuxFun/LemmaUDir.lean` | 220 | **`lemmaU_dir`** (one point, one direction) |
| `AuxFun/LemmaUArith.lean` | 382 | **`lemmaU_arith`** (the parameter bookkeeping of Lemma U) |
| `AuxFun/LemmaUMain.lean` | 339 | **`lemmaU_core`** (Lemma U at every point of Y(S)) |
| `AuxFun/MonoIndep.lean` | 151 | D3c: **`exists_Psi_ne_zero`** (P∘exp ≢ 0 for distinct (W,U)-monomials) |
| `W88/Prop61Data.lean` | 163 | **`exists_LUData`**: number field `IntermediateField.adjoin ℚ (finite set)`, a basis of W with algebraic coordinates, `conePt` |
| `W88/Prop61Arith.lean` | 234 | `delta61`, `delta_pow`, `sq_le_delta` (uses (NR)), `log_delta_le`, **`siegel61`**, **`growth61`**, **`budget61`** |
| `W88/Prop61.lean` | 353 | `monoFam` (monomials aᵅ(eᵇ)^β Π(σ³)^{D−a_j}(σ³℘)^{a_j}), **`LSG.W88.prop61_b`** (any b ≥ 1), `prop61` (b = 1) |

Total ≈ 3.9k lines (19 files).

### `lemmaU_core` (statement)
```
theorem LSG.Aux.lemmaU_core (Ls) (ι : K →+* ℂ) (V) (Dt : LUData Ls ι μ τ) (hyV : ∀ j, Dt.y j ∈ V)
    (hwV : ∀ r, Dt.w r ∈ V) :
    ∃ c₀ ≥ 1, ∀ D L (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ) (S T A₀ A₁ : ℕ) (B U : ℝ),
      1 ≤ S → 0 ≤ B → (∀ l i, (μs l).α i ≤ A₀) → (∀ l i, (μs l).β i ≤ A₁) → (∀ l, |p l| ≤ e^B) →
      (∀ z ∈ V, ‖z‖ ≤ c₀ S → ‖Psi Ls μs p z‖ ≤ e^{−U}) →
      c₀ (B + log(L+1) + (A₀+1) log(S+1) + (A₁+1) S + (D+1) S² + (T+1) log(T+2)) ≤ U →
      ∀ h ≤ S, VanishAlong (Psi Ls μs p) (span (range Dt.w)) T (Σ h_j • Dt.y j)
```
`LUData`: y, w, X₀ (cone representatives of exp((y_j)_k)), γ₂, γ₃ ∈ K with ι γ = g, and size (H, d) for
the coordinates of y_j (G_a, exp of G_m), X₀, w_r, e₁ = ℘(ω₁/2), g₂/2.

## 3. Status (2026-10-30): **D1 + D3 DONE**

```
theorem LSG.W88.prop61 (Ls : Fin m → PeriodPair) (hg : ∀ k, IsAlgebraic ℚ (Ls k).g₂ ∧ IsAlgebraic ℚ (Ls k).g₃)
    (V W : Submodule ℂ (Tan d0 d1 m)) (hWV : W ≤ V) (hW : RationalOverQbarTan W)
    (hn : finrank ℂ V < d0 + d1 + m) (y : Fin μ → Tan d0 d1 m) (hyV : ∀ j, y j ∈ V) (hyL : ∀ j, y j ∈ Lam Ls)
    (ω : Fin κ → Tan d0 d1 m) (hωV : ∀ i, ω i ∈ V) (hωP : ∀ i, ω i ∈ Per Ls) (hω : LinearIndependent ℤ ω)
    (hNR : d1 + 2 * d0 + κ ≤ 2 * finrank ℂ V) :
    ∃ C > 0, ∃ S₀ : ℕ, ∀ S ≥ S₀, ∃ (D L : ℕ) (μs : Fin L → Mono d0 d1 m D) (p : Fin L → ℤ),
      (∀ l, Σ α ≤ Δ / log S) ∧ (∀ l, Σ β ≤ Δ / S) ∧ D ≤ Δ / S² ∧ (∃ x, Psi Ls μs p x ≠ 0) ∧
      ∀ h, (∀ j, h j ≤ S) → VanishAlong (Psi Ls μs p) W (Δ / log S) (Σ h_j • y_j)
  -- Δ = delta61 C (d1 + 2m − κ) d0 (d − n) S = (C S^{d1+2m−κ} (log S)^{d0})^{1/(d−n)}
```
`Psi Ls μs p x = Σ_l p_l (μs l).eval Ls x` (the monomials evaluated on `exp_G` via `ellW = (σ³, σ³℘, σ³℘′)`);
the μs are distinct monomials with elliptic part `(σ³)^{D−a_j}(σ³℘)^{a_j}`, homogeneous of degree `D` in every block.
`#print axioms LSG.W88.prop61`: [propext, Classical.choice, Quot.sound]. Build: `lake build LSG.W88.Prop61`
(≈ 5 min from the Stage-2 oleans; the slowest files are `LemmaUMain`, `Prop61` ≈ 1 min each).

**Remark B (2026-10-30, continuation): `LSG.W88.prop61_b (b : ℕ) (hb : 1 ≤ b)`**, same hypotheses, with
Δ = `delta61 C (d1+2m−κ) (b*d0) (d−n) S` = (C S^{d₁+2m−κ}(log S)^{b d₀})^{1/(d−n)} and the `G_a` degree bound
Σα ≤ Δ/(log S)^b (W88's `D₀ (log S)^b = Δ`); the other bounds and the multiplicity order Δ/log S (a = 1) are
unchanged. `prop61` is now the corollary `b = 1` (`simpa only [one_mul, pow_one]`). Changes: A₀ = ⌊Δ/(ν (log S)^b)⌋,
`siegel61` applied with (log S)^b in place of log S (it is generic in that variable), and A₀ ≤ Δ/(ν log S) for
`growth61`/`budget61` (the budget term only shrinks). `#print axioms LSG.W88.prop61_b`:
[propext, Classical.choice, Quot.sound]. (b is a natural number; real b would only need rpow for (log S)^b.)

### What the proof does (vs. W_UPGRADE)
* Step 1 = `prop21_G_deg` with r = ν²S, R = ν³S, U = ν⁶Δ, Siegel parameter Δ/ν, monomial degrees ⌊Δ/(ν log S)⌋,
  ⌊Δ/(νS)⌋, ⌊Δ/(νS²)⌋; ν = 3 + c₁ + c₀ + 16 m c_W + c₀(9 + 3K_t) and C = max(1, c₂ν^{6(n+1)}/K_ν) explicit.
* Step 2′ at **every** t ∈ Y(S) (no 𝒯, no F′, no product over translations): `lemmaU_core`.
* (NR) is used exactly once, in `sq_le_delta` (Δ ≥ S², needed for c₁ r² log(R/r) ≤ U).

### Remaining gaps / next steps (for D4)
1. **Bridge to the algebraic side** (not done): `Psi Ls μs p` ↦ an `MvPolynomial (Var d₀ d₁ m)` (G_m as Y with
   YZ = 1, elliptic blocks (U, V, W) = (σ³℘, σ³℘′, σ³)), `P ∉ IG` from `∃ x, Psi x ≠ 0`, and analytic `VanishAlong`
   ↦ `LSG.ME.VanishesAlong` (derivations `Dw` along W in the chart at each point). Est. 400–600 lines
   (the chart identity `δ = L·D` of `ME/Deriv.lean` + one-variable Taylor along lines).
2. ~~Remark B~~: **done** (`prop61_b`, natural b ≥ 1).
3. Vector extensions (class 𝒞, MG♮/MX/MX′): not covered (G₂ = E^m only); `prop21_G` and the chart lemma would need
   the E^♮ coordinates.
4. Multiplicity T + 1 for Philippon: take Δ/log S ≥ T + 1 downstream (our statement gives all k < Δ/log S).

## 4. Log
* 2026-10-30: plan; NFSize, TaylorK, WpSeries, LawSize, AlgPoints, Chart, Polarize, LemmaUAlg/Id/Fac/Bounds, LemmaU,
  LemmaUDir, LemmaUArith, LemmaUMain (`lemmaU_core`), MonoIndep, Prop61Data, Prop61Arith, Prop61 (`prop61`). All
  axiom-clean; no sorry. Lesson: in proofs with ~100 hypotheses, bare `linarith`/`nlinarith` time out
  (Positivstellensatz products); use `linarith only [...]` or move arithmetic into small standalone lemmas.
* 2026-10-30 (continuation): Remark B, `prop61_b` (+32 lines in `Prop61.lean`); `prop61` = `prop61_b 1`.
