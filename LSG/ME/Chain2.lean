import Mathlib
import LSG.ME.PhOpTwo
import LSG.ME.Chain

/-!
# Roy's chain of ideals with Philippon's operators (chain v2; STAGE2 §10)

Chain v1 (`LSG.ME.Chain`) generates `L_r` by derivation words `D_l P`, whose elliptic degrees grow
with `r T`. Here the generators are Philippon's operators `δ^κ_σ P = phOp σ w c c' κ P`, of block
degree `dblE D` **for every `κ`**, so all ideals of the chain, and the ideal `A` of Roy's vanishing
claim, are generated in degrees independent of `T` and `r`.

* `gensR2 r = {phOp σ w c c' κ P : σ ∈ Σ[r], w ∈ W, κ ≤ r T, all c, c'}`,
  `Lr2 r = I_G ⊔ (gensR2 r)`; monotone (`Lr2_mono`).
* **Degrees**: `gensR2_mem_FLE` (`FLE (dblE D)`, i.e. elliptic degrees `≤ 2 D`, the others `≤ D`),
  `transl_gensR2_mem_FLE` (`FLE (dblE (dblE D)) ≤ FLE (4 • D)`), independent of `T` and `r`.
* **Nontriviality**: `Lr2_le_vanish_zero` (formal order `> r T` along `W` on `Σ[r]`).
* **`exists_flat2`**: some `r < d₀ + d₁ + m` has `hdim L_{r+1} = hdim L_r`.
* **`hAVO2`** (Roy's vanishing claim): for `p ⊇ L_{r+1}`, `V = Z(p)`, `GV` stabilizing `V`,
  `A₂ = I_G ⊔ (τ v c Q : Q ∈ gensR2 r, v ∈ V, all c)` has formal order `> T` along `W` on
  `⋃ s ∈ S, s + GV` (`A₂ ≤ ordIdeal W T (⋃ s ∈ S, s + GV)`); `A₂` is generated in `FLE (4 • D)`.
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE hdata hdata_le_of_le hdim_section_lt hdim_add_height_eq)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

section Chain2

variable [DecidableEq K] [CharZero K]

variable (g₂ g₃) (W : Submodule K (LieE K d₀ d₁ m)) (S : Finset (GPt K d₀ d₁ g₂ g₃))
  (P : MvPolynomial (Var d₀ d₁ m) K) (T : ℕ)

/-- Generators of `L_r`: Philippon's operators `δ^κ_σ P`, `σ ∈ Σ[r]`, `w ∈ W`, `κ ≤ r T`. -/
def gensR2 (r : ℕ) : Set (MvPolynomial (Var d₀ d₁ m) K) :=
  {Q | ∃ σ ∈ sig S r, ∃ w ∈ W, ∃ κ ≤ r * T, ∃ c c' : Fin m → Fin 2,
    Q = phOp g₂ g₃ σ w c c' κ P}

/-- Roy's ideal `L_r = I_G + (gensR2 r)` (chain v2). -/
noncomputable def Lr2 (r : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span (gensR2 g₂ g₃ W S P T r)

variable {g₂ g₃ W S P T}

omit [CharZero K] in
theorem gensR2_mono (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (r : ℕ) :
    gensR2 g₂ g₃ W S P T r ⊆ gensR2 g₂ g₃ W S P T (r + 1) := by
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  exact ⟨σ, sig_mono hS r hσ, w, hw, κ, by nlinarith, c, c', rfl⟩

omit [CharZero K] in
theorem Lr2_mono (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (r : ℕ) :
    Lr2 g₂ g₃ W S P T r ≤ Lr2 g₂ g₃ W S P T (r + 1) :=
  sup_le_sup_left (Ideal.span_mono (gensR2_mono hS r)) _

omit [CharZero K] in
theorem Lr2_mono' (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) {r r' : ℕ} (h : r ≤ r') :
    Lr2 g₂ g₃ W S P T r ≤ Lr2 g₂ g₃ W S P T r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Lr2_mono hS n)

omit [CharZero K] in
theorem phGens_subset_gensR2 {σ : GPt K d₀ d₁ g₂ g₃} {r : ℕ} (hσ : σ ∈ sig S r) :
    phGens g₂ g₃ W {P} σ (r * T) ⊆ gensR2 g₂ g₃ W S P T r := by
  rintro _ ⟨Q, hQ, w, hw, κ, hκ, c, c', rfl⟩
  rw [Set.mem_singleton_iff.mp hQ]
  exact ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩

/-! ### Degrees (independent of `T` and `r`) -/

omit [CharZero K] in
/-- **Block degrees of the generators**: `FLE (dblE D)` for all `r`, `T`. -/
theorem gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE K blk D) (r : ℕ) :
    ∀ Q ∈ gensR2 g₂ g₃ W S P T r, Q ∈ FLE K blk (dblE D) := by
  rintro _ ⟨σ, _, w, _, κ, _, c, c', rfl⟩
  exact phOp_mem_FLE σ w c c' κ hPD

theorem dblE_dblE_le (D : Blk m → ℕ) : dblE (dblE D) ≤ 4 • D := fun b => by
  simp only [dblE, Pi.smul_apply, smul_eq_mul]
  have := bmul_le_two b
  calc bmul b * (bmul b * D b) ≤ 2 * (2 * D b) :=
        Nat.mul_le_mul this (Nat.mul_le_mul_right _ this)
    _ = 4 * D b := by ring

omit [CharZero K] in
/-- Translates of generators (the generators of `A₂`): `FLE (dblE (dblE D)) ⊆ FLE (4 • D)`. -/
theorem transl_gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE K blk D) (r : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) K} (hQ : Q ∈ gensR2 g₂ g₃ W S P T r)
    (v : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) :
    τ g₂ g₃ v c Q ∈ FLE K blk (dblE (dblE D)) :=
  transl_mem_FLE v c (gensR2_mem_FLE hPD r Q hQ)

/-! ### Nontriviality -/

variable (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- **The last ideal vanishes at `0`** when `P` has formal order `> r T` along `W` on `Σ[r]`. -/
theorem Lr2_le_vanish_zero {d : Fin m → ℕ} (hP : IsHomE P d) {r : ℕ}
    (hvan : ∀ g ∈ sig S r, OrdGt g₂ g₃ W P (r * T) g) :
    Lr2 g₂ g₃ W S P T r ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) := by
  refine sup_le (IG_le_vanish two_ne_zero _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  have h0 := (zeros_phOp hΔ W (Qs := {P}) (fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩)
    σ 0 (r * T)).mpr (fun Q hQ => by rw [Set.mem_singleton_iff.mp hQ, zero_add]; exact hvan σ hσ)
  rw [mem_zeros_iff_le_vanish] at h0
  exact h0 (Ideal.mem_sup_right (Ideal.subset_span ⟨P, rfl, w, hw, κ, hκ, c, c', rfl⟩))

/-! ### The pigeonhole -/

omit [DecidableEq K] [CharZero K] hΔ in
theorem coeff_zero_aeval_fexp (p : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m)
    (Q : MvPolynomial (Var d₀ d₁ m) K) :
    PowerSeries.coeff 0 (aeval (fexp g₂ g₃ p w) Q) = eval (coords p 1) Q := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_aeval]
  simp only [fexp_const]; rfl

variable [IsAlgClosed K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include hD

/-- `hdim L₀ < d₀ + d₁ + 2m` (`P ∉ I_G`, `I_G` prime). -/
theorem hdim_Lr2_zero_lt {d : Fin m → ℕ} (hP : IsHomE P d)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) (hL0 : Lr2 g₂ g₃ W S P T 0 ≠ ⊤) :
    (hdata blk D K (Lr2 g₂ g₃ W S P T 0)).1 < d₀ + d₁ + 2 * m := by
  have hprime := IG_isPrime (d₀ := d₀) (d₁ := d₁) g₂ g₃ two_ne_zero
  rw [← vanish_univ hΔ two_ne_zero] at hPI
  obtain ⟨h, -, lam, hh⟩ : ∃ h ∈ (Set.univ : Set (GPt K d₀ d₁ g₂ g₃)), ∃ lam,
      eval (coords h lam) P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPI (mem_vanish.mpr hcon)
  have hh1 : eval (coords h 1) P ≠ 0 := by
    intro h1
    apply hh
    rw [coords_eq_scl h lam]
    change aeval (scl (fun k => (lam k : K)) (coords h 1)) P = 0
    rw [aeval_scl hP]
    change _ * eval (coords h 1) P = 0
    rw [h1, mul_zero]
  obtain ⟨c, hc⟩ := exists_good two_ne_zero hΔ h 0
  obtain ⟨c', hc'⟩ := exists_good two_ne_zero hΔ (0 : GPt K d₀ d₁ g₂ g₃) 0
  set Q₀ := phOp g₂ g₃ 0 0 c c' 0 P
  have hQ₀ : Q₀ ∈ Lr2 g₂ g₃ W S P T 0 :=
    Ideal.mem_sup_right (Ideal.subset_span
      ⟨0, zero_mem_sig S, 0, W.zero_mem, 0, Nat.zero_le _, c, c', rfl⟩)
  have hτ : Q₀ ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
    intro hm
    have h1 := mem_vanish.mp (IG_le_vanish two_ne_zero Set.univ hm) h (Set.mem_univ _) 1
    rw [eval_phOp_coords, aeval_lawPt hΔ hP, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul, constantCoeff_aeval] at h1
    simp only [fexp_const, add_zero] at h1
    change _ * eval (coords h 1) P = 0 at h1
    have hu : IsUnit (∏ k, lawPt g₂ g₃ h 1 0 0 c c' (.e k (chartAt (h + 0) k)) ^ d k) :=
      IsUnit.prod_univ_iff.mpr fun k => (lawPt_unit hΔ h 1 0 0 hc hc' k).pow _
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, add_zero] at hu
    exact (mul_ne_zero hu hh1) h1
  have hlt := hdim_section_lt blk D K hD (J := IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) (P := Q₀)
    (fun Q hQ => (hprime.mem_or_mem hQ).resolve_left hτ)
    (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQ₀))) hL0
  rwa [hdim_IG D hD two_ne_zero] at hlt

/-- **Pigeonhole** (chain v2): two consecutive ideals have the same Hilbert dimension. -/
theorem exists_flat2 {d : Fin m → ℕ} (hP : IsHomE P d) (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
    (hlast : Lr2 g₂ g₃ W S P T (d₀ + d₁ + m) ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃))) :
    ∃ r < d₀ + d₁ + m,
      (hdata blk D K (Lr2 g₂ g₃ W S P T (r + 1))).1 = (hdata blk D K (Lr2 g₂ g₃ W S P T r)).1 := by
  have hlast' : Lr2 g₂ g₃ W S P T (d₀ + d₁ + m) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlast
  have hne : ∀ r ≤ d₀ + d₁ + m, Lr2 g₂ g₃ W S P T r ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hlast' (Lr2_mono' hS hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d₀ + d₁ + m, (hdata blk D K (Lr2 g₂ g₃ W S P T (r + 1))).1 <
      (hdata blk D K (Lr2 g₂ g₃ W S P T r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D K (Lr2_mono hS r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d₀ + d₁ + m, (hdata blk D K (Lr2 g₂ g₃ W S P T r)).1 + r ≤
      (hdata blk D K (Lr2 g₂ g₃ W S P T 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have h0 := hdim_Lr2_zero_lt hΔ D hD hP hPI (hne 0 (Nat.zero_le _))
  have h1 := hdec (d₀ + d₁ + m) le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlast
  omega

end Chain2

/-! ### Roy's vanishing claim -/

section AVO

variable [DecidableEq K] [CharZero K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- **Roy's vanishing claim** (chain v2): with `p ⊇ L_{r+1}`, `V = Z(p)` and `GV` stabilizing `V`,
the ideal `A₂ = I_G + (τ v c Q : Q ∈ gensR2 r, v ∈ V, all c)` has formal order `> T` along `W` on
`⋃ s ∈ S, s + GV`. Its generators lie in `FLE (dblE (dblE D)) ⊆ FLE (4 • D)`
(`transl_gensR2_mem_FLE`). -/
theorem hAVO2 (W : Submodule K (LieE K d₀ d₁ m)) (S : Finset (GPt K d₀ d₁ g₂ g₃))
    {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d) (T r : ℕ)
    {p : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (hLp : Lr2 g₂ g₃ W S P T (r + 1) ≤ p)
    (GV : Set (GPt K d₀ d₁ g₂ g₃))
    (hGV : ∀ u ∈ GV, ∀ v ∈ zeros (g₂ := g₂) (g₃ := g₃) (p : Set _), u + v ∈ zeros (p : Set _)) :
    IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span {Q' | ∃ Q ∈ gensR2 g₂ g₃ W S P T r,
        ∃ v ∈ zeros (g₂ := g₂) (g₃ := g₃) (p : Set _), ∃ c, Q' = τ g₂ g₃ v c Q} ≤
      ordIdeal g₂ g₃ W T (⋃ s ∈ S, gtransl s GV) := by
  refine sup_le (IG_le_ordIdeal W T _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨_, ⟨σ, hσ, w', hw', κ, hκ, c₁, c₂, rfl⟩, v, hv, c, rfl⟩ y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨s, hs, hy⟩ := hy
  have hu : y - s ∈ GV := mem_gtransl.mp hy
  -- 1. `P` has formal order `> (r + 1) T` at `y + v + σ`
  have hz : y - s + v ∈ zeros ((IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔
      Ideal.span (phGens g₂ g₃ W {P} (σ + s) ((r + 1) * T)) : Ideal _) : Set _) := by
    have h1 := hGV _ hu v hv
    rw [mem_zeros_iff_le_vanish] at h1 ⊢
    refine le_trans (sup_le ?_ ?_) (hLp.trans h1)
    · exact le_sup_left
    · exact (Ideal.span_mono (phGens_subset_gensR2 (add_mem_sig hσ hs))).trans le_sup_right
  have hord := (zeros_phOp hΔ W (Qs := {P}) (fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩)
    (σ + s) (y - s + v) ((r + 1) * T)).mp hz P rfl
  rw [show y - s + v + (σ + s) = y + v + σ by abel] at hord
  -- 2. all words of length `≤ (r + 1) T` kill `P` at `y + v + σ`
  have hvog := vog_of_ordGt hord
  -- 3. the two-parameter lemma and the translation by `v`
  exact ordGt_transl_phOp hΔ hP hvog hw' c c₁ c₂ (by rw [Nat.succ_mul]; omega)

end AVO

end LSG.ME
