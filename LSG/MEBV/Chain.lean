/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Comp
import LSG.MEBV.SliceIG
import LSG.MEBV.PhOpTwo

/-!
# Roy's chain with Philippon's operators, relevant pigeonhole, Roy's vanishing claim (M2.5 α; template `LSG.MEB.Chain`)

Template: `LSG.ME.{Chain, Chain2, MainAbChain, MainAbSlice}`. The analytic input is β's (STAGE_A4 §7.3, request
(2)): `phOp`, `phOp_mem_FLE`, `isHomV_phOp`, `phOp_mem_vanish`, `ordGtV_of_phOp_mem_vanish`, the two-parameter lemma
`ordGtV_phOp`, translation invariance `ordGtV_lawSub`, and the order ideal `ordIdealB`.

Here `n = dim G̃ = d₀ + d₁ + Σ_k (g_k + 1)` (`dimG`).

* `sigB` lemmas; `gensR2 r = {phOp σ w c c' κ P : σ ∈ Σ[r], w ∈ W, κ ≤ r T}`, `Lr2 r = IGsem ⊔ (gensR2 r)`.
* Degrees: `gensR2_mem_FLE` (`dblB B D`), `transl_gensR2_mem_FLE` (`dblB B (dblB B D) ≤ LV B • D`), `isHomV_gensR2`.
* `Lr2_le_vanish_zero`.
* Dimensions: **`hdim_IGsem_le`**: `hdim IGsem ≤ n + m` (slicing and B6);
  **`hdim_ge_of_le_vanish_zero`**: `m ≤ hdim L` for `L ≤ I({0})` (slicing).
* **`exists_flat_rel`**: some `r < n` has `hdim (relI L_{r+1}) = hdim (relI L_r)`.
* **`hAVO2`** (Roy's vanishing claim): `A₂ = IGexp ⊔ (τ v c Q : Q ∈ gensR2 r, v ∈ Z(p))` lies in
  `ordIdealB W T (⋃ s ∈ S, s + GV)`.
* **`Zs_subset_transl`**: the normalised zeros `h` of `A₂` satisfy `h + V ⊆ Z(L_r)`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The sets `Σ[r]` -/

theorem zero_mem_sigB (S : Finset (GPt d₀ d₁ B)) : (0 : GPt d₀ d₁ B) ∈ sigB S 0 :=
  ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_sigB {S : Finset (GPt d₀ d₁ B)} {r : ℕ} {g s : GPt d₀ d₁ B}
    (hg : g ∈ sigB S r) (hs : s ∈ S) : g + s ∈ sigB S (r + 1) := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  refine ⟨Fin.snoc σ s, fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hs
    · simpa using hσ i
  · simp [Fin.sum_univ_castSucc]

theorem sigB_mono {S : Finset (GPt d₀ d₁ B)} (hS : (0 : GPt d₀ d₁ B) ∈ S) (r : ℕ) :
    sigB S r ⊆ sigB S (r + 1) :=
  fun g hg => by simpa using add_mem_sigB hg hS

theorem sigB_zero {S : Finset (GPt d₀ d₁ B)} {g : GPt d₀ d₁ B} (hg : g ∈ sigB S 0) : g = 0 := by
  obtain ⟨σ, -, rfl⟩ := hg
  simp

/-! ### The chain -/

section Chain

variable (W : Submodule ℂ (Tan d₀ d₁ B)) (S : Finset (GPt d₀ d₁ B))
  (P : MvPolynomial (Var d₀ d₁ B) ℂ) (T : ℕ)

/-- Generators of `L_r`: Philippon's operators `δ^κ_σ P`, `σ ∈ Σ[r]`, `w ∈ W`, `κ ≤ r T`. -/
def gensR2 (r : ℕ) : Set (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  {Q | ∃ σ ∈ sigB S r, ∃ w ∈ W, ∃ κ ≤ r * T, ∃ c c' : ∀ k, Fin (B k).nLV,
    Q = phOp σ w c c' κ P}

/-- Roy's ideal `L_r = IGsem + (gensR2 r)`. -/
noncomputable def Lr2 (r : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  IGsem d₀ d₁ B ⊔ Ideal.span (gensR2 W S P T r)

variable {W S P T}

theorem gensR2_mono (hS : (0 : GPt d₀ d₁ B) ∈ S) (r : ℕ) :
    gensR2 W S P T r ⊆ gensR2 W S P T (r + 1) := by
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  exact ⟨σ, sigB_mono hS r hσ, w, hw, κ, by nlinarith, c, c', rfl⟩

theorem Lr2_mono (hS : (0 : GPt d₀ d₁ B) ∈ S) (r : ℕ) :
    Lr2 W S P T r ≤ Lr2 W S P T (r + 1) :=
  sup_le_sup_left (Ideal.span_mono (gensR2_mono hS r)) _

theorem Lr2_mono' (hS : (0 : GPt d₀ d₁ B) ∈ S) {r r' : ℕ} (h : r ≤ r') :
    Lr2 W S P T r ≤ Lr2 W S P T r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Lr2_mono hS n)

/-- **Block degrees of the generators**: `FLE (dblB D)` for all `r`, `T`. -/
theorem gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE ℂ blk D) (r : ℕ) :
    ∀ Q ∈ gensR2 W S P T r, Q ∈ FLE ℂ blk (dblB B D) := by
  rintro _ ⟨σ, _, w, _, κ, _, c, c', rfl⟩
  exact phOp_mem_FLE σ w c c' κ hPD

variable (B) in
/-- The degree multiplier of two translations: `(2^{eL B})²` (MEB: `4`). -/
def LV : ℕ := (2 ^ eL B) ^ 2

theorem one_le_LV : 1 ≤ LV B := Nat.one_le_pow _ _ (pow_pos two_pos _)

theorem dblB_dblB_le (D : Blk m → ℕ) : dblB B (dblB B D) ≤ LV B • D := fun b => by
  simp only [dblB, Pi.smul_apply, smul_eq_mul, LV]
  have := bmulB_le (B := B) b
  calc bmulB B b * (bmulB B b * D b) ≤ 2 ^ eL B * (2 ^ eL B * D b) :=
        Nat.mul_le_mul this (Nat.mul_le_mul_right _ this)
    _ = (2 ^ eL B) ^ 2 * D b := by ring

/-- Translates of generators (the generators of `A₂`): `FLE (dblB (dblB D))`. -/
theorem transl_gensR2_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE ℂ blk D) (r : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} (hQ : Q ∈ gensR2 W S P T r)
    (v : GPt d₀ d₁ B) (c : ∀ k, Fin (B k).nLV) :
    τ v c Q ∈ FLE ℂ blk (dblB B (dblB B D)) :=
  transl_mem_FLE v c (gensR2_mem_FLE hPD r Q hQ)

theorem isHomV_gensR2 {d : Fin m → ℕ} (hP : IsHomV P d) {r : ℕ} :
    ∀ Q ∈ gensR2 W S P T r, IsHomV Q (ldMul B d) := by
  rintro _ ⟨σ, _, w, _, κ, _, c, c', rfl⟩
  exact isHomV_phOp σ w c c' κ hP

/-- **The last ideal vanishes at `0`** when `P` has order `> r T` along `W` on `Σ[r]`. -/
theorem Lr2_le_vanish_zero {d : Fin m → ℕ} (hP : IsHomV P d) {r : ℕ}
    (hvan : ∀ g ∈ sigB S r, OrdGtV W P (r * T) g) :
    Lr2 W S P T r ≤ vanish ({0} : Set (GPt d₀ d₁ B)) := by
  refine sup_le (fun Q hQ => mem_vanish.mpr fun g _ lam => mem_vanish.mp hQ g (Set.mem_univ _) lam)
    (Ideal.span_le.mpr ?_)
  · rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
    exact phOp_mem_vanish hP (by rw [zero_add]; exact hvan σ hσ) hw hκ c c'

end Chain

/-! ### Dimensions -/

section Dims

variable (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include hD

/-- **Ideals vanishing at `0` have dimension `≥ m`** (slice `I({0})` once in every block). -/
theorem hdim_ge_of_le_vanish_zero {L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)}
    (hL : L ≤ vanish ({0} : Set (GPt d₀ d₁ B))) : m ≤ (hdata blk D ℂ L).1 := by
  classical
  obtain ⟨α, hα⟩ := exists_good_alpha (d₀ := d₀) (d₁ := d₁) (B := B)
    (Set.singleton_nonempty (0 : GPt d₀ d₁ B)) {0}
  have hα' : ∀ k, lsl α k ∉ vanish ({0} : Set (GPt d₀ d₁ B)) := fun k h =>
    hα 0 (Finset.mem_singleton_self 0) k (by rwa [gtransl_zero])
  have hp := vanish_singleton_isPrime (0 : GPt d₀ d₁ B)
  obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hp hα'
  have hdrop := hdim_vanishP_add_le D hD hp hα' hg₀ hs₀ Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hdrop
  have h := hdata_le_of_le blk D ℂ hL (vanish_ne_top (Set.singleton_nonempty _))
  rcases h with h | ⟨h, -⟩ <;> omega

/-- **`hdim IGsem ≤ dim G + m`**: slice once in every block (`hfun_le_sl`) and use B6 (`hfun_slIGexp_le`). -/
theorem hdim_IGsem_le :
    (hdata blk D ℂ (IGsem d₀ d₁ B)).1 ≤ d₀ + d₁ + ∑ k, ((B k).g + 1) + m := by
  classical
  obtain ⟨α, hα⟩ := exists_good_alpha (d₀ := d₀) (d₁ := d₁) (B := B)
    (Set.univ_nonempty : (Set.univ : Set (GPt d₀ d₁ B)).Nonempty) {0}
  have hα' : ∀ k, lsl α k ∉ IGsem d₀ d₁ B := fun k h =>
    hα 0 (Finset.mem_singleton_self 0) k (by rwa [gtransl_zero])
  have hp : (vanish (Set.univ : Set (GPt d₀ d₁ B))).IsPrime := IGsem_isPrime
  have hspec := StrongSix.M2.hdata_spec blk D ℂ (IGsem_ne_top (d₀ := d₀) (d₁ := d₁) (B := B))
  obtain ⟨hdeg, hlc, hP0⟩ := polB_data (B := B) (d₀ := d₀) (d₁ := d₁) hD
  set Q : Polynomial ℤ := (∏ k : Fin m, (Polynomial.C (D (.e k) : ℤ) * Polynomial.X + 1)) *
    polB B d₀ d₁ D
  have hlin : ∀ k : Fin m, Polynomial.C (D (.e k) : ℤ) * Polynomial.X + 1 ≠ 0 ∧
      (Polynomial.C (D (.e k) : ℤ) * Polynomial.X + 1).natDegree = 1 := fun k => by
    have ha : (D (.e k) : ℤ) ≠ 0 := by have := hD (.e k); omega
    have h1 := Polynomial.natDegree_linear (b := (1 : ℤ)) ha
    rw [map_one] at h1
    refine ⟨fun h0 => ?_, h1⟩
    rw [h0, Polynomial.natDegree_zero] at h1
    omega
  have hprod0 : (∏ k : Fin m, (Polynomial.C (D (.e k) : ℤ) * Polynomial.X + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => (hlin k).1
  have hQ0 : Q ≠ 0 := mul_ne_zero hprod0 hP0
  have hQdeg : Q.natDegree = m + (d₀ + d₁ + ∑ k, ((B k).g + 1)) := by
    rw [Polynomial.natDegree_mul hprod0 hP0, hdeg,
      Polynomial.natDegree_prod _ _ fun k _ => (hlin k).1,
      Finset.sum_congr rfl fun k _ => (hlin k).2]
    simp
  have hg := StrongSix.M2.hasData_poly hQ0
  have hle : ∀ t : ℕ, (hfun blk D ℂ (IGsem d₀ d₁ B) t : ℤ) ≤ Q.eval (t : ℤ) := by
    intro t
    have h1 := hfun_le_sl α hp hα' D t
    have h2 := StrongSix.M2.hfun_mono blk D ℂ (sup_le_sup_right (IGexp_le_IGsem
      (d₀ := d₀) (d₁ := d₁) (B := B)) (Ideal.span _) : sl α (IGexp d₀ d₁ B) ≤ sl α (IGsem d₀ d₁ B)) t
    have h3 := hfun_slIGexp_le (d₀ := d₀) (d₁ := d₁) α D t
    have e1 : Q.eval (t : ℤ) = (∏ k : Fin m, ((t : ℤ) * D (.e k) + 1)) *
        (polB B d₀ d₁ D).eval (t : ℤ) := by
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      congr 1
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [e1, polB_eval]
    have := h1.trans (Nat.mul_le_mul_left _ (h2.trans h3))
    exact_mod_cast this
  rcases hspec.compare hg (Filter.Eventually.of_forall hle)
    (Filter.Eventually.of_forall fun _ => by positivity) with h | ⟨h, -⟩ <;> omega

end Dims

/-! ### The relevant pigeonhole -/

section Flat

variable {W : Submodule ℂ (Tan d₀ d₁ B)} {S : Finset (GPt d₀ d₁ B)}
  {P : MvPolynomial (Var d₀ d₁ B) ℂ} {T : ℕ} (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include hD

/-- Some generator of `L₀` lies outside `IGsem` (`P ∉ IGsem`, β's `ordGtV_of_phOp_mem_vanish`). -/
theorem exists_gen_L0_notMem {d : Fin m → ℕ} (hP : IsHomV P d) (hPI : P ∉ IGsem d₀ d₁ B) :
    ∃ Q ∈ gensR2 W S P T 0, Q ∉ IGsem d₀ d₁ B := by
  by_contra hcon
  push_neg at hcon
  apply hPI
  refine mem_IGsem_iff_liftZ.mpr fun u μ => ?_
  have hord : OrdGtV W P 0 (expG d₀ d₁ B u + 0) := by
    refine ordGtV_of_phOp_mem_vanish hP fun w hw κ hκ c c' => ?_
    have hmem := hcon _ ⟨0, zero_mem_sigB S, w, hw, κ, by simpa using hκ, c, c', rfl⟩
    exact vanish_antitone (Set.subset_univ _) hmem
  rw [add_zero] at hord
  have := (ordGtV_iff hP).mp hord u rfl μ 0 W.zero_mem 0 le_rfl
  simpa [lineF] using this

/-- `hdim L₀ < hdim IGsem` (`P ∉ IGsem`, `IGsem` prime). -/
theorem hdim_Lr2_zero_lt_IGsem {d : Fin m → ℕ} (hP : IsHomV P d) (hPI : P ∉ IGsem d₀ d₁ B)
    (hL0 : Lr2 W S P T 0 ≠ ⊤) :
    (hdata blk D ℂ (Lr2 W S P T 0)).1 < (hdata blk D ℂ (IGsem d₀ d₁ B)).1 := by
  obtain ⟨Q₀, hQ₀, hQ₀I⟩ := exists_gen_L0_notMem D hD hP hPI
  have hprime := IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)
  exact StrongSix.M2.hdim_section_lt blk D ℂ hD (J := IGsem d₀ d₁ B) (P := Q₀)
    (L := Lr2 W S P T 0)
    (fun Q hQ => (hprime.mem_or_mem hQ).resolve_left hQ₀I)
    (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (Ideal.mem_sup_right (Ideal.subset_span hQ₀))))) hL0

/-- `hdim L₀ < dim G + m`. -/
theorem hdim_Lr2_zero_lt {d : Fin m → ℕ} (hP : IsHomV P d) (hPI : P ∉ IGsem d₀ d₁ B)
    (hL0 : Lr2 W S P T 0 ≠ ⊤) :
    (hdata blk D ℂ (Lr2 W S P T 0)).1 < d₀ + d₁ + ∑ k, ((B k).g + 1) + m := by
  have := hdim_Lr2_zero_lt_IGsem D hD hP hPI hL0
  have := hdim_IGsem_le (d₀ := d₀) (d₁ := d₁) (B := B) D hD
  omega

/-- **Pigeonhole for the relevant radicals of the chain** (`n = dim G`). -/
theorem exists_flat_rel {d : Fin m → ℕ} (hP : IsHomV P d) (hS : (0 : GPt d₀ d₁ B) ∈ S)
    (hPI : P ∉ IGsem d₀ d₁ B)
    (hlast : Lr2 W S P T (d₀ + d₁ + ∑ k, ((B k).g + 1)) ≤ vanish ({0} : Set (GPt d₀ d₁ B))) :
    ∃ r < d₀ + d₁ + ∑ k, ((B k).g + 1),
      (hdata blk D ℂ (relI d₀ d₁ B (Lr2 W S P T (r + 1)))).1 =
        (hdata blk D ℂ (relI d₀ d₁ B (Lr2 W S P T r))).1 := by
  set n := d₀ + d₁ + ∑ k, ((B k).g + 1)
  set J : ℕ → Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) := fun r => relI d₀ d₁ B (Lr2 W S P T r)
  have hlastJ : J n ≤ vanish ({0} : Set (GPt d₀ d₁ B)) := relI_le_vanish_zero hlast
  have hlast' : J n ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlastJ
  have hmono : ∀ r, J r ≤ J (r + 1) := fun r => relI_mono (Lr2_mono hS r)
  have hmono' : ∀ {r r'}, r ≤ r' → J r ≤ J r' := by
    intro r r' h
    induction r', h using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (hmono n)
  have hne : ∀ r ≤ n, J r ≠ ⊤ := fun r hr => ne_top_of_le_ne_top hlast' (hmono' hr)
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ r < n, (hdata blk D ℂ (J (r + 1))).1 < (hdata blk D ℂ (J r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D ℂ (hmono r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ n, (hdata blk D ℂ (J r)).1 + r ≤ (hdata blk D ℂ (J 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have hL0 : Lr2 W S P T 0 ≠ ⊤ := ne_top_of_le_ne_top (hne 0 (Nat.zero_le _)) (le_relI _)
  have h0 := hdim_Lr2_zero_lt D hD hP hPI hL0
  have h0' : (hdata blk D ℂ (J 0)).1 ≤ (hdata blk D ℂ (Lr2 W S P T 0)).1 := by
    rcases hdata_le_of_le blk D ℂ (show Lr2 W S P T 0 ≤ J 0 from le_relI _)
      (hne 0 (Nat.zero_le _)) with h | ⟨h, -⟩ <;> omega
  have h1 := hdec n le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlastJ
  omega

end Flat

/-! ### Roy's vanishing claim -/

/-- **Roy's vanishing claim** (chain v2): with `p ⊇ L_{r+1}` and `GV` stabilizing `Z(p)`, the ideal
`A₂ = IGexp + (τ v c Q : Q ∈ gensR2 r, v ∈ Z(p), all c)` has order `> T` along `W` on `⋃ s ∈ S, s + GV`. -/
theorem hAVO2 (W : Submodule ℂ (Tan d₀ d₁ B)) (S : Finset (GPt d₀ d₁ B))
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) (T r : ℕ)
    {p : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} (hLp : Lr2 W S P T (r + 1) ≤ p)
    (GV : Set (GPt d₀ d₁ B))
    (hGV : ∀ u ∈ GV, ∀ v ∈ (zeros (p : Set _) : Set (GPt d₀ d₁ B)), u + v ∈ zeros (p : Set _)) :
    IGexp d₀ d₁ B ⊔ Ideal.span {Q' | ∃ Q ∈ gensR2 W S P T r,
        ∃ v ∈ (zeros (p : Set _) : Set (GPt d₀ d₁ B)), ∃ c, Q' = τ v c Q} ≤
      ordIdealB W T (⋃ s ∈ S, gtransl s GV) := by
  refine sup_le (IGexp_le_IGsem.trans (IGsem_le_ordIdealB T _)) (Ideal.span_le.mpr ?_)
  rintro _ ⟨_, ⟨σ, hσ, w', hw', κ, hκ, c₁, c₂, rfl⟩, v, hv, c, rfl⟩
  refine mem_ordIdealB_of (isHomV_transl v c (isHomV_phOp σ w' c₁ c₂ κ hP)) fun y hy => ?_
  simp only [Set.mem_iUnion] at hy
  obtain ⟨s, hs, hy⟩ := hy
  have hu : y - s ∈ GV := mem_gtransl.mp hy
  -- 1. `P` has order `> (r + 1) T` at `(y + v) + σ`
  have hz : y - s + v ∈ (zeros (p : Set _) : Set (GPt d₀ d₁ B)) := hGV _ hu v hv
  have hord : OrdGtV W P ((r + 1) * T) (y - s + v + (σ + s)) := by
    refine ordGtV_of_phOp_mem_vanish hP fun w hw κ' hκ' c c' => ?_
    rw [mem_zeros_iff_le_vanish] at hz
    exact hz (hLp (Ideal.mem_sup_right (Ideal.subset_span
      ⟨σ + s, add_mem_sigB hσ hs, w, hw, κ', hκ', c, c', rfl⟩)))
  rw [show y - s + v + (σ + s) = y + v + σ by abel] at hord
  -- 2. the two-parameter lemma, 3. the translation by `v`
  have h2 := ordGtV_phOp (κ := κ) (T := T) hP hord hw' (by rw [Nat.succ_mul]; omega) c₁ c₂
  exact ordGtV_lawSub (isHomV_phOp σ w' c₁ c₂ κ hP) h2 c 1

/-- **Normalised zeros of `A₂`**: `h + V ⊆ Z(L_r)`. -/
theorem Zs_subset_transl (α : Alpha B) (W : Submodule ℂ (Tan d₀ d₁ B))
    (S : Finset (GPt d₀ d₁ B)) {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hP : IsHomV P d) (T r : ℕ) (V : Set (GPt d₀ d₁ B)) :
    Zs (d₀ := d₀) (d₁ := d₁) α (IGexp d₀ d₁ B ⊔ Ideal.span {Q' | ∃ Q ∈ gensR2 W S P T r,
      ∃ v ∈ V, ∃ c, Q' = τ v c Q}) ⊆
      {h | gtransl h V ⊆ zeros (Lr2 W S P T r : Set _)} := by
  intro h hh
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨c, hc⟩ := exists_good h v
  obtain ⟨μ, hμ⟩ := eval_transl_good hc
  obtain ⟨lam₀, hn⟩ : ∃ lam₀, nrm α h = coords h lam₀ := ⟨_, rfl⟩
  have hgen : ∀ Q ∈ gensR2 W S P T r, Q ∈ vanish {h + v} := by
    intro Q hQ
    have h0 : eval (coords (h + v) fun k => lam₀ k ^ (B k).ld * μ k) Q = 0 := by
      rw [← hμ, ← hn]
      exact hh.2 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨Q, hQ, v, hv, c, rfl⟩))
    have hQh := isHomV_iff_wV.mp (isHomV_gensR2 hP Q hQ)
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [Set.mem_singleton_iff.mp hg]
    exact (eval_coords_eq_zero_iff hQh _ _ lam).mp h0
  change v + h ∈ zeros (Lr2 W S P T r : Set _)
  rw [add_comm, mem_zeros_iff_le_vanish]
  refine sup_le (fun Q hQ => mem_vanish.mpr fun g _ lam => mem_vanish.mp hQ g (Set.mem_univ _) lam)
    (Ideal.span_le.mpr fun Q hQ => hgen Q hQ)

end LSG.MEBV
