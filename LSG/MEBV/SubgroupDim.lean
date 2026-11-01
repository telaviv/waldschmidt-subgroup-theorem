/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupImm
import LSG.MEBV.MainAux
import LSG.MEBV.Chain
import LSG.ME.DimTrdeg

/-!
# Dimension of `H⁰` and finiteness of `H / H⁰` (M2.5 β′; template `LSG.MEB.SubgroupDim`)

All tangent-space computations happen at one smooth point `liftZ u' μ'` of the cone of `G̃`
(`exists_smooth_G`, α's `hdim_IGsem_le`), and every irreducible `Y ⊆ H` is translated through it.

* **`tz_le_lieAlg`**: the tangent-space bound at every point of every coset of `H⁰` (the field `tz`).
* **`hdim_le_of_subset`**, **`le_hdim_H0`**, **`hdim_H0`**: `hdim I(H⁰) = dim lieAlg H + m`.
* **`finite_cosets_H0`**: finitely many cosets of `H⁰` (representatives in `H`) cover `H`.
-/

open MvPolynomial Module Filter Topology Set
open StrongSix.M2 (hdata)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Order `> 1` from one lift -/

theorem ordGtV_span_of_dirD {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hP : IsHomV P d) (hPv : P ∈ vanish E) {u w : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ E)
    (h : dirD P u w = 0) : OrdGtV (ℂ ∙ w) P 1 (expG d₀ d₁ B u) := by
  refine ⟨u, rfl, fun w' hw' k hk => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw'
  interval_cases k
  · simp only [iteratedDeriv_zero, zero_smul, add_zero]
    exact eval_liftV_eq_zero_of_mem_vanish hPv hu
  · rw [iteratedDeriv_one]
    have e : (fun s : ℂ => eval (liftV (u + s • a • w)) P) =
        fun s => (fun r : ℂ => eval (liftV (u + r • w)) P) (a * s) := by
      funext s; rw [smul_smul, mul_comm]
    rw [e, deriv_comp_mul_left a (fun r : ℂ => eval (liftV (u + r • w)) P) 0, mul_zero]
    rw [dirD] at h
    rw [h, smul_zero]

variable {H : Set (GPt d₀ d₁ B)}

/-- **Lie directions from a coset point.** -/
theorem mem_lieAlg_of_coset (hH : IsSubgroupG H) (hc : IsZClosed H) {h : GPt d₀ d₁ B} {u w : Tan d₀ d₁ B}
    (hu : expG d₀ d₁ B u ∈ gtransl h H)
    (hd : ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomV P d → P ∈ vanish (gtransl h H) →
      dirD P u w = 0) : w ∈ lieAlg hH := by
  have hord : ∀ P ∈ homogVanish (gtransl h H), OrdGtV (ℂ ∙ w) P 1 (expG d₀ d₁ B u) := fun P hP => by
    obtain ⟨d, hdP⟩ := isHomV_of_mem_homogVanish hP
    exact ordGtV_span_of_dirD hdP hP.1 hu (hd P d hdP hP.1)
  have h1 := ordGtV_one_of_coset hord
  have hmem : expG d₀ d₁ B u + -h ∈ H := by
    rw [mem_gtransl] at hu; simpa [sub_eq_add_neg] using hu
  exact mem_lieAlg_of_ordGtV hH hc hmem h1

/-- **The tangent-space bound at every point of every coset of `H⁰`.** -/
theorem tz_le_lieAlg (hH : IsSubgroupG H) (hc : IsZClosed H) (g : GPt d₀ d₁ B) (u : Tan d₀ d₁ B)
    (hu : expG d₀ d₁ B u = g) (w : Tan d₀ d₁ B)
    (h : ∀ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (d : Fin m → ℕ), IsHomV P d →
      P ∈ vanish (gtransl g (H0 hH)) → deriv (fun r : ℂ => eval (liftV (u + r • w)) P) 0 = 0) :
    w ∈ lieAlg hH := by
  rw [← lieAlg_H0 hH hc]
  refine mem_lieAlg_of_coset (H0_isSubgroup hH) (isZClosed_H0 hH) (h := g) ?_ fun P d hP hPv => h P d hP hPv
  rw [hu, mem_gtransl, sub_self]
  exact (H0_isSubgroup hH).zero_mem

/-! ### A smooth point of the cone of `G̃` -/

theorem lc_ne_zero_blocks {ch : ∀ k, Fin (B k).nT} {a : Var d₀ d₁ B → ℂ} (hne : eval a (Lc ch) ≠ 0) (k : Fin m) :
    (fun c : Fin (B k).N => a (.e k (Sum.inl c))) ≠ 0 := fun h0 => by
  apply hne
  rw [Lc, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp only [Lk, map_pow, eval_X]
  have := congrFun h0 ((B k).fc (ch k))
  simp only [Pi.zero_apply] at this
  rw [this, zero_pow two_ne_zero]

/-- A point of the cone of `G̃` with nonzero scalings where `dim T(IGsem) ≤ dim G̃ + m`. -/
theorem exists_smooth_G : ∃ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ), (∀ k, μ k ≠ 0) ∧
    finrank ℂ (LSG.ME.tangentSpace (IGsem d₀ d₁ B) (liftZ u μ)) ≤ dimG d₀ d₁ B + m := by
  haveI := IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)
  obtain ⟨ch, -, hL⟩ := exists_chart_zero (d₀ := d₀) (d₁ := d₁) (B := B)
  have hh : Lc ch ∉ IGsem d₀ d₁ B := notMem_IGsem_of_eval_ne hL
  obtain ⟨a, ha, hne, hdim⟩ := LSG.ME.exists_smooth_point (IGsem d₀ d₁ B) (Lc ch) hh
  have hz : ∀ P ∈ IGexp d₀ d₁ B, eval a P = 0 := fun P hP => (mem_zeroLocus_iff.mp ha) P (IGexp_le_IGsem hP)
  obtain ⟨g, ν, rfl⟩ := exists_coordsZ_of_IGexp hz fun k _ => lc_ne_zero_blocks hne k
  have hν : ∀ k, ν k ≠ 0 := fun k h0 => lc_ne_zero_blocks hne k (funext fun c => by simp [coordsZ, h0])
  obtain ⟨lam₀, h0⟩ := coords_expG (liftG g)
  rw [expG_liftG] at h0
  set μ : Fin m → ℂ := fun k => ν k / lam₀ k
  have hμ : ∀ k, μ k ≠ 0 := fun k => div_ne_zero (hν k) (Units.ne_zero _)
  have he : liftZ (liftG g) μ = coordsZ g ν := by
    have := liftZ_eq_coordsZ (u := liftG g) (lam₀ := lam₀) (by rw [expG_liftG]; exact h0) μ
    rw [this, expG_liftG]
    congr 1; funext k; simp [μ, div_mul_cancel₀ _ (Units.ne_zero (lam₀ k))]
  refine ⟨liftG g, μ, hμ, ?_⟩
  rw [he, hdim, ← LSG.ME.hdim_eq_trdeg blk (fun _ => 1) (fun _ => le_rfl)]
  have := hdim_IGsem_le (d₀ := d₀) (d₁ := d₁) (B := B) (fun _ => 1) fun _ => le_rfl
  simpa [dimG] using this

theorem range_dLZl_le (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    LinearMap.range (dLZl u μ) ≤ LSG.ME.tangentSpace (IGsem d₀ d₁ B) (liftZ u μ) := by
  rintro _ ⟨⟨w, σ⟩, rfl⟩
  exact dLZ_mem_tangentSpace μ σ fun _ => Set.mem_univ _

theorem tangentSpace_IGsem_eq {u : Tan d₀ d₁ B} {μ : Fin m → ℂ} (hμ : ∀ k, μ k ≠ 0)
    (hT : finrank ℂ (LSG.ME.tangentSpace (IGsem d₀ d₁ B) (liftZ u μ)) ≤ dimG d₀ d₁ B + m) :
    LSG.ME.tangentSpace (IGsem d₀ d₁ B) (liftZ u μ) = LinearMap.range (dLZl u μ) := by
  refine (Submodule.eq_of_le_of_finrank_le (range_dLZl_le u μ) ?_).symm
  rw [LinearMap.finrank_range_of_inj (dLZl_injective hμ), Module.finrank_prod, finrank_Tan,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact hT

/-- **At a smooth point of the cone of `G̃`**, tangent vectors of the cone of a coset `h + H` come from
`lieAlg H`. -/
theorem tangent_coset_le_map (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ B} {μ : Fin m → ℂ}
    (hμ : ∀ k, μ k ≠ 0)
    (hT : finrank ℂ (LSG.ME.tangentSpace (IGsem d₀ d₁ B) (liftZ u μ)) ≤ dimG d₀ d₁ B + m)
    {h : GPt d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ gtransl h H) :
    LSG.ME.tangentSpace (vanish (gtransl h H)) (liftZ u μ) ≤
      (Submodule.prod (lieAlg hH) ⊤).map (dLZl u μ) := by
  intro v hv
  have hIG : IGsem d₀ d₁ B ≤ vanish (gtransl h H) := vanish_antitone (Set.subset_univ _)
  have hv' := LSG.MEB.tangentSpace_anti hIG _ hv
  rw [tangentSpace_IGsem_eq hμ hT] at hv'
  obtain ⟨⟨w, σ⟩, rfl⟩ := hv'
  refine ⟨(w, σ), ⟨?_, Submodule.mem_top⟩, rfl⟩
  have hs : dLZ u μ 0 σ ∈ LSG.ME.tangentSpace (vanish (gtransl h H)) (liftZ u μ) :=
    dLZ_mem_tangentSpace μ σ fun r => by simpa using hu
  have hw0 : dLZ u μ w 0 ∈ LSG.ME.tangentSpace (vanish (gtransl h H)) (liftZ u μ) := by
    have e : dLZ u μ w 0 = dLZl u μ (w, σ) - dLZl u μ (0, σ) := by
      rw [← map_sub]; simp [dLZl_apply]
    rw [e]
    exact Submodule.sub_mem _ hv hs
  exact mem_lieAlg_of_coset hH hc hu fun P d hP hPv => dirD_eq_zero_of_tangent hP hPv hμ hw0

theorem finrank_lieAlg_prod (hH : IsSubgroupG H) :
    finrank ℂ ↥(Submodule.prod (lieAlg hH) (⊤ : Submodule ℂ (Fin m → ℂ))) = finrank ℂ (lieAlg hH) + m := by
  rw [LSG.MEB.finrank_submodule_prod, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-! ### The upper bound -/

/-- **`hdim I(Y) ≤ dim lieAlg H + m`** for every irreducible nonempty `Y ⊆ H`. -/
theorem hdim_le_of_subset (hH : IsSubgroupG H) (hc : IsZClosed H) {Y : Set (GPt d₀ d₁ B)}
    (hY : (vanish Y).IsPrime) (hYH : Y ⊆ H) (hne : Y.Nonempty) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (hdata blk D ℂ (vanish Y)).1 ≤ finrank ℂ (lieAlg hH) + m := by
  obtain ⟨u, μ, hμ, hT⟩ := exists_smooth_G (d₀ := d₀) (d₁ := d₁) (B := B)
  obtain ⟨y₀, hy₀⟩ := hne
  set h := expG d₀ d₁ B u - y₀
  set Y' := gtransl h Y
  have hY' : (vanish Y').IsPrime := vanish_gtransl_isPrime hY h
  have huY : expG d₀ d₁ B u ∈ Y' := by rw [mem_gtransl]; simpa [h] using hy₀
  have huH : expG d₀ d₁ B u ∈ gtransl h H := gtransl_mono h hYH huY
  have ha : liftZ u μ ∈ zeroLocus ℂ (vanish Y') :=
    mem_zeroLocus_iff.mpr fun f hf => eval_liftZ_eq_zero_of_mem_vanish hf huY μ
  have h1 := LSG.ME.trdeg_le_finrank_tangentSpace (vanish Y') (liftZ u μ) ha
  rw [← LSG.ME.hdim_eq_trdeg blk D hD, hdim_vanish_gtransl D ⟨y₀, hy₀⟩ h] at h1
  refine h1.trans ?_
  have h2 : LSG.ME.tangentSpace (vanish Y') (liftZ u μ) ≤
      LSG.ME.tangentSpace (vanish (gtransl h H)) (liftZ u μ) :=
    LSG.MEB.tangentSpace_anti (vanish_antitone (gtransl_mono h hYH)) _
  refine (Submodule.finrank_mono (h2.trans (tangent_coset_le_map hH hc hμ hT huH))).trans ?_
  exact (Submodule.finrank_map_le _ _).trans (finrank_lieAlg_prod hH).le

/-! ### The lower bound for `H⁰` -/

theorem mem_of_coords_zero {E : Set (GPt d₀ d₁ B)} (hE : IsZClosed E) {g : GPt d₀ d₁ B} {ν : Fin m → ℂˣ}
    (h : ∀ P ∈ vanish E, eval (coords g ν) P = 0) : g ∈ E := by
  rw [← zeros_homogVanish hE]
  intro Q hQ lam
  obtain ⟨d, hd⟩ := hQ.2
  exact (eval_coords_eq_zero_iff hd g ν lam).mp (h Q hQ.1)

theorem le_hdim_H0 (hH : IsSubgroupG H) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    finrank ℂ (lieAlg hH) + m ≤ (hdata blk D ℂ (vanish (H0 hH))).1 := by
  haveI := vanish_H0_isPrime hH
  obtain ⟨ch, -, hL⟩ := exists_chart_zero (d₀ := d₀) (d₁ := d₁) (B := B)
  have h0 : expG d₀ d₁ B 0 ∈ H0 hH := by simpa using (H0_isSubgroup hH).zero_mem
  have hh : Lc ch ∉ vanish (H0 hH) := fun hm => hL (eval_liftV_eq_zero_of_mem_vanish hm h0)
  obtain ⟨b, hb, hne, hdim⟩ := LSG.ME.exists_smooth_point (vanish (H0 hH)) (Lc ch) hh
  have hz : ∀ P ∈ IGexp d₀ d₁ B, eval b P = 0 := fun P hP =>
    (mem_zeroLocus_iff.mp hb) P (vanish_antitone (Set.subset_univ _) (IGexp_le_IGsem hP))
  obtain ⟨g, ν, rfl⟩ := exists_coordsZ_of_IGexp hz fun k _ => lc_ne_zero_blocks hne k
  have hν : ∀ k, ν k ≠ 0 := fun k h0 => lc_ne_zero_blocks hne k (funext fun c => by simp [coordsZ, h0])
  have hg : g ∈ H0 hH := by
    refine mem_of_coords_zero (ν := fun k => Units.mk0 (ν k) (hν k)) (isZClosed_H0 hH) fun P hP => ?_
    rw [coords_eq_coordsZ]
    exact (mem_zeroLocus_iff.mp hb) P hP
  obtain ⟨lam₀, h0'⟩ := coords_expG (liftG g)
  set μ : Fin m → ℂ := fun k => ν k / lam₀ k
  have hμ : ∀ k, μ k ≠ 0 := fun k => div_ne_zero (hν k) (Units.ne_zero _)
  have he : liftZ (liftG g) μ = coordsZ g ν := by
    have := liftZ_eq_coordsZ (u := liftG g) (lam₀ := lam₀) h0' μ
    rw [this, expG_liftG]
    congr 1; funext k; simp [μ, div_mul_cancel₀ _ (Units.ne_zero (lam₀ k))]
  rw [LSG.ME.hdim_eq_trdeg blk D hD, ← hdim, ← he, ← finrank_lieAlg_prod hH]
  have hle : (Submodule.prod (lieAlg hH) ⊤).map (dLZl (liftG g) μ) ≤
      LSG.ME.tangentSpace (vanish (H0 hH)) (liftZ (liftG g) μ) := by
    rintro _ ⟨⟨w, σ⟩, ⟨hw, -⟩, rfl⟩
    refine dLZ_mem_tangentSpace μ σ fun r => ?_
    rw [map_add, expG_liftG]
    exact (H0_isSubgroup hH).add_mem _ hg _ (expG_mem_H0 hH (Submodule.smul_mem _ r hw))
  refine le_of_eq_of_le ?_ (Submodule.finrank_mono hle)
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (dLZl_injective hμ) _))

/-- **`hdim I(H⁰) = dim lieAlg H + m`.** -/
theorem hdim_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (hdata blk D ℂ (vanish (H0 hH))).1 = finrank ℂ (lieAlg hH) + m := by
  refine le_antisymm ?_ (le_hdim_H0 hH D hD)
  exact hdim_le_of_subset hH hc (vanish_H0_isPrime hH) (H0_subset hH hc)
    ⟨0, (H0_isSubgroup hH).zero_mem⟩ D hD

/-! ### Finitely many cosets -/

/-- A coset `g + H⁰` (`g ∈ H`) equals every irreducible Zariski-closed `Y ⊆ H` containing it. -/
theorem coset_eq_of_le (hH : IsSubgroupG H) (hc : IsZClosed H) {g : GPt d₀ d₁ B} (hg : g ∈ H)
    {Y : Set (GPt d₀ d₁ B)} (hYc : IsZClosed Y) (hY : (vanish Y).IsPrime) (hYH : Y ⊆ H)
    (hsub : gtransl g (H0 hH) ⊆ Y) : Y = gtransl g (H0 hH) := by
  set Y' := gtransl (-g) Y
  have hY'p : (vanish Y').IsPrime := vanish_gtransl_isPrime hY (-g)
  have hneg : gtransl (-g) H = H := gtransl_self_of_mem hH (hH.neg_mem _ hg)
  have hY'H : Y' ⊆ H := hneg ▸ gtransl_mono (-g) hYH
  have hH0Y' : H0 hH ⊆ Y' := by
    have := gtransl_mono (-g) hsub
    rwa [gtransl_gtransl, add_neg_cancel, gtransl_zero] at this
  have hle : vanish Y' ≤ vanish (H0 hH) := vanish_antitone hH0Y'
  have heq : vanish Y' = vanish (H0 hH) := by
    by_contra hne
    have hlt : vanish Y' < vanish (H0 hH) := lt_of_le_of_ne hle hne
    have h1 := StrongSix.M2.hdim_lt_of_lt blk (fun _ => 1) ℂ (fun _ => le_rfl)
      (vanish_H0_isPrime hH).ne_top hlt
    have h2 := hdim_le_of_subset hH hc hY'p hY'H ⟨0, hH0Y' (H0_isSubgroup hH).zero_mem⟩ (fun _ => 1)
      (fun _ => le_rfl)
    rw [hdim_H0 hH hc _ fun _ => le_rfl] at h1
    omega
  have hY'c : IsZClosed Y' := isZClosed_gtransl hYc (-g)
  have hY'eq : Y' = H0 hH := by
    rw [← zeros_vanish hY'c, ← zeros_vanish (isZClosed_H0 hH), heq]
  calc Y = gtransl g Y' := by rw [gtransl_gtransl, neg_add_cancel, gtransl_zero]
    _ = gtransl g (H0 hH) := by rw [hY'eq]

/-- **Finitely many cosets of `H⁰` cover `H`.** -/
theorem finite_cosets_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ∃ Rc : Finset (GPt d₀ d₁ B), (∀ c ∈ Rc, c ∈ H) ∧ H ⊆ ⋃ c ∈ Rc, gtransl c (H0 hH) := by
  classical
  obtain ⟨ps, hps, hcov⟩ := exists_components (H := H)
  let good : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) → Prop := fun p =>
    ∃ g ∈ H, zeros (p : Set _) = gtransl g (H0 hH)
  let rep : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) → GPt d₀ d₁ B := fun p =>
    if hp : good p then hp.choose else 0
  refine ⟨(ps.filter good).image rep, ?_, ?_⟩
  · intro c hc'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc'
    have hgp : good p := (Finset.mem_filter.mp hp).2
    simp only [rep, dif_pos hgp]
    exact hgp.choose_spec.1
  · intro g hg
    have hpr : (vanish (gtransl g (H0 hH))).IsPrime := vanish_gtransl_isPrime (vanish_H0_isPrime hH) g
    have hsubH : gtransl g (H0 hH) ⊆ H := by
      intro x hx
      rw [mem_gtransl] at hx
      simpa using hH.add_mem _ (H0_subset hH hc hx) _ hg
    obtain ⟨p, hp, hple⟩ := hcov _ hpr (vanish_antitone hsubH)
    obtain ⟨hpprime, hHp, hvz⟩ := hps p hp
    set Y := zeros (p : Set (MvPolynomial (Var d₀ d₁ B) ℂ))
    have hYc : IsZClosed Y := ⟨_, rfl⟩
    have hYH : Y ⊆ H := by
      rw [← zeros_vanish hc]; exact fun x hx P hP lam => hx P (hHp hP) lam
    have hsubY : gtransl g (H0 hH) ⊆ Y := by
      rw [← zeros_vanish (isZClosed_gtransl (isZClosed_H0 hH) g)]
      exact fun x hx P hP lam => hx P (hple hP) lam
    have hYeq := coset_eq_of_le hH hc hg hYc (by rw [hvz]; exact hpprime) hYH hsubY
    have hgood : good p := ⟨g, hg, hYeq⟩
    refine Set.mem_iUnion₂.mpr ⟨rep p, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hgood⟩, rfl⟩, ?_⟩
    have hrep : zeros (p : Set _) = gtransl (rep p) (H0 hH) := by
      simp only [rep, dif_pos hgood]; exact hgood.choose_spec.2
    rw [← hrep]
    exact hsubY (by rw [mem_gtransl, sub_self]; exact (H0_isSubgroup hH).zero_mem)

end LSG.MEBV
