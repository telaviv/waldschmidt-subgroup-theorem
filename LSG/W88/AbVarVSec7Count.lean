/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVSec7Rat
import LSG.W88.Sec7Aux
import LSG.W88.Sec7Count
import LSG.W88.AbVarPer
import LSG.AuxFun.AlgPoints

/-!
# M2.6.8d: counting, codimensions and the arithmetic data for the vector-extension §7

For `O : ObstrDataBV d₀ r d₁ B M` and `T′ = tanG O = pushTA(T̃′)`:

* `PerAV_le_PerAVf`, **`pushTA_perG`** (`pushTA` maps the periods `PerG` of `G̃_r` into `PerAVf`),
  **`perAVf_nsmul`** (`ω ∈ PerAVf ⇒ n • ω ∈ PerAV` for some `n > 0`: a common multiple of the `IsNsmulIn lat per`
  exponents), **`htilG_le_span`** (`exp⁻¹(grp) ∘ liftTA ⊆ span_ℚ (T′ + PerAV)`).
* `t0_leAV`, **`delta_eqAV`**, **`delta_posAV`** (a proper obstruction has codimension `≥ 1` in `G`).
* The grid `gridPtsAV y M = {exp(liftTA(Σ h_j y_j)) : h_j ≤ M}`, `mem_gridPtsAV`, `sig_gridPtsAV`.
* `exists_inequiv_grid_genAV` (a copy of `Sec7VCount.exists_inequiv_grid_gen`, which cannot be imported next to
  `AbVarVSec7Rat`: both files define `LSG.W88.tanG`).
* **`exists_LUDataAV`**: the arithmetic data of Lemma U (copy of `exists_LUDataA` plus the `sPart`, `w.s` and `M`
  entries).
-/

open Complex Finset Module NumberField LSG.Aux LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88.AVS

open LSG.W88.AVS

open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock ObstrDataBV PerG expG sigB)
open LSG.W88.Vec (AlgMat)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### Periods -/

theorem PerAV_le_PerAVf (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) :
    PerAV d₀ d₁ An M ≤ PerAVf d₀ d₁ B M :=
  fun _ hp => ⟨hp.1, hp.2.1, fun k => (An k).an.lat_le (hp.2.2.1 k), hp.2.2.2⟩

/-- **`pushTA` maps the periods of `G̃_r` into `PerAVf`.** -/
theorem pushTA_perG {p : LSG.MEBV.Tan (d₀ + r) d₁ B} (hp : p ∈ PerG (d₀ + r) d₁ B) :
    pushTA M p ∈ PerAVf d₀ d₁ B M := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨funext fun i => by simp [h1], h2, fun k => (h3 k).1, ?_⟩
  have hw : p.2.2.2 = etaB B p.2.2.1 := funext fun k => (h3 k).2
  funext i
  simp only [pushTA_apply, Pi.add_apply, h1, Pi.zero_apply, zero_add, hw]

/-- **A positive multiple of a full period is a counted period.** -/
theorem perAVf_nsmul (An : ∀ k, VBlockAn (B k)) {ω : TanAV d₀ d₁ r B} (hω : ω ∈ PerAVf d₀ d₁ B M) :
    ∃ n : ℕ, 0 < n ∧ n • ω ∈ PerAV d₀ d₁ An M := by
  obtain ⟨N, hN, hNk⟩ := exists_common_mult (fun k => ω.2.2.1 k ∈ (B k).base.per)
    (fun k N => N • ω.2.2.1 k ∈ (An k).an.lat)
    (fun k N M' h => by rw [mul_smul]; exact (An k).an.lat.nsmul_mem h M')
    (fun k hk => (An k).an.lat_nsmul _ hk) hω.2.2.1
  have hNω : N • ω ∈ PerAVf d₀ d₁ B M := (PerAVf d₀ d₁ B M).nsmul_mem hω N
  exact ⟨N, hN, hNω.1, hNω.2.1, fun k => hNk k, hNω.2.2.2⟩

/-- **`exp⁻¹(grp) ⊆ span_ℚ (T′ + PerAV)` on `G`.** -/
theorem htilG_le_span (O : ObstrDataBV d₀ r d₁ B M) (An : ∀ k, VBlockAn (B k)) {u : TanAV d₀ d₁ r B}
    (hu : expG (d₀ + r) d₁ B (liftTA u) ∈ O.grp) :
    u ∈ Submodule.span ℚ (((tanG O).toAddSubgroup ⊔ PerAV d₀ d₁ An M : AddSubgroup (TanAV d₀ d₁ r B)) :
      Set (TanAV d₀ d₁ r B)) := by
  obtain ⟨N, hN, hNu⟩ := O.htil _ hu
  obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hNu
  have hpush : N • u = pushTA M a + pushTA M b := by
    rw [← map_add, hab, map_nsmul, pushTA_liftTA]
  obtain ⟨n, hn, hnb⟩ := perAVf_nsmul An (pushTA_perG (M := M) hb)
  refine mem_span_rat_of_nsmul (N := n * N) (Nat.mul_pos hn hN) (Submodule.subset_span ?_)
  rw [mul_smul, hpush, smul_add]
  refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left ?_) (AddSubgroup.mem_sup_right hnb)
  exact (tanG O).toAddSubgroup.nsmul_mem (show pushTA M a ∈ tanG O from ⟨a, ha, rfl⟩) n

/-! ### Codimensions -/

theorem finrank_TanAV : finrank ℂ (TanAV d₀ d₁ r B) = d₀ + d₁ + ∑ k, (B k).g + r := by
  simp [Module.finrank_prod, Module.finrank_pi_fintype]
  ring

theorem t0_leAV (O : ObstrDataBV d₀ r d₁ B M) : O.t0 ≤ d₀ := by
  rw [t0_eq]; simpa using Submodule.finrank_le ((tanG O).map (LinearMap.fst ℂ (Fin d₀ → ℂ) _))

theorem sum_g_succ : ∑ k, ((B k).g + 1) = ∑ k, (B k).g + m := by
  rw [Finset.sum_add_distrib]; simp

/-- The codimension of the obstruction in `G`. -/
theorem delta_eqAV (O : ObstrDataBV d₀ r d₁ B M) :
    d₀ - O.t0 + finrank ℚ O.U + (∑ k, ((B k).g + 1) + r - O.t2) =
      d₀ + d₁ + ∑ k, (B k).g + r - finrank ℂ (tanG O) := by
  have h1 := finrank_tanG O
  have h2 := t2_eq O
  have h3 := t0_eq O
  have h4 := t2G_le O
  have h5 := t0_leAV O
  have h6 : finrank ℚ O.U ≤ d₁ := by simpa using Submodule.finrank_le O.U
  have h7 := sum_g_succ (B := B)
  rw [← h3] at h1
  omega

/-- **A proper obstruction has codimension `≥ 1` in `G`.** -/
theorem delta_posAV (O : ObstrDataBV d₀ r d₁ B M) (hO : O.Proper) :
    1 ≤ d₀ - O.t0 + finrank ℚ O.U + (∑ k, ((B k).g + 1) + r - O.t2) := by
  rw [delta_eqAV]
  by_contra hcon
  apply hO
  have hle : finrank ℂ (tanG O) ≤ d₀ + d₁ + ∑ k, (B k).g + r := by
    have := Submodule.finrank_le (tanG O)
    rw [finrank_TanAV] at this
    exact this
  have htop : tanG O = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [finrank_TanAV]; omega)
  change O.tan = ⊤
  rw [tan_eq_comap, htop, Submodule.comap_top]

/-! ### The grid -/

open scoped Classical in
/-- The grid points `exp(liftTA(Σ h_j y_j))`, `0 ≤ h_j ≤ M`. -/
def gridPtsAV {μ : ℕ} (y : Fin μ → TanAV d₀ d₁ r B) (N : ℕ) : Finset (LSG.MEBV.GPt (d₀ + r) d₁ B) :=
  Finset.univ.image fun h : Fin μ → Fin (N + 1) => expG (d₀ + r) d₁ B (liftTA (∑ j, (h j : ℕ) • y j))

theorem mem_gridPtsAV {μ : ℕ} {y : Fin μ → TanAV d₀ d₁ r B} {N : ℕ} {g : LSG.MEBV.GPt (d₀ + r) d₁ B} :
    g ∈ gridPtsAV y N ↔ ∃ h : Fin μ → ℕ, (∀ j, h j ≤ N) ∧ g = expG (d₀ + r) d₁ B (liftTA (∑ j, h j • y j)) := by
  classical
  unfold gridPtsAV
  constructor
  · intro hg
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨fun j => h j, fun j => Nat.lt_succ_iff.mp (h j).isLt, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact Finset.mem_image.mpr ⟨fun j => ⟨h j, Nat.lt_succ_of_le (hh j)⟩, Finset.mem_univ _, rfl⟩

theorem sig_gridPtsAV {μ : ℕ} {y : Fin μ → TanAV d₀ d₁ r B} {N n : ℕ} {σ : LSG.MEBV.GPt (d₀ + r) d₁ B}
    (hσ : σ ∈ sigB (gridPtsAV y N) n) :
    ∃ h : Fin μ → ℕ, (∀ j, h j ≤ n * N) ∧ σ = expG (d₀ + r) d₁ B (liftTA (∑ j, h j • y j)) := by
  obtain ⟨σs, hσs, rfl⟩ := hσ
  choose h hh hσh using fun i => mem_gridPtsAV.mp (hσs i)
  refine ⟨fun j => ∑ i, h i j, fun j => ?_, ?_⟩
  · calc ∑ i, h i j ≤ ∑ _i : Fin n, N := Finset.sum_le_sum fun i _ => hh i j
      _ = n * N := by simp
  · rw [Finset.sum_congr rfl fun i _ => hσh i, ← map_sum, ← map_sum, Finset.sum_comm]
    simp only [Finset.sum_smul]

/-! ### Pairwise inequivalent grid points (copy of `Sec7VCount.exists_inequiv_grid_gen`) -/

/-- **Pairwise inequivalent grid points.** -/
theorem exists_inequiv_grid_genAV {E G : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup G]
    (ex : E →+ G) (grp : Set G) (h0 : (0 : G) ∈ grp) (Z : AddSubgroup E)
    (hZ : ∀ u, ex u ∈ grp → u ∈ Submodule.span ℚ (Z : Set E)) {μ : ℕ} (y : Fin μ → E) (M : ℕ) :
    ∃ F : Finset G,
      (∀ g ∈ F, ∃ h : Fin μ → ℕ, (∀ j, h j ≤ M) ∧ g = ex (∑ j, h j • y j)) ∧
      (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ grp → g = g') ∧
      F.card = (M + 1) ^ (rk (AddSubgroup.closure (Set.range y)) -
        rk (AddSubgroup.closure (Set.range y) ⊓ Z)) := by
  classical
  set Q := Submodule.span ℚ (Z : Set E)
  have hrk : rk (AddSubgroup.closure (Set.range y)) - rk (AddSubgroup.closure (Set.range y) ⊓ Z) =
      finrank ℚ (Submodule.span ℚ (Set.range y)) -
        finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ Q) := by
    unfold rk
    rw [span_inf_eq, span_closure_range]
  obtain ⟨idx, hidx⟩ := exists_indep_mod y Q
  generalize hℓ : finrank ℚ (Submodule.span ℚ (Set.range y)) -
    finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ Q) = ℓ at idx hidx hrk
  set pt : (Fin ℓ → Fin (M + 1)) → G := fun a => ex (∑ k, (a k : ℕ) • y (idx k)) with hpt
  have hinj : ∀ a b, pt a - pt b ∈ grp → a = b := by
    intro a b hab
    have e : ex ((∑ k, (a k : ℕ) • y (idx k)) - ∑ k, (b k : ℕ) • y (idx k)) = pt a - pt b :=
      ex.map_sub _ _
    have hQ := hZ _ (by rw [e]; exact hab)
    have e2 : (∑ k, (a k : ℕ) • y (idx k)) - ∑ k, (b k : ℕ) • y (idx k) =
        ∑ k, (((a k : ℕ) : ℚ) - ((b k : ℕ) : ℚ)) • y (idx k) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e2] at hQ
    have hc := hidx (fun k => ((a k : ℕ) : ℚ) - ((b k : ℕ) : ℚ)) hQ
    funext k
    have := congrFun hc k
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact Fin.ext (by exact_mod_cast this)
  have hinj' : Function.Injective pt := fun a b h => hinj a b (by rw [h, sub_self]; exact h0)
  have hidxinj : Function.Injective idx := by
    intro k k' hkk
    by_contra hne
    have := hidx (Pi.single k 1 - Pi.single k' 1) (by
      have e : ∑ j, (Pi.single k (1 : ℚ) - Pi.single k' 1 : Fin ℓ → ℚ) j • y (idx j) =
          y (idx k) - y (idx k') := by
        simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]
      rw [e, hkk, sub_self]; exact Q.zero_mem)
    have h1 := congrFun this k
    simp [hne] at h1
  refine ⟨Finset.univ.image pt, ?_, ?_, ?_⟩
  · rintro g hg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨fun j => ∑ k, if idx k = j then (a k : ℕ) else 0, fun j => ?_, ?_⟩
    · by_cases h : ∃ k, idx k = j
      · obtain ⟨k₀, rfl⟩ := h
        change (∑ k, if idx k = idx k₀ then (a k : ℕ) else 0) ≤ M
        rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp [hidxinj.ne hk]) (by simp)]
        simp only [↓reduceIte]
        exact Nat.lt_succ_iff.mp (a k₀).isLt
      · push Not at h
        simp [h]
    · simp only [pt]
      congr 1
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp
  · intro g hg g' hg' hgg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hg'
    rw [hinj a b hgg]
  · rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, hrk]

/-! ### The arithmetic data of Lemma U -/

/-- **Construction of the data of Lemma U.** -/
theorem exists_LUDataAV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) (hMa : AlgMat M)
    (W : Submodule ℂ (TanAV d₀ d₁ r B)) (hW : RationalOverQbarAV W) {μ : ℕ} (y : Fin μ → TanAV d₀ d₁ r B)
    (hyL : ∀ j, y j ∈ LamAV d₀ d₁ An M) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ι : K →+* ℂ) (τ : ℕ) (Dt : LUDataAV ι An M μ τ),
      Dt.y = y ∧ Submodule.span ℂ (Set.range Dt.w) = W := by
  classical
  -- a basis of `W` with algebraic coordinates
  set St : Set (TanAV d₀ d₁ r B) := {w | w ∈ W ∧ AlgTanAV w}
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ St
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨bF, hbF⟩ := hbfin.exists_finset_coe
  set τ := bF.card
  let w : Fin τ → TanAV d₀ d₁ r B := fun q => (bF.equivFin.symm q : TanAV d₀ d₁ r B)
  have hwb : ∀ q, w q ∈ b := fun q => by rw [← hbF]; exact (bF.equivFin.symm q).2
  have hrange : Set.range w = b := by
    ext x; constructor
    · rintro ⟨q, rfl⟩; exact hwb q
    · intro hx
      have hx' : x ∈ bF := by rw [← hbF] at hx; exact hx
      exact ⟨bF.equivFin ⟨x, hx'⟩, by simp [w]⟩
  have hspan : Submodule.span ℂ (Set.range w) = W := by
    rw [hrange, hbspan]; exact hW.symm
  have hwS : ∀ q, w q ∈ St := fun q => hbS (hwb q)
  -- the finite set of algebraic numbers
  let val : ((Fin μ × Fin d₀) ⊕ (Fin μ × Fin d₁) ⊕ (Fin μ × Fin r) ⊕ (Fin τ × Fin d₀) ⊕ (Fin τ × Fin d₁) ⊕
      (Fin τ × Σ k, Fin (B k).g) ⊕ (Fin τ × Fin r) ⊕ (Fin r × Fin m)) → ℂ := fun a =>
    match a with
    | .inl ji => (y ji.1).1 ji.2
    | .inr (.inl ji) => exp ((y ji.1).2.1 ji.2)
    | .inr (.inr (.inl ji)) => sPart M (y ji.1) ji.2
    | .inr (.inr (.inr (.inl ri))) => (w ri.1).1 ri.2
    | .inr (.inr (.inr (.inr (.inl ri)))) => (w ri.1).2.1 ri.2
    | .inr (.inr (.inr (.inr (.inr (.inl rki))))) => (w rki.1).2.2.1 rki.2.1 rki.2.2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl ri)))))) => (w ri.1).2.2.2 ri.2
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr ij)))))) => M ij.1 ij.2
  let Fs : Finset ℂ := univ.image val
  have hval : ∀ a, val a ∈ Fs := fun a => mem_image_of_mem _ (mem_univ a)
  have halg : ∀ x ∈ Fs, IsAlgebraic ℚ x := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    rcases a with ji | ji | ji | ri | ri | rki | ri | ij
    · exact (hyL ji.1).1 ji.2
    · exact (hyL ji.1).2.1 ji.2
    · exact (hyL ji.1).2.2.2 ji.2
    · exact (hwS ri.1).2.1 ri.2
    · exact (hwS ri.1).2.2.1 ri.2
    · exact (hwS rki.1).2.2.2.1 rki.2.1 rki.2.2
    · exact (hwS ri.1).2.2.2.2 ri.2
    · exact hMa ij.1 ij.2
  -- the number field
  let F := IntermediateField.adjoin ℚ (Fs : Set ℂ)
  haveI : FiniteDimensional ℚ F :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  haveI : NumberField F := ⟨⟩
  let ι : F →+* ℂ := F.val.toRingHom
  have hmem : ∀ x ∈ Fs, x ∈ F := fun x hx => IntermediateField.subset_adjoin ℚ _ hx
  -- sizes
  choose dn hdn1 hdni using fun x : Fs => exists_den (⟨x.1, hmem x.1 x.2⟩ : F)
  set H : ℝ := 1 + ∑ x : Fs, house (⟨x.1, hmem x.1 x.2⟩ : F)
  set d : ℕ := ∏ x : Fs, dn x
  have hH : 1 ≤ H := by
    have := sum_nonneg fun x (_ : x ∈ (univ : Finset Fs)) => house_nonneg (⟨x.1, hmem x.1 x.2⟩ : F)
    simp only [H]; linarith
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun x _ => by
    have := hdn1 x; omega)
  have hsz : ∀ x ∈ Fs, Sz ι H d x := by
    intro x hx
    refine ⟨⟨x, hmem x hx⟩, rfl, ?_, ?_⟩
    · have := single_le_sum (f := fun x : Fs => house (⟨x.1, hmem x.1 x.2⟩ : F))
        (fun x _ => house_nonneg _) (mem_univ ⟨x, hx⟩)
      simp only [H]; linarith
    · have hdv : dn ⟨x, hx⟩ ∣ d := dvd_prod_of_mem _ (mem_univ _)
      obtain ⟨e, he⟩ := hdv
      have : ((d : ℕ) : F) * ⟨x, hmem x hx⟩ = (e : F) * ((dn ⟨x, hx⟩ : F) * ⟨x, hmem x hx⟩) := by
        rw [he]; push_cast; ring
      rw [this]
      have he' : IsIntegral ℤ (e : F) := by
        simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := (e : ℤ))
      exact he'.mul (hdni _)
  refine ⟨F, inferInstance, inferInstance, ι, τ,
    { y := y, w := w, H := H, d := d, hH := hH, hd := hd,
      ha := fun j i => hsz _ (hval (.inl (j, i))),
      hb := fun j i => hsz _ (hval (.inr (.inl (j, i)))),
      hlat := fun j k => (hyL j).2.2.1 k,
      hs := fun j i => hsz _ (hval (.inr (.inr (.inl (j, i))))),
      hw0 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inl (q, i)))))),
      hw1 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inr (.inl (q, i))))))),
      hw2 := fun q k i => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inl (q, ⟨k, i⟩)))))))),
      hw3 := fun q i => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inl (q, i))))))))),
      hM := fun i j => hsz _ (hval (.inr (.inr (.inr (.inr (.inr (.inr (.inr (i, j))))))))) },
    rfl, hspan⟩

end LSG.W88.AVS
