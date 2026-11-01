/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.WustB
import LSG.MEBV.WustAlgB
import LSG.MEBV.MainGrp

/-!
# Wüstholz transversal data on unions of cosets of `H⁰` (M2.5, β; port of `LSG.MEB.WustCosetB`)

From the tangent-space bound `TZPropV O`, the transversal data `WustData` on `E = ⋃_{a ∈ R} (a + H⁰)` (distinct
cosets, `ℓ_k ∉ I(a + H⁰)`) is built coset by coset, as in MEB. The vector-block changes:
* charts are **fibre indices** `ch k : Fin (B k).nT` whose base chart `fc (ch k)` is a chart of the base and is nonzero
  at the pairing point (`chart_cover` + `fc_charts`);
* the derivations `Dh ch w` are the `X_c² ∂` derivations of `LSG.MEBV.Deriv`; `eval_Dh_liftV` has the same shape as
  MEB's (`Lc · ∂_w − (Euler term) · P`), so the left kernel of the pairing is still in `T_{H⁰}`;
* `WustData.cE = 2` (`Eul_Dh`).

* `coset_data`, `exists_seps`, `exists_wustData`; **`wust_of_tz : TZPropV O → WustPropV O`** and
  **`wustInput : WustInput d₀ d₁ B`** (α's `Main`/`MainPush` input).
-/

open MvPolynomial Module
open StrongSix.M2 (hfun)

namespace LSG.MEBV

open LSG.MEB (Blk exists_biorth)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- Determinants of matrices with entries of one multidegree `e`. -/
theorem isWH_det {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Var d₀ d₁ B) ℂ))
    {e : Fin m → ℕ} (h : ∀ i j, IsWeightedHomogeneous wV (A i j) e) :
    IsWeightedHomogeneous wV A.det (n • e) := by
  rw [← mem_weightedHomogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule]
  have := IsWeightedHomogeneous.prod Finset.univ (fun i => A (σ i) i) (fun _ => e)
    (fun i _ => h _ _)
  simpa using this

theorem eval_lpow_ne {α : Alpha B} {g : GPt d₀ d₁ B} (hg : ∀ k, lval α g k ≠ 0) (c : Fin m → ℕ) :
    eval (coords g 1) (lpow (d₀ := d₀) (d₁ := d₁) α c) ≠ 0 := by
  rw [lpow, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  rw [map_pow, eval_coords_lsl]
  simpa using pow_ne_zero _ (hg k)

/-- Rescaling transversal data by a multiplier `L ∉ I(C)` keeps the relations. -/
theorem rescale_rel {C : Set (GPt d₀ d₁ B)} (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ)
    (MvPolynomial (Var d₀ d₁ B) ℂ)) {T N L : MvPolynomial (Var d₀ d₁ B) ℂ} (hT : T ∈ vanish C)
    (b : Prop) [Decidable b] (h : D T - (if b then N else 0) ∈ vanish C) :
    D (L * T) - (if b then L * N else 0) ∈ vanish C := by
  have e : D (L * T) - (if b then L * N else 0) = L * (D T - (if b then N else 0)) + T * D L := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    split_ifs <;> ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hT)

/-- **Transversal data on one coset.** -/
theorem coset_data {O : ObstrDataGV d₀ d₁ B} (htz : TZPropV O) (W : Submodule ℂ (Tan d₀ d₁ B))
    (α : Alpha B) (a : GPt d₀ d₁ B) (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a O.grp)) :
    ∃ (ch : ∀ k, Fin (B k).nT) (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) → Tan d₀ d₁ B)
      (T : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) → MvPolynomial (Var d₀ d₁ B) ℂ)
      (N : MvPolynomial (Var d₀ d₁ B) ℂ) (dN : Fin m → ℕ),
      (∀ k, (B k).fc (ch k) ∈ (B k).base.charts) ∧ (∀ i, w i ∈ W) ∧ (∀ j, T j ∈ vanish (gtransl a O.grp)) ∧
      N ∉ vanish (gtransl a O.grp) ∧ IsWeightedHomogeneous wV N dN ∧
      ∀ i j, Dh ch (w i) (T j) - (if i = j then N else 0) ∈ vanish (gtransl a O.grp) := by
  classical
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)
  set V := O.grp
  set Cs := gtransl a V
  have hpC : (vanish Cs).IsPrime := vanish_gtransl_isPrime (vanish_grp_isPrime O) a
  obtain ⟨g, hgC, hg⟩ := point_of_lsl_notMem hpC hℓ
  have hCg : gtransl g V = Cs := gtransl_eq_of_sub_mem O.grp_sub (mem_gtransl.mp hgC)
  set u := liftG g
  have hu : expG d₀ d₁ B u = g := expG_liftG g
  have hlift : liftV u = coords g 1 := (coords_one_eq_liftV g).symm
  have hvan : ∀ P ∈ vanish Cs, eval (liftV u) P = 0 := fun P hP => by
    rw [hlift]; exact mem_vanish.mp hP g hgC 1
  -- a chart nonzero at `g`
  have hch : ∀ k, ∃ t, (B k).fc t ∈ (B k).base.charts ∧
      (B k).base.θ (u.2.2.1 k) ((B k).fc t) ≠ 0 := fun k => by
    obtain ⟨c, hc, hne⟩ := (B k).base.chart_cover _ ((B k).base.θ_ne _) ((B k).base.θ_model _)
    obtain ⟨t, rfl⟩ := (B k).fc_charts c hc
    exact ⟨t, hc, hne⟩
  choose ch hchc hchne using hch
  have hLc : eval (liftV u) (Lc ch) ≠ 0 := by
    rw [Lc, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by rw [eval_Lk_liftV]; exact pow_ne_zero _ (hchne k)
  -- the pairing and its left kernel
  let ι := {P : MvPolynomial (Var d₀ d₁ B) ℂ // (∃ d, IsHomV P d) ∧ P ∈ vanish Cs}
  let φ : ι → Tan d₀ d₁ B →ₗ[ℂ] ℂ := fun P => pairL ch (liftV u) P.1
  have hK : ∀ w ∈ W, (∀ i, φ i w = 0) → w ∈ O.tan := by
    intro w _ hw
    refine htz g u hu w fun P d hP hPg => ?_
    rw [hCg] at hPg
    have h0 : eval (liftV u) (Dh ch w P) = 0 := hw ⟨P, ⟨d, hP⟩, hPg⟩
    rw [eval_Dh_liftV ch hchc hP u w, hvan P hPg, mul_zero, sub_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hLc
  obtain ⟨w, ind, hwW, hδ⟩ := exists_biorth φ W O.tan hK ℓ le_rfl
  -- one multidegree
  choose dP hdP using fun j => (ind j).2.1
  set dT : Fin m → ℕ := ∑ j, dP j
  have hle : ∀ j, dP j ≤ dT := fun j =>
    Finset.single_le_sum (f := fun j => dP j) (fun _ _ => zero_le) (Finset.mem_univ j)
  set c : Fin ℓ → ℂ := fun j => eval (liftV u) (lpow (d₀ := d₀) (d₁ := d₁) α (dT - dP j))
  have hc : ∀ j, c j ≠ 0 := fun j => by
    simp only [c, hlift]; exact eval_lpow_ne hg _
  set T1 : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ := fun j =>
    C (c j)⁻¹ * (lpow α (dT - dP j) * (ind j).1)
  have hT1C : ∀ j, T1 j ∈ vanish Cs := fun j =>
    Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (ind j).2.2)
  have hT1h : ∀ j, IsHomV (T1 j) dT := fun j => by
    rw [isHomV_iff_wV]
    have := (isWH_lpow (d₀ := d₀) (d₁ := d₁) α (dT - dP j)).mul (isHomV_iff_wV.mp (hdP j))
    rw [tsub_add_cancel_of_le (hle j)] at this
    simpa using this.C_mul (c j)⁻¹
  have hT1 : ∀ i j, eval (liftV u) (Dh ch (w i) (T1 j)) = if i = j then 1 else 0 := by
    intro i j
    have h1 : Dh ch (w i) (T1 j) = C (c j)⁻¹ * (lpow α (dT - dP j) * Dh ch (w i) (ind j).1 +
        (ind j).1 * Dh ch (w i) (lpow α (dT - dP j))) := by
      rw [show T1 j = C (c j)⁻¹ * (lpow α (dT - dP j) * (ind j).1) from rfl, Dh_C_mul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm]
    rw [h1, map_mul, map_add, map_mul, map_mul, eval_C, hvan _ (ind j).2.2, zero_mul, add_zero]
    have h2 : eval (liftV u) (Dh ch (w i) (ind j).1) = if i = j then 1 else 0 := hδ i j
    rw [h2, show eval (liftV u) (lpow α (dT - dP j)) = c j from rfl]
    split_ifs <;> field_simp [hc j]
  -- determinant and adjugate
  set A : Matrix (Fin ℓ) (Fin ℓ) (MvPolynomial (Var d₀ d₁ B) ℂ) := fun i j => Dh ch (w i) (T1 j)
  set T : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ := fun j => ∑ k, T1 k * A.adjugate k j
  refine ⟨ch, w, T, A.det, ℓ • (fun k => dT k + 2), hchc, hwW, fun j => ?_, fun hN => ?_, ?_, fun i j => ?_⟩
  · exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hT1C k)
  · have hev : eval (liftV u) A.det = 1 := by
      rw [RingHom.map_det]
      have : (eval (liftV u)).mapMatrix A = 1 := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
        exact hT1 i j
      rw [this, Matrix.det_one]
    have := hvan _ hN
    rw [hev] at this
    exact one_ne_zero this
  · exact isWH_det A fun i j => isHomV_iff_wV.mp (isHomV_Dh ch (w i) (hT1h j))
  · have e : Dh ch (w i) (T j) - (if i = j then A.det else 0) =
        ∑ k, T1 k * Dh ch (w i) (A.adjugate k j) := by
      have hmul : ∑ k, A i k * A.adjugate k j = if i = j then A.det else 0 := by
        have := congrFun (congrFun (Matrix.mul_adjugate A) i) j
        rw [Matrix.mul_apply] at this
        rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        split_ifs <;> simp
      simp only [T, map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
      rw [← hmul, add_sub_assoc, ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl (fun x _ => show A.adjugate x j * Dh ch (w i) (T1 x) -
        A i x * A.adjugate x j = 0 by simp only [A]; ring), Finset.sum_const_zero, add_zero]
    rw [e]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hT1C k)

/-- **Multihomogeneous separators** of one multidegree for distinct cosets. -/
theorem exists_seps {V : Set (GPt d₀ d₁ B)} (hVs : IsSubgroupG V) (hVc : IsZClosed V)
    (hp : (vanish V).IsPrime) (α : Alpha B) (R : Finset (GPt d₀ d₁ B))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ V)
    (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V)) :
    ∃ (Bs : GPt d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ) (EB : Fin m → ℕ), ∀ a ∈ R,
      IsWeightedHomogeneous wV (Bs a) EB ∧ Bs a ∉ vanish (gtransl a V) ∧
      ∀ b ∈ R, a ≠ b → Bs a ∈ vanish (gtransl b V) := by
  classical
  have hsep : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∃ Q : MvPolynomial (Var d₀ d₁ B) ℂ,
      (∃ d, IsWeightedHomogeneous wV Q d) ∧ Q ∈ vanish (gtransl b V) ∧ Q ∉ vanish (gtransl a V) := by
    intro a ha b hb hab
    have hab' : a ∉ gtransl b V := fun h => hdist a ha b hb hab (mem_gtransl.mp h)
    obtain ⟨Q, ⟨hQb, d, hd⟩, hQa⟩ := exists_homogVanish_ne (isZClosed_gtransl hVc b) hab'
    refine ⟨Q, ⟨d, hd⟩, hQb, fun h => hQa 1 (mem_vanish.mp h a ⟨0, hVs.zero_mem, zero_add a⟩ 1)⟩
  choose! Q hQh hQb hQa using hsep
  choose! dQ hdQ using hQh
  set B0 : GPt d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ := fun a => ∏ b ∈ R.erase a, Q a b
  set e : GPt d₀ d₁ B → Fin m → ℕ := fun a => ∑ b ∈ R.erase a, dQ a b
  set EB : Fin m → ℕ := ∑ a ∈ R, e a
  refine ⟨fun a => lpow α (EB - e a) * B0 a, EB, fun a ha => ⟨?_, fun h => ?_, fun b hb hab => ?_⟩⟩
  · have h1 : IsWeightedHomogeneous wV (B0 a) (e a) :=
      IsWeightedHomogeneous.prod _ _ _ fun b hb =>
        hdQ a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
    have h2 := (isWH_lpow (d₀ := d₀) (d₁ := d₁) α (EB - e a)).mul h1
    rwa [tsub_add_cancel_of_le (Finset.single_le_sum (f := e) (fun _ _ => zero_le) ha)] at h2
  · have hpa := vanish_gtransl_isPrime hp a
    rcases hpa.mem_or_mem h with h1 | h1
    · exact lpow_notMem hpa α (hℓ a ha) _ h1
    · obtain ⟨b, hb, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpa)).mp h1
      exact hQa a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm hQ
  · refine Ideal.mul_mem_left _ _ ?_
    have hbm : b ∈ R.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    rw [show B0 a = Q a b * ∏ x ∈ (R.erase a).erase b, Q a x from
      (Finset.mul_prod_erase _ _ hbm).symm]
    exact Ideal.mul_mem_right _ _ (hQb a ha b hb hab)

/-- **Transversal data on finite unions of distinct cosets of `H⁰`**, from `TZProp`. -/
theorem exists_wustData {O : ObstrDataGV d₀ d₁ B} (htz : TZPropV O)
    (W : Submodule ℂ (Tan d₀ d₁ B)) (R : Finset (GPt d₀ d₁ B))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ O.grp) (α : Alpha B)
    (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a O.grp)) :
    ∃ WD : WustData d₀ d₁ B W (⋃ a ∈ R, gtransl a O.grp)
        (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)),
      ∀ a ∈ R, WD.M ∉ vanish (gtransl a O.grp) := by
  classical
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)
  set V := O.grp
  have hp : (vanish V).IsPrime := vanish_grp_isPrime O
  have hpC : ∀ a, (vanish (gtransl a V)).IsPrime := fun a => vanish_gtransl_isPrime hp a
  have hcd : ∀ a, ∃ (ch : ∀ k, Fin (B k).nT) (w : Fin ℓ → Tan d₀ d₁ B)
      (T : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ) (N : MvPolynomial (Var d₀ d₁ B) ℂ)
      (dN : Fin m → ℕ), a ∈ R → ((∀ k, (B k).fc (ch k) ∈ (B k).base.charts) ∧ (∀ i, w i ∈ W) ∧
      (∀ j, T j ∈ vanish (gtransl a O.grp)) ∧ N ∉ vanish (gtransl a O.grp) ∧
      IsWeightedHomogeneous wV N dN ∧
      ∀ i j, Dh ch (w i) (T j) - (if i = j then N else 0) ∈ vanish (gtransl a O.grp)) := by
    intro a
    by_cases ha : a ∈ R
    · obtain ⟨ch, w, T, N, dN, h⟩ := coset_data htz W α a (hℓ a ha)
      exact ⟨ch, w, T, N, dN, fun _ => h⟩
    · exact ⟨fun k => (B k).t₀, 0, 0, 0, 0, fun h => absurd h ha⟩
  choose ch w T0 N0 dN hprop using hcd
  have hch : ∀ a ∈ R, ∀ k, (B k).fc (ch a k) ∈ (B k).base.charts := fun a ha => (hprop a ha).1
  have hwW : ∀ a ∈ R, ∀ i, w a i ∈ W := fun a ha => (hprop a ha).2.1
  have hT0 : ∀ a ∈ R, ∀ j, T0 a j ∈ vanish (gtransl a V) := fun a ha => (hprop a ha).2.2.1
  have hN0 : ∀ a ∈ R, N0 a ∉ vanish (gtransl a V) := fun a ha => (hprop a ha).2.2.2.1
  have hN0h : ∀ a ∈ R, IsWeightedHomogeneous wV (N0 a) (dN a) := fun a ha =>
    (hprop a ha).2.2.2.2.1
  have hδ0 : ∀ a ∈ R, ∀ i j, Dh (ch a) (w a i) (T0 a j) - (if i = j then N0 a else 0) ∈
      vanish (gtransl a V) := fun a ha => (hprop a ha).2.2.2.2.2
  obtain ⟨Bs, EB, hBs⟩ := exists_seps O.grp_sub O.grp_closed hp α R hdist hℓ
  set EN : Fin m → ℕ := ∑ a ∈ R, dN a
  have hleN : ∀ a ∈ R, dN a ≤ EN := fun a ha =>
    Finset.single_le_sum (f := dN) (fun _ _ => zero_le) ha
  set L : GPt d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ := fun a => lpow α (EN - dN a)
  set T : GPt d₀ d₁ B → Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ := fun a j => L a * T0 a j
  set N : GPt d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ := fun a => L a * N0 a
  set Dk : GPt d₀ d₁ B → Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ)
    (MvPolynomial (Var d₀ d₁ B) ℂ) := fun a i => Dh (ch a) (w a i)
  have hT : ∀ a ∈ R, ∀ j, T a j ∈ vanish (gtransl a V) := fun a ha j =>
    Ideal.mul_mem_left _ _ (hT0 a ha j)
  have hTδ : ∀ a ∈ R, ∀ i j, Dk a i (T a j) - (if i = j then N a else 0) ∈ vanish (gtransl a V) :=
    fun a ha i j => rescale_rel (Dk a i) (hT0 a ha j) (i = j) (hδ0 a ha i j)
  have hN : ∀ a ∈ R, N a ∉ vanish (gtransl a V) := fun a ha h =>
    ((hpC a).mem_or_mem h).elim (lpow_notMem (hpC a) α (hℓ a ha) _) (hN0 a ha)
  have hNh : ∀ a ∈ R, IsWeightedHomogeneous wV (N a) EN := fun a ha => by
    have := (isWH_lpow (d₀ := d₀) (d₁ := d₁) α (EN - dN a)).mul (hN0h a ha)
    rwa [tsub_add_cancel_of_le (hleN a ha)] at this
  have hglue := fun a' (ha' : a' ∈ R) => LSG.ME.glue (K := ℂ) R (fun a => vanish (gtransl a V))
    (fun a _ => hpC a) Dk T N Bs hT hTδ hN (fun a ha => (hBs a ha).2.1)
    (fun a ha b hb hab => (hBs a ha).2.2 b hb hab) a' ha'
  set Dv : Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
    fun i => ∑ a ∈ R, Bs a • Dk a i
  set Q : Fin ℓ → MvPolynomial (Var d₀ d₁ B) ℂ := fun j => ∑ a ∈ R, Bs a ^ 2 * T a j
  set M : MvPolynomial (Var d₀ d₁ B) ℂ := ∑ a ∈ R, Bs a ^ 3 * N a
  refine ⟨{ ι' := (∀ k, Fin (B k).nT) × Tan d₀ d₁ B
            Dw := Dmix
            Ws := Wmix W
            Dv := Dv
            Q := Q
            M := M
            μ := 3 • EB + EN
            hQ := fun j => (mem_vanish_biUnion R _).mpr fun a' ha' => (hglue a' ha').1 j
            hδ := fun i j => (mem_vanish_biUnion R _).mpr fun a' ha' => (hglue a' ha').2.1 i j
            hMh := IsWeightedHomogeneous.sum _ _ _ fun a ha =>
              (((hBs a ha).1.pow 3).mul (hNh a ha))
            cE := 2
            hcomm := fun k p x => Eul_Dh k p.1 p.2 x
            hDv := fun i n x hx => LSG.ME.glued_mem_VOg R Bs (fun a => (ch a, w a i))
              (fun a ha => show (ch a, w a i) ∈ Wmix W from ⟨hch a ha, hwW a ha i⟩) hx
            bridge := fun S0 A hA => hA.trans (homOrd_le_VOg W S0 _) }, fun a' ha' => ?_⟩
  exact (hglue a' ha').2.2

/-- **The sliced Wüstholz lemma from the tangent-space bound** (α's request, M2.md α → β/β′ (2)). -/
theorem wust_of_tz {O : ObstrDataGV d₀ d₁ B} (htz : TZPropV O) : WustPropV O :=
  wust_field_of_data (vanish_grp_isPrime O) fun W R hdist α hℓ =>
    exists_wustData htz W R hdist α hℓ

/-- **The Wüstholz input** of α's `Main`, for every family. -/
theorem wustInput : WustInput d₀ d₁ B := fun _ htz => wust_of_tz htz

end LSG.MEBV
