/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupDim
import LSG.MEB.SubgroupRat

/-!
# `π_base(lieAlg H)` is rational, and the base-group comparison (M2.5 β′)

Port of MEV's `isAbelianTangent_map_piZ` (transcendence-degree count) to vector-extension blocks, with the
comparison group taken in **MEB's** product of the bases `G_b = G_a^{d₀} × G_m^{d₁} × ∏ A_k` (`baseB B`).

For a Zariski-closed subgroup `H ⊆ G̃` with `T = lieAlg H` and `P = π_base(T)`:
* `B' = zcl_{G_b} (exp_{G_b} (0 × 0 × P))`, with `0 × 0 × P ⊆ lieAlg B'`; a transcendence basis of coordinates on
  `B'⁰` consists of base cone coordinates `e k c` only.
* `K₀ = T ∩ ker π_base` projects onto `dim K₀` of the coordinates `x_i`, `b_j`, `w_k`; the functions `X_i`, `Y_j`,
  `T_{k,t₀}` (affine in `w_k` where `θ_{i₀} ≠ 0`) together with the base coordinates are algebraically independent
  modulo `I(H⁰)` (MEB's prime `I(exp (0 × 0 × P))` replaces MEV's density argument).
* Hence **`lieAlg_zclB_eq`**: `lieAlg B' = 0 × 0 × P`, and **`isRatSub_map_piB`**: `IsRatSub (perBase B) P`
  (MEB's `isRatSub_map_piA` applied to `B'`).
-/

open MvPolynomial Module Set
open StrongSix.M2 (hdata)

namespace LSG.MEBV

open LSG.MEB (Blk AbBlock IsRatSub perAb)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

variable (B) in
/-- The family of bases. -/
abbrev baseB : Fin m → AbBlock := fun k => (B k).base

/-- The projection `π_base : Tan → ∏ ℂ^{g_k}`. -/
def piB : Tan d₀ d₁ B →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) :=
  (LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))

@[simp] theorem piB_apply (u : Tan d₀ d₁ B) : piB u = u.2.2.1 := rfl

/-- The base variables inside `Var`. -/
def mvB : LSG.MEB.Var d₀ d₁ (baseB B) → Var d₀ d₁ B
  | .x i => .x i
  | .y j => .y j
  | .z j => .z j
  | .e k c => .e k (Sum.inl c)

/-- Decoding the linear coordinates `(x, b, w)`. -/
def decV (i : Fin (d₀ + d₁ + m)) : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m :=
  Sum.map finSumFinEquiv.symm id (finSumFinEquiv.symm i)

theorem decV_surj (q : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m) :
    ∃ i, decV (d₀ := d₀) (d₁ := d₁) (m := m) i = q := by
  refine ⟨finSumFinEquiv (Sum.map finSumFinEquiv id q), ?_⟩
  simp only [decV, Equiv.symm_apply_apply]
  rcases q with q | q <;> simp

/-- The linear coordinates `(x, b, w)` as one vector. -/
def rhoV : Tan d₀ d₁ B →ₗ[ℂ] (Fin (d₀ + d₁ + m) → ℂ) where
  toFun u i := Sum.elim (Sum.elim u.1 u.2.1) u.2.2.2 (decV i)
  map_add' u v := by
    funext i; simp only [Pi.add_apply]; rcases decV i with (_ | _) | _ <;> rfl
  map_smul' c u := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply]; rcases decV i with (_ | _) | _ <;> rfl

variable {H : Set (GPt d₀ d₁ B)}

/-- **The Lie algebra of `zcl_{G_b} (exp (0 × 0 × π_base(lieAlg H)))` is `0 × 0 × π_base(lieAlg H)`.** -/
theorem lieAlg_zclB_eq (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ((((lieAlg hH).map piB).map LSG.MEB.inAbL) : Submodule ℂ (LSG.MEB.Tan d₀ d₁ (baseB B))) =
      LSG.MEB.lieAlg (LSG.MEB.zcl_isSubgroup (LSG.MEB.isSubgroupG_expG_image
        (((lieAlg hH).map piB).map LSG.MEB.inAbL))) := by
  classical
  set T := lieAlg hH with hTdef
  set P := T.map (piB (d₀ := d₀) (d₁ := d₁) (B := B)) with hPdef
  set PA := P.map (LSG.MEB.inAbL (d₀ := d₀) (d₁ := d₁) (B := baseB B))
  set S : Set (LSG.MEB.GPt d₀ d₁ (baseB B)) := LSG.MEB.expG d₀ d₁ (baseB B) '' (PA : Set _)
  have hB : LSG.MEB.IsSubgroupG (LSG.MEB.zcl S) :=
    LSG.MEB.zcl_isSubgroup (LSG.MEB.isSubgroupG_expG_image PA)
  have hBc : LSG.MEB.IsZClosed (LSG.MEB.zcl S) := LSG.MEB.isZClosed_zcl S
  have hPB : PA ≤ LSG.MEB.lieAlg hB := by
    intro v hv c
    rw [LSG.MEB.mem_Htil]
    exact LSG.MEB.subset_zcl S ⟨c • v, PA.smul_mem c hv, rfl⟩
  have hSB : LSG.MEB.vanish S ≤ LSG.MEB.vanish (LSG.MEB.H0 hB) := by
    rw [← LSG.MEB.vanish_zcl S]; exact LSG.MEB.vanish_antitone (LSG.MEB.H0_subset hB hBc)
  haveI := LSG.MEB.vanish_H0_isPrime hB
  obtain ⟨ι, _, g, -, hb, hcard⟩ := LSG.ME.exists_coord_transcendenceBasis (LSG.MEB.vanish (LSG.MEB.H0 hB))
  have hindB : ∀ Q : MvPolynomial ι ℂ, rename g Q ∈ LSG.MEB.vanish (LSG.MEB.H0 hB) → Q = 0 := by
    intro Q hQ
    refine (algebraicIndependent_iff.mp hb.1) Q ?_
    rw [← aeval_rename]
    exact (LSG.ME.aeval_genPt_eq_zero_iff _).mpr hQ
  have hSpt : ∀ g' ∈ S, g'.1 = 0 ∧ ∀ j, g'.ym j = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨rfl, fun j => Units.ext (by simp [LSG.MEB.expG_apply, LSG.MEB.expGf, LSG.MEB.GPt.ym,
      LSG.MEB.expU])⟩
  have hgE : ∀ i, ∃ k c, g i = LSG.MEB.Var.e k c := by
    intro i
    rcases hgi : g i with j | j | j | ⟨k, c⟩
    · exfalso
      have hm : rename g (X i) ∈ LSG.MEB.vanish (LSG.MEB.H0 hB) := hSB (LSG.MEB.mem_vanish.mpr
        fun g' hg' lam => by
          rw [rename_X, hgi, eval_X, LSG.MEB.coords_x]; exact congrFun (hSpt g' hg').1 j)
      have := congrArg (eval fun _ => (1 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.MEB.vanish (LSG.MEB.H0 hB) := hSB (LSG.MEB.mem_vanish.mpr
        fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.MEB.coords_y,
            (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.MEB.vanish (LSG.MEB.H0 hB) := hSB (LSG.MEB.mem_vanish.mpr
        fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.MEB.coords_z,
            (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exact ⟨k, c, rfl⟩
  -- `K₀ = T ∩ ker π_base` and its coordinates
  set f := (piB (d₀ := d₀) (d₁ := d₁) (B := B)).comp T.subtype
  have hrange : LinearMap.range f = P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  set K0 := LinearMap.ker f
  set f0 := (rhoV (d₀ := d₀) (d₁ := d₁) (B := B)).comp (T.subtype.comp K0.subtype)
  have hf0 : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hZ : ((w : T) : Tan d₀ d₁ B).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hco : ∀ q, Sum.elim (Sum.elim ((w : T) : Tan d₀ d₁ B).1 ((w : T) : Tan d₀ d₁ B).2.1)
        ((w : T) : Tan d₀ d₁ B).2.2.2 q = 0 := fun q => by
      obtain ⟨i, rfl⟩ := decV_surj (d₀ := d₀) (d₁ := d₁) (m := m) q
      exact congrFun hw i
    have : ((w : T) : Tan d₀ d₁ B) = 0 :=
      Prod.ext (funext fun i => hco (.inl (.inl i)))
        (Prod.ext (funext fun j => hco (.inl (.inr j)))
          (Prod.ext hZ (funext fun k => hco (.inr k))))
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ιL, -, hsurjL⟩ := LSG.ME.exists_coord_surj (LinearMap.range f0)
  have hr : finrank ℂ (LinearMap.range f0) = finrank ℂ K0 := LinearMap.finrank_range_of_inj hf0
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  -- the combined family of coordinates
  let varV : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m → Var d₀ d₁ B :=
    Sum.elim (Sum.elim Var.x Var.y) fun k => Var.eT k (B k).t₀
  set e := Sum.elim (fun l => varV (decV (ιL l))) (fun i => mvB (g i))
  set s : Fin (finrank ℂ (LinearMap.range f0)) → Set ℂ :=
    fun l => Sum.elim (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ)) (fun _ => univ) (decV (ιL l))
  have hX : ∀ Q : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0))) ℂ,
      (∀ x ∈ Set.pi univ s, eval x Q = 0) → Q = 0 := by
    intro Q hQ
    refine funext_set s (fun l => ?_) fun x hx => by rw [hQ x hx, map_zero]
    change (Sum.elim (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ)) (fun _ => univ)
      (decV (ιL l)) : Set ℂ).Infinite
    rcases decV (ιL l) with (_ | _) | _
    · exact Set.infinite_univ
    · exact (Set.finite_singleton 0).infinite_compl
    · exact Set.infinite_univ
  -- generic points of `exp (0 × 0 × P)`
  set Y : Set (ι → ℂ) := {y | ∃ u ∈ T, (∀ k, (B k).base.θ (u.2.2.1 k) (B k).base.i₀ ≠ 0) ∧
    ∃ μ : Fin m → ℂ, (∀ k, μ k ≠ 0) ∧ y = LSG.MEB.liftZ (LSG.MEB.inAbL (piB u)) μ ∘ g}
  set L0 : MvPolynomial (LSG.MEB.Var d₀ d₁ (baseB B)) ℂ := ∏ k, X (LSG.MEB.Var.e k (B k).base.i₀)
  have hL0 : ∀ (v : LSG.MEB.Tan d₀ d₁ (baseB B)) μ,
      eval (LSG.MEB.liftZ v μ) L0 = ∏ k, μ k * (B k).base.θ (v.2.2 k) (B k).base.i₀ := by
    intro v μ
    simp [L0, LSG.MEB.liftZ]
  have hY : ∀ Q : MvPolynomial ι ℂ, (∀ y ∈ Y, eval y Q = 0) → Q = 0 := by
    intro Q hQ
    refine hindB Q (hSB ?_)
    have hpr := LSG.MEB.vanish_expG_image_isPrime PA
    have hprod : rename g Q * L0 ∈ LSG.MEB.vanish S := by
      rw [LSG.MEB.mem_vanish_expG_image_iff]
      intro v hv μ
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
      rw [map_mul, hL0]
      by_cases h0 : ∏ k, μ k * (B k).base.θ ((LSG.MEB.inAbL (piB u) : LSG.MEB.Tan d₀ d₁ (baseB B)).2.2 k)
          (B k).base.i₀ = 0
      · rw [h0, mul_zero]
      · have hne : ∀ k, μ k * (B k).base.θ (u.2.2.1 k) (B k).base.i₀ ≠ 0 := fun k =>
          (Finset.prod_ne_zero_iff.mp h0) k (Finset.mem_univ k)
        rw [eval_rename, hQ _ ⟨u, hu, fun k => right_ne_zero_of_mul (hne k), μ,
          fun k => left_ne_zero_of_mul (hne k), rfl⟩, zero_mul]
    refine (hpr.mem_or_mem hprod).resolve_right fun hL => ?_
    have := (LSG.MEB.mem_vanish_expG_image_iff PA).mp hL 0 PA.zero_mem 1
    rw [hL0] at this
    exact (Finset.prod_ne_zero_iff.mpr fun k _ => by simpa using (B k).base.θ_i₀) this
  haveI := vanish_H0_isPrime hH
  have hind : ∀ R : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0)) ⊕ ι) ℂ,
      rename e R ∈ vanish (H0 hH) → R = 0 := by
    intro R hRm
    refine LSG.ME.eq_zero_of_eval_elim hX hY fun x hx y hy => ?_
    obtain ⟨u, hu, hgen, μ, hμ, rfl⟩ := hy
    set y' : Fin (finrank ℂ (LinearMap.range f0)) → ℂ := fun l =>
      Sum.elim (Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j))
        (fun k => (x l / μ k + (B k).Φ (u.2.2.1 k) (B k).t₀) / (B k).base.θ (u.2.2.1 k) (B k).base.i₀ -
          u.2.2.2 k) (decV (ιL l))
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hsurjL y'
    have hwZ : ((w : T) : Tan d₀ d₁ B).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hpt : Sum.elim x (LSG.MEB.liftZ (LSG.MEB.inAbL (piB u)) μ ∘ g) =
        liftZ (u + ((w : T) : Tan d₀ d₁ B)) μ ∘ e := by
      funext t
      cases t with
      | inl l =>
        have hl := hw l
        have hxl : x l ∈ s l := hx l (Set.mem_univ l)
        change x l = liftZ (u + ((w : T) : Tan d₀ d₁ B)) μ (varV (decV (ιL l)))
        simp only [s] at hxl
        change Sum.elim (Sum.elim ((w : T) : Tan d₀ d₁ B).1 ((w : T) : Tan d₀ d₁ B).2.1)
          ((w : T) : Tan d₀ d₁ B).2.2.2 (decV (ιL l)) = y' l at hl
        simp only [y'] at hl
        generalize decV (ιL l) = q at hl hxl ⊢
        rcases q with (i | j) | k
        · change ((w : T) : Tan d₀ d₁ B).1 i = x l - u.1 i at hl
          change x l = u.1 i + ((w : T) : Tan d₀ d₁ B).1 i
          rw [hl]; ring
        · change ((w : T) : Tan d₀ d₁ B).2.1 j = Complex.log (x l) - u.2.1 j at hl
          change x l ≠ 0 at hxl
          change x l = Complex.exp (u.2.1 j + ((w : T) : Tan d₀ d₁ B).2.1 j)
          rw [hl, add_sub_cancel, Complex.exp_log hxl]
        · change ((w : T) : Tan d₀ d₁ B).2.2.2 k = (x l / μ k + (B k).Φ (u.2.2.1 k) (B k).t₀) /
            (B k).base.θ (u.2.2.1 k) (B k).base.i₀ - u.2.2.2 k at hl
          change x l = μ k * ((B k).base.θ ((u + ((w : T) : Tan d₀ d₁ B)).2.2.1 k) ((B k).fc (B k).t₀) *
            (u + ((w : T) : Tan d₀ d₁ B)).2.2.2 k - (B k).Φ ((u + ((w : T) : Tan d₀ d₁ B)).2.2.1 k) (B k).t₀)
          have hz : (u + ((w : T) : Tan d₀ d₁ B)).2.2.1 k = u.2.2.1 k := by simp [hwZ]
          rw [hz, (B k).fc_t₀]
          simp only [Prod.snd_add, Pi.add_apply, hl]
          field_simp [hgen k, hμ k]
          ring
      | inr i =>
        obtain ⟨k, c, hkc⟩ := hgE i
        simp only [Sum.elim_inr, Function.comp_apply, e, hkc, mvB, LSG.MEB.liftZ, liftZ]
        simp [Tan.blkV, hwZ]
    rw [hpt, ← eval_rename]
    rw [H0, vanish_zcl, mem_vanish_expG_iff] at hRm
    exact hRm _ (T.add_mem hu (w : T).2) μ
  -- the count
  have hcount := LSG.ME.card_le_trdeg_of_indep (vanish (H0 hH)) e hind
  rw [← LSG.ME.hdim_eq_trdeg blk (fun _ => 1) (fun _ => le_rfl), hdim_H0 hH hc _ fun _ => le_rfl,
    Fintype.card_sum, Fintype.card_fin] at hcount
  have hι : Fintype.card ι = finrank ℂ (LSG.MEB.lieAlg hB) + m := by
    have := congrArg Cardinal.toNat hcard
    rwa [Cardinal.toNat_natCast, ← LSG.ME.hdim_eq_trdeg LSG.MEB.blk (fun _ => 1) (fun _ => le_rfl),
      LSG.MEB.hdim_H0 hB hBc _ fun _ => le_rfl] at this
  have hPA : finrank ℂ PA = finrank ℂ P :=
    (Submodule.equivMapOfInjective _ LSG.MEB.inAbL_injective P).finrank_eq.symm
  have hle : finrank ℂ (LSG.MEB.lieAlg hB) ≤ finrank ℂ PA := by
    have hK : finrank ℂ (LinearMap.ker f) = finrank ℂ K0 := rfl
    have hTT : finrank ℂ T = finrank ℂ (lieAlg hH) := rfl
    omega
  exact Submodule.eq_of_le_of_finrank_le hPB hle

/-- **`π_base(lieAlg H)` is rational for the base periods.** -/
theorem isRatSub_map_piB (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsRatSub (perBase B) ((lieAlg hH).map (piB (d₀ := d₀) (d₁ := d₁))) := by
  set P := (lieAlg hH).map (piB (d₀ := d₀) (d₁ := d₁) (B := B))
  set PA := P.map (LSG.MEB.inAbL (d₀ := d₀) (d₁ := d₁) (B := baseB B))
  have hB := LSG.MEB.zcl_isSubgroup (LSG.MEB.isSubgroupG_expG_image PA)
  have hBc : LSG.MEB.IsZClosed (LSG.MEB.zcl (LSG.MEB.expG d₀ d₁ (baseB B) '' (PA : Set _))) :=
    LSG.MEB.isZClosed_zcl _
  have h := LSG.MEB.isRatSub_map_piA hB hBc
  rw [← lieAlg_zclB_eq hH hc] at h
  have e : PA.map LSG.MEB.piA = P := by
    have hid : (LSG.MEB.piA (d₀ := d₀) (d₁ := d₁) (B := baseB B)).comp LSG.MEB.inAbL = LinearMap.id :=
      LinearMap.ext fun z => rfl
    simp only [PA]; rw [← Submodule.map_comp, hid, Submodule.map_id]
  rw [e] at h
  exact h

end LSG.MEBV
