/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.MEV.SubgroupAbV
import LSG.MEV.MultEstStmtV

/-!
# W88 §7 for the class `𝒞`: the abelian image of a closed subgroup of `G̃`

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)` with `P = π_Z(lieAlg H)`, the abelian subgroup
`B = zcl (exp_G (0 × 0 × P))` of `G = G_a^{d₀} × G_m^{d₁} × E^m` (the layer `LSG.ME`) has Lie
algebra
exactly `0 × 0 × P` (**`lieAlg_zclB_eq`**). This is the transcendence-degree count inside the proof
of
`LSG.MEV.isAbelianTangent_map_piZ` (`LSG/MEV/SubgroupAbV.lean`, whose statement only exports the
abelian-tangent property); the argument is reproduced verbatim up to that step.
It is used to count points modulo an obstruction (`LSG.W88.Sec7VCount`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Set Module
open LSG.W88 (IsAbelianTangent)
open LSG.AuxV (ellN)
open LSG.W88.Vec (vecIncl torIncl g2Incl)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- The abelian subgroup `B = zcl (exp_G (0 × 0 × P))`. -/
def zclB (Ls : Fin m → PeriodPair) (P : Submodule ℂ (Fin m → ℂ)) :
    Set (LSG.ME.GPt ℂ d₀ d₁ (LSG.ME.g2L Ls) (LSG.ME.g3L Ls)) :=
  LSG.ME.zcl (LSG.ME.expG Ls ''
    (P.map (LSG.ME.inAbL (d₀ := d₀) (d₁ := d₁) (m := m)) : Set (LSG.W88.Tan d₀ d₁ m)))

theorem zclB_isSubgroup (P : Submodule ℂ (Fin m → ℂ)) :
    LSG.ME.IsSubgroupG (zclB (d₀ := d₀) (d₁ := d₁) Ls P) :=
  LSG.ME.zcl_isSubgroup two_ne_zero (LSG.ME.discr_g2L Ls) (LSG.ME.expG_submodule_isSubgroup _)

theorem zclB_closed (P : Submodule ℂ (Fin m → ℂ)) :
    LSG.ME.IsZClosed (zclB (d₀ := d₀) (d₁ := d₁) Ls P) := LSG.ME.isZClosed_zcl _

/-- **The Lie algebra of `B` is `0 × 0 × π_Z(lieAlg H)`** (proof as in `isAbelianTangent_map_piZ`).
-/
theorem lieAlg_zclB_eq {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ((lieAlg Ls hH).map piZ).map (LSG.ME.inAbL (d₀ := d₀) (d₁ := d₁) (m := m)) =
      LSG.ME.lieAlg Ls (zclB_isSubgroup (d₀ := d₀) (d₁ := d₁) ((lieAlg Ls hH).map piZ))
        (zclB_closed ((lieAlg Ls hH).map piZ)) := by
  classical
  set T := lieAlg Ls hH with hTdef
  set P := T.map (piZ (d₀ := d₀) (d₁ := d₁) (m := m)) with hPdef
  set PA := P.map (LSG.ME.inAbL (d₀ := d₀) (d₁ := d₁) (m := m))
  -- the abelian subgroup `B`
  set S : Set (LSG.ME.GPt ℂ d₀ d₁ (LSG.ME.g2L Ls) (LSG.ME.g3L Ls)) :=
    LSG.ME.expG Ls '' (PA : Set (LSG.W88.Tan d₀ d₁ m))
  have hB : LSG.ME.IsSubgroupG (LSG.ME.zcl S) :=
    LSG.ME.zcl_isSubgroup two_ne_zero (LSG.ME.discr_g2L Ls) (LSG.ME.expG_submodule_isSubgroup PA)
  have hBc : LSG.ME.IsZClosed (LSG.ME.zcl S) := LSG.ME.isZClosed_zcl S
  have hPB : PA ≤ LSG.ME.lieAlg Ls hB hBc := by
    intro v hv
    rw [LSG.ME.mem_lieAlg]
    intro c
    rw [LSG.ME.mem_Htil]
    exact LSG.ME.subset_zcl S ⟨c • v, PA.smul_mem c hv, rfl⟩
  have hSB : LSG.ME.vanish S ≤ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) := by
    rw [← LSG.ME.vanish_zcl S]; exact LSG.ME.vanish_antitone (LSG.ME.H0_subset hB hBc)
  have := LSG.ME.vanish_H0_isPrime (Ls := Ls) hB hBc
  obtain ⟨ι, _, g, -, hb, hcard⟩ :=
    LSG.ME.exists_coord_transcendenceBasis (LSG.ME.vanish (LSG.ME.H0 Ls hB hBc))
  have hindB : ∀ Q : MvPolynomial ι ℂ, rename g Q ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) →
      Q = 0 := by
    intro Q hQ
    refine (algebraicIndependent_iff.mp hb.1) Q ?_
    rw [← aeval_rename]
    exact (LSG.ME.aeval_genPt_eq_zero_iff _).mpr hQ
  have hSpt : ∀ g' ∈ S, g'.1 = 0 ∧ ∀ j, g'.ym j = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨rfl, fun j => Units.ext (by simp [LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU,
      LSG.ME.inAbL])⟩
  have hgE : ∀ i, ∃ k c, g i = LSG.ME.Var.e k c := by
    intro i
    rcases hgi : g i with j | j | j | ⟨k, c⟩
    · exfalso
      have hm : rename g (X i) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [rename_X, hgi, eval_X]; exact congrFun (hSpt g' hg').1 j)
      have := congrArg (eval fun _ => (1 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.ME.coords,
            LSG.ME.coordsZ_y, (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.ME.coords,
            LSG.ME.coordsZ_z, (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exact ⟨k, c, rfl⟩
  -- `K₀ = T′ ∩ ker π_Z` and its coordinates
  set f := (piZ (d₀ := d₀) (d₁ := d₁) (m := m)).comp T.subtype
  have hrange : LinearMap.range f = P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  set K0 := LinearMap.ker f
  set f0 := (rhoV (d₀ := d₀) (d₁ := d₁) (m := m)).comp (T.subtype.comp K0.subtype)
  have hf0 : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hZ : ((w : T) : TanG d₀ d₁ m).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hco : ∀ q, Sum.elim (Sum.elim ((w : T) : TanG d₀ d₁ m).1 ((w : T) : TanG d₀ d₁ m).2.1)
        ((w : T) : TanG d₀ d₁ m).2.2.2 q = 0 := fun q => by
      obtain ⟨i, rfl⟩ := decV_surj q
      exact congrFun hw i
    have : ((w : T) : TanG d₀ d₁ m) = 0 :=
      Prod.ext (funext fun i => hco (.inl (.inl i)))
        (Prod.ext (funext fun j => hco (.inl (.inr j)))
          (Prod.ext hZ (funext fun k => hco (.inr k))))
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ιL, -, hsurjL⟩ := LSG.ME.exists_coord_surj (LinearMap.range f0)
  have hr : finrank ℂ (LinearMap.range f0) = finrank ℂ K0 := LinearMap.finrank_range_of_inj hf0
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  -- the combined family of coordinates
  have hPk : ∀ k, ¬ actB P k → ∀ u ∈ T, u.2.2.1 k = 0 := by
    intro k hk u hu
    by_contra hne
    exact hk ⟨piZ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, hne⟩
  let fcV : Fin m → Var d₀ d₁ m := fun k => if actB P k then .e k 3 else .e k 4
  let varV : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m → Var d₀ d₁ m :=
    Sum.elim (Sum.elim Var.x Var.y) fcV
  set e := Sum.elim (fun l => varV (decV (ιL l))) (fun i => mvV (g i))
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
  set Y : Set (ι → ℂ) := {y | ∃ u ∈ T, (∀ k, actB P k → u.2.2.1 k ∉ (Ls k).lattice) ∧
    ∃ lam : Fin m → ℂˣ, y = LSG.ME.coords (LSG.ME.expG Ls
      (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) (piZ u))) lam ∘ g}
  have hY : ∀ Q : MvPolynomial ι ℂ, (∀ y ∈ Y, eval y Q = 0) → Q = 0 := by
    intro Q hQ
    refine hindB Q (hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => ?_))
    obtain ⟨v, hv, rfl⟩ := hg'
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    refine dens_ME P (rename g Q) (fun z' hz' hgen lam' => ?_) hz lam
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz'
    rw [eval_rename]
    exact hQ _ ⟨u, hu, hgen, lam', rfl⟩
  have := vanish_H0_isPrime (Ls := Ls) hH
  have hind : ∀ R : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0)) ⊕ ι) ℂ,
      rename e R ∈ vanish (H0 Ls hH) → R = 0 := by
    intro R hRm
    refine LSG.ME.eq_zero_of_eval_elim hX hY fun x hx y hy => ?_
    obtain ⟨u, hu, hgen, lam, rfl⟩ := hy
    set y' : Fin (finrank ℂ (LinearMap.range f0)) → ℂ := fun l =>
      Sum.elim (Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j))
        (fun k => x l / lam k - u.2.2.2 k + zeta (Ls k) (u.2.2.1 k)) (decV (ιL l))
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hsurjL y'
    have hwZ : ((w : T) : TanG d₀ d₁ m).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hpt : Sum.elim x (LSG.ME.coords (LSG.ME.expG Ls
        (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) (piZ u))) lam ∘ g) =
        coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam ∘ e := by
      funext t
      cases t with
      | inl l =>
        have hl := hw l
        have hxl : x l ∈ s l := hx l (Set.mem_univ l)
        change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (varV (decV (ιL l)))
        simp only [s] at hxl
        change Sum.elim (Sum.elim ((w : T) : TanG d₀ d₁ m).1 ((w : T) : TanG d₀ d₁ m).2.1)
          ((w : T) : TanG d₀ d₁ m).2.2.2 (decV (ιL l)) = y' l at hl
        simp only [y'] at hl
        generalize decV (ιL l) = q at hl hxl ⊢
        rcases q with (i | j) | k
        · change ((w : T) : TanG d₀ d₁ m).1 i = x l - u.1 i at hl
          change x l = u.1 i + ((w : T) : TanG d₀ d₁ m).1 i
          rw [hl]; ring
        · change ((w : T) : TanG d₀ d₁ m).2.1 j = Complex.log (x l) - u.2.1 j at hl
          change x l ≠ 0 at hxl
          change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (.y j)
          rw [coords_expGV_y]
          change x l = Complex.exp (u.2.1 j + ((w : T) : TanG d₀ d₁ m).2.1 j)
          rw [hl, add_sub_cancel, Complex.exp_log hxl]
        · change ((w : T) : TanG d₀ d₁ m).2.2.2 k =
            x l / lam k - u.2.2.2 k + zeta (Ls k) (u.2.2.1 k) at hl
          have hz : (u + ((w : T) : TanG d₀ d₁ m)).2.2.1 k = u.2.2.1 k := by
            simp [hwZ]
          have hw' : (u + ((w : T) : TanG d₀ d₁ m)).2.2.2 k - zeta (Ls k) (u.2.2.1 k) =
              x l / lam k := by
            simp only [Prod.snd_add, Pi.add_apply, hl]; ring
          change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (fcV k)
          simp only [fcV]
          split_ifs with hk
          · rw [coords_expGV_e, hz, expN_of_notMem _ (hgen k hk)]
            simp only [ptAff, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
            rw [hw', mul_div_cancel₀ _ (lam k).ne_zero]
          · have h0 := hPk k hk u hu
            rw [coords_expGV_e, hz]
            have hmem : u.2.2.1 k ∈ (Ls k).lattice := by rw [h0]; exact (Ls k).lattice.zero_mem
            simp only [expN, hmem, ↓reduceIte, ptO, Matrix.cons_val_four, Matrix.tail_cons,
              Matrix.head_cons]
            rw [hw', mul_div_cancel₀ _ (lam k).ne_zero]
      | inr i =>
        obtain ⟨k, c, hkc⟩ := hgE i
        simp only [Sum.elim_inr, Function.comp_apply, e, hkc, mvV]
        rw [coords_expGV_e, expN_base]
        simp [hwZ, LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb]
        rfl
    rw [hpt, ← eval_rename]
    exact mem_vanish.mp hRm _ (expGV_mem_H0 hH (T.add_mem hu (w : T).2)) lam
  -- the count
  have hcount := LSG.ME.card_le_trdeg_of_indep (vanish (H0 Ls hH)) e hind
  rw [trdeg_H0 hH hc, Fintype.card_sum, Fintype.card_fin] at hcount
  have hι : Fintype.card ι = finrank ℂ (LSG.ME.lieAlg Ls hB hBc) + m := by
    have := congrArg Cardinal.toNat hcard
    rwa [Cardinal.toNat_natCast, LSG.ME.trdeg_H0 hB hBc] at this
  have hPA : finrank ℂ PA = finrank ℂ P :=
    (Submodule.equivMapOfInjective _ LSG.ME.inAbL_injective P).finrank_eq.symm
  have hle : finrank ℂ (LSG.ME.lieAlg Ls hB hBc) ≤ finrank ℂ PA := by
    have hK : finrank ℂ (LinearMap.ker f) = finrank ℂ K0 := rfl
    have hTT : finrank ℂ T = finrank ℂ (lieAlg Ls hH) := rfl
    omega
  exact Submodule.eq_of_le_of_finrank_le hPB hle

end

end LSG.MEV
