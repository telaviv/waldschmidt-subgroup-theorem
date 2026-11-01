/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.ME.MultEstStmt
import StrongSix.Thm1.Quot

/-!
# Counting points modulo the obstruction subgroup (W88 §7)

For obstruction data `O` (`LSG.ME.ObstrData`) with `G′ = O.grp = zcl (exp_G T_{G′})`:

* **`htil_le_span`**: `exp_G⁻¹(G′) ⊆ span_ℚ (T_{G′} + Ω)`. The `G_a` part lies in `h₀` (linear forms
  vanishing on `h₀` vanish on `G′`); the `G_m` part lies in `U^⊥ + 2πi ℚ^{d₁}` (characters in `U`
  are trivial on `G′`; `StrongSix.Thm1.mulVecLin_surjective`); the abelian part has a multiple in
  `t + Λ` (`exists_abelianTangent_Htil`: finitely many cosets).
* **`exists_inequiv_grid`**: for generators `y_j` of `Y` and `M ∈ ℕ` there are
  `(M+1)^λ` grid points `exp_G(Σ hⱼ yⱼ)`, `0 ≤ hⱼ ≤ M`, pairwise inequivalent modulo `G′`, where
  `λ = rk Y − rk (Y ∩ (T_{G′} + Ω))` (the rank of `W88`'s `Γ / Γ ∩ G′`).
-/

open MvPolynomial LSG.ME LSG.Elliptic LSG.Weierstrass Module

noncomputable section

namespace LSG.W88

variable {d0 d1 m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Membership in `G′` through polynomials vanishing on `exp_G(T_{G′})` -/

theorem eval_of_mem_grp (O : ObstrData d0 d1 Ls) {g : GPt ℂ d0 d1 (g2L Ls) (g3L Ls)}
    (hg : g ∈ O.grp) {P : MvPolynomial (Var d0 d1 m) ℂ}
    (hP : ∀ u ∈ O.tan, ∀ lam, eval (coords (expG Ls u) lam) P = 0) (lam : Fin m → ℂˣ) :
    eval (coords g lam) P = 0 := by
  rw [O.grp_eq] at hg
  refine hg P (mem_vanish.mpr ?_) lam
  rintro _ ⟨u, hu, rfl⟩ lam'
  exact hP u hu lam'

/-- **The `G_a` part of `G′` lies in `h₀`.** -/
theorem fst_mem_h0 (O : ObstrData d0 d1 Ls) {g : GPt ℂ d0 d1 (g2L Ls) (g3L Ls)}
    (hg : g ∈ O.grp) : g.1 ∈ O.h0 := by
  by_contra hn
  obtain ⟨f, hf, hfh⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hf0 : ∀ a ∈ O.h0, f a = 0 := fun a ha => by
    have : f a ∈ O.h0.map f := ⟨a, ha, rfl⟩
    rw [hfh] at this; exact this
  set P : MvPolynomial (Var d0 d1 m) ℂ := ∑ i, C (f (Pi.single i 1)) * X (Var.x i)
  have hev : ∀ (h : GPt ℂ d0 d1 (g2L Ls) (g3L Ls)) lam, eval (coords h lam) P = f h.1 := by
    intro h lam
    simp only [P, map_sum, map_mul, eval_C, eval_X, coords, coordsZ_x]
    conv_rhs => rw [pi_eq_sum_univ h.1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  apply hf
  rw [← hev g 1]
  refine eval_of_mem_grp O hg (fun u hu lam => ?_) 1
  rw [hev]
  exact hf0 _ hu.1

theorem coe_pow_toNat_mul (u : ℂˣ) (n : ℤ) :
    (u : ℂ) ^ n.toNat * ((u⁻¹ : ℂˣ) : ℂ) ^ (-n).toNat = (u : ℂ) ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simp
  · rcases k with _ | k
    · simp
    · have h1 : (-((k + 1 : ℕ) : ℤ)).toNat = 0 := by omega
      have h2 : (-(-((k + 1 : ℕ) : ℤ))).toNat = k + 1 := by omega
      rw [h1, h2, pow_zero, one_mul, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, inv_pow]

/-- **Characters in `U` are trivial on `G′`.** -/
theorem chr_eq_one_of_mem_grp (O : ObstrData d0 d1 Ls) {g : GPt ℂ d0 d1 (g2L Ls) (g3L Ls)}
    (hg : g ∈ O.grp) (φ : Fin d1 → ℤ) (hφ : (fun j => (φ j : ℚ)) ∈ O.U) :
    ∏ j, ((g.ym j : ℂˣ) : ℂ) ^ φ j = 1 := by
  set P : MvPolynomial (Var d0 d1 m) ℂ :=
    (∏ j, X (Var.y j) ^ (φ j).toNat * X (Var.z j) ^ (-φ j).toNat) - 1
  have hev : ∀ (h : GPt ℂ d0 d1 (g2L Ls) (g3L Ls)) lam,
      eval (coords h lam) P = ∏ j, ((h.ym j : ℂˣ) : ℂ) ^ φ j - 1 := by
    intro h lam
    simp only [P, map_sub, map_prod, map_mul, map_pow, eval_X, map_one, coords, coordsZ_y,
      coordsZ_z, coe_pow_toNat_mul]
  have h0 := eval_of_mem_grp O hg (P := P) (fun u hu lam => ?_) 1
  · rw [hev] at h0; exact sub_eq_zero.mp h0
  · rw [hev, sub_eq_zero]
    have hU := hu.2.1 _ hφ
    have : ∏ j, (((expG Ls u).ym j : ℂˣ) : ℂ) ^ φ j = Complex.exp (∑ j, (φ j : ℂ) * u.2.1 j) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [GPt.ym, expG, expU, toMul_ofMul, Units.val_mk0]
      rw [← Complex.exp_int_mul]
    rw [this]
    have hU' : ∑ j, (φ j : ℂ) * u.2.1 j = 0 := by simpa using hU
    rw [hU', Complex.exp_zero]

/-- **Torus part**: `b ∈ U^⊥ + 2πi ℚ^{d₁}` when all characters in `U` are trivial on `e^b`. -/
theorem exists_rat_torus (U : Submodule ℚ (Fin d1 → ℚ)) (b : Fin d1 → ℂ)
    (h : ∀ φ : Fin d1 → ℤ, (fun j => (φ j : ℚ)) ∈ U → Complex.exp (∑ j, (φ j : ℂ) * b j) = 1) :
    ∃ r : Fin d1 → ℚ, (fun j => b j - 2 * Real.pi * Complex.I * r j) ∈ torusLie U := by
  -- each basis row of `U` pairs with `b` into `2πi ℚ`
  have hq : ∀ k, ∃ q : ℚ, ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) * b j =
      2 * Real.pi * Complex.I * q := by
    intro k
    obtain ⟨n, hn, z, hz⟩ := StrongSix.Thm1.exists_common_den (StrongSix.Thm1.phiRow U k)
    have hzU : (fun j => (z j : ℚ)) ∈ U := by
      have : (fun j => (z j : ℚ)) = (n : ℚ) • StrongSix.Thm1.phiRow U k :=
        funext fun j => by simp [hz j]
      rw [this]; exact U.smul_mem _ (StrongSix.Thm1.phiRow_mem U k)
    obtain ⟨l, hl⟩ := Complex.exp_eq_one_iff.mp (h z hzU)
    refine ⟨l / n, ?_⟩
    have hsum : ∑ j, (z j : ℂ) * b j = (n : ℂ) * ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) * b j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (z j : ℂ) = ((z j : ℚ) : ℂ) := by push_cast; rfl
      rw [this, hz j]; push_cast; ring
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [hsum] at hl
    push_cast
    field_simp
    linear_combination hl
  choose q hq using hq
  set M : Matrix (Fin (finrank ℚ U)) (Fin d1) ℚ := Matrix.of fun k j => StrongSix.Thm1.phiRow U k j
  obtain ⟨r, hr⟩ := StrongSix.Thm1.mulVecLin_surjective M
    (StrongSix.Thm1.phiRow_linearIndependent U) q
  refine ⟨r, ?_⟩
  have hrow : ∀ k, ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) *
      (b j - 2 * Real.pi * Complex.I * r j) = 0 := by
    intro k
    have hk := congrFun hr k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply] at hk
    have hk' : ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) * (r j : ℂ) = (q k : ℂ) := by
      exact_mod_cast hk
    simp only [mul_sub, Finset.sum_sub_distrib, hq k]
    rw [show ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) * (2 * Real.pi * Complex.I * r j) =
      2 * Real.pi * Complex.I * ∑ j, ((StrongSix.Thm1.phiRow U k j : ℚ) : ℂ) * r j by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hk', sub_self]
  intro φ hφ
  have hspan : φ ∈ Submodule.span ℚ (Set.range (StrongSix.Thm1.phiRow U)) := by
    have hb := (Module.finBasis ℚ U).span_eq
    have : (⟨φ, hφ⟩ : U) ∈ Submodule.span ℚ (Set.range (Module.finBasis ℚ U)) := by
      rw [hb]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span U.subtype this
    rw [← Set.range_comp] at this
    exact this
  clear hφ
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hrow k
  | zero => simp
  | add x y _ _ px py =>
    simp only [Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib, px, py, add_zero]
  | smul a x _ px =>
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
    rw [show ∑ j, (a : ℂ) * (x j : ℂ) * (b j - 2 * Real.pi * Complex.I * r j) =
      (a : ℂ) * ∑ j, (x j : ℂ) * (b j - 2 * Real.pi * Complex.I * r j) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, px, mul_zero]

/-- **Abelian part**: every element of `exp⁻¹(G′) ∩ (0 × 0 × ℂ^m)` has a multiple in `t + Λ`. -/
theorem exists_nsmul_ab (O : ObstrData d0 d1 Ls) {x : Fin m → ℂ}
    (hx : inAb (d₀ := d0) (d₁ := d1) x ∈ Htil Ls O.grp_sub) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ v ∈ O.t, ∃ l : Fin m → ℂ, (∀ j, l j ∈ (Ls j).lattice) ∧ n • x = v + l := by
  classical
  obtain ⟨t', -, ht', F, -, hF⟩ := exists_abelianTangent_Htil O.grp_sub O.grp_closed
  have htt : ∀ z, z ∈ t' ↔ z ∈ O.t := by
    intro z
    rw [ht', mem_lieAlg]
    simp only [mem_Htil]
    rw [O.lie]
    simp [inAb, Submodule.mem_prod]
  have hmem : ∀ k : ℕ, inAb (d₀ := d0) (d₁ := d1) ((k + 1 : ℕ) • x) ∈ Htil Ls O.grp_sub := by
    intro k
    have : inAb (d₀ := d0) (d₁ := d1) ((k + 1 : ℕ) • x) = (k + 1 : ℕ) • inAb x := by
      simp [inAb]
    rw [this]; exact (Htil Ls O.grp_sub).nsmul_mem hx _
  choose f hfF v hv l hl hdec using fun k : ℕ => hF _ (hmem k)
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (F.card + 1)) (t := F) (f := f) (by simp) (fun k _ => hfF k)
  refine ⟨(a : ℤ) - b, sub_ne_zero.mpr (by exact_mod_cast hab), v a - v b,
    Submodule.sub_mem _ ((htt _).mp (hv a)) ((htt _).mp (hv b)), l a - l b,
    fun j => (Ls j).lattice.sub_mem (hl a j) (hl b j), ?_⟩
  have e1 := hdec a
  have e2 := hdec b
  rw [hfab] at e1
  have : ((a : ℤ) - b) • x = ((a + 1 : ℕ) • x) - ((b + 1 : ℕ) • x) := by
    rw [sub_smul]; simp [add_smul]
  rw [this, e1, e2]; abel

/-! ### `exp⁻¹(G′) ⊆ span_ℚ (T_{G′} + Ω)` -/

/-- `T_{G′} + Ω` as an additive subgroup. -/
def tanPer (O : ObstrData d0 d1 Ls) : AddSubgroup (Tan d0 d1 m) :=
  O.tan.toAddSubgroup ⊔ Per Ls

theorem mem_span_of_zsmul {E : Type*} [AddCommGroup E] [Module ℚ E] {S : Set E} {x : E} {n : ℤ}
    (hn : n ≠ 0) (h : n • x ∈ Submodule.span ℚ S) : x ∈ Submodule.span ℚ S := by
  have : x = ((n : ℚ)⁻¹) • (n • x) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
  rw [this]; exact Submodule.smul_mem _ _ h

theorem htil_le_span (O : ObstrData d0 d1 Ls) {u : Tan d0 d1 m} (hu : u ∈ Htil Ls O.grp_sub) :
    u ∈ Submodule.span ℚ (tanPer O : Set (Tan d0 d1 m)) := by
  have hsub : ∀ w ∈ tanPer O, w ∈ Submodule.span ℚ (tanPer O : Set (Tan d0 d1 m)) :=
    fun w hw => Submodule.subset_span hw
  have htan : ∀ w ∈ O.tan, w ∈ tanPer O := fun w hw =>
    AddSubgroup.mem_sup_left (show w ∈ O.tan.toAddSubgroup from hw)
  have hper : ∀ w ∈ Per Ls, w ∈ tanPer O := fun w hw => AddSubgroup.mem_sup_right hw
  have hg : expG Ls u ∈ O.grp := mem_Htil.mp hu
  -- `G_a`
  have ha : u.1 ∈ O.h0 := fst_mem_h0 O hg
  -- `G_m`
  obtain ⟨r, hr⟩ := exists_rat_torus O.U u.2.1 fun φ hφ => by
    have h1 := chr_eq_one_of_mem_grp O hg φ hφ
    rw [← h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [GPt.ym, expG, expU, toMul_ofMul, Units.val_mk0]
    rw [← Complex.exp_int_mul]
  obtain ⟨N, hN, z, hz⟩ := StrongSix.Thm1.exists_common_den r
  set b' : Fin d1 → ℂ := fun j => u.2.1 j - 2 * Real.pi * Complex.I * r j
  set wL : Tan d0 d1 m := (u.1, b', 0) with hwL
  set wP : Tan d0 d1 m := (0, fun j => 2 * Real.pi * Complex.I * r j, 0) with hwP
  have hwL : wL ∈ O.tan := ⟨ha, hr, Submodule.zero_mem _⟩
  -- `N • wP ∈ Ω`
  have hNwP : (N : ℤ) • wP ∈ Per Ls := by
    refine ⟨by simp [wP], fun j => ⟨z j, ?_⟩, fun j => by simp [wP]⟩
    change ((N : ℕ) : ℤ) • ((2 * Real.pi * Complex.I * (r j : ℂ))) = _
    have : (z j : ℂ) = (N : ℂ) * r j := by exact_mod_cast hz j
    rw [zsmul_eq_mul, this]; push_cast; ring
  have hwP : wP ∈ Submodule.span ℚ (tanPer O : Set (Tan d0 d1 m)) :=
    mem_span_of_zsmul (n := N) (by exact_mod_cast hN) (hsub _ (hper _ hNwP))
  -- the abelian remainder
  set x : Fin m → ℂ := u.2.2
  have hsplit : u = wL + wP + inAb x := by
    refine Prod.ext (by simp [wL, wP, inAb]) (Prod.ext ?_ (by simp [wL, wP, inAb, x]))
    funext j; simp [wL, wP, inAb, b']
  have hNx : inAb (d₀ := d0) (d₁ := d1) ((N : ℤ) • x) ∈ Htil Ls O.grp_sub := by
    have h1 : (N : ℤ) • u ∈ Htil Ls O.grp_sub := (Htil Ls O.grp_sub).zsmul_mem hu _
    have h2 : (N : ℤ) • wL ∈ Htil Ls O.grp_sub :=
      (Htil Ls O.grp_sub).zsmul_mem (mem_Htil.mpr (O.expG_mem hwL)) _
    have h3 : (N : ℤ) • wP ∈ Htil Ls O.grp_sub := per_le_Htil O.grp_sub hNwP
    have : inAb (d₀ := d0) (d₁ := d1) ((N : ℤ) • x) = (N : ℤ) • u - (N : ℤ) • wL - (N : ℤ) • wP := by
      conv_rhs => rw [hsplit]
      simp only [smul_add]; abel_nf; simp [inAb]
    rw [this]
    exact (Htil Ls O.grp_sub).sub_mem ((Htil Ls O.grp_sub).sub_mem h1 h2) h3
  obtain ⟨n, hn, v, hv, l, hl, hnx⟩ := exists_nsmul_ab O hNx
  have hab : inAb (d₀ := d0) (d₁ := d1) x ∈ Submodule.span ℚ (tanPer O : Set (Tan d0 d1 m)) := by
    refine mem_span_of_zsmul (n := n * N) (mul_ne_zero hn (by exact_mod_cast hN)) (hsub _ ?_)
    have : (n * N) • inAb (d₀ := d0) (d₁ := d1) x = inAb v + inAb l := by
      refine Prod.ext (by simp [inAb]) (Prod.ext (by simp [inAb]) ?_)
      simp only [inAb, Prod.smul_snd, Prod.snd_add]
      rw [mul_smul, hnx]
    rw [this]
    refine (tanPer O).add_mem (htan _ ⟨Submodule.zero_mem _, Submodule.zero_mem _, hv⟩) (hper _ ?_)
    exact ⟨rfl, fun j => ⟨0, by simp [inAb]⟩, hl⟩
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hsub _ (htan _ hwL)) hwP) hab

/-! ### Ranks and the grid -/

theorem span_inf_eq {E : Type*} [AddCommGroup E] [Module ℚ E] (Y X : AddSubgroup E) :
    Submodule.span ℚ ((Y ⊓ X : AddSubgroup E) : Set E) =
      Submodule.span ℚ (Y : Set E) ⊓ Submodule.span ℚ (X : Set E) := by
  -- every element of `span_ℚ Y` has a nonzero integer multiple in `Y`
  have key : ∀ (Z : AddSubgroup E) (v : E), v ∈ Submodule.span ℚ (Z : Set E) →
      ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Z := by
    intro Z v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ px py =>
      obtain ⟨a, ha, hax⟩ := px
      obtain ⟨b, hb, hby⟩ := py
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul]
      exact Z.add_mem (Z.zsmul_mem hax _) (Z.zsmul_mem hby _)
    | smul q x _ px =>
      obtain ⟨a, ha, hax⟩ := px
      refine ⟨q.den * a, mul_ne_zero (by exact_mod_cast q.den_nz) ha, ?_⟩
      have : ((q.den * a : ℤ)) • (q • x) = q.num • (a • x) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ (q.num), ← Int.cast_smul_eq_zsmul ℚ a,
          smul_smul, smul_smul]
        congr 1
        push_cast
        rw [mul_comm (q.den : ℚ) a, mul_assoc, Rat.den_mul_eq_num, mul_comm]
      rw [this]; exact Z.zsmul_mem hax _
  apply le_antisymm
  · exact Submodule.span_le.mpr fun v hv =>
      ⟨Submodule.subset_span hv.1, Submodule.subset_span hv.2⟩
  · rintro v ⟨hY, hX⟩
    obtain ⟨a, ha, hav⟩ := key Y v hY
    obtain ⟨b, hb, hbv⟩ := key X v hX
    refine mem_span_of_zsmul (n := a * b) (mul_ne_zero ha hb) (Submodule.subset_span ⟨?_, ?_⟩)
    · rw [mul_comm, mul_smul]; exact Y.zsmul_mem hav _
    · rw [mul_smul]; exact X.zsmul_mem hbv _

theorem span_closure_range {E : Type*} [AddCommGroup E] [Module ℚ E] {μ : ℕ} (y : Fin μ → E) :
    Submodule.span ℚ ((AddSubgroup.closure (Set.range y) : AddSubgroup E) : Set E) =
      Submodule.span ℚ (Set.range y) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ px py => exact Submodule.add_mem _ px py
    | neg x _ px => exact Submodule.neg_mem _ px
  · exact Submodule.span_mono (AddSubgroup.subset_closure)

/-- **Independent generators modulo a `ℚ`-subspace** (StrongSix `exists_indep_mod_Omega`, `s = id`). -/
theorem exists_indep_mod {E : Type*} [AddCommGroup E] [Module ℚ E] {μ : ℕ} (y : Fin μ → E)
    (Q : Submodule ℚ E) :
    ∃ idx : Fin (finrank ℚ (Submodule.span ℚ (Set.range y)) -
        finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ Q)) → Fin μ,
      ∀ c : Fin _ → ℚ, (∑ k, c k • y (idx k)) ∈ Q → c = 0 := by
  classical
  set Y' := Submodule.span ℚ (Set.range y) with hY'
  set π : E →ₗ[ℚ] E ⧸ Q := Q.mkQ
  set t : Set (E ⧸ Q) := Set.range (π ∘ y) with ht
  have hspan_t : Submodule.span ℚ t = Y'.map Q.mkQ := by
    rw [ht, Set.range_comp, ← Submodule.map_span]
  have : FiniteDimensional ℚ Y' := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hdim : finrank ℚ (Submodule.span ℚ t) = finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Q) := by
    have := StrongSix.Roy.finrank_map_add_inf_ker Q.mkQ Y'
    rw [Submodule.ker_mkQ] at this
    rw [hspan_t]; omega
  obtain ⟨b, hbt, hbspan, hli⟩ := exists_linearIndependent ℚ t
  let _ : Fintype b := ((Set.finite_range _).subset hbt).fintype
  have hcard : Fintype.card b = finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Q) := by
    rw [← hdim, ← hbspan, ← finrank_span_eq_card hli, Subtype.range_coe]
  let e : Fin (finrank ℚ Y' - finrank ℚ ↥(Y' ⊓ Q)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ x : b, ∃ j, π (y j) = x := fun x => by
    obtain ⟨j, hj⟩ := hbt x.2
    exact ⟨j, hj⟩
  choose f hf using hpre
  refine ⟨fun k => f (e k), fun c hc => ?_⟩
  have h0 : ∑ k, c k • ((e k : b) : E ⧸ Q) = 0 := by
    have : Q.mkQ (∑ k, c k • y (f (e k))) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hc
    rw [map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hf (e k)]
  have hli' : LinearIndependent ℚ fun k => ((e k : b) : E ⧸ Q) := hli.comp e e.injective
  funext k
  exact (Fintype.linearIndependent_iff.mp hli') c h0 k

/-- **Pairwise inequivalent grid points.** -/
theorem exists_inequiv_grid (O : ObstrData d0 d1 Ls) {μ : ℕ} (y : Fin μ → Tan d0 d1 m) (M : ℕ) :
    ∃ F : Finset (GPt ℂ d0 d1 (g2L Ls) (g3L Ls)),
      (∀ g ∈ F, ∃ h : Fin μ → ℕ, (∀ j, h j ≤ M) ∧ g = expG Ls (∑ j, h j • y j)) ∧
      (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') ∧
      F.card = (M + 1) ^ (rk (AddSubgroup.closure (Set.range y)) -
        rk (AddSubgroup.closure (Set.range y) ⊓ tanPer O)) := by
  classical
  set Q := Submodule.span ℚ (tanPer O : Set (Tan d0 d1 m))
  have hrk : rk (AddSubgroup.closure (Set.range y)) - rk (AddSubgroup.closure (Set.range y) ⊓ tanPer O) =
      finrank ℚ (Submodule.span ℚ (Set.range y)) - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ Q) := by
    unfold rk
    rw [span_inf_eq, span_closure_range]
  obtain ⟨idx, hidx⟩ := exists_indep_mod y Q
  generalize hℓ : finrank ℚ (Submodule.span ℚ (Set.range y)) -
    finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ Q) = ℓ at idx hidx hrk
  set pt : (Fin ℓ → Fin (M + 1)) → GPt ℂ d0 d1 (g2L Ls) (g3L Ls) :=
    fun a => expG Ls (∑ k, (a k : ℕ) • y (idx k)) with hpt
  -- equivalence forces equality of coefficients
  have hinj : ∀ a b, pt a - pt b ∈ O.grp → a = b := by
    intro a b hab
    have e : expG Ls ((∑ k, (a k : ℕ) • y (idx k)) - ∑ k, (b k : ℕ) • y (idx k)) = pt a - pt b :=
      (expGHom Ls).map_sub _ _
    have hmem : (∑ k, (a k : ℕ) • y (idx k)) - ∑ k, (b k : ℕ) • y (idx k) ∈ Htil Ls O.grp_sub := by
      rw [mem_Htil, e]; exact hab
    have hQ := htil_le_span O hmem
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
  have hinj' : Function.Injective pt := fun a b h => hinj a b (by rw [h, sub_self]; exact O.grp_sub.zero_mem)
  -- `idx` is injective
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
        show (∑ k, if idx k = idx k₀ then (a k : ℕ) else 0) ≤ M
        rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg (fun e => hk (hidxinj e)))
          (by simp), if_pos rfl]
        exact Nat.lt_succ_iff.mp (a k₀).isLt
      · push Not at h
        simp [h]
    · simp only [pt]
      congr 1
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_ite_eq Finset.univ (idx k), if_pos (Finset.mem_univ _)]
  · intro g hg g' hg' hgg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hg'
    rw [hinj a b hgg]
  · rw [Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, hrk]

end LSG.W88
