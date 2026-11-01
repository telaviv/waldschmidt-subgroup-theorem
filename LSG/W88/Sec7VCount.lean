/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7VBase
import LSG.W88.Sec7VPoly
import LSG.W88.Sec7Count

/-!
# W88 §7 for the class `𝒞`: counting points modulo the obstruction

For obstruction data `O : ObstrDataV` (`grp = zcl (exp T̃′)`, Lie algebra `T̃′ = O.tan`):

* **`htilV_le_span`**: `exp⁻¹(grp) ⊆ span_ℚ (T̃′ + Ω̃)`. The additive part lies in `π₀(T̃′)` (linear
  forms); the toric part in `U^⊥ + 2πi ℚ^{d₁}` (characters in `U`, `exists_rat_torus`); the base
  part has a
  multiple in `t + Λ` (**`base_partV`**: through `grp ∩ {x = 0, y = 1}`, its finitely many
  components
  `finite_cosets_H0`, the abelian subgroup `B = zcl exp(0 × 0 × t)` with Lie algebra `0 × 0 × t`
  (`lieAlg_zclB_eq`) and the abelian finiteness `exists_abelianTangent_Htil`); the rest is a vector
  of
  the vector group in `exp⁻¹(grp)`, hence in `T̃′` (`lin_mem_lieAlg_of_Htil`).
* **`htilG_le_span`**: the same on `G` after the push-out `pushT`.
* **`exists_inequiv_grid_gen`**: `(M+1)^λ` grid points pairwise inequivalent (abstract version of
  `LSG.W88.exists_inequiv_grid`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module LSG.MEV
open LSG.W88.Vec (TanV PerV etaV vecIncl torIncl g2Incl perTanId perTan)
open LSG.ME (g2L g3L)

noncomputable section

namespace LSG.W88

variable {d0 r d1 m : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### Membership in `grp` through polynomials -/

theorem eval_of_mem_grpV (O : ObstrDataV d0 r d1 Ls M) {g : GPtV (d0 + r) d1 Ls}
    (hg : g ∈ O.grp) {P : MvPolynomial (Var (d0 + r) d1 m) ℂ}
    (hP : ∀ u ∈ O.tan, ∀ lam, eval (coords (expGV Ls u) lam) P = 0) (lam : Fin m → ℂˣ) :
    eval (coords g lam) P = 0 := by
  rw [O.grp_eq] at hg
  refine hg P (mem_vanish.mpr ?_) lam
  rintro _ ⟨u, hu, rfl⟩ lam'
  exact hP u hu lam'

/-- **The additive part.** -/
theorem fst_mem_tanV (O : ObstrDataV d0 r d1 Ls M) {g : GPtV (d0 + r) d1 Ls} (hg : g ∈ O.grp) :
    g.1 ∈ O.tan.map (LinearMap.fst ℂ _ _) := by
  by_contra hn
  obtain ⟨f, hf, hfh⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hf0 : ∀ a ∈ O.tan.map (LinearMap.fst ℂ _ _), f a = 0 := fun a ha => by
    have : f a ∈ (O.tan.map (LinearMap.fst ℂ _ _)).map f := ⟨a, ha, rfl⟩
    rw [hfh] at this; exact this
  set P : MvPolynomial (Var (d0 + r) d1 m) ℂ := ∑ i, C (f (Pi.single i 1)) * X (Var.x i)
  have hev : ∀ (h : GPtV (d0 + r) d1 Ls) lam, eval (coords h lam) P = f h.1 := by
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
  refine eval_of_mem_grpV O hg (fun u hu lam => ?_) 1
  rw [hev]
  exact hf0 _ ⟨u, hu, rfl⟩

theorem prB_mem_torusLie (O : ObstrDataV d0 r d1 Ls M) {u : TanG (d0 + r) d1 m} (hu : u ∈ O.tan) :
    u.2.1 ∈ torusLie O.S.U := by
  rw [← O.S.map_prB_tan]
  exact ⟨u, hu, rfl⟩

/-- **Characters in `U` are trivial on `grp`.** -/
theorem chr_eq_one_of_mem_grpV (O : ObstrDataV d0 r d1 Ls M) {g : GPtV (d0 + r) d1 Ls}
    (hg : g ∈ O.grp) (φ : Fin d1 → ℤ) (hφ : (fun j => (φ j : ℚ)) ∈ O.S.U) :
    ∏ j, ((g.ym j : ℂˣ) : ℂ) ^ φ j = 1 := by
  set P : MvPolynomial (Var (d0 + r) d1 m) ℂ :=
    (∏ j, X (Var.y j) ^ (φ j).toNat * X (Var.z j) ^ (-φ j).toNat) - 1
  have hev : ∀ (h : GPtV (d0 + r) d1 Ls) lam,
      eval (coords h lam) P = ∏ j, ((h.ym j : ℂˣ) : ℂ) ^ φ j - 1 := by
    intro h lam
    simp only [P, map_sub, map_prod, map_mul, map_pow, eval_X, map_one, coords, coordsZ_y,
      coordsZ_z, coe_pow_toNat_mul]
  have h0 := eval_of_mem_grpV O hg (P := P) (fun u hu lam => ?_) 1
  · rw [hev] at h0; exact sub_eq_zero.mp h0
  · rw [hev, sub_eq_zero]
    have hU := prB_mem_torusLie O hu _ hφ
    have : ∏ j, (((expGV Ls u).ym j : ℂˣ) : ℂ) ^ φ j =
        Complex.exp (∑ j, (φ j : ℂ) * u.2.1 j) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [GPtV.ym, expGV, LSG.ME.expU, toMul_ofMul, Units.val_mk0]
      rw [← Complex.exp_int_mul]
    rw [this]
    have hU' : ∑ j, (φ j : ℂ) * u.2.1 j = 0 := by simpa using hU
    rw [hU', Complex.exp_zero]

/-! ### The base part -/

theorem tan_map_piZ_le (O : ObstrDataV d0 r d1 Ls M) : O.tan.map piZ ≤ O.S.t := by
  rw [ObstrDataV.tan, SubgroupPreV.tan, Submodule.map_sup, Submodule.map_sup]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩; simp
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩; simp
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [perTan_one] at hx
    simp only [piZ_apply, g2Incl_apply]
    refine Submodule.span_induction (p := fun x _ => x.1 ∈ O.S.t) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨h1, -, -⟩; exact h1
    · exact O.S.t.zero_mem
    · intro x y _ _ hx hy; exact O.S.t.add_mem hx hy
    · intro c x _ hx; exact O.S.t.smul_mem c hx

theorem g2Incl_perTanId_mem (O : ObstrDataV d0 r d1 Ls M) {z w : Fin m → ℂ}
    (h : (z, w) ∈ perTanId Ls O.S.t) : g2Incl (z, w) ∈ O.tan := by
  refine Submodule.mem_sup_right ⟨(z, w), ?_, rfl⟩
  rw [perTan_one]; exact h

theorem exp_mul_eq_one {b : ℂ} (h : ∀ c : ℂ, Complex.exp (c * b) = 1) : b = 0 := by
  by_contra hb
  have := h (Real.pi * Complex.I / b)
  rw [div_mul_cancel₀ _ hb, Complex.exp_pi_mul_I] at this
  norm_num at this

/-- The points with trivial additive and toric coordinates. -/
def Z0 (n d1 : ℕ) (Ls : Fin m → PeriodPair) : Set (GPtV n d1 Ls) :=
  zeros ((Set.range fun i : Fin n => (X (.x i) : MvPolynomial (Var n d1 m) ℂ)) ∪
    Set.range fun j : Fin d1 => (X (.y j) - 1 : MvPolynomial (Var n d1 m) ℂ))

theorem mem_Z0 {n : ℕ} {g : GPtV n d1 Ls} : g ∈ Z0 n d1 Ls ↔ g.1 = 0 ∧ ∀ j, g.ym j = 1 := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, fun j => Units.ext ?_⟩
    · simpa [coords] using h _ (Or.inl ⟨i, rfl⟩) 1
    · simpa [coords, sub_eq_zero] using h _ (Or.inr ⟨j, rfl⟩) 1
  · rintro ⟨h1, h2⟩ P hP lam
    rcases hP with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp [coords, h1]
    · simp [coords, h2]

theorem Z0_isSubgroup {n : ℕ} : IsSubgroupG (Z0 n d1 Ls) where
  zero_mem := mem_Z0.mpr ⟨rfl, fun _ => rfl⟩
  add_mem g hg h hh := by
    obtain ⟨g1, g2⟩ := mem_Z0.mp hg
    obtain ⟨h1, h2⟩ := mem_Z0.mp hh
    refine mem_Z0.mpr ⟨?_, fun j => ?_⟩
    · change g.1 + h.1 = 0; rw [g1, h1, add_zero]
    · rw [GPtV.ym_add, g2, h2, mul_one]
  neg_mem g hg := by
    obtain ⟨g1, g2⟩ := mem_Z0.mp hg
    refine mem_Z0.mpr ⟨?_, fun j => ?_⟩
    · change -g.1 = 0; rw [g1, neg_zero]
    · rw [GPtV.ym_neg, g2, inv_one]

theorem expGV_mem_Z0 {n : ℕ} {z w : Fin m → ℂ} :
    expGV Ls ((0, 0, z, w) : TanG n d1 m) ∈ Z0 n d1 Ls :=
  mem_Z0.mpr ⟨rfl, fun j => Units.ext (by simp [expGV, GPtV.ym, LSG.ME.expU])⟩

theorem eval_coords_rename {n : ℕ} (z w : Fin m → ℂ) (lam : Fin m → ℂˣ)
    (Q : MvPolynomial (LSG.ME.Var n d1 m) ℂ) :
    eval (coords (expGV Ls ((0, 0, z, w) : TanG n d1 m)) lam) (rename mvV Q) =
      eval (LSG.ME.coords (LSG.ME.expG Ls (LSG.ME.inAb (d₀ := n) (d₁ := d1) z)) lam) Q := by
  rw [eval_rename]
  refine congrArg (fun x => eval x Q) ?_
  funext v
  cases v with
  | x i => simp [mvV, coords, expGV, LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb]
  | y j => simp [mvV, coords, expGV, GPtV.ym, LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb,
      LSG.ME.GPt.ym]
  | z j => simp [mvV, coords, expGV, GPtV.ym, LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb,
      LSG.ME.GPt.ym]
  | e k c =>
    simp only [Function.comp_apply, mvV]
    rw [coords_expGV_e, expN_base]
    simp [LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb]
    rfl

/-- **The base part**: a vector `(0, 0, z, w)` of `exp⁻¹(grp)` has `N z ∈ t + Λ` for some `N ≠ 0`.
-/
theorem base_partV (O : ObstrDataV d0 r d1 Ls M) {z w : Fin m → ℂ}
    (h : expGV Ls ((0, 0, z, w) : TanG (d0 + r) d1 m) ∈ O.grp) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ v ∈ O.S.t, ∃ l : Fin m → ℂ, (∀ k, l k ∈ (Ls k).lattice) ∧
      N • z = v + l := by
  classical
  set G0 := O.grp ∩ Z0 (d0 + r) d1 Ls
  have hs0 : IsSubgroupG G0 :=
    { zero_mem := ⟨O.grp_sub.zero_mem, Z0_isSubgroup.zero_mem⟩
      add_mem := fun g hg h hh => ⟨O.grp_sub.add_mem g hg.1 h hh.1,
        Z0_isSubgroup.add_mem g hg.2 h hh.2⟩
      neg_mem := fun g hg => ⟨O.grp_sub.neg_mem g hg.1, Z0_isSubgroup.neg_mem g hg.2⟩ }
  have hc0 : IsZClosed G0 := O.grp_closed.inter (isZClosed_zeros _)
  -- the Lie algebra of `G0`
  have hlie : ∀ v, v ∈ lieAlg Ls hs0 → v ∈ O.tan ∧ v.1 = 0 ∧ v.2.1 = 0 := by
    intro v hv
    refine ⟨(O.lie v).mp fun c => (hv c).1, ?_, ?_⟩
    · have := (mem_Z0.mp (hv 1).2).1
      simpa [expGV] using this
    · funext j
      refine exp_mul_eq_one fun c => ?_
      have := congrArg Units.val ((mem_Z0.mp (hv c).2).2 j)
      simpa [expGV, GPtV.ym, LSG.ME.expU] using this
  have hP : (lieAlg Ls hs0).map piZ = O.S.t := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact tan_map_piZ_le O ⟨v, (hlie v hv).1, rfl⟩
    · intro z' hz'
      obtain ⟨w', hw'⟩ := exists_perTanId O.S.t_ab hz'
      refine ⟨g2Incl (z', w'), fun c => ⟨?_, ?_⟩, rfl⟩
      · exact O.expGV_mem (O.tan.smul_mem c (g2Incl_perTanId_mem O hw'))
      · simp only [g2Incl_apply, Prod.smul_mk, smul_zero]
        exact expGV_mem_Z0
  -- a multiple of `g` lies in `G0⁰`
  set g := expGV Ls ((0, 0, z, w) : TanG (d0 + r) d1 m)
  have hg0 : g ∈ G0 := ⟨h, expGV_mem_Z0⟩
  obtain ⟨R, hR, hcov⟩ := finite_cosets_H0 hs0 hc0
  have hmem : ∀ k : ℕ, (k + 1) • g ∈ G0 := fun k => hs0.toAddSubgroupV.nsmul_mem hg0 (k + 1)
  choose f hfR hf using fun k : ℕ => Set.mem_iUnion₂.mp (hcov (hmem k))
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R.card + 1)) (t := R) (f := f) (by simp) (fun k _ => hfR k)
  have hs00 := H0_isSubgroup (Ls := Ls) hs0
  set N₁ : ℤ := (a : ℤ) - b
  have hN₁ : N₁ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have hN₁g : N₁ • g ∈ H0 Ls hs0 := by
    have e1 := mem_gtransl.mp (hf a)
    have e2 := mem_gtransl.mp (hf b)
    rw [hfab] at e1
    have := hs00.toAddSubgroupV.sub_mem e1 e2
    have e : N₁ • g = ((a + 1) • g - f b) - ((b + 1) • g - f b) := by
      rw [sub_sub_sub_cancel_right, ← natCast_zsmul, ← natCast_zsmul,
        show N₁ = ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) by push_cast; simp only [N₁]; ring,
        sub_zsmul, sub_eq_add_neg]
    rw [e]; exact this
  have hgN : N₁ • g = expGV Ls ((0, 0, N₁ • z, N₁ • w) : TanG (d0 + r) d1 m) := by
    rw [show g = expGVHom Ls ((0, 0, z, w) : TanG (d0 + r) d1 m) from rfl, ← map_zsmul]
    simp
  -- `exp_G (inAb (N₁ z)) ∈ B`
  have hB : LSG.ME.expG Ls (LSG.ME.inAb (d₀ := d0 + r) (d₁ := d1) (N₁ • z)) ∈
      zclB (d₀ := d0 + r) (d₁ := d1) Ls O.S.t := by
    intro Q hQ lam
    rw [← eval_coords_rename (N₁ • z) (N₁ • w) lam Q, ← hgN]
    refine mem_vanish.mp ?_ _ hN₁g lam
    rw [H0, vanish_zcl]
    refine mem_vanish.mpr ?_
    rintro _ ⟨v, hv, rfl⟩ lam'
    obtain ⟨hvT, hv1, hv2⟩ := hlie v hv
    have hv' : v = ((0, 0, v.2.2.1, v.2.2.2) : TanG (d0 + r) d1 m) := by
      ext <;> simp [hv1, hv2]
    rw [hv', eval_coords_rename]
    refine LSG.ME.mem_vanish.mp hQ _ ⟨_, ⟨v.2.2.1, ?_, rfl⟩, rfl⟩ lam'
    rw [← hP]; exact ⟨v, hv, rfl⟩
  -- the abelian finiteness for `B`
  have heq := lieAlg_zclB_eq hs0 hc0
  rw [hP] at heq
  obtain ⟨t', -, ht', F, -, hF⟩ :=
    LSG.ME.exists_abelianTangent_Htil (zclB_isSubgroup (d₀ := d0 + r) (d₁ := d1) (Ls := Ls) O.S.t)
      (zclB_closed O.S.t)
  have htt : ∀ x, x ∈ t' ↔ x ∈ O.S.t := by
    intro x
    rw [ht', ← heq, Submodule.mem_map]
    constructor
    · rintro ⟨x', hx', hxx⟩; rwa [← LSG.ME.inAbL_injective hxx]
    · intro hx; exact ⟨x, hx, rfl⟩
  have hBk : ∀ k : ℕ, LSG.ME.inAb (d₀ := d0 + r) (d₁ := d1) ((k + 1 : ℕ) • (N₁ • z)) ∈
      LSG.ME.Htil Ls (zclB_isSubgroup (d₀ := d0 + r) (d₁ := d1) (Ls := Ls) O.S.t) := by
    intro k
    have e : LSG.ME.inAb (d₀ := d0 + r) (d₁ := d1) ((k + 1 : ℕ) • (N₁ • z)) =
        (k + 1 : ℕ) • LSG.ME.inAb (N₁ • z) := by simp [LSG.ME.inAb]
    rw [e]
    exact (LSG.ME.Htil Ls _).nsmul_mem (LSG.ME.mem_Htil.mpr hB) _
  choose f' hf'F v hv l hl hdec using fun k : ℕ => hF _ (hBk k)
  obtain ⟨a', ha', b', hb', hab', hfab'⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (F.card + 1)) (t := F) (f := f') (by simp) (fun k _ => hf'F k)
  refine ⟨((a' : ℤ) - b') * N₁, mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hab')) hN₁,
    v a' - v b', O.S.t.sub_mem ((htt _).mp (hv a')) ((htt _).mp (hv b')), l a' - l b',
    fun j => (Ls j).lattice.sub_mem (hl a' j) (hl b' j), ?_⟩
  have e1 := hdec a'
  have e2 := hdec b'
  rw [hfab'] at e1
  have : (((a' : ℤ) - b') * N₁) • z =
      ((a' + 1 : ℕ) • (N₁ • z)) - ((b' + 1 : ℕ) • (N₁ • z)) := by
    rw [mul_smul, sub_smul]; simp [add_smul]
  rw [this, e1, e2]; abel

/-! ### `exp⁻¹(grp) ⊆ span_ℚ (T̃′ + Ω̃)` -/

/-- `T̃′ + Ω̃` as an additive subgroup. -/
def tanPerV (O : ObstrDataV d0 r d1 Ls M) : AddSubgroup (TanG (d0 + r) d1 m) :=
  O.tan.toAddSubgroup ⊔ PerV Ls 1

theorem htilV_le_span (O : ObstrDataV d0 r d1 Ls M) {u : TanG (d0 + r) d1 m}
    (hu : expGV Ls u ∈ O.grp) :
    u ∈ Submodule.span ℚ (tanPerV O : Set (TanG (d0 + r) d1 m)) := by
  set Q := Submodule.span ℚ (tanPerV O : Set (TanG (d0 + r) d1 m))
  have htan : ∀ w ∈ O.tan, w ∈ Q := fun w hw =>
    Submodule.subset_span (AddSubgroup.mem_sup_left (show w ∈ O.tan.toAddSubgroup from hw))
  have hper : ∀ w ∈ PerV Ls 1, w ∈ Q := fun w hw =>
    Submodule.subset_span (AddSubgroup.mem_sup_right hw)
  have hHt : ∀ w ∈ O.tan, expGV Ls w ∈ O.grp := fun w hw => O.expGV_mem hw
  have hHp : ∀ w ∈ PerV Ls 1, expGV Ls w ∈ O.grp := fun w hw => by
    rw [(expGV_eq_zero_iff Ls w).mpr hw]; exact O.grp_sub.zero_mem
  have hsub : ∀ a b, expGV Ls a ∈ O.grp → expGV Ls b ∈ O.grp → expGV Ls (a - b) ∈ O.grp :=
    fun a b ha hb => by
      rw [show expGV Ls (a - b) = expGVHom Ls (a - b) from rfl, map_sub]
      exact O.grp_sub.toAddSubgroupV.sub_mem ha hb
  have hzs : ∀ (k : ℤ) a, expGV Ls a ∈ O.grp → expGV Ls (k • a) ∈ O.grp := fun k a ha => by
    rw [show expGV Ls (k • a) = expGVHom Ls (k • a) from rfl, map_zsmul]
    exact O.grp_sub.toAddSubgroupV.zsmul_mem ha k
  -- additive part
  obtain ⟨va, hva, hva1⟩ := fst_mem_tanV O hu
  set u₁ := u - va
  have hu₁ : expGV Ls u₁ ∈ O.grp := hsub _ _ hu (hHt _ hva)
  have hva1' : va.1 = u.1 := hva1
  have hu₁1 : u₁.1 = 0 := by simp [u₁, hva1']
  -- toric part
  obtain ⟨q, hq⟩ := exists_rat_torus O.S.U u₁.2.1 fun φ hφ => by
    have h1 := chr_eq_one_of_mem_grpV O hu₁ φ hφ
    rw [← h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [GPtV.ym, expGV, LSG.ME.expU, toMul_ofMul, Units.val_mk0]
    rw [← Complex.exp_int_mul]
  set vt : TanG (d0 + r) d1 m := torIncl (fun j => u₁.2.1 j - 2 * Real.pi * Complex.I * q j)
  have hvt : vt ∈ O.tan := Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, hq, rfl⟩)
  obtain ⟨N, hN, zN, hzN⟩ := StrongSix.Thm1.exists_common_den q
  set wP : TanG (d0 + r) d1 m := (0, fun j => 2 * Real.pi * Complex.I * q j, 0, 0)
  have hNwP : (N : ℤ) • wP ∈ PerV Ls 1 := by
    refine ⟨by simp [wP], fun j => ⟨zN j, ?_⟩, fun j => by simp [wP], ?_⟩
    · change ((N : ℕ) : ℤ) • (2 * Real.pi * Complex.I * (q j : ℂ)) = _
      have : (zN j : ℂ) = (N : ℂ) * q j := by exact_mod_cast hzN j
      rw [zsmul_eq_mul, this]; push_cast; ring
    · simp only [wP, Matrix.one_mulVec]
      funext j
      simp [etaV, LSG.Weierstrass.eta_zero]
  have hwP : wP ∈ Q := mem_span_of_zsmul (n := N) (by exact_mod_cast hN) (hper _ hNwP)
  set u₂ := u₁ - vt - wP
  have hu₂1 : u₂.1 = 0 := by simp [u₂, hu₁1, vt, wP]
  have hu₂2 : u₂.2.1 = 0 := by
    funext j; simp [u₂, vt, wP]
  have hNu₂ : expGV Ls ((N : ℤ) • u₂) ∈ O.grp := by
    rw [show (N : ℤ) • u₂ = (N : ℤ) • u₁ - (N : ℤ) • vt - (N : ℤ) • wP by
      simp only [u₂, smul_sub]]
    exact hsub _ _ (hsub _ _ (hzs _ _ hu₁) (hzs _ _ (hHt _ hvt))) (hHp _ hNwP)
  have hNu₂' : (N : ℤ) • u₂ =
      ((0, 0, (N : ℤ) • u₂.2.2.1, (N : ℤ) • u₂.2.2.2) : TanG (d0 + r) d1 m) := by
    ext <;> simp [hu₂1, hu₂2]
  rw [hNu₂'] at hNu₂
  -- base part
  obtain ⟨N', hN', v, hv, l, hl, hdec⟩ := base_partV O hNu₂
  obtain ⟨wv, hwv⟩ := exists_perTanId O.S.t_ab hv
  set pl : TanG (d0 + r) d1 m := (0, 0, l, etaV Ls l)
  have hpl : pl ∈ PerV Ls 1 := ⟨rfl, fun j => ⟨0, by simp [pl]⟩, hl, by simp [pl]⟩
  set u₃ := N' • ((N : ℤ) • u₂) - g2Incl (v, wv) - pl
  have hu₃ : u₃ = ((0, 0, 0, u₃.2.2.2) : TanG (d0 + r) d1 m) := by
    have hz : (N' • ((N : ℤ) • u₂)).2.2.1 = v + l := by
      rw [hNu₂']; simpa using hdec
    ext
    · simp [u₃, pl, hu₂1]
    · simp [u₃, pl, hu₂2]
    · simp only [u₃, pl, Prod.snd_sub, Prod.fst_sub, hz, g2Incl_apply]
      simp
    · rfl
  have hu₃H : expGV Ls u₃ ∈ O.grp :=
    hsub _ _ (hsub _ _ (hzs _ _ (by rw [hNu₂']; exact hNu₂)) (hHt _ (g2Incl_perTanId_mem O hwv)))
      (hHp _ hpl)
  have hu₃T : u₃ ∈ O.tan := by
    rw [hu₃] at hu₃H ⊢
    have := lin_mem_lieAlg_of_Htil O.grp_sub O.grp_closed (a := 0) (w := u₃.2.2.2)
      (mem_Htil.mpr hu₃H)
    exact (O.lie _).mp this
  have hu₂Q : u₂ ∈ Q := by
    refine mem_span_of_zsmul (n := N' * N) (mul_ne_zero hN' (by exact_mod_cast hN)) ?_
    have e : (N' * (N : ℤ)) • u₂ = u₃ + g2Incl (v, wv) + pl := by
      simp only [u₃, mul_smul]; abel
    rw [e]
    exact Q.add_mem (Q.add_mem (htan _ hu₃T) (htan _ (g2Incl_perTanId_mem O hwv))) (hper _ hpl)
  have e : u = va + vt + wP + u₂ := by simp only [u₂, u₁]; abel
  rw [e]
  exact Q.add_mem (Q.add_mem (Q.add_mem (htan _ hva) (htan _ hvt)) hwP) hu₂Q

/-! ### On `G` -/

/-- `T′ = pushT(T̃′)`, the tangent space of the obstruction in `G`. -/
def tanG (O : ObstrDataV d0 r d1 Ls M) : Submodule ℂ (TanV d0 d1 m r) :=
  O.tan.map (pushT (d0 := d0) (d1 := d1) M)

theorem pushT_per {p : TanG (d0 + r) d1 m} (hp : p ∈ PerV Ls 1) :
    pushT (d0 := d0) (d1 := d1) M p ∈ PerV Ls M := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨funext fun i => by simp [h1], h2, h3, ?_⟩
  funext i
  simp only [pushT_apply, Pi.add_apply, h1, h4, Matrix.one_mulVec, Pi.zero_apply, zero_add]

/-- **`exp⁻¹(grp) ⊆ span_ℚ (T′ + Ω)` on `G`.** -/
theorem htilG_le_span (O : ObstrDataV d0 r d1 Ls M) {u : TanV d0 d1 m r}
    (hu : expGV Ls (liftT u) ∈ O.grp) :
    u ∈ Submodule.span ℚ
      (((tanG O).toAddSubgroup ⊔ PerV Ls M : AddSubgroup (TanV d0 d1 m r)) :
        Set (TanV d0 d1 m r)) := by
  have h := htilV_le_span O hu
  set f : TanG (d0 + r) d1 m →ₗ[ℚ] TanV d0 d1 m r :=
    (pushT (d0 := d0) (d1 := d1) M).restrictScalars ℚ
  have hf : f (liftT u) = u := pushT_liftT M u
  rw [← hf]
  have hmap := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hx
  change f (y + z) ∈ _
  rw [map_add]
  exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (show f y ∈ (tanG O) from ⟨y, hy, rfl⟩))
    (AddSubgroup.mem_sup_right (pushT_per hz))

/-! ### Pairwise inequivalent grid points (abstract version) -/

/-- **Pairwise inequivalent grid points.** -/
theorem exists_inequiv_grid_gen {E G : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup G]
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

end LSG.W88
