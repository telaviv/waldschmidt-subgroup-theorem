/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupClass
import LSG.MEB.SubgroupHtil

/-!
# The analytic preimage of `H⁰` (M2.5 β′): the field `ObstrDataGV.htil`

Port of W88's `Sec7VCount.htilV_le_span` (with an explicit multiple, as `LSG.MEB.htil_of_zcl`). For a
Zariski-closed subgroup `H` with `T = lieAlg H` and `G′ = H⁰ = zcl (exp T)`:

* **`fst_mem_of_H0`**: the `G_a` part of `G′` lies in `pr_A(T)` (linear forms);
* **`chr_eq_one_of_H0`**: characters in `UOf H` are trivial on `G′`;
* **`base_part`**: a vector `(0, 0, z, w)` of `exp⁻¹(G′)` has `N z ∈ t + Λ` for some `N ≠ 0`: through
  `G₀ = G′ ∩ {x = 0, y = 1}`, its finitely many cosets of `G₀⁰` (`finite_cosets_H0`), the base-group comparison
  `B′ = zcl_{G_b} exp(0 × 0 × t)` with Lie algebra `0 × 0 × t` (`lieAlg_zclB_eq`) and MEB's abelian finiteness
  `exists_nsmul_abB`;
* the rest is a vector of the vector group in `exp⁻¹(G′)`, hence in `T` (`lin_mem_lieAlg_of_Htil`);
* **`htil_H0`**: `exp u ∈ H⁰ ⇒ ∃ N > 0, N • u ∈ T + Ω(G̃)`.
-/

open MvPolynomial Set Module
open LSG.W88 (torusLie)

namespace LSG.MEBV

open LSG.MEB (IsRatSub perAb)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock} {H : Set (GPt d₀ d₁ B)}

theorem eval_of_mem_H0 (hH : IsSubgroupG H) {g : GPt d₀ d₁ B} (hg : g ∈ H0 hH)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : ∀ u ∈ lieAlg hH, ∀ lam, eval (coords (expG d₀ d₁ B u) lam) P = 0) (lam : Fin m → ℂˣ) :
    eval (coords g lam) P = 0 := by
  refine hg P (mem_vanish.mpr ?_) lam
  rintro _ ⟨u, hu, rfl⟩ lam'
  exact hP u hu lam'

/-- **The `G_a` part of `H⁰` lies in `pr_A(T)`.** -/
theorem fst_mem_of_H0 (hH : IsSubgroupG H) {g : GPt d₀ d₁ B} (hg : g ∈ H0 hH) :
    g.1 ∈ (lieAlg hH).map (prA (d₀ := d₀) (d₁ := d₁) (B := B)) := by
  by_contra hn
  obtain ⟨f, hf, hfh⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hf0 : ∀ a ∈ (lieAlg hH).map (prA (d₀ := d₀) (d₁ := d₁) (B := B)), f a = 0 := fun a ha => by
    have : f a ∈ ((lieAlg hH).map prA).map f := ⟨a, ha, rfl⟩
    rw [hfh] at this; exact this
  set P : MvPolynomial (Var d₀ d₁ B) ℂ := ∑ i, C (f (Pi.single i 1)) * X (Var.x i)
  have hev : ∀ (h : GPt d₀ d₁ B) lam, eval (coords h lam) P = f h.1 := by
    intro h lam
    simp only [P, map_sum, map_mul, eval_C, eval_X, coords_x]
    conv_rhs => rw [pi_eq_sum_univ h.1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  apply hf
  rw [← hev g 1]
  refine eval_of_mem_H0 hH hg (fun u hu lam => ?_) 1
  rw [hev]
  exact hf0 _ ⟨u, hu, rfl⟩

/-- **Characters in `UOf H` are trivial on `H⁰`.** -/
theorem chr_eq_one_of_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) {g : GPt d₀ d₁ B} (hg : g ∈ H0 hH)
    (φ : Fin d₁ → ℤ) (hφ : (fun j => (φ j : ℚ)) ∈ UOf hH) :
    ∏ j, ((g.ym j : ℂˣ) : ℂ) ^ φ j = 1 := by
  set P : MvPolynomial (Var d₀ d₁ B) ℂ :=
    (∏ j, X (Var.y j) ^ (φ j).toNat * X (Var.z j) ^ (-φ j).toNat) - 1
  have hev : ∀ (h : GPt d₀ d₁ B) lam,
      eval (coords h lam) P = ∏ j, ((h.ym j : ℂˣ) : ℂ) ^ φ j - 1 := by
    intro h lam
    simp only [P, map_sub, map_prod, map_mul, map_pow, eval_X, map_one, coords_y, coords_z,
      LSG.W88.coe_pow_toNat_mul]
  have h0 := eval_of_mem_H0 hH hg (P := P) (fun u hu lam => ?_) 1
  · rw [hev] at h0; exact sub_eq_zero.mp h0
  · rw [hev, sub_eq_zero]
    have hU := torus_mem hH hc hu _ hφ
    have : ∏ j, (((expG d₀ d₁ B u).ym j : ℂˣ) : ℂ) ^ φ j = Complex.exp (∑ j, (φ j : ℂ) * u.2.1 j) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [GPt.ym, expG_apply, expGf, expU, toMul_ofMul, Units.val_mk0]
      rw [← Complex.exp_int_mul]
    rw [this]
    have hU' : ∑ j, (φ j : ℂ) * u.2.1 j = 0 := by simpa using hU
    rw [hU', Complex.exp_zero]

/-! ### The base part -/

variable (d₀ d₁ B) in
/-- `{x = 0, y = 1}`. -/
def Z0 : Set (GPt d₀ d₁ B) := {g | g.1 = 0 ∧ ∀ j, g.ym j = 1}

theorem Z0_isSubgroup : IsSubgroupG (Z0 d₀ d₁ B) where
  zero_mem := ⟨rfl, fun _ => rfl⟩
  add_mem g hg h hh := ⟨by simp [hg.1, hh.1], fun j => by simp [hg.2 j, hh.2 j]⟩
  neg_mem g hg := ⟨by simp [hg.1], fun j => by simp [hg.2 j]⟩

theorem isZClosed_Z0 : IsZClosed (Z0 d₀ d₁ B) := by
  refine ⟨Set.range (fun i => (X (Var.x i) : MvPolynomial (Var d₀ d₁ B) ℂ)) ∪
    Set.range (fun j => (X (Var.y j) : MvPolynomial (Var d₀ d₁ B) ℂ) - 1), ?_⟩
  ext g
  simp only [Z0, mem_setOf_eq, zeros, mem_union, mem_range]
  constructor
  · rintro ⟨h1, h2⟩ P hP lam
    rcases hP with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp [h1]
    · simp [h2 j]
  · intro h
    refine ⟨funext fun i => ?_, fun j => Units.ext ?_⟩
    · simpa using h _ (Or.inl ⟨i, rfl⟩) 1
    · have := h _ (Or.inr ⟨j, rfl⟩) 1
      simpa [sub_eq_zero] using this

theorem expG_mem_Z0 {z : ∀ k, Fin (B k).g → ℂ} {w : Fin m → ℂ} :
    expG d₀ d₁ B ((0, 0, z, w) : Tan d₀ d₁ B) ∈ Z0 d₀ d₁ B :=
  ⟨rfl, fun j => Units.ext (by simp [GPt.ym, expG_apply, expGf, expU])⟩

/-- **The base part.** -/
theorem base_part (hH : IsSubgroupG H) (hc : IsZClosed H) {z : ∀ k, Fin (B k).g → ℂ} {w : Fin m → ℂ}
    (h : expG d₀ d₁ B ((0, 0, z, w) : Tan d₀ d₁ B) ∈ H0 hH) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ v ∈ tOf hH, ∃ l ∈ perBase B, N • z = v + l := by
  classical
  set G' := H0 hH
  have hG' := H0_isSubgroup hH
  have hG'c := isZClosed_H0 hH
  set G0 := G' ∩ Z0 d₀ d₁ B
  have hs0 : IsSubgroupG G0 :=
    { zero_mem := ⟨hG'.zero_mem, Z0_isSubgroup.zero_mem⟩
      add_mem := fun g hg h hh => ⟨hG'.add_mem g hg.1 h hh.1, Z0_isSubgroup.add_mem g hg.2 h hh.2⟩
      neg_mem := fun g hg => ⟨hG'.neg_mem g hg.1, Z0_isSubgroup.neg_mem g hg.2⟩ }
  have hc0 : IsZClosed G0 := hG'c.inter isZClosed_Z0
  have hlieG' : lieAlg hG' = lieAlg hH := lieAlg_H0 hH hc
  -- the Lie algebra of `G0`
  have hlie : ∀ v, v ∈ lieAlg hs0 → v ∈ lieAlg hH ∧ v.1 = 0 ∧ v.2.1 = 0 := by
    intro v hv
    refine ⟨hlieG' ▸ fun c => (hv c).1, ?_, ?_⟩
    · simpa [expG_apply, expGf] using (hv 1).2.1
    · funext j
      refine LSG.ME.eq_zero_of_forall_exp fun c => ?_
      have := congrArg Units.val ((hv c).2.2 j)
      simpa [expG_apply, expGf, GPt.ym, expU] using this
  have hP : (lieAlg hs0).map piB = tOf hH := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, (hlie v hv).1, rfl⟩
    · intro z' hz'
      obtain ⟨w', hw'⟩ := exists_perTanId (isRatSub_tOf hH hc) hz'
      have hmem : (g2Incl (z', w') : Tan d₀ d₁ B) ∈ lieAlg hH :=
        perTanId_map_le hH hc (Submodule.mem_map.mpr ⟨(z', w'), hw', rfl⟩)
      refine ⟨g2Incl (z', w'), fun c => ⟨?_, ?_⟩, rfl⟩
      · exact expG_mem_H0 hH ((lieAlg hH).smul_mem c hmem)
      · change expG d₀ d₁ B (c • ((0, 0, z', w') : Tan d₀ d₁ B)) ∈ _
        simpa using (expG_mem_Z0 (z := c • z') (w := c • w'))
  -- a multiple of `g` lies in `G0⁰`
  set g := expG d₀ d₁ B ((0, 0, z, w) : Tan d₀ d₁ B)
  have hg0 : g ∈ G0 := ⟨h, expG_mem_Z0⟩
  obtain ⟨R, -, hcov⟩ := finite_cosets_H0 hs0 hc0
  have hs00 := H0_isSubgroup hs0
  have hmem : ∀ k : ℕ, (k + 1) • g ∈ G0 := fun k => by
    rw [← map_nsmul]
    have : ((k + 1) • ((0, 0, z, w) : Tan d₀ d₁ B)) ∈ Htil hs0 := (Htil hs0).nsmul_mem hg0 _
    exact this
  choose f hfR hf using fun k : ℕ => Set.mem_iUnion₂.mp (hcov (hmem k))
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R.card + 1)) (t := R) (f := f) (by simp) (fun k _ => hfR k)
  set N₁ : ℤ := (a : ℤ) - b
  have hN₁ : N₁ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have hgN : N₁ • g = expG d₀ d₁ B ((0, 0, N₁ • z, N₁ • w) : Tan d₀ d₁ B) := by
    rw [← map_zsmul]; congr 1; ext <;> simp
  have hN₁g : expG d₀ d₁ B ((0, 0, N₁ • z, N₁ • w) : Tan d₀ d₁ B) ∈ H0 hs0 := by
    rw [← hgN]
    have e1 := mem_gtransl.mp (hf a)
    have e2 := mem_gtransl.mp (hf b)
    rw [hfab] at e1
    have hsub : (a + 1) • g - f b - ((b + 1) • g - f b) ∈ H0 hs0 := by
      have := hs00.add_mem _ e1 _ (hs00.neg_mem _ e2)
      simpa [sub_eq_add_neg] using this
    have e : N₁ • g = (a + 1) • g - f b - ((b + 1) • g - f b) := by
      rw [sub_sub_sub_cancel_right, show N₁ = ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) by
        simp only [N₁]; push_cast; ring, sub_smul, natCast_zsmul, natCast_zsmul]
    rw [e]; exact hsub
  -- the base-group comparison
  set PA := ((lieAlg hs0).map piB).map (LSG.MEB.inAbL (d₀ := d₀) (d₁ := d₁) (B := baseB B))
  have hB := LSG.MEB.zcl_isSubgroup (LSG.MEB.isSubgroupG_expG_image PA)
  have hBc : LSG.MEB.IsZClosed (LSG.MEB.zcl (LSG.MEB.expG d₀ d₁ (baseB B) '' (PA : Set _))) :=
    LSG.MEB.isZClosed_zcl _
  have heq := lieAlg_zclB_eq hs0 hc0
  have ht : ∀ x, LSG.MEB.inAbL (d₀ := d₀) (d₁ := d₁) x ∈ LSG.MEB.lieAlg hB ↔ x ∈ tOf hH := by
    intro x
    rw [← heq, ← hP, Submodule.mem_map]
    exact ⟨fun ⟨x', hx', hxx⟩ => LSG.MEB.inAbL_injective hxx ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  have hBx : LSG.MEB.inAbL (d₀ := d₀) (d₁ := d₁) (N₁ • z) ∈ LSG.MEB.Htil hB := by
    rw [LSG.MEB.mem_Htil]
    intro Q hQ lam
    obtain ⟨μ, -, hμ⟩ := LSG.MEB.coords_eq_liftZ (LSG.MEB.inAbL (N₁ • z)) lam
    rw [hμ]
    rw [SetLike.mem_coe, LSG.MEB.mem_vanish_expG_image_iff] at hQ
    have hR : rename mvB Q ∈ vanish (H0 hs0) := by
      rw [H0, vanish_zcl, mem_vanish_expG_iff]
      intro v hv μ'
      obtain ⟨-, hv1, hv2⟩ := hlie v hv
      have := hQ _ ⟨v.2.2.1, ⟨v, hv, rfl⟩, rfl⟩ μ'
      have hfun : liftZ v μ' ∘ mvB = LSG.MEB.liftZ (LSG.MEB.inAbL v.2.2.1) μ' := by
        funext q
        rcases q with i | j | j | ⟨k, c⟩
        · simp [mvB, liftZ, LSG.MEB.liftZ, hv1]
        · simp [mvB, liftZ, LSG.MEB.liftZ, hv2]
        · simp [mvB, liftZ, LSG.MEB.liftZ, hv2]
        · simp [mvB, liftZ, LSG.MEB.liftZ, Tan.blkV]
      rw [eval_rename, hfun]
      exact this
    have := eval_liftZ_eq_zero_of_mem_vanish hR hN₁g μ
    have hfun : liftZ ((0, 0, N₁ • z, N₁ • w) : Tan d₀ d₁ B) μ ∘ mvB =
        LSG.MEB.liftZ (LSG.MEB.inAbL (N₁ • z)) μ := by
      funext q
      rcases q with i | j | j | ⟨k, c⟩
      · simp [mvB, liftZ, LSG.MEB.liftZ]
      · simp [mvB, liftZ, LSG.MEB.liftZ]
      · simp [mvB, liftZ, LSG.MEB.liftZ]
      · simp [mvB, liftZ, LSG.MEB.liftZ, Tan.blkV]
    rw [eval_rename, hfun] at this
    exact this
  obtain ⟨n, hn, v, hv, l, hl, hnx⟩ := LSG.MEB.exists_nsmul_abB hB hBc ht hBx
  exact ⟨n * N₁, mul_ne_zero hn hN₁, v, hv, l, hl, by rw [mul_smul]; exact hnx⟩

theorem natAbs_smul_mem' {E : Type*} [AddCommGroup E] (S : AddSubgroup E) {M : ℤ} {u : E}
    (h : M • u ∈ S) : M.natAbs • u ∈ S := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg M
  · simpa using h
  · simpa using S.neg_mem h

/-- **`exp⁻¹(H⁰) ⊆ (1/N)(T + Ω)`.** -/
theorem htil_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ H0 hH) :
    ∃ N : ℕ, 0 < N ∧ N • u ∈ (lieAlg hH).toAddSubgroup ⊔ PerG d₀ d₁ B := by
  set T := lieAlg hH
  set S := T.toAddSubgroup ⊔ PerG d₀ d₁ B
  have hG' := H0_isSubgroup hH
  have htan : ∀ w ∈ T, w ∈ S := fun w hw => AddSubgroup.mem_sup_left (show w ∈ T.toAddSubgroup from hw)
  have hper : ∀ w ∈ PerG d₀ d₁ B, w ∈ S := fun w hw => AddSubgroup.mem_sup_right hw
  have hHt : ∀ w ∈ T, w ∈ Htil hG' := fun w hw => expG_mem_H0 hH hw
  have hHp : ∀ w ∈ PerG d₀ d₁ B, w ∈ Htil hG' := fun w hw => PerG_le_Htil hG' hw
  -- additive part
  obtain ⟨va, hva, hva1⟩ := fst_mem_of_H0 hH hu
  set u₁ := u - va
  have hu₁ : u₁ ∈ Htil hG' := (Htil hG').sub_mem hu (hHt _ hva)
  have hu₁1 : u₁.1 = 0 := by
    have : va.1 = u.1 := hva1
    simp [u₁, this]
  -- toric part
  obtain ⟨q, hq⟩ := LSG.W88.exists_rat_torus (UOf hH) u₁.2.1 fun φ hφ => by
    have h1 := chr_eq_one_of_H0 hH hc hu₁ φ hφ
    rw [← h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [GPt.ym, expG_apply, expGf, expU, toMul_ofMul, Units.val_mk0]
    rw [← Complex.exp_int_mul]
  set vt : Tan d₀ d₁ B := torIncl (fun j => u₁.2.1 j - 2 * Real.pi * Complex.I * q j)
  have hvt : vt ∈ T := torIncl_mem hH hc hq
  obtain ⟨N, hN, zN, hzN⟩ := StrongSix.Thm1.exists_common_den q
  set wP : Tan d₀ d₁ B := (0, fun j => 2 * Real.pi * Complex.I * q j, 0, 0)
  have hNwP : (N : ℤ) • wP ∈ PerG d₀ d₁ B := by
    refine ⟨by simp [wP], fun j => ⟨zN j, ?_⟩, fun k => ?_⟩
    · change ((N : ℕ) : ℤ) • (2 * Real.pi * Complex.I * (q j : ℂ)) = _
      have : (zN j : ℂ) = (N : ℂ) * q j := by exact_mod_cast hzN j
      rw [zsmul_eq_mul, this]; push_cast; ring
    · refine ⟨by simpa [wP, Tan.blkV] using (B k).base.per.zero_mem, ?_⟩
      simp [wP, Tan.blkV, (B k).η_zero]
  set u₂ := u₁ - vt - wP
  have hu₂1 : u₂.1 = 0 := by simp [u₂, hu₁1, vt, wP, torIncl]
  have hu₂2 : u₂.2.1 = 0 := by funext j; simp [u₂, vt, wP, torIncl]
  have hNu₂ : (N : ℤ) • u₂ ∈ Htil hG' := by
    rw [show (N : ℤ) • u₂ = (N : ℤ) • u₁ - (N : ℤ) • vt - (N : ℤ) • wP by simp only [u₂, smul_sub]]
    exact (Htil hG').sub_mem ((Htil hG').sub_mem ((Htil hG').zsmul_mem hu₁ _)
      ((Htil hG').zsmul_mem (hHt _ hvt) _)) (hHp _ hNwP)
  have hNu₂' : (N : ℤ) • u₂ = ((0, 0, (N : ℤ) • u₂.2.2.1, (N : ℤ) • u₂.2.2.2) : Tan d₀ d₁ B) := by
    ext <;> simp [hu₂1, hu₂2]
  -- base part
  obtain ⟨N', hN', v, hv, l, hl, hdec⟩ := base_part hH hc (hNu₂' ▸ hNu₂ : _)
  obtain ⟨wv, hwv⟩ := exists_perTanId (isRatSub_tOf hH hc) hv
  have hgv : (g2Incl (v, wv) : Tan d₀ d₁ B) ∈ T :=
    perTanId_map_le hH hc (Submodule.mem_map.mpr ⟨(v, wv), hwv, rfl⟩)
  set pl : Tan d₀ d₁ B := (0, 0, l, etaB B l)
  have hpl : pl ∈ PerG d₀ d₁ B :=
    ⟨rfl, fun j => ⟨0, by simp [pl]⟩, fun k => ⟨hl k (Set.mem_univ k), rfl⟩⟩
  set u₃ := N' • ((N : ℤ) • u₂) - g2Incl (v, wv) - pl
  have hu₃ : u₃ = ((0, 0, 0, u₃.2.2.2) : Tan d₀ d₁ B) := by
    have hz : (N' • ((N : ℤ) • u₂)).2.2.1 = v + l := by
      rw [hNu₂']; simpa using hdec
    ext
    · simp [u₃, pl, hu₂1, g2Incl]
    · simp [u₃, pl, hu₂2, g2Incl]
    · simp only [u₃, pl, Prod.snd_sub, Prod.fst_sub, hz, g2Incl]
      simp
    · rfl
  have hu₃H : u₃ ∈ Htil hG' :=
    (Htil hG').sub_mem ((Htil hG').sub_mem ((Htil hG').zsmul_mem hNu₂ _) (hHt _ hgv)) (hHp _ hpl)
  have hu₃T : u₃ ∈ T := by
    rw [hu₃] at hu₃H ⊢
    have := lin_mem_lieAlg_of_Htil hG' (isZClosed_H0 hH) (a := 0) (w := u₃.2.2.2) hu₃H
    rwa [lieAlg_H0 hH hc] at this
  have hM : (N' * N : ℤ) ≠ 0 := mul_ne_zero hN' (by exact_mod_cast hN)
  have key : (N' * N : ℤ) • u = (N' * N : ℤ) • va + (N' * N : ℤ) • vt + N' • ((N : ℤ) • wP) +
      (u₃ + g2Incl (v, wv) + pl) := by
    simp only [u₃, u₂, u₁, mul_smul, smul_sub]; abel
  have hmem : (N' * N : ℤ) • u ∈ S := by
    rw [key]
    refine S.add_mem (S.add_mem (S.add_mem (htan _ (T.toAddSubgroup.zsmul_mem hva _))
      (htan _ (T.toAddSubgroup.zsmul_mem hvt _))) (hper _ ((PerG d₀ d₁ B).zsmul_mem hNwP _)))
      (S.add_mem (S.add_mem (htan _ hu₃T) (htan _ hgv)) (hper _ hpl))
  exact ⟨_, Int.natAbs_pos.mpr hM, natAbs_smul_mem' S hmem⟩

end LSG.MEBV
