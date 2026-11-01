/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupGraph
import LSG.W88.Sec7Count

/-!
# The analytic preimage of an obstruction subgroup (A4.3, β″): the field `ObstrDataB.htil`

Port of W88's `Sec7Count.htil_le_span` to abstract blocks, in the form `ObstrDataB.htil` wants (a positive multiple
lies in `T + Ω`, rather than `span_ℚ (T + Ω)`). For `G′ = zcl (exp (h₀ × U^⊥ × t))`:

* `eval_zcl_expG`; **`fst_mem_of_zcl`**: the `G_a` part of `G′` lies in `h₀`; **`chr_eq_one_of_zcl`**: characters in
  `U` are trivial on `G′`;
* **`exists_nsmul_abB`**: if `t = {z | (0, 0, z) ∈ lieAlg G′}`, every `z` with `exp(0, 0, z) ∈ G′` has a nonzero multiple
  in `t + perAb` (`LSG.Subgroups.exists_finset_cosets`: finitely many cosets);
* **`htil_of_zcl`**: `exp u ∈ G′ ⇒ ∃ N > 0, N • u ∈ T_{G′} + Ω`.
-/

open MvPolynomial Set Module
open LSG.W88 (torusLie)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

theorem eval_zcl_expG {T : Submodule ℂ (Tan d₀ d₁ B)} {g : GPt d₀ d₁ B}
    (hg : g ∈ zcl (expG d₀ d₁ B '' (T : Set (Tan d₀ d₁ B)))) {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : ∀ u ∈ T, ∀ lam, eval (coords (expG d₀ d₁ B u) lam) P = 0) (lam : Fin m → ℂˣ) :
    eval (coords g lam) P = 0 := by
  refine hg P (mem_vanish.mpr ?_) lam
  rintro _ ⟨u, hu, rfl⟩ lam'
  exact hP u hu lam'

/-- **The `G_a` part of `zcl (exp (h₀ × U^⊥ × t))` lies in `h₀`.** -/
theorem fst_mem_of_zcl {h0 : Submodule ℂ (Fin d₀ → ℂ)} {U : Submodule ℚ (Fin d₁ → ℚ)}
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {g : GPt d₀ d₁ B}
    (hg : g ∈ zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set (Tan d₀ d₁ B)))) : g.1 ∈ h0 := by
  by_contra hn
  obtain ⟨f, hf, hfh⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hf0 : ∀ a ∈ h0, f a = 0 := fun a ha => by
    have : f a ∈ h0.map f := ⟨a, ha, rfl⟩
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
  refine eval_zcl_expG hg (fun u hu lam => ?_) 1
  rw [hev]
  exact hf0 _ hu.1

/-- **Characters in `U` are trivial on `zcl (exp (h₀ × U^⊥ × t))`.** -/
theorem chr_eq_one_of_zcl {h0 : Submodule ℂ (Fin d₀ → ℂ)} {U : Submodule ℚ (Fin d₁ → ℚ)}
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {g : GPt d₀ d₁ B}
    (hg : g ∈ zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set (Tan d₀ d₁ B))))
    (φ : Fin d₁ → ℤ) (hφ : (fun j => (φ j : ℚ)) ∈ U) :
    ∏ j, ((g.ym j : ℂˣ) : ℂ) ^ φ j = 1 := by
  set P : MvPolynomial (Var d₀ d₁ B) ℂ :=
    (∏ j, X (Var.y j) ^ (φ j).toNat * X (Var.z j) ^ (-φ j).toNat) - 1
  have hev : ∀ (h : GPt d₀ d₁ B) lam,
      eval (coords h lam) P = ∏ j, ((h.ym j : ℂˣ) : ℂ) ^ φ j - 1 := by
    intro h lam
    simp only [P, map_sub, map_prod, map_mul, map_pow, eval_X, map_one, coords_y, coords_z,
      LSG.W88.coe_pow_toNat_mul]
  have h0 := eval_zcl_expG hg (P := P) (fun u hu lam => ?_) 1
  · rw [hev] at h0; exact sub_eq_zero.mp h0
  · rw [hev, sub_eq_zero]
    have hU := hu.2.1 _ hφ
    have : ∏ j, (((expG d₀ d₁ B u).ym j : ℂˣ) : ℂ) ^ φ j = Complex.exp (∑ j, (φ j : ℂ) * u.2.1 j) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [GPt.ym, expG_apply, expGf, expU, toMul_ofMul, Units.val_mk0]
      rw [← Complex.exp_int_mul]
    rw [this]
    have hU' : ∑ j, (φ j : ℂ) * u.2.1 j = 0 := by simpa using hU
    rw [hU', Complex.exp_zero]

/-- **Abelian part**: if `t` is the abelian part of `lieAlg G′`, every `x` with `exp(0, 0, x) ∈ G′` has a nonzero
multiple in `t + perAb`. -/
theorem exists_nsmul_abB {G' : Set (GPt d₀ d₁ B)} (hsub : IsSubgroupG G') (hc : IsZClosed G')
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)}
    (ht : ∀ z, inAbL (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg hsub ↔ z ∈ t)
    {x : ∀ k, Fin (B k).g → ℂ} (hx : inAbL (d₀ := d₀) (d₁ := d₁) x ∈ Htil hsub) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ v ∈ t, ∃ l ∈ perAb B, n • x = v + l := by
  classical
  let L : Submodule ℤ (∀ k, Fin (B k).g → ℂ) := (perAb B).toIntSubmodule
  haveI : DiscreteTopology L := discreteTopology_perAb
  have hspan : Submodule.span ℝ (L : Set (∀ k, Fin (B k).g → ℂ)) = ⊤ := span_perAb
  let SA : AddSubgroup (∀ k, Fin (B k).g → ℂ) :=
    (Htil hsub).comap (inAbL (d₀ := d₀) (d₁ := d₁) (B := B)).toAddMonoidHom
  have hS : IsClosed (SA : Set (∀ k, Fin (B k).g → ℂ)) :=
    (isClosed_Htil hsub hc).preimage (by fun_prop : Continuous fun z : (∀ k, Fin (B k).g → ℂ) =>
      ((0, 0, z) : Tan d₀ d₁ B))
  have hLS : (L : Set (∀ k, Fin (B k).g → ℂ)) ⊆ SA := fun ω hω =>
    Per_le_Htil hsub ⟨rfl, fun i => ⟨0, by simp⟩, fun k => hω k (Set.mem_univ k)⟩
  have hlin : ∀ z, z ∈ LSG.Subgroups.linPart SA ↔ z ∈ t := by
    intro z
    rw [← ht z, mem_lieAlg_iff_real hsub hc, LSG.Subgroups.mem_linPart]
    refine forall_congr' fun s => ?_
    change inAbL (s • z) ∈ Htil hsub ↔ _
    rw [show inAbL (s • z) = ((s : ℂ) • inAbL z : Tan d₀ d₁ B) by
      rw [← map_smul]; congr 1]
  obtain ⟨F, -, hF⟩ := LSG.Subgroups.exists_finset_cosets L SA hspan hS hLS
  have hmem : ∀ k : ℕ, (k + 1 : ℕ) • x ∈ SA := fun k => SA.nsmul_mem hx _
  choose f hfF v hv l hl hdec using fun k : ℕ => hF _ (hmem k)
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (F.card + 1)) (t := F) (f := f) (by simp) (fun k _ => hfF k)
  refine ⟨(a : ℤ) - b, sub_ne_zero.mpr (by exact_mod_cast hab), v a - v b,
    Submodule.sub_mem _ ((hlin _).mp (hv a)) ((hlin _).mp (hv b)), l a - l b,
    (perAb B).sub_mem (hl a) (hl b), ?_⟩
  have e1 := hdec a
  have e2 := hdec b
  rw [hfab] at e1
  have : ((a : ℤ) - b) • x = ((a + 1 : ℕ) • x) - ((b + 1 : ℕ) • x) := by
    rw [sub_smul]; simp [add_smul]
  rw [this, e1, e2]; abel

theorem natAbs_smul_mem {E : Type*} [AddCommGroup E] (S : AddSubgroup E) {M : ℤ} {u : E}
    (h : M • u ∈ S) : M.natAbs • u ∈ S := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg M
  · simpa using h
  · simpa using S.neg_mem h

/-- **`exp⁻¹(G′) ⊆ (1/N)(T_{G′} + Ω)`** for `G′ = zcl (exp (h₀ × U^⊥ × t))` whose Lie algebra has abelian part `t`
(W88's `htil_le_span`, with an explicit multiple). -/
theorem htil_of_zcl {h0 : Submodule ℂ (Fin d₀ → ℂ)} {U : Submodule ℚ (Fin d₁ → ℚ)}
    {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} {G' : Set (GPt d₀ d₁ B)}
    (hG : G' = zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set (Tan d₀ d₁ B)))) (hsub : IsSubgroupG G')
    (ht : ∀ z, inAbL (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg hsub ↔ z ∈ t)
    {u : Tan d₀ d₁ B} (hu : expG d₀ d₁ B u ∈ G') :
    ∃ N : ℕ, 0 < N ∧ N • u ∈ (tanOf h0 U t).toAddSubgroup ⊔ Per d₀ d₁ B := by
  set S := (tanOf h0 U t).toAddSubgroup ⊔ Per d₀ d₁ B
  have htan : ∀ w ∈ tanOf h0 U t, w ∈ S := fun w hw =>
    AddSubgroup.mem_sup_left (show w ∈ (tanOf h0 U t).toAddSubgroup from hw)
  have hper : ∀ w ∈ Per d₀ d₁ B, w ∈ S := fun w hw => AddSubgroup.mem_sup_right hw
  have hc : IsZClosed G' := hG ▸ isZClosed_zcl _
  have hg : expG d₀ d₁ B u ∈ zcl (expG d₀ d₁ B '' (tanOf h0 U t : Set (Tan d₀ d₁ B))) := hG ▸ hu
  -- `G_a`
  have ha : u.1 ∈ h0 := fst_mem_of_zcl hg
  -- `G_m`
  obtain ⟨r, hr⟩ := LSG.W88.exists_rat_torus U u.2.1 fun φ hφ => by
    have h1 := chr_eq_one_of_zcl hg φ hφ
    rw [← h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [GPt.ym, expG_apply, expGf, expU, toMul_ofMul, Units.val_mk0]
    rw [← Complex.exp_int_mul]
  obtain ⟨N, hN, z, hz⟩ := StrongSix.Thm1.exists_common_den r
  set b' : Fin d₁ → ℂ := fun j => u.2.1 j - 2 * Real.pi * Complex.I * r j
  set wL : Tan d₀ d₁ B := (u.1, b', 0) with hwLdef
  set wP : Tan d₀ d₁ B := (0, fun j => 2 * Real.pi * Complex.I * r j, 0) with hwPdef
  have hwL : wL ∈ tanOf h0 U t := ⟨ha, hr, Submodule.zero_mem _⟩
  -- `N • wP ∈ Ω`
  have hNwP : (N : ℤ) • wP ∈ Per d₀ d₁ B := by
    refine ⟨by simp [wP], fun j => ⟨z j, ?_⟩, fun k => by simp [wP, (B k).per.zero_mem]⟩
    change ((N : ℕ) : ℤ) • ((2 * Real.pi * Complex.I * (r j : ℂ))) = _
    have : (z j : ℂ) = (N : ℂ) * r j := by exact_mod_cast hz j
    rw [zsmul_eq_mul, this]; push_cast; ring
  -- the abelian remainder
  set x : ∀ k, Fin (B k).g → ℂ := u.2.2
  have hsplit : u = wL + wP + inAbL x := by
    refine Prod.ext (by simp [wL, wP]) (Prod.ext ?_ (by simp [wL, wP, x]))
    funext j; simp [wL, wP, b']
  have hNx : inAbL (d₀ := d₀) (d₁ := d₁) ((N : ℤ) • x) ∈ Htil hsub := by
    have h1 : (N : ℤ) • u ∈ Htil hsub := (Htil hsub).zsmul_mem hu _
    have h2 : (N : ℤ) • wL ∈ Htil hsub :=
      (Htil hsub).zsmul_mem (mem_Htil.mpr (hG ▸ subset_zcl _ ⟨wL, hwL, rfl⟩)) _
    have h3 : (N : ℤ) • wP ∈ Htil hsub := Per_le_Htil hsub hNwP
    have : inAbL (d₀ := d₀) (d₁ := d₁) ((N : ℤ) • x) = (N : ℤ) • u - (N : ℤ) • wL - (N : ℤ) • wP := by
      conv_rhs => rw [hsplit]
      rw [map_zsmul]
      simp only [smul_add]; abel
    rw [this]
    exact (Htil hsub).sub_mem ((Htil hsub).sub_mem h1 h2) h3
  obtain ⟨n, hn, v, hv, l, hl, hnx⟩ := exists_nsmul_abB hsub hc ht hNx
  have hM : (n * N : ℤ) ≠ 0 := mul_ne_zero hn (by exact_mod_cast hN)
  have key : (n * N : ℤ) • u = (n * N : ℤ) • wL + n • ((N : ℤ) • wP) + (inAbL v + inAbL l) := by
    have h1 : (inAbL v + inAbL l : Tan d₀ d₁ B) = n • ((N : ℤ) • inAbL x) := by
      rw [← map_add, ← hnx, map_zsmul, map_zsmul]
    rw [h1]
    conv_lhs => rw [hsplit]
    simp only [smul_add, mul_smul]
  have hmem : (n * N : ℤ) • u ∈ S := by
    rw [key]
    refine S.add_mem (S.add_mem (htan _ ((tanOf h0 U t).toAddSubgroup.zsmul_mem hwL _))
      (hper _ ((Per d₀ d₁ B).zsmul_mem hNwP _))) (S.add_mem (htan _ ?_) (hper _ ?_))
    · exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, hv⟩
    · exact ⟨rfl, fun i => ⟨0, by simp⟩, fun k => hl k (Set.mem_univ k)⟩
  exact ⟨_, Int.natAbs_pos.mpr hM, natAbs_smul_mem S hmem⟩

end LSG.MEB
