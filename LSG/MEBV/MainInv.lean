/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Chain

/-!
# Symmetries of the order hypothesis (M2.5 α; template `LSG.MEV.MainVecInv`)

For the push-out, `MultEstGV` carries a subspace `Kv ⊆ Lie G̃` of symmetries of the order hypothesis
(`OrdGtV W P n y → OrdGtV W P n (y + exp v)`). They pass to the chain and to a maximal relevant component:

* **`zeros_Lr2_add`**: the zero sets `Z(L_r)` are stable under such translations;
* **`le_stab`**: a maximal relevant component `V` (`hdim I(V) = hdim relI L`) of a stable `Z(L)` is stable under
  the connected group `exp Kv`: `exp (c v) ∈ stabG V` for all `v ∈ Kv`, `c ∈ ℂ`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- The zero sets of the chain are stable under translations preserving the order of `P`. -/
theorem zeros_Lr2_add {W : Submodule ℂ (Tan d₀ d₁ B)} {S : Finset (GPt d₀ d₁ B)}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {T : ℕ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {k : GPt d₀ d₁ B} (hk : ∀ y n, OrdGtV W P n y → OrdGtV W P n (y + k)) (r : ℕ)
    {h : GPt d₀ d₁ B} (hh : h ∈ zeros (Lr2 W S P T r : Set _)) :
    h + k ∈ zeros (Lr2 W S P T r : Set _) := by
  rw [mem_zeros_iff_le_vanish] at hh ⊢
  refine sup_le (vanish_antitone (Set.subset_univ _)) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  have hord : OrdGtV W P (r * T) (h + σ) :=
    ordGtV_of_phOp_mem_vanish hP fun w' hw' κ' hκ' c₁ c₂ =>
      hh (Ideal.mem_sup_right (Ideal.subset_span ⟨σ, hσ, w', hw', κ', hκ', c₁, c₂, rfl⟩))
  have hord' : OrdGtV W P (r * T) (h + k + σ) := by
    rw [show h + k + σ = h + σ + k by abel]
    exact hk _ _ hord
  exact phOp_mem_vanish hP hord' hw hκ c c'

theorem nsmul_mem_subgroupG {H : Set (GPt d₀ d₁ B)} (hH : IsSubgroupG H) {g : GPt d₀ d₁ B}
    (hg : g ∈ H) : ∀ n : ℕ, n • g ∈ H
  | 0 => by rw [zero_smul]; exact hH.zero_mem
  | n + 1 => by rw [succ_nsmul]; exact hH.add_mem _ (nsmul_mem_subgroupG hH hg n) _ hg

theorem expG_natCast_smul (n : ℕ) (u : Tan d₀ d₁ B) :
    expG d₀ d₁ B ((n : ℂ) • u) = n • expG d₀ d₁ B u := by
  rw [← map_nsmul, Nat.cast_smul_eq_nsmul]

/-- **A maximal relevant component is stable under a connected group of symmetries of `Z(L)`.** -/
theorem le_stab (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime)
    (hdim : (hdata blk D ℂ (vanish V)).1 = (hdata blk D ℂ (relI d₀ d₁ B L)).1)
    (hVL : V ⊆ zeros (L : Set _)) (Kv : Submodule ℂ (Tan d₀ d₁ B))
    (hK : ∀ v ∈ Kv, ∀ h ∈ zeros (L : Set (MvPolynomial (Var d₀ d₁ B) ℂ)),
      h + expG d₀ d₁ B v ∈ zeros (L : Set _)) :
    ∀ v ∈ Kv, ∀ c : ℂ, expG d₀ d₁ B (c • v) ∈ stabG V := by
  classical
  obtain ⟨R, hR⟩ := component_rel D hD hV hp hdim
  set GV := stabG V
  have hGV : IsSubgroupG GV := stabG_isSubgroup hV
  -- every `exp(v)`, `v ∈ Kv`, lies in one of the cosets
  have hcov : ∀ v ∈ Kv, ∃ a ∈ R, expG d₀ d₁ B v - a ∈ GV := by
    intro v hv
    have hmem : expG d₀ d₁ B v ∈ {h | gtransl h V ⊆ zeros (L : Set _)} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hK v hv x (hVL hx)
    have := hR hmem
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨a, ha, hm⟩ := this
    exact ⟨a, ha, mem_gtransl.mp hm⟩
  intro v hv c
  -- pigeonhole: for every `x`, some `j x` (`1 ≤ j ≤ |R|`) lies in the stabiliser
  have hpig : ∀ x : ℂ, ∃ j : ℕ, 1 ≤ j ∧ j ≤ R.card ∧ expG d₀ d₁ B (((j : ℂ) * x) • v) ∈ GV := by
    intro x
    choose! f hfR hf using fun i : ℕ => hcov (((i : ℂ) * x) • v) (Kv.smul_mem _ hv)
    have hmaps : ∀ i ∈ Finset.range (R.card + 1), f i ∈ R := fun i _ => hfR i
    obtain ⟨i, hi, i', hi', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmaps
    have hd : ∀ {i i' : ℕ}, f i = f i' → i' < i →
        expG d₀ d₁ B ((((i - i' : ℕ) : ℂ) * x) • v) ∈ GV := by
      intro i i' he hlt
      have h1 := hf i
      have h2 := hf i'
      rw [he] at h1
      have h3 := hGV.add_mem _ h1 _ (hGV.neg_mem _ h2)
      have e : expG d₀ d₁ B ((((i - i' : ℕ) : ℂ) * x) • v) =
          expG d₀ d₁ B (((i : ℂ) * x) • v) - f i' +
            -(expG d₀ d₁ B (((i' : ℂ) * x) • v) - f i') := by
        rw [Nat.cast_sub hlt.le, sub_mul, sub_smul, map_sub]; abel
      rw [e]; exact h3
    have hR' : i < R.card + 1 ∧ i' < R.card + 1 :=
      ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hi'⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i' - i, by omega, by omega, hd heq.symm hlt⟩
    · exact ⟨i - i', by omega, by omega, hd heq hlt⟩
  -- the factorial multiple
  have hfac : ∀ x : ℂ, expG d₀ d₁ B ((((R.card.factorial : ℕ) : ℂ) * x) • v) ∈ GV := by
    intro x
    obtain ⟨j, hj1, hjN, hj⟩ := hpig x
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hj1 hjN
    have := nsmul_mem_subgroupG hGV hj q
    rw [← expG_natCast_smul, smul_smul, ← mul_assoc, mul_comm (q : ℂ), ← Nat.cast_mul,
      ← hq] at this
    exact this
  have hN : ((R.card.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have := hfac (c / (R.card.factorial : ℂ))
  rwa [mul_div_cancel₀ _ hN] at this

end LSG.MEBV
