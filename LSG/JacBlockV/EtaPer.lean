/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.FibrePeriod

/-!
# M2.8 prep: the fibre period formula for every `e : ℕ`

`ThetaData.etaB_perVec` (`LSG.JacAnV.FibrePeriod`) gives `η̄(perVec e) = (3/5)(ζ^e)⁴ perB5` for `e : Fin 4`. The M2.8
bridge meets lean_mstar's generators `(j, e)` with arbitrary `e : ℕ`. Here:

* `perVec_add_five`, `perVec_four`: `perVec` is 5-periodic and `perVec 4 = −(perVec 0 + ⋯ + perVec 3)`;
* **`ThetaData.etaB_perVec_nat`**: `η̄(perVec e) = (3/5)(ζ^e)⁴ perB5` for all `e : ℕ`;
* `ThetaData.etaB_perVec_nat'`: the same, written `(3/5) ζ^{4e} perB5` (lean_mstar's `ζ^{(N−1)e}` with `N = 5`).
-/

noncomputable section

namespace LSG.JacAn

open LSG.JacAnV Beta

lemma zetaN_five_root (j : Fin 2) : IsPrimitiveRoot (zetaN 5 ^ ((j : ℕ) + 1)) 5 :=
  (zetaN_prim 5 (by norm_num)).pow_of_coprime ((j : ℕ) + 1) (by fin_cases j <;> decide)

lemma perVec_add_five (e : ℕ) : perVec (e + 5) = perVec e := by
  funext j; rw [perVec_eq, perVec_eq, pow_add, (zetaN_five_root j).pow_eq_one, mul_one]

lemma perVec_four : perVec 4 = -(perVec 0 + perVec 1 + perVec 2 + perVec 3) := by
  funext j
  simp only [Pi.neg_apply, Pi.add_apply, perVec_eq]
  have hs := (zetaN_five_root j).geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  linear_combination cJ j * hs

lemma perVec_mem_latt' (e : Fin 4) : perVec (e : ℕ) ∈ latt := AddSubgroup.subset_closure ⟨e, rfl⟩

variable {A : A1Facts} {B₁' B₂' : LocalBranch f₅ 2} {p' : ℂ × ℂ} {hp' : p' ∈ dom2 B₁' B₂'} {hx' : p'.1 ≠ p'.2}
  {G : GermRad A hp' hx'} (D : ThetaData G)

/-- **The fibre period formula for every `e`.** -/
theorem ThetaData.etaB_perVec_nat (SF : SurjFacts A) (e : ℕ) :
    D.etaB (perVec e) = 3 / 5 * (zetaN 5 ^ e) ^ 4 * perB5 := by
  have hζ5 : zetaN 5 ^ 5 = 1 := (zetaN_prim 5 (by norm_num)).pow_eq_one
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    by_cases he : e < 4
    · exact D.etaB_perVec SF ⟨e, he⟩
    by_cases h4 : e = 4
    · subst h4
      have hm : ∀ i : Fin 4, perVec (i : ℕ) ∈ latt := perVec_mem_latt'
      have h0 := D.etaB_perVec SF 0
      have h1 := D.etaB_perVec SF 1
      have h2 := D.etaB_perVec SF 2
      have h3 := D.etaB_perVec SF 3
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl] at h0 h1 h2 h3 hm
      have hm0 := hm 0
      have hm1 := hm 1
      have hm2 := hm 2
      have hm3 := hm 3
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hm0 hm1 hm2 hm3
      -- `η̄` is additive on `latt`
      have hS : D.etaB (perVec 0 + perVec 1 + perVec 2 + perVec 3) =
          D.etaB (perVec 0) + D.etaB (perVec 1) + D.etaB (perVec 2) + D.etaB (perVec 3) := by
        rw [D.etaB_add (add_mem (add_mem hm0 hm1) hm2) hm3, D.etaB_add (add_mem hm0 hm1) hm2,
          D.etaB_add hm0 hm1]
      have hsum := add_mem (add_mem (add_mem hm0 hm1) hm2) hm3
      have hneg : D.etaB (-(perVec 0 + perVec 1 + perVec 2 + perVec 3)) =
          -D.etaB (perVec 0 + perVec 1 + perVec 2 + perVec 3) := by
        have h := D.etaB_add hsum (neg_mem hsum)
        rw [add_neg_cancel] at h
        have hz : D.etaB 0 = 0 := D.etaHom.map_zero
        rw [hz] at h
        linear_combination -h
      rw [perVec_four, hneg, hS, h0, h1, h2, h3]
      have hgeo : 1 + zetaN 5 ^ 4 + (zetaN 5 ^ 4) ^ 2 + (zetaN 5 ^ 4) ^ 3 + (zetaN 5 ^ 4) ^ 4 = 0 := by
        have hs := ((zetaN_prim 5 (by norm_num)).pow_of_coprime 4 (by decide)).geom_sum_eq_zero (by norm_num)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
        linear_combination hs
      simp only [pow_zero, pow_one, one_pow]
      linear_combination (-(3 / 5 : ℂ) * perB5) * hgeo
    · obtain ⟨k, rfl⟩ : ∃ k, e = k + 5 := ⟨e - 5, by omega⟩
      rw [perVec_add_five, ih k (by omega), pow_add, hζ5, mul_one]

/-- The same, in lean_mstar's form `(3/5) ζ^{4e} perB5`. -/
theorem ThetaData.etaB_perVec_nat' (SF : SurjFacts A) (e : ℕ) :
    D.etaB (perVec e) = 3 / 5 * zetaN 5 ^ (4 * e) * perB5 := by
  rw [D.etaB_perVec_nat SF e, ← pow_mul, mul_comm e 4]

end LSG.JacAn
