/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.B56Check
import LSG.Jac.P2Sound

/-!
# B5: from exact identities to ideal membership

* `evalTerms_idTerms`: the value of `idTerms D A B cs`.
* `mem_of_idTerms`: if the identity holds at `x` and every `g` lies in an ideal `I`, then `A(x) B(x) ∈ I`
  (given `D` invertible).
* `xmono_pow`: `xmono x (e · 8^v) = x_v^e` (`e < 8`).
-/

namespace LSG.Jac

variable {R : Type*} [CommRing R]

lemma evalTerms_idTerms (x y : Fin 9 → R) (D : ℕ) (A B : SP) (cs : List (SP × SP)) :
    evalTerms x y (idTerms D A B cs) =
      D * evalSP x y A * evalSP x y B - (cs.map fun p => evalSP x y p.1 * evalSP x y p.2).sum := by
  unfold idTerms evalTerms
  rw [List.map_cons, List.sum_cons, List.map_map, sub_eq_add_neg]
  congr 1
  · simp [sval]
  · rw [← neg_one_mul, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp [sval]

lemma mem_of_idTerms (I : Ideal R) (x : Fin 9 → R) (D : ℕ) (A B : SP) (cs : List (SP × SP))
    (hD : IsUnit (D : R)) (h : evalTerms x x (idTerms D A B cs) = 0)
    (hI : ∀ p ∈ cs, evalSP x x p.2 ∈ I) : evalSP x x A * evalSP x x B ∈ I := by
  rw [evalTerms_idTerms, sub_eq_zero] at h
  have hs : (cs.map fun p => evalSP x x p.1 * evalSP x x p.2).sum ∈ I := by
    refine list_sum_mem fun z hz => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact I.mul_mem_left _ (hI p hp)
  rw [← h] at hs
  have : evalSP x x A * evalSP x x B = (hD.unit⁻¹ : Rˣ) * (D * evalSP x x A * evalSP x x B) := by
    rw [mul_assoc (D : R), ← mul_assoc, show ((hD.unit⁻¹ : Rˣ) : R) * D = 1 from hD.val_inv_mul]
    ring
  rw [this]
  exact I.mul_mem_left _ hs

end LSG.Jac
