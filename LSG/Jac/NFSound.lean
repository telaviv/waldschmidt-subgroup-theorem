/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerSound
import LSG.Jac.CheckerNF2

/-!
# Checking a normal-form table against the quadrics (Stage A1c)

A leaf `(μ, row)` of the normal-form table claims `δ · X^μ ≡ NF(μ) = Σ ±n X^{std s}` modulo the quadrics. The
certificate is a list of degree-2 cofactors `c_j` with `δ X^μ − NF(μ) − Σ_j c_j Q_j = 0` as polynomials. The kernel
checks this identity by Kronecker packing over the monomial *index* (`idx` field of the table leaves): every monomial
that occurs is looked up in the table, and `Σ ±w 2^{B · idx} = 0` with `Σ |w| < 2^B` (`nfEntryOK`).

* `nfEntry_sound`: one checked leaf is valid at every point where all quadrics vanish.
* `nfValid_of_check`: `nfAllOK` (all leaves, with their certificates in order) gives `NFValid` at every such point.
-/

namespace LSG.Jac

open Finset

lemma lsum_neg {R α : Type*} [CommRing R] (l : List α) (f : α → R) :
    (l.map fun a => -f a).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

lemma sval_not (n : ℕ) (s : Bool) : sval n (!s) = -sval n s := by cases s <;> simp [sval]

lemma sv_nfPack (tr : T) (B : ℕ) (L : List (ℕ × Bool × ℕ)) :
    sv (nfPack tr B L) = (L.map fun e => sval e.1 e.2.1 * 2 ^ (B * (tr.find e.2.2).idx)).sum := by
  unfold nfPack
  rw [sv_foldl _ _ (fun e => sval e.1 e.2.1 * 2 ^ (B * (tr.find e.2.2).idx)), sv_zero, zero_add]
  intro acc e; rw [sv_addS]; simp [sv, Nat.shiftLeft_eq]

section Sound

variable {R : Type*} [CommRing R]

/-- **One leaf.** -/
theorem nfEntry_sound (tr : T) (B K δ : ℕ) (stdc : List ℕ) (Qd : List (List (ℕ × ℕ × Bool)))
    (keys : List ℕ) (hkeys : ∀ l ∈ tr.leaves, keys.getD l.idx 0 = l.key) (l : Leaf)
    (cofs : List (List (ℕ × ℕ × Bool))) (h : nfEntryOK tr B K δ stdc Qd l cofs = true)
    (x : Fin 9 → R) (hQ : ∀ q ∈ Qd, evalRow x q = 0) :
    (δ : R) * xmono x l.key = evalNF x stdc l.row := by
  unfold nfEntryOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hk, hnc⟩, hB⟩, hz⟩ := h
  set L := nfTerms δ stdc Qd l.key l.row cofs with hLdef
  have hk' : ∀ e ∈ L, (tr.find e.2.2).key = e.2.2 ∧ (tr.find e.2.2).idx < K := by
    intro e he
    have := List.all_eq_true.mp hk e he
    simpa [Bool.and_eq_true] using this
  -- Kronecker
  have hsum : (L.map fun e => (sval e.1 e.2.1 : R) * xmono x e.2.2).sum = 0 := by
    have h0 := kron_zero (R := R) (L.map fun e => (sval e.1 e.2.1, (tr.find e.2.2).idx)) K B
      (by intro p hp; simp only [List.mem_map] at hp; obtain ⟨e, he, rfl⟩ := hp; exact (hk' e he).2)
      (by
        simp only [List.map_map, Function.comp_def, abs_sval]
        have := hB; zify at this
        simpa [Nat.cast_list_sum, List.map_map, Function.comp_def] using this)
      (by
        have : sv (nfPack tr B L) = 0 := by simp [sv, hz]
        rw [sv_nfPack] at this
        simpa [List.map_map, Function.comp_def] using this)
      (fun i => xmono x (keys.getD i 0))
    simp only [List.map_map, Function.comp_def] at h0
    rw [← h0]
    refine lsum_congr fun e he => ?_
    rw [hkeys _ (tr.find_mem _), (hk' e he).1]
  -- split the terms
  rw [hLdef] at hsum
  unfold nfTerms at hsum
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hsum
  have hcof : (((cofs.zip Qd).flatMap fun cq => cq.1.flatMap fun a => cq.2.map fun q =>
      (a.2.1 * q.2.1, !(a.2.2 != q.2.2), a.1 + q.1)).map fun e =>
        (sval e.1 e.2.1 : R) * xmono x e.2.2).sum = 0 := by
    rw [map_flatMap_sum]
    refine List.sum_eq_zero fun v hv => ?_
    simp only [List.mem_map] at hv
    obtain ⟨cq, hcq, rfl⟩ := hv
    have hq : evalRow x cq.2 = 0 := hQ _ (List.of_mem_zip hcq).2
    have hnc' := List.all_eq_true.mp hnc cq hcq
    have : (evalRow x cq.1) * evalRow x cq.2 = ((cq.1.flatMap fun a => cq.2.map fun q =>
        (a.2.1 * q.2.1, !(a.2.2 != q.2.2), a.1 + q.1)).map fun e =>
          (sval e.1 e.2.1 : R) * xmono x e.2.2).sum * (-1) := by
      rw [map_flatMap_sum, evalRow, evalRow, lsum_mul_lsum, lsum_mul_right]
      refine lsum_congr fun a ha => ?_
      rw [List.map_map, lsum_mul_right]
      refine lsum_congr fun q hq' => ?_
      have hn := List.all_eq_true.mp (List.all_eq_true.mp hnc' a ha) q hq'
      simp only [Function.comp_apply, sval_not, sval_mul_bne, xmono_add x hn]
      push_cast; ring
    rw [hq, mul_zero] at this
    linear_combination this
  rw [hcof, add_zero] at hsum
  unfold evalNF
  have e1 : (sval δ false : R) = δ := by simp [sval]
  rw [e1] at hsum
  have e2 : (l.row.map fun t => (sval t.2.1 t.2.2 : R) * xmono x (stdc.getD t.1 0)) =
      ((l.row.map fun t => (t.2.1, !t.2.2, stdc.getD t.1 0)).map fun e =>
        -((sval e.1 e.2.1 : R) * xmono x e.2.2)) := by
    simp [List.map_map, Function.comp_def, sval_not]
  rw [e2]
  simp only [Int.cast_neg, neg_mul, lsum_neg] at hsum ⊢
  linear_combination hsum

/-- **The whole table.** -/
theorem nfValid_of_check (tr : T) (B K δ : ℕ) (stdc : List ℕ) (Qd : List (List (ℕ × ℕ × Bool)))
    (keys : List ℕ) (cert : List (ℕ × List (List (ℕ × ℕ × Bool))))
    (h : nfAllOK tr B K δ stdc Qd keys cert = true) (x : Fin 9 → R) (hQ : ∀ q ∈ Qd, evalRow x q = 0) :
    NFValid tr stdc δ x := by
  unfold nfAllOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hk, hlen⟩, hall⟩ := h
  have hkeys : ∀ l ∈ tr.leaves, keys.getD l.idx 0 = l.key := by
    intro l hl; simpa using List.all_eq_true.mp hk l hl
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
  have hi' : i < cert.length := hlen ▸ hi
  have hmem : (tr.leaves[i], cert[i]) ∈ tr.leaves.zip cert := by
    have : i < (tr.leaves.zip cert).length := by simp [List.length_zip, hi, hi']
    have h2 := List.getElem_mem this
    simpa [List.getElem_zip] using h2
  have := List.all_eq_true.mp hall _ hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact nfEntry_sound tr B K δ stdc Qd keys hkeys _ _ this.2 x hQ

/-- **A chunk of leaves.** -/
theorem nfRange_sound (tr : T) (B K δ : ℕ) (stdc : List ℕ) (Qd : List (List (ℕ × ℕ × Bool)))
    (keys : List ℕ) (hk : keysOK tr keys = true) (a : ℕ) (cert : List (ℕ × List (List (ℕ × ℕ × Bool))))
    (h : nfRangeOK tr B K δ stdc Qd a cert = true) (x : Fin 9 → R) (hQ : ∀ q ∈ Qd, evalRow x q = 0)
    (i : ℕ) (hi : i < tr.leaves.length) (hai : a ≤ i) (hia : i < a + cert.length) :
    (δ : R) * xmono x tr.leaves[i].key = evalNF x stdc tr.leaves[i].row := by
  unfold nfRangeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hall⟩ := h
  have hkeys : ∀ l ∈ tr.leaves, keys.getD l.idx 0 = l.key := by
    intro l hl; unfold keysOK at hk; simpa using List.all_eq_true.mp hk l hl
  have hj : i - a < ((tr.leaves.drop a).zip cert).length := by
    simp [List.length_zip, List.length_drop]; omega
  have hmem := List.getElem_mem hj
  simp only [List.getElem_zip, List.getElem_drop] at hmem
  have := List.all_eq_true.mp hall _ hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  have e : a + (i - a) = i := by omega
  simp only [e] at this
  exact nfEntry_sound tr B K δ stdc Qd keys hkeys _ _ this.2 x hQ

end Sound

end LSG.Jac
