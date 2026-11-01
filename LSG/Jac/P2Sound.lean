/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.CheckerP2
import LSG.Jac.Diag

/-!
# Soundness for P2: exact single-copy identities with a large identity table

* `evalOd_spec`, `sound2Vd`: `evalO2_spec` and `sound2V` (`CheckerSound.lean`) with `2^d` accumulator slots
  (same proofs, `8` replaced by `d`).
* `idSeq_spec`: what `idSeqOK` certifies.
* `evalTerms_p2`: on `V(Q)`, if `dup x = 0`, the identity `p2Terms D i Cs Hs` evaluates to `D x_i⁷`.
-/

namespace LSG.Jac

open Data Finset

variable {R : Type*} [CommRing R]

/-- **The accumulator computes the expansion `G`**, slot by slot: slot `j` is `G (NF_j ⊗ ky)` (`X`-side table
`trX`, `Y`-side table `tr`). -/
theorem evalOd_spec (d : ℕ) (tr trX : T) (hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ d) (ps : List Term) :
    (evalOd d trX tr ps).Perfect d ∧ ∀ j < 2 ^ d, (evalOd d trX tr ps).V j =
      G ps (fun μ ν => fiber (rowL (trX.find μ).row) j * sv (tr.find ν).ky) := by
  simp only [evalOd, evalFrom, lfold_eq]
  obtain ⟨h1, h2⟩ := AT.foldl_spec d ps _ _
    (fun acc q _ hp => prodNF_spec tr trX hrows q.c q.neg q.a q.b acc hp) (AT.zero d) (AT.perfect_zero d)
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj, show (AT.zero d).V j = 0 by simp [AT.V, AT.get_zero, sv_zero], zero_add, G_spec]
  refine lsum_congr fun q _ => lsum_congr fun ra _ => lsum_congr fun rb _ => ?_
  rw [sv_yprod, sv_zero, zero_add, lsum_mul_left]
  refine lsum_congr fun t _ => ?_
  rw [lsum_mul_left]
  exact lsum_congr fun u _ => by simp only [Int.cast_id]; ring


/-- **Soundness of the checker** (two tables). If the packed normal form of `Σ_q ±c_q a_q b_q` vanishes, the
weight bound holds and the structural checks pass, then `δX δY · Σ_q ±c_q a_q(x, y) b_q(x, y) = 0` wherever `trX`
is a valid normal form at `x` and `trY` at `y`. -/
theorem sound2Vd (d : ℕ) (trX trY : T) (stdcX stdcY : List ℕ) (NX NY b MX MY δX δY : ℕ) (hNX : NX ≤ 2 ^ d)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (hlY : ∀ l ∈ trY.leaves, leafOK NY b MY l = true)
    (ps : List Term) (hV : ∀ j < 2 ^ d, (evalOd d trX trY ps).V j = 0) (hB : wsum ps * (MX * MY) < 2 ^ b)
    (hT : ∀ q ∈ ps, termOK2 trX trY q = true ∧ q.a.wf = true ∧ q.b.wf = true)
    (x y : Fin 9 → R) (hx : NFValid trX stdcX δX x) (hy : NFValid trY stdcY δY y) :
    ((δX : R) * δY) * evalTerms x y ps = 0 := by
  -- structural facts
  have hTX : ∀ q ∈ ps, ∀ ra ∈ q.a.rows, ∀ rb ∈ q.b.rows,
      nocarry ra.1 rb.1 = true ∧ (trX.find (ra.1 + rb.1)).key = ra.1 + rb.1 := by
    intro q hq ra hra rb hrb
    have h := (hT q hq).1
    unfold termOK2 at h
    rw [Bool.and_eq_true] at h
    exact pairOK_spec h.1 (List.mem_map_of_mem hra) (List.mem_map_of_mem hrb)
  have hTY : ∀ q ∈ ps, ∀ ra ∈ q.a.rows, ∀ rb ∈ q.b.rows, ∀ t ∈ ra.2, ∀ u ∈ rb.2,
      nocarry t.1 u.1 = true ∧ (trY.find (t.1 + u.1)).key = t.1 + u.1 := by
    intro q hq ra hra rb hrb t ht u hu
    have h := (hT q hq).1
    unfold termOK2 at h
    rw [Bool.and_eq_true] at h
    exact pairOK_spec h.2 (SP.wf_spec (hT q hq).2.1 hra ht) (SP.wf_spec (hT q hq).2.2 hrb hu)
  have hkeys : ∀ e ∈ terms ps, (trX.find e.2.1).key = e.2.1 ∧ (trY.find e.2.2).key = e.2.2 := by
    intro e he
    obtain ⟨q, hq, ra, hra, rb, hrb, t, ht, u, hu, h1, h2⟩ := mem_terms he
    rw [h1, h2]
    exact ⟨(hTX q hq ra hra rb hrb).2, (hTY q hq ra hra rb hrb t ht u hu).2⟩
  have hLX := fun c => leafOKX_spec (hlX _ (trX.find_mem c))
  have hLY := fun c => leafOK_spec (hlY _ (trY.find_mem c))
  -- the digit matrix
  set A : ℕ → ℕ → ℤ := fun μ s => fiber (rowL (trX.find μ).row) s with hA
  set Ay : ℕ → ℕ → ℤ := fun ν t => fiber (rowL (trY.find ν).row) t with hAy
  set D : ℕ → ℕ → ℤ := fun s t => G ps (fun μ ν => A μ s * Ay ν t) with hD
  -- packed side
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ d :=
    fun μ t ht => lt_of_lt_of_le ((hLX μ).1 t ht) hNX
  obtain ⟨-, hval⟩ := evalOd_spec d trY trX hrows ps
  have hpack : ∀ s < NX, ∑ t ∈ range NY, D s t * 2 ^ (b * t) = 0 := by
    intro s hs
    have h0 := hval s (lt_of_lt_of_le hs hNX)
    rw [hV s (lt_of_lt_of_le hs hNX)] at h0
    have hk : ∀ μ ν, A μ s * sv (trY.find ν).ky = A μ s * ∑ t ∈ range NY, Ay ν t * 2 ^ (b * t) := by
      intro μ ν
      rw [(hLY ν).1, sv_packS, row_expand_int _ NY (hLY ν).2.1 (fun t => 2 ^ (b * t))]
    rw [G_congr ps (F' := fun μ ν => A μ s * ∑ t ∈ range NY, Ay ν t * 2 ^ (b * t)) (fun e _ => hk _ _),
      G_expand1] at h0
    exact h0.symm
  -- bound on the digits
  have hbound : ∀ s t, |D s t| < 2 ^ b := by
    intro s t
    refine lt_of_le_of_lt (abs_G_le ps _ ((MX : ℤ) * MY) fun e _ => ?_) ?_
    · rw [abs_mul]
      exact mul_le_mul ((abs_fiber_rowL _ _).trans (by exact_mod_cast (hLX _).2))
        ((abs_fiber_rowL _ _).trans (by exact_mod_cast (hLY _).2.2)) (abs_nonneg _) (by positivity)
    · exact_mod_cast hB
  -- digits vanish
  have hD0 : ∀ s < NX, ∀ t < NY, D s t = 0 := fun s hs t ht =>
    digits_eq_zero b NY (D s) (fun k _ => hbound s k) (hpack s hs) t ht
  -- semantic side
  have hNFX : ∀ μ, (trX.find μ).key = μ →
      (δX : R) * xmono x μ = ∑ s ∈ range NX, (A μ s : R) * xmono x (stdcX.getD s 0) := by
    intro μ hμ
    have := hx _ (trX.find_mem μ)
    rw [hμ] at this
    rw [this, evalNF, row_expand _ NX (hLX μ).1 (fun s => xmono x (stdcX.getD s 0))]
  have hNFY : ∀ ν, (trY.find ν).key = ν →
      (δY : R) * xmono y ν = ∑ t ∈ range NY, (Ay ν t : R) * xmono y (stdcY.getD t 0) := by
    intro ν hν
    have := hy _ (trY.find_mem ν)
    rw [hν] at this
    rw [this, evalNF, row_expand _ NY (hLY ν).2.1 (fun t => xmono y (stdcY.getD t 0))]
  rw [evalTerms_eq_G x y ps (fun q hq ra hra rb hrb => (hTX q hq ra hra rb hrb).1)
      (fun q hq ra hra rb hrb t ht u hu => (hTY q hq ra hra rb hrb t ht u hu).1), G_smul,
    G_congr ps (F' := fun μ ν => (∑ s ∈ range NX, (A μ s : R) * xmono x (stdcX.getD s 0)) *
      (∑ t ∈ range NY, (Ay ν t : R) * xmono y (stdcY.getD t 0))) (fun e he => by
        rw [← hNFX _ (hkeys e he).1, ← hNFY _ (hkeys e he).2]; ring),
    G_expand]
  refine sum_eq_zero fun s hs => sum_eq_zero fun t ht => ?_
  rw [show G ps (fun μ ν => A μ s * Ay ν t) = D s t from rfl,
    hD0 s (mem_range.mp hs) t (mem_range.mp ht)]
  simp


/-- What `idSeqOK` certifies. -/
theorem idSeq_spec : ∀ (ls : List Leaf) (n : ℕ), idSeqOK ls n = true →
    ∀ i (h : i < ls.length), ls[i].idx = n + i ∧ ls[i].row = [(n + i, 1, false)]
  | [], _, _, i, h => absurd h (by simp)
  | l :: ls, n, hs, i, h => by
    have hs' : ((Nat.beq l.idx n && decide (l.row = [(n, 1, false)])) && idSeqOK ls (n + 1)) = true := hs
    simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hs'
    cases i with
    | zero => simpa using hs'.1
    | succ i =>
      have := idSeq_spec ls (n + 1) hs'.2 i (by simpa using h)
      simp only [List.getElem_cons_succ]
      rw [this.1, this.2, show n + 1 + i = n + (i + 1) by omega]
      exact ⟨rfl, rfl⟩

/-- An identity table certified by `idSeqOK` is valid (`δ = 1`) for `stdc = keys`. -/
lemma idSeq_facts (tr : T) (h : idSeqOK tr.leaves 0 = true) :
    ∀ l ∈ tr.leaves, l.idx < tr.leaves.length ∧ l.row = [(l.idx, 1, false)] ∧
      (tr.leaves.map Leaf.key).getD l.idx 0 = l.key := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
  have := idSeq_spec _ 0 h i hi
  rw [zero_add] at this
  refine ⟨by rw [this.1]; exact hi, by rw [this.2, this.1], ?_⟩
  rw [this.1]
  simp [List.getD_eq_getElem?_getD, hi]

lemma leafOKX_idSeq (tr : T) (h : idSeqOK tr.leaves 0 = true) :
    ∀ l ∈ tr.leaves, leafOKX tr.leaves.length 1 l = true := by
  intro l hl
  obtain ⟨h1, h2, -⟩ := idSeq_facts tr h l hl
  simp [leafOKX, rowN, h2, h1]

lemma nfValid_idSeq (tr : T) (h : idSeqOK tr.leaves 0 = true) (x : Fin 9 → R) :
    NFValid tr (tr.leaves.map Leaf.key) 1 x := by
  intro l hl
  obtain ⟨-, h2, h3⟩ := idSeq_facts tr h l hl
  simp only [evalNF, h2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h3]
  simp [sval]

/-- **Exact single-copy identities through an identity table** (`2^d` slots, `Y`-table `T0`). -/
theorem exact_of_idSeq (d : ℕ) (tr : T) (h : idSeqOK tr.leaves 0 = true) (hN : tr.leaves.length ≤ 2 ^ d)
    (ps : List Term) (hO : (evalOd d tr T0 ps).allZero = true) (hB : wsum ps * (1 * 1) < 2 ^ 128)
    (hT : ps.all (fun q => termOK2 tr T0 q && q.a.wf && q.b.wf) = true) (x y : Fin 9 → R) :
    evalTerms x y ps = 0 := by
  have hlX := leafOKX_idSeq tr h
  have hperf : (evalOd d tr T0 ps).Perfect d := (evalOd_spec d T0 tr (fun μ t ht =>
    lt_of_lt_of_le ((leafOKX_spec (hlX _ (tr.find_mem μ))).1 t ht) hN) ps).1
  have hT' : ∀ q ∈ ps, termOK2 tr T0 q = true ∧ q.a.wf = true ∧ q.b.wf = true := fun q hq => by
    have := List.all_eq_true.mp hT q hq
    simpa [Bool.and_eq_true, and_assoc] using this
  have := sound2Vd d tr T0 (tr.leaves.map Leaf.key) [0] tr.leaves.length 1 128 1 1 1 1 hN hlX
    (leafOK_T0 128 (by norm_num)) ps (AT.allZero_spec hperf hO) hB hT' x y (nfValid_idSeq tr h x) (nfValid_T0 y)
  simpa using this

/-! ## The P2 identity -/

lemma xmono_zero' (y : Fin 9 → R) : xmono y 0 = 1 := by simp [xmono, digit]

lemma evalSP_monoSP (x y : Fin 9 → R) (c : ℕ) : evalSP x y (monoSP c) = xmono x c := by
  simp [evalSP, monoSP, evalRow, sval, xmono_zero']

lemma evalSP_zeroSP (x y : Fin 9 → R) : evalSP x y zeroSP = 0 := by simp [evalSP, zeroSP]

lemma evalSP_rowSP (x y : Fin 9 → R) (r : List (ℕ × ℕ × Bool)) : evalSP x y (rowSP r) = evalRow x r := by
  unfold evalSP rowSP evalRow
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [evalRow, xmono_zero', mul_comm]

lemma xmono_seven (x : Fin 9 → R) (i : Fin 9) : xmono x (7 * 8 ^ (i : ℕ)) = x i ^ 7 := by
  fin_cases i <;> simp [xmono, digit, Fin.prod_univ_succ]

/-- On `V(Q)`, where `dup x = 0`, the P2 identity reduces to `D x_i⁷`. -/
theorem evalTerms_p2 (D : ℕ) (i : Fin 9) (Cs Hs : List SP) (x y : Fin 9 → R) (hx : OnQ x)
    (hd : ∀ k : Fin 9, evalSP x x (law k 4) = 0)
    (hdiag : (List.range 9).all (fun k => diagOK (law k 4)) = true) :
    evalTerms x y (p2Terms D i Cs Hs) = D * x i ^ 7 := by
  unfold p2Terms evalTerms
  rw [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_map, List.map_map]
  have h1 : ∀ a ∈ (List.range 9).map ((fun q : Term => (sval q.c q.neg : R) * evalSP x y q.a * evalSP x y q.b) ∘
      fun k => (⟨1, true, Cs.getD k zeroSP, diagSP (law k 4)⟩ : Term)), a = 0 := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    simp only [Function.comp_apply]
    rw [evalSP_diagSP x y _ (List.all_eq_true.mp hdiag k hk), hd ⟨k, List.mem_range.mp hk⟩, mul_zero]
  have h2 : ∀ a ∈ (List.range 9).map ((fun q : Term => (sval q.c q.neg : R) * evalSP x y q.a * evalSP x y q.b) ∘
      fun j => (⟨1, true, Hs.getD j zeroSP, rowSP (Qd.getD j [])⟩ : Term)), a = 0 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simp only [Function.comp_apply]
    rw [evalSP_rowSP, show evalRow x (Qd.getD j []) = 0 from hx ⟨j, List.mem_range.mp hj⟩, mul_zero]
  rw [List.sum_eq_zero h1, List.sum_eq_zero h2]
  simp [evalSP_monoSP, evalSP_oneSP, sval, xmono_seven]

end LSG.Jac
