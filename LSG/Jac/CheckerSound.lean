/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Checker
import LSG.Jac.Kron

/-!
# Soundness of the normal-form + Kronecker checker (Stage A1c)

**Main result** (`sound_bidegree`). Let `tr` be a normal-form table (`N` standard monomials, slot width `b`, row
norms `≤ M`) with `leafOK` at every leaf, and let `ps` describe an identity `Σ_q ±c_q a_q b_q`. If

* `hO`: the packed normal form vanishes, `(evalO tr ps).1 = (evalO tr ps).2`;
* `hB`: `wsum ps · M² < 2^b`;
* `hT`: `termOK` for every product (code pairs add without carry to keys of `tr`), and every `SP` is `wf`;

then for all `x y : Fin 9 → R` (any commutative ring) at which the table is a *valid normal form*
(`NFValid δ x`: `δ · X^key = NF(row)` at `x` for every leaf), `δ² · Σ_q ±c_q a_q(x, y) b_q(x, y) = 0`.

**Proof.** Both the packed integer and `δ² ·` the value are images of one formal expansion `G` over the flat list of
term products (`terms`): `sv (evalO …) = G (kx ⊗ ky)` (`sv_evalO`) and `δ² · value = G (NF ⊗ NF)` (`evalTerms_eq_G`,
`NFValid`). Expanding both normal forms in the standard basis, `G` becomes `Σ_{s,t} D_{s,t} (f_s g_t)` with one integer
matrix `D` (`G_expand`). The packed side is `Σ_{s,t} D_{s,t} 2^{b(Ns + t)} = 0` with `|D_{s,t}| ≤ wsum · M² < 2^b`, so
`D = 0` (`digits_eq_zero`).
-/

namespace LSG.Jac

open Finset

/-! ## Semantics -/

/-- The monomial with code `c`, evaluated at `x`. -/
def xmono {R : Type*} [CommMonoid R] (x : Fin 9 → R) (c : ℕ) : R := ∏ i : Fin 9, x i ^ digit c i

section Eval

variable {R : Type*} [CommRing R]

/-- Value of a row of monomials: `Σ ±n X^c`. -/
def evalRow (x : Fin 9 → R) (r : List (ℕ × ℕ × Bool)) : R :=
  (r.map fun t => (sval t.2.1 t.2.2 : R) * xmono x t.1).sum

/-- Value of a normal-form row: `Σ ±n X^{std s}`. -/
def evalNF (x : Fin 9 → R) (stdc : List ℕ) (r : List (ℕ × ℕ × Bool)) : R :=
  (r.map fun t => (sval t.2.1 t.2.2 : R) * xmono x (stdc.getD t.1 0)).sum

/-- Value of an `SP` at `(x, y)`. -/
def evalSP (x y : Fin 9 → R) (p : SP) : R :=
  (p.rows.map fun r => xmono x r.1 * evalRow y r.2).sum

/-- Value of an identity `Σ_q ±c_q a_q b_q` at `(x, y)`. -/
def evalTerms (x y : Fin 9 → R) (ps : List Term) : R :=
  (ps.map fun q => (sval q.c q.neg : R) * evalSP x y q.a * evalSP x y q.b).sum

end Eval


/-! ## Monomials -/

section Mono

variable {R : Type*} [CommMonoid R]

lemma nocarry_digit {a b : ℕ} (h : nocarry a b = true) (i : Fin 9) :
    digit (a + b) i = digit a i + digit b i := by
  unfold nocarry at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr i.2)
  simpa using this

/-- Adding codes without carry multiplies monomials. -/
theorem xmono_add (x : Fin 9 → R) {a b : ℕ} (h : nocarry a b = true) :
    xmono x (a + b) = xmono x a * xmono x b := by
  simp only [xmono, ← prod_mul_distrib, ← pow_add, nocarry_digit h]

end Mono

/-! ## Signed pairs -/

/-- The integer `P − N` represented by `(P, N)`. -/
def sv (p : ℕ × ℕ) : ℤ := p.1 - p.2

lemma sv_addS (acc : ℕ × ℕ) (c : ℕ) (neg : Bool) (v : ℕ × ℕ) :
    sv (addS acc c neg v) = sv acc + sval c neg * sv v := by
  unfold addS sval sv; cases neg <;> simp [cond] <;> ring

lemma sv_mulS (x y : ℕ × ℕ) : sv (mulS x y) = sv x * sv y := by
  unfold mulS sv; push_cast; ring

lemma sval_mul_bne (a b : ℕ) (s t : Bool) : sval (a * b) (s != t) = sval a s * sval b t := by
  cases s <;> cases t <;> simp [sval]

lemma abs_sval (a : ℕ) (s : Bool) : |sval a s| = a := by cases s <;> simp [sval]

lemma sv_foldl {α : Type*} (l : List α) (F : ℕ × ℕ → α → ℕ × ℕ) (g : α → ℤ)
    (hF : ∀ acc a, sv (F acc a) = sv acc + g a) (acc : ℕ × ℕ) :
    sv (l.foldl F acc) = sv acc + (l.map g).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hF, List.map_cons, List.sum_cons]; ring

@[simp] lemma lfold_eq {α β : Type} (f : β → α → β) (l : List α) (b : β) :
    lfold f l b = l.foldl f b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih (f b a)

lemma T.find_leaf (v : Leaf) (c : ℕ) : (T.leaf v).find c = v := rfl

lemma T.find_node (k : ℕ) (l r : T) (c : ℕ) :
    (T.node k l r).find c = if c < k then l.find c else r.find c := by
  show cond (Nat.blt c k) (l.find c) (r.find c) = _
  by_cases h : c < k <;> simp [h, Nat.blt_eq]

lemma AT.get_leaf (a : ℕ × ℕ) (i : ℕ) : (AT.leaf a).get i = a := rfl

lemma AT.get_node (l r : AT) (i : ℕ) :
    (AT.node l r).get i = if i % 2 = 0 then l.get (i / 2) else r.get (i / 2) := by
  show cond (Nat.beq (i % 2) 0) (l.get (i / 2)) (r.get (i / 2)) = _
  by_cases h : i % 2 = 0 <;> simp [h]

lemma AT.addAt_leaf (a : ℕ × ℕ) (i c : ℕ) (neg : Bool) (v : ℕ × ℕ) :
    (AT.leaf a).addAt i c neg v = .leaf (addS a c neg v) := rfl

lemma AT.addAt_node (l r : AT) (i c : ℕ) (neg : Bool) (v : ℕ × ℕ) :
    (AT.node l r).addAt i c neg v =
      if i % 2 = 0 then .node (l.addAt (i / 2) c neg v) r else .node l (r.addAt (i / 2) c neg v) := by
  show cond (Nat.beq (i % 2) 0) (AT.node (l.addAt (i / 2) c neg v) r) (AT.node l (r.addAt (i / 2) c neg v)) = _
  by_cases h : i % 2 = 0 <;> simp [h]

lemma AT.allZero_leaf (a : ℕ × ℕ) : (AT.leaf a).allZero = true ↔ a.1 = a.2 := by
  show Nat.beq a.1 a.2 = true ↔ a.1 = a.2
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

lemma AT.allZero_node (l r : AT) : (AT.node l r).allZero = (l.allZero && r.allZero) := by
  show cond l.allZero r.allZero false = _
  cases l.allZero <;> rfl

lemma sv_packS (w : ℕ) (row : List (ℕ × ℕ × Bool)) :
    sv (packS w row) = (row.map fun t => sval t.2.1 t.2.2 * 2 ^ (w * t.1)).sum := by
  unfold packS
  rw [sv_foldl _ _ (fun t => sval t.2.1 t.2.2 * 2 ^ (w * t.1))]
  · simp [sv]
  · intro acc t; rw [sv_addS]; simp [sv, Nat.shiftLeft_eq]

/-! ## List-sum helpers -/

section ListSum

variable {R : Type*} [CommRing R] {α β : Type*}

lemma map_flatMap_sum (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma lsum_mul_left (r : R) (l : List α) (f : α → R) :
    r * (l.map f).sum = (l.map fun a => r * f a).sum := (List.sum_map_mul_left l f r).symm

lemma lsum_mul_right (r : R) (l : List α) (f : α → R) :
    (l.map f).sum * r = (l.map fun a => f a * r).sum := (List.sum_map_mul_right l f r).symm

lemma lsum_finset_comm {ι : Type*} (s : Finset ι) (l : List α) (f : α → ι → R) :
    (l.map fun a => ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sum_add_distrib]

lemma cast_lsum (l : List α) (f : α → ℤ) : (((l.map f).sum : ℤ) : R) = (l.map fun a => (f a : R)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma lsum_congr {l : List α} {f g : α → R} (h : ∀ a ∈ l, f a = g a) :
    (l.map f).sum = (l.map g).sum := by rw [List.map_congr_left h]

lemma lsum_mul_lsum (l₁ : List α) (l₂ : List β) (f : α → R) (g : β → R) :
    (l₁.map f).sum * (l₂.map g).sum = (l₁.map fun a => (l₂.map fun b => f a * g b).sum).sum := by
  rw [lsum_mul_right]; exact lsum_congr fun a _ => lsum_mul_left _ _ _

lemma lsum_abs_le (l : List α) (f : α → ℤ) : |(l.map f).sum| ≤ (l.map fun a => |f a|).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (by linarith)

lemma lsum_le {l : List α} {f g : α → ℤ} (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

end ListSum

/-! ## The formal expansion `G` -/

/-- The flat list of term products `(±c_q ±n_t ±n_u, α + α', β + β')`. -/
def terms (ps : List Term) : List (ℤ × ℕ × ℕ) :=
  ps.flatMap fun q => q.a.rows.flatMap fun ra => q.b.rows.flatMap fun rb =>
    ra.2.flatMap fun t => rb.2.map fun u =>
      (sval q.c q.neg * sval t.2.1 t.2.2 * sval u.2.1 u.2.2, ra.1 + rb.1, t.1 + u.1)

/-- The formal expansion evaluated with a "monomial pairing" `F`. -/
def G {R : Type*} [CommRing R] (ps : List Term) (F : ℕ → ℕ → R) : R :=
  ((terms ps).map fun e => (e.1 : R) * F e.2.1 e.2.2).sum

section G

variable {R : Type*} [CommRing R]

/-- `G` as a nested sum. -/
lemma G_spec (ps : List Term) (F : ℕ → ℕ → R) :
    G ps F = (ps.map fun q => (q.a.rows.map fun ra => (q.b.rows.map fun rb =>
      (ra.2.map fun t => (rb.2.map fun u =>
        (sval q.c q.neg : R) * sval t.2.1 t.2.2 * sval u.2.1 u.2.2 * F (ra.1 + rb.1) (t.1 + u.1)).sum).sum).sum).sum).sum := by
  simp only [G, terms, map_flatMap_sum, List.map_map, Function.comp_def]
  push_cast
  rfl

lemma mem_terms {ps : List Term} {e : ℤ × ℕ × ℕ} (he : e ∈ terms ps) :
    ∃ q ∈ ps, ∃ ra ∈ q.a.rows, ∃ rb ∈ q.b.rows, ∃ t ∈ ra.2, ∃ u ∈ rb.2,
      e.2.1 = ra.1 + rb.1 ∧ e.2.2 = t.1 + u.1 := by
  simp only [terms, List.mem_flatMap, List.mem_map] at he
  obtain ⟨q, hq, ra, hra, rb, hrb, t, ht, u, hu, rfl⟩ := he
  exact ⟨q, hq, ra, hra, rb, hrb, t, ht, u, hu, rfl, rfl⟩

lemma G_congr (ps : List Term) {F F' : ℕ → ℕ → R}
    (h : ∀ e ∈ terms ps, F e.2.1 e.2.2 = F' e.2.1 e.2.2) : G ps F = G ps F' :=
  lsum_congr fun e he => by rw [h e he]

lemma G_smul (ps : List Term) (r : R) (F : ℕ → ℕ → R) :
    r * G ps F = G ps (fun μ ν => r * F μ ν) := by
  simp only [G, lsum_mul_left]; exact lsum_congr fun e _ => by ring

lemma G_cast (ps : List Term) (F : ℕ → ℕ → ℤ) : ((G ps F : ℤ) : R) = G ps (fun μ ν => (F μ ν : R)) := by
  simp only [G, cast_lsum]
  exact lsum_congr fun e _ => by push_cast; rfl

/-- **Bilinear expansion.** `G (Σ_s A μ s f_s ⊗ Σ_t B ν t g_t) = Σ_{s,t} G(A_s ⊗ B_t) f_s g_t`. -/
lemma G_expand (ps : List Term) (n m : ℕ) (A B : ℕ → ℕ → ℤ) (f g : ℕ → R) :
    G ps (fun μ ν => (∑ s ∈ range n, (A μ s : R) * f s) * (∑ t ∈ range m, (B ν t : R) * g t)) =
      ∑ s ∈ range n, ∑ t ∈ range m,
        ((G ps (fun μ ν => A μ s * B ν t) : ℤ) : R) * (f s * g t) := by
  have h1 : ∀ μ ν, (∑ s ∈ range n, (A μ s : R) * f s) * (∑ t ∈ range m, (B ν t : R) * g t) =
      ∑ s ∈ range n, ∑ t ∈ range m, ((A μ s * B ν t : ℤ) : R) * (f s * g t) := by
    intro μ ν; rw [sum_mul_sum]; refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
    push_cast; ring
  simp only [h1, G, mul_sum]
  rw [lsum_finset_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [lsum_finset_comm]
  refine sum_congr rfl fun t _ => ?_
  simp only [cast_lsum, lsum_mul_right]
  exact lsum_congr fun e _ => by push_cast; ring

/-- One-sided expansion (over `ℤ`). -/
lemma G_expand1 (ps : List Term) (n : ℕ) (a : ℕ → ℤ) (B : ℕ → ℕ → ℤ) (g : ℕ → ℤ) :
    G ps (fun μ ν => a μ * ∑ t ∈ range n, B ν t * g t) =
      ∑ t ∈ range n, G ps (fun μ ν => a μ * B ν t) * g t := by
  have h : ∀ e : ℤ × ℕ × ℕ, e.1 * (a e.2.1 * ∑ t ∈ range n, B e.2.2 t * g t) =
      ∑ t ∈ range n, e.1 * (a e.2.1 * B e.2.2 t) * g t := by
    intro e; rw [mul_sum, mul_sum]; exact sum_congr rfl fun t _ => by ring
  simp only [G, Int.cast_id, h, lsum_finset_comm, lsum_mul_right]

/-- The total weight `Σ_e |w_e|` equals `wsum`. -/
lemma terms_abs (ps : List Term) : ((terms ps).map fun e => |e.1|).sum = (wsum ps : ℤ) := by
  simp only [terms, map_flatMap_sum, List.map_map, Function.comp_def, abs_mul, abs_sval, wsum, rowN,
    Nat.cast_list_sum, Nat.cast_mul]
  refine lsum_congr fun q _ => ?_
  rw [lsum_mul_left]
  refine lsum_congr fun ra _ => ?_
  rw [lsum_mul_left]
  refine lsum_congr fun rb _ => ?_
  rw [lsum_mul_lsum, lsum_mul_left]
  refine lsum_congr fun t _ => ?_
  rw [lsum_mul_left]
  exact lsum_congr fun u _ => by ring

/-- `|G ps F| ≤ wsum · C` when `|F| ≤ C` on the terms. -/
lemma abs_G_le (ps : List Term) (F : ℕ → ℕ → ℤ) (C : ℤ) (hF : ∀ e ∈ terms ps, |F e.2.1 e.2.2| ≤ C) :
    |G ps F| ≤ wsum ps * C := by
  refine (lsum_abs_le _ _).trans ?_
  rw [← terms_abs, lsum_mul_right]
  refine lsum_le fun e he => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hF e he) (abs_nonneg _)

end G

/-! ## The packed side -/

/-- The signed list `(±n, slot)` of a row. -/
def rowL (r : List (ℕ × ℕ × Bool)) : List (ℤ × ℕ) := r.map fun t => (sval t.2.1 t.2.2, t.1)

section Packed

variable (tr : T)

lemma sv_yprod (p q : List (ℕ × ℕ × Bool)) (acc : ℕ × ℕ) :
    sv (yprod tr p q acc) = sv acc + (p.map fun t => (q.map fun u =>
      sval t.2.1 t.2.2 * sval u.2.1 u.2.2 * sv (tr.find (t.1 + u.1)).ky).sum).sum := by
  unfold yprod
  simp only [lfold_eq]
  rw [sv_foldl _ _ (fun t => (q.map fun u =>
      sval t.2.1 t.2.2 * sval u.2.1 u.2.2 * sv (tr.find (t.1 + u.1)).ky).sum)]
  intro acc t
  rw [sv_foldl _ _ (fun u => sval t.2.1 t.2.2 * sval u.2.1 u.2.2 * sv (tr.find (t.1 + u.1)).ky)]
  intro acc u
  rw [sv_addS, sval_mul_bne]

lemma sv_zero : sv (0, 0) = 0 := by simp [sv]

/-! ### The accumulator tree -/

/-- A perfect accumulator tree of depth `d`. -/
inductive AT.Perfect : ℕ → AT → Prop
  | leaf (v : ℕ × ℕ) : AT.Perfect 0 (.leaf v)
  | node {d : ℕ} {l r : AT} : AT.Perfect d l → AT.Perfect d r → AT.Perfect (d + 1) (.node l r)

/-- The signed value of slot `j`. -/
noncomputable def AT.V (t : AT) (j : ℕ) : ℤ := sv (t.get j)

lemma AT.perfect_zero : ∀ d, (AT.zero d).Perfect d
  | 0 => .leaf _
  | d + 1 => .node (AT.perfect_zero d) (AT.perfect_zero d)

lemma AT.get_zero : ∀ d j, (AT.zero d).get j = (0, 0)
  | 0, _ => rfl
  | d + 1, j => by unfold AT.zero; rw [AT.get_node]; split_ifs <;> exact AT.get_zero d _

lemma AT.perfect_addAt {d : ℕ} {t : AT} (ht : t.Perfect d) (i c : ℕ) (neg : Bool) (v : ℕ × ℕ) :
    (t.addAt i c neg v).Perfect d := by
  induction ht generalizing i with
  | leaf a => exact .leaf _
  | node hl hr ihl ihr =>
    rw [AT.addAt_node]; split_ifs
    · exact .node (ihl _) hr
    · exact .node hl (ihr _)

lemma AT.get_addAt {d : ℕ} {t : AT} (ht : t.Perfect d) (c : ℕ) (neg : Bool) (v : ℕ × ℕ) :
    ∀ i j, i < 2 ^ d → j < 2 ^ d →
      (t.addAt i c neg v).get j = if j = i then addS (t.get i) c neg v else t.get j := by
  induction ht with
  | leaf a =>
    intro i j hi hj
    simp only [pow_zero, Nat.lt_one_iff] at hi hj
    subst hi hj; simp [AT.addAt_leaf, AT.get_leaf]
  | node hl hr ihl ihr =>
    rename_i d l r
    intro i j hi hj
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    rw [AT.addAt_node]
    by_cases hi0 : i % 2 = 0 <;> by_cases hj0 : j % 2 = 0 <;> simp only [hi0, hj0, if_true, if_false,
      AT.get_node, ihl, ihr, hi2, hj2, show (1 : ℕ) % 2 = 1 from rfl] <;> (try simp) <;>
      first
      | (by_cases hij : j / 2 = i / 2 <;> simp [hij] <;> (try omega) <;> (have : j = i := by omega) <;>
          simp [this])
      | (have : j ≠ i := by omega
         simp [this])

lemma AT.allZero_spec {d : ℕ} {t : AT} (ht : t.Perfect d) (h : t.allZero = true) :
    ∀ j < 2 ^ d, t.V j = 0 := by
  induction ht with
  | leaf a => intro j _; rw [AT.allZero_leaf] at h; simp [AT.V, AT.get_leaf, sv, h]
  | node hl hr ihl ihr =>
    rename_i d l r
    intro j hj
    simp only [AT.allZero_node, Bool.and_eq_true] at h
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    unfold AT.V
    rw [AT.get_node]
    split_ifs
    · exact ihl h.1 _ hj2
    · exact ihr h.2 _ hj2

lemma AT.V_addAt {d : ℕ} {t : AT} (ht : t.Perfect d) (i c : ℕ) (neg : Bool) (v : ℕ × ℕ) (hi : i < 2 ^ d)
    (j : ℕ) (hj : j < 2 ^ d) :
    (t.addAt i c neg v).V j = t.V j + if i = j then sval c neg * sv v else 0 := by
  unfold AT.V
  rw [AT.get_addAt ht c neg v i j hi hj]
  by_cases h : j = i
  · subst h; simp [sv_addS]
  · simp [h, Ne.symm h]

/-- Folding a slot-additive update over a list. -/
lemma AT.foldl_spec {α : Type*} (d : ℕ) (l : List α) (F : AT → α → AT) (g : α → ℕ → ℤ)
    (hF : ∀ acc, ∀ a ∈ l, acc.Perfect d →
      (F acc a).Perfect d ∧ ∀ j < 2 ^ d, (F acc a).V j = acc.V j + g a j)
    (acc : AT) (hacc : acc.Perfect d) :
    (l.foldl F acc).Perfect d ∧
      ∀ j < 2 ^ d, (l.foldl F acc).V j = acc.V j + (l.map fun a => g a j).sum := by
  induction l generalizing acc with
  | nil => exact ⟨hacc, fun j _ => by simp⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := hF acc a List.mem_cons_self hacc
    obtain ⟨h3, h4⟩ := ih (fun acc b hb => hF acc b (List.mem_cons_of_mem _ hb)) (F acc a) h1
    refine ⟨h3, fun j hj => ?_⟩
    rw [List.foldl_cons, h4 j hj, h2 j hj, List.map_cons, List.sum_cons]; ring

lemma fiber_rowL_eq (row : List (ℕ × ℕ × Bool)) (j : ℕ) :
    fiber (rowL row) j = (row.map fun t => if t.1 = j then sval t.2.1 t.2.2 else 0).sum := by
  simp [fiber, rowL, List.map_map, Function.comp_def]

lemma addRow_spec {d : ℕ} (row : List (ℕ × ℕ × Bool)) (hrow : ∀ t ∈ row, t.1 < 2 ^ d) (c : ℕ)
    (neg : Bool) (v : ℕ × ℕ) (acc : AT) (hacc : acc.Perfect d) :
    (addRow acc row c neg v).Perfect d ∧
      ∀ j < 2 ^ d, (addRow acc row c neg v).V j = acc.V j + sval c neg * fiber (rowL row) j * sv v := by
  unfold addRow
  simp only [lfold_eq]
  obtain ⟨h1, h2⟩ := AT.foldl_spec d row (fun acc t => acc.addAt t.1 (c * t.2.1) (neg != t.2.2) v)
    (fun t j => if t.1 = j then sval c neg * sval t.2.1 t.2.2 * sv v else 0)
    (fun acc t ht hp => ⟨AT.perfect_addAt hp _ _ _ _, fun j hj => by
      rw [AT.V_addAt hp _ _ _ _ (hrow t ht) j hj, sval_mul_bne]⟩) acc hacc
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj, fiber_rowL_eq, lsum_mul_left, lsum_mul_right]
  congr 1
  exact lsum_congr fun t _ => by split_ifs <;> simp

lemma prodNF_spec (trX : T) {d : ℕ} (hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ d) (c : ℕ)
    (neg : Bool) (A B : SP) (acc : AT) (hacc : acc.Perfect d) :
    (prodNF trX tr c neg A B acc).Perfect d ∧ ∀ j < 2 ^ d, (prodNF trX tr c neg A B acc).V j = acc.V j +
      (A.rows.map fun ra => (B.rows.map fun rb => sval c neg * fiber (rowL (trX.find (ra.1 + rb.1)).row) j *
        sv (yprod tr ra.2 rb.2 (0, 0))).sum).sum := by
  have hB : ∀ (ra : ℕ × List (ℕ × ℕ × Bool)) (acc : AT), acc.Perfect d →
      (B.rows.foldl (fun acc rb => addRow acc (trX.find (ra.1 + rb.1)).row c neg
        (yprod tr ra.2 rb.2 (0, 0))) acc).Perfect d ∧
      ∀ j < 2 ^ d, (B.rows.foldl (fun acc rb => addRow acc (trX.find (ra.1 + rb.1)).row c neg
        (yprod tr ra.2 rb.2 (0, 0))) acc).V j = acc.V j + (B.rows.map fun rb => sval c neg *
          fiber (rowL (trX.find (ra.1 + rb.1)).row) j * sv (yprod tr ra.2 rb.2 (0, 0))).sum :=
    fun ra acc hp => AT.foldl_spec d B.rows
      (fun acc rb => addRow acc (trX.find (ra.1 + rb.1)).row c neg (yprod tr ra.2 rb.2 (0, 0)))
      (fun rb j => sval c neg * fiber (rowL (trX.find (ra.1 + rb.1)).row) j *
        sv (yprod tr ra.2 rb.2 (0, 0)))
      (fun acc rb _ hp' => addRow_spec _ (hrows _) c neg _ acc hp') acc hp
  simp only [prodNF, lfold_eq]
  exact AT.foldl_spec d A.rows _ _ (fun acc ra _ hp => hB ra acc hp) acc hacc

/-- **The accumulator computes the expansion `G`**, slot by slot: slot `j` is `G (NF_j ⊗ ky)` (`X`-side table
`trX`, `Y`-side table `tr`). -/
theorem evalO2_spec (trX : T) (hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8) (ps : List Term) :
    (evalO2 trX tr ps).Perfect 8 ∧ ∀ j < 2 ^ 8, (evalO2 trX tr ps).V j =
      G ps (fun μ ν => fiber (rowL (trX.find μ).row) j * sv (tr.find ν).ky) := by
  simp only [evalO2, evalFrom, lfold_eq]
  obtain ⟨h1, h2⟩ := AT.foldl_spec 8 ps _ _
    (fun acc q _ hp => prodNF_spec tr trX hrows q.c q.neg q.a q.b acc hp) (AT.zero 8) (AT.perfect_zero 8)
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj, show (AT.zero 8).V j = 0 by simp [AT.V, AT.get_zero, sv_zero], zero_add, G_spec]
  refine lsum_congr fun q _ => lsum_congr fun ra _ => lsum_congr fun rb _ => ?_
  rw [sv_yprod, sv_zero, zero_add, lsum_mul_left]
  refine lsum_congr fun t _ => ?_
  rw [lsum_mul_left]
  exact lsum_congr fun u _ => by simp only [Int.cast_id]; ring

end Packed

/-! ## The main soundness theorem -/

lemma T.find_mem (tr : T) (c : ℕ) : tr.find c ∈ tr.leaves := by
  induction tr with
  | leaf v => simp [T.find_leaf, T.leaves]
  | node k l r ihl ihr =>
    rw [T.find_node]; unfold T.leaves
    split_ifs
    · exact List.mem_append_left _ ihl
    · exact List.mem_append_right _ ihr

lemma pairOK_spec {tr : T} {l₁ l₂ : List ℕ} (h : pairOK tr l₁ l₂ = true) {a c : ℕ} (ha : a ∈ l₁)
    (hc : c ∈ l₂) : nocarry a c = true ∧ (tr.find (a + c)).key = a + c := by
  unfold pairOK at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h a ha) c hc
  simpa [Bool.and_eq_true] using this

lemma SP.wf_spec {p : SP} (h : p.wf = true) {r : ℕ × List (ℕ × ℕ × Bool)} (hr : r ∈ p.rows)
    {t : ℕ × ℕ × Bool} (ht : t ∈ r.2) : t.1 ∈ p.yc := by
  unfold SP.wf at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h r hr) t ht
  simpa using this

lemma leafOKX_spec {N M : ℕ} {l : Leaf} (h : leafOKX N M l = true) :
    (∀ t ∈ l.row, t.1 < N) ∧ rowN l.row ≤ M := by
  unfold leafOKX at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

lemma leafOKX_of_leafOK {N b M : ℕ} {l : Leaf} (h : leafOK N b M l = true) : leafOKX N M l = true := by
  unfold leafOK at h; unfold leafOKX
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.2, h.2⟩

lemma leafOK_spec {N b M : ℕ} {l : Leaf} (h : leafOK N b M l = true) :
    l.ky = packS b l.row ∧ (∀ t ∈ l.row, t.1 < N) ∧ rowN l.row ≤ M := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

section Main

variable {R : Type*} [CommRing R]

lemma row_expand (r : List (ℕ × ℕ × Bool)) (n : ℕ) (hr : ∀ t ∈ r, t.1 < n) (f : ℕ → R) :
    (r.map fun t => (sval t.2.1 t.2.2 : R) * f t.1).sum =
      ∑ s ∈ range n, (fiber (rowL r) s : R) * f s := by
  have hL : ∀ p ∈ rowL r, p.2 < n := by
    intro p hp
    simp only [rowL, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hr t ht
  have := sum_fiber (rowL r) n hL f
  simp only [rowL, List.map_map, Function.comp_def, zsmul_eq_mul] at this
  rw [this]; rfl

lemma row_expand_int (r : List (ℕ × ℕ × Bool)) (n : ℕ) (hr : ∀ t ∈ r, t.1 < n) (f : ℕ → ℤ) :
    (r.map fun t => sval t.2.1 t.2.2 * f t.1).sum = ∑ s ∈ range n, fiber (rowL r) s * f s := by
  simpa using row_expand (R := ℤ) r n hr f

lemma abs_fiber_rowL (r : List (ℕ × ℕ × Bool)) (s : ℕ) : |fiber (rowL r) s| ≤ rowN r := by
  refine (abs_fiber_le _ s).trans (le_of_eq ?_)
  simp only [rowL, rowN, List.map_map, Function.comp_def, abs_sval, Nat.cast_list_sum]

/-- Normal-form validity of a table at a point: `δ · X^key = NF(row)` for every leaf. -/
def NFValid (tr : T) (stdc : List ℕ) (δ : ℕ) (x : Fin 9 → R) : Prop :=
  ∀ l ∈ tr.leaves, (δ : R) * xmono x l.key = evalNF x stdc l.row

/-- Expansion of the value of an identity, given the no-carry conditions. -/
lemma evalTerms_eq_G (x y : Fin 9 → R) (ps : List Term)
    (hX : ∀ q ∈ ps, ∀ ra ∈ q.a.rows, ∀ rb ∈ q.b.rows, nocarry ra.1 rb.1 = true)
    (hY : ∀ q ∈ ps, ∀ ra ∈ q.a.rows, ∀ rb ∈ q.b.rows, ∀ t ∈ ra.2, ∀ u ∈ rb.2,
      nocarry t.1 u.1 = true) :
    evalTerms x y ps = G ps (fun μ ν => xmono x μ * xmono y ν) := by
  rw [G_spec]
  unfold evalTerms
  refine lsum_congr fun q hq => ?_
  rw [mul_assoc, evalSP, evalSP, lsum_mul_lsum, lsum_mul_left]
  refine lsum_congr fun ra hra => ?_
  rw [lsum_mul_left]
  refine lsum_congr fun rb hrb => ?_
  unfold evalRow
  rw [show (sval q.c q.neg : R) * (xmono x ra.1 * (ra.2.map fun t => (sval t.2.1 t.2.2 : R) *
      xmono y t.1).sum * (xmono x rb.1 * (rb.2.map fun t => (sval t.2.1 t.2.2 : R) * xmono y t.1).sum)) =
      ((sval q.c q.neg : R) * (xmono x ra.1 * xmono x rb.1)) *
      ((ra.2.map fun t => (sval t.2.1 t.2.2 : R) * xmono y t.1).sum *
        (rb.2.map fun t => (sval t.2.1 t.2.2 : R) * xmono y t.1).sum) by ring,
    lsum_mul_lsum, lsum_mul_left, ← xmono_add x (hX q hq ra hra rb hrb)]
  refine lsum_congr fun t ht => ?_
  rw [lsum_mul_left]
  refine lsum_congr fun u hu => ?_
  rw [xmono_add y (hY q hq ra hra rb hrb t ht u hu)]
  ring


/-- **Soundness of the checker** (two tables). If the packed normal form of `Σ_q ±c_q a_q b_q` vanishes, the
weight bound holds and the structural checks pass, then `δX δY · Σ_q ±c_q a_q(x, y) b_q(x, y) = 0` wherever `trX`
is a valid normal form at `x` and `trY` at `y`. -/
theorem sound2V (trX trY : T) (stdcX stdcY : List ℕ) (NX NY b MX MY δX δY : ℕ) (hNX : NX ≤ 2 ^ 8)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (hlY : ∀ l ∈ trY.leaves, leafOK NY b MY l = true)
    (ps : List Term) (hV : ∀ j < 2 ^ 8, (evalO2 trX trY ps).V j = 0) (hB : wsum ps * (MX * MY) < 2 ^ b)
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
  have hrows : ∀ μ, ∀ t ∈ (trX.find μ).row, t.1 < 2 ^ 8 :=
    fun μ t ht => lt_of_lt_of_le ((hLX μ).1 t ht) hNX
  obtain ⟨-, hval⟩ := evalO2_spec trY trX hrows ps
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

/-- `evalO2` is a perfect tree of depth 8 (given the slot bound of the `X`-table). -/
lemma evalO2_perfect (trX trY : T) {NX MX : ℕ} (hNX : NX ≤ 2 ^ 8)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (ps : List Term) : (evalO2 trX trY ps).Perfect 8 :=
  (evalO2_spec trY trX (fun μ t ht => lt_of_lt_of_le ((leafOKX_spec (hlX _ (trX.find_mem μ))).1 t ht) hNX)
    ps).1

/-- **Soundness of the checker** (two tables, kernel check `allZero`). -/
theorem sound2 (trX trY : T) (stdcX stdcY : List ℕ) (NX NY b MX MY δX δY : ℕ) (hNX : NX ≤ 2 ^ 8)
    (hlX : ∀ l ∈ trX.leaves, leafOKX NX MX l = true) (hlY : ∀ l ∈ trY.leaves, leafOK NY b MY l = true)
    (ps : List Term) (hO : (evalO2 trX trY ps).allZero = true) (hB : wsum ps * (MX * MY) < 2 ^ b)
    (hT : ∀ q ∈ ps, termOK2 trX trY q = true ∧ q.a.wf = true ∧ q.b.wf = true)
    (x y : Fin 9 → R) (hx : NFValid trX stdcX δX x) (hy : NFValid trY stdcY δY y) :
    ((δX : R) * δY) * evalTerms x y ps = 0 :=
  sound2V trX trY stdcX stdcY NX NY b MX MY δX δY hNX hlX hlY ps
    (AT.allZero_spec (evalO2_perfect trX trY hNX hlX ps) hO) hB hT x y hx hy

/-- **Soundness of the checker** (one table, bidegree `(d, d)`). -/
theorem sound_bidegree (tr : T) (stdc : List ℕ) (N b M δ : ℕ) (hN : N ≤ 2 ^ 8)
    (hleaf : ∀ l ∈ tr.leaves, leafOK N b M l = true) (ps : List Term)
    (hO : (evalO tr ps).allZero = true) (hB : wsum ps * M ^ 2 < 2 ^ b)
    (hT : ∀ q ∈ ps, termOK tr q = true ∧ q.a.wf = true ∧ q.b.wf = true)
    (x y : Fin 9 → R) (hx : NFValid tr stdc δ x) (hy : NFValid tr stdc δ y) :
    (δ : R) ^ 2 * evalTerms x y ps = 0 := by
  rw [sq]
  exact sound2 tr tr stdc stdc N N b M M δ δ hN (fun l hl => leafOKX_of_leafOK (hleaf l hl)) hleaf ps hO
    (by rw [← sq]; exact hB) hT x y hx hy

end Main

end LSG.Jac
