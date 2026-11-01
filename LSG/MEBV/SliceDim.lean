/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Slice
import LSG.MEBV.ModelIG

/-!
# Partial slices: primality, the dimension drop, the slice Nullstellensatz (M2.5 α; template `LSG.MEB.SliceDim`)

For a Finset `s` of blocks, `vanishP s α E` is the ideal of polynomials vanishing at the cone representatives of
the points `g ∈ E` with `ℓ_k(rep g_k) ≠ 0` (`k ∈ s`), normalised (`ℓ_k = 1`) in the blocks `k ∈ s`.

* `homP s α N P`, **`eval_homP`**; **`vanishP_isPrime`**; `vanishP_mono`, `lsl_sub_one_mem_vanishP`,
  `lsl_sub_one_notMem_vanishP`.
* **`hdim_vanishP_add_le`**: `hdim (vanishP univ α E) + m ≤ hdim (vanish E)`.
* `hom_mem_vanish_of_mem_vanishP`, `sl_vanish_le_vanishP`.
* **`radical_sl`** (slice Nullstellensatz, through the field `surjV`; the slices are `X`-only, so only points
  with nonzero `X`-parts occur): for `IGexp ≤ I`,
  `√(sl α I) = vanish' nrm (Zs α I)`.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun hdata)
open LSG.MEB (Blk)

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

open Classical in
/-- Normalise the scalings in the blocks `k ∈ s` (where `ℓ_k(rep) ≠ 0`). -/
noncomputable def nscal (s : Finset (Fin m)) (α : Alpha B) (g : GPt d₀ d₁ B)
    (lam : Fin m → ℂˣ) : Fin m → ℂˣ :=
  fun k => if h : k ∈ s ∧ lval α g k ≠ 0 then Units.mk0 (lval α g k)⁻¹ (inv_ne_zero h.2) else lam k

/-- The partially sliced vanishing ideal. -/
noncomputable def vanishP (s : Finset (Fin m)) (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  StrongSix.M2.vanish' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 (nscal s α p.1 p.2))
    {p | p.1 ∈ E ∧ ∀ k ∈ s, lval α p.1 k ≠ 0}

theorem mem_vanishP {s : Finset (Fin m)} {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanishP s α E ↔ ∀ g ∈ E, (∀ k ∈ s, lval α g k ≠ 0) → ∀ lam,
      eval (coords g (nscal s α g lam)) P = 0 := by
  rw [vanishP, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg hs lam; exact h (g, lam) ⟨hg, hs⟩
  · rintro h ⟨g, lam⟩ ⟨hg, hs⟩; exact h g hg hs lam

theorem nscal_mem {s : Finset (Fin m)} {α : Alpha B} {g : GPt d₀ d₁ B} {lam : Fin m → ℂˣ}
    {k : Fin m} (hk : k ∈ s) (hl : lval α g k ≠ 0) :
    (nscal s α g lam k : ℂ) = (lval α g k)⁻¹ := by
  simp [nscal, hk, hl]

theorem nscal_notMem {s : Finset (Fin m)} {α : Alpha B} {g : GPt d₀ d₁ B}
    {lam : Fin m → ℂˣ} {k : Fin m} (hk : k ∉ s) : nscal s α g lam k = lam k := by
  simp [nscal, hk]

theorem vanishP_empty (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    vanishP ∅ α E = vanish E := by
  ext P
  rw [mem_vanishP, mem_vanish]
  have e : ∀ (g : GPt d₀ d₁ B) lam, nscal ∅ α g lam = lam := fun g lam => by
    funext k; exact nscal_notMem (Finset.notMem_empty k)
  simp [e]

theorem vanish_le_vanishP (s : Finset (Fin m)) (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    vanish E ≤ vanishP s α E := fun _ hP =>
  mem_vanishP.mpr fun g hg _ _ => mem_vanish.mp hP g hg _

theorem vanishP_mono {s s' : Finset (Fin m)} (h : s ⊆ s') (α : Alpha B)
    (E : Set (GPt d₀ d₁ B)) : vanishP s α E ≤ vanishP s' α E := by
  intro P hP
  refine mem_vanishP.mpr fun g hg hs' lam => ?_
  have e : nscal s α g (nscal s' α g lam) = nscal s' α g lam := by
    funext k
    by_cases hk : k ∈ s
    · apply Units.ext
      rw [nscal_mem hk (hs' k (h hk)), nscal_mem (h hk) (hs' k (h hk))]
    · exact nscal_notMem hk
  rw [← e]
  exact mem_vanishP.mp hP g hg (fun k hk => hs' k (h hk)) _

theorem lsl_sub_one_mem_vanishP {s : Finset (Fin m)} {k : Fin m} (hk : k ∈ s) (α : Alpha B)
    (E : Set (GPt d₀ d₁ B)) : lsl α k - 1 ∈ vanishP s α E := by
  refine mem_vanishP.mpr fun g _ hs lam => ?_
  rw [map_sub, eval_coords_lsl, nscal_mem hk (hs k hk), map_one, inv_mul_cancel₀ (hs k hk),
    sub_self]

theorem lsl_sub_one_notMem_vanishP {s : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ s) (α : Alpha B) {E : Set (GPt d₀ d₁ B)} {g : GPt d₀ d₁ B}
    (hg : g ∈ E) (hs : ∀ k ∈ s, lval α g k ≠ 0) : lsl α k - 1 ∉ vanishP s α E := by
  classical
  intro hmem
  have hev : ∀ lam : Fin m → ℂˣ, (lam k : ℂ) * lval α g k - 1 = 0 := fun lam => by
    have := mem_vanishP.mp hmem g hg hs lam
    rwa [map_sub, eval_coords_lsl, nscal_notMem hk, map_one] at this
  by_cases h1 : lval α g k = 1
  · have := hev fun _ => Units.mk0 2 two_ne_zero
    rw [h1] at this
    norm_num at this
  · have := hev 1
    simp only [Pi.one_apply, Units.val_one, one_mul] at this
    exact h1 (sub_eq_zero.mp this)

/-! ### Homogenisation in the blocks of `s` -/

/-- The weights of the blocks in `s`. -/
def wS (s : Finset (Fin m)) : Var d₀ d₁ B → Fin m → ℕ := fun v k => if k ∈ s then wV v k else 0

/-- `homP s α N P = Σ_e (∏_{k ∈ s} ℓ_k^{N − e_k}) · P_e`. -/
noncomputable def homP (s : Finset (Fin m)) (α : Alpha B) (N : ℕ)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ e : Fin m → Fin (N + 1), (∏ k ∈ s, lsl α k ^ (N - (e k : ℕ))) *
    weightedHomogeneousComponent (wS s) (fun k => (e k : ℕ)) P

theorem weight_wS_le (s : Finset (Fin m)) (x : Var d₀ d₁ B →₀ ℕ) (k : Fin m) :
    Finsupp.weight (wS s) x k ≤ x.degree := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.degree]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, wS]
  split_ifs
  · cases v <;> simp [wV, Pi.single_apply]
    split_ifs <;> simp
  · simp

/-- `P` is the sum of its `wS`-components in the box `[0, N]^m`, `N ≥ totalDegree P`. -/
theorem sum_box_comp (s : Finset (Fin m)) {N : ℕ} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hN : P.totalDegree ≤ N) :
    ∑ e : Fin m → Fin (N + 1), weightedHomogeneousComponent (wS s) (fun k => (e k : ℕ)) P = P := by
  classical
  ext x
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hx : P.coeff x = 0
  · simp [hx]
  have hb : ∀ k, Finsupp.weight (wS s) x k < N + 1 := fun k =>
    Nat.lt_succ_of_le ((weight_wS_le s x k).trans
      ((le_totalDegree (MvPolynomial.mem_support_iff.mpr hx)).trans hN))
  let e₀ : Fin m → Fin (N + 1) := fun k => ⟨Finsupp.weight (wS s) x k, hb k⟩
  rw [Finset.sum_eq_single e₀ (fun e _ he => ite_eq_right_iff.mpr fun hw =>
      absurd (funext fun k => Fin.ext (congrFun hw k).symm) he) (by simp)]
  simp only [↓reduceIte]

/-- The scale factors `ρ_k = λ_k ℓ_k(rep g_k)` (`k ∈ s`), `1` elsewhere. -/
noncomputable def rho (s : Finset (Fin m)) (α : Alpha B) (g : GPt d₀ d₁ B)
    (lam : Fin m → ℂˣ) (k : Fin m) : ℂ :=
  if k ∈ s then (lam k : ℂ) * lval α g k else 1

theorem coords_eq_rho {s : Finset (Fin m)} {α : Alpha B} {g : GPt d₀ d₁ B}
    (hs : ∀ k ∈ s, lval α g k ≠ 0) (lam : Fin m → ℂˣ) :
    coords g lam = fun v => (∏ k, rho s α g lam k ^ wS s v k) * coords g (nscal s α g lam) v := by
  classical
  funext v
  cases v with
  | x i => simp [coords, wS, wV]
  | y j => simp [coords, wS, wV]
  | z j => simp [coords, wS, wV]
  | e k c =>
    simp only [coords, wS, wV, Pi.single_apply]
    rw [Finset.prod_eq_single k (fun b _ hb => by simp; intro _ h; exact absurd h hb) (by simp)]
    by_cases hk : k ∈ s
    · simp only [hk, ite_true, rho, pow_one, nscal_mem hk (hs k hk)]
      field_simp [hs k hk]
    · simp [hk, rho, nscal_notMem hk]

theorem eval_homP {s : Finset (Fin m)} {α : Alpha B} {N : ℕ} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hN : P.totalDegree ≤ N) {g : GPt d₀ d₁ B} (hs : ∀ k ∈ s, lval α g k ≠ 0)
    (lam : Fin m → ℂˣ) :
    eval (coords g lam) (homP s α N P) =
      (∏ k ∈ s, ((lam k : ℂ) * lval α g k) ^ N) * eval (coords g (nscal s α g lam)) P := by
  classical
  conv_rhs => rw [← sum_box_comp s hN]
  rw [homP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := wS s)
    (fun k => (e k : ℕ)) P
  rw [map_mul, map_prod, coords_eq_rho hs lam, LSG.MEB.eval_scale (wS s) (rho s α g lam) _ hh,
    ← coords_eq_rho hs lam]
  have hl : ∀ k ∈ s, eval (coords g lam) (lsl α k) = rho s α g lam k := fun k hk => by
    rw [eval_coords_lsl]; simp [rho, hk]
  rw [Finset.prod_congr rfl fun k hk => by rw [map_pow, hl k hk]]
  have hsplit : (∏ k, rho s α g lam k ^ (e k : ℕ)) = ∏ k ∈ s, rho s α g lam k ^ (e k : ℕ) := by
    rw [← Finset.prod_subset (Finset.subset_univ s) (fun k _ hk => by simp [rho, hk])]
  rw [hsplit, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hle : (e k : ℕ) ≤ N := Nat.lt_succ_iff.mp (e k).isLt
  simp only [rho, hk, ite_true]
  rw [← pow_add, Nat.sub_add_cancel hle]

/-! ### Primality and the dimension drop -/

theorem prod_lsl_notMem {s : Finset (Fin m)} {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k ∈ s, lsl α k ∉ vanish E) :
    ∏ k ∈ s, lsl (d₀ := d₀) (d₁ := d₁) α k ∉ vanish E := by
  intro h
  obtain ⟨k, hk, hk'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
  exact hℓ k hk hk'

theorem homP_mem_vanish_iff {s : Finset (Fin m)} {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    {N : ℕ} {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hN : P.totalDegree ≤ N)
    (hhP : homP s α N P ∈ vanish E) :
    P ∈ vanishP s α E := by
  refine mem_vanishP.mpr fun g hg hs lam => ?_
  have h0 := mem_vanish.mp hhP g hg lam
  rw [eval_homP hN hs lam] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (hs k hk))

/-- **Partial slices of irreducible sets are irreducible.** -/
theorem vanishP_isPrime {s : Finset (Fin m)} {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k ∈ s, lsl α k ∉ vanish E) {g₀ : GPt d₀ d₁ B}
    (hg₀ : g₀ ∈ E) (hs₀ : ∀ k ∈ s, lval α g₀ k ≠ 0) : (vanishP s α E).IsPrime := by
  classical
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanishP s α E := htop ▸ Submodule.mem_top
    have := mem_vanishP.mp h1 g₀ hg₀ hs₀ 1
    simp at this
  set NP := P.totalDegree
  set NQ := Q.totalDegree
  have hmem : homP s α NP P * homP s α NQ Q * ∏ k ∈ s, lsl (d₀ := d₀) (d₁ := d₁) α k ∈
      vanish E := by
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [map_mul, map_mul, map_prod]
    by_cases hs : ∀ k ∈ s, lval α g k ≠ 0
    · rw [eval_homP le_rfl hs lam, eval_homP le_rfl hs lam]
      have := mem_vanishP.mp hPQ g hg hs lam
      rw [map_mul] at this
      rcases mul_eq_zero.mp this with h | h <;> simp [h]
    · push_neg at hs
      obtain ⟨k, hk, hk0⟩ := hs
      rw [Finset.prod_eq_zero hk (by rw [eval_coords_lsl, hk0, mul_zero]), mul_zero]
  rcases hp.mem_or_mem hmem with h | h
  · rcases hp.mem_or_mem h with h' | h'
    · exact Or.inl (homP_mem_vanish_iff le_rfl h')
    · exact Or.inr (homP_mem_vanish_iff le_rfl h')
  · exact absurd h (prod_lsl_notMem hp hℓ)

/-- **The dimension drop**: `hdim (vanishP s α E) + #s ≤ hdim (vanish E)`. -/
theorem hdim_vanishP_add_le (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {α : Alpha B} {E : Set (GPt d₀ d₁ B)} (hp : (vanish E).IsPrime)
    (hℓ : ∀ k, lsl α k ∉ vanish E) {g₀ : GPt d₀ d₁ B} (hg₀ : g₀ ∈ E)
    (hs₀ : ∀ k, lval α g₀ k ≠ 0) (s : Finset (Fin m)) :
    (hdata blk D ℂ (vanishP s α E)).1 + s.card ≤ (hdata blk D ℂ (vanish E)).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vanishP_empty]
  | insert k s hk ih =>
    have hpr := vanishP_isPrime hp (fun k _ => hℓ k) hg₀ (s := s) (fun k _ => hs₀ k)
    have hpr' := vanishP_isPrime hp (fun k _ => hℓ k) hg₀ (s := insert k s) (fun k _ => hs₀ k)
    have hlt := StrongSix.M2.hdim_section_lt blk D ℂ hD (J := vanishP s α E)
      (L := vanishP (insert k s) α E) (P := lsl α k - 1)
      (fun Q hQ => (hpr.mem_or_mem hQ).resolve_left
        (lsl_sub_one_notMem_vanishP hk α hg₀ fun k _ => hs₀ k))
      (sup_le (vanishP_mono (Finset.subset_insert k s) α E)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (lsl_sub_one_mem_vanishP (Finset.mem_insert_self k s) α E))))
      hpr'.ne_top
    rw [Finset.card_insert_of_notMem hk]
    omega

/-- Multihomogeneous elements of `vanishP univ α E` lie in `vanish E`. -/
theorem hom_mem_vanish_of_mem_vanishP {α : Alpha B} {E : Set (GPt d₀ d₁ B)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wV Q d)
    (hQs : Q ∈ vanishP Finset.univ α E) : Q ∈ vanish E := by
  classical
  have hmul : Q * ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ∈ vanish E := by
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [map_mul, map_prod]
    by_cases h0 : ∃ k, lval α g k = 0
    · obtain ⟨k, hk⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_coords_lsl, hk, mul_zero]),
        mul_zero]
    push_neg at h0
    have hn := mem_vanishP.mp hQs g hg (fun k _ => h0 k) lam
    rw [eval_coords_eq_zero_iff hQ g _ lam] at hn
    rw [hn, zero_mul]
  exact (hp.mem_or_mem hmul).resolve_right (prod_lsl_notMem hp fun k _ => hℓ k)

theorem sl_vanish_le_vanishP (α : Alpha B) (E : Set (GPt d₀ d₁ B)) :
    sl α (vanish E) ≤ vanishP Finset.univ α E :=
  sup_le (vanish_le_vanishP _ α E) (Ideal.span_le.mpr (by
    rintro _ ⟨k, rfl⟩; exact lsl_sub_one_mem_vanishP (Finset.mem_univ k) α E))

/-! ### The slice Nullstellensatz -/

/-- The points with all `ℓ_k(rep) ≠ 0` at whose normalised representative `I` vanishes. -/
def Zs (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) : Set (GPt d₀ d₁ B) :=
  {g | (∀ k, lval α g k ≠ 0) ∧ ∀ P ∈ I, eval (nrm α g) P = 0}

/-- A zero of `IGexp` with nonzero `X`-parts in every block is a cone representative (the field `surjV`). -/
theorem exists_coords_of_IGexp {a : Var d₀ d₁ B → ℂ} (ha : ∀ P ∈ IGexp d₀ d₁ B, eval a P = 0)
    (hne : ∀ k, (fun c : Fin (B k).N => a (.e k (Sum.inl c))) ≠ 0) :
    ∃ (g : GPt d₀ d₁ B) (ν : Fin m → ℂˣ), a = coords g ν := by
  obtain ⟨g, ν, rfl⟩ := exists_coordsZ_of_IGexp ha fun k _ => hne k
  have hν : ∀ k, ν k ≠ 0 := fun k h0 => hne k (by funext c; simp [coordsZ, h0])
  exact ⟨g, fun k => Units.mk0 (ν k) (hν k), by rw [coords_eq_coordsZ]; rfl⟩

theorem sl_le_vanish_Zs (α : Alpha B) (I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    sl α I ≤ StrongSix.M2.vanish' (nrm α) (Zs (d₀ := d₀) (d₁ := d₁) α I) := by
  refine sup_le (fun P hP => (StrongSix.M2.mem_vanish' _).mpr fun g hg => hg.2 P hP)
    (Ideal.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
  rw [map_sub, nrm, eval_coords_lsl]
  simp [hg.1 k]

/-- **The slice Nullstellensatz**: for `IGexp ≤ I`, `√(sl α I) = I(Zs α I)` (normalised points). -/
theorem radical_sl (α : Alpha B) {I : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)}
    (hI : IGexp d₀ d₁ B ≤ I) :
    (sl α I).radical = StrongSix.M2.vanish' (nrm α) (Zs (d₀ := d₀) (d₁ := d₁) α I) := by
  classical
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  ext P
  rw [mem_vanishingIdeal_iff, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg
    refine h (nrm α g) ?_
    rw [mem_zeroLocus_iff]
    intro p hp
    exact (StrongSix.M2.mem_vanish' _).mp (sl_le_vanish_Zs α I hp) g hg
  · intro h x hx
    rw [mem_zeroLocus_iff] at hx
    have hxI : ∀ p ∈ sl α I, eval x p = 0 := hx
    have hl : ∀ k, eval x (lsl α k) = 1 := fun k => by
      have := hxI _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
      rwa [map_sub, map_one, sub_eq_zero] at this
    have hne : ∀ k, (fun c : Fin (B k).N => x (.e k (Sum.inl c))) ≠ 0 := fun k h0 => by
      have := hl k
      rw [eval_lsl] at this
      simp only [show ∀ c, x (.e k (Sum.inl c)) = 0 from fun c => congrFun h0 c, mul_zero,
        Finset.sum_const_zero] at this
      exact zero_ne_one this
    obtain ⟨g, ν, rfl⟩ := exists_coords_of_IGexp
      (fun p hp => hxI p (Ideal.mem_sup_left (hI hp))) hne
    have hlv : ∀ k, (ν k : ℂ) * lval α g k = 1 := fun k => by
      rw [← eval_coords_lsl]; exact hl k
    have hlv0 : ∀ k, lval α g k ≠ 0 := fun k h0 => by
      have := hlv k; rw [h0, mul_zero] at this; exact zero_ne_one this
    have hν : coords g ν = nrm α g := by
      unfold nrm
      congr 1
      funext k
      apply Units.ext
      simp only [hlv0 k, ↓reduceDIte, Units.val_mk0]
      exact eq_inv_of_mul_eq_one_left (hlv k)
    have hg : g ∈ Zs (d₀ := d₀) (d₁ := d₁) α I :=
      ⟨hlv0, fun p hp => by rw [← hν]; exact hxI p (Ideal.mem_sup_left hp)⟩
    have := h g hg
    rw [← hν] at this
    exact this

end LSG.MEBV
