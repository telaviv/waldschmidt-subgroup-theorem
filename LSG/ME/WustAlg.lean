import Mathlib
import StrongSix.M2.WustholzGen
import LSG.ME.Order

/-!
# Wüstholz's lemma with a multiplier (generalised Roy Lemma 8.16, Thm 8.18)

In the multi-cone model `J = vanish E` is homogeneous in each elliptic block and the chart
derivations raise elliptic degrees, so Roy's hypothesis `Dᵢ Qⱼ ≡ δᵢⱼ (mod J)` cannot hold. We
replace it by

  `Dᵢ Qⱼ − δᵢⱼ · M ∈ J`, with `M` a **non-zero-divisor modulo `J`** (`M x ∈ J → x ∈ J`).

The proofs are those of StrongSix (`DL_qprod_off/diag`, `indep_mod`, `wustholz_count'`,
`wustholz'`) with `P` replaced by `M · P` at each derivation step; the diagonal constant becomes
`c · M^{|l|}`, which is cancelled using the non-zero-divisor hypothesis. The degree shift `S₀ c₀`
is unchanged (`M` never enters the products `P · Q^m`).

* `Dv_qprodM`, `DL_qprod_offM`, `DL_qprod_diagM`, `indep_modM`.
* **`wustholz_countM'`**, **`wustholzM'`**: `(k+1)^ℓ · H(J; t) ≤ H(A; t + S₀ c₀)` (any block
  structure, any derivations `Derivation K K[σ] K[σ]`, words, no commutativity).
* **`glue`**: gluing transversal data on finitely many primes `p_k` (one per coset) with
  separators `B_k ∈ ⋂_{k' ≠ k} p_{k'} \ p_k`: `D = Σ B_k • D_k`, `Q = Σ B_k² T_k`, `M = Σ B_k³ N_k`.
* `nzd_of_primes`: an element outside each of finitely many primes is a non-zero-divisor modulo
  their intersection.
* `DL_glued_mem`: words in glued derivations `Σ f_k • Dv (e_k)` (`e_k ∈ Ws`) of length `≤ n` map
  `VOg Dv Ws J n` into `J` (order of vanishing transfers to the glued derivations).
-/

open MvPolynomial Module Submodule
open StrongSix.M2 (DL DL_nil DL_cons DL_pow_mem qprod qprod_zero qprod_cons qprod_mem FLE hfun
  mul_mem_FLE FLE_mono qprod_mem_FLE' mem_of_natCast_mul_mem)

namespace LSG.ME

section Generic

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {ι : Type*} [DecidableEq ι]
  (Dv : ι → Derivation K R R) {J : Ideal R} {Q : ι → R} {M : R}

/-- `Dᵢ Q^m ≡ (mult. of i in m) · M · Q^{m − i} (mod J^{|m|})`. -/
theorem Dv_qprodM (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (i : ι) (m : Multiset ι) :
    Dv i (qprod Q m) - (m.count i : R) * M * qprod Q (m.erase i) ∈ J ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp [qprod_zero]
  | cons a m ih =>
    have hsplit : Dv i (qprod Q (a ::ₘ m)) -
        ((a ::ₘ m).count i : R) * M * qprod Q ((a ::ₘ m).erase i) =
        Q a * (Dv i (qprod Q m) - (m.count i : R) * M * qprod Q (m.erase i)) +
          qprod Q m * (Dv i (Q a) - if i = a then M else 0) := by
      rw [qprod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      by_cases h : i = a
      · subst h
        rw [Multiset.count_cons_self, Multiset.erase_cons_head,
          ite_eq_left_of_eq_true _ _ (eq_self i)]
        by_cases hc : m.count i = 0
        · rw [hc]; push_cast; ring
        · have : qprod Q m = Q i * qprod Q (m.erase i) := by
            conv_lhs => rw [← Multiset.cons_erase (Multiset.count_ne_zero.mp hc)]
            exact qprod_cons Q i _
          rw [this]; push_cast; ring
      · rw [Multiset.count_cons_of_ne h, Multiset.erase_cons_tail m (Ne.symm h), qprod_cons,
          ite_eq_right_of_eq_false _ _ (eq_false h)]
        ring
    rw [hsplit, Multiset.card_cons]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']; exact Ideal.mul_mem_mul (hQ a) ih
    · rw [pow_succ]; exact Ideal.mul_mem_mul (qprod_mem J hQ m) (hδ i a)

theorem Dv_mul_qprodM (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J) (i : ι) (m : Multiset ι) (P : R) :
    Dv i (P * qprod Q m) - ((m.count i : R) * M * P) * qprod Q (m.erase i) ∈
      J ^ Multiset.card m := by
  have e : Dv i (P * qprod Q m) - ((m.count i : R) * M * P) * qprod Q (m.erase i) =
      P * (Dv i (qprod Q m) - (m.count i : R) * M * qprod Q (m.erase i)) +
        qprod Q m * Dv i P := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Dv_qprodM Dv hQ hδ i m))
    (Ideal.mul_mem_right _ _ (qprod_mem J hQ m))

/-- **Roy Lemma 8.16 with a multiplier, off-diagonal.** -/
theorem DL_qprod_offM (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J) (l : List ι) :
    ∀ (m : Multiset ι) (P : R), l.length ≤ Multiset.card m → (l : Multiset ι) ≠ m →
      DL Dv l (P * qprod Q m) ∈ J := by
  induction l with
  | nil =>
    intro m P _ hne
    have hm : Multiset.card m ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h ▸ rfl)
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_self hm (qprod_mem J hQ m))
  | cons i l ih =>
    intro m P hlen hne
    rw [List.length_cons] at hlen
    rw [DL_cons]
    have hs' : DL Dv l (Dv i (P * qprod Q m) -
        ((m.count i : R) * M * P) * qprod Q (m.erase i)) ∈ J := by
      have := DL_pow_mem Dv J l (Multiset.card m - l.length)
        (x := Dv i (P * qprod Q m) - ((m.count i : R) * M * P) * qprod Q (m.erase i))
        (by rw [Nat.sub_add_cancel (by omega)]; exact Dv_mul_qprodM Dv hQ hδ i m P)
      exact Ideal.pow_le_self (by omega) this
    have hmain : DL Dv l (((m.count i : R) * M * P) * qprod Q (m.erase i)) ∈ J := by
      by_cases hc : m.count i = 0
      · rw [hc]; simp
      · have him : i ∈ m := Multiset.count_ne_zero.mp hc
        refine ih _ _ ?_ ?_
        · rw [Multiset.card_erase_of_mem him, Nat.pred_eq_sub_one]; omega
        · intro h
          apply hne
          rw [← Multiset.cons_coe, h, Multiset.cons_erase him]
    have := Ideal.add_mem _ hmain hs'
    rwa [map_sub, add_sub_cancel] at this

/-- **Roy Lemma 8.16 with a multiplier, diagonal.** -/
theorem DL_qprod_diagM (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J) (l : List ι) :
    ∃ c : ℕ, c ≠ 0 ∧ ∀ P : R, DL Dv l (P * qprod Q l) - (c : R) * M ^ l.length * P ∈ J := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun P => by simp [qprod_zero]⟩
  | cons i l ih =>
    obtain ⟨c, hc, hcP⟩ := ih
    refine ⟨c * ((l : Multiset ι).count i + 1), Nat.mul_ne_zero hc (Nat.succ_ne_zero _),
      fun P => ?_⟩
    rw [DL_cons]
    have hs := Dv_mul_qprodM Dv hQ hδ i (i :: l : Multiset ι) P
    rw [← Multiset.cons_coe, Multiset.count_cons_self, Multiset.erase_cons_head,
      Multiset.card_cons] at hs
    have hs' := DL_pow_mem Dv J l 1 (by rw [add_comm]; exact hs)
    rw [pow_one] at hs'
    have h1 := hcP ((((l : Multiset ι).count i + 1 : ℕ) : R) * M * P)
    rw [← Multiset.cons_coe]
    have := Ideal.add_mem _ h1 hs'
    rw [map_sub] at this
    convert this using 1
    rw [List.length_cons]
    push_cast
    ring

theorem mem_of_pow_mul_mem (hM : ∀ x, M * x ∈ J → x ∈ J) :
    ∀ (n : ℕ) {x : R}, M ^ n * x ∈ J → x ∈ J := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact hM x (ih (by rwa [pow_succ, mul_assoc] at hx))

/-- **Independence modulo `A`, with a multiplier.** -/
theorem indep_modM [CharZero K] (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J) (hM : ∀ x, M * x ∈ J → x ∈ J)
    {A : Ideal R} {S0 : ℕ} (hA : ∀ x ∈ A, ∀ l : List ι, l.length ≤ S0 → DL Dv l x ∈ J)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (idx : κ → Multiset ι) (hidx : Function.Injective idx)
    (hcard : ∀ a, Multiset.card (idx a) ≤ S0) (f : κ → R) (hfJ : ∀ a, f a ∈ J → f a = 0)
    (hsum : ∑ a, f a * qprod Q (idx a) ∈ A) : ∀ a, f a = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hnon : (Finset.univ.filter fun a => f a ≠ 0).Nonempty := by
    obtain ⟨a, ha⟩ := hne; exact ⟨a, by simpa using ha⟩
  obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image _ (fun a => Multiset.card (idx a)) hnon
  have ha0' : f a0 ≠ 0 := (Finset.mem_filter.mp ha0).2
  set l := (idx a0).toList with hl
  have hlc : (l : Multiset ι) = idx a0 := Multiset.coe_toList _
  have hll : l.length = Multiset.card (idx a0) := Multiset.length_toList _
  have htot := hA _ hsum l (hll ▸ hcard a0)
  rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at htot
  have hrest : ∑ a ∈ Finset.univ.erase a0, DL Dv l (f a * qprod Q (idx a)) ∈ J := by
    refine Ideal.sum_mem _ fun a ha => ?_
    by_cases hfa : f a = 0
    · rw [hfa, zero_mul, map_zero]; exact J.zero_mem
    · refine DL_qprod_offM Dv hQ hδ l _ _ ?_ ?_
      · rw [hll]; exact hmin a (by simpa using hfa)
      · rw [hlc]; exact fun h => (Finset.mem_erase.mp ha).1 (hidx h).symm
  have h0 : DL Dv l (f a0 * qprod Q (idx a0)) ∈ J := by
    have := J.sub_mem htot hrest
    rwa [add_sub_cancel_right] at this
  obtain ⟨c, hc, hcP⟩ := DL_qprod_diagM Dv hQ hδ l
  have := J.sub_mem h0 (hcP (f a0))
  rw [hlc, sub_sub_cancel, mul_assoc] at this
  exact ha0' (hfJ a0 (mem_of_pow_mul_mem hM _ (mem_of_natCast_mul_mem (K := K) hc this)))

end Generic

/-! ### The count in `K[σ]` -/

section CountGen

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K]

/-- **Wüstholz's lemma with a multiplier, counting form** (any block structure `β : σ → ι`). -/
theorem wustholz_countM' (β : σ → ι) (D : ι → ℕ) {κ : Type*} [DecidableEq κ]
    (Dv : κ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    {A J : Ideal (MvPolynomial σ K)} {Q : κ → MvPolynomial σ K} {M : MvPolynomial σ K}
    (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (hM : ∀ x, M * x ∈ J → x ∈ J) {c0 : ℕ}
    (hQdeg : ∀ j, Q j ∈ FLE K β (c0 • D)) {S0 : ℕ}
    (hA : ∀ x ∈ A, ∀ l : List κ, l.length ≤ S0 → DL Dv l x ∈ J)
    {α : Type*} [Fintype α] [DecidableEq α] (idx : α → Multiset κ) (hidx : Function.Injective idx)
    (hcard : ∀ a, Multiset.card (idx a) ≤ S0) (t : ℕ) :
    Fintype.card α * hfun β D K J t ≤ hfun β D K A (t + S0 * c0) := by
  classical
  set F := FLE K β (t • D) with hF
  set F' := FLE K β ((t + S0 * c0) • D) with hF'
  set p := J.restrictScalars K ⊓ F with hp
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  set E := q ⊓ F with hE
  have : FiniteDimensional K p := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional K E := Submodule.finiteDimensional_of_le inf_le_right
  have hpE : p ⊓ E = ⊥ := eq_bot_iff.mpr fun x hx =>
    hq.disjoint.le_bot ⟨hx.1, hx.2.1⟩
  have hpE' : p ⊔ E = F := by
    rw [hE, ← sup_inf_assoc_of_le q (inf_le_right : p ≤ F), hq.sup_eq_top, top_inf_eq]
  have hdimE : finrank K E = hfun β D K J t := by
    have := Submodule.finrank_sup_add_finrank_inf_eq p E
    rw [hpE, hpE', finrank_bot] at this
    change _ = finrank K F - finrank K p
    omega
  let Ψ : (α → E) →ₗ[K] MvPolynomial σ K := ∑ a, (LinearMap.mulRight K (qprod Q (idx a))) ∘ₗ
    E.subtype ∘ₗ LinearMap.proj a
  have hΨ : ∀ f, Ψ f = ∑ a, (f a : MvPolynomial σ K) * qprod Q (idx a) := fun f => by
    simp [Ψ, LinearMap.sum_apply]
  have hEJ : ∀ x : E, (x : MvPolynomial σ K) ∈ J → (x : MvPolynomial σ K) = 0 := fun x hx =>
    (Submodule.mem_bot K).mp (hpE ▸ ⟨⟨hx, x.2.2⟩, x.2⟩)
  have hzero : ∀ f, Ψ f ∈ A → f = 0 := fun f hf => by
    have := indep_modM Dv hQ hδ hM hA idx hidx hcard (fun a => (f a : MvPolynomial σ K))
      (fun a => hEJ (f a)) (hΨ f ▸ hf)
    funext a; exact Subtype.ext (this a)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    exact (Submodule.mem_bot K).mpr (hzero f (by rw [LinearMap.mem_ker.mp hf]; exact A.zero_mem))
  set U := LinearMap.range Ψ
  have hUF' : U ≤ F' := by
    rintro _ ⟨f, rfl⟩
    rw [hΨ]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : (f a : MvPolynomial σ K) ∈ F := (f a).2.2
    have h2 := qprod_mem_FLE' hQdeg (idx a)
    have h3 := mul_mem_FLE K h1 h2
    rw [← add_smul] at h3
    exact FLE_mono K β (fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have := hcard a; nlinarith)) h3
  have : FiniteDimensional K U := Submodule.finiteDimensional_of_le hUF'
  set X := A.restrictScalars K ⊓ F'
  have : FiniteDimensional K X := Submodule.finiteDimensional_of_le inf_le_right
  have hUX : U ⊓ X = ⊥ := eq_bot_iff.mpr fun x ⟨⟨f, hf⟩, hxA, _⟩ => by
    subst hf; rw [hzero f hxA, map_zero]; exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U X
  rw [hUX, finrank_bot, add_zero] at hsum
  have hle : finrank K ↥(U ⊔ X) ≤ finrank K F' :=
    Submodule.finrank_mono (sup_le hUF' inf_le_right)
  have hU : finrank K U = Fintype.card α * finrank K E := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hA' : hfun β D K A (t + S0 * c0) = finrank K F' - finrank K X := rfl
  rw [hA', ← hdimE]
  omega

/-- **Wüstholz's lemma with a multiplier** (Roy Thm 8.18 generalised): the box `{0..k}^ℓ`. -/
theorem wustholzM' (β : σ → ι) (D : ι → ℕ) {ℓ : ℕ}
    (Dv : Fin ℓ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    {A J : Ideal (MvPolynomial σ K)} {Q : Fin ℓ → MvPolynomial σ K} {M : MvPolynomial σ K}
    (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (hM : ∀ x, M * x ∈ J → x ∈ J) {c0 : ℕ}
    (hQdeg : ∀ j, Q j ∈ FLE K β (c0 • D)) {S0 k : ℕ} (hk : ℓ * k ≤ S0)
    (hA : ∀ x ∈ A, ∀ l : List (Fin ℓ), l.length ≤ S0 → DL Dv l x ∈ J) (t : ℕ) :
    (k + 1) ^ ℓ * hfun β D K J t ≤ hfun β D K A (t + S0 * c0) := by
  classical
  let idx : (Fin ℓ → Fin (k + 1)) → Multiset (Fin ℓ) := fun a => ∑ i, (a i : ℕ) • {i}
  have hcount : ∀ a j, (idx a).count j = a j := by
    intro a j
    simp only [idx, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
    simp
  have hidx : Function.Injective idx := fun a b h => funext fun j => Fin.ext (by
    rw [← hcount a j, ← hcount b j, h])
  have hcard : ∀ a, Multiset.card (idx a) ≤ S0 := by
    intro a
    have : Multiset.card (idx a) = ∑ i, (a i : ℕ) := by
      simp only [idx, Multiset.card_sum, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
    rw [this]
    calc ∑ i, (a i : ℕ) ≤ ∑ _i : Fin ℓ, k := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (a i).2
      _ = ℓ * k := by simp
      _ ≤ S0 := hk
  have := wustholz_countM' β D Dv hQ hδ hM hQdeg hA idx hidx hcard t
  simpa using this

end CountGen

/-! ### Gluing transversal data over finitely many primes -/

section Glue

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

theorem derivation_sum_apply {κ : Type*} (s : Finset κ) (f : κ → Derivation K R R) (x : R) :
    (∑ k ∈ s, f k) x = ∑ k ∈ s, f k x := by
  simp

/-- An element outside each of finitely many primes is a non-zero-divisor modulo their
intersection. -/
theorem nzd_of_primes {κ : Type*} (s : Finset κ) (p : κ → Ideal R) (hp : ∀ k ∈ s, (p k).IsPrime)
    {M : R} (hM : ∀ k ∈ s, M ∉ p k) (x : R) (hx : M * x ∈ ⨅ k ∈ s, p k) : x ∈ ⨅ k ∈ s, p k := by
  simp only [Submodule.mem_iInf] at hx ⊢
  intro k hk
  exact ((hp k hk).mem_or_mem (hx k hk)).resolve_left (hM k hk)

/-- **Gluing** (Roy Lemma 8.15, projective form). Transversal data `(D_k, T_k, N_k)` modulo the
prime `p_k` for each `k ∈ s`, and separators `B_k ∉ p_k`, `B_k ∈ p_{k'}` (`k' ≠ k`), give
`D = Σ B_k • D_k`, `Q = Σ B_k² T_k`, `M = Σ B_k³ N_k` with `Q ∈ p_{k'}`,
`D_i Q_j − δᵢⱼ M ∈ p_{k'}` and `M ∉ p_{k'}` for all `k' ∈ s`. -/
theorem glue {κ ι : Type*} [DecidableEq ι] (s : Finset κ) (p : κ → Ideal R)
    (hp : ∀ k ∈ s, (p k).IsPrime) (Dk : κ → ι → Derivation K R R) (T : κ → ι → R) (N B : κ → R)
    (hT : ∀ k ∈ s, ∀ j, T k j ∈ p k)
    (hTδ : ∀ k ∈ s, ∀ i j, Dk k i (T k j) - (if i = j then N k else 0) ∈ p k)
    (hN : ∀ k ∈ s, N k ∉ p k) (hB : ∀ k ∈ s, B k ∉ p k)
    (hBo : ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → B k ∈ p k') (k' : κ) (hk' : k' ∈ s) :
    (∀ j, (∑ k ∈ s, B k ^ 2 * T k j) ∈ p k') ∧
    (∀ i j, (∑ k ∈ s, B k • Dk k i) (∑ k ∈ s, B k ^ 2 * T k j) -
      (if i = j then ∑ k ∈ s, B k ^ 3 * N k else 0) ∈ p k') ∧
    (∑ k ∈ s, B k ^ 3 * N k) ∉ p k' := by
  classical
  have : (p k').IsPrime := hp k' hk'
  set π := Ideal.Quotient.mk (p k')
  have hz : ∀ {x}, x ∈ p k' ↔ π x = 0 := fun {x} => (Ideal.Quotient.eq_zero_iff_mem).symm
  have hBz : ∀ k ∈ s, k ≠ k' → π (B k) = 0 := fun k hk hne => hz.mp (hBo k hk k' hk' hne)
  have hTz : ∀ j, π (T k' j) = 0 := fun j => hz.mp (hT k' hk' j)
  have hTδz : ∀ i j, π (Dk k' i (T k' j)) = if i = j then π (N k') else 0 := by
    intro i j
    have := hz.mp (hTδ k' hk' i j)
    rw [map_sub, sub_eq_zero] at this
    rw [this]; split_ifs <;> simp
  -- `π (D (B² T)) = π(B)² π(D T) + 2 π(B) π(T) π(D B)`
  have hD : ∀ (D : Derivation K R R) (b t : R),
      π (D (b ^ 2 * t)) = π b ^ 2 * π (D t) + 2 * π b * π t * π (D b) := by
    intro D b t
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast]
    norm_num; ring
  have hsingle : ∀ (f : κ → R), (∀ k ∈ s, k ≠ k' → π (f k) = 0) →
      π (∑ k ∈ s, f k) = π (f k') := by
    intro f hf
    rw [map_sum, Finset.sum_eq_single k' (fun k hk hne => hf k hk hne) (fun h => absurd hk' h)]
  refine ⟨fun j => hz.mpr ?_, fun i j => hz.mpr ?_, fun hmem => ?_⟩
  · rw [hsingle _ (fun k hk hne => by rw [map_mul, map_pow, hBz k hk hne]; ring), map_mul,
      hTz, mul_zero]
  · have hQ : ∀ D : Derivation K R R,
        π (D (∑ k ∈ s, B k ^ 2 * T k j)) = π (B k') ^ 2 * π (D (T k' j)) := by
      intro D
      rw [map_sum, hsingle (fun k => D (B k ^ 2 * T k j)) (fun k hk hne => by
        rw [hD, hBz k hk hne]; ring), hD, hTz]
      ring
    have hL : π ((∑ k ∈ s, B k • Dk k i) (∑ k ∈ s, B k ^ 2 * T k j)) =
        π (B k') ^ 3 * (if i = j then π (N k') else 0) := by
      rw [derivation_sum_apply]
      simp only [Derivation.smul_apply, smul_eq_mul]
      rw [hsingle (fun k => B k * (Dk k i) (∑ k ∈ s, B k ^ 2 * T k j)) (fun k hk hne => by
        rw [map_mul, hBz k hk hne, zero_mul]), map_mul, hQ, hTδz]
      ring
    rw [map_sub, hL]
    split_ifs
    · rw [hsingle (fun k => B k ^ 3 * N k) (fun k hk hne => by
        rw [map_mul, map_pow, hBz k hk hne]; ring)]
      simp [map_mul, map_pow]
    · simp
  · have h1 := hz.mp hmem
    rw [hsingle (fun k => B k ^ 3 * N k) (fun k hk hne => by
      rw [map_mul, map_pow, hBz k hk hne]; ring), map_mul, map_pow] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact hB k' hk' (hz.mpr (pow_eq_zero_iff (by norm_num) |>.mp h))
    · exact hN k' hk' (hz.mpr h)

end Glue

/-! ### Orders of vanishing for glued derivations -/

section Glued

variable {K : Type*} [Field K] {R ι : Type*} [CommRing R] [Algebra K R]
  {Dv : ι → Derivation K R R} {Ws : Set ι} {J : Ideal R}

/-- A derivation `Σ_{k ∈ s} f_k • Dv (e_k)` with all `e_k ∈ Ws` lowers the order by one. -/
theorem glued_mem_VOg {κ : Type*} (s : Finset κ) (f : κ → R) (e : κ → ι) (he : ∀ k ∈ s, e k ∈ Ws)
    {n : ℕ} {x : R} (hx : x ∈ VOg Dv Ws J (n + 1)) :
    (∑ k ∈ s, f k • Dv (e k)) x ∈ VOg Dv Ws J n := by
  rw [derivation_sum_apply]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Derivation.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ ((mem_VOg_succ.mp hx).2 _ (he k hk))

/-- **Words in glued derivations.** If each `D' i` lowers the order by one, then words of length
`≤ n` in the `D' i` map `VOg Dv Ws J n` into `J`. -/
theorem DL_glued_mem {κ : Type*} (D' : κ → Derivation K R R)
    (hD' : ∀ i (n : ℕ) x, x ∈ VOg Dv Ws J (n + 1) → D' i x ∈ VOg Dv Ws J n) :
    ∀ (l : List κ) {n : ℕ} {x : R}, x ∈ VOg Dv Ws J n → l.length ≤ n → DL D' l x ∈ J := by
  intro l
  induction l with
  | nil => intro n x hx _; exact VOg_le n hx
  | cons i l ih =>
    intro n x hx hl
    rw [DL_cons]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hl; omega⟩
    exact ih (hD' i n' x hx) (by simpa using hl)

end Glued

end LSG.ME
