import Mathlib
import LSG.MEV.Blk4
import LSG.MEV.SubgroupHilbV3

/-!
# A 3-block lower bound for the linear group `h₀ × T_U` (STAGE5_MEV §10.3)

The analogue of StrongSix's `exists_indep_restr` / `hfun_prodSet_ge` for the grading
`(leading x | trailing x | y)` of `G_a^{d₀ + r} × G_m^{d₁}`: for `h₀ ⊆ ℂ^{d₀+r}` with
`t₀ = dim leadL(h₀)` (`leadL` = the first `d₀` coordinates) and `j = dim (h₀ ∩ ker leadL)`, there
are

  `(N₀/t₀ + 1)^{t₀} (N₂/j + 1)^j (N₁/s + 1)^s`, `s = d₁ − dim U`,

polynomials of degrees `≤ N₀` in the leading, `≤ N₂` in the trailing and `≤ N₁` in the `y`
variables which are linearly independent modulo `I(h₀ × T_U)`.

* `exists_lin_surj`: coordinates — `t₀` leading coordinates and `j` trailing coordinates which are
  jointly surjective on `h₀`.
* **`exists_lin_family4`**: the family (monomials in these coordinates times torus characters;
  Dedekind's lemma as in StrongSix).
-/

open MvPolynomial Module

namespace LSG.MEV

noncomputable section

variable {d₀ r d₁ m : ℕ}

/-- The leading `d₀` coordinates. -/
def leadL : (Fin (d₀ + r) → ℂ) →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.funLeft ℂ ℂ (Fin.castAdd r)

@[simp] theorem leadL_apply (x : Fin (d₀ + r) → ℂ) (i : Fin d₀) :
    leadL x i = x (Fin.castAdd r i) := rfl

/-- **Leading and trailing coordinates on `h₀`.** -/
theorem exists_lin_surj (h0 : Submodule ℂ (Fin (d₀ + r) → ℂ)) :
    ∃ (ιL : Fin (finrank ℂ (h0.map (leadL (d₀ := d₀) (r := r)))) → Fin d₀)
      (ιT : Fin (finrank ℂ ↥(h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r)))) → Fin (d₀ + r)),
      (∀ k, d₀ ≤ (ιT k : ℕ)) ∧
      ∀ (s : Fin (finrank ℂ (h0.map (leadL (d₀ := d₀) (r := r)))) → ℂ)
        (s' : Fin (finrank ℂ ↥(h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r)))) → ℂ),
        ∃ x ∈ h0, (∀ l, x (Fin.castAdd r (ιL l)) = s l) ∧ ∀ k, x (ιT k) = s' k := by
  classical
  obtain ⟨ιL, -, hsL⟩ := LSG.ME.exists_coord_surj (h0.map (leadL (d₀ := d₀) (r := r)))
  obtain ⟨ιT, -, hsT⟩ :=
    LSG.ME.exists_coord_surj (h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r)))
  refine ⟨ιL, ιT, fun k => ?_, fun s s' => ?_⟩
  · by_contra hk
    push Not at hk
    obtain ⟨z, hz, hz1⟩ := hsT (Pi.single k 1)
    have h0' : z (ιT k) = 0 := by
      have := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2) ⟨ιT k, hk⟩
      rw [leadL_apply] at this
      exact this
    have := hz1 k
    rw [h0'] at this
    simp at this
  · obtain ⟨z, ⟨x₁, hx₁, rfl⟩, hz⟩ := hsL s
    obtain ⟨x₂, hx₂, hx₂'⟩ := hsT fun k => s' k - x₁ (ιT k)
    obtain ⟨hx₂h, hx₂k⟩ := Submodule.mem_inf.mp hx₂
    refine ⟨x₁ + x₂, h0.add_mem hx₁ hx₂h, fun l => ?_, fun k => ?_⟩
    · have e1 := hz l
      have e2 := congrFun (LinearMap.mem_ker.mp hx₂k) (ιL l)
      rw [leadL_apply] at e1 e2
      rw [Pi.add_apply, e1, e2, Pi.zero_apply, add_zero]
    · rw [Pi.add_apply, hx₂' k]; ring

/-- Products of powers of variables of one block. -/
theorem prod_pow_mem4 (ct : ℕ) {ι' : Type*} [Fintype ι'] (v : ι' → Var d₀ d₁ m) (b : Blk4 m)
    (hb : ∀ l, blk4 ct (v l) = b) (e : ι' → ℕ) {N : ℕ} (he : ∑ l, e l ≤ N) :
    ∏ l, (X (v l) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ e l ∈
      StrongSix.M2.FLE ℂ (blk4 ct) (Pi.single b N) := by
  classical
  have h := StrongSix.M2.prod_mem_FLE' (K := ℂ) (β := (blk4 ct : Var d₀ d₁ m → Blk4 m))
    Finset.univ (fun l => (X (v l) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ e l)
    (fun l => Pi.single b (e l)) fun l _ => by
      have := LSG.ME.fle_pow_single (LSG.ME.fle_X (K := ℂ)
        (β := (blk4 ct : Var d₀ d₁ m → Blk4 m)) (v l)) (e l)
      rwa [hb, mul_one] at this
  refine StrongSix.M2.FLE_mono ℂ _ (fun b' => ?_) h
  simp only [Finset.sum_apply, Pi.single_apply]
  split_ifs <;> simp [he]

theorem sum_fin_le {ι' : Type*} [Fintype ι'] {M N : ℕ} (hc : Fintype.card ι' = N)
    (a : ι' → Fin (M / N + 1)) : ∑ l, (a l : ℕ) ≤ M := by
  calc ∑ l, (a l : ℕ) ≤ ∑ _l : ι', M / N := Finset.sum_le_sum fun l _ => Nat.lt_succ_iff.mp (a l).2
    _ = N * (M / N) := by simp [hc]
    _ ≤ M := Nat.mul_div_le M N

/-- **The 3-block family on `h₀ × T_U`.** -/
theorem exists_lin_family4 (h0 : Submodule ℂ (Fin (d₀ + r) → ℂ)) (U : Submodule ℚ (Fin d₁ → ℚ))
    (N0 N2 N1 : ℕ) :
    ∃ (a : ℕ) (A : Fin a → MvPolynomial (StrongSix.M2.V3 (d₀ + r) d₁) ℂ),
      a = (N0 / finrank ℂ (h0.map (leadL (d₀ := d₀) (r := r))) + 1) ^
          finrank ℂ (h0.map (leadL (d₀ := d₀) (r := r))) *
        (N2 / finrank ℂ ↥(h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) + 1) ^
          finrank ℂ ↥(h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) *
        (N1 / (d₁ - finrank ℚ U) + 1) ^ (d₁ - finrank ℚ U) ∧
      (∀ i, rename (ιLV (m := m)) (A i) ∈ StrongSix.M2.FLE ℂ (blk4 d₀) (D4f N0 N2 N1 0)) ∧
      ∀ c : Fin a → ℂ, ∑ i, c i • A i ∈
        StrongSix.M2.vanish (StrongSix.M2.prodSet h0 (StrongSix.M2.lsat U)) → c = 0 := by
  classical
  set t0 := finrank ℂ (h0.map (leadL (d₀ := d₀) (r := r))) with ht0
  set j := finrank ℂ ↥(h0 ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) with hj0
  obtain ⟨ιL, ιT, hιT, hsurj⟩ := exists_lin_surj (d₀ := d₀) (r := r) h0
  obtain ⟨κ, _, jj, hjj, hκ, hind⟩ := StrongSix.M2.exists_indep_quot U
  set s := d₁ - finrank ℚ U with hs
  set M0 := N0 / t0 + 1
  set M2 := N2 / j + 1
  set M1 := N1 / s + 1
  let ι := ((Fin t0 → Fin M0) × (Fin j → Fin M2)) × (κ → Fin M1)
  let B : ι → MvPolynomial (StrongSix.M2.V3 (d₀ + r) d₁) ℂ := fun p =>
    ((∏ l, X (Sum.inl (Fin.castAdd r (ιL l))) ^ (p.1.1 l : ℕ)) *
      ∏ k, X (Sum.inl (ιT k)) ^ (p.1.2 k : ℕ)) * ∏ q, X (Sum.inr (Sum.inl (jj q))) ^ (p.2 q : ℕ)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => B (e.symm i), ?_, ?_, ?_⟩
  · simp [ι, Fintype.card_prod, hκ, M0, M2, M1]
  · intro i
    set p := e.symm i
    have hren : rename (ιLV (m := m)) (B p) =
        ((∏ l, X (Var.x (Fin.castAdd r (ιL l)) : Var (d₀ + r) d₁ m) ^ (p.1.1 l : ℕ)) *
          ∏ k, X (Var.x (ιT k) : Var (d₀ + r) d₁ m) ^ (p.1.2 k : ℕ)) *
          ∏ q, X (Var.y (jj q) : Var (d₀ + r) d₁ m) ^ (p.2 q : ℕ) := by
      simp [B, map_prod, map_pow, rename_X, ιLV]
    rw [hren]
    have h1 := prod_pow_mem4 (m := m) (d₁ := d₁) d₀
      (fun l => (Var.x (Fin.castAdd r (ιL l)) : Var (d₀ + r) d₁ m)) .xl
      (fun l => by simp [blk4_x]) (fun l => (p.1.1 l : ℕ)) (N := N0)
      (sum_fin_le (by simp [t0]) p.1.1)
    have h2 := prod_pow_mem4 (m := m) (d₁ := d₁) d₀ (fun k => (Var.x (ιT k) : Var (d₀ + r) d₁ m))
      .xt (fun k => by have := hιT k; simp [blk4_x]; omega) (fun k => (p.1.2 k : ℕ)) (N := N2)
      (sum_fin_le (by simp [j]) p.1.2)
    have h3 := prod_pow_mem4 (m := m) (d₀ := d₀ + r) d₀
      (fun q => (Var.y (jj q) : Var (d₀ + r) d₁ m)) .yz (fun q => rfl) (fun q => (p.2 q : ℕ))
      (N := N1) (sum_fin_le (by simp [hκ, s]) p.2)
    refine StrongSix.M2.FLE_mono ℂ _ (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ h1 h2) h3)
    cases b <;> simp
  · intro c hc
    set w : ι → ℂ := fun p => c (e p)
    have hw : ∑ p, w p • B p ∈
        StrongSix.M2.vanish (StrongSix.M2.prodSet h0 (StrongSix.M2.lsat U)) := by
      have : ∑ p, w p • B p = ∑ i, c i • B (e.symm i) := by
        rw [← e.sum_comp (fun i => c i • B (e.symm i))]
        simp [w]
      rw [this]; exact hc
    let χ := StrongSix.M2.torusChar (K := ℂ) U jj
    have hχinj := StrongSix.M2.torusChar_injective (K := ℂ) U jj hjj hind
    have hval : ∀ (z : Fin t0 → ℂ) (z' : Fin j → ℂ) (y : StrongSix.M2.TU ℂ U),
        ∑ p : ι, w p * (((∏ l, z l ^ (p.1.1 l : ℕ)) * ∏ k, z' k ^ (p.1.2 k : ℕ)) *
          χ (fun q => (p.2 q : ℕ)) y) = 0 := by
      intro z z' y
      obtain ⟨x, hx, hxL, hxT⟩ := hsurj z z'
      have hg : ((x, y.1) : StrongSix.Thm1.GPt ℂ (d₀ + r) d₁) ∈
          StrongSix.M2.prodSet h0 (StrongSix.M2.lsat U) :=
        (StrongSix.M2.mem_prodSet_lsat_iff h0 U _).mpr ⟨hx, y.2⟩
      have h1 : eval (StrongSix.M2.pt ((x, y.1) : StrongSix.Thm1.GPt ℂ (d₀ + r) d₁))
          (∑ p, w p • B p) = 0 := hw _ hg
      rw [← h1, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [B, smul_eval, map_mul, map_prod, map_pow, eval_X, StrongSix.M2.pt,
        Sum.elim_inl, Sum.elim_inr, hxL, hxT, χ, StrongSix.M2.torusChar, MonoidHom.coe_mk,
        OneHom.coe_mk]
      rfl
    -- step 1: coefficients of the polynomial identity
    have hstep : ∀ (ab : (Fin t0 → Fin M0) × (Fin j → Fin M2)) (y : StrongSix.M2.TU ℂ U),
        ∑ b : κ → Fin M1, w (ab, b) * χ (fun q => (b q : ℕ)) y = 0 := by
      intro ab y
      let mono : (Fin t0 → Fin M0) × (Fin j → Fin M2) → (Fin t0 ⊕ Fin j →₀ ℕ) := fun ab =>
        Finsupp.equivFunOnFinite.symm (Sum.elim (fun l => (ab.1 l : ℕ)) fun k => (ab.2 k : ℕ))
      have hmono : Function.Injective mono := by
        intro a a' haa
        have h1 : ∀ v, mono a v = mono a' v := fun v => by rw [haa]
        refine Prod.ext (funext fun l => Fin.ext ?_) (funext fun k => Fin.ext ?_)
        · simpa [mono] using h1 (Sum.inl l)
        · simpa [mono] using h1 (Sum.inr k)
      let Q : MvPolynomial (Fin t0 ⊕ Fin j) ℂ :=
        ∑ a, monomial (mono a) (∑ b : κ → Fin M1, w (a, b) * χ (fun q => (b q : ℕ)) y)
      have hQ : Q = 0 := by
        apply MvPolynomial.funext
        intro u
        rw [map_zero, ← hval (fun l => u (Sum.inl l)) (fun k => u (Sum.inr k)) y,
          Fintype.sum_prod_type]
        simp only [Q, map_sum, eval_monomial]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Fintype.prod_sum_type]
        simp only [mono, Finsupp.coe_equivFunOnFinite_symm, Sum.elim_inl, Sum.elim_inr]
        ring
      have := congrArg (fun q : MvPolynomial (Fin t0 ⊕ Fin j) ℂ => q.coeff (mono ab)) hQ
      simp only [Q, coeff_sum, coeff_monomial] at this
      rw [Finset.sum_eq_single ab
        (fun a' _ ha' => ite_eq_right_iff.mpr fun h => absurd h (hmono.ne ha'))
        (by simp)] at this
      simpa using this
    -- step 2: Dedekind
    have hded : LinearIndependent ℂ
        fun b : κ → Fin M1 => (χ (fun q => (b q : ℕ)) : StrongSix.M2.TU ℂ U → ℂ) :=
      (linearIndependent_monoidHom (StrongSix.M2.TU ℂ U) ℂ).comp
        (fun b : κ → Fin M1 => χ fun q => (b q : ℕ))
        (hχinj.comp fun b b' hb => funext fun q => Fin.ext (congrFun hb q))
    have hw0 : ∀ p, w p = 0 := by
      rintro ⟨ab, b⟩
      exact (Fintype.linearIndependent_iff.mp hded) (fun b => w (ab, b)) (by
        funext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact hstep ab y) b
    funext i
    have := hw0 (e.symm i)
    simpa [w] using this

end

end LSG.MEV
