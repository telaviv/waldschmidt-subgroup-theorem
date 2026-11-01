import Mathlib
import LSG.MEV.Blk4Lin

/-!
# The Hilbert lower bound for `H⁰ ⊆ G̃` in the 4-block grading (STAGE5_MEV §10.3)

* **`hfun_H0_ge_gen4`**: copy of `hfun_H0_ge_genV` with `blk4 ct`, for any family `A` on the linear
  group of degrees `(tD₀ lead, tD₃ trail, tD₁ y)` independent modulo `I(L0V)`.
* **`hfun_H0_geV4`** (`G̃_r`, `d₀ + r` additive coordinates, cutoff `d₀`): with
  `h₀ = π₀(T′ ∩ vector group)`, `t₀ = dim leadL(h₀)`, `j = dim (h₀ ∩ ker leadL)`,
  `(tD₀/t₀ + 1)^{t₀} (tD₂/j + 1)^j (tD₁/t₁ + 1)^{t₁} (⌊tD₂/2⌋ + 1)^{t₂ + m} ≤ H(vanish H⁰; t)`
  in the grading `(D₀, D₂, D₁, D₂)` (lead, trail, `yz`, `E^♮`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module Set
open LSG.W88 (IsAbelianTangent torusLie)
open LSG.W88.Vec (vecIncl torIncl g2Incl)
open StrongSix.M2 (FLE hfun)

namespace LSG.MEV

noncomputable section

section Gen

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}
variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **The Hilbert lower bound, general form, 4-block grading**: any family `A` of polynomials on the
linear group of degrees `(tD₀, tD₃, tD₁)` (lead, trail, `y`), independent modulo `I(L0V)`. -/
theorem hfun_H0_ge_gen4 (ct D₀ D₁ D₂ D₃ t : ℕ) {a : ℕ}
    (A : Fin a → MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)
    (hAmem : ∀ i, rename (ιLV (m := m)) (A i) ∈
      FLE ℂ (blk4 ct) (D4f (t * D₀) (t * D₃) (t * D₁) 0))
    (hAind : ∀ c : Fin a → ℂ, ∑ i, c i • A i ∈
      (StrongSix.M2.vanish (L0V Ls hH) : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) →
        c = 0) :
    a * (t * D₂ / 2 + 1) ^ (finrank ℂ ((lieAlg Ls hH).map piZ) + finrank ℂ (FibV Ls hH) + m) ≤
      hfun (blk4 ct) (D4f D₀ D₃ D₁ D₂) ℂ (vanish (H0 Ls hH)) t := by
  classical
  set tz := (lieAlg Ls hH).map (piZ (d₀ := d₀) (d₁ := d₁) (m := m))
  set r := finrank ℂ tz
  set f := finrank ℂ (FibV Ls hH)
  obtain ⟨ιz, hιz, hsz⟩ := LSG.ME.exists_coord_surj tz
  obtain ⟨ιw, hιw, hsw⟩ := LSG.ME.exists_coord_surj (FibV Ls hH)
  set n := t * D₂ / 2
  let J := {k : Fin m // k ∉ Set.range ιz}
  have hJ : Fintype.card J = m - r := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective hιz,
      Fintype.card_fin]
  have hr : r ≤ m := by simpa using Fintype.card_le_of_injective ιz hιz
  let act : Fin m → Prop := actB tz
  let κ := Fin (n + 1) × Fin (n + 1)
  let P0 : Fin a × (Fin r → κ) → MvPolynomial (Var d₀ d₁ m) ℂ := fun q =>
    rename ιLV (A q.1) * ∏ l, monoPV n (ιz l) (q.2 l)
  let Mq : (Fin f → Fin (n + 1)) × (J → Fin (n + 1)) → MvPolynomial (Var d₀ d₁ m) ℂ := fun d =>
    (∏ l, X (.e (ιw l) (fcI act (ιw l))) ^ (d.1 l : ℕ)) *
      ∏ j : J, X (.e j.1 (svI act j.1)) ^ (d.2 j : ℕ)
  let Pf : (Fin a × (Fin r → κ)) × ((Fin f → Fin (n + 1)) × (J → Fin (n + 1))) →
      MvPolynomial (Var d₀ d₁ m) ℂ := fun p => P0 p.1 * Mq p.2
  set F := FLE ℂ (blk4 ct) (t • D4f (m := m) D₀ D₃ D₁ D₂)
  -- block degrees
  have hPfmem : ∀ p, Pf p ∈ F := by
    intro p
    have h2 : ∏ l, monoPV (d₀ := d₀) (d₁ := d₁) n (ιz l) (p.1.2 l) ∈
        FLE ℂ blk (∑ l, Pi.single (LSG.ME.Blk.e (ιz l)) n) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun l _ => monoPV_mem n (ιz l) (p.1.2 l)
    have h3 : ∏ l, (X (.e (ιw l) (fcI act (ιw l))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^
        (p.2.1 l : ℕ) ∈ FLE ℂ blk (∑ l, Pi.single (LSG.ME.Blk.e (ιw l)) n) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun l _ =>
        pow_X_mem (.e (ιw l) (fcI act (ιw l))) (Nat.lt_succ_iff.mp (p.2.1 l).isLt)
    have h4 : ∏ j : J, (X (.e j.1 (svI act j.1)) : MvPolynomial (Var d₀ d₁ m) ℂ) ^
        (p.2.2 j : ℕ) ∈ FLE ℂ blk (∑ j : J, Pi.single (LSG.ME.Blk.e j.1) n) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun j _ =>
        pow_X_mem (.e j.1 (svI act j.1)) (Nat.lt_succ_iff.mp (p.2.2 j).isLt)
    have hE : (∏ l, monoPV (d₀ := d₀) (d₁ := d₁) n (ιz l) (p.1.2 l)) * Mq p.2 ∈
        FLE ℂ blk (LSG.ME.Dfun (m := m) 0 0 (t * D₂)) := by
      refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (StrongSix.M2.mul_mem_FLE ℂ h2
        (StrongSix.M2.mul_mem_FLE ℂ h3 h4))
      simp only [Pi.add_apply]
      cases b with
      | x => simp only [sum_single_x]; simp [LSG.ME.Dfun]
      | yz => simp only [sum_single_yz]; simp [LSG.ME.Dfun]
      | e k =>
        rw [sum_single_e ιz hιz, sum_single_e ιw hιw, sum_single_e (Subtype.val : J → Fin m)
          Subtype.val_injective]
        have h2n : 2 * n ≤ t * D₂ := Nat.mul_div_le (t * D₂) 2
        simp only [LSG.ME.Dfun]
        have hJk : (∃ j : J, j.1 = k) ↔ ¬ ∃ l, ιz l = k :=
          ⟨fun ⟨j, hj⟩ => hj ▸ j.2, fun h => ⟨⟨k, h⟩, rfl⟩⟩
        by_cases h1 : ∃ l, ιz l = k
        · have h3 : ¬ ∃ j : J, j.1 = k := fun h => hJk.mp h h1
          rw [ite_eq_left h1, ite_eq_right h3]
          split_ifs <;> omega
        · have h3 : ∃ j : J, j.1 = k := hJk.mpr h1
          rw [ite_eq_right h1, ite_eq_left h3]
          split_ifs <;> omega
    have hE4 := fle4_of_fle ct (D' := D4f 0 0 0 (t * D₂))
      (fun b => by cases b <;> simp [b4to3, LSG.ME.Dfun]) hE
    have hP : Pf p = rename ιLV (A p.1.1) *
        ((∏ l, monoPV (d₀ := d₀) (d₁ := d₁) n (ιz l) (p.1.2 l)) * Mq p.2) := by
      simp only [Pf, P0]; ring
    rw [hP]
    refine StrongSix.M2.FLE_mono ℂ (blk4 ct) (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ (hAmem p.1.1) hE4)
    cases b <;> simp
  -- independence modulo `vanish H⁰`
  set Q := F ⧸ LSG.ME.Nsub (K := ℂ) (blk4 ct) (D4f (m := m) D₀ D₃ D₁ D₂) (vanish (H0 Ls hH)) t
  let fq : (Fin a × (Fin r → κ)) × ((Fin f → Fin (n + 1)) × (J → Fin (n + 1))) → Q := fun p =>
    Submodule.Quotient.mk ⟨Pf p, hPfmem p⟩
  have hind : LinearIndependent ℂ fq := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have hvan : ∑ p, c p • Pf p ∈ vanish (H0 Ls hH) := by
      have hmk : (LSG.ME.Nsub (K := ℂ) (blk4 ct) (D4f (m := m) D₀ D₃ D₁ D₂)
          (vanish (H0 Ls hH)) t).mkQ (∑ p, c p • (⟨Pf p, hPfmem p⟩ : F)) = 0 := by
        rw [map_sum]; exact hc0
      have := (Submodule.Quotient.mk_eq_zero _).mp hmk
      simpa using this
    have hsplit : ∑ p, c p • Pf p = ∑ d, (∑ q, c (q, d) • P0 q) * Mq d := by
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by simp only [Pf, smul_mul_assoc]
    have hB : ∀ d (g : GPtV d₀ d₁ Ls) (φ : Fin m → ℂ) (ν ν' : Fin m → ℂ),
        (∀ k, k ∉ Set.range (Subtype.val : J → Fin m) → ν k = ν' k) →
        eval (coordsZ (g + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m)) ν)
          (∑ q, c (q, d) • P0 q) = eval (coordsZ g ν') (∑ q, c (q, d) • P0 q) := by
      intro d g φ ν ν' hνν'
      have hι' : ∀ l, ν (ιz l) = ν' (ιz l) := fun l =>
        hνν' (ιz l) (by rintro ⟨j, hj⟩; exact j.2 ⟨l, hj.symm⟩)
      simp only [map_sum, smul_eval, P0, eval_P0, linPtG_fibshift, hι']
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 2
      refine Finset.prod_congr rfl fun l _ => ?_
      congr 1
      funext c'
      rw [block_fibshift]
    have hA := sepA hH act hsw (Subtype.val : J → Fin m) Subtype.val_injective
      (fun d => ∑ q, c (q, d) • P0 q) hB (hsplit ▸ hvan)
    have hprime := vanish_H0_isPrime (Ls := Ls) hH
    obtain ⟨g₀, hg₀, hg₀1⟩ := exists_sv_point hH (d₀ := d₀) (d₁ := d₁)
    have hPi : ((∏ l, X (.e (ιw l) (svI act (ιw l)))) * ∏ j : J, X (.e j.1 (svI act j.1)) :
        MvPolynomial (Var d₀ d₁ m) ℂ) ∉ vanish (H0 Ls hH) := by
      intro hmem
      have := mem_vanish.mp hmem g₀ hg₀ 1
      simp only [map_mul, map_prod, eval_X] at this
      rw [Finset.prod_eq_one (fun l _ => hg₀1 (ιw l)), Finset.prod_eq_one (fun j _ => hg₀1 j.1),
        mul_one] at this
      exact one_ne_zero this
    intro p
    obtain ⟨q, d⟩ := p
    have hB0 : ∑ q, c (q, d) • P0 q ∈ vanish (H0 Ls hH) :=
      (hprime.mem_or_mem (hA d)).resolve_right hPi
    have := indep_coreV hH hc hιz hsz n A hAind (fun q => c (q, d)) hB0
    exact congrFun this q
  have hcard := hind.fintype_card_le_finrank
  rw [← LSG.ME.hfun_eq_finrank_quotient] at hcard
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hJ, κ] at hcard
  have e : (n + 1) ^ (r + f + m) = ((n + 1) * (n + 1)) ^ r * ((n + 1) ^ f * (n + 1) ^ (m - r)) := by
    rw [← sq, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  calc a * (n + 1) ^ (r + f + m)
      = a * ((n + 1) * (n + 1)) ^ r * ((n + 1) ^ f * (n + 1) ^ (m - r)) := by rw [e]; ring
    _ ≤ _ := hcard

end Gen

section Spec

variable {d₀ r d₁ m : ℕ} {Ls : Fin m → PeriodPair}
variable {H : Set (GPtV (d₀ + r) d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- `h₀ = π₀(T′ ∩ vector group) ⊆ ℂ^{d₀+r}`. -/
abbrev h0V : Submodule ℂ (Fin (d₀ + r) → ℂ) :=
  ((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ (Fin (d₀ + r) → ℂ) (Fin m → ℂ))

omit hc in
theorem L0V_eq : L0V Ls hH = StrongSix.M2.prodSet (h0V hH)
    (StrongSix.M2.lsat (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH))))) := rfl

/-- **The 4-block Hilbert lower bound for `H⁰`.** -/
theorem hfun_H0_geV4 (D₀ D₁ D₂ t : ℕ) :
    (t * D₀ / finrank ℂ ((h0V hH).map (leadL (d₀ := d₀) (r := r))) + 1) ^
        finrank ℂ ((h0V hH).map (leadL (d₀ := d₀) (r := r))) *
      (t * D₂ / finrank ℂ ↥(h0V hH ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) + 1) ^
        finrank ℂ ↥(h0V hH ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) *
      (t * D₁ / finrank ℂ ((lieAlg Ls hH).comap
          (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG (d₀ + r) d₁ m)) + 1) ^
        finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG (d₀ + r) d₁ m)) *
      (t * D₂ / 2 + 1) ^ (finrank ℂ ↥(lieAlg Ls hH ⊓
        (LinearMap.ker (prA : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) ⊓
          LinearMap.ker prB)) + m) ≤
      hfun (blk4 d₀) (D4f D₀ D₂ D₁ D₂) ℂ (vanish (H0 Ls hH)) t := by
  obtain ⟨a, A, ha, hAmem, hAind⟩ := exists_lin_family4 (m := m) (h0V hH)
    (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH)))) (t * D₀) (t * D₂) (t * D₁)
  rw [d1_sub_U0 hH hc] at ha
  have h2 := hfun_H0_ge_gen4 hH hc d₀ D₀ D₁ D₂ D₂ t A hAmem (fun c hcv => hAind c hcv)
  rw [finrank_T2 hH hc, ← ha]
  exact h2

end Spec

end

end LSG.MEV
