import Mathlib
import LSG.MEV.SubgroupHilbV2

/-!
# The Hilbert lower bound for `H⁰ ⊆ G̃` (gap G4), part 3: the bound

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)` with Lie algebra `T′`:

* **`hfun_H0_ge_genV`**: `H(L0V; tD₀, tD₁) · (⌊tD₂/2⌋ + 1)^{dim t + dim FibV + m} ≤ H(vanish H⁰; tD)`.
* **`hfun_H0_geV`**: with StrongSix's `hfun_prodSet_ge`, the explicit bound with the projection
  exponents `t₀ = dim π₀(Γ)`, `t₁ = dim (T′ ∩ torus)`, `t₂ = dim (T′ ∩ ker π₀ ∩ ker π₁)`:
  `(tD₀/t₀ + 1)^{t₀} · (tD₁/t₁ + 1)^{t₁} · (⌊tD₂/2⌋ + 1)^{t₂ + m} ≤ H(vanish H⁰; tD)`.
* **`hdim_H0_eq_exps`**: `hdim (vanish H⁰) = t₀ + t₁ + t₂ + m`: the lower bound has the full degree.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module Set
open LSG.W88 (IsAbelianTangent torusLie)
open LSG.W88.Vec (vecIncl torIncl g2Incl)
open StrongSix.M2 (FLE hfun)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

section Bound

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **The Hilbert lower bound, general form.** -/
theorem hfun_H0_ge_genV (D₀ D₁ D₂ t : ℕ) :
    hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish (L0V Ls hH)) t *
        (t * D₂ / 2 + 1) ^ (finrank ℂ ((lieAlg Ls hH).map piZ) + finrank ℂ (FibV Ls hH) + m) ≤
      hfun blk (LSG.ME.Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH)) t := by
  classical
  set tz := (lieAlg Ls hH).map (piZ (d₀ := d₀) (d₁ := d₁) (m := m))
  set r := finrank ℂ tz
  set f := finrank ℂ (FibV Ls hH)
  obtain ⟨ιz, hιz, hsz⟩ := LSG.ME.exists_coord_surj tz
  obtain ⟨ιw, hιw, hsw⟩ := LSG.ME.exists_coord_surj (FibV Ls hH)
  set n := t * D₂ / 2
  set a := hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish (L0V Ls hH)) t
  obtain ⟨A, hAmem, hAind⟩ := LSG.ME.exists_indep_lift StrongSix.M2.blk ![D₀, D₁]
    (StrongSix.M2.vanish (L0V Ls hH) : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) t
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
  set F := FLE ℂ blk (t • LSG.ME.Dfun (m := m) D₀ D₁ D₂)
  -- block degrees
  have hPfmem : ∀ p, Pf p ∈ F := by
    intro p
    have h1 : rename ιLV (A p.1.1) ∈ FLE ℂ blk (fun b : LSG.ME.Blk m => match b with
        | .x => t * D₀ | .yz => t * D₁ | .e _ => 0) := by
      refine LSG.ME.rename_mem_FLE ιLV (β := StrongSix.M2.blk) (fun i : Fin 2 => if i = 0 then
        LSG.ME.Blk.x else LSG.ME.Blk.yz) (fun v => ?_) (fun b => ?_) (hAmem p.1.1)
      · rcases v with i | j | j <;> rfl
      · cases b <;> simp [Fin.sum_univ_two]
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
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (StrongSix.M2.mul_mem_FLE ℂ
      (StrongSix.M2.mul_mem_FLE ℂ h1 h2) (StrongSix.M2.mul_mem_FLE ℂ h3 h4))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
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
  -- independence modulo `vanish H⁰`
  set Q := F ⧸ LSG.ME.Nsub (K := ℂ) blk (LSG.ME.Dfun (m := m) D₀ D₁ D₂) (vanish (H0 Ls hH)) t
  let fq : (Fin a × (Fin r → κ)) × ((Fin f → Fin (n + 1)) × (J → Fin (n + 1))) → Q := fun p =>
    Submodule.Quotient.mk ⟨Pf p, hPfmem p⟩
  have hind : LinearIndependent ℂ fq := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have hvan : ∑ p, c p • Pf p ∈ vanish (H0 Ls hH) := by
      have hmk : (LSG.ME.Nsub (K := ℂ) blk (LSG.ME.Dfun (m := m) D₀ D₁ D₂)
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

/-- **The Hilbert lower bound with the projection exponents `(t₀, t₁, t₂ + m)`.** -/
theorem hfun_H0_geV (D₀ D₁ D₂ t : ℕ) :
    (t * D₀ / finrank ℂ (((lieAlg Ls hH).comap vecIncl).map
        (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ))) + 1) ^
        finrank ℂ (((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ))) *
      (t * D₁ / finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m)) +
        1) ^ finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m)) *
      (t * D₂ / 2 + 1) ^ (finrank ℂ ↥(lieAlg Ls hH ⊓
        (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓ LinearMap.ker prB)) + m) ≤
      hfun blk (LSG.ME.Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH)) t := by
  have h1 := StrongSix.M2.hfun_prodSet_ge (K := ℂ)
    (((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ)))
    (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH)))) D₀ D₁ t
  rw [d1_sub_U0 hH hc] at h1
  have h2 := hfun_H0_ge_genV hH hc D₀ D₁ D₂ t
  rw [finrank_T2 hH hc]
  exact le_trans (Nat.mul_le_mul_right _ h1) h2

/-- **The degree of the lower bound is the Hilbert dimension**: `hdim (vanish H⁰) = t₀ + t₁ + t₂ + m`. -/
theorem hdim_H0_eq_exps (D : LSG.ME.Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (StrongSix.M2.hdata blk D ℂ (vanish (H0 Ls hH))).1 =
      finrank ℂ (((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ))) +
        finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m)) +
        finrank ℂ ↥(lieAlg Ls hH ⊓
          (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓ LinearMap.ker prB)) + m := by
  rw [hdim_H0 hH hc D hD, t0_add_t1_add_t2 hH hc]

end Bound

end

end LSG.MEV
