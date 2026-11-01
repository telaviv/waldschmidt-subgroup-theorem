import Mathlib
import LSG.ME.SubgroupHilb
import LSG.ME.ProductGraph

/-!
# The Hilbert lower bound for `H⁰` with the free cone scalings (STAGE2 §11)

`hfun_H0_ge'` (`SubgroupHilb`) bounds `H(vanish H⁰; tD)` below by a polynomial of degree
`t₀ + t₁ + 2 t₂` in `t`, while `hdim (vanish H⁰) = t₀ + t₁ + t₂ + m` (`hdim_H0`). The missing
`m − t₂` come from the elliptic blocks `k ∉ ι` (outside the coordinates onto which the abelian
tangent space projects): there the cone scaling is free. Multiplying the old family by the powers
`∏_{k ∉ ι} V_k^{γ_k}` (`0 ≤ γ_k ≤ t D₂`) keeps it independent modulo `vanish H⁰`:

* `vanish H⁰` is prime (`vanish_H0_isPrime`) and `∏_{k ∉ ι} V_k ∉ vanish H⁰` (the identity has
  `V = 1`), so it suffices that `B_γ · ∏ V_k ∈ vanish H⁰` for every `γ`, where
  `B_γ = Σ_{a, β} c_{a β γ} A_a M_β`;
* at a point `h ∈ H⁰` with all `V`-coordinates `r_k ≠ 0` (`k ∉ ι`), varying the scalings
  `s_k` (`k ∉ ι`, zero allowed by `eval_coordsZ_eq_zero`) gives the polynomial identity
  `Σ_γ B_γ(h) ∏ (r_k s_k)^{γ_k} = 0` in `s`, whence every `B_γ(h) = 0`.

Results:
* **`indep_H0_core`**: the independence statement inside `hfun_H0_ge`, for any `L0 ⊆ π_L(H⁰)`.
* **`hfun_H0_ge_gen`**: `H(L0; tD₀, tD₁) · ((tD₂+1)²)^{t₂} · (tD₂+1)^{m − t₂} ≤ H(vanish H⁰; tD)`.
* **`hfun_H0_ge''`**: with `L0 = V × T_{lsat(qspan Λ)}` for any `V × T_Λ ⊆ π_L(H⁰)` and StrongSix's
  `hfun_prodSet_ge`: the explicit lower bound of degree `t₀ + t₁ + t₂ + m`.
* `prodSet_ML_subset_projL`: `ML = V × T_Λ` (the linear part of `H⁰`, `ProductGraph`) gives such a
  `V × T_Λ`, with `dim V = dim h₀` and `qspan Λ = U` in the product decomposition.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan IsAbelianTangent)
open StrongSix.M2 (FLE hfun)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

theorem eval_rename_ιL_Z (g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) (ν : Fin m → ℂ)
    (P : MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ) :
    eval (coordsZ g ν) (rename ιL P) = eval (StrongSix.M2.pt (linPt g)) P := by
  rw [eval_rename]
  congr 2
  funext v
  rcases v with i | j | j <;> rfl

/-- **The independence statement inside `hfun_H0_ge`**, for an arbitrary `L0 ⊆ π_L(H⁰)`. -/
theorem indep_H0_core (hH : IsSubgroupG H) (hc : IsZClosed H) {tAb : Submodule ℂ (Fin m → ℂ)}
    (htAb : ∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) {r : ℕ}
    {ι : Fin r → Fin m} (hι : Function.Injective ι)
    (hsurj : ∀ y : Fin r → ℂ, ∃ z ∈ tAb, ∀ l, z (ι l) = y l)
    {L0 : Set (StrongSix.Thm1.GPt ℂ d₀ d₁)} (hL0 : L0 ⊆ projL (H0 Ls hH hc)) (n : ℕ) {a : ℕ}
    (A : Fin a → MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)
    (hAind : ∀ c : Fin a → ℂ, ∑ i, c i • A i ∈
      (StrongSix.M2.vanish L0 : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) → c = 0)
    (c : Fin a × (Fin r → Fin (n + 1) × Fin (n + 1)) → ℂ)
    (hvan : ∑ p, c p • (rename ιL (A p.1) * ∏ l, monoP n (ι l) (p.2 l)) ∈ vanish (H0 Ls hH hc)) :
    c = 0 := by
  classical
  let κ := Fin (n + 1) × Fin (n + 1)
  let Pf : Fin a × (Fin r → κ) → MvPolynomial (Var d₀ d₁ m) ℂ := fun p =>
    rename ιL (A p.1) * ∏ l, monoP n (ι l) (p.2 l)
  -- evaluate at points of `L⁰ × ∏ cone(E_{ι l})`
  have heval : ∀ x ∈ L0, ∀ z : Fin r → Fin 3 → ℂ,
      (∀ l, z l ∈ coneE (g2L Ls (ι l)) (g3L Ls (ι l))) →
      ∑ β : Fin r → κ, (∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i)) *
        ∏ l, monoF n (β l) (z l) = 0 := by
    intro x hx z hz
    choose lam u v hl huv hzl using hz
    choose e he using fun l => exists_pt_of_coneE (Ls := Ls) (ι l) (huv l)
    obtain ⟨g, hg, hgx, hge⟩ := exists_H0_point hH hc htAb hsurj (hL0 hx) e
    let μ : Fin m → ℂˣ := fun k =>
      if h : ∃ l, ι l = k then Units.mk0 (lam h.choose) (hl _) else 1
    have hμ : ∀ l, (μ (ι l) : ℂ) = lam l := by
      intro l
      have h : ∃ l', ι l' = ι l := ⟨l, rfl⟩
      simp only [μ, h, ↓reduceDIte, Units.val_mk0]
      rw [hι h.choose_spec]
    have hblock : ∀ l, (fun c => coords g μ (.e (ι l) c)) = z l := by
      intro l
      funext c'
      simp only [coords, coordsZ_e, hμ, hge l, he l, hzl l]
      fin_cases c' <;> simp
    have key : ∑ β : Fin r → κ, (∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i)) *
        ∏ l, monoF n (β l) (z l) = eval (coords g μ) (∑ p, c p • Pf p) := by
      rw [map_sum, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eval]
      simp only [Pf, map_mul, map_prod, eval_rename_ιL, hgx, eval_monoP, hblock]
      ring
    rw [key]
    exact mem_vanish.mp hvan g hg μ
  funext p
  obtain ⟨i₀, β₀⟩ := p
  have hzero : ∀ x ∈ L0, ∀ β : Fin r → κ, ∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i) = 0 := by
    intro x hx
    have hne : ∀ l, (coneE (g2L Ls (ι l)) (g3L Ls (ι l))).Nonempty := by
      intro l
      obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq
        (4 * (0 : ℂ) ^ 3 - g2L Ls (ι l) * 0 - g3L Ls (ι l)) (n := 2) (by norm_num)
      exact ⟨_, 1, 0, v, one_ne_zero, hv, rfl⟩
    have := indep_prod_fin (monoF (K := ℂ) n) r (fun l => coneE (g2L Ls (ι l)) (g3L Ls (ι l)))
      hne (fun l => monoF_linearIndependent two_ne_zero _ _ n) _ (heval x hx)
    exact fun β => congrFun this β
  have hβ : ∑ i, c (i, β₀) • A i ∈ (StrongSix.M2.vanish L0 :
      Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) := by
    intro x hx
    simpa [map_sum, mul_comm] using hzero x hx β₀
  exact congrFun (hAind _ hβ) i₀

/-! ### The free scalings -/

/-- The `V`-coordinate of the identity is `λ`. -/
theorem eval_coords_zero_V (lam : Fin m → ℂˣ) (k : Fin m) :
    coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) lam (.e k 1) = lam k := by
  simp [coords, rep, O]

/-- **Separation of the free scalings.** If `Σ_γ B_γ · ∏_{k ∈ J} V_k^{γ_k}` vanishes on `E`, where
the `B_γ` do not involve the blocks `k ∈ J`, then each `B_γ · ∏_{k ∈ J} V_k` vanishes on `E`. -/
theorem sep_free_scalings {J : Type} [Fintype J] [DecidableEq J] (e : J → Fin m)
    (he : Function.Injective e) {N : ℕ} {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}
    (B : (J → Fin (N + 1)) → MvPolynomial (Var d₀ d₁ m) ℂ)
    (hB : ∀ γ (g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) (ν ν' : Fin m → ℂ),
      (∀ k, k ∉ Set.range e → ν k = ν' k) → eval (coordsZ g ν) (B γ) = eval (coordsZ g ν') (B γ))
    (hvan : ∑ γ, B γ * ∏ k, X (.e (e k) 1) ^ (γ k : ℕ) ∈ vanish E) (γ₀ : J → Fin (N + 1)) :
    B γ₀ * ∏ k, X (.e (e k) 1) ∈ vanish E := by
  classical
  refine mem_vanish.mpr fun h hh μ => ?_
  set rr : J → ℂ := fun k => rep (h.2.2 (e k)) 1
  by_cases hr : ∃ k, rr k = 0
  · obtain ⟨k, hk⟩ := hr
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ k) (by simpa [coords] using hk),
      mul_zero]
  push Not at hr
  set b : (J → Fin (N + 1)) → ℂ := fun γ => eval (coords h μ) (B γ)
  -- the polynomial in the free scalings
  let Ψ : MvPolynomial J ℂ := ∑ γ, C (b γ * ∏ k, rr k ^ (γ k : ℕ)) *
    monomial (Finsupp.equivFunOnFinite.symm fun k => (γ k : ℕ)) 1
  have hΨ : Ψ = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_zero]
    let ν : Fin m → ℂ := fun k => if hk : ∃ j, e j = k then s hk.choose else μ k
    have hνe : ∀ j, ν (e j) = s j := by
      intro j
      have hk : ∃ j', e j' = e j := ⟨j, rfl⟩
      simp only [ν, hk, ↓reduceDIte]
      rw [he hk.choose_spec]
    have hν : ∀ k, k ∉ Set.range e → ν k = μ k := by
      intro k hk
      have : ¬ ∃ j, e j = k := fun ⟨j, hj⟩ => hk ⟨j, hj⟩
      simp only [ν, this, ↓reduceDIte]
    have h0 := eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hvan h hh lam) ν
    rw [← h0, map_sum, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [map_mul, eval_C, eval_monomial, map_prod, map_pow, eval_X, coordsZ_e, hνe, one_mul]
    rw [Finsupp.prod_fintype _ _ (by simp), hB γ h ν (fun k => (μ k : ℂ)) hν]
    simp only [b, coords, mul_pow, Finset.prod_mul_distrib, rr, Finsupp.coe_equivFunOnFinite_symm]
    ring
  have hcoeff := congrArg (fun q : MvPolynomial J ℂ =>
    q.coeff (Finsupp.equivFunOnFinite.symm fun k => (γ₀ k : ℕ))) hΨ
  simp only [Ψ, coeff_sum, coeff_C_mul, coeff_monomial, AddMonoidAlgebra.coeff_zero] at hcoeff
  have hne : ∀ γ, γ ≠ γ₀ → (Finsupp.equivFunOnFinite.symm fun k => (γ k : ℕ)) ≠
      Finsupp.equivFunOnFinite.symm fun k => (γ₀ k : ℕ) := by
    intro γ hγ heq
    apply hγ
    funext k
    exact Fin.ext (by simpa using congrFun (congrArg (⇑) heq) k)
  rw [Finset.sum_eq_single γ₀ (fun γ _ hγ => by simp [hne γ hγ]) (by simp)] at hcoeff
  simp only [↓reduceIte, mul_one] at hcoeff
  have hprod : ∏ k, rr k ^ (γ₀ k : ℕ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr k)
  have hb : b γ₀ = 0 := (mul_eq_zero.mp hcoeff).resolve_right hprod
  rw [map_mul, show eval (coords h μ) (B γ₀) = b γ₀ from rfl, hb, zero_mul]

/-! ### The bound -/

/-- **The Hilbert lower bound with the free cone scalings**, for any `L0 ⊆ π_L(H⁰)`:
`H(L0; tD₀, tD₁) · ((tD₂+1)²)^{t₂} · (tD₂+1)^{m − t₂} ≤ H(vanish H⁰; tD)`. -/
theorem hfun_H0_ge_gen (hH : IsSubgroupG H) (hc : IsZClosed H)
    {L0 : Set (StrongSix.Thm1.GPt ℂ d₀ d₁)} (hL0 : L0 ⊆ projL (H0 Ls hH hc)) (D₀ D₁ D₂ t : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish L0) t *
          ((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb * (t * D₂ + 1) ^ (m - finrank ℂ tAb) ≤
        hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH hc)) t := by
  classical
  have hH0 := H0_isSubgroup hH hc
  have hc0 := isZClosed_H0 (Ls := Ls) hH hc
  obtain ⟨tAb, hab, htAb0, -⟩ := exists_abelianTangent_Htil hH0 hc0
  have htAb : ∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc := fun z =>
    (htAb0 z).trans (mem_lieAlg_H0 hH hc)
  refine ⟨tAb, hab, htAb, ?_⟩
  set r := finrank ℂ tAb
  obtain ⟨ι, hι, hsurj⟩ := exists_coord_surj tAb
  set n := t * D₂
  set a := hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish L0) t
  obtain ⟨A, hAmem, hAind⟩ := exists_indep_lift StrongSix.M2.blk ![D₀, D₁]
    (StrongSix.M2.vanish L0 : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) t
  let J := {k : Fin m // k ∉ Set.range ι}
  have hJ : Fintype.card J = m - r := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective hι,
      Fintype.card_fin]
  let κ := Fin (n + 1) × Fin (n + 1)
  let Pf0 : Fin a × (Fin r → κ) → MvPolynomial (Var d₀ d₁ m) ℂ := fun p =>
    rename ιL (A p.1) * ∏ l, monoP n (ι l) (p.2 l)
  let Vm : (J → Fin (n + 1)) → MvPolynomial (Var d₀ d₁ m) ℂ := fun γ =>
    ∏ k : J, X (.e k.1 1) ^ (γ k : ℕ)
  let Pf : (Fin a × (Fin r → κ)) × (J → Fin (n + 1)) → MvPolynomial (Var d₀ d₁ m) ℂ := fun p =>
    Pf0 p.1 * Vm p.2
  set F := FLE ℂ blk (t • Dfun (m := m) D₀ D₁ D₂)
  have hX : ∀ k c, (X (.e k c) : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
      FLE ℂ blk (Pi.single (Blk.e k) 1) := fun k c => by
    have := fle_X (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k c)
    rwa [blk_e] at this
  have hPfmem : ∀ p, Pf p ∈ F := by
    intro p
    have h1 : rename ιL (A p.1.1) ∈ FLE ℂ blk (fun b : Blk m => match b with
        | .x => t * D₀ | .yz => t * D₁ | .e _ => 0) := by
      refine rename_mem_FLE ιL (β := StrongSix.M2.blk) (fun i : Fin 2 => if i = 0 then Blk.x
        else Blk.yz) (fun v => ?_) (fun b => ?_) (hAmem p.1.1)
      · rcases v with i | j | j <;> rfl
      · cases b <;> simp [Fin.sum_univ_two]
    have h2 : ∏ l, monoP (d₀ := d₀) (d₁ := d₁) n (ι l) (p.1.2 l) ∈
        FLE ℂ blk (∑ l, Pi.single (Blk.e (ι l)) n) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun l _ => monoP_mem n (ι l) (p.1.2 l)
    have h3 : Vm p.2 ∈ FLE ℂ blk (∑ k : J, Pi.single (Blk.e k.1) n) := by
      refine StrongSix.M2.prod_mem_FLE' _ _ _ fun k _ => ?_
      refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
        (StrongSix.M2.pow_mem_FLE' (hX k.1 1) (p.2 k : ℕ))
      have := (p.2 k).isLt
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> omega
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ h1 h2) h3)
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    cases b with
    | x => simp [Dfun]
    | yz => simp [Dfun]
    | e k =>
      simp only [Pi.single_apply, Blk.e.injEq, zero_add, Dfun]
      by_cases hk : ∃ l, ι l = k
      · obtain ⟨l, rfl⟩ := hk
        rw [Finset.sum_eq_single l
          (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd (hι h.symm) hb) (by simp)]
        rw [Finset.sum_eq_zero (fun k' _ => ite_eq_right_iff.mpr fun h => absurd ⟨l, h⟩ k'.2)]
        simp [n]
      · push Not at hk
        rw [Finset.sum_eq_zero (fun l _ => ite_eq_right_iff.mpr fun h => absurd h.symm (hk l))]
        rw [Finset.sum_eq_single (⟨k, fun ⟨l, hl⟩ => hk l hl⟩ : J)
          (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd (Subtype.ext h.symm) hb) (by simp)]
        simp [n]
  -- independence modulo `vanish H⁰`
  set Q := F ⧸ Nsub (K := ℂ) blk (Dfun (m := m) D₀ D₁ D₂) (vanish (H0 Ls hH hc)) t
  let f : (Fin a × (Fin r → κ)) × (J → Fin (n + 1)) → Q := fun p =>
    Submodule.Quotient.mk ⟨Pf p, hPfmem p⟩
  have hind : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have hvan : ∑ p, c p • Pf p ∈ vanish (H0 Ls hH hc) := by
      have hmk : (Nsub (K := ℂ) blk (Dfun (m := m) D₀ D₁ D₂) (vanish (H0 Ls hH hc)) t).mkQ
          (∑ p, c p • (⟨Pf p, hPfmem p⟩ : F)) = 0 := by
        rw [map_sum]; exact hc0
      have := (Submodule.Quotient.mk_eq_zero _).mp hmk
      simpa using this
    have hsplit : ∑ p, c p • Pf p = ∑ γ, (∑ q, c (q, γ) • Pf0 q) * Vm γ := by
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by simp only [Pf, smul_mul_assoc]
    have hsep : ∀ γ₀, (∑ q, c (q, γ₀) • Pf0 q) * ∏ k : J, X (.e k.1 1) ∈
        vanish (H0 Ls hH hc) := by
      intro γ₀
      refine sep_free_scalings (J := J) Subtype.val Subtype.val_injective (N := n)
        (fun γ => ∑ q, c (q, γ) • Pf0 q) ?_ (hsplit ▸ hvan) γ₀
      intro γ g ν ν' hνν'
      have hι' : ∀ l, ν (ι l) = ν' (ι l) := fun l =>
        hνν' (ι l) (by rintro ⟨k, hk⟩; exact k.2 ⟨l, hk.symm⟩)
      simp only [map_sum, smul_eval, Pf0, map_mul, map_prod, eval_rename_ιL_Z, eval_monoP,
        coordsZ_e, hι']
    have hprime := vanish_H0_isPrime (Ls := Ls) hH hc
    have hV : ∏ k : J, (X (.e k.1 1) : MvPolynomial (Var d₀ d₁ m) ℂ) ∉ vanish (H0 Ls hH hc) := by
      intro hmem
      have := mem_vanish.mp hmem 0 hH0.zero_mem 1
      simp [map_prod, eval_coords_zero_V] at this
    have hB : ∀ γ₀, ∑ q, c (q, γ₀) • Pf0 q ∈ vanish (H0 Ls hH hc) := fun γ₀ =>
      (hprime.mem_or_mem (hsep γ₀)).resolve_right hV
    intro p
    obtain ⟨q, γ₀⟩ := p
    have := indep_H0_core hH hc htAb hι hsurj hL0 n A hAind (fun q => c (q, γ₀)) (hB γ₀)
    exact congrFun this q
  have hcard := hind.fintype_card_le_finrank
  rw [← hfun_eq_finrank_quotient] at hcard
  simpa [Fintype.card_prod, Fintype.card_fun, κ, Fintype.card_fin, sq, hJ] using hcard

/-- **The Hilbert lower bound, explicit form** (degree `t₀ + t₁ + t₂ + m` in `t`), for any
`V × T_{lsat U} ⊆ π_L(H⁰)`. -/
theorem hfun_H0_ge'' (hH : IsSubgroupG H) (hc : IsZClosed H) (V : Submodule ℂ (Fin d₀ → ℂ))
    (U : Submodule ℚ (Fin d₁ → ℚ))
    (hVU : StrongSix.M2.prodSet V (StrongSix.M2.lsat U) ⊆ projL (H0 Ls hH hc))
    (D₀ D₁ D₂ t : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      (t * D₀ / finrank ℂ V + 1) ^ finrank ℂ V *
          (t * D₁ / (d₁ - finrank ℚ U) + 1) ^ (d₁ - finrank ℚ U) *
          ((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb * (t * D₂ + 1) ^ (m - finrank ℂ tAb) ≤
        hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH hc)) t := by
  obtain ⟨tAb, hab, htAb, hle⟩ := hfun_H0_ge_gen hH hc hVU D₀ D₁ D₂ t
  refine ⟨tAb, hab, htAb, le_trans ?_ hle⟩
  have := StrongSix.M2.hfun_prodSet_ge (K := ℂ) V U D₀ D₁ t
  calc _ = ((t * D₀ / finrank ℂ V + 1) ^ finrank ℂ V *
          (t * D₁ / (d₁ - finrank ℚ U) + 1) ^ (d₁ - finrank ℚ U)) *
          (((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb * (t * D₂ + 1) ^ (m - finrank ℂ tAb)) := by ring
    _ ≤ hfun StrongSix.M2.blk ![D₀, D₁] ℂ
          (StrongSix.M2.vanish (StrongSix.M2.prodSet V (StrongSix.M2.lsat U))) t *
          (((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb * (t * D₂ + 1) ^ (m - finrank ℂ tAb)) :=
        Nat.mul_le_mul_right _ this
    _ = _ := by ring

/-- The linear part `ML = V × T_Λ` of `H⁰` (`ProductGraph`) lies in `π_L(H⁰)`, hence so does
`V × T_{lsat(qspan Λ)}`. Here `V = h₀` and `qspan Λ = U` in the product decomposition
`lieAlg_eq_prod` (`linV_ML_eq`). -/
theorem prodSet_ML_subset_projL (hH : IsSubgroupG H) (hc : IsZClosed H) :
    StrongSix.M2.prodSet (StrongSix.M2.linV (ML Ls hH hc))
        (StrongSix.M2.lsat (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) ⊆
      projL (H0 Ls hH hc) := by
  intro x hx
  have hx' : x ∈ ML Ls hH hc := by
    rw [ML_eq_prodSet hH hc]; exact StrongSix.M2.prodSet_sat_subset _ _ hx
  exact ⟨inLpt x, hx', rfl⟩

end LSG.ME
