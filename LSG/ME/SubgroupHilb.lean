import Mathlib
import LSG.ME.SubgroupDim
import LSG.ME.SubgroupConeE
import LSG.ME.SubgroupHilbAux
import StrongSix.M2.Index

/-!
# The Hilbert lower bound for `H⁰` (STAGE2 §4–§5, item 6; `K = ℂ`)

Block degrees `D = (D₀, D₁, D₂, …, D₂)` (`Dfun`). For a Zariski-closed subgroup `H ⊆ G(ℂ)` with identity
component `H⁰`:

* `π_L(H⁰) = V × T_Λ` (StrongSix's `classify`), with identity component
  `L⁰ = V × T_{lsat(qspan Λ)}`; `t₀ = dim V = dim π₀(H⁰)`, `t₁ = d₁ − rk Λ = dim π₁(H⁰)`.
* `t` = the abelian tangent space of `H⁰` (`t ⊆ ℂ^m`, `z ∈ t ↔ (0, 0, z) ∈ lieAlg H`),
  `t₂ = dim t = dim (H⁰ ∩ (0 × 0 × E^m))`; `ι : Fin t₂ → Fin m` coordinates with `t ↠ ℂ^{t₂}`.
* **`exists_H0_point`**: `(π_L, π_ι) : H⁰ → L⁰ × E^{t₂}` is onto (surjectivity of `expE`, and
  `exp(0, 0, t) ⊆ H⁰`).
* **`hfun_H0_ge`**: `H(L⁰; tD₀, tD₁) · ((t D₂ + 1)²)^{t₂} ≤ H(vanish H⁰; t D)`: products of
  polynomials independent on `L⁰` with cone monomials (`monoF`) in the blocks `ι`, which are
  independent on `L⁰ × ∏ cone(E_{ι l})` (`indep_prod_fin`).
* **`hfun_H0_ge'`**: with StrongSix's `hfun_prodSet_ge`:
  `(tD₀/t₀ + 1)^{t₀} (tD₁/t₁ + 1)^{t₁} ((tD₂ + 1)²)^{t₂} ≤ H(vanish H⁰; tD)`
  (each elliptic factor of `H⁰` contributes `2 = 1 + 1` to the cone dimension).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan IsAbelianTangent)
open StrongSix.M2 (FLE hfun)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-- The block degrees `(D₀, D₁, D₂, …, D₂)`. -/
def Dfun (D₀ D₁ D₂ : ℕ) : Blk m → ℕ
  | .x => D₀
  | .yz => D₁
  | .e _ => D₂

/-! ### `lieAlg H⁰ = lieAlg H` -/

theorem mem_lieAlg_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) {v : Tan d₀ d₁ m} :
    v ∈ lieAlg Ls (H0_isSubgroup hH hc) (isZClosed_H0 hH hc) ↔ v ∈ lieAlg Ls hH hc := by
  rw [mem_lieAlg, mem_lieAlg]
  constructor
  · intro h c; exact mem_Htil.mpr (H0_subset hH hc (mem_Htil.mp (h c)))
  · intro h c
    exact mem_Htil.mpr (expG_mem_H0 hH hc (mem_lieAlg.mpr fun c' => by
      rw [smul_smul]; exact h _))

/-! ### Linear variables and cone monomials -/

/-- The linear variables inside `Var`. -/
def ιL : StrongSix.M2.V3 d₀ d₁ → Var d₀ d₁ m
  | .inl i => .x i
  | .inr (.inl j) => .y j
  | .inr (.inr j) => .z j

theorem eval_rename_ιL (g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) (lam : Fin m → ℂˣ)
    (P : MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ) :
    eval (coords g lam) (rename ιL P) = eval (StrongSix.M2.pt (linPt g)) P := by
  rw [eval_rename]
  congr 2
  funext v
  rcases v with i | j | j <;> rfl

/-- The cone monomial `monoF n p` in block `k`. -/
noncomputable def monoP (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) :
    MvPolynomial (Var d₀ d₁ m) ℂ :=
  if (p.1 : ℕ) ≤ p.2 then X (.e k 0) ^ (p.1 : ℕ) * X (.e k 2) ^ ((p.2 : ℕ) - p.1)
  else X (.e k 1) * X (.e k 0) ^ (p.2 : ℕ) * X (.e k 2) ^ ((p.1 : ℕ) - 1 - p.2)

theorem eval_monoP (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) (x : Var d₀ d₁ m → ℂ) :
    eval x (monoP n k p) = monoF n p (fun c => x (.e k c)) := by
  unfold monoP monoF
  split_ifs <;> simp

theorem monoP_mem (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) :
    monoP (d₀ := d₀) (d₁ := d₁) n k p ∈ FLE ℂ blk (Pi.single (Blk.e k) n) := by
  classical
  obtain ⟨i, j⟩ := p
  have hX : ∀ c, (X (.e k c) : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ FLE ℂ blk (Pi.single (Blk.e k) 1) :=
    fun c => by
      have := fle_X (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.e k c)
      rwa [blk_e] at this
  have hpow : ∀ c (a : ℕ), (X (.e k c) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ a ∈
      FLE ℂ blk (Pi.single (Blk.e k) a) := fun c a => by
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (StrongSix.M2.pow_mem_FLE' (hX c) a)
    simp [Pi.single_apply]
  have hi := i.isLt
  have hj := j.isLt
  unfold monoP
  dsimp only
  split_ifs with h
  · refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ (hpow 0 i) (hpow 2 (j - i)))
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  · push Not at h
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ (hX 1) (hpow 0 j)) (hpow 2 (i - 1 - j)))
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega

/-! ### Surjectivity of `(π_L, π_ι)` on `H⁰` -/

/-- **Onto `L⁰ × E^{t₂}`.** -/
theorem exists_H0_point (hH : IsSubgroupG H) (hc : IsZClosed H) {tAb : Submodule ℂ (Fin m → ℂ)}
    (htAb : ∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) {r : ℕ}
    {ι : Fin r → Fin m} (hsurj : ∀ y : Fin r → ℂ, ∃ z ∈ tAb, ∀ l, z (ι l) = y l)
    {x : StrongSix.Thm1.GPt ℂ d₀ d₁} (hx : x ∈ projL (H0 Ls hH hc))
    (e : ∀ l, EPt (g2L Ls) (g3L Ls) (ι l)) :
    ∃ g ∈ H0 Ls hH hc, linPt g = x ∧ ∀ l, g.2.2 (ι l) = e l := by
  obtain ⟨g', hg', rfl⟩ := hx
  choose w hw using fun l => expE_surjective (Ls (ι l)) (e l - g'.2.2 (ι l))
  obtain ⟨z, hz, hzι⟩ := hsurj w
  have hmem : expG Ls (inAb (d₀ := d₀) (d₁ := d₁) z) ∈ H0 Ls hH hc :=
    expG_mem_H0 hH hc ((htAb z).mp hz)
  refine ⟨g' + expG Ls (inAb z), (H0_isSubgroup hH hc).add_mem _ hg' _ hmem, ?_, fun l => ?_⟩
  · refine Prod.ext (by simp [linPt, expG, inAb]) ?_
    show Additive.toMul (g'.2.1 + Additive.ofMul fun j => expU 0) = Additive.toMul g'.2.1
    rw [toMul_add, toMul_ofMul]
    convert mul_one (Additive.toMul g'.2.1)
    exact Units.ext (by simp [expU])
  · have h1 : (g' + expG Ls (inAb z)).2.2 (ι l) =
        g'.2.2 (ι l) + (expG Ls (inAb (d₀ := d₀) (d₁ := d₁) z)).2.2 (ι l) := rfl
    have h2 : (expG Ls (inAb (d₀ := d₀) (d₁ := d₁) z)).2.2 (ι l) = expE (Ls (ι l)) (w l) := by
      rw [← hzι]; rfl
    rw [h1, h2, hw, add_sub_cancel]

/-! ### The bound -/

/-- A cone point of `E_k` gives a point of `E_k`. -/
theorem exists_pt_of_coneE (k : Fin m) {u v : ℂ} (huv : v ^ 2 = 4 * u ^ 3 - g2L Ls k * u - g3L Ls k) :
    ∃ e : EPt (g2L Ls) (g3L Ls) k, rep e = ![u, v, 1] := by
  have heq : (curve (g2L Ls k) (g3L Ls k)).toAffine.Equation u (v / 2) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [LSG.Elliptic.curve, zero_mul, add_zero]
    linear_combination huv / 4
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (by rw [curve_Δ two_ne_zero]; exact discr_g2L Ls k)).mp heq
  refine ⟨.some u (v / 2) hns, ?_⟩
  funext c
  fin_cases c <;> simp [rep]
  ring

/-- **The Hilbert lower bound with projection-based exponents.** -/
theorem hfun_H0_ge (hH : IsSubgroupG H) (hc : IsZClosed H) (D₀ D₁ D₂ t : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish (StrongSix.M2.prodSet
          (StrongSix.M2.linV (projL (H0 Ls hH hc)))
          (StrongSix.M2.lsat (StrongSix.M2.qspan (StrongSix.M2.latt (projL (H0 Ls hH hc))))))) t *
        ((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb ≤
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
  -- the linear part
  set L0 := StrongSix.M2.prodSet (StrongSix.M2.linV (projL (H0 Ls hH hc)))
    (StrongSix.M2.lsat (StrongSix.M2.qspan (StrongSix.M2.latt (projL (H0 Ls hH hc)))))
  have hL0 : L0 ⊆ projL (H0 Ls hH hc) := by
    rw [projL_eq_prodSet two_ne_zero (discr_g2L Ls) hH0 hc0]
    exact StrongSix.M2.prodSet_sat_subset _ _
  set a := hfun StrongSix.M2.blk ![D₀, D₁] ℂ (StrongSix.M2.vanish L0) t
  obtain ⟨A, hAmem, hAind⟩ := exists_indep_lift StrongSix.M2.blk ![D₀, D₁]
    (StrongSix.M2.vanish L0 : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) t
  -- the family
  let κ := Fin (n + 1) × Fin (n + 1)
  let Pf : Fin a × (Fin r → κ) → MvPolynomial (Var d₀ d₁ m) ℂ := fun p =>
    rename ιL (A p.1) * ∏ l, monoP n (ι l) (p.2 l)
  set F := FLE ℂ blk (t • Dfun (m := m) D₀ D₁ D₂)
  have hPfmem : ∀ p, Pf p ∈ F := by
    intro p
    have h1 : rename ιL (A p.1) ∈ FLE ℂ blk (fun b : Blk m => match b with
        | .x => t * D₀ | .yz => t * D₁ | .e _ => 0) := by
      refine rename_mem_FLE ιL (β := StrongSix.M2.blk) (fun i : Fin 2 => if i = 0 then Blk.x
        else Blk.yz) (fun v => ?_) (fun b => ?_) (hAmem p.1)
      · rcases v with i | j | j <;> rfl
      · cases b <;> simp [Fin.sum_univ_two]
    have h2 : ∏ l, monoP (d₀ := d₀) (d₁ := d₁) n (ι l) (p.2 l) ∈
        FLE ℂ blk (∑ l, Pi.single (Blk.e (ι l)) n) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun l _ => monoP_mem n (ι l) (p.2 l)
    refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_) (StrongSix.M2.mul_mem_FLE ℂ h1 h2)
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    cases b with
    | x => simp [Dfun]
    | yz => simp [Dfun]
    | e k =>
      simp only [Pi.single_apply, Blk.e.injEq, zero_add, Dfun]
      by_cases hk : ∃ l, ι l = k
      · obtain ⟨l, rfl⟩ := hk
        rw [Finset.sum_eq_single l (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd (hι h.symm) hb)
          (by simp)]
        simp [n]
      · push Not at hk
        simp [Ne.symm (hk _)]
  -- independence modulo `vanish H⁰`
  set Q := F ⧸ Nsub (K := ℂ) blk (Dfun (m := m) D₀ D₁ D₂) (vanish (H0 Ls hH hc)) t
  let f : Fin a × (Fin r → κ) → Q := fun p => Submodule.Quotient.mk ⟨Pf p, hPfmem p⟩
  have hind : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    -- the combination vanishes on `H⁰`
    have hvan : ∑ p, c p • Pf p ∈ vanish (H0 Ls hH hc) := by
      have hmk : (Nsub (K := ℂ) blk (Dfun (m := m) D₀ D₁ D₂) (vanish (H0 Ls hH hc)) t).mkQ
          (∑ p, c p • (⟨Pf p, hPfmem p⟩ : F)) = 0 := by
        rw [map_sum]; exact hc0
      have := (Submodule.Quotient.mk_eq_zero _).mp hmk
      simpa using this
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
    intro p
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
  have hcard := hind.fintype_card_le_finrank
  rw [← hfun_eq_finrank_quotient] at hcard
  simpa [Fintype.card_prod, Fintype.card_fun, κ, Fintype.card_fin, sq] using hcard

/-- **The Hilbert lower bound, explicit form.** -/
theorem hfun_H0_ge' (hH : IsSubgroupG H) (hc : IsZClosed H) (D₀ D₁ D₂ t : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧
      (t * D₀ / finrank ℂ (StrongSix.M2.linV (projL (H0 Ls hH hc))) + 1) ^
          finrank ℂ (StrongSix.M2.linV (projL (H0 Ls hH hc))) *
        (t * D₁ / (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (projL (H0 Ls hH hc))))) +
          1) ^ (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (projL (H0 Ls hH hc))))) *
        ((t * D₂ + 1) ^ 2) ^ finrank ℂ tAb ≤
      hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH hc)) t := by
  obtain ⟨tAb, hab, htAb, hle⟩ := hfun_H0_ge hH hc D₀ D₁ D₂ t
  exact ⟨tAb, hab, htAb, le_trans (Nat.mul_le_mul_right _
    (StrongSix.M2.hfun_prodSet_ge _ _ D₀ D₁ t)) hle⟩

end LSG.ME
