import Mathlib
import LSG.MEV.SubgroupAbV
import LSG.MEV.SubgroupPush
import LSG.ME.SubgroupHilb2
import LSG.W88.K11Lin

/-!
# The Hilbert lower bound for `H⁰ ⊆ G̃` (gap G4), part 1: the base layer

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)`, `T′ = lieAlg H`, `t = π_Z(T′)`:

* `L0V hH = V × T_{lsat U₀}` with `V = π₀(Γ)` (`Γ = T′ ∩ (vector group)`) and
  `U₀ = qspan Λ(HL H⁰)`: the linear part used for the Hilbert function (StrongSix's
  `hfun_prodSet_ge` applies to it).
* `FibV hH = {w | (0, 0, 0, w) ∈ T′}`: the pure fibre directions of `T′`.
* **`exists_H0_pointV`**: `(π_L, base_ι) : H⁰ → L0V × ∏_l E_{ι l}` is onto, for coordinates `ι` with
  `t ↠ ℂ^ι`. (Points `exp(vecIncl(a, w) + g2Incl(z, w′)) + inLin(0, y)`; `g2Incl(z, w′) ∈ T′` by
  `perTanId t ⊆ T′`, which uses G1.)
* `monoPV`: the abelian cone monomials `monoF` in the base coordinates `(U, V, W)` of a block.
* **`indep_coreV`**: polynomials independent modulo `vanish L0V`, times cone monomials in the
  blocks `ι`, are independent modulo `vanish H⁰` (`indep_prod_fin`, `monoF_linearIndependent`).
* `coeff_sep`: a polynomial identity on a product of infinite sets has zero coefficients.
* **Exponents**: `t₂ := dim (T′ ∩ ker π₀ ∩ ker π₁) = dim t + dim FibV` (`finrank_T2`), and
  `t₀ + t₁ + t₂ = dim T′` (`t0_add_t1_add_t2`), so the lower bound of part 2 has degree
  `t₀ + t₁ + t₂ + m = hdim (vanish H⁰)` (`hdim_H0`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module Set
open LSG.W88 (IsAbelianTangent torusLie)
open LSG.W88.Vec (vecIncl torIncl g2Incl perTanId perTan)
open StrongSix.M2 (FLE hfun)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Linear variables and cone monomials -/

theorem repV_base {L : PeriodPair} (q : EVL L) (c : Fin 3) :
    repV q c.castSucc.castSucc = rep q.base c := by
  have := congrFun (Pe_repV q) c
  rwa [Pe_apply] at this

/-- The linear variables inside `Var`. -/
def ιLV : StrongSix.M2.V3 d₀ d₁ → Var d₀ d₁ m
  | .inl i => .x i
  | .inr (.inl j) => .y j
  | .inr (.inr j) => .z j

/-- The linear point `(x, y)` of a point of `G̃`. -/
def linPtG (g : GPtV d₀ d₁ Ls) : StrongSix.Thm1.GPt ℂ d₀ d₁ := (g.1, fun j => g.ym j)

theorem eval_rename_ιLV (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ)
    (P : MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ) :
    eval (coordsZ g ν) (rename ιLV P) = eval (StrongSix.M2.pt (linPtG g)) P := by
  rw [eval_rename]
  congr 2
  funext v
  rcases v with i | j | j <;> rfl

theorem eval_rename_ιLV' (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ)
    (P : MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ) :
    eval (coords g lam) (rename ιLV P) = eval (StrongSix.M2.pt (linPtG g)) P :=
  eval_rename_ιLV g _ P

/-- The cone monomial `monoF n p` in the base coordinates of block `k`. -/
def monoPV (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  rename mvV (LSG.ME.monoP (d₀ := d₀) (d₁ := d₁) n k p)

theorem eval_monoPV (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) (x : Var d₀ d₁ m → ℂ) :
    eval x (monoPV n k p) = LSG.ME.monoF n p (fun c => x (.e k c.castSucc.castSucc)) := by
  rw [monoPV, eval_rename, LSG.ME.eval_monoP]; rfl

theorem monoPV_mem (n : ℕ) (k : Fin m) (p : Fin (n + 1) × Fin (n + 1)) :
    monoPV (d₀ := d₀) (d₁ := d₁) n k p ∈ FLE ℂ blk (Pi.single (LSG.ME.Blk.e k) n) := by
  classical
  refine LSG.ME.rename_mem_FLE mvV (β := LSG.ME.blk) id (fun v => by cases v <;> rfl)
    (fun i' => ?_) (LSG.ME.monoP_mem n k p)
  simp

/-! ### Polynomial identities on products -/

/-- **Coefficients of a polynomial identity on a product of infinite sets vanish.** -/
theorem coeff_sep {J : Type*} [Fintype J] [DecidableEq J] {N : ℕ} (E : (J → Fin (N + 1)) → ℂ)
    (S : J → Set ℂ) (hS : ∀ j, (S j).Infinite)
    (h : ∀ x : J → ℂ, (∀ j, x j ∈ S j) → ∑ γ, E γ * ∏ j, x j ^ (γ j : ℕ) = 0) : E = 0 := by
  classical
  let Ψ : MvPolynomial J ℂ := ∑ γ, monomial (Finsupp.equivFunOnFinite.symm fun j => (γ j : ℕ)) (E γ)
  have hΨ : Ψ = 0 := by
    refine funext_set S hS fun x hx => ?_
    rw [map_zero, ← h x fun j => hx j (Set.mem_univ j), map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp
  funext γ₀
  have hcoeff := congrArg (fun q : MvPolynomial J ℂ =>
    q.coeff (Finsupp.equivFunOnFinite.symm fun j => (γ₀ j : ℕ))) hΨ
  simp only [Ψ, coeff_sum, coeff_monomial, AddMonoidAlgebra.coeff_zero] at hcoeff
  have hne : ∀ γ, γ ≠ γ₀ → (Finsupp.equivFunOnFinite.symm fun j => (γ j : ℕ)) ≠
      Finsupp.equivFunOnFinite.symm fun j => (γ₀ j : ℕ) := by
    intro γ hγ heq
    apply hγ
    funext j
    exact Fin.ext (by simpa using congrFun (congrArg (⇑) heq) j)
  rw [Finset.sum_eq_single γ₀ (fun γ _ hγ => by simp [hne γ hγ]) (by simp)] at hcoeff
  simpa using hcoeff

/-! ### The linear part and the fibre directions -/

variable {H : Set (GPtV d₀ d₁ Ls)}

variable (Ls) in
/-- `V × T_{lsat U₀}`: `V = π₀(Γ)`, `U₀ = qspan Λ(HL H⁰)`. -/
def L0V (hH : IsSubgroupG H) : Set (StrongSix.Thm1.GPt ℂ d₀ d₁) :=
  StrongSix.M2.prodSet (((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ _ _))
    (StrongSix.M2.lsat (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH)))))

variable (Ls) in
/-- The pure fibre directions `{w | (0, 0, 0, w) ∈ T′}`. -/
def FibV (hH : IsSubgroupG H) : Submodule ℂ (Fin m → ℂ) :=
  ((lieAlg Ls hH).comap vecIncl).comap (LinearMap.inr ℂ (Fin d₀ → ℂ) (Fin m → ℂ))

theorem mem_FibV {hH : IsSubgroupG H} {w : Fin m → ℂ} :
    w ∈ FibV Ls hH ↔ ((0, 0, 0, w) : TanG d₀ d₁ m) ∈ lieAlg Ls hH := Iff.rfl

section Points

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **Onto `L0V × ∏ E_{ι l}`.** -/
theorem exists_H0_pointV {r : ℕ} {ι : Fin r → Fin m}
    (hsurj : ∀ y : Fin r → ℂ, ∃ z ∈ (lieAlg Ls hH).map piZ, ∀ l, z (ι l) = y l)
    {x : StrongSix.Thm1.GPt ℂ d₀ d₁} (hx : x ∈ L0V Ls hH)
    (e : ∀ l, (curve (Ls (ι l)).g₂ (Ls (ι l)).g₃).toAffine.Point) :
    ∃ g ∈ H0 Ls hH, linPtG g = x ∧ ∀ l, (g.2.2 (ι l)).base = e l := by
  classical
  have hab := isAbelianTangent_map_piZ hH hc
  have hH0 := H0_isSubgroup hH
  have hc0 := isZClosed_H0 (Ls := Ls) hH
  obtain ⟨hxa, hxy⟩ := hx
  obtain ⟨p, hp, hpa⟩ := Submodule.mem_map.mp hxa
  choose ζ hζ using fun l => LSG.ME.expE_surjective (Ls (ι l)) (e l)
  obtain ⟨z, hz, hzι⟩ := hsurj ζ
  obtain ⟨w, hw⟩ := exists_perTanId hab hz
  have hg2 : (g2Incl (z, w) : TanG d₀ d₁ m) ∈ lieAlg Ls hH :=
    perTan_map_le hH hc hab (Submodule.mem_map.mpr ⟨(z, w), by rwa [perTan_one], rfl⟩)
  -- the torus point
  have hy : inLin Ls ((0 : Fin (d₀ + m) → ℂ), x.2) ∈ H0 Ls hH := by
    have hmem : ((0 : Fin (d₀ + m) → ℂ), x.2) ∈ HL Ls (H0 Ls hH) := by
      rw [HL_eq_prodSet hH0 hc0]
      exact StrongSix.M2.prodSet_sat_subset _ _ ⟨Submodule.zero_mem _, hxy⟩
    exact hmem
  set u : TanG d₀ d₁ m := vecIncl p + g2Incl (z, w)
  have hu : u ∈ lieAlg Ls hH := (lieAlg Ls hH).add_mem hp hg2
  refine ⟨expGV Ls u + inLin Ls ((0 : Fin (d₀ + m) → ℂ), x.2),
    hH0.add_mem _ (expGV_mem_H0 hH hu) _ hy, ?_, fun l => ?_⟩
  · refine Prod.ext ?_ ?_
    · funext i
      simp [linPtG, u, expGV, inLin, ← hpa]
    · funext j
      apply Units.ext
      simp [linPtG, u, expGV, inLin, GPtV.ym, LSG.ME.expU]
  · show (expV (Ls (ι l)) (u.2.2.1 (ι l), u.2.2.2 (ι l)) + ⟨0, 0⟩).base = e l
    rw [add_base, expV_base]
    simp only [u, Prod.snd_add, Prod.fst_add, Pi.add_apply, vecIncl_apply, g2Incl_apply,
      Pi.zero_apply, zero_add, hzι l, hζ l]
    exact add_zero _

/-- **Independence on `L0V × ∏ cone(E_{ι l})`.** -/
theorem indep_coreV {r : ℕ} {ι : Fin r → Fin m} (hι : Function.Injective ι)
    (hsurj : ∀ y : Fin r → ℂ, ∃ z ∈ (lieAlg Ls hH).map piZ, ∀ l, z (ι l) = y l)
    (n : ℕ) {a : ℕ} (A : Fin a → MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)
    (hAind : ∀ c : Fin a → ℂ, ∑ i, c i • A i ∈
      (StrongSix.M2.vanish (L0V Ls hH) : Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) → c = 0)
    (c : Fin a × (Fin r → Fin (n + 1) × Fin (n + 1)) → ℂ)
    (hvan : ∑ p, c p • (rename ιLV (A p.1) * ∏ l, monoPV n (ι l) (p.2 l)) ∈ vanish (H0 Ls hH)) :
    c = 0 := by
  classical
  let κ := Fin (n + 1) × Fin (n + 1)
  have heval : ∀ x ∈ L0V Ls hH, ∀ z : Fin r → Fin 3 → ℂ,
      (∀ l, z l ∈ LSG.ME.coneE (LSG.ME.g2L Ls (ι l)) (LSG.ME.g3L Ls (ι l))) →
      ∑ β : Fin r → κ, (∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i)) *
        ∏ l, LSG.ME.monoF n (β l) (z l) = 0 := by
    intro x hx z hz
    choose lam u v hl huv hzl using hz
    choose e he using fun l => LSG.ME.exists_pt_of_coneE (Ls := Ls) (ι l) (huv l)
    obtain ⟨g, hg, hgx, hge⟩ := exists_H0_pointV hH hc hsurj hx e
    let μ : Fin m → ℂˣ := fun k =>
      if h : ∃ l, ι l = k then Units.mk0 (lam h.choose) (hl _) else 1
    have hμ : ∀ l, (μ (ι l) : ℂ) = lam l := by
      intro l
      have h : ∃ l', ι l' = ι l := ⟨l, rfl⟩
      simp only [μ, h, ↓reduceDIte, Units.val_mk0]
      rw [hι h.choose_spec]
    have hblock : ∀ l, (fun c => coords g μ (.e (ι l) c.castSucc.castSucc)) = z l := by
      intro l
      funext c'
      simp only [coords, coordsZ_e, hμ, repV_base, hge l, hzl l]
      refine (congrArg (fun q => lam l * q) (congrFun (he l) c')).trans ?_
      fin_cases c' <;> simp
    have key : ∑ β : Fin r → κ, (∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i)) *
        ∏ l, LSG.ME.monoF n (β l) (z l) =
        eval (coords g μ) (∑ p, c p • (rename ιLV (A p.1) * ∏ l, monoPV n (ι l) (p.2 l))) := by
      rw [map_sum, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eval]
      simp only [map_mul, map_prod, eval_rename_ιLV', hgx, eval_monoPV, hblock]
      ring
    rw [key]
    exact mem_vanish.mp hvan g hg μ
  funext p
  obtain ⟨i₀, β₀⟩ := p
  have hzero : ∀ x ∈ L0V Ls hH, ∀ β : Fin r → κ,
      ∑ i, c (i, β) * eval (StrongSix.M2.pt x) (A i) = 0 := by
    intro x hx
    have hne : ∀ l, (LSG.ME.coneE (LSG.ME.g2L Ls (ι l)) (LSG.ME.g3L Ls (ι l))).Nonempty := by
      intro l
      obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq
        (4 * (0 : ℂ) ^ 3 - LSG.ME.g2L Ls (ι l) * 0 - LSG.ME.g3L Ls (ι l)) (n := 2) (by norm_num)
      exact ⟨_, 1, 0, v, one_ne_zero, hv, rfl⟩
    have := LSG.ME.indep_prod_fin (LSG.ME.monoF (K := ℂ) n) r
      (fun l => LSG.ME.coneE (LSG.ME.g2L Ls (ι l)) (LSG.ME.g3L Ls (ι l)))
      hne (fun l => LSG.ME.monoF_linearIndependent two_ne_zero _ _ n) _ (heval x hx)
    exact fun β => congrFun this β
  have hβ : ∑ i, c (i, β₀) • A i ∈ (StrongSix.M2.vanish (L0V Ls hH) :
      Ideal (MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)) := by
    intro x hx
    simpa [map_sum, mul_comm] using hzero x hx β₀
  exact congrFun (hAind _ hβ) i₀

end Points

/-! ### Exponents -/

section Exps

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- `d₁ − dim U₀ = t₁ = dim (T′ ∩ torus)`. -/
theorem d1_sub_U0 :
    d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH)))) =
      finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m)) := by
  have hH0 := H0_isSubgroup hH
  have hc0 := isZClosed_H0 (Ls := Ls) hH
  have hab0 := isAbelianTangent_map_piZ hH0 hc0
  have h1 := lieAlg_comap_torIncl hH0 hc0 hab0
  rw [lieAlg_H0 hH hc] at h1
  rw [h1]
  have : finrank ℂ (torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH))))) +
      finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls (H0 Ls hH)))) = d₁ :=
    LSG.W88.K11.finrank_annC _
  omega

/-- **`t₂ = dim t + dim FibV`.** -/
theorem finrank_T2 :
    finrank ℂ ↥(lieAlg Ls hH ⊓ (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓
      LinearMap.ker prB)) = finrank ℂ ((lieAlg Ls hH).map piZ) + finrank ℂ (FibV Ls hH) := by
  classical
  have hab := isAbelianTangent_map_piZ hH hc
  set T := lieAlg Ls hH
  set T₂ := T ⊓ (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓ LinearMap.ker prB)
  set g := (piZ (d₀ := d₀) (d₁ := d₁) (m := m)).comp T₂.subtype
  have hrange : LinearMap.range g = T.map piZ := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact Submodule.mem_map.mpr ⟨u.1, u.2.1, rfl⟩
    · intro z hz
      obtain ⟨w, hw⟩ := exists_perTanId hab hz
      have hg2 : (g2Incl (z, w) : TanG d₀ d₁ m) ∈ T :=
        perTan_map_le hH hc hab (Submodule.mem_map.mpr ⟨(z, w), by rwa [perTan_one], rfl⟩)
      refine ⟨⟨g2Incl (z, w), hg2, ?_, ?_⟩, rfl⟩
      · simp
      · simp
  -- the kernel is `FibV`
  let φ : FibV Ls hH →ₗ[ℂ] LinearMap.ker g :=
    { toFun := fun w => ⟨⟨vecIncl (0, w.1), w.2, by simp, by simp⟩, by simp [g]⟩
      map_add' := fun w w' => by ext <;> simp
      map_smul' := fun c w => by ext <;> simp }
  have hφ : Function.Bijective φ := by
    constructor
    · intro w w' h
      have := congrArg (fun x : LinearMap.ker g => ((x : T₂) : TanG d₀ d₁ m).2.2.2) h
      exact Subtype.ext (by simpa [φ] using this)
    · rintro ⟨⟨u, huT, hA, hB⟩, hu⟩
      have hz : u.2.2.1 = 0 := LinearMap.mem_ker.mp hu
      have hA' : u.1 = 0 := hA
      have hB' : u.2.1 = 0 := hB
      have hue : u = vecIncl (0, u.2.2.2) := by ext <;> simp [hA', hB', hz]
      refine ⟨⟨u.2.2.2, ?_⟩, ?_⟩
      · show vecIncl (0, u.2.2.2) ∈ T
        rw [← hue]; exact huT
      · ext <;> simp [φ, hA', hB', hz]
  have hk := (LinearEquiv.ofBijective φ hφ).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange] at hrn
  omega

/-- **`t₀ + t₁ + t₂ = dim T′`** (`SubgroupPreV.finrank_tan_eq` for the classification datum). -/
theorem t0_add_t1_add_t2 :
    finrank ℂ (((lieAlg Ls hH).comap vecIncl).map (LinearMap.fst ℂ (Fin d₀ → ℂ) (Fin m → ℂ))) +
      finrank ℂ ((lieAlg Ls hH).comap (torIncl : (Fin d₁ → ℂ) →ₗ[ℂ] TanG d₀ d₁ m)) +
      finrank ℂ ↥(lieAlg Ls hH ⊓ (LinearMap.ker (prA : TanG d₀ d₁ m →ₗ[ℂ] (Fin d₀ → ℂ)) ⊓
        LinearMap.ker prB)) = finrank ℂ (lieAlg Ls hH) := by
  obtain ⟨S, hS, hU, -, hgam⟩ := exists_subgroupV hH hc
  have h := S.finrank_tan_eq
  have htor := lieAlg_comap_torIncl hH hc (isAbelianTangent_map_piZ hH hc)
  rw [hS, hgam, hU, ← htor] at h
  exact h.symm

end Exps

end

end LSG.MEV
