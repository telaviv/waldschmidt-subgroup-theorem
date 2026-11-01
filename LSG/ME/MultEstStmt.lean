import Mathlib
import LSG.ME.SubgroupHilb2
import LSG.ME.Chain2

/-!
# The statement `MultEstAb` (STAGE2 §4, §11)

Philippon's multiplicity estimate on `G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` over `ℂ`, the curves
`E_k` given by period pairs `Ls k` (so nonsingular, `2 ≠ 0`), in the form of
`StrongSix.Thm1.MultEst`.

* `ObstrData d₀ d₁ Ls`: the obstruction subgroup `G′`, by its tangent data `(h₀, U, t)` (`t` an
  abelian tangent space, `IsAbelianTangent`) **without** `ℚ̄`-rationality of `h₀`, together with
  the subgroup itself, `grp = zcl (exp_G (T_{G′}))`, `T_{G′} = h₀ × U^⊥ × t` (`ObstrData.tan`).
  `grp` is a Zariski-closed subgroup with Lie algebra `T_{G′}` (`ObstrData.lie`: `exp(ℂ v) ⊆ grp`
  iff `v ∈ T_{G′}`). `Proper`: `T_{G′} ≠ Tan`.
* `ObstrData.toSubgroupData`: the map to `LSG.W88.SubgroupData Ls` under `ℚ̄`-rationality of `h₀`
  (automatic for `d₀ ≤ 1`, `ObstrData.toSubgroupData_of_le_one`); same tangent space.
* **`ObstrData.ofSubgroup`**: the obstruction attached to a Zariski-closed subgroup `H`: `grp = H⁰`,
  `T_{G′} = lieAlg H` (product decomposition `lieAlg_eq_prod`); `ofSubgroup_proper`: proper if
  `H ≠ G`.
* **`MultEstAb`**: the statement. Inequivalence modulo `G′` is `g − g′ ∉ grp`. The exponent of `D₂`
  is `t₂ = dim t` (projective dimension of the abelian part) against `m` on the right.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan IsAbelianTangent torusLie SubgroupData RationalOverQbar)
open StrongSix.M2 (FLE)

namespace LSG.ME

/-- **Obstruction data**: a connected algebraic subgroup `G′ ⊆ G(ℂ)` with tangent space
`h₀ × U^⊥ × t`, given by its tangent data and as a set `grp = zcl (exp_G (h₀ × U^⊥ × t))`. -/
structure ObstrData (d₀ d₁ : ℕ) {m : ℕ} (Ls : Fin m → PeriodPair) where
  /-- the additive part -/
  h0 : Submodule ℂ (Fin d₀ → ℂ)
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d₁ → ℚ)
  /-- the tangent space of the abelian part -/
  t : Submodule ℂ (Fin m → ℂ)
  t_ab : IsAbelianTangent Ls t
  /-- the subgroup itself -/
  grp : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))
  grp_eq : grp = zcl (expG Ls '' ((h0.prod ((torusLie U).prod t) : Submodule ℂ (Tan d₀ d₁ m)) :
    Set (Tan d₀ d₁ m)))
  grp_sub : IsSubgroupG grp
  grp_closed : IsZClosed grp
  /-- `T_{G′}` is the Lie algebra of `grp` -/
  lie : ∀ v : Tan d₀ d₁ m, (∀ c : ℂ, expG Ls (c • v) ∈ grp) ↔ v ∈ h0.prod ((torusLie U).prod t)

namespace ObstrData

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} (O : ObstrData d₀ d₁ Ls)

/-- The tangent space `T_{G′} = h₀ × U^⊥ × t`. -/
def tan : Submodule ℂ (Tan d₀ d₁ m) := O.h0.prod ((torusLie O.U).prod O.t)

/-- `G′ ≠ G`. -/
def Proper : Prop := O.tan ≠ ⊤

theorem expG_mem {u : Tan d₀ d₁ m} (hu : u ∈ O.tan) : expG Ls u ∈ O.grp :=
  by simpa using (O.lie u).mpr hu 1

/-- **To `W88.SubgroupData`**, given `ℚ̄`-rationality of `h₀`. -/
def toSubgroupData (hrat : RationalOverQbar O.h0) : SubgroupData (d0 := d₀) (d1 := d₁) Ls where
  h0 := O.h0
  U := O.U
  t := O.t
  h0_rat := hrat
  t_ab := O.t_ab

theorem toSubgroupData_tan (hrat : RationalOverQbar O.h0) : (O.toSubgroupData hrat).tan = O.tan :=
  rfl

/-- For `d₀ ≤ 1` the rationality is automatic. -/
noncomputable def toSubgroupData_of_le_one (hd : d₀ ≤ 1) : SubgroupData (d0 := d₀) (d1 := d₁) Ls :=
  O.toSubgroupData (rationalOverQbar_of_le_one hd _)

end ObstrData

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-- **The obstruction attached to a Zariski-closed subgroup `H`**: `grp = H⁰`,
`T_{G′} = lieAlg H = h₀ × U^⊥ × t`. -/
noncomputable def ObstrData.ofSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ObstrData d₀ d₁ Ls where
  h0 := (lieAlg Ls hH hc).comap (LinearMap.inl ℂ (Fin d₀ → ℂ) ((Fin d₁ → ℂ) × (Fin m → ℂ)))
  U := StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc))
  t := (lieAlg Ls hH hc).comap inAbL
  t_ab := isAbelianTangent_comap_inAbL hH hc
  grp := H0 Ls hH hc
  grp_eq := by rw [← lieAlg_eq_prod hH hc]; rfl
  grp_sub := H0_isSubgroup hH hc
  grp_closed := isZClosed_H0 hH hc
  lie v := by
    rw [← lieAlg_eq_prod hH hc, ← mem_lieAlg_H0 hH hc, mem_lieAlg]
    exact forall_congr' fun c => mem_Htil.symm

theorem ObstrData.ofSubgroup_tan (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (ObstrData.ofSubgroup hH hc).tan = lieAlg Ls hH hc :=
  (lieAlg_eq_prod hH hc).symm

theorem ObstrData.ofSubgroup_grp (hH : IsSubgroupG H) (hc : IsZClosed H) :
    (ObstrData.ofSubgroup hH hc).grp = H0 Ls hH hc := rfl

/-- **Properness**: if `H ≠ G` then `lieAlg H ≠ Tan` (else `H ⊇ H⁰ ⊇ exp_G(Tan) = G`). -/
theorem ObstrData.ofSubgroup_proper (hH : IsSubgroupG H) (hc : IsZClosed H) (hne : H ≠ Set.univ) :
    (ObstrData.ofSubgroup hH hc).Proper := by
  intro htop
  apply hne
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) Ls g
  have hu : u ∈ lieAlg Ls hH hc := by
    rw [← ObstrData.ofSubgroup_tan hH hc, htop]; trivial
  exact H0_subset hH hc (expG_mem_H0 hH hc hu)

/-! ### The statement -/

/-- **The multiplicity estimate on `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` over `ℂ`** (Philippon 1986,
Thm. 2.1, constants absorbed). `P` is homogeneous of degree `D₂` in each elliptic block, of block
degrees `≤ (D₀, D₁, D₂)`, `P ∉ I_G`, and has formal order `> n T` along `W` at every point of
`Σ(n)`, `n = d₀ + d₁ + m`. Then there is a proper obstruction `G′` with
`T^c · |F| · D₀^{t₀} D₁^{t₁} D₂^{t₂} ≤ C · D₀^{d₀} D₁^{d₁} D₂^m` for every `F ⊆ S` of points
pairwise inequivalent modulo `G′`, `c = dim W − dim (W ∩ T_{G′})`, `t₀ = dim h₀`,
`t₁ = d₁ − dim U`, `t₂ = dim t`. -/
def MultEstAb : Prop :=
  ∀ (d₀ d₁ m : ℕ) (Ls : Fin m → PeriodPair), ∃ C : ℕ,
    ∀ (W : Submodule ℂ (Tan d₀ d₁ m)) (S : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))
      (P : MvPolynomial (Var d₀ d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ S → IsHomE P (fun _ => D₂) →
      P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → P ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sig S (d₀ + d₁ + m), OrdGt (g2L Ls) (g3L Ls) W P ((d₀ + d₁ + m) * T) σ) →
      ∃ O : ObstrData d₀ d₁ Ls, O.Proper ∧
        ∀ F : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ finrank ℂ O.h0 *
              D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ finrank ℂ O.t ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m

end LSG.ME
