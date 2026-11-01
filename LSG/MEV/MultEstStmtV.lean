import Mathlib
import LSG.MEV.ChainV
import LSG.MEV.SubgroupPush
import LSG.ME.SubgroupHilb

/-!
# The statement `MultEstVec`: the multiplicity estimate for the vector-extension class

`G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of `(E₁ × ⋯ × E_m)^♮` along `M : ℂ^m → ℂ^r`
(`LSG/W88/StatementVec.lean`). Every such `G` is the quotient `G̃_r / K_M` of

  `G̃_r = G_a^{d₀+r} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮`  (the model of `LSG.MEV` with `d₀ + r` additive
  coordinates)

by the vector subgroup `K_M = {(0, −Mv; 0; 0, v) : v ∈ ℂ^m}` (`kerK M`): the last `r` additive
coordinates are the vector part of `G₂` (this also covers non-onto `M`, e.g. `M = 0`,
`G₂ = E^m × G_a`).

* `toLie : TanG ≃ LieV`: the two coordinate systems of `Lie G̃` (`(a, b, z, w)` of the subgroup
  layer,
  `(a, b, (z_k, w_k)_k)` of `OrdGt`).
* `kvec M v = (0, −Mv; 0; 0, v)`, `kerK M = range (kvec M)`.
* `InvarK Ls M P`: `P` is a polynomial on `G`, i.e. invariant under translation by `K_M`
  (on all cone representatives).
* `TrailDeg D P`: degree `≤ D` in the `r` trailing additive variables (they belong to `G₂`, so W88
  gives
  them the elliptic degree `D₂`).
* `ObstrDataV`: the obstruction, a member `S` of the family of `G̃_r` (`SubgroupPreV`: `U`, `t`,
  `Γ`, no
  rationality), the subgroup `grp = zcl (exp T̃′)` with Lie algebra `T̃′ = S.tan ⊇ K_M`.
  W88's projection exponents of `G′ = G̃′ / K_M`: `t₀ = dim pr_{G_a^{d₀}} T̃′` (`t0`),
  `t₁ = d₁ − dim U`, `t₂ = dim (T̃′ ∩ ker pr_{G_a^{d₀}} ∩ ker pr_{G_m})` (`t2`; it counts `K_M`, so
  the right
  side has `D₂^{2m + r}`, i.e. `D₂^{d₂}` with `d₂ = m + r` after dividing by `D₂^{dim K_M}`).
* **`MultEstVec`**, in the style of `LSG.ME.MultEstAb`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.ME (g2L g3L Dfun)
open StrongSix.M2 (FLE)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m r : ℕ}

/-! ### The two coordinate systems of `Lie G̃` -/

/-- `(a, b, z, w) ↦ (a, b, (z_k, w_k)_k)`. -/
def toLie : TanG d₀ d₁ m ≃ₗ[ℂ] LieV ℂ d₀ d₁ m where
  toFun p := (p.1, p.2.1, fun k => (p.2.2.1 k, p.2.2.2 k))
  invFun q := (q.1, q.2.1, fun k => (q.2.2 k).1, fun k => (q.2.2 k).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toLie_apply (p : TanG d₀ d₁ m) :
    toLie p = (p.1, p.2.1, fun k => (p.2.2.1 k, p.2.2.2 k)) := rfl

/-! ### The kernel of `G̃_r → G` -/

/-- `v ↦ (0, −Mv; 0; 0, v)`. -/
def kvec (M : Matrix (Fin r) (Fin m) ℂ) : (Fin m → ℂ) →ₗ[ℂ] TanG (d₀ + r) d₁ m where
  toFun v := (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec v), 0, 0, v)
  map_add' v v' := by
    refine Prod.ext ?_ (Prod.ext (by simp) (Prod.ext (by simp) rfl))
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp
    · simp [Matrix.mulVec_add]; ring
  map_smul' c v := by
    refine Prod.ext ?_ (Prod.ext (by simp) (Prod.ext (by simp) rfl))
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Matrix.mulVec_smul]

/-- `K_M`, the tangent space of the kernel of `G̃_r → G`. -/
def kerK (M : Matrix (Fin r) (Fin m) ℂ) : Submodule ℂ (TanG (d₀ + r) d₁ m) :=
  LinearMap.range (kvec (d₀ := d₀) (d₁ := d₁) M)

/-- **Polynomials on `G`**: invariance under translation by `K_M`. -/
def InvarK (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) : Prop :=
  ∀ (g : GPtV (d₀ + r) d₁ Ls) (lam : Fin m → ℂˣ) (v : Fin m → ℂ),
    eval (coords (g + expGV Ls (kvec M v)) lam) P = eval (coords g lam) P

/-- Degree `≤ D` in the `r` trailing additive variables (the vector part of `G₂`). -/
def TrailDeg (D : ℕ) (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) : Prop :=
  ∀ s ∈ P.support, ∑ i : Fin r, s (.x (Fin.natAdd d₀ i)) ≤ D

/-- The projection to `ℂ^{d₀}` (the leading additive coordinates). -/
def prLead : TanG (d₀ + r) d₁ m →ₗ[ℂ] (Fin d₀ → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (Fin.castAdd r)).comp (prA (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m))

@[simp] theorem prLead_apply (p : TanG (d₀ + r) d₁ m) (i : Fin d₀) :
    prLead p i = p.1 (Fin.castAdd r i) := rfl

/-! ### The obstruction -/

/-- **Obstruction data** for `G = G̃_r / K_M`: a member `S` of the family of `G̃_r` (no
rationality),
the subgroup `grp = zcl (exp_{G̃}(T̃′))`, `T̃′ = S.tan`, Zariski closed with Lie algebra `T̃′`, and
`K_M ⊆ T̃′`. -/
structure ObstrDataV (d₀ r d₁ : ℕ) {m : ℕ} (Ls : Fin m → PeriodPair)
    (M : Matrix (Fin r) (Fin m) ℂ) where
  /-- the tangent data `(U, t, Γ)` on `G̃_r` -/
  S : SubgroupPreV (d₀ := d₀ + r) (d₁ := d₁) Ls (1 : Matrix (Fin m) (Fin m) ℂ)
  /-- the subgroup itself -/
  grp : Set (GPtV (d₀ + r) d₁ Ls)
  grp_eq : grp = zcl (expGV Ls '' (S.tan : Set (TanG (d₀ + r) d₁ m)))
  grp_sub : IsSubgroupG grp
  grp_closed : IsZClosed grp
  /-- `T̃′` is the Lie algebra of `grp` -/
  lie : ∀ v : TanG (d₀ + r) d₁ m, (∀ c : ℂ, expGV Ls (c • v) ∈ grp) ↔ v ∈ S.tan
  /-- `G̃′ ⊇ K_M`, i.e. `G̃′` is the preimage of a subgroup of `G` -/
  ker_le : kerK (d₀ := d₀) (d₁ := d₁) M ≤ S.tan

namespace ObstrDataV

variable {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ} (O : ObstrDataV d₀ r d₁ Ls M)

/-- `T̃′`. -/
def tan : Submodule ℂ (TanG (d₀ + r) d₁ m) := O.S.tan

/-- `G′ ≠ G`. -/
def Proper : Prop := O.tan ≠ ⊤

/-- `t₀ = dim pr_{G_a^{d₀}} T̃′`. -/
def t0 : ℕ := finrank ℂ (O.tan.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)))

/-- `t₂ = dim (T̃′ ∩ ker pr_{G_a^{d₀}} ∩ ker pr_{G_m})` (base, fibre and trailing additive
directions). -/
def t2 : ℕ := finrank ℂ ↥(O.tan ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
  LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m))))

theorem expGV_mem {u : TanG (d₀ + r) d₁ m} (hu : u ∈ O.tan) : expGV Ls u ∈ O.grp := by
  simpa using (O.lie u).mpr hu 1

end ObstrDataV

/-! ### The statement -/

/-- **The multiplicity estimate for `G = G_a^{d₀} × G_m^{d₁} × ((E₁ × ⋯ × E_m)^♮ pushed along M)`**
(Philippon 1986, Thm. 2.1, constants absorbed), in the model `G = G̃_r / K_M`.
`P` is a polynomial on `G` (`K_M`-invariant), homogeneous of degree `D₂` in each `E^♮` block, of
degree `≤ D₀` in the additive variables and `≤ D₂` in the `r` trailing ones (part of `G₂`),
`≤ D₁` in the toric ones, `P ∉ I_G̃`, and of formal order `> n T` along `W` at every point of
`Σ(n)`,
`n = dim G̃_r = d₀ + r + d₁ + 2m`. Then there is a proper obstruction `G′` with
`T^c · |F| · D₀^{t₀} D₁^{t₁} D₂^{t₂} ≤ C · D₀^{d₀} D₁^{d₁} D₂^{2m + r}` for every `F ⊆ S` of points
pairwise inequivalent modulo `G̃′`, `c = dim W − dim (W ∩ T̃′)`. -/
def MultEstVec : Prop :=
  ∀ (d₀ r d₁ m : ℕ) (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ), ∃ C : ℕ,
    ∀ (W : Submodule ℂ (TanG (d₀ + r) d₁ m)) (S : Finset (GPtV (d₀ + r) d₁ Ls))
      (P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ) (T D₀ D₁ D₂ : ℕ),
      (0 : GPtV (d₀ + r) d₁ Ls) ∈ S → IsHomV P (fun _ => D₂) →
      P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂) → TrailDeg (d₀ := d₀) D₂ P → InvarK Ls M P →
      P ∉ IG (d₀ := d₀ + r) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      1 ≤ T → 1 ≤ D₀ → 1 ≤ D₁ → 1 ≤ D₂ →
      (∀ σ ∈ sig S (d₀ + r + d₁ + 2 * m),
        OrdGt Ls (W.map (toLie : TanG (d₀ + r) d₁ m ≃ₗ[ℂ] LieV ℂ (d₀ + r) d₁ m).toLinearMap) P
          ((d₀ + r + d₁ + 2 * m) * T) σ) →
      ∃ O : ObstrDataV d₀ r d₁ Ls M, O.Proper ∧
        ∀ F : Finset (GPtV (d₀ + r) d₁ Ls), F ⊆ S →
          (∀ g ∈ F, ∀ g' ∈ F, g - g' ∈ O.grp → g = g') →
          T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O.t0 *
              D₁ ^ (d₁ - finrank ℚ O.S.U) * D₂ ^ O.t2 ≤
            C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r)

end

end LSG.MEV
