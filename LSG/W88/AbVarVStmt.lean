/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunAV.PropG
import LSG.AuxFunAV.LemmaUMain
import LSG.MEBV.Stmt
import LSG.W88.StatementVec
import LSG.W88.StatementAbVar

/-!
# M2.6.6: W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`: the statement

Generic over a family of vector blocks `B : Fin m → VBlock` with analytic packages `An : ∀ k, VBlockAn (B k)` and an
onto `M : ℂ^m → ℂ^r` (in M2: `B = fun _ => aBlockV`, `d₀ = 0`, `r = 1`, `M = bᵀ`). Tangent space
`TanAV d₀ d₁ r B ∋ (a, b, z, s)`, `s = M w` (`LSG/AuxFunAV/Mono.lean`); `G = Σ_k g_k`, `d₂ = G + r`.

* **`LamAV d₀ d₁ An M`**: `a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`, `z_k ∈ lat_k`, `s − M η(z) ∈ ℚ̄^r` (`sPart`). These are the
  logarithms of algebraic points whose base parts are the origin (torsion after the finite-index passage
  `lat ↔ per`); M2's `Λ` (toric logarithms plus `Q″`-periods) lies in it.
* `PerAV d₀ d₁ An M` (`LSG/AuxFunAV/Mono.lean`): `0 × 2πiℤ^{d₁} × {(λ, M η(λ)) : λ ∈ ∏ lat_k}`.
* `AlgTanAV`, `RationalOverQbarAV`.
* **`SubgroupDataAV d₀ d₁ B M`**: `T_U × (B̃ + Γ)`: `U ⊂ ℚ^{d₁}`, `t` rational for the base periods (the abelian image
  `B ⊂ ∏ A_k`), `Γ ⊂ ℂ^{d₀} × ℂ^r` `ℚ̄`-rational. `tan = Γ + U^⊥ + perTanA M t`, `perTanA M t = (id × M)(perTanId t)`.
  W88's projection codimensions `δ₀ = d₀ − dim pr₀ Γ`, `δ₁ = dim U`, `δ = codim`, `δ₂ = δ − δ₀ − δ₁` (as
  `Vec.SubgroupDataV`).
* **`Theorem41AbVarVPer An M`**: W88 Thm 4.1 under (NR) and toric injectivity (`TorInjAV`), for `Y ⊆ LamAV`.
  A W88 consequence only for algebraic `M`; the §5d form `HyperplaneKappaAbVarV` additionally needs
  `PerTanFib B M` to be one (REVIEW_STATEMENT_M2 m2).
* §5d: **`FibOK`** (a member whose abelian part is nonzero contains the fibre `0 × 0 × 0 × ℂ^r`), **`PerTanFib B M`**
  (the block-family property behind it: `t ≠ 0 ⇒ 0 × ℂ^r ⊂ perTanA M t`; for `A_σ̄^♮`, anti-affineness N6 of the
  sub-extensions), `fibOK_of_perTanFib`, `gmLsgAV` (whose `sub` records `FibOK`, as the M2.8 bridge's `hsub` needs),
  **`HyperplaneKappaAbVarV`**.
-/

open Module LSG.AuxAV

noncomputable section

namespace LSG.W88

open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock perBase perTanId)
open LSG.W88.Vec (RatPair AlgPair AlgMat)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock}

/-! ### Points, periods, rationality -/

theorem sPart_add (M : Matrix (Fin r) (Fin m) ℂ) {p q : TanAV d₀ d₁ r B}
    (hp : ∀ k, p.2.2.1 k ∈ (B k).base.per) (hq : ∀ k, q.2.2.1 k ∈ (B k).base.per) :
    sPart M (p + q) = sPart M p + sPart M q := by
  have he : etaB B (p.2.2.1 + q.2.2.1) = etaB B p.2.2.1 + etaB B q.2.2.1 :=
    funext fun k => (B k).η_add (hp k) (hq k)
  unfold sPart
  change p.2.2.2 + q.2.2.2 - M.mulVec (etaB B (p.2.2.1 + q.2.2.1)) = _
  rw [he, Matrix.mulVec_add]; abel

theorem sPart_neg (M : Matrix (Fin r) (Fin m) ℂ) {p : TanAV d₀ d₁ r B}
    (hp : ∀ k, p.2.2.1 k ∈ (B k).base.per) : sPart M (-p) = -sPart M p := by
  have he : etaB B (-p.2.2.1) = -etaB B p.2.2.1 := funext fun k => (B k).η_neg (hp k)
  unfold sPart
  change -p.2.2.2 - M.mulVec (etaB B (-p.2.2.1)) = _
  rw [he, Matrix.mulVec_neg]; abel

variable (d₀ d₁) in
/-- **The logarithms of algebraic points with base parts in `lat`.** -/
def LamAV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : AddSubgroup (TanAV d₀ d₁ r B) where
  carrier := {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧
    (∀ k, p.2.2.1 k ∈ (An k).an.lat) ∧ AlgVec (sPart M p)}
  add_mem' {p q} hp hq := by
    refine ⟨fun i => (hp.1 i).add (hq.1 i), fun i => ?_,
      fun k => (An k).an.lat.add_mem (hp.2.2.1 k) (hq.2.2.1 k), fun i => ?_⟩
    · change IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
      rw [Complex.exp_add]; exact (hp.2.1 i).mul (hq.2.1 i)
    · rw [sPart_add M (fun k => (An k).an.lat_le (hp.2.2.1 k)) (fun k => (An k).an.lat_le (hq.2.2.1 k))]
      exact (hp.2.2.2 i).add (hq.2.2.2 i)
  zero_mem' := by
    refine ⟨fun _ => isAlgebraic_zero, fun _ => by simpa using isAlgebraic_one,
      fun k => (An k).an.lat.zero_mem, fun i => ?_⟩
    have he : etaB B (0 : ∀ k, Fin (B k).g → ℂ) = 0 := funext fun k => (B k).η_zero
    have : sPart M (0 : TanAV d₀ d₁ r B) = 0 := by
      unfold sPart; change (0 : Fin r → ℂ) - M.mulVec (etaB B 0) = 0
      rw [he, Matrix.mulVec_zero, sub_zero]
    rw [this]; exact isAlgebraic_zero
  neg_mem' {p} hp := by
    refine ⟨fun i => (hp.1 i).neg, fun i => ?_, fun k => (An k).an.lat.neg_mem (hp.2.2.1 k), fun i => ?_⟩
    · change IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
      rw [Complex.exp_neg]; exact (hp.2.1 i).inv
    · rw [sPart_neg M (fun k => (An k).an.lat_le (hp.2.2.1 k))]
      exact (hp.2.2.2 i).neg

/-- The `ℚ̄`-structure of `T_G`. -/
def AlgTanAV (p : TanAV d₀ d₁ r B) : Prop :=
  AlgVec p.1 ∧ AlgVec p.2.1 ∧ (∀ k j, IsAlgebraic ℚ (p.2.2.1 k j)) ∧ AlgVec p.2.2.2

/-- `ℚ̄`-rational subspaces of `T_G`. -/
def RationalOverQbarAV (W : Submodule ℂ (TanAV d₀ d₁ r B)) : Prop :=
  W = Submodule.span ℂ {w | w ∈ W ∧ AlgTanAV w}

/-! ### The subgroup family -/

/-- `(a, s) ↦ (a, 0, 0, s)`: the vector group `G_a^{d₀} × (fibre of G₂)`. -/
def vecInclA : ((Fin d₀ → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun x := (x.1, 0, 0, x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- `b ↦ (0, b, 0, 0)`: the torus. -/
def torInclA : (Fin d₁ → ℂ) →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun b := (0, b, 0, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- `(z, s) ↦ (0, 0, z, s)`: the factor `G₂`. -/
def g2InclA : ((∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ)) →ₗ[ℂ] TanAV d₀ d₁ r B where
  toFun x := (0, 0, x.1, x.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

variable (d₀ d₁ r B) in
/-- The fibre `0 × 0 × 0 × ℂ^r` of `G₂ → ∏ A_k`. -/
def fibreAV : Submodule ℂ (TanAV d₀ d₁ r B) :=
  LinearMap.range ((vecInclA : _ →ₗ[ℂ] TanAV d₀ d₁ r B) ∘ₗ LinearMap.inr ℂ (Fin d₀ → ℂ) (Fin r → ℂ))

variable (B) in
/-- **`T_{B̃}`**: the image of `perTanId t` in `T(G₂) = ∏ ℂ^{g_k} × ℂ^r` (push-out along `M`). -/
def perTanA (M : Matrix (Fin r) (Fin m) ℂ) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    Submodule ℂ ((∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ)) :=
  (perTanId B t).map (LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M))

variable (d₀ d₁ B) in
/-- **Data of a connected algebraic subgroup** `G′ = T_U × (B̃ + Γ)` of `G`. -/
structure SubgroupDataAV (M : Matrix (Fin r) (Fin m) ℂ) where
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d₁ → ℚ)
  /-- the base tangent space of the abelian image `B ⊂ ∏ A_k` -/
  t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)
  /-- the vector part, inside `G_a^{d₀} × (fibre of G₂)` -/
  gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))
  gam_rat : RatPair gam
  t_rat : IsRatSub (perBase B) t

namespace SubgroupDataAV

variable {M : Matrix (Fin r) (Fin m) ℂ} (H : SubgroupDataAV d₀ d₁ B M)

/-- `T_{G′} = Γ + U^⊥ + T_{B̃}`. -/
def tan : Submodule ℂ (TanAV d₀ d₁ r B) :=
  H.gam.map vecInclA ⊔ (torusLie H.U).map torInclA ⊔ (perTanA B M H.t).map g2InclA

/-- `δ₀ = d₀ − dim π₀(G′)`. -/
def δ0 : ℕ := d₀ - finrank ℂ (H.gam.map (LinearMap.fst ℂ _ _))
/-- `δ₁ = dim U`. -/
def δ1 : ℕ := finrank ℚ H.U
/-- `δ = codim G′`. -/
def δ : ℕ := (d₀ + d₁ + ∑ k, (B k).g + r) - finrank ℂ H.tan
/-- `δ₂ = δ − δ₀ − δ₁`. -/
def δ2 : ℕ := H.δ - H.δ0 - H.δ1

/-- `G′ ≠ G`. -/
def Proper : Prop := H.δ ≠ 0

end SubgroupDataAV

/-! ### The statement -/

/-- **The W88 conclusion** for `(V, W, Y)`. -/
def Concl41AV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) (V W : Submodule ℂ (TanAV d₀ d₁ r B))
    (Y : AddSubgroup (TanAV d₀ d₁ r B)) : Prop :=
  ∃ H : SubgroupDataAV d₀ d₁ B M, H.Proper ∧
    finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) < H.δ ∧
    (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerAV d₀ d₁ An M)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
        ((d₀ + d₁ + ∑ k, (B k).g + r : ℕ) - finrank ℂ V : ℤ) ≤
      ((H.δ : ℤ) - (finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ)) *
        ((d₁ + 2 * (∑ k, (B k).g + r) : ℕ) - rk (Y ⊓ PerAV d₀ d₁ An M) : ℤ))

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`, under (NR) and toric
injectivity** (the family `B`, its packages and `M` fixed; `d₀, d₁` free), with the `B_k`-components (base parts) of
the logarithms in the period lattice (`LamAV`; the `G_a`, `G_m` and fibre components are arbitrary algebraic).

This is a W88 consequence only when `M` is algebraic: for non-algebraic `M` the coordinates `s = M w` are not
`ℚ̄`-rational and the Prop is not a W88 instance (REVIEW_STATEMENT_M2 m2). It is proved (`theorem41AbVarVPer`,
`AbVarVSec7.lean`) for onto algebraic `M` with `r ≤ 1`. -/
def Theorem41AbVarVPer (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : Prop :=
  ∀ (d₀ d₁ : ℕ) (V W : Submodule ℂ (TanAV d₀ d₁ r B)) (Y : AddSubgroup (TanAV d₀ d₁ r B)),
    finrank ℂ V < d₀ + d₁ + ∑ k, (B k).g + r → W ≤ V → RationalOverQbarAV W →
    Y.FG → (∀ y ∈ Y, y ∈ V ∧ y ∈ LamAV d₀ d₁ An M) → TorInjAV M V →
    -- (NR)
    d₁ + 2 * d₀ + rk (Y ⊓ PerAV d₀ d₁ An M) ≤ 2 * finrank ℂ V →
    Concl41AV An M V W Y

variable (B) in
/-- **Taylor packages over every number field.** -/
def TayAllV :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (k : Fin m), VBlockTay (B k) ι

/-! ### The §5d form -/

/-- **A member whose abelian part is nonzero contains the fibre.** -/
def FibOK {M : Matrix (Fin r) (Fin m) ℂ} (H : SubgroupDataAV d₀ d₁ B M) : Prop :=
  H.t ≠ ⊥ → fibreAV d₀ d₁ r B ≤ H.tan

variable (B) in
/-- **The fibre property of the block family**: the push-out of `B^♮` contains the fibre for every nonzero rational
`t` (for `A_σ̄^♮`: anti-affineness of the sub-extensions, M2.md N6). -/
def PerTanFib (M : Matrix (Fin r) (Fin m) ℂ) : Prop :=
  ∀ t : Submodule ℂ (∀ k, Fin (B k).g → ℂ), IsRatSub (perBase B) t → t ≠ ⊥ →
    ∀ x : Fin r → ℂ, ((0 : ∀ k, Fin (B k).g → ℂ), x) ∈ perTanA B M t

theorem fibOK_of_perTanFib {M : Matrix (Fin r) (Fin m) ℂ} (hF : PerTanFib B M) (H : SubgroupDataAV d₀ d₁ B M) :
    FibOK H := by
  intro ht v hv
  obtain ⟨x, rfl⟩ := hv
  refine Submodule.mem_sup_right ⟨(0, x), hF H.t H.t_rat ht x, ?_⟩
  rfl

/-- **The group model of `G_a^{d₀} × G_m^{d₁} × (∏ B_k^♮ pushed out along M)`**; `sub` records `FibOK`. -/
def gmLsgAV (d₀ d₁ : ℕ) (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) :
    MStarCopy.GroupModel (TanAV d₀ d₁ r B) where
  d₁ := d₁
  d₂ := ∑ k, (B k).g + r
  alg := AlgTanAV
  lam := ((LamAV d₀ d₁ An M : AddSubgroup (TanAV d₀ d₁ r B)) : Set (TanAV d₀ d₁ r B))
  per := Submodule.span ℚ ((PerAV d₀ d₁ An M : AddSubgroup (TanAV d₀ d₁ r B)) : Set (TanAV d₀ d₁ r B))
  sub := fun S => ∃ H : SubgroupDataAV d₀ d₁ B M, S = H.tan ∧ FibOK H

/-- **The W88 §5d statement for the vector-extension class** (toric-injective hyperplanes, `TorInjAV`), the family
`B`, its packages and `M` fixed, with the `B_k`-components (base parts) of the logarithms in the period lattice
(`LamAV`; the `G_a`, `G_m` and fibre components are arbitrary algebraic). Proved for the `A^♮` instance
(`hyperplaneKappaAbVarV_aBlockV`).

This is a W88 consequence only when `M` is algebraic and the block family satisfies `PerTanFib B M`: otherwise
`gmLsgAV.sub` (which records `FibOK`) can miss genuine subgroups, e.g. for `b` with an `F`-linear relation
(REVIEW_STATEMENT_M2 m2). The proved instance has both (`AlgMat`, `perTanFib_aBlockV_of_adapted`). -/
def HyperplaneKappaAbVarV (An : ∀ k, VBlockAn (B k)) (M : Matrix (Fin r) (Fin m) ℂ) : Prop :=
  ∀ d₀ d₁ : ℕ, HyperplaneKappaOnLsg (gmLsgAV d₀ d₁ An M) (TorInjAV M)

end LSG.W88
