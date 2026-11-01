/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.PhOpTwo
import LSG.MEB.Deriv

/-!
# Homogenised chart derivations on vector-extension blocks (M2.5, β; the new design point of M2.md §M2.4a.6)

**Block level.** For a fibre index `t` of a block `b` with base chart `c = fc t`, the derivation `X_c² ∂_{(ζ, ω)}`
(`ζ` a base direction, `ω` the fibre direction) is polynomial and homogeneous of degree `+2` on `(X, T)`:
* `X_l ↦ X_c Σ_j ζ_j W_{cjl}(X)`;
* `T_{t′} ↦ Σ_j ζ_j R_{tjt′} + ω X_c² X_{fc t′}`, with the cubic
  `R_{tjt′} = T_t W_{cj(fc t′)} + X_{fc t′} WT_{tj} + Σ_a ∂_a plk_{tt′} · W_{cja}` (`VBlock.RT`).

Its **analytic meaning** (`VBlock.eval_bCoef`, from `θ_flow`, `T_flow`, the derivative of `T_plk` and Euler's identity
for `plk`): at `lift (z, w)`, the coefficient of every coordinate `a` is
`θ_c² · ∂_{(ζ,ω)} lift_a − θ_c (∂_ζ θ_c) · lift_a`, so on a block-homogeneous `P` of degree `d` it acts as
`θ_c² ∂_{(ζ,ω)} − d θ_c ∂_ζθ_c`. The second term is the Euler correction.

**Product.** For a fibre-index choice `ch : ∀ k, Fin (B k).nT` and `w ∈ Tan`,
`Dh ch w = Lc · (Σ ξ_i ∂_{x_i} + Σ η_j (y_j ∂_{y_j} − z_j ∂_{z_j})) + Σ_k Lo_k · (block-`k` derivation)`, with
`L_k = X_{k, fc (ch k)}²`, `Lc = Π_k L_k`, `Lo_k = Π_{k′ ≠ k} L_{k′}`. It raises every block degree by `2`
(`isHomV_Dh`), so `[Eul_k, Dh] = 2 Dh`.

* **`eval_Dh_liftV`**: `Dh P (liftV u) = Lc(liftV u) · ∂_w (P ∘ liftV)(u) − (Σ_k Lo_k(liftV u) s_k d_k) · P(liftV u)`,
  `s_k = θ_c(z_k) (∂_{ζ_k} θ)_c(z_k)`.
* `Dh_mem_FLE` (`D ↦ D + eTwos`), `Dh_eq_mkDerivation`.
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEBV

open LSG.MEB (Blk)

/-! ### Block level -/

namespace VBlock

variable (b : VBlock)

/-- The cubic `R_{t j t′} = T_t W_{cjl} + X_l WT_{tj} + Σ_a ∂_a plk_{tt′} W_{cja}` (`c = fc t`, `l = fc t′`). -/
noncomputable def RT (t : Fin b.nT) (j : Fin b.g) (t' : Fin b.nT) : MvPolynomial b.Idx ℂ :=
  X (Sum.inr t) * rename Sum.inl (b.base.W (b.fc t) j (b.fc t')) +
    X (Sum.inl (b.fc t')) * rename Sum.inl (b.WT t j) +
    ∑ a, rename Sum.inl (pderiv a (b.plk t t')) * rename Sum.inl (b.base.W (b.fc t) j a)

/-- **The block coefficients of `X_c² ∂_{(ζ, ω)}`**, `c = fc t`. -/
noncomputable def bCoef (t : Fin b.nT) (ζ : Fin b.g → ℂ) (ω : ℂ) : b.Idx → MvPolynomial b.Idx ℂ
  | Sum.inl l => X (Sum.inl (b.fc t)) * ∑ j, C (ζ j) * rename Sum.inl (b.base.W (b.fc t) j l)
  | Sum.inr t' => ∑ j, C (ζ j) * b.RT t j t' + C ω * X (Sum.inl (b.fc t)) ^ 2 * X (Sum.inl (b.fc t'))

theorem isHomogeneous_RT (t : Fin b.nT) (j : Fin b.g) (t' : Fin b.nT) : (b.RT t j t').IsHomogeneous 3 := by
  have hW : ∀ c j l, (rename Sum.inl (b.base.W c j l) : MvPolynomial b.Idx ℂ).IsHomogeneous 2 :=
    fun c j l => (b.base.W_hom c j l).rename_isHomogeneous
  have h1 := (isHomogeneous_X ℂ (Sum.inr t : b.Idx)).mul (hW (b.fc t) j (b.fc t'))
  have h2 := (isHomogeneous_X ℂ (Sum.inl (b.fc t') : b.Idx)).mul
    ((b.WT_hom t j).rename_isHomogeneous (f := Sum.inl))
  have h3 : (∑ a, rename Sum.inl (pderiv a (b.plk t t')) * rename Sum.inl (b.base.W (b.fc t) j a) :
      MvPolynomial b.Idx ℂ).IsHomogeneous 3 :=
    IsHomogeneous.sum _ _ _ fun a _ =>
      ((b.plk_hom t t').pderiv.rename_isHomogeneous (f := Sum.inl)).mul (hW _ _ _)
  exact (h1.add h2).add h3

theorem isHomogeneous_bCoef (t : Fin b.nT) (ζ : Fin b.g → ℂ) (ω : ℂ) (a : b.Idx) :
    (b.bCoef t ζ ω a).IsHomogeneous 3 := by
  cases a with
  | inl l =>
    have hs : (∑ j, C (ζ j) * rename Sum.inl (b.base.W (b.fc t) j l) : MvPolynomial b.Idx ℂ).IsHomogeneous 2 :=
      IsHomogeneous.sum _ _ _ fun j _ => (b.base.W_hom _ j l).rename_isHomogeneous.C_mul _
    exact (isHomogeneous_X ℂ (Sum.inl (b.fc t) : b.Idx)).mul hs
  | inr t' =>
    have hs : (∑ j, C (ζ j) * b.RT t j t').IsHomogeneous 3 :=
      IsHomogeneous.sum _ _ _ fun j _ => (b.isHomogeneous_RT t j t').C_mul _
    have hx := (((isHomogeneous_X ℂ (Sum.inl (b.fc t) : b.Idx)).pow 2).C_mul ω).mul
      (isHomogeneous_X ℂ (Sum.inl (b.fc t') : b.Idx))
    exact hs.add hx

/-- The derivative of the block lift along `r ↦ (z, w) + r (ζ, ω)`. -/
noncomputable def bD (z : Fin b.g → ℂ) (w : ℂ) (ζ : Fin b.g → ℂ) (ω : ℂ) : b.Idx → ℂ
  | Sum.inl l => fderiv ℂ b.base.θ z ζ l
  | Sum.inr t' => fderiv ℂ b.base.θ z ζ (b.fc t') * w - fderiv ℂ b.Φ z ζ t' + ω * b.base.θ z (b.fc t')

theorem hasDerivAt_θ_line (z ζ : Fin b.g → ℂ) (l : Fin b.N) :
    HasDerivAt (fun r : ℂ => b.base.θ (z + r • ζ) l) (fderiv ℂ b.base.θ z ζ l) 0 := by
  have hθ : HasFDerivAt b.base.θ (fderiv ℂ b.base.θ z) (z + (0 : ℂ) • ζ) := by
    simpa using (b.base.θ_analytic z).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun r : ℂ => z + r • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const ζ).const_add z
  have h := hasDerivAt_pi.mp (hθ.comp_hasDerivAt (0 : ℂ) hl) l
  simpa [Function.comp_def] using h

theorem hasDerivAt_Φ_line (z ζ : Fin b.g → ℂ) (t : Fin b.nT) :
    HasDerivAt (fun r : ℂ => b.Φ (z + r • ζ) t) (fderiv ℂ b.Φ z ζ t) 0 := by
  have hΦ : HasFDerivAt b.Φ (fderiv ℂ b.Φ z) (z + (0 : ℂ) • ζ) := by
    simpa using (b.Φ_analytic z).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun r : ℂ => z + r • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const ζ).const_add z
  have h := hasDerivAt_pi.mp (hΦ.comp_hasDerivAt (0 : ℂ) hl) t
  simpa [Function.comp_def] using h

theorem hasDerivAt_T_line (z ζ : Fin b.g → ℂ) (w : ℂ) (t : Fin b.nT) :
    HasDerivAt (fun r : ℂ => b.T (z + r • ζ) w t)
      (fderiv ℂ b.base.θ z ζ (b.fc t) * w - fderiv ℂ b.Φ z ζ t) 0 :=
  ((b.hasDerivAt_θ_line z ζ (b.fc t)).mul_const w).sub (b.hasDerivAt_Φ_line z ζ t)

/-- **The block lift along a line.** -/
theorem hasDerivAt_lift_line (z : Fin b.g → ℂ) (w : ℂ) (ζ : Fin b.g → ℂ) (ω : ℂ) (a : b.Idx) :
    HasDerivAt (fun r : ℂ => b.lift ((z, w) + r • (ζ, ω)) a) (b.bD z w ζ ω a) 0 := by
  cases a with
  | inl l => simpa [lift, liftOf, bD] using b.hasDerivAt_θ_line z ζ l
  | inr t' =>
    have h := ((b.hasDerivAt_θ_line z ζ (b.fc t')).mul
      (((hasDerivAt_id (0 : ℂ)).mul_const ω).const_add w)).sub (b.hasDerivAt_Φ_line z ζ t')
    simp only [id, zero_mul, add_zero, mul_one, zero_smul] at h
    convert h using 1
    · funext r; simp [lift, liftOf, fibOf]
    · simp [bD]; ring

/-- `fderiv` of a coordinate of `T` in `z`. -/
theorem fderiv_T (z : Fin b.g → ℂ) (w : ℂ) (t : Fin b.nT) (v : Fin b.g → ℂ) :
    fderiv ℂ (fun z' => b.T z' w t) z v = fderiv ℂ b.base.θ z v (b.fc t) * w - fderiv ℂ b.Φ z v t := by
  have hθ := (hasFDerivAt_pi'.mp (b.base.θ_analytic z).differentiableAt.hasFDerivAt) (b.fc t)
  have hΦ := (hasFDerivAt_pi'.mp (b.Φ_analytic z).differentiableAt.hasFDerivAt) t
  have h : HasFDerivAt (fun z' => b.base.θ z' (b.fc t) * w - b.Φ z' t) _ z := (hθ.mul_const w).sub hΦ
  rw [show (fun z' => b.T z' w t) = fun z' => b.base.θ z' (b.fc t) * w - b.Φ z' t from rfl, h.fderiv]
  simp [mul_comm]

theorem lift_comp_inl (p : (Fin b.g → ℂ) × ℂ) : b.lift p ∘ Sum.inl = b.base.θ p.1 := rfl

theorem eval_rename_inl (p : (Fin b.g → ℂ) × ℂ) (Q : MvPolynomial (Fin b.N) ℂ) :
    eval (b.lift p) (rename Sum.inl Q) = eval (b.base.θ p.1) Q := by
  rw [eval_rename, lift_comp_inl]

/-- **The value of `R`** (from `T_plk`, `θ_flow`, `T_flow` and Euler's identity for `plk`). -/
theorem eval_RT (t : Fin b.nT) (ht : b.fc t ∈ b.base.charts) (j : Fin b.g) (t' : Fin b.nT)
    (z : Fin b.g → ℂ) (w : ℂ) :
    eval (b.lift (z, w)) (b.RT t j t') = b.base.θ z (b.fc t) *
      (b.base.θ z (b.fc t) * (fderiv ℂ b.base.θ z (Pi.single j 1) (b.fc t') * w -
        fderiv ℂ b.Φ z (Pi.single j 1) t') - b.T z w t' * fderiv ℂ b.base.θ z (Pi.single j 1) (b.fc t)) := by
  set e : Fin b.g → ℂ := Pi.single j 1
  set c := b.fc t
  set l := b.fc t'
  set θz := b.base.θ z
  set dθ := fderiv ℂ b.base.θ z e
  set dT := dθ c * w - fderiv ℂ b.Φ z e t
  set dT' := dθ l * w - fderiv ℂ b.Φ z e t'
  set P := b.plk t t'
  -- the flows
  have hWl : θz c * dθ l - θz l * dθ c = eval θz (b.base.W c j l) := b.base.θ_flow c ht j l z
  have hWa : ∀ a, θz c * dθ a - θz a * dθ c = eval θz (b.base.W c j a) := fun a =>
    b.base.θ_flow c ht j a z
  have hWT : θz c * dT - b.T z w t * dθ c = eval θz (b.WT t j) := by
    have := b.T_flow t ht j z w
    rw [show (fun z' => fibOf b.base.θ b.fc b.Φ z' w t) = fun z' => b.T z' w t from rfl, b.fderiv_T] at this
    exact this
  -- Plücker, and its derivative along `e`
  have hPk : θz c * b.T z w t' - θz l * b.T z w t = eval θz P := b.T_plk t t' z w
  have hPl : ∑ a, eval θz (pderiv a P) * dθ a =
      dθ c * b.T z w t' + θz c * dT' - (dθ l * b.T z w t + θz l * dT) := by
    have hL : HasDerivAt (fun r : ℂ => b.base.θ (z + r • e) c * b.T (z + r • e) w t' -
        b.base.θ (z + r • e) l * b.T (z + r • e) w t)
        (dθ c * b.T z w t' + θz c * dT' - (dθ l * b.T z w t + θz l * dT)) 0 := by
      have h := ((b.hasDerivAt_θ_line z e c).mul (b.hasDerivAt_T_line z e w t')).sub
        ((b.hasDerivAt_θ_line z e l).mul (b.hasDerivAt_T_line z e w t))
      rw [zero_smul, add_zero] at h
      exact h
    have hR : HasDerivAt (fun r : ℂ => eval (b.base.θ (z + r • e)) P)
        (∑ a, eval (b.base.θ (z + (0 : ℂ) • e)) (pderiv a P) * dθ a) 0 :=
      LSG.MEB.hasDerivAt_eval (fun a => b.hasDerivAt_θ_line z e a) P
    have heq : (fun r : ℂ => b.base.θ (z + r • e) c * b.T (z + r • e) w t' -
        b.base.θ (z + r • e) l * b.T (z + r • e) w t) = fun r => eval (b.base.θ (z + r • e)) P :=
      funext fun r => b.T_plk t t' (z + r • e) w
    rw [heq] at hL
    have := hR.unique hL
    simpa using this
  -- Euler
  have hEu : ∑ a, θz a * eval θz (pderiv a P) = 2 * eval θz P := by
    have h := congrArg (eval θz) (b.plk_hom t t').sum_X_mul_pderiv
    simpa [map_sum, nsmul_eq_mul] using h
  -- the sum term
  have hS : ∑ a, eval θz (pderiv a P) * eval θz (b.base.W c j a) =
      θz c * ∑ a, eval θz (pderiv a P) * dθ a - dθ c * ∑ a, θz a * eval θz (pderiv a P) := by
    simp_rw [← hWa, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hval : eval (b.lift (z, w)) (b.RT t j t') = b.T z w t * eval θz (b.base.W c j l) +
      θz l * eval θz (b.WT t j) + ∑ a, eval θz (pderiv a P) * eval θz (b.base.W c j a) := by
    simp only [RT, map_add, map_mul, map_sum, eval_X, b.eval_rename_inl]
    rfl
  rw [hval]
  linear_combination (-b.T z w t) * hWl + (-θz l) * hWT + hS + θz c * hPl - dθ c * hEu +
    2 * dθ c * hPk

theorem fderiv_eq_sum_mul (z ζ : Fin b.g → ℂ) (x : Fin b.N) :
    fderiv ℂ b.base.θ z ζ x = ∑ j, ζ j * fderiv ℂ b.base.θ z (Pi.single j 1) x := by
  rw [LSG.MEB.fderiv_apply_eq_sum b.base.θ z ζ]
  simp [Finset.sum_apply]

theorem fderivΦ_eq_sum_mul (z ζ : Fin b.g → ℂ) (x : Fin b.nT) :
    fderiv ℂ b.Φ z ζ x = ∑ j, ζ j * fderiv ℂ b.Φ z (Pi.single j 1) x := by
  rw [LSG.MEB.fderiv_apply_eq_sum b.Φ z ζ]
  simp [Finset.sum_apply]

/-- **The analytic meaning of the block coefficients**: `θ_c² ∂ lift_a − θ_c ∂_ζθ_c · lift_a`. -/
theorem eval_bCoef (t : Fin b.nT) (ht : b.fc t ∈ b.base.charts) (z : Fin b.g → ℂ) (w : ℂ)
    (ζ : Fin b.g → ℂ) (ω : ℂ) (a : b.Idx) :
    eval (b.lift (z, w)) (b.bCoef t ζ ω a) = b.base.θ z (b.fc t) ^ 2 * b.bD z w ζ ω a -
      b.base.θ z (b.fc t) * fderiv ℂ b.base.θ z ζ (b.fc t) * b.lift (z, w) a := by
  set θc := b.base.θ z (b.fc t)
  have hX : ∀ x, b.lift (z, w) (Sum.inl x) = b.base.θ z x := fun _ => rfl
  cases a with
  | inl l =>
    have hsum : ∑ j, ζ j * eval (b.lift (z, w)) (rename Sum.inl (b.base.W (b.fc t) j l)) =
        θc * (∑ j, ζ j * fderiv ℂ b.base.θ z (Pi.single j 1) l) -
          b.base.θ z l * (∑ j, ζ j * fderiv ℂ b.base.θ z (Pi.single j 1) (b.fc t)) := by
      simp only [b.eval_rename_inl, ← b.base.θ_flow _ ht _ l z, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [bCoef, bD, map_mul, map_sum, eval_C, eval_X, hX]
    rw [hsum, b.fderiv_eq_sum_mul z ζ l, b.fderiv_eq_sum_mul z ζ (b.fc t)]
    ring
  | inr t' =>
    have hsum : ∑ j, ζ j * eval (b.lift (z, w)) (b.RT t j t') =
        θc ^ 2 * w * (∑ j, ζ j * fderiv ℂ b.base.θ z (Pi.single j 1) (b.fc t')) -
          θc ^ 2 * (∑ j, ζ j * fderiv ℂ b.Φ z (Pi.single j 1) t') -
            θc * b.T z w t' * (∑ j, ζ j * fderiv ℂ b.base.θ z (Pi.single j 1) (b.fc t)) := by
      simp only [b.eval_RT t ht _ t' z w, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hT : b.lift (z, w) (Sum.inr t') = b.T z w t' := rfl
    simp only [bCoef, bD, map_add, map_mul, map_sum, eval_C, eval_X, map_pow, hX]
    rw [hsum, hT, b.fderiv_eq_sum_mul z ζ (b.fc t'), b.fderivΦ_eq_sum_mul z ζ t',
      b.fderiv_eq_sum_mul z ζ (b.fc t)]
    simp only [T_apply]
    ring

end VBlock

/-! ### The product derivations -/

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- The squared chart form `X_{k, fc (ch k)}²` of block `k`. -/
noncomputable def Lk (ch : ∀ k, Fin (B k).nT) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  X (Var.e k (Sum.inl ((B k).fc (ch k)))) ^ 2

/-- The product of the squared chart forms. -/
noncomputable def Lc (ch : ∀ k, Fin (B k).nT) : MvPolynomial (Var d₀ d₁ B) ℂ := ∏ k, Lk ch k

/-- The product of the squared chart forms of the other blocks. -/
noncomputable def Lo (ch : ∀ k, Fin (B k).nT) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∏ k' ∈ Finset.univ.erase k, Lk ch k'

theorem Lk_mul_Lo (ch : ∀ k, Fin (B k).nT) (k : Fin m) :
    Lk (d₀ := d₀) (d₁ := d₁) ch k * Lo ch k = Lc ch :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ k)

/-- The coefficients of `Dh ch w`. -/
noncomputable def DhCoef (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ
  | .x i => C (w.1 i) * Lc ch
  | .y j => C (w.2.1 j) * X (.y j) * Lc ch
  | .z j => -(C (w.2.1 j) * X (.z j)) * Lc ch
  | .e k a => Lo ch k * rename (Var.e k) ((B k).bCoef (ch k) (w.2.2.1 k) (w.2.2.2 k) a)

/-- **The homogenised chart derivation** `Dh ch w` (block derivations `X_c² ∂`). -/
noncomputable def Dh (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  ∑ v, DhCoef ch w v • pderiv v

theorem Dh_apply (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    Dh ch w P = ∑ v, DhCoef ch w v * pderiv v P := by
  rw [Dh, show ⇑(∑ v, DhCoef ch w v • (pderiv v : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ)
      (MvPolynomial (Var d₀ d₁ B) ℂ))) = ∑ v, ⇑(DhCoef ch w v • (pderiv v : Derivation ℂ
      (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))) from
    map_sum Derivation.coeFnAddMonoidHom _ _]
  simp [Finset.sum_apply, smul_eq_mul]

theorem Dh_eq_mkDerivation (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) :
    Dh ch w = mkDerivation ℂ (DhCoef ch w) := by
  refine derivation_ext fun v => ?_
  rw [Dh_apply, mkDerivation_X, Finset.sum_eq_single v]
  · simp
  · intro v' _ hv'; simp [pderiv_X, Pi.single_apply, Ne.symm hv']
  · intro h; exact absurd (Finset.mem_univ v) h

/-! ### Homogeneity -/

/-- Renaming a homogeneous block polynomial into block `k`. -/
theorem isWH_rename_e {M : Type*} [AddCommMonoid M] (ω : Var d₀ d₁ B → M) (k : Fin m) (δ : M)
    (hω : ∀ a, ω (.e k a) = δ) {p : MvPolynomial (B k).Idx ℂ} {n : ℕ} (hp : p.IsHomogeneous n) :
    IsWeightedHomogeneous ω (rename (Var.e k) p) (n • δ) := by
  have h1 := LSG.MEB.isWH_map_weight hp (multiplesHom M δ)
  have hrb : ∀ q : MvPolynomial (B k).Idx ℂ,
      rename (Var.e (d₀ := d₀) (d₁ := d₁) k) q = bind₁ (fun a => X (Var.e k a)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p a hp => simp [hp]
  rw [hrb]
  refine LSG.MEB.isWeightedHomogeneous_bind₁ (w := Function.const _ δ) (fun a => ?_) (by simpa using h1)
  simpa [hω] using isWeightedHomogeneous_X ℂ ω (Var.e k a : Var d₀ d₁ B)

theorem isWH_Lk (ch : ∀ k, Fin (B k).nT) (k k' : Fin m) :
    IsWeightedHomogeneous (wk k) (Lk (d₀ := d₀) (d₁ := d₁) ch k') (if k' = k then 2 else 0) := by
  have h := (isWeightedHomogeneous_X ℂ (wk k)
    (Var.e k' (Sum.inl ((B k').fc (ch k'))) : Var d₀ d₁ B)).pow 2
  by_cases hk : k' = k
  · simpa [Lk, wk, hk] using h
  · simpa [Lk, wk, hk] using h

theorem isWH_Lc (ch : ∀ k, Fin (B k).nT) (k : Fin m) :
    IsWeightedHomogeneous (wk k) (Lc (d₀ := d₀) (d₁ := d₁) ch) 2 := by
  have h := IsWeightedHomogeneous.prod (w := wk k) Finset.univ
    (fun k' => Lk (d₀ := d₀) (d₁ := d₁) ch k') (fun k' => if k' = k then 2 else 0) fun k' _ =>
      isWH_Lk ch k k'
  simpa [Lc] using h

theorem isWH_Lo (ch : ∀ k, Fin (B k).nT) (k k₀ : Fin m) :
    IsWeightedHomogeneous (wk k) (Lo (d₀ := d₀) (d₁ := d₁) ch k₀) (if k₀ = k then 0 else 2) := by
  have h := IsWeightedHomogeneous.prod (w := wk k) (Finset.univ.erase k₀)
    (fun k' => Lk (d₀ := d₀) (d₁ := d₁) ch k') (fun k' => if k' = k then 2 else 0) fun k' _ =>
      isWH_Lk ch k k'
  have e : (∑ i ∈ Finset.univ.erase k₀, if i = k then 2 else 0) = if k₀ = k then 0 else 2 := by
    rw [Finset.sum_ite_eq']
    by_cases hk : k₀ = k
    · simp [hk]
    · simp [Finset.mem_erase, Ne.symm hk, hk]
  rw [e] at h
  exact h

theorem isWH_DhCoef (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) (k : Fin m) (v : Var d₀ d₁ B) :
    IsWeightedHomogeneous (wk k) (DhCoef ch w v) (2 + wk k v) := by
  cases v with
  | x i => simpa [DhCoef, wk] using (isWH_Lc ch k).C_mul (w.1 i)
  | y j =>
    have := ((isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d₀ d₁ B)).mul (isWH_Lc ch k)).C_mul
      (w.2.1 j)
    simpa [DhCoef, wk, mul_assoc] using this
  | z j =>
    have := (((isWeightedHomogeneous_X ℂ (wk k) (Var.z j : Var d₀ d₁ B)).mul (isWH_Lc ch k)).C_mul
      (w.2.1 j)).neg
    simpa [DhCoef, wk, mul_assoc] using this
  | e k₀ a =>
    have hR := isWH_rename_e (d₀ := d₀) (d₁ := d₁) (wk k) k₀ (if k₀ = k then 1 else 0)
      (fun _ => rfl) ((B k₀).isHomogeneous_bCoef (ch k₀) (w.2.2.1 k₀) (w.2.2.2 k₀) a)
    have := (isWH_Lo ch k k₀).mul hR
    have e : (if k₀ = k then 0 else 2) + 3 • (if k₀ = k then 1 else 0) =
        2 + wk k (Var.e k₀ a : Var d₀ d₁ B) := by
      simp only [wk]; split_ifs <;> simp
    rw [e] at this
    exact this

/-- `Dh` raises every block degree by two. -/
theorem isHomV_Dh (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hP : IsHomV P d) : IsHomV (Dh ch w P) (fun k => d k + 2) := by
  intro k
  rw [Dh_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun v _ => ?_
  by_cases h : wk k v ≤ d k
  · have hp : IsWeightedHomogeneous (wk k) (pderiv v P) (d k - wk k v) :=
      (hP k).pderiv (Nat.sub_add_cancel h)
    convert (isWH_DhCoef ch w k v).mul hp using 1
    dsimp only
    omega
  · have hv : pderiv v P = 0 := by
      refine pderiv_eq_zero_of_notMem_vars fun hv => ?_
      obtain ⟨s, hs, hsv⟩ := (mem_vars_iff_mem_support v).mp hv
      have hw := hP k (mem_support_iff.mp hs)
      have hle : s v * wk k v ≤ Finsupp.weight (wk k) s := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact Finset.single_le_sum (f := fun x => s x • wk k x) (fun _ _ => Nat.zero_le _) hsv
      have : 1 ≤ s v := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hsv)
      have : wk k v ≤ s v * wk k v := Nat.le_mul_of_pos_left _ this
      omega
    simp [hv, isWeightedHomogeneous_zero]

/-! ### Block degrees -/

/-- The degree shift of `Dh`: `2` on the blocks, `0` otherwise. -/
def eTwos : Blk m → ℕ
  | .e _ => 2
  | _ => 0

theorem isWH_wB_Lk (ch : ∀ k, Fin (B k).nT) (k : Fin m) :
    IsWeightedHomogeneous wB (Lk (d₀ := d₀) (d₁ := d₁) ch k) (2 • Pi.single (Blk.e k) 1) := by
  simpa [Lk, wB, blk] using (isWeightedHomogeneous_X ℂ wB
    (Var.e k (Sum.inl ((B k).fc (ch k))) : Var d₀ d₁ B)).pow 2

theorem DhCoef_mem_FLE (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    DhCoef ch w v ∈ StrongSix.M2.FLE ℂ blk (Pi.single (blk v) 1 + eTwos) := by
  have hLc : IsWeightedHomogeneous wB (Lc (d₀ := d₀) (d₁ := d₁) ch)
      (∑ k, 2 • (Pi.single (Blk.e k) 1 : Blk m → ℕ)) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => isWH_wB_Lk ch k
  have hLcle : (∑ k, 2 • (Pi.single (Blk.e k) 1 : Blk m → ℕ)) = eTwos := by
    funext b
    rw [← Finset.smul_sum, Pi.smul_apply, LSG.MEB.sum_single_e]
    cases b <;> simp [eTwos]
  rw [hLcle] at hLc
  cases v with
  | x i =>
    refine mem_FLE_of_isWH (hLc.C_mul (w.1 i)) fun b => ?_
    simp
  | y j =>
    have h := (((isWeightedHomogeneous_X ℂ wB (Var.y j : Var d₀ d₁ B)).mul hLc).C_mul (w.2.1 j))
    refine mem_FLE_of_isWH (by simpa [DhCoef, mul_assoc] using h) (le_of_eq ?_)
    simp [wB]
  | z j =>
    have h := (((isWeightedHomogeneous_X ℂ wB (Var.z j : Var d₀ d₁ B)).mul hLc).C_mul
      (w.2.1 j)).neg
    refine mem_FLE_of_isWH (by simpa [DhCoef, mul_assoc] using h) (le_of_eq ?_)
    simp [wB]
  | e k a =>
    have hLo : IsWeightedHomogeneous wB (Lo (d₀ := d₀) (d₁ := d₁) ch k)
        (∑ k' ∈ Finset.univ.erase k, 2 • (Pi.single (Blk.e k') 1 : Blk m → ℕ)) :=
      IsWeightedHomogeneous.prod _ _ _ fun k' _ => isWH_wB_Lk ch k'
    have hR := isWH_rename_e (d₀ := d₀) (d₁ := d₁) wB k (Pi.single (Blk.e k) 1) (fun _ => rfl)
      ((B k).isHomogeneous_bCoef (ch k) (w.2.2.1 k) (w.2.2.2 k) a)
    refine mem_FLE_of_isWH (hLo.mul hR) (le_of_eq ?_)
    funext b
    rw [← Finset.smul_sum]
    simp only [Pi.add_apply, Pi.smul_apply, LSG.MEB.sum_single_e, smul_eq_mul, blk]
    cases b with
    | e k₀ =>
      by_cases h : k₀ = k
      · subst h; simp [Pi.single_apply, eTwos]
      · simp [Pi.single_apply, eTwos, h]
    | x => simp [Pi.single_apply, eTwos]
    | yz => simp [Pi.single_apply, eTwos]

/-- **Block degrees under `Dh`**: block degrees go up by at most two, the others do not go up. -/
theorem Dh_mem_FLE (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    Dh ch w P ∈ StrongSix.M2.FLE ℂ blk (D + eTwos) := by
  rw [Dh_eq_mkDerivation]
  exact LSG.MEB.mkDerivation_mem_FLE' (DhCoef_mem_FLE ch w) hP

/-! ### The analytic meaning -/

/-- The derivative of the coordinates of `liftV` along `r ↦ u + r w`. -/
noncomputable def liftV' (u w : Tan d₀ d₁ B) : Var d₀ d₁ B → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * Complex.exp (u.2.1 j)
  | .z j => -w.2.1 j * Complex.exp (-u.2.1 j)
  | .e k a => (B k).bD (u.2.2.1 k) (u.2.2.2 k) (w.2.2.1 k) (w.2.2.2 k) a

theorem hasDerivAt_liftV (u w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    HasDerivAt (fun r : ℂ => liftV (u + r • w) v) (liftV' u w v) 0 := by
  cases v with
  | x i =>
    simpa [liftV, liftV'] using ((hasDerivAt_id (0 : ℂ)).mul_const (w.1 i)).const_add (u.1 i)
  | y j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (u.2.1 j)).cexp
    simpa [liftV, liftV', mul_comm] using h
  | z j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (u.2.1 j)).neg.cexp
    simpa [liftV, liftV', mul_comm] using h
  | e k a => exact (B k).hasDerivAt_lift_line (u.2.2.1 k) (u.2.2.2 k) (w.2.2.1 k) (w.2.2.2 k) a

theorem eval_Lk_liftV (ch : ∀ k, Fin (B k).nT) (u : Tan d₀ d₁ B) (k : Fin m) :
    eval (liftV u) (Lk ch k) = (B k).base.θ (u.2.2.1 k) ((B k).fc (ch k)) ^ 2 := by
  simp [Lk, liftV, Tan.blkV]

/-- The Euler-correction scalar `s_k = θ_c(z_k) · (∂_{ζ_k} θ)_c(z_k)`, `c = fc (ch k)`. -/
noncomputable def sk (ch : ∀ k, Fin (B k).nT) (u w : Tan d₀ d₁ B) (k : Fin m) : ℂ :=
  (B k).base.θ (u.2.2.1 k) ((B k).fc (ch k)) *
    fderiv ℂ (B k).base.θ (u.2.2.1 k) (w.2.2.1 k) ((B k).fc (ch k))

theorem eval_rename_e_liftV (u : Tan d₀ d₁ B) (k : Fin m) (p : MvPolynomial (B k).Idx ℂ) :
    eval (liftV u) (rename (Var.e k) p) = eval ((B k).lift (u.blkV k)) p := by
  rw [eval_rename]; rfl

/-- The coefficients of `Dh` at a lifted point (`eval_bCoef`). -/
theorem eval_DhCoef_liftV (ch : ∀ k, Fin (B k).nT)
    (hch : ∀ k, (B k).fc (ch k) ∈ (B k).base.charts) (u w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    eval (liftV u) (DhCoef ch w v) = eval (liftV u) (Lc ch) * liftV' u w v -
      ∑ k, eval (liftV u) (Lo ch k) * sk ch u w k * (wk k v : ℂ) * liftV u v := by
  cases v with
  | x i => simp [DhCoef, liftV', wk, mul_comm]
  | y j => simp [DhCoef, liftV', wk, liftV]; ring
  | z j => simp [DhCoef, liftV', wk, liftV]; ring
  | e k₀ a =>
    have hLc : eval (liftV u) (Lc ch) =
        (B k₀).base.θ (u.2.2.1 k₀) ((B k₀).fc (ch k₀)) ^ 2 * eval (liftV u) (Lo ch k₀) := by
      rw [← Lk_mul_Lo ch k₀, map_mul, eval_Lk_liftV]
    have hRHS : ∑ k, eval (liftV u) (Lo ch k) * sk ch u w k *
        ((wk k (Var.e k₀ a : Var d₀ d₁ B) : ℕ) : ℂ) * liftV u (.e k₀ a) =
        eval (liftV u) (Lo ch k₀) * sk ch u w k₀ * liftV u (.e k₀ a) := by
      rw [Finset.sum_eq_single k₀]
      · simp [wk]
      · intro k _ hk; simp [wk, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ k₀) h
    rw [hRHS]
    simp only [DhCoef, map_mul, eval_rename_e_liftV]
    rw [show u.blkV k₀ = (u.2.2.1 k₀, u.2.2.2 k₀) from rfl,
      (B k₀).eval_bCoef (ch k₀) (hch k₀), hLc]
    simp only [liftV', sk, liftV, Tan.blkV]
    ring

/-- **The analytic meaning of `Dh`** for multihomogeneous `P`. -/
theorem eval_Dh_liftV (ch : ∀ k, Fin (B k).nT) (hch : ∀ k, (B k).fc (ch k) ∈ (B k).base.charts)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) (u w : Tan d₀ d₁ B) :
    eval (liftV u) (Dh ch w P) =
      eval (liftV u) (Lc ch) * deriv (fun r : ℂ => eval (liftV (u + r • w)) P) 0 -
        (∑ k, eval (liftV u) (Lo ch k) * sk ch u w k * d k) * eval (liftV u) P := by
  have hd := (LSG.MEB.hasDerivAt_eval (hasDerivAt_liftV u w) P).deriv
  simp only [zero_smul, add_zero] at hd
  rw [hd, Dh_apply, map_sum]
  simp only [map_mul, eval_DhCoef_liftV ch hch, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have he := congrArg (eval (liftV u)) ((hP k).sum_weight_X_mul_pderiv)
    simp only [map_sum, map_nsmul, nsmul_eq_mul, map_mul, eval_X, smul_eq_mul, map_natCast] at he
    set c := eval (liftV u) (Lo ch k) * sk ch u w k
    calc ∑ v, c * (wk k v : ℂ) * liftV u v * eval (liftV u) (pderiv v P)
        = c * ∑ v, (wk k v : ℂ) * (liftV u v * eval (liftV u) (pderiv v P)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
      _ = c * (d k) * eval (liftV u) P := by rw [he]; ring

end LSG.MEBV
