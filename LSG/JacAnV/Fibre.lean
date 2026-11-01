/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.KTheta

/-!
# M2.2 (N2): the fibre coordinates of `A_σ̄^♮` as derivative lifts of `θ_N`

With `K` the Lemma-K♮ constants (`ThetaData.kK`) and `ℓ(z) = ⅓ (K₀₀ z₀ + K₁₀ z₁)` (`ellK`):

* **`fibT k z w = θ_k(z) (w + ℓ(z)) − ⅓ ∂₀θ_k(z)`** (entire, linear in `w`, `∂_w T_k = θ_k`);
* **`fibT_add`** (cocycle): `T_k(z + ω, w + η̄(ω)) = facN(ω, z) · T_k(z, w)` for `ω ∈ latt`, with the *same*
  multiplier `facN` as `θ_N` and the fibre period `η̄(ω) = ⅓ L_ω(e₀) − ℓ(ω)` (`etaB`), additive (`etaB_add`);
* **`fibT_plucker`**: `θ_c T_l − θ_l T_c = −⅓ W^{(c)}_0(θ)_l` for any chart `c` with a projective flow `W^{(c)}`
  (`fibT_plucker0`, `fibT_plucker4` for the charts 0 and 4);
* **`fibT_flow`** (fibre flow, from Lemma K♮): `θ_c ∂_jT_c − T_c ∂_jθ_c = ⅓ Q_{c,j0}(θ)` for `c ∈ {0, 4, 8}`;
* `zetaB` (`ζ̄ = ⅓ ∂₀θ₀/θ₀ − ℓ`): `T₀ = θ₀ (w − ζ̄)` (`fibT_zero_eq`), `∂_jζ̄ = −℘_{j0}` (`pd_zetaB`),
  `ζ̄(z + ω) = ζ̄(z) + η̄(ω)` (`zetaB_add`). The fibre period is therefore the period of the Kleinian `ζ̄`
  (input for N5).
-/

noncomputable section

open Filter

namespace LSG.JacAn

open LSG.JacAnV

variable {A : A1Facts} {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad A hp hx} (D : ThetaData G)

/-- `ℓ(z) = ⅓ (K₀₀ z₀ + K₁₀ z₁)`. -/
def ThetaData.ellK : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (1 / 3 : ℂ) • (D.kK 0 0 • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0 +
    D.kK 1 0 • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1)

lemma ThetaData.ellK_apply (z : Fin 2 → ℂ) : D.ellK z = 1 / 3 * (D.kK 0 0 * z 0 + D.kK 1 0 * z 1) := by
  simp [ThetaData.ellK]; ring

lemma ThetaData.ellK_single (j : Fin 2) : D.ellK (Pi.single j 1) = 1 / 3 * D.kK j 0 := by
  rw [D.ellK_apply]; fin_cases j <;> simp

/-- **The fibre coordinates** `T_k(z, w) = θ_k(z) (w + ℓ(z)) − ⅓ ∂₀θ_k(z)`. -/
def ThetaData.fibT (k : Fin 9) (z : Fin 2 → ℂ) (w : ℂ) : ℂ :=
  D.thetaN z k * (w + D.ellK z) - 1 / 3 * pd 0 (cmpV D.thetaN k) z

/-- **The fibre period** `η̄(ω) = ⅓ L_ω(e₀) − ℓ(ω)`. It is the field `η` of the instance `aBlockV`; not to be
confused with `LSG.AuxAV.etaB` (`LSG/AuxFunAV/Mono.lean`), the blockwise `η` of a `VBlock` family. -/
def ThetaData.etaB (ω : Fin 2 → ℂ) : ℂ := 1 / 3 * D.Lf ω (Pi.single 0 1) - D.ellK ω

lemma ThetaData.fibT_w (k : Fin 9) (z : Fin 2 → ℂ) (w s : ℂ) :
    D.fibT k z (w + s) = D.fibT k z w + s * D.thetaN z k := by
  unfold ThetaData.fibT; ring

lemma ThetaData.ent_fibT (k : Fin 9) (w : ℂ) : Ent (fun z => D.fibT k z w) := by
  have hk := ent_cmp D.analyticAt_thetaN k
  have e : (fun z => D.fibT k z w) =
      fun z => cmpV D.thetaN k z * (w + D.ellK z) - 1 / 3 * pd 0 (cmpV D.thetaN k) z := rfl
  rw [e]
  exact (hk.mul ((ent_const w).add (ent_lin D.ellK))).sub ((hk.pd 0).const_mul _)

/-- The shift of `θ_N` in affine-exponential form. -/
lemma ThetaData.thetaN_add_aff {ω : Fin 2 → ℂ} (hω : ω ∈ latt) (z : Fin 2 → ℂ) :
    D.thetaN (z + ω) = (Complex.exp (-D.lamN ω) * D.fac ω 0 * Complex.exp (D.Lf ω z)) • D.thetaN z := by
  rw [D.thetaN_add (isPer_of_mem_latt hω), D.facN_aff hω]

/-- **The cocycle**: `T_k(z + ω, w + η̄(ω)) = facN(ω, z) · T_k(z, w)`. -/
theorem ThetaData.fibT_add {ω : Fin 2 → ℂ} (hω : ω ∈ latt) (k : Fin 9) (z : Fin 2 → ℂ) (w : ℂ) :
    D.fibT k (z + ω) (w + D.etaB ω) = D.facN ω z * D.fibT k z w := by
  have h0 : ∀ z, cmpV D.thetaN k (z + ω) =
      Complex.exp (-D.lamN ω) * D.fac ω 0 * Complex.exp (D.Lf ω z) * cmpV D.thetaN k z := fun z => by
    simp only [cmpV, D.thetaN_add_aff hω z, Pi.smul_apply, smul_eq_mul]
  have hd := KHyp.pd_shift (ent_cmp D.analyticAt_thetaN k) h0 0 z
  have h0z := h0 z
  simp only [cmpV] at h0z hd
  unfold ThetaData.fibT ThetaData.etaB
  rw [hd, map_add, h0z, D.facN_aff hω]
  ring

/-- `η̄` is additive on `latt`. -/
theorem ThetaData.etaB_add {ω ω' : Fin 2 → ℂ} (hω : ω ∈ latt) (hω' : ω' ∈ latt) :
    D.etaB (ω + ω') = D.etaB ω + D.etaB ω' := by
  unfold ThetaData.etaB
  rw [D.Lf_add (isPer_of_mem_latt hω) (isPer_of_mem_latt hω'), map_add, add_apply]
  ring

/-- `η̄` as an additive map on `latt`. -/
def ThetaData.etaHom : latt →+ ℂ where
  toFun ω := D.etaB ω
  map_zero' := by simp [ThetaData.etaB, D.Lf_zero]
  map_add' ω ω' := D.etaB_add ω.2 ω'.2

/-- **The Plücker relations**: `θ_c T_l − θ_l T_c = −⅓ W_0(θ)_l` for a chart-`c` projective flow `W`. -/
theorem ThetaData.fibT_plucker {W : Fin 2 → P9 → P9} {c : Fin 9} {z : Fin 2 → ℂ}
    (hPF : PFAt W 1 c D.thetaN z) (l : Fin 9) (w : ℂ) :
    D.thetaN z c * D.fibT l z w - D.thetaN z l * D.fibT c z w = -(1 / 3) * W 0 (D.thetaN z) l := by
  have e := hPF (Pi.single 0 1) l
  have hd := (D.analyticAt_thetaN z).differentiableAt
  unfold ThetaData.fibT
  rw [pd_cmp hd, pd_cmp hd]
  simp only [Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, zero_mul,
    add_zero, one_mul] at e
  linear_combination (-1 / 3 : ℂ) * e

theorem ThetaData.fibT_plucker0 (z : Fin 2 → ℂ) (l : Fin 9) (w : ℂ) :
    D.thetaN z 0 * D.fibT l z w - D.thetaN z l * D.fibT 0 z w = -(1 / 3) * flowW 0 (D.thetaN z) l :=
  D.fibT_plucker (D.thetaN_PF0 z) l w

theorem ThetaData.fibT_plucker4 (z : Fin 2 → ℂ) (l : Fin 9) (w : ℂ) :
    D.thetaN z 4 * D.fibT l z w - D.thetaN z l * D.fibT 4 z w = -(1 / 3) * A.W4 0 (D.thetaN z) l :=
  D.fibT_plucker (D.thetaN_PF4 z) l w

/-- `∂_j T_k`. -/
lemma ThetaData.pd_fibT (k : Fin 9) (j : Fin 2) (z : Fin 2 → ℂ) (w : ℂ) :
    pd j (fun z => D.fibT k z w) z = pd j (cmpV D.thetaN k) z * (w + D.ellK z) +
      D.thetaN z k * (1 / 3 * D.kK j 0) - 1 / 3 * pd j (pd 0 (cmpV D.thetaN k)) z := by
  have hk := ent_cmp D.analyticAt_thetaN k
  have e : (fun z => D.fibT k z w) =
      fun z => cmpV D.thetaN k z * (w + D.ellK z) - 1 / 3 * pd 0 (cmpV D.thetaN k) z := rfl
  rw [e, pd_sub ((hk.mul ((ent_const w).add (ent_lin D.ellK))) z).differentiableAt
      (((hk.pd 0).const_mul _) z).differentiableAt,
    pd_mul (hk.diff z) (((ent_const w).add (ent_lin D.ellK)).diff z),
    pd_add ((ent_const w).diff z) ((ent_lin D.ellK).diff z), pd_const, pd_lin, D.ellK_single,
    pd_const_mul _ ((hk.pd 0).diff z)]
  simp only [cmpV]
  ring

/-- **The fibre flow** (Lemma K♮): `θ_c ∂_jT_c − T_c ∂_jθ_c = ⅓ Q_{c,j0}(θ)` for `c ∈ {0, 4, 8}`. -/
theorem ThetaData.fibT_flow {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (j : Fin 2) (z : Fin 2 → ℂ) (w : ℂ) :
    D.thetaN z c * pd j (fun z => D.fibT c z w) z - D.fibT c z w * pd j (cmpV D.thetaN c) z =
      1 / 3 * kQ c j 0 (D.thetaN z) := by
  have hK := D.kK_spec hc j 0 z
  rw [D.pd_fibT]
  unfold kG at hK
  unfold ThetaData.fibT
  linear_combination (-1 / 3 : ℂ) * hK

/-! ### The Kleinian `ζ̄` -/

/-- `ζ̄ = ⅓ ∂₀θ₀ / θ₀ − ℓ` (meromorphic; used where `θ₀ ≠ 0`). -/
def ThetaData.zetaB (z : Fin 2 → ℂ) : ℂ := 1 / 3 * pd 0 (cmpV D.thetaN 0) z / D.thetaN z 0 - D.ellK z

theorem ThetaData.fibT_zero_eq {z : Fin 2 → ℂ} (hz : D.thetaN z 0 ≠ 0) (w : ℂ) :
    D.fibT 0 z w = D.thetaN z 0 * (w - D.zetaB z) := by
  unfold ThetaData.fibT ThetaData.zetaB
  field_simp
  ring

/-- **`ζ̄(z + ω) = ζ̄(z) + η̄(ω)`.** -/
theorem ThetaData.zetaB_add {ω : Fin 2 → ℂ} (hω : ω ∈ latt) {z : Fin 2 → ℂ} (hz : D.thetaN z 0 ≠ 0) :
    D.zetaB (z + ω) = D.zetaB z + D.etaB ω := by
  have hf : D.facN ω z ≠ 0 := by
    rw [ThetaData.facN]
    exact mul_ne_zero (Complex.exp_ne_zero _) (D.fac_ne_zero (isPer_of_mem_latt hω) z)
  have hzω : D.thetaN (z + ω) 0 ≠ 0 := by
    rw [D.thetaN_add (isPer_of_mem_latt hω)]; simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hf hz
  have e := D.fibT_add hω 0 z 0
  rw [D.fibT_zero_eq hzω, D.fibT_zero_eq hz, D.thetaN_add (isPer_of_mem_latt hω)] at e
  simp only [Pi.smul_apply, smul_eq_mul] at e
  have : D.facN ω z * D.thetaN z 0 * (D.etaB ω - D.zetaB (z + ω) + D.zetaB z) = 0 := by
    linear_combination e
  have h2 := (mul_eq_zero.mp this).resolve_left (mul_ne_zero hf hz)
  linear_combination -h2

lemma ThetaData.zetaB_differentiableAt {z : Fin 2 → ℂ} (hz : D.thetaN z 0 ≠ 0) :
    DifferentiableAt ℂ D.zetaB z := by
  have h0 := ent_cmp D.analyticAt_thetaN 0
  exact ((((h0.pd 0).const_mul (1 / 3 : ℂ)) z).div (h0 z) hz).differentiableAt.sub
    (ent_lin D.ellK z).differentiableAt

/-- **`∂_j ζ̄ = −℘_{j0} = −θ_{m(j,0)}/θ₀`.** -/
theorem ThetaData.pd_zetaB (j : Fin 2) {z : Fin 2 → ℂ} (hz : D.thetaN z 0 ≠ 0) :
    pd j D.zetaB z = -(D.thetaN z (mIdx j 0) / D.thetaN z 0) := by
  have h0 := ent_cmp D.analyticAt_thetaN 0
  have hev : (fun z => D.fibT 0 z 0) =ᶠ[nhds z] fun z => -(cmpV D.thetaN 0 z * D.zetaB z) := by
    filter_upwards [(h0 z).continuousAt.eventually_ne hz] with y hy
    rw [D.fibT_zero_eq hy]; simp [cmpV]
  have hT : pd j (fun z => D.fibT 0 z 0) z = pd j (fun z => -(cmpV D.thetaN 0 z * D.zetaB z)) z := by
    unfold pd; rw [hev.fderiv_eq]
  have hneg : pd j (fun z => -(cmpV D.thetaN 0 z * D.zetaB z)) z =
      -(pd j (cmpV D.thetaN 0) z * D.zetaB z + D.thetaN z 0 * pd j D.zetaB z) := by
    have := pd_const_mul (f := fun z => cmpV D.thetaN 0 z * D.zetaB z) (-1 : ℂ)
      ((h0.diff z).mul (D.zetaB_differentiableAt hz)) j
    simp only [neg_one_mul] at this
    rw [this, pd_mul (f := cmpV D.thetaN 0) (h0.diff z) (D.zetaB_differentiableAt hz)]
  have hfl := D.fibT_flow (c := 0) (Or.inl rfl) j z 0
  rw [hT, hneg, D.fibT_zero_eq hz] at hfl
  simp only [kQ, ↓reduceIte] at hfl
  have h1 : D.thetaN z 0 * (D.thetaN z 0 * pd j D.zetaB z + D.thetaN z (mIdx j 0)) = 0 := by
    linear_combination -hfl
  have h2 := (mul_eq_zero.mp h1).resolve_left hz
  rw [neg_div', eq_div_iff hz]
  linear_combination h2

end LSG.JacAn
