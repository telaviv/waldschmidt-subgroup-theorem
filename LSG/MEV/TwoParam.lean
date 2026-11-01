import Mathlib
import LSG.MEV.TwoBlock

/-!
# The two-parameter lemma and Roy's vanishing claim on `G̃`

* **`dv_words_of_ordGt`**: formal order `> N` at `p` (homogeneous `Q`) gives
  `(Dv_w^i Dv_{w'}^j Q)(p) = 0` for `w, w' ∈ W`, `i + j ≤ N` (canonical charts at `p`; Taylor
  formula along `ZG p` and `polarize`).
* `W2 y σ w w'`: the two-parameter formal point `(y + σ) + exp(z w) + exp(z' w')` over `R = ℂ⟦z⟧`
  (blocks from `two_block`); **`W2_isVFlow`**: a flow of `Dv w'` in `z'` with initial value
  `ZG (y + σ) w`.
* **`ordGt_phOp`** (Philippon's `δ^κ_σ` lowers the order by `κ`): if `P` (homogeneous) has formal
  order `> N` at `y + σ`, then `phOp σ w' c₁ c₂ κ P` has formal order `> T` at `y` for
  `w' ∈ W`, `κ + T ≤ N`.
* **`hAVO2`** (Roy's vanishing claim): with `p ⊇ L_{r+1}`, `V = Z(p)`, `GV` stabilizing `V`, the
  ideal `A = I_G̃ + (τ_v^c Q : Q ∈ gensR2 r, v ∈ V)` has formal order `> T` along `W` on
  `⋃ s ∈ S, s + GV`; its generators lie in `FLE (9 • D)`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk c2)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

local notation "Rz" => PowerSeries ℂ

/-! ### Words from the formal order -/

theorem dv_words_of_ordGt {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {N : ℕ} {p : GPtV d₀ d₁ Ls} (h : OrdGt Ls W Q N p)
    {w w' : LieV ℂ d₀ d₁ m} (hw : w ∈ W) (hw' : w' ∈ W) {i j : ℕ} (hij : i + j ≤ N) :
    eval (coords p 1) ((Dv Ls (chartsV p) w)^[i] ((Dv Ls (chartsV p) w')^[j] Q)) = 0 := by
  have hpow : ∀ w'' ∈ W, ∀ n ≤ N, eval (coords p 1) ((Dv Ls (chartsV p) w'')^[n] Q) = 0 := by
    intro w'' hw'' n hn
    have hlow := (ordGt_iff hQ W N p).mp h w'' hw'' n hn
    have ht := taylorV (ZG_isVFlow p w'') n Q
    rw [hlow, mul_zero, const_ZG] at ht
    exact ht.symm
  set A := (Dv Ls (chartsV p) w).toLinearMap
  set B := (Dv Ls (chartsV p) w').toLinearMap
  have hAB : Commute A B := LinearMap.ext fun Q => Dv_comm (chartsV p) w w' Q
  have hpw : ∀ (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
      (n : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ), (D.toLinearMap ^ n) Q = D^[n] Q := by
    intro D n Q; rw [Module.End.pow_apply]; rfl
  have := polarize A B hAB (aeval (coords p 1)).toLinearMap Q N (fun α β n hn => by
    have e : α • A + β • B = (Dv Ls (chartsV p) (α • w + β • w')).toLinearMap := by
      rw [Dv_add, Dv_smul, Dv_smul]; rfl
    rw [e]
    simp only [hpw, AlgHom.toLinearMap_apply, MvPolynomial.coe_aeval_eq_eval]
    exact hpow _ (W.add_mem (W.smul_mem α hw) (W.smul_mem β hw')) n hn) hij
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at this
  change (aeval (coords p 1)) (((Dv Ls (chartsV p) w).toLinearMap ^ i)
    (((Dv Ls (chartsV p) w').toLinearMap ^ j) Q)) = 0 at this
  rw [hpw, hpw] at this
  exact this

/-! ### Generic rescaling -/

/-- Rescaling of the `E^♮` blocks, any coefficient ring. -/
def sclG {A : Type*} [CommRing A] (u : Fin m → A) (Γ : Var d₀ d₁ m → A) : Var d₀ d₁ m → A
  | .e k c => u k * Γ (.e k c)
  | v => Γ v

theorem aeval_sclG {A : Type*} [CommRing A] [Algebra ℂ A] {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    {d : Fin m → ℕ} (hQ : IsHomV Q d) (u : Fin m → A) (Γ : Var d₀ d₁ m → A) :
    aeval (sclG u Γ) Q = (∏ k, u k ^ d k) * aeval Γ Q := by
  classical
  have : sclG u Γ = fun v => (∏ k, u k ^ wb blk (Blk.e k) v) * Γ v := by
    funext v
    cases v with
    | x i => simp [sclG, wb]
    | y j => simp [sclG, wb]
    | z j => simp [sclG, wb]
    | e k c =>
      simp only [sclG, wb, blk_e]
      rw [Finset.prod_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
  rw [this]; exact aeval_weightScale _ d u Γ Q hQ

/-! ### The two-parameter point -/

/-- The block flows of the two-parameter point. -/
noncomputable def W2e (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m) (k : Fin m) :
    Fin 5 → PowerSeries Rz :=
  (two_block (σ.2.2 k) (y.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 ((w'.2.2 k).1 / 2)
    (w'.2.2 k).2).choose

theorem W2e_spec (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m) (k : Fin m) :
    IsBFlow (R := Rz) (Ls k).g₂ (Ls k).g₃ (chartV ((y + σ).2.2 k)) ((w'.2.2 k).1 / 2)
        (w'.2.2 k).2 (W2e y σ w w' k) ∧
      (∀ l, PowerSeries.constantCoeff (W2e y σ w w' k l) = ZG Ls (y + σ) w (.e k l)) ∧
      ∀ A ∈ lawsAt (algebraMap ℂ (PowerSeries Rz) (Ls k).g₂)
        (algebraMap ℂ (PowerSeries Rz) (Ls k).g₃)
        (fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB (σ.2.2 k) ((w'.2.2 k).1 / 2) (w'.2.2 k).2 l))
        (fun l => PowerSeries.C (ZB (y.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 l)),
        A = A (bi (chartV ((y + σ).2.2 k))) • W2e y σ w w' k :=
  (two_block (σ.2.2 k) (y.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 ((w'.2.2 k).1 / 2)
    (w'.2.2 k).2).choose_spec

variable (Ls) in
/-- **The two-parameter formal point** `(y + σ) + exp(z w) + exp(z' w')`. -/
noncomputable def W2 (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m) :
    Var d₀ d₁ m → PowerSeries Rz
  | .x i => PowerSeries.C (ZG Ls (y + σ) w (.x i)) +
      PowerSeries.map (algebraMap ℂ Rz) (ExpV (g2L Ls) (g3L Ls) w' (.x i))
  | .y j => PowerSeries.C (ZG Ls (y + σ) w (.y j)) *
      PowerSeries.map (algebraMap ℂ Rz) (ExpV (g2L Ls) (g3L Ls) w' (.y j))
  | .z j => PowerSeries.C (ZG Ls (y + σ) w (.z j)) *
      PowerSeries.map (algebraMap ℂ Rz) (ExpV (g2L Ls) (g3L Ls) w' (.z j))
  | .e k l => W2e y σ w w' k l

theorem W2_const (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m) :
    (fun v => PowerSeries.constantCoeff (W2 Ls y σ w w' v)) = ZG Ls (y + σ) w := by
  funext v
  cases v with
  | x i => simp [W2, ExpV]
  | y j => simp [W2, ExpV, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
  | z j => simp [W2, ExpV, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
  | e k l => exact (W2e_spec y σ w w' k).2.1 l

theorem W2_isVFlow (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m) :
    IsVFlow (R := Rz) Ls (chartsV (y + σ)) w' (W2 Ls y σ w w') := by
  intro v
  cases v with
  | x i =>
    simp only [W2, ExpV, dvV, map_add, map_mul, aeval_C, PowerSeries.derivative_C, zero_add,
      LSG.ME.derivative_map, PowerSeries.map_C, PowerSeries.map_X]
    simp [PowerSeries.algebraMap_apply]
  | y j =>
    simp only [W2, ExpV, dvV, map_mul, aeval_C, aeval_X, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_C, mul_zero, add_zero, LSG.ME.derivative_map,
      derivative_rescale_exp, PowerSeries.map_C]
    simp only [PowerSeries.algebraMap_apply]
    ring
  | z j =>
    simp only [W2, ExpV, dvV, map_mul, map_neg, aeval_C, aeval_X, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_C, mul_zero, add_zero, LSG.ME.derivative_map,
      derivative_rescale_exp, PowerSeries.map_C]
    simp only [PowerSeries.algebraMap_apply]
    ring
  | e k l =>
    have h := (W2e_spec y σ w w' k).1.ode l
    simp only [W2]
    rw [h, dvV, ← AlgHom.coe_toRingHom, dvalB_map]
    simp only [AlgHom.coe_toRingHom, aeval_C]
    congr 1
    funext l'; simp [bvars, W2]

end LSG.MEV
