import Mathlib
import LSG.MEV.SubgroupLiftV

/-!
# Zariski tangent vectors integrate: `TZ H ⊆ lieAlg H` (gap G3, core)

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)`:
* `TZ Ls H = {w | ∀ Q ∈ vanish H, (D̂_w Q)(FV 0) = 0}` (`FV 0`: the `V`-normalised identity
  `(0, 1, 1, (0 : 1 : 0 : 0 : 0)_k)`), a `ℂ`-subspace.
* `scl r`: block rescaling of polynomials; `vanish H` is stable (`scl_mem_vanish`);
  **`eval_Dh_scale`**: `(D̂_w Q)(r · y) = (∏ r_k²) (D̂_w (scl r Q))(y)`.
* **`first_order`**: for `w ∈ TZ H`, `p ∈ H̃` with `V ≠ 0` at `exp p`, and `Q ∈ vanish H`:
  `(D̂_w Q)(FV p) = 0`. Proof: translate by `g = exp p` with a good law (`τ_g Q ∈ vanish H`), compare
  the translate of the curve `FV(c w)` with the rescaled curve `S(c) · FV(p + c w)`; the
  `S′(0)`-terms are block-Euler terms, which vanish on cone points of `H`.
* **`Dh_mem_vanish`**: `w ∈ TZ H` ⇒ `D̂_w (vanish H) ⊆ vanish H` (at `2`-torsion fibres `D̂_w`
  vanishes identically, `DV_eq_zero_of_V`).
* **`TZ_subset_lieAlg`** (all derivatives of `Q(FV(c w))` vanish at `0`) and `lieAlg_subset_TZ`;
  **`mem_TZ_iff`**: `TZ H = lieAlg H`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.AuxV (ellN)
open LSG.Aux (ellW)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Block rescaling of polynomials -/

/-- The scaling factor of a variable. -/
def rr (r : Fin m → ℂ) : Var d₀ d₁ m → ℂ
  | .e k _ => r k
  | _ => 1

theorem scaleV_eq_rr (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (v : Var d₀ d₁ m) :
    scaleV r y v = rr r v * y v := by
  cases v <;> simp [rr]

/-- Block rescaling of polynomials. -/
def scl (r : Fin m → ℂ) : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ :=
  aeval fun v => C (rr r v) * X v

theorem eval_scl (r : Fin m → ℂ) (y : Var d₀ d₁ m → ℂ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval y (scl r Q) = eval (scaleV r y) Q := by
  rw [scl, eval_aeval']
  have : (fun k => eval y (C (rr r k) * X k)) = scaleV r y := by funext v; simp [scaleV_eq_rr]
  rw [this]

theorem scl_scl_inv {r : Fin m → ℂ} (hr : ∀ k, r k ≠ 0) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    scl r (scl (fun k => (r k)⁻¹) Q) = Q := by
  have : (scl (d₀ := d₀) (d₁ := d₁) r).comp (scl fun k => (r k)⁻¹) =
      AlgHom.id ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, scl, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      algebraMap_eq]
    rw [← mul_assoc, ← C_mul]
    cases v <;> simp [rr, hr]
  exact congrArg (fun φ => φ Q) this

theorem scaleV_coords (r : Fin m → ℂˣ) (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) :
    scaleV (fun k => (r k : ℂ)) (coords g lam) = coords g (fun k => r k * lam k) := by
  funext v; cases v <;> simp [coords, mul_assoc]

theorem scl_mem_vanish {E : Set (GPtV d₀ d₁ Ls)} (r : Fin m → ℂˣ)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ vanish E) :
    scl (fun k => (r k : ℂ)) Q ∈ vanish E :=
  mem_vanish.mpr fun g hg lam => by
    rw [eval_scl, scaleV_coords]; exact mem_vanish.mp hQ g hg _

/-- Directional derivatives of a rescaled polynomial. -/
theorem dir_scl (r : Fin m → ℂ) (y u : Var d₀ d₁ m → ℂ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    ∑ v, eval y (pderiv v (scl r Q)) * u v =
      ∑ v, eval (scaleV r y) (pderiv v Q) * scaleV r u v := by
  classical
  have h1 := LSG.ME.hasDerivAt_eval (Y := fun t : ℂ => y + t • u) (c₀ := 0)
    (fun v => by simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (u v)).const_add (y v))
    (scl r Q)
  have h2 := LSG.ME.hasDerivAt_eval (Y := fun t : ℂ => scaleV r y + t • scaleV r u) (c₀ := 0)
    (fun v => by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (scaleV r u v)).const_add (scaleV r y v)) Q
  have e : (fun t : ℂ => eval (y + t • u) (scl r Q)) =
      fun t => eval (scaleV r y + t • scaleV r u) Q := by
    funext t
    have : scaleV r (y + t • u) = scaleV r y + t • scaleV r u := by
      funext v; simp only [scaleV_eq_rr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [eval_scl, this]
  rw [e] at h1
  simpa using h1.unique h2

/-- **`D̂_w` and block rescaling.** -/
theorem eval_Dh_scale (r : Fin m → ℂ) (w : TanG d₀ d₁ m) (y : Var d₀ d₁ m → ℂ)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (scaleV r y) (Dh Ls w Q) = (∏ k, r k ^ 2) * eval y (Dh Ls w (scl r Q)) := by
  rw [eval_Dh, eval_Dh, dir_scl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [DV_scale]; ring

/-! ### Block-Euler terms -/

/-- The block-`k` part of a cone vector. -/
def blockPart (k : Fin m) (y : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ
  | .e k' c => if k' = k then y (.e k' c) else 0
  | _ => 0

/-- **Block-Euler terms vanish** on cone representatives of points of `E`. -/
theorem euler_eq_zero {E : Set (GPtV d₀ d₁ Ls)} {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : Q ∈ vanish E) {g : GPtV d₀ d₁ Ls} (hg : g ∈ E) (ν : Fin m → ℂˣ) (k : Fin m) :
    ∑ v, eval (coords g ν) (pderiv v Q) * blockPart k (coords g ν) v = 0 := by
  classical
  set y := coords g ν
  have h1 := LSG.ME.hasDerivAt_eval (Y := fun t : ℂ => y + t • blockPart k y) (c₀ := 0)
    (fun v => by simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (blockPart k y v)).const_add (y v))
    Q
  have hev : (fun t : ℂ => eval (y + t • blockPart k y) Q) =ᶠ[𝓝 0] fun _ => 0 := by
    have : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 :=
      (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)
    filter_upwards [this] with t ht
    let r : Fin m → ℂˣ := fun k' => if k' = k then Units.mk0 _ ht else 1
    have : y + t • blockPart k y = coords g fun k' => r k' * ν k' := by
      rw [← scaleV_coords]
      funext v
      cases v with
      | x i => simp [blockPart, y]
      | y j => simp [blockPart, y]
      | z j => simp [blockPart, y]
      | e k' c => by_cases hk : k' = k <;> simp [blockPart, r, hk, y] <;> ring
    rw [this]; exact mem_vanish.mp hQ g hg _
  have h0 := (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev
  simpa using h1.unique h0

/-! ### The Zariski tangent space at the identity -/

theorem goodV_zero : GoodV Ls (0 : TanG d₀ d₁ m) := fun k => by
  have := congrFun (LSG.AuxV.ellN_at_zero (Ls k) 0) 1
  rw [LSG.AuxV.ellN_one] at this
  simp [this, ptO]

variable (Ls) in
/-- **The Zariski tangent space at the identity**, in Lie-algebra coordinates. -/
def TZ (H : Set (GPtV d₀ d₁ Ls)) : Submodule ℂ (TanG d₀ d₁ m) where
  carrier := {w | ∀ Q ∈ vanish H, eval (FV Ls 0) (Dh Ls w Q) = 0}
  add_mem' {w w'} hw hw' Q hQ := by rw [Dh_add, hw Q hQ, hw' Q hQ, add_zero]
  zero_mem' Q _ := by
    have := Dh_smul (Ls := Ls) 0 0 Q (FV Ls 0); simpa using this
  smul_mem' c w hw Q hQ := by rw [Dh_smul, hw Q hQ, mul_zero]

/-- A point with `V = 0` in some block. -/
theorem eval_Dh_eq_zero_of_V {g : GPtV d₀ d₁ Ls} (ν : Fin m → ℂˣ) {k : Fin m}
    (hV : repV (g.2.2 k) 1 = 0) (w : TanG d₀ d₁ m) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (coords g ν) (Dh Ls w Q) = 0 := by
  rw [eval_Dh]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [DV_eq_zero_of_V Ls (y := coords g ν) (k := k) (p := g.2.2 k) (u := ν k)
    (by funext c; simp [coords]) hV, mul_zero]

/-- `GoodV p` iff `V ≠ 0` in every block of `exp p`. -/
theorem goodV_iff (p : TanG d₀ d₁ m) : GoodV Ls p ↔ ∀ k, repV ((expGV Ls p).2.2 k) 1 ≠ 0 := by
  refine forall_congr' fun k => ?_
  obtain ⟨c, hc0, hc⟩ := LSG.AuxV.ellN_eq_smul_expN (Ls k) (p.2.2.1 k) (p.2.2.2 k)
  have h1 := congrFun hc 1
  rw [LSG.AuxV.ellN_one] at h1
  rw [show (expGV Ls p).2.2 k = expV (Ls k) (p.2.2.1 k, p.2.2.2 k) from rfl, repV_expV, h1]
  simp [hc0]

/-! ### The first-order step -/

section First

variable {H : Set (GPtV d₀ d₁ Ls)}

theorem transl_mem_vanish (hH : IsSubgroupG H) {g : GPtV d₀ d₁ Ls} (hg : g ∈ H) (cc : Fin m → LC)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ vanish H) : τ Ls g cc Q ∈ vanish H :=
  mem_vanish.mpr fun h hh lam => by
    obtain ⟨ν, hν⟩ := eval_transl g h cc lam
    rw [hν]
    exact eval_coordsZ_eq_zero (fun lam' => mem_vanish.mp hQ _ (hH.add_mem _ hh _ hg) lam') ν

variable (hH : IsSubgroupG H)

/-- The translated vector. -/
def trV (g : GPtV d₀ d₁ Ls) (cc : Fin m → LC) (x : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ :=
  fun v => eval x (translVar Ls g cc v)

theorem eval_τ (g : GPtV d₀ d₁ Ls) (cc : Fin m → LC) (x : Var d₀ d₁ m → ℂ)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) : eval x (τ Ls g cc Q) = eval (trV g cc x) Q := by
  rw [τ, eval_aeval']; rfl

theorem prop_of_V {N F R : Fin 5 → ℂ} {a b : ℂ} (hN : N = a • R) (hF : F = b • R) (hb : b ≠ 0)
    (hF1 : F 1 = 1) : N = N 1 • F := by
  have hN' : N = (a / b) • F := by rw [hN, hF, smul_smul, div_mul_cancel₀ _ hb]
  have h1 : N 1 = a / b := by rw [hN']; simp [hF1]
  rw [h1]; exact hN'

/-- **The translated curve is a rescaled curve.** -/
theorem trV_FV {c : ℂ} {p₀ w : TanG d₀ d₁ m} (h0 : GoodV Ls (c • w))
    (h1 : GoodV Ls (p₀ + c • w)) (cc : Fin m → LC) :
    trV (expGV Ls p₀) cc (FV Ls (c • w)) =
      scaleV (fun k => trV (expGV Ls p₀) cc (FV Ls (c • w)) (.e k 1)) (FV Ls (p₀ + c • w)) := by
  obtain ⟨ν, hν⟩ := FV_eq_coords h0
  obtain ⟨ν', hν'⟩ := FV_eq_coords h1
  funext v
  cases v with
  | x i => simp [trV, translVar, FV, liftV, expGV, add_comm]
  | y j =>
    simp [trV, translVar, FV, liftV, expGV, GPtV.ym, LSG.ME.expU, Complex.exp_add]
  | z j =>
    simp [trV, translVar, FV, liftV, expGV, GPtV.ym, LSG.ME.expU, Complex.exp_add,
      Complex.exp_neg, mul_comm]
  | e k i =>
    have hblk : ∀ x : Var d₀ d₁ m → ℂ, (fun l => trV (expGV Ls p₀) cc x (.e k l)) =
        nlawc (cc k) (Ls k).g₂ (Ls k).g₃ (fun l => x (.e k l)) (repV ((expGV Ls p₀).2.2 k)) := by
      intro x; funext l; simp [trV, translVar, eval_lawPolyV]
    obtain ⟨μ, hμ⟩ := nlawc_repV (cc k) ((expGV Ls (c • w)).2.2 k) ((expGV Ls p₀).2.2 k)
    have hN : (fun l => trV (expGV Ls p₀) cc (FV Ls (c • w)) (.e k l)) =
        ((ν k : ℂ) ^ 3 * μ) • repV ((expGV Ls (p₀ + c • w)).2.2 k) := by
      rw [hblk, hν]
      have : (fun l => coords (expGV Ls (c • w)) ν (.e k l)) =
          (ν k : ℂ) • repV ((expGV Ls (c • w)).2.2 k) := by funext l; simp [coords]
      rw [this, nlawc_smul_left, hμ, smul_smul, expGV_add, Prod.snd_add, Prod.snd_add,
        Pi.add_apply, add_comm ((expGV Ls (c • w)).2.2 k)]
    have hF : (fun l => FV Ls (p₀ + c • w) (.e k l)) =
        (ν' k : ℂ) • repV ((expGV Ls (p₀ + c • w)).2.2 k) := by
      rw [hν']; funext l; simp [coords]
    have := prop_of_V hN hF (ν' k).ne_zero (FV_V h1 k)
    exact congrFun this i

variable (hc : IsZClosed H)
include hH hc

omit hc in
/-- **The first-order step.** -/
theorem first_order {w : TanG d₀ d₁ m} (hw : w ∈ TZ Ls H) {p : TanG d₀ d₁ m}
    (hpH : expGV Ls p ∈ H) (hp : GoodV Ls p) {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : Q ∈ vanish H) : eval (FV Ls p) (Dh Ls w Q) = 0 := by
  classical
  set g := expGV Ls p
  obtain ⟨cc, hcc⟩ := exists_good (0 : GPtV d₀ d₁ Ls) g
  -- the scaling factors
  set S : ℂ → Fin m → ℂ := fun c k => trV g cc (FV Ls (c • w)) (.e k 1)
  have hS0 : ∀ k, S 0 k ≠ 0 := by
    intro k hk
    have hgood := hcc k
    obtain ⟨ν, hν⟩ := FV_eq_coords (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
    have e := trV_FV (p₀ := p) (c := 0) (w := w)
      (by simpa using goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) (by simpa using hp) cc
    have hblk := congrFun e (.e k 1)
    apply hgood
    have hzero : (fun l => trV g cc (FV Ls ((0 : ℂ) • w)) (.e k l)) = 0 := by
      funext l
      have := congrFun e (.e k l)
      rw [this]; simp only [scaleV_e]
      have : trV g cc (FV Ls ((0 : ℂ) • w)) (.e k 1) = 0 := hk
      rw [this, zero_mul]; rfl
    have hblk' : (fun l => trV g cc (FV Ls ((0 : ℂ) • w)) (.e k l)) =
        nlawc (cc k) (Ls k).g₂ (Ls k).g₃ (fun l => FV Ls ((0 : ℂ) • w) (.e k l)) (repV (g.2.2 k)) := by
      funext l; simp [trV, translVar, eval_lawPolyV]
    have hF0 : (fun l => FV Ls ((0 : ℂ) • w) (.e k l)) = (ν k : ℂ) • repV ((0 : GPtV d₀ d₁ Ls).2.2 k) := by
      rw [zero_smul, hν, expGV_zero]; funext l; simp [coords]
    rw [hblk', hF0, nlawc_smul_left] at hzero
    have h3 : (ν k : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (ν k).ne_zero
    funext l
    have := congrFun hzero l
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left h3
  -- reduce to `Q₂ = scl (S 0)⁻¹ Q`
  set Q₂ := scl (fun k => (S 0 k)⁻¹) Q
  have hQ₂ : Q₂ ∈ vanish H := scl_mem_vanish (fun k => (Units.mk0 _ (hS0 k))⁻¹) hQ
  suffices hsuff : eval (scaleV (S 0) (FV Ls p)) (Dh Ls w Q₂) = 0 by
    rw [eval_Dh_scale, scl_scl_inv hS0] at hsuff
    exact (mul_eq_zero.mp hsuff).resolve_left
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hS0 k))
  -- the two expressions of the derivative of `c ↦ (τ_g Q₂)(FV(c w))` at `0`
  have hgoodc := goodV_eventually (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) w
  have hgoodp := goodV_eventually hp w
  simp only [zero_add] at hgoodc
  have hA : HasDerivAt (fun c : ℂ => eval (FV Ls (c • w)) (τ Ls g cc Q₂)) 0 0 := by
    have := hasDerivAt_eval_FV (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) w (τ Ls g cc Q₂)
    rw [hw _ (transl_mem_vanish hH hpH cc hQ₂)] at this
    simpa using this
  -- the rescaled curve
  have hSd : ∀ k, HasDerivAt (fun c => S c k)
      (∑ v, eval (FV Ls 0) (pderiv v (translVar Ls g cc (.e k 1))) *
        DV Ls w (FV Ls 0) v) 0 := by
    intro k
    have := LSG.ME.hasDerivAt_eval (Y := fun c : ℂ => FV Ls (0 + c • w)) (c₀ := 0)
      (fun v => hasDerivAt_FV (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) w v)
      (translVar Ls g cc (.e k 1))
    simpa [S, trV] using this
  set S' : Fin m → ℂ := fun k => ∑ v, eval (FV Ls 0) (pderiv v (translVar Ls g cc (.e k 1))) *
        DV Ls w (FV Ls 0) v
  have hZ : ∀ v, HasDerivAt (fun c => scaleV (S c) (FV Ls (p + c • w)) v)
      (scaleV (S 0) (DV Ls w (FV Ls p)) v + ∑ k, S' k * blockPart k (FV Ls p) v) 0 := by
    intro v
    have hF := hasDerivAt_FV hp w v
    cases v with
    | e k c =>
      refine ((hSd k).mul hF).congr_deriv ?_
      simp only [scaleV_e, blockPart, zero_smul, add_zero]
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [ite_true]; ring
    | x i => simpa [blockPart] using hF
    | y j => simpa [blockPart] using hF
    | z j => simpa [blockPart] using hF
  have hB := LSG.ME.hasDerivAt_eval hZ Q₂
  have heq : (fun c : ℂ => eval (FV Ls (c • w)) (τ Ls g cc Q₂)) =ᶠ[𝓝 0]
      fun c => eval (scaleV (S c) (FV Ls (p + c • w))) Q₂ := by
    filter_upwards [hgoodc, hgoodp] with c h0 h1
    rw [eval_τ, trV_FV h0 h1 cc]
  have huniq := (hA.congr_of_eventuallyEq heq.symm).unique hB
  simp only [zero_smul, add_zero] at huniq
  -- split the derivative
  obtain ⟨ν, hν⟩ := FV_eq_coords hp
  have hZ0 : scaleV (S 0) (FV Ls p) = coords g fun k => Units.mk0 _ (hS0 k) * ν k := by
    rw [hν, ← scaleV_coords]; rfl
  have heuler : ∀ k, ∑ v, eval (scaleV (S 0) (FV Ls p)) (pderiv v Q₂) * blockPart k (FV Ls p) v
      = 0 := by
    intro k
    have h := euler_eq_zero hQ₂ hpH (fun k => Units.mk0 _ (hS0 k) * ν k) k
    rw [← hZ0] at h
    have hb : blockPart k (scaleV (S 0) (FV Ls p)) = S 0 k • blockPart k (FV Ls p) := by
      funext v; cases v with
      | e k' c => by_cases hk : k' = k <;> simp [blockPart, hk]
      | x i => simp [blockPart]
      | y j => simp [blockPart]
      | z j => simp [blockPart]
    rw [hb] at h
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ (S 0 k), ← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left (hS0 k)
  have hsplit : ∑ v, eval (scaleV (S 0) (FV Ls p)) (pderiv v Q₂) *
      (scaleV (S 0) (DV Ls w (FV Ls p)) v + ∑ k, S' k * blockPart k (FV Ls p) v) =
      ∑ v, eval (scaleV (S 0) (FV Ls p)) (pderiv v Q₂) * scaleV (S 0) (DV Ls w (FV Ls p)) v := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    have : ∀ k ∈ Finset.univ, ∑ v, eval (scaleV (S 0) (FV Ls p)) (pderiv v Q₂) *
        (S' k * blockPart k (FV Ls p) v) = 0 := fun k _ => by
      simp only [mul_left_comm _ (S' k), ← Finset.mul_sum, heuler k, mul_zero]
    rw [Finset.sum_eq_zero this, add_zero]
  rw [eval_Dh]
  simp only [DV_scale, mul_left_comm _ (∏ k, S 0 k ^ 2), ← Finset.mul_sum]
  rw [← hsplit, ← huniq, mul_zero]

omit hc in
/-- **`D̂_w` preserves `vanish H`** for `w ∈ TZ H`. -/
theorem Dh_mem_vanish {w : TanG d₀ d₁ m} (hw : w ∈ TZ Ls H) {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : Q ∈ vanish H) : Dh Ls w Q ∈ vanish H := by
  refine mem_vanish.mpr fun g hg lam => ?_
  by_cases hV : ∀ k, repV (g.2.2 k) 1 ≠ 0
  · obtain ⟨p, rfl⟩ := expGV_surjective Ls g
    have hp : GoodV Ls p := (goodV_iff p).mpr hV
    obtain ⟨ν, hν⟩ := FV_eq_coords hp
    let ρ : Fin m → ℂˣ := fun k => lam k * (ν k)⁻¹
    have hco : coords (expGV Ls p) lam = scaleV (fun k => (ρ k : ℂ)) (FV Ls p) := by
      rw [hν, scaleV_coords]; congr 1; funext k; simp [ρ]
    rw [hco, eval_Dh_scale]
    rw [first_order hH hw hg hp (scl_mem_vanish ρ hQ), mul_zero]
  · push Not at hV
    obtain ⟨k, hk⟩ := hV
    exact eval_Dh_eq_zero_of_V lam hk w Q

/-- **Zariski tangent vectors integrate**: `TZ H ⊆ lieAlg H`. -/
theorem TZ_subset_lieAlg {w : TanG d₀ d₁ m} (hw : w ∈ TZ Ls H) : w ∈ lieAlg Ls hH := by
  classical
  let f : MvPolynomial (Var d₀ d₁ m) ℂ → ℂ → ℂ := fun Q c => eval (FV Ls (0 + c • w)) Q
  set B := {c : ℂ | GoodV Ls ((0 : TanG d₀ d₁ m) + c • w)}
  have hBo : IsOpen B := by
    have : B = ⋂ k, (fun c : ℂ => ellW (Ls k) 2 (((0 : TanG d₀ d₁ m) + c • w).2.2.1 k)) ⁻¹' {0}ᶜ := by
      ext c; simp [B, GoodV]
    rw [this]
    refine isOpen_iInter_of_finite fun k => (isOpen_compl_singleton).preimage ?_
    have : Continuous (fun c : ℂ => ((0 : TanG d₀ d₁ m) + c • w).2.2.1 k) := by
      simp only [zero_add, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]; fun_prop
    exact (LSG.Aux.differentiable_ellW (Ls k) 2).continuous.comp this
  have h0B : (0 : ℂ) ∈ B := by simpa [B] using goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)
  have hderiv : ∀ Q, ∀ c ∈ B, HasDerivAt (f Q) (f (Dh Ls w Q) c) c :=
    fun Q c hc => hasDerivAt_eval_FV_at hc Q
  have hf0 : ∀ Q ∈ vanish H, f Q 0 = 0 := by
    intro Q hQ
    obtain ⟨ν, hν⟩ := FV_eq_coords (p := (0 : TanG d₀ d₁ m) + (0 : ℂ) • w) h0B
    simp only [f]
    rw [hν]
    exact mem_vanish.mp hQ _ (by simpa [expGV_zero] using hH.zero_mem) ν
  have hiter : ∀ n, ∀ Q ∈ vanish H, iteratedDeriv n (f Q) 0 = 0 := by
    intro n
    induction n with
    | zero => intro Q hQ; simpa using hf0 Q hQ
    | succ n ih =>
      intro Q hQ
      rw [iteratedDeriv_succ']
      have hev : deriv (f Q) =ᶠ[𝓝 0] f (Dh Ls w Q) := by
        filter_upwards [hBo.mem_nhds h0B] with c hc
        exact (hderiv Q c hc).deriv
      rw [hev.iteratedDeriv_eq n]
      exact ih _ (Dh_mem_vanish hH hw hQ)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBo 0 h0B
  have han : ∀ Q, AnalyticOnNhd ℂ (f Q) (Metric.ball 0 r) := by
    intro Q
    have hd : DifferentiableOn ℂ (f Q) (Metric.ball 0 r) := fun c hc =>
      (hderiv Q c (hball hc)).differentiableAt.differentiableWithinAt
    exact hd.analyticOnNhd Metric.isOpen_ball
  have hzero : ∀ Q ∈ vanish H, ∀ c ∈ Metric.ball (0 : ℂ) r, f Q c = 0 := by
    intro Q hQ
    have htop : analyticOrderAt (f Q) 0 = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (han Q 0 (Metric.mem_ball_self hr))).mpr fun i _ => hiter i Q hQ
    exact (han Q).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected (Metric.mem_ball_self hr)
      (analyticOrderAt_eq_top.mp htop)
  have hsmall : ∀ c ∈ Metric.ball (0 : ℂ) r, expGV Ls (c • w) ∈ H := by
    intro c hcb
    obtain ⟨ν, hν⟩ := FV_eq_coords (hball hcb)
    rw [← zeros_vanish hc]
    intro Q hQ lam
    let ρ : Fin m → ℂˣ := fun k => lam k * (ν k)⁻¹
    have hco : coords (expGV Ls ((0 : TanG d₀ d₁ m) + c • w)) lam =
        scaleV (fun k => (ρ k : ℂ)) (FV Ls (0 + c • w)) := by
      rw [hν, scaleV_coords]; congr 1; funext k; simp [ρ]
    have := hzero _ (scl_mem_vanish ρ hQ) c hcb
    simp only [f, eval_scl] at this
    rw [zero_add] at hco
    rw [hco]; simpa using this
  intro c
  refine smul_mem_of_frequently hc w 0 ?_ c
  have hev : ∀ᶠ c' in 𝓝[≠] (0 : ℂ), expGV Ls (c' • w) ∈ H :=
    nhdsWithin_le_nhds (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr) fun c' h => hsmall c' h)
  exact hev.frequently

omit hc in
/-- `lieAlg H ⊆ TZ H`. -/
theorem lieAlg_subset_TZ {w : TanG d₀ d₁ m} (hw : w ∈ lieAlg Ls hH) : w ∈ TZ Ls H := by
  intro Q hQ
  have hd := hasDerivAt_eval_FV (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) w Q
  have hev : (fun c : ℂ => eval (FV Ls (0 + c • w)) Q) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [goodV_eventually (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁)) w] with c hc'
    obtain ⟨ν, hν⟩ := FV_eq_coords hc'
    rw [hν]; exact mem_vanish.mp hQ _ (by rw [zero_add]; exact hw c) ν
  exact hd.unique ((hasDerivAt_const _ _).congr_of_eventuallyEq hev)

/-- **`TZ H = lieAlg H`.** -/
theorem TZ_eq_lieAlg : TZ Ls H = lieAlg Ls hH :=
  le_antisymm (fun _ hw => TZ_subset_lieAlg hH hc hw) fun _ hw => lieAlg_subset_TZ hH hw

end First

end

end LSG.MEV
