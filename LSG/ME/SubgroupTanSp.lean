import Mathlib
import LSG.ME.SubgroupIrred
import LSG.ME.SmoothPoint

/-!
# Zariski tangent spaces of `vanish H` on the cone (STAGE2 §5, item 5; `K = ℂ`)

`tangentSpace p a` (`LSG.ME.SmoothPoint`) is the Zariski tangent space at a cone point `a` of the
affine cone `Z(p) ⊆ ℂ^Var`. The cone directions contribute `m` extra dimensions uniformly:

* `scal k a`: the `k`-th cone scaling direction at `a` (the block-`k` part of `a`); it lies in
  `tangentSpace (vanish E) a` at every zero `a` of `vanish E` (`scal_mem_tangentSpace`, Euler).
* **`finrank_tangentSpace_zero_le`**: at the identity, `dim T ≤ dim_ℂ lieAlg H + m` (a tangent vector is
  `D_w + Σ s_k · scal_k` with `w ∈ TZ H = lieAlg H`).
* **`le_finrank_tangentSpace`**: at a `V`-normalised point `a` of `H⁰`,
  `dim_ℂ lieAlg H + m ≤ dim T_a(vanish H⁰)` (the vectors `D̂_w(a)`, `w ∈ lieAlg H`, by the first-order
  step for `H⁰`, plus the scalings; injectivity because the `V`-chart derivation is nonzero on `E`).
* **`finrank_tangentSpace_scale`**: rescaling the cone coordinates does not change the dimension.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set Module
open LSG.W88 (Tan)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- The `k`-th cone scaling direction at `a`. -/
def scal (k : Fin m) (a : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ := fun i => (wE k i : ℂ) * a i

/-- **Cone scalings are tangent.** -/
theorem scal_mem_tangentSpace {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} {a : Var d₀ d₁ m → ℂ}
    (ha : ∀ P ∈ vanish E, eval a P = 0) (k : Fin m) : scal k a ∈ tangentSpace (vanish E) a := by
  classical
  intro f hf
  obtain ⟨s, hs⟩ := sum_multiComp f
  have key : ∀ d, ∑ i, scal k a i * eval a (pderiv i (weightedHomogeneousComponent wV d f)) = 0 := by
    intro d
    have hd : IsWeightedHomogeneous (wE k) (weightedHomogeneousComponent wV d f) (d k) :=
      fun t ht => by rw [weight_wE, (weightedHomogeneousComponent_isWeightedHomogeneous d f) ht]
    have := congrArg (eval a) hd.sum_weight_X_mul_pderiv
    rw [map_nsmul, ha _ (multiComp_mem_vanish d hf), smul_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scal, map_mul, eval_X, nsmul_eq_mul, map_natCast]
    ring
  have hp : ∀ i, pderiv i f = ∑ d ∈ s, pderiv i (weightedHomogeneousComponent wV d f) := by
    intro i; conv_lhs => rw [hs]
    rw [map_sum]
  simp_rw [hp, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun d _ => key d

/-- The directional derivative is `Σ v_i ∂_i P(a)`. -/
theorem hasDerivAt_dir (a v : Var d₀ d₁ m → ℂ) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    HasDerivAt (fun c : ℂ => eval (a + c • v) P) (∑ i, v i * eval a (pderiv i P)) 0 := by
  classical
  have := hasDerivAt_eval (c₀ := 0) (Y := fun c : ℂ => a + c • v) (Y' := v) (fun i => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (a i)) P
  simp only [zero_smul, add_zero] at this
  refine this.congr_deriv (Finset.sum_congr rfl fun i _ => mul_comm _ _)

/-! ### The tangent space at the identity -/

variable {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-- The identity's cone point `coords 0 1`. -/
noncomputable abbrev a0 (Ls : Fin m → PeriodPair) (d₀ d₁ : ℕ) : Var d₀ d₁ m → ℂ :=
  coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1

theorem a0_x (i : Fin d₀) : a0 Ls d₀ d₁ (.x i) = 0 := rfl
theorem a0_y (j : Fin d₁) : a0 Ls d₀ d₁ (.y j) = 1 := by simp [coords]
theorem a0_z (j : Fin d₁) : a0 Ls d₀ d₁ (.z j) = 1 := by simp [coords]
theorem a0_e (k : Fin m) (c : Fin 3) : a0 Ls d₀ d₁ (.e k c) = O c := by
  simp only [coords, coordsZ_e, Pi.one_apply, Units.val_one, one_mul]; rfl

/-- **Upper bound at the identity**: `dim T_0 (vanish H) ≤ dim_ℂ lieAlg H + m`. -/
theorem finrank_tangentSpace_zero_le (hH : IsSubgroupG H) (hc : IsZClosed H) :
    finrank ℂ (tangentSpace (vanish H) (a0 Ls d₀ d₁)) ≤ finrank ℂ (lieAlg Ls hH hc) + m := by
  classical
  set a := a0 Ls d₀ d₁
  have h0H : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ H := hH.zero_mem
  have ha : ∀ P ∈ vanish H, eval a P = 0 := fun P hP => mem_vanish.mp hP 0 h0H 1
  -- the explicit linear map `(w, s) ↦ D_w(0) + Σ s_k scal_k`
  let Φ : (Tan d₀ d₁ m × (Fin m → ℂ)) →ₗ[ℂ] (Var d₀ d₁ m → ℂ) :=
    { toFun := fun ws v => match v with
        | .x i => ws.1.1 i
        | .y j => ws.1.2.1 j
        | .z j => -ws.1.2.1 j
        | .e k c => if c = 0 then -(1 / 2) * ws.1.2.2 k else if c = 1 then ws.2 k else 0
      map_add' := fun ws ws' => by
        funext v; cases v with
        | x i => rfl
        | y j => rfl
        | z j => simp; ring
        | e k c => simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun r ws => by
        funext v; cases v with
        | x i => rfl
        | y j => rfl
        | z j => simp
        | e k c => simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]; split_ifs <;> ring }
  let Ψ := Φ ∘ₗ (LinearMap.prodMap (lieAlg Ls hH hc).subtype LinearMap.id)
  have hle : tangentSpace (vanish H) a ≤ LinearMap.range Ψ := by
    intro v hv
    have hdir : ∀ P ∈ vanish H, ∑ i, v i * eval a (pderiv i P) = 0 := hv
    -- constraints from `I_G`
    have hyz : ∀ j, v (.z j) = -v (.y j) := by
      intro j
      have h := hdir _ (IG_le_vanish two_ne_zero H (YZ_mem_IG (g2L Ls) (g3L Ls) j))
      have hd := hasDerivAt_dir a v (YZ ℂ d₀ m j)
      rw [h] at hd
      have hd' : HasDerivAt (fun c : ℂ => eval (a + c • v) (YZ ℂ d₀ m j))
          (v (.y j) + v (.z j)) 0 := by
        have e : (fun c : ℂ => eval (a + c • v) (YZ ℂ d₀ m j)) =
            fun c => (1 + c * v (.y j)) * (1 + c * v (.z j)) - 1 := by
          funext c; simp [YZ, a, a0_y, a0_z]
        rw [e]
        have := (((hasDerivAt_id (0 : ℂ)).mul_const (v (.y j))).const_add 1).mul
          (((hasDerivAt_id (0 : ℂ)).mul_const (v (.z j))).const_add 1) |>.sub_const 1
        simpa using this
      have := hd.unique hd'
      linear_combination -this
    have hW : ∀ k, v (.e k 2) = 0 := by
      intro k
      have h := hdir _ (IG_le_vanish two_ne_zero H (Fk_mem_IG (g2L Ls) (g3L Ls) k))
      have hd := hasDerivAt_dir a v (Fk (g2L Ls) (g3L Ls) d₀ d₁ k)
      rw [h] at hd
      have hd' : HasDerivAt (fun c : ℂ => eval (a + c • v) (Fk (g2L Ls) (g3L Ls) d₀ d₁ k))
          (v (.e k 2)) 0 := by
        have e : (fun c : ℂ => eval (a + c • v) (Fk (g2L Ls) (g3L Ls) d₀ d₁ k)) =
            fun c => (1 + c * v (.e k 1)) ^ 2 * (c * v (.e k 2)) - 4 * (c * v (.e k 0)) ^ 3 +
              g2L Ls k * (c * v (.e k 0)) * (c * v (.e k 2)) ^ 2 + g3L Ls k * (c * v (.e k 2)) ^ 3 := by
          funext c; simp [Fk, F, a, a0_e, O]
        rw [e]
        have hl : ∀ b : ℂ, HasDerivAt (fun c : ℂ => c * b) b 0 := fun b => by
          simpa using (hasDerivAt_id (0 : ℂ)).mul_const b
        have t1 := (((hl (v (.e k 1))).const_add 1).pow 2).mul (hl (v (.e k 2)))
        have t2 := ((hl (v (.e k 0))).pow 3).const_mul 4
        have t3 := ((hl (v (.e k 0))).const_mul (g2L Ls k)).mul ((hl (v (.e k 2))).pow 2)
        have t4 := ((hl (v (.e k 2))).pow 3).const_mul (g3L Ls k)
        have := ((t1.sub t2).add t3).add t4
        convert this using 1
        simp
      exact (hd.unique hd').symm
    -- the parameters
    let w : Tan d₀ d₁ m := (fun i => v (.x i), fun j => v (.y j), fun k => -2 * v (.e k 0))
    let s : Fin m → ℂ := fun k => v (.e k 1)
    have hΦ : Φ (w, s) = v := by
      funext i
      cases i with
      | x i => rfl
      | y j => rfl
      | z j => exact (hyz j).symm
      | e k c => fin_cases c <;> simp [Φ, w, s, hW k]
    -- `w ∈ TZ H`
    have hscal : ∀ k, scal k a ∈ tangentSpace (vanish H) a := scal_mem_tangentSpace ha
    have hwTZ : w ∈ TZ Ls H := by
      refine mem_TZ.mpr fun P hP => ?_
      rw [chartAt_zero, Dw_apply, map_sum]
      change ∑ x, eval a (dval (g2L Ls) (g3L Ls) (fun _ => 1) w x * pderiv x P) = 0
      have hval : ∀ i, eval a (dval (g2L Ls) (g3L Ls) (fun _ => 1) w i) =
          v i - ∑ k, s k * scal k a i := by
        have hax : ∀ i, a (.x i) = 0 := a0_x
        have hay : ∀ j, a (.y j) = 1 := a0_y
        have haz : ∀ j, a (.z j) = 1 := a0_z
        have hae : ∀ k c, a (.e k c) = O c := a0_e
        intro i
        cases i with
        | x i => simp [dval, scal, wE, wV, hax, w]
        | y j => simp [dval, scal, wE, wV, hay, w]
        | z j => simp [dval, scal, wE, wV, haz, w, hyz j]
        | e k c =>
          rw [Finset.sum_eq_single k (fun b _ hb => by simp [scal, wE, wV, hb.symm])
            (by simp)]
          fin_cases c <;> simp [dval, scal, wE, wV, hae, O, chartPoly, chartV, w, s, hW k] <;> ring
      simp only [map_mul, hval, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hdir P hP, Finset.sum_comm, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      have h0 : s k * ∑ i, scal k a i * eval a (pderiv i P) = 0 := by
        rw [(hscal k) P hP, mul_zero]
      rw [← h0, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact ⟨(⟨w, (mem_TZ_iff hH hc).mp hwTZ⟩, s), hΦ⟩
  calc finrank ℂ (tangentSpace (vanish H) a) ≤ finrank ℂ (LinearMap.range Ψ) :=
        Submodule.finrank_mono hle
    _ ≤ finrank ℂ ((lieAlg Ls hH hc) × (Fin m → ℂ)) := LinearMap.finrank_range_le Ψ
    _ = finrank ℂ (lieAlg Ls hH hc) + m := by
        rw [Module.finrank_prod, Module.finrank_fin_fun]

/-! ### Lower bound at a `V`-normalised point of `H⁰` -/

variable (Ls) in
/-- `D̂_w` at a `V`-normalised point, explicitly. -/
noncomputable def dvec (a : Var d₀ d₁ m → ℂ) (w : Tan d₀ d₁ m) : Var d₀ d₁ m → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * a (.y j)
  | .z j => -(w.2.1 j * a (.z j))
  | .e k c => w.2.2 k * chartVf (g2L Ls k) (g3L Ls k) (fun c => a (.e k c)) c

theorem eval_dhat_eq_dvec {a : Var d₀ d₁ m → ℂ} (hV : ∀ k, a (.e k 1) = 1) (w : Tan d₀ d₁ m)
    (i : Var d₀ d₁ m) : eval a (dhat (g2L Ls) (g3L Ls) w i) = dvec Ls a w i := by
  rw [dhat, map_mul, eval_Vfac_of_V hV, one_mul]
  cases i with
  | x i => simp [dval, dvec]
  | y j => simp [dval, dvec]
  | z j => simp [dval, dvec]
  | e k c => simp only [dval, dvec, map_mul, eval_C, eval_chartPoly_one]

theorem sum_dvec_eq {a : Var d₀ d₁ m → ℂ} (hV : ∀ k, a (.e k 1) = 1) (w : Tan d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    ∑ i, dvec Ls a w i * eval a (pderiv i P) = eval a (Dhat (g2L Ls) (g3L Ls) w P) := by
  rw [Dhat, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, eval_dhat_eq_dvec hV]

/-- The `V`-chart derivation does not vanish at a `V`-normalised point of `E`. -/
theorem chartVf_ne_zero {a b U W : ℂ} (hF : W - 4 * U ^ 3 + a * U * W ^ 2 + b * W ^ 3 = 0) :
    chartVf a b ![U, 1, W] ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [chartVf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h0 h2
  have hW : W = 0 := by linear_combination W * h0 - U * h2 + (3 / 2 : ℂ) * hF
  subst hW
  have hU : U = 0 := by
    have : U ^ 3 = 0 := by linear_combination -(1 / 4 : ℂ) * hF
    exact (pow_eq_zero_iff (by norm_num)).mp this
  subst hU
  norm_num at h0

/-- **Lower bound at a `V`-normalised point of `H⁰`.** -/
theorem le_finrank_tangentSpace {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} (hH : IsSubgroupG H)
    (hc : IsZClosed H) {p : Tan d₀ d₁ m} (hp : expG Ls p ∈ H0 Ls hH hc) {U : Fin m → Set ℂ}
    {F : Fin m → ℂ → Fin 3 → ℂ} (hF : IsVLift Ls U F) (hpU : ∀ k, p.2.2 k ∈ U k) :
    finrank ℂ (lieAlg Ls hH hc) + m ≤
      finrank ℂ (tangentSpace (vanish (H0 Ls hH hc)) (liftX F p)) := by
  classical
  obtain ⟨lam, hlam⟩ := hF.liftX_eq hpU
  set a := liftX F p
  have hV : ∀ k, a (.e k 1) = 1 := hF.V_eq hpU
  have ha : ∀ P ∈ vanish (H0 Ls hH hc), eval a P = 0 := fun P hP => by
    rw [hlam]; exact mem_vanish.mp hP _ hp lam
  have hH0 := H0_isSubgroup hH hc
  have hc0 := isZClosed_H0 (Ls := Ls) hH hc
  have hTZ : ∀ w ∈ lieAlg Ls hH hc, w ∈ TZ Ls (H0 Ls hH hc) := fun w hw =>
    (mem_TZ_iff hH0 hc0).mpr (mem_lieAlg.mpr fun c =>
      mem_Htil.mpr (expG_mem_H0 hH hc ((lieAlg Ls hH hc).smul_mem c hw)))
  have hδ : ∀ w ∈ lieAlg Ls hH hc, dvec Ls a w ∈ tangentSpace (vanish (H0 Ls hH hc)) a := by
    intro w hw f hf
    obtain ⟨s, hs⟩ := sum_multiComp f
    have hp' : ∀ i, pderiv i f = ∑ d ∈ s, pderiv i (weightedHomogeneousComponent wV d f) := by
      intro i; conv_lhs => rw [hs]
      rw [map_sum]
    simp_rw [hp', map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [sum_dvec_eq hV]
    exact eval_Dhat_lift_eq_zero hH0 (hTZ w hw) hp hF hpU
      ⟨multiComp_mem_vanish d hf, d, weightedHomogeneousComponent_isWeightedHomogeneous d f⟩
  have hscal : ∀ k, scal k a ∈ tangentSpace (vanish (H0 Ls hH hc)) a := scal_mem_tangentSpace ha
  let Φ : ((lieAlg Ls hH hc) × (Fin m → ℂ)) →ₗ[ℂ] (Var d₀ d₁ m → ℂ) :=
    { toFun := fun ws => dvec Ls a ws.1 + ∑ k, ws.2 k • scal k a
      map_add' := fun ws ws' => by
        funext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add,
          Prod.snd_add, Submodule.coe_add, add_mul, Finset.sum_add_distrib]
        cases i <;> simp [dvec] <;> ring
      map_smul' := fun r ws => by
        funext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Prod.smul_fst,
          Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, mul_add, Finset.mul_sum]
        cases i <;> simp [dvec] <;> ring }
  have hrange : ∀ ws, Φ ws ∈ tangentSpace (vanish (H0 Ls hH hc)) a := fun ws =>
    Submodule.add_mem _ (hδ _ ws.1.2)
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hscal k))
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, s⟩ h
    have hv : ∀ i, dvec Ls a w i + ∑ k, s k * scal k a i = 0 := fun i => by
      have := congrFun h i
      simpa [Φ] using this
    have hsk : ∀ k, s k = 0 := by
      intro k
      have := hv (.e k 1)
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [scal, wE, wV, hb.symm]) (by simp)] at this
      simpa [dvec, chartVf, scal, wE, wV, hV k] using this
    have hw : (w : Tan d₀ d₁ m) = 0 := by
      have hx : ∀ i, (w : Tan d₀ d₁ m).1 i = 0 := fun i => by
        simpa [dvec, scal, wE, wV] using hv (.x i)
      have hy : ∀ j, (w : Tan d₀ d₁ m).2.1 j = 0 := fun j => by
        have := hv (.y j)
        simp only [dvec, scal, wE, wV, Pi.zero_apply, Nat.cast_zero, zero_mul,
          Finset.sum_const_zero, mul_zero, add_zero] at this
        exact (mul_eq_zero.mp this).resolve_right (by simp [a, liftX, Complex.exp_ne_zero])
      have he : ∀ k, (w : Tan d₀ d₁ m).2.2 k = 0 := by
        intro k
        by_contra hk
        have hFk : a (.e k 2) - 4 * a (.e k 0) ^ 3 + g2L Ls k * a (.e k 0) * a (.e k 2) ^ 2 +
            g3L Ls k * a (.e k 2) ^ 3 = 0 := by
          have := ha _ (IG_le_vanish two_ne_zero _ (Fk_mem_IG (g2L Ls) (g3L Ls) k))
          simp only [Fk, LSG.Elliptic.F, map_add, map_sub, map_mul, map_pow, eval_X, eval_C,
            map_ofNat, hV k] at this
          linear_combination this
        apply chartVf_ne_zero hFk
        funext c
        have := hv (.e k c)
        simp only [hsk, zero_mul, Finset.sum_const_zero, add_zero, dvec] at this
        have hc' := (mul_eq_zero.mp this).resolve_left hk
        rw [show (fun c => a (.e k c)) = ![a (.e k 0), 1, a (.e k 2)] by
          funext c; fin_cases c <;> simp [hV k]] at hc'
        exact hc'
      exact Prod.ext (funext hx) (Prod.ext (funext hy) (funext he))
    exact Prod.ext (Subtype.ext hw) (funext hsk)
  have := LinearMap.finrank_le_finrank_of_injective
    (f := Φ.codRestrict (tangentSpace (vanish (H0 Ls hH hc)) a) hrange)
    (fun x y hxy => hinj (congrArg Subtype.val hxy))
  rwa [Module.finrank_prod, Module.finrank_fin_fun] at this

/-! ### Rescaling the cone coordinates -/

/-- Rescaling of the cone coordinates by `μ`. -/
def scaleV (μ : Fin m → ℂˣ) (x : Var d₀ d₁ m → ℂ) : Var d₀ d₁ m → ℂ :=
  fun i => (∏ k, ((μ k : ℂˣ) : ℂ) ^ wV i k) * x i

theorem finrank_tangentSpace_scale_le {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} (μ : Fin m → ℂˣ)
    (x : Var d₀ d₁ m → ℂ) :
    finrank ℂ (tangentSpace (vanish E) x) ≤ finrank ℂ (tangentSpace (vanish E) (scaleV μ x)) := by
  classical
  set c : Var d₀ d₁ m → ℂ := fun i => ∏ k, ((μ k : ℂˣ) : ℂ) ^ wV i k
  have hc0 : ∀ i, c i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun k _ =>
    pow_ne_zero _ (Units.ne_zero _)
  let σ : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ :=
    aeval fun i => C (c i) * X i
  have hev : ∀ y P, eval y (σ P) = eval (scaleV μ y) P := by
    intro y P
    rw [eval_aeval']
    congr 2
    funext i
    simp [scaleV, c]
  have hvan : ∀ P ∈ vanish E, σ P ∈ vanish E := by
    intro P hP
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [hev]
    have : scaleV μ (coords g lam) = coords g (fun k => μ k * lam k) := by
      rw [coords_mul]; rfl
    rw [this]
    exact mem_vanish.mp hP g hg _
  have hpd : ∀ i P, pderiv i (σ P) = C (c i) * σ (pderiv i P) := by
    intro i P
    induction P using MvPolynomial.induction_on with
    | C a => simp [σ]
    | add p q hp hq => simp only [map_add, hp, hq, mul_add]
    | mul_X p v hp =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, σ, aeval_X, pderiv_X, map_add]
      by_cases hiv : i = v
      · subst hiv; simp; ring
      · simp [hiv]; ring
  let L : (Var d₀ d₁ m → ℂ) →ₗ[ℂ] (Var d₀ d₁ m → ℂ) :=
    { toFun := fun v i => c i * v i
      map_add' := fun v w => by funext i; simp [mul_add]
      map_smul' := fun r v => by funext i; simp; ring }
  have hL : ∀ v ∈ tangentSpace (vanish E) x, L v ∈ tangentSpace (vanish E) (scaleV μ x) := by
    intro v hv P hP
    have := hv (σ P) (hvan P hP)
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpd, map_mul, eval_C, hev]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hinj : Function.Injective (L.restrict hL) := by
    intro v w hvw
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hvw) i
    simp only [L, LinearMap.coe_restrict_apply, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact mul_left_cancel₀ (hc0 i) this
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem scaleV_scaleV_inv (μ : Fin m → ℂˣ) (x : Var d₀ d₁ m → ℂ) :
    scaleV (fun k => (μ k)⁻¹) (scaleV μ x) = x := by
  funext i
  simp only [scaleV, ← mul_assoc, ← Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), Finset.prod_const_one, one_mul]

theorem finrank_tangentSpace_scale {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} (μ : Fin m → ℂˣ)
    (x : Var d₀ d₁ m → ℂ) :
    finrank ℂ (tangentSpace (vanish E) (scaleV μ x)) = finrank ℂ (tangentSpace (vanish E) x) := by
  refine le_antisymm ?_ (finrank_tangentSpace_scale_le μ x)
  have := finrank_tangentSpace_scale_le (E := E) (fun k => (μ k)⁻¹) (scaleV μ x)
  rwa [scaleV_scaleV_inv] at this

end LSG.ME
