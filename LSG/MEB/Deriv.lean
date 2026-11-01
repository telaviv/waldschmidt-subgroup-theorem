/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.PhOpTwo

/-!
# Homogenised chart derivations and the order of vanishing (A4.1a, β)

For a chart choice `ch : ∀ k, Fin (B k).N` (with `ch k ∈ (B k).charts`) and `w = (ξ, η, ζ) ∈ Lie G`,
`Dh ch w = Lc · (Σ ξ_i ∂_{x_i} + Σ η_j (y_j ∂_{y_j} − z_j ∂_{z_j})) + Σ_k Lo_k · Σ_{j,l} ζ_{kj} W^{ch k}_{jl}(X_k) ∂_{e k l}`,
`L_k = X_{e k (ch k)}`, `Lc = Π_k L_k`, `Lo_k = Π_{k' ≠ k} L_{k'}` (`LSG.ME.Order.Dh` for abstract blocks). It raises
every block degree by one (`isHomB_Dh`).

* `hasDerivAt_eval`: the chain rule for polynomial evaluation along a curve.
* **`eval_Dh_liftB`** (analytic meaning, from `θ_flow`):
  `Dh P (liftB u) = Lc(liftB u) · ∂_w (P ∘ liftB)(u) − Σ_k Lo_k(liftB u) (∂_w θ_k)_{ch k} · E_k P (liftB u)`,
  `E_k` the block-`k` Euler operator (`E_k P = d_k P` for `P` homogeneous).
* **`ordAt_Dh`**, **`Dh_mem_ordIdealB`**: for multihomogeneous `P` of order `> n + 1` along `W` (at a lift, resp. on
  `E`) and `w ∈ W`, `Dh ch w P` has order `> n` (the one-derivative case of the two-parameter estimate,
  `LSG.MEB.isBigO_iteratedDeriv_snd`).
* **`DhWord_mem_vanish`**: the Taylor/word bridge for Wüstholz's lemma: all `Dh`-words of length `≤ T` in directions of
  `W` map a multihomogeneous element of `ordIdealB W T E` into `vanish E`.
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### The derivations -/

/-- The chart form of block `k`. -/
noncomputable def Lk (ch : ∀ k, Fin (B k).N) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ := X (.e k (ch k))

/-- The product of the chart forms. -/
noncomputable def Lc (ch : ∀ k, Fin (B k).N) : MvPolynomial (Var d₀ d₁ B) ℂ := ∏ k, Lk ch k

/-- The product of the chart forms of the other blocks. -/
noncomputable def Lo (ch : ∀ k, Fin (B k).N) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∏ k' ∈ Finset.univ.erase k, Lk ch k'

theorem Lk_mul_Lo (ch : ∀ k, Fin (B k).N) (k : Fin m) :
    Lk (d₀ := d₀) (d₁ := d₁) ch k * Lo ch k = Lc ch :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ k)

/-- The coefficients of `Dh ch w`. -/
noncomputable def DhCoef (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) :
    Var d₀ d₁ B → MvPolynomial (Var d₀ d₁ B) ℂ
  | .x i => C (w.1 i) * Lc ch
  | .y j => C (w.2.1 j) * X (.y j) * Lc ch
  | .z j => -(C (w.2.1 j) * X (.z j)) * Lc ch
  | .e k l => Lo ch k * ∑ j, C (w.2.2 k j) * bind₁ (fun b => X (Var.e k b)) ((B k).W (ch k) j l)

/-- **The homogenised chart derivation** `Dh ch w`. -/
noncomputable def Dh (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  ∑ v, DhCoef ch w v • pderiv v

theorem Dh_apply (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    Dh ch w P = ∑ v, DhCoef ch w v * pderiv v P := by
  rw [Dh, show ⇑(∑ v, DhCoef ch w v • (pderiv v : Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ)
      (MvPolynomial (Var d₀ d₁ B) ℂ))) = ∑ v, ⇑(DhCoef ch w v • (pderiv v : Derivation ℂ
      (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))) from
    map_sum Derivation.coeFnAddMonoidHom _ _]
  simp [Finset.sum_apply, smul_eq_mul]

/-! ### Homogeneity -/

theorem isWH_Lc (ch : ∀ k, Fin (B k).N) (k : Fin m) :
    IsWeightedHomogeneous (wk k) (Lc (d₀ := d₀) (d₁ := d₁) ch) 1 := by
  have h := IsWeightedHomogeneous.prod (w := wk k) Finset.univ (fun k' => Lk (d₀ := d₀) (d₁ := d₁) ch k')
    (fun k' => if k' = k then 1 else 0) fun k' _ => by
      simpa [Lk, wk] using isWeightedHomogeneous_X ℂ (wk k) (Var.e k' (ch k') : Var d₀ d₁ B)
  simpa [Lc] using h

theorem isWH_Lo (ch : ∀ k, Fin (B k).N) (k k₀ : Fin m) :
    IsWeightedHomogeneous (wk k) (Lo (d₀ := d₀) (d₁ := d₁) ch k₀) (if k₀ = k then 0 else 1) := by
  have h := IsWeightedHomogeneous.prod (w := wk k) (Finset.univ.erase k₀)
    (fun k' => Lk (d₀ := d₀) (d₁ := d₁) ch k') (fun k' => if k' = k then 1 else 0) fun k' _ => by
      simpa [Lk, wk] using isWeightedHomogeneous_X ℂ (wk k) (Var.e k' (ch k') : Var d₀ d₁ B)
  have e : (∑ i ∈ Finset.univ.erase k₀, if i = k then 1 else 0) = if k₀ = k then 0 else 1 := by
    rw [Finset.sum_ite_eq']
    by_cases hk : k₀ = k
    · simp [hk]
    · simp [Finset.mem_erase, Ne.symm hk, hk]
  rw [e] at h
  exact h

theorem isWH_DhCoef (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) (k : Fin m) (v : Var d₀ d₁ B) :
    IsWeightedHomogeneous (wk k) (DhCoef ch w v) (1 + wk k v) := by
  cases v with
  | x i => simpa [DhCoef, wk] using (isWH_Lc ch k).C_mul (w.1 i)
  | y j =>
    have := ((isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var d₀ d₁ B)).mul (isWH_Lc ch k)).C_mul (w.2.1 j)
    simpa [DhCoef, wk, mul_assoc] using this
  | z j =>
    have := (((isWeightedHomogeneous_X ℂ (wk k) (Var.z j : Var d₀ d₁ B)).mul (isWH_Lc ch k)).C_mul
      (w.2.1 j)).neg
    simpa [DhCoef, wk, mul_assoc] using this
  | e k₀ l =>
    have hW : ∀ j, IsWeightedHomogeneous (wk k)
        (bind₁ (fun b => X (Var.e k₀ b)) ((B k₀).W (ch k₀) j l) : MvPolynomial (Var d₀ d₁ B) ℂ)
        (2 • (if k₀ = k then 1 else 0)) := fun j => by
      have h1 := isWH_map_weight ((B k₀).W_hom (ch k₀) j l)
        (multiplesHom ℕ (if k₀ = k then 1 else 0))
      refine isWeightedHomogeneous_bind₁ (fun b => ?_) (by simpa using h1)
      simpa [wk] using isWeightedHomogeneous_X ℂ (wk k) (Var.e k₀ b : Var d₀ d₁ B)
    have hsum := IsWeightedHomogeneous.sum Finset.univ _ _ fun j _ => (hW j).C_mul (w.2.2 k₀ j)
    have := (isWH_Lo ch k k₀).mul hsum
    convert this using 1
    · rfl
    · show 1 + (if k₀ = k then 1 else 0) = _
      split_ifs <;> simp

/-- `Dh` raises every block degree by one. -/
theorem isHomB_Dh (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hP : IsHomB P d) : IsHomB (Dh ch w P) (d + 1) := by
  intro k
  rw [Dh_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun v _ => ?_
  by_cases h : wk k v ≤ d k
  · have hp : IsWeightedHomogeneous (wk k) (pderiv v P) (d k - wk k v) :=
      (hP k).pderiv (Nat.sub_add_cancel h)
    convert (isWH_DhCoef ch w k v).mul hp using 1
    simp only [Pi.add_apply, Pi.one_apply]; omega
  · have hv : pderiv v P = 0 := by
      refine pderiv_eq_zero_of_notMem_vars fun hv => ?_
      obtain ⟨s, hs, hsv⟩ := (mem_vars_iff_mem_support v).mp hv
      have hw := hP k (mem_support_iff.mp hs)
      have hle : s v * wk k v ≤ Finsupp.weight (wk k) s := by
        rw [Finsupp.weight_apply, Finsupp.sum]
        exact Finset.single_le_sum (f := fun x => s x • wk k x) (fun _ _ => Nat.zero_le _)
          hsv
      have : 1 ≤ s v := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hsv)
      have : wk k v ≤ s v * wk k v := Nat.le_mul_of_pos_left _ this
      omega
    simp [hv, isWeightedHomogeneous_zero]

/-! ### The chain rule -/

theorem hasDerivAt_eval {σ : Type*} [Fintype σ] {x : ℂ → σ → ℂ} {x' : σ → ℂ} {s : ℂ}
    (hx : ∀ v, HasDerivAt (fun r => x r v) (x' v) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun r => eval (x r) P) (∑ v, eval (x s) (pderiv v P) * x' v) s := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p v₀ hp =>
    have h := hp.mul (hx v₀)
    simp only [map_mul, eval_X] at h ⊢
    convert h using 1
    simp only [pderiv_mul, map_add, map_mul, eval_X, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun v _ => by ring
    · rw [Finset.sum_eq_single v₀]
      · simp [pderiv_X]
      · intro v _ hv; simp [pderiv_X, hv]
      · intro h; exact absurd (Finset.mem_univ v₀) h

/-! ### The analytic meaning -/

/-- The derivative of the coordinates of `liftB` along `r ↦ u + r w`. -/
noncomputable def liftB' (u w : Tan d₀ d₁ B) : Var d₀ d₁ B → ℂ
  | .x i => w.1 i
  | .y j => w.2.1 j * Complex.exp (u.2.1 j)
  | .z j => -w.2.1 j * Complex.exp (-u.2.1 j)
  | .e k l => fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) l

theorem hasDerivAt_liftB (u w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    HasDerivAt (fun r : ℂ => liftB (u + r • w) v) (liftB' u w v) 0 := by
  cases v with
  | x i =>
    simpa [liftB, liftB'] using ((hasDerivAt_id (0 : ℂ)).mul_const (w.1 i)).const_add (u.1 i)
  | y j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (u.2.1 j)).cexp
    simpa [liftB, liftB', mul_comm] using h
  | z j =>
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const (w.2.1 j)).const_add (u.2.1 j)).neg.cexp
    simpa [liftB, liftB', mul_comm] using h
  | e k l =>
    have hθ : HasFDerivAt (B k).θ (fderiv ℂ (B k).θ (u.2.2 k)) (u.2.2 k + (0 : ℂ) • w.2.2 k) := by
      simpa using ((B k).θ_analytic (u.2.2 k)).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun r : ℂ => u.2.2 k + r • w.2.2 k) (w.2.2 k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (w.2.2 k)).const_add (u.2.2 k)
    have h := hasDerivAt_pi.mp (hθ.comp_hasDerivAt (0 : ℂ) hl) l
    simpa [liftB, liftB', Function.comp_def] using h

theorem fderiv_apply_eq_sum {N g : ℕ} (θ : (Fin g → ℂ) → Fin N → ℂ) (z w : Fin g → ℂ) :
    fderiv ℂ θ z w = ∑ j, w j • fderiv ℂ θ z (Pi.single j 1) := by
  have hw : w = ∑ j, w j • (Pi.single j 1 : Fin g → ℂ) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul]

theorem eval_Lk_liftB (ch : ∀ k, Fin (B k).N) (u : Tan d₀ d₁ B) (k : Fin m) :
    eval (liftB u) (Lk ch k) = (B k).θ (u.2.2 k) (ch k) := by
  simp [Lk, liftB]

/-- The coefficients of `Dh` at a lifted point (`θ_flow`). -/
theorem eval_DhCoef_liftB (ch : ∀ k, Fin (B k).N) (hch : ∀ k, ch k ∈ (B k).charts) (u w : Tan d₀ d₁ B)
    (v : Var d₀ d₁ B) :
    eval (liftB u) (DhCoef ch w v) = eval (liftB u) (Lc ch) * liftB' u w v -
      ∑ k, eval (liftB u) (Lo ch k) * fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) (ch k) * (wk k v : ℂ) *
        liftB u v := by
  cases v with
  | x i => simp [DhCoef, liftB', wk, mul_comm]
  | y j => simp [DhCoef, liftB', wk, liftB]; ring
  | z j => simp [DhCoef, liftB', wk, liftB]; ring
  | e k₀ l =>
    set z := u.2.2 k₀
    set Dθ := fderiv ℂ (B k₀).θ z (w.2.2 k₀)
    have hW : ∀ j, eval (liftB u) (bind₁ (fun b => X (Var.e k₀ b)) ((B k₀).W (ch k₀) j l)) =
        (B k₀).θ z (ch k₀) * fderiv ℂ (B k₀).θ z (Pi.single j 1) l -
          (B k₀).θ z l * fderiv ℂ (B k₀).θ z (Pi.single j 1) (ch k₀) := fun j => by
      have hθ : (fun v => eval (liftB u) (X (Var.e k₀ v) : MvPolynomial (Var d₀ d₁ B) ℂ)) = (B k₀).θ z := by
        funext v; simp [liftB, z]
      rw [eval_bind₁', hθ, ← (B k₀).θ_flow (ch k₀) (hch k₀) j l z]
    have hsum : ∑ j, w.2.2 k₀ j * ((B k₀).θ z (ch k₀) * fderiv ℂ (B k₀).θ z (Pi.single j 1) l -
          (B k₀).θ z l * fderiv ℂ (B k₀).θ z (Pi.single j 1) (ch k₀)) =
        (B k₀).θ z (ch k₀) * Dθ l - (B k₀).θ z l * Dθ (ch k₀) := by
      simp only [Dθ, fderiv_apply_eq_sum (B k₀).θ z (w.2.2 k₀), Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hLc : eval (liftB u) (Lc ch) = (B k₀).θ z (ch k₀) * eval (liftB u) (Lo ch k₀) := by
      rw [← Lk_mul_Lo ch k₀, map_mul, eval_Lk_liftB]
    have hRHS : ∑ k, eval (liftB u) (Lo ch k) * fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) (ch k) *
        ((wk k (Var.e k₀ l : Var d₀ d₁ B) : ℕ) : ℂ) * liftB u (.e k₀ l) =
        eval (liftB u) (Lo ch k₀) * Dθ (ch k₀) * (B k₀).θ z l := by
      rw [Finset.sum_eq_single k₀]
      · simp [wk, liftB, Dθ, z]
      · intro k _ hk; simp [wk, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ k₀) h
    rw [hRHS]
    simp only [DhCoef, map_mul, map_sum, eval_C, hW, hsum, liftB', hLc]
    rw [show fderiv ℂ (B k₀).θ (u.2.2 k₀) (w.2.2 k₀) l = Dθ l from rfl]
    ring

/-- **The analytic meaning of `Dh`** for multihomogeneous `P`. -/
theorem eval_Dh_liftB (ch : ∀ k, Fin (B k).N) (hch : ∀ k, ch k ∈ (B k).charts)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) (u w : Tan d₀ d₁ B) :
    eval (liftB u) (Dh ch w P) =
      eval (liftB u) (Lc ch) * deriv (fun r : ℂ => eval (liftB (u + r • w)) P) 0 -
        (∑ k, eval (liftB u) (Lo ch k) * fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) (ch k) * d k) *
          eval (liftB u) P := by
  have hd := (hasDerivAt_eval (hasDerivAt_liftB u w) P).deriv
  simp only [zero_smul, add_zero] at hd
  rw [hd, Dh_apply, map_sum]
  simp only [map_mul, eval_DhCoef_liftB ch hch, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have he := congrArg (eval (liftB u)) ((hP k).sum_weight_X_mul_pderiv)
    simp only [map_sum, map_nsmul, nsmul_eq_mul, map_mul, eval_X, smul_eq_mul, map_natCast] at he
    set c := eval (liftB u) (Lo ch k) * fderiv ℂ (B k).θ (u.2.2 k) (w.2.2 k) (ch k)
    calc ∑ v, c * (wk k v : ℂ) * liftB u v * eval (liftB u) (pderiv v P)
        = c * ∑ v, (wk k v : ℂ) * (liftB u v * eval (liftB u) (pderiv v P)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
      _ = c * (d k) * eval (liftB u) P := by rw [he]; ring

/-! ### The bridge -/

theorem continuous_eval_liftB_affine (Q : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) :
    Continuous fun s : ℂ => eval (liftB (u + s • w)) Q :=
  continuous_iff_continuousAt.mpr fun s₀ =>
    (analyticAt_eval_of (f := fun v (s : ℂ) => liftB (u + s • w) v)
      (fun v => analyticAt_liftB_comp (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) v)
      Q).continuousAt

/-- **`Dh` lowers the order by one** (multihomogeneous `P`, `w ∈ W`). -/
theorem ordAt_Dh {W : Submodule ℂ (Tan d₀ d₁ B)} (ch : ∀ k, Fin (B k).N) (hch : ∀ k, ch k ∈ (B k).charts)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) {n : ℕ} {u w : Tan d₀ d₁ B}
    (hw : w ∈ W) (h : OrdAt W P (n + 1) u) : OrdAt W (Dh ch w P) n u := by
  rw [ordAt_iff_one (isHomB_Dh ch w hP)]
  intro w' hw'
  have h1 := (ordAt_iff_one hP).mp h
  let H : ℂ × ℂ → ℂ := fun q => eval (liftB (u + (q.1 • w' + q.2 • w))) P
  have hHa : AnalyticOnNhd ℂ H univ := fun q₀ _ => by
    have haff : AnalyticAt ℂ (fun q : ℂ × ℂ => u + (q.1 • w' + q.2 • w)) q₀ :=
      analyticAt_const.add ((analyticAt_fst.smul analyticAt_const).add (analyticAt_snd.smul analyticAt_const))
    have hv : ∀ v, AnalyticAt ℂ (fun q : ℂ × ℂ => liftB (u + (q.1 • w' + q.2 • w)) v) q₀ :=
      fun v => analyticAt_liftB_comp haff v
    exact analyticAt_eval_of hv P
  have hH : H =O[𝓝 0] fun q => ‖q‖ ^ (n + 2) := by
    refine isBigO_of_diag hHa fun v k hk => ?_
    have hmem : v.1 • w' + v.2 • w ∈ W := W.add_mem (W.smul_mem _ hw') (W.smul_mem _ hw)
    have e : (fun r : ℂ => H (r • v)) = lineF P u (v.1 • w' + v.2 • w) 1 := by
      funext r
      simp only [H, lineF, liftZ_one, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    rw [e]
    exact h 1 _ hmem k (Nat.lt_succ_iff.mp hk)
  have hD : (fun s => iteratedDeriv 1 (fun r => H (s, r)) 0) =O[𝓝 0] fun s => ‖s‖ ^ (n + 1) := by
    simpa using isBigO_iteratedDeriv_snd (κ := 1) hHa hH (by omega)
  have hform : lineF (Dh ch w P) u w' 1 = fun s =>
      eval (liftB (u + s • w')) (Lc ch) * iteratedDeriv 1 (fun r => H (s, r)) 0 -
        (∑ k, eval (liftB (u + s • w')) (Lo ch k) *
          fderiv ℂ (B k).θ ((u + s • w').2.2 k) (w.2.2 k) (ch k) * d k) * lineF P u w' 1 s := by
    funext s
    simp only [lineF_one]
    rw [eval_Dh_liftB ch hch hP, iteratedDeriv_one]
    congr 3
    funext r
    simp only [H, add_assoc]
  rw [hform]
  refine IsBigO.sub ?_ ?_
  · simpa using ((continuous_eval_liftB_affine (Lc ch) u w').continuousAt.isBigO_one ℝ).mul hD
  · have hE : ContinuousAt (fun s : ℂ => ∑ k, eval (liftB (u + s • w')) (Lo ch k) *
        fderiv ℂ (B k).θ ((u + s • w').2.2 k) (w.2.2 k) (ch k) * d k) 0 := by
      refine tendsto_finsetSum _ fun k _ => ?_
      refine ((continuous_eval_liftB_affine _ u w').continuousAt.mul ?_).mul continuousAt_const
      have hf : ContinuousAt (fun z => fderiv ℂ (B k).θ z) ((u + (0 : ℂ) • w').2.2 k) :=
        ((B k).θ_analytic _).fderiv.continuousAt
      have hz : Continuous fun s : ℂ => (u + s • w').2.2 k := by fun_prop
      exact (continuous_apply (ch k)).continuousAt.comp
        ((ContinuousLinearMap.apply ℂ _ (w.2.2 k)).continuous.continuousAt.comp
          (hf.comp hz.continuousAt))
    have h2 := (h1 w' hw').trans (isLittleO_norm_pow_norm_pow (show n + 1 < n + 2 by omega)).isBigO
    simpa using (hE.isBigO_one ℝ).mul h2

/-- **`Dh` maps order `> n + 1` on `E` to order `> n`** (multihomogeneous elements). -/
theorem Dh_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} (ch : ∀ k, Fin (B k).N)
    (hch : ∀ k, ch k ∈ (B k).charts) {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d)
    {n : ℕ} {E : Set (GPt d₀ d₁ B)} {w : Tan d₀ d₁ B} (hw : w ∈ W) (h : P ∈ ordIdealB W (n + 1) E) :
    Dh ch w P ∈ ordIdealB W n E :=
  fun u hu => ordAt_Dh ch hch hP hw (h u hu)

/-- A word in the derivations `Dh`. -/
noncomputable def DhWord : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B) →
    MvPolynomial (Var d₀ d₁ B) ℂ → MvPolynomial (Var d₀ d₁ B) ℂ
  | [], P => P
  | p :: l, P => Dh p.1 p.2 (DhWord l P)

theorem DhWord_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)} :
    ∀ (l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)), (∀ p ∈ l, (∀ k, p.1 k ∈ (B k).charts) ∧ p.2 ∈ W) →
      ∀ {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}, IsHomB P d → ∀ {n : ℕ},
        P ∈ ordIdealB W (n + l.length) E →
          DhWord l P ∈ ordIdealB W n E ∧ IsHomB (DhWord l P) (d + (l.length : Fin m → ℕ))
  | [], _, P, d, hP, n, h => ⟨by simpa [DhWord] using h, by simpa [DhWord] using hP⟩
  | p :: l, hl, P, d, hP, n, h => by
    have hl' : ∀ q ∈ l, (∀ k, q.1 k ∈ (B k).charts) ∧ q.2 ∈ W := fun q hq =>
      hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨h1, h2⟩ := DhWord_mem_ordIdealB l hl' hP (n := n + 1) (by
      simpa [List.length_cons, add_assoc, add_comm 1] using h)
    have hp := hl p (List.mem_cons_self ..)
    refine ⟨Dh_mem_ordIdealB p.1 hp.1 h2 hp.2 h1, ?_⟩
    have := isHomB_Dh p.1 p.2 h2
    simpa [DhWord, List.length_cons, add_assoc] using this

/-- **The Taylor/word bridge** (for Wüstholz's lemma): every word of length `≤ T` in the derivations `Dh ch w`
(`ch` in the charts, `w ∈ W`) maps a multihomogeneous element of `ordIdealB W T E` into `vanish E`. -/
theorem DhWord_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)}
    {l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)} (hl : ∀ p ∈ l, (∀ k, p.1 k ∈ (B k).charts) ∧ p.2 ∈ W)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) {T : ℕ} (hlen : l.length ≤ T)
    (h : P ∈ ordIdealB W T E) : DhWord l P ∈ vanish E := by
  have h' : P ∈ ordIdealB W ((T - l.length) + l.length) E := by rwa [Nat.sub_add_cancel hlen]
  exact ordIdealB_le_vanish _ E (DhWord_mem_ordIdealB l hl hP h').1

/-! ### Block degrees -/

section Degree

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq ι] {β : σ → ι}

/-- A derivation raising each variable's block degree by at most `E` raises all block degrees by at most `E`
(`LSG.ME.mkDerivation_mem_FLE`, retyped). -/
theorem mkDerivation_mem_FLE' {f : σ → MvPolynomial σ ℂ} {E : ι → ℕ}
    (hf : ∀ v, f v ∈ StrongSix.M2.FLE ℂ β (Pi.single (β v) 1 + E)) {D : ι → ℕ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ StrongSix.M2.FLE ℂ β D) : mkDerivation ℂ f P ∈ StrongSix.M2.FLE ℂ β (D + E) := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hsS : s ∈ StrongSix.M2.S β D := hP hs
  rw [mkDerivation_monomial]
  refine Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun i hi => ?_)
  have hi1 : 1 ≤ s i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : Finsupp.single i 1 ≤ s := fun x => by
    rw [Finsupp.single_apply]; split_ifs with h
    · subst h; exact hi1
    · exact Nat.zero_le _
  have hb : ∀ b, StrongSix.M2.bdeg β (s - Finsupp.single i 1) b + (if β i = b then 1 else 0) =
      StrongSix.M2.bdeg β s b :=
    fun b => by rw [← StrongSix.M2.bdeg_single, ← StrongSix.M2.bdeg_add, tsub_add_cancel_of_le hle]
  have hmon : (monomial (s - Finsupp.single i 1) ((s i : ℕ) : ℂ) : MvPolynomial σ ℂ) ∈
      StrongSix.M2.FLE ℂ β (D - Pi.single (β i) 1) := by
    rw [StrongSix.M2.FLE, monomial_mem_restrictSupport]
    refine Or.inl fun b => ?_
    have h1 := hb b
    have h2 := hsS b
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases h : b = β i
    · subst h; simp only [ite_true] at h1 ⊢; omega
    · simp only [h, Ne.symm h, ite_false] at h1 ⊢; omega
  dsimp only
  rw [smul_eq_mul]
  refine StrongSix.M2.FLE_mono ℂ β (fun b => ?_) (StrongSix.M2.mul_mem_FLE ℂ hmon (hf i))
  have h1 := hb b
  have h2 := hsS b
  simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h : b = β i
  · subst h; simp only [ite_true] at h1 ⊢; omega
  · simp only [h, Ne.symm h, ite_false] at h1 ⊢; omega

end Degree

/-- The degree shift of `Dh`: `1` on abelian blocks, `0` otherwise. -/
def eOnes : Blk m → ℕ
  | .e _ => 1
  | _ => 0

theorem Dh_eq_mkDerivation (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) :
    Dh ch w = mkDerivation ℂ (DhCoef ch w) := by
  refine derivation_ext fun v => ?_
  rw [Dh_apply, mkDerivation_X, Finset.sum_eq_single v]
  · simp
  · intro v' _ hv'; simp [pderiv_X, Pi.single_apply, Ne.symm hv']
  · intro h; exact absurd (Finset.mem_univ v) h

theorem isWH_wB_Lk (ch : ∀ k, Fin (B k).N) (k : Fin m) :
    IsWeightedHomogeneous wB (Lk (d₀ := d₀) (d₁ := d₁) ch k) (Pi.single (Blk.e k) 1) := by
  simpa [Lk, wB] using isWeightedHomogeneous_X ℂ wB (Var.e k (ch k) : Var d₀ d₁ B)

theorem sum_single_e (s : Finset (Fin m)) (b : Blk m) :
    (∑ k ∈ s, (Pi.single (Blk.e k) 1 : Blk m → ℕ)) b = if ∃ k ∈ s, b = Blk.e k then 1 else 0 := by
  rw [Finset.sum_apply]
  cases b with
  | e k₀ =>
    simp only [Pi.single_apply, Blk.e.injEq]
    rw [Finset.sum_ite_eq]
    by_cases h : k₀ ∈ s <;> simp [h]
  | x => simp [Pi.single_apply]
  | yz => simp [Pi.single_apply]

theorem DhCoef_mem_FLE (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    DhCoef ch w v ∈ StrongSix.M2.FLE ℂ blk (Pi.single (blk v) 1 + eOnes) := by
  have hLc : IsWeightedHomogeneous wB (Lc (d₀ := d₀) (d₁ := d₁) ch) (∑ k, Pi.single (Blk.e k) 1) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => isWH_wB_Lk ch k
  have hLcle : (∑ k, (Pi.single (Blk.e k) 1 : Blk m → ℕ)) = eOnes := by
    funext b; rw [sum_single_e]; cases b <;> simp [eOnes]
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
    have h := (((isWeightedHomogeneous_X ℂ wB (Var.z j : Var d₀ d₁ B)).mul hLc).C_mul (w.2.1 j)).neg
    refine mem_FLE_of_isWH (by simpa [DhCoef, mul_assoc] using h) (le_of_eq ?_)
    simp [wB]
  | e k l =>
    have hLo : IsWeightedHomogeneous wB (Lo (d₀ := d₀) (d₁ := d₁) ch k)
        (∑ k' ∈ Finset.univ.erase k, Pi.single (Blk.e k') 1) :=
      IsWeightedHomogeneous.prod _ _ _ fun k' _ => isWH_wB_Lk ch k'
    have hW : ∀ j, IsWeightedHomogeneous wB
        (bind₁ (fun b => X (Var.e k b)) ((B k).W (ch k) j l) : MvPolynomial (Var d₀ d₁ B) ℂ)
        (2 • Pi.single (Blk.e k) 1) := fun j => by
      have h1 := isWH_map_weight ((B k).W_hom (ch k) j l) (multiplesHom (Blk m → ℕ) (Pi.single (Blk.e k) 1))
      refine isWeightedHomogeneous_bind₁ (fun b => ?_) (by simpa using h1)
      simpa [wB] using isWeightedHomogeneous_X ℂ wB (Var.e k b : Var d₀ d₁ B)
    have hsum := IsWeightedHomogeneous.sum Finset.univ _ _ fun j _ => (hW j).C_mul (w.2.2 k j)
    refine mem_FLE_of_isWH (hLo.mul hsum) (le_of_eq ?_)
    funext b
    simp only [Pi.add_apply, sum_single_e, Pi.smul_apply, smul_eq_mul, blk]
    cases b with
    | e k₀ =>
      by_cases h : k₀ = k
      · subst h; simp [Pi.single_apply, eOnes]
      · simp [Pi.single_apply, eOnes, h]
    | x => simp [Pi.single_apply, eOnes]
    | yz => simp [Pi.single_apply, eOnes]

/-- **Block degrees under `Dh`**: abelian block degrees go up by at most one, the others do not go up. -/
theorem Dh_mem_FLE (ch : ∀ k, Fin (B k).N) (w : Tan d₀ d₁ B) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    Dh ch w P ∈ StrongSix.M2.FLE ℂ blk (D + eOnes) := by
  rw [Dh_eq_mkDerivation]
  exact mkDerivation_mem_FLE' (DhCoef_mem_FLE ch w) hP

/-! ### The glued family `Dmix` and StrongSix's words `DL` -/

/-- All chart derivations, indexed by (chart choice, direction) (`LSG.ME.Dmix`). -/
noncomputable def Dmix (p : (∀ k, Fin (B k).N) × Tan d₀ d₁ B) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Dh p.1 p.2

/-- The admissible indices: charts of the blocks and directions in `W` (`LSG.ME.Wmix`). -/
def Wmix (W : Submodule ℂ (Tan d₀ d₁ B)) : Set ((∀ k, Fin (B k).N) × Tan d₀ d₁ B) :=
  {p | (∀ k, p.1 k ∈ (B k).charts) ∧ p.2 ∈ W}

theorem DL_Dmix_mem_FLE (l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    StrongSix.M2.DL Dmix l P ∈ StrongSix.M2.FLE ℂ blk (D + l.length • eOnes) := by
  induction l generalizing D P with
  | nil => simpa using hP
  | cons p l ih =>
    rw [StrongSix.M2.DL_cons]
    have := ih (Dh_mem_FLE p.1 p.2 hP)
    rwa [List.length_cons, add_smul, one_smul, add_comm (l.length • eOnes), ← add_assoc]

theorem DL_Dmix_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)} :
    ∀ (l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)), (∀ p ∈ l, p ∈ Wmix W) →
      ∀ {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}, IsHomB P d → ∀ {n : ℕ},
        P ∈ ordIdealB W (n + l.length) E → StrongSix.M2.DL Dmix l P ∈ ordIdealB W n E
  | [], _, P, d, hP, n, h => by simpa using h
  | p :: l, hl, P, d, hP, n, h => by
    rw [StrongSix.M2.DL_cons]
    have hp := hl p (List.mem_cons_self ..)
    refine DL_Dmix_mem_ordIdealB l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (isHomB_Dh p.1 p.2 hP)
      (Dh_mem_ordIdealB p.1 hp.1 hP hp.2 ?_)
    simpa [List.length_cons, add_assoc, add_comm 1] using h

/-- **The word bridge in StrongSix's form**: words of length `≤ T` in `Dmix` over `Wmix W` map a multihomogeneous
element of `ordIdealB W T E` into `vanish E` (`LSG.ME.mem_VOg_mix`). -/
theorem DL_Dmix_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)}
    {l : List ((∀ k, Fin (B k).N) × Tan d₀ d₁ B)} (hl : ∀ p ∈ l, p ∈ Wmix W)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomB P d) {T : ℕ} (hlen : l.length ≤ T)
    (h : P ∈ ordIdealB W T E) : StrongSix.M2.DL Dmix l P ∈ vanish E := by
  have h' : P ∈ ordIdealB W ((T - l.length) + l.length) E := by rwa [Nat.sub_add_cancel hlen]
  exact ordIdealB_le_vanish _ E (DL_Dmix_mem_ordIdealB l hl hP h')

end LSG.MEB
