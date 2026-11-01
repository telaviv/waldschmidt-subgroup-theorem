/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Deriv

/-!
# Chart derivations and the order of vanishing (M2.5, β)

The `VBlock` analogue of the second half of `LSG.MEB.Deriv`, for the derivations `Dh ch w` of `LSG.MEBV.Deriv`
(block derivations `X_c² ∂`, degree `+2`).

* **`ordAt_Dh`**, **`Dh_mem_ordIdealB`**: for multihomogeneous `P` of order `> n + 1` along `W` and `w ∈ W`,
  `Dh ch w P` has order `> n` (one-derivative case of the two-parameter estimate, from `eval_Dh_liftV`).
* `DhWord`, **`DhWord_mem_vanish`**: words of length `≤ T` map a multihomogeneous element of `ordIdealB W T E` into
  `vanish E`.
* `Dmix`, `Wmix` (fibre-index choices whose charts are charts of the bases, directions in `W`),
  `DL_Dmix_mem_FLE` (`D ↦ D + |l| • eTwos`), **`DL_Dmix_mem_vanish`** (StrongSix's `DL`).
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEBV

open LSG.MEB (Blk)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

theorem continuous_eval_liftV_affine (Q : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) :
    Continuous fun s : ℂ => eval (liftV (u + s • w)) Q :=
  continuous_iff_continuousAt.mpr fun s₀ =>
    (LSG.MEB.analyticAt_eval_of (f := fun v (s : ℂ) => liftV (u + s • w) v)
      (fun v => analyticAt_liftV_comp (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) v)
      Q).continuousAt

theorem continuousAt_sk (ch : ∀ k, Fin (B k).nT) (u w' w : Tan d₀ d₁ B) (k : Fin m) :
    ContinuousAt (fun s : ℂ => sk ch (u + s • w') w k) 0 := by
  have hz : Continuous fun s : ℂ => (u + s • w').2.2.1 k := by fun_prop
  have hθ : ContinuousAt (fun s : ℂ => (B k).base.θ ((u + s • w').2.2.1 k) ((B k).fc (ch k))) 0 :=
    ((continuous_apply ((B k).fc (ch k))).comp (LSG.MEB.AbBlock.continuous_θ (B k).base)).continuousAt.comp
      hz.continuousAt
  have hf : ContinuousAt (fun z => fderiv ℂ (B k).base.θ z) ((u + (0 : ℂ) • w').2.2.1 k) :=
    ((B k).base.θ_analytic _).fderiv.continuousAt
  have hd : ContinuousAt (fun s : ℂ =>
      fderiv ℂ (B k).base.θ ((u + s • w').2.2.1 k) (w.2.2.1 k) ((B k).fc (ch k))) 0 :=
    (continuous_apply ((B k).fc (ch k))).continuousAt.comp
      ((ContinuousLinearMap.apply ℂ _ (w.2.2.1 k)).continuous.continuousAt.comp
        (hf.comp hz.continuousAt))
  exact hθ.mul hd

/-- **`Dh` lowers the order by one** (multihomogeneous `P`, `w ∈ W`). -/
theorem ordAt_Dh {W : Submodule ℂ (Tan d₀ d₁ B)} (ch : ∀ k, Fin (B k).nT)
    (hch : ∀ k, (B k).fc (ch k) ∈ (B k).base.charts)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ} {u w : Tan d₀ d₁ B}
    (hw : w ∈ W) (h : OrdAt W P (n + 1) u) : OrdAt W (Dh ch w P) n u := by
  rw [ordAt_iff_one (isHomV_Dh ch w hP)]
  intro w' hw'
  have h1 := (ordAt_iff_one hP).mp h
  let H : ℂ × ℂ → ℂ := fun q => eval (liftV (u + (q.1 • w' + q.2 • w))) P
  have hHa : AnalyticOnNhd ℂ H univ := fun q₀ _ => by
    have haff : AnalyticAt ℂ (fun q : ℂ × ℂ => u + (q.1 • w' + q.2 • w)) q₀ :=
      analyticAt_const.add ((analyticAt_fst.smul analyticAt_const).add
        (analyticAt_snd.smul analyticAt_const))
    have hv : ∀ v, AnalyticAt ℂ (fun q : ℂ × ℂ => liftV (u + (q.1 • w' + q.2 • w)) v) q₀ :=
      fun v => analyticAt_liftV_comp haff v
    exact LSG.MEB.analyticAt_eval_of hv P
  have hH : H =O[𝓝 0] fun q => ‖q‖ ^ (n + 2) := by
    refine LSG.MEB.isBigO_of_diag hHa fun v k hk => ?_
    have hmem : v.1 • w' + v.2 • w ∈ W := W.add_mem (W.smul_mem _ hw') (W.smul_mem _ hw)
    have e : (fun r : ℂ => H (r • v)) = lineF P u (v.1 • w' + v.2 • w) 1 := by
      funext r
      simp only [H, lineF, liftZ_one, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]
    rw [e]
    exact h 1 _ hmem k (Nat.lt_succ_iff.mp hk)
  have hD : (fun s => iteratedDeriv 1 (fun r => H (s, r)) 0) =O[𝓝 0] fun s => ‖s‖ ^ (n + 1) := by
    simpa using LSG.MEB.isBigO_iteratedDeriv_snd (κ := 1) hHa hH (by omega)
  have hform : lineF (Dh ch w P) u w' 1 = fun s =>
      eval (liftV (u + s • w')) (Lc ch) * iteratedDeriv 1 (fun r => H (s, r)) 0 -
        (∑ k, eval (liftV (u + s • w')) (Lo ch k) * sk ch (u + s • w') w k * d k) *
          lineF P u w' 1 s := by
    funext s
    simp only [lineF_one]
    rw [eval_Dh_liftV ch hch hP, iteratedDeriv_one]
    congr 3
    funext r
    simp only [H, add_assoc]
  rw [hform]
  refine IsBigO.sub ?_ ?_
  · simpa using ((continuous_eval_liftV_affine (Lc ch) u w').continuousAt.isBigO_one ℝ).mul hD
  · have hE : ContinuousAt (fun s : ℂ => ∑ k, eval (liftV (u + s • w')) (Lo ch k) *
        sk ch (u + s • w') w k * d k) 0 := by
      refine tendsto_finsetSum _ fun k _ => ?_
      exact ((continuous_eval_liftV_affine _ u w').continuousAt.mul
        (continuousAt_sk ch u w' w k)).mul continuousAt_const
    have h2 := (h1 w' hw').trans (isLittleO_norm_pow_norm_pow (show n + 1 < n + 2 by omega)).isBigO
    simpa using (hE.isBigO_one ℝ).mul h2

/-- **`Dh` maps order `> n + 1` on `E` to order `> n`** (multihomogeneous elements). -/
theorem Dh_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} (ch : ∀ k, Fin (B k).nT)
    (hch : ∀ k, (B k).fc (ch k) ∈ (B k).base.charts) {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ} {E : Set (GPt d₀ d₁ B)} {w : Tan d₀ d₁ B} (hw : w ∈ W)
    (h : P ∈ ordIdealB W (n + 1) E) : Dh ch w P ∈ ordIdealB W n E :=
  fun u hu => ordAt_Dh ch hch hP hw (h u hu)

/-! ### Words -/

/-- All chart derivations, indexed by (fibre-index choice, direction). -/
noncomputable def Dmix (p : (∀ k, Fin (B k).nT) × Tan d₀ d₁ B) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Dh p.1 p.2

/-- The admissible indices: base charts of the blocks and directions in `W`. -/
def Wmix (W : Submodule ℂ (Tan d₀ d₁ B)) : Set ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B) :=
  {p | (∀ k, (B k).fc (p.1 k) ∈ (B k).base.charts) ∧ p.2 ∈ W}

/-- A word in the derivations `Dh` (applied right to left). -/
noncomputable def DhWord : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B) →
    MvPolynomial (Var d₀ d₁ B) ℂ → MvPolynomial (Var d₀ d₁ B) ℂ
  | [], P => P
  | p :: l, P => Dh p.1 p.2 (DhWord l P)

theorem DhWord_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)} :
    ∀ (l : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B)), (∀ p ∈ l, p ∈ Wmix W) →
      ∀ {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}, IsHomV P d → ∀ {n : ℕ},
        P ∈ ordIdealB W (n + l.length) E →
          DhWord l P ∈ ordIdealB W n E ∧ IsHomV (DhWord l P) (fun k => d k + 2 * l.length)
  | [], _, P, d, hP, n, h => ⟨by simpa [DhWord] using h, by simpa [DhWord] using hP⟩
  | p :: l, hl, P, d, hP, n, h => by
    have hl' : ∀ q ∈ l, q ∈ Wmix W := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨h1, h2⟩ := DhWord_mem_ordIdealB l hl' hP (n := n + 1) (by
      simpa [List.length_cons, add_assoc, add_comm 1] using h)
    have hp := hl p (List.mem_cons_self ..)
    refine ⟨Dh_mem_ordIdealB p.1 hp.1 h2 hp.2 h1, ?_⟩
    have := isHomV_Dh p.1 p.2 h2
    show IsHomV (Dh p.1 p.2 (DhWord l P)) _
    convert this using 1

/-- **The Taylor/word bridge** (for Wüstholz's lemma). -/
theorem DhWord_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)}
    {l : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B)} (hl : ∀ p ∈ l, p ∈ Wmix W)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {T : ℕ} (hlen : l.length ≤ T)
    (h : P ∈ ordIdealB W T E) : DhWord l P ∈ vanish E := by
  have h' : P ∈ ordIdealB W ((T - l.length) + l.length) E := by rwa [Nat.sub_add_cancel hlen]
  exact ordIdealB_le_vanish _ E (DhWord_mem_ordIdealB l hl hP h').1

theorem DL_Dmix_mem_FLE (l : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B)) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ StrongSix.M2.FLE ℂ blk D) :
    StrongSix.M2.DL Dmix l P ∈ StrongSix.M2.FLE ℂ blk (D + l.length • eTwos) := by
  induction l generalizing D P with
  | nil => simpa using hP
  | cons p l ih =>
    rw [StrongSix.M2.DL_cons]
    have := ih (Dh_mem_FLE p.1 p.2 hP)
    rwa [List.length_cons, add_smul, one_smul, add_comm (l.length • eTwos), ← add_assoc]

theorem DL_Dmix_mem_ordIdealB {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)} :
    ∀ (l : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B)), (∀ p ∈ l, p ∈ Wmix W) →
      ∀ {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}, IsHomV P d → ∀ {n : ℕ},
        P ∈ ordIdealB W (n + l.length) E → StrongSix.M2.DL Dmix l P ∈ ordIdealB W n E
  | [], _, P, d, hP, n, h => by simpa using h
  | p :: l, hl, P, d, hP, n, h => by
    rw [StrongSix.M2.DL_cons]
    have hp := hl p (List.mem_cons_self ..)
    refine DL_Dmix_mem_ordIdealB l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (isHomV_Dh p.1 p.2 hP) (Dh_mem_ordIdealB p.1 hp.1 hP hp.2 ?_)
    simpa [List.length_cons, add_assoc, add_comm 1] using h

/-- **The word bridge in StrongSix's form**: words of length `≤ T` in `Dmix` over `Wmix W` map a
multihomogeneous element of `ordIdealB W T E` into `vanish E`. -/
theorem DL_Dmix_mem_vanish {W : Submodule ℂ (Tan d₀ d₁ B)} {E : Set (GPt d₀ d₁ B)}
    {l : List ((∀ k, Fin (B k).nT) × Tan d₀ d₁ B)} (hl : ∀ p ∈ l, p ∈ Wmix W)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {T : ℕ} (hlen : l.length ≤ T)
    (h : P ∈ ordIdealB W T E) : StrongSix.M2.DL Dmix l P ∈ vanish E := by
  have h' : P ∈ ordIdealB W ((T - l.length) + l.length) E := by rwa [Nat.sub_add_cancel hlen]
  exact ordIdealB_le_vanish _ E (DL_Dmix_mem_ordIdealB l hl hP h')

end LSG.MEBV
