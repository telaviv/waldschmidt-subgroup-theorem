/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.OrdAn
import LSG.MEBV.Lift

/-!
# The analytic order of vanishing on `G̃` (M2.5, β)

The `VBlock` analogue of `LSG.MEB.Ord`. Block `k` of a cone point is its `X`- and `T`-coordinates together, and
the lift of block `k` is `lift_k(z_k, w_k)`.

* **Bounded scalars** (`isBigO_eval_blockwise`, from MEB's `exists_bound_smul`): if two families of cone points
  differ blockwise by scalars and are continuous with nonzero blocks at the base point, a multihomogeneous `P` takes
  `O`-comparable values. Degenerate laws only make the scalar small.
* `lineF P u w μ s = P(liftZ (u + s w) μ)`, analytic in `s`.
* **`OrdAt W P n u`**: order `> n` along `W` at the lift `u`, at every block scaling `μ`; `ordAt_iff_isBigO`.
* **`ordIdealB W n E`**: the ideal of polynomials of order `> n` at every lift of every point of `E`.
  `IGsem_le_ordIdealB`, `ordIdealB_le_vanish`, `ordIdealB_anti`.
* `mem_PerG_of_expG_eq` (the kernel of `expG`), `liftG g` (the canonical lift, `coords g 1 = liftV (liftG g)`).
* **Lift independence** (`ordAt_add_per`, `ordGtV_iff`, `mem_ordIdealB_of`): for multihomogeneous `P`, the frozen
  `OrdGtV` (one lift, `μ = 1`) is equivalent to `OrdAt` at every lift.
-/

open MvPolynomial Asymptotics Filter Topology Set

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Scaled lifts -/

/-- The block-`k` part of a cone point. -/
def blkPt (x : Var d₀ d₁ B → ℂ) (k : Fin m) : (B k).Idx → ℂ := fun b => x (.e k b)

theorem liftZ_mul_eq (u : Tan d₀ d₁ B) (μ c : Fin m → ℂ) :
    liftZ u (μ * c) = fun v => (∏ k, c k ^ wV v k) * liftZ u μ v := by
  funext v
  cases v with
  | x i => simp [liftZ, wV]
  | y j => simp [liftZ, wV]
  | z j => simp [liftZ, wV]
  | e k b =>
    simp only [liftZ, wV, Pi.single_apply, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
      Finset.mem_univ, ite_true, Pi.mul_apply]
    ring

theorem eval_liftZ_mul {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    (u : Tan d₀ d₁ B) (μ c : Fin m → ℂ) :
    eval (liftZ u (μ * c)) P = (∏ k, c k ^ d k) * eval (liftZ u μ) P := by
  rw [liftZ_mul_eq, LSG.MEB.eval_scale wV c _ (isHomV_iff_wV.mp hP)]

/-- **Blockwise comparison.** Let `F x'` be a blockwise rescaling of `G x'` near `x`, with `F, G` continuous at
`x` on the blocks and the blocks of `G x` nonzero. Then `P ∘ F = O(P ∘ G)` for multihomogeneous `P`. -/
theorem isBigO_eval_blockwise {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {X' : Type*} [TopologicalSpace X'] {x : X'} (F G : X' → Var d₀ d₁ B → ℂ)
    (hFc : ∀ k, ContinuousAt (fun x' => blkPt (F x') k) x)
    (hGc : ∀ k, ContinuousAt (fun x' => blkPt (G x') k) x) (hG0 : ∀ k, blkPt (G x) k ≠ 0)
    (hrel : ∀ᶠ x' in 𝓝 x, ∃ c : Fin m → ℂ, F x' = fun v => (∏ k, c k ^ wV v k) * G x' v) :
    (fun x' => eval (F x') P) =O[𝓝 x] fun x' => eval (G x') P := by
  choose M hM using fun k => LSG.MEB.exists_bound_smul (hFc k) (hGc k) (hG0 k)
  have hall : ∀ᶠ x' in 𝓝 x, ∀ k, ∀ c : ℂ, blkPt (F x') k = c • blkPt (G x') k → ‖c‖ ≤ M k :=
    eventually_all.mpr hM
  refine IsBigO.of_bound (∏ k, M k ^ d k) ?_
  filter_upwards [hall, hrel] with x' hb hr
  obtain ⟨c, hc⟩ := hr
  have hck : ∀ k, ‖c k‖ ≤ M k := fun k => by
    refine hb k (c k) (funext fun b => ?_)
    simp only [blkPt, hc, Pi.smul_apply, smul_eq_mul]
    simp [wV, Pi.single_apply, Finset.prod_ite_eq']
  rw [hc, LSG.MEB.eval_scale wV c _ (isHomV_iff_wV.mp hP), norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hck k) _

/-! ### Line functions and the order -/

/-- The line function `s ↦ P(liftZ (u + s w) μ)`. -/
noncomputable def lineF (P : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) (μ : Fin m → ℂ) (s : ℂ) :
    ℂ :=
  eval (liftZ (u + s • w) μ) P

theorem analyticAt_lineF (P : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) (μ : Fin m → ℂ)
    (s₀ : ℂ) : AnalyticAt ℂ (lineF P u w μ) s₀ :=
  (analyticAt_eval_liftZ P (u + s₀ • w, μ)).comp (f := fun s : ℂ => ((u + s • w, μ) : LZ d₀ d₁ B))
    (by fun_prop)

variable (W : Submodule ℂ (Tan d₀ d₁ B))

/-- **Order `> n` along `W` at the lift `u`**, at every block scaling. -/
def OrdAt (P : MvPolynomial (Var d₀ d₁ B) ℂ) (n : ℕ) (u : Tan d₀ d₁ B) : Prop :=
  ∀ μ : Fin m → ℂ, ∀ w ∈ W, ∀ k ≤ n, iteratedDeriv k (lineF P u w μ) 0 = 0

variable {W}

theorem ordAt_iff_isBigO {P : MvPolynomial (Var d₀ d₁ B) ℂ} {n : ℕ} {u : Tan d₀ d₁ B} :
    OrdAt W P n u ↔ ∀ μ, ∀ w ∈ W, lineF P u w μ =O[𝓝 0] fun s => ‖s‖ ^ (n + 1) := by
  refine forall_congr' fun μ => forall₂_congr fun w _ => ?_
  rw [← LSG.MEB.isBigO_pow_iff (analyticAt_lineF P u w μ 0)]
  exact ⟨fun h i hi => h i (Nat.lt_succ_iff.mp hi), fun h i hi => h i (Nat.lt_succ_iff.mpr hi)⟩

variable (W) in
/-- **The order ideal**: order `> n` along `W` at every lift (and every scaling) of every point of `E`. -/
noncomputable def ordIdealB (n : ℕ) (E : Set (GPt d₀ d₁ B)) : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) where
  carrier := {P | ∀ u, expG d₀ d₁ B u ∈ E → OrdAt W P n u}
  add_mem' {P Q} hP hQ u hu := by
    have hP' := ordAt_iff_isBigO.mp (hP u hu)
    have hQ' := ordAt_iff_isBigO.mp (hQ u hu)
    rw [ordAt_iff_isBigO]
    intro μ w hw
    have : lineF (P + Q) u w μ = lineF P u w μ + lineF Q u w μ := by
      funext s; simp [lineF]
    rw [this]
    exact (hP' μ w hw).add (hQ' μ w hw)
  zero_mem' u _ := by
    rw [ordAt_iff_isBigO]
    intro μ w _
    have : lineF (0 : MvPolynomial (Var d₀ d₁ B) ℂ) u w μ = 0 := by funext s; simp [lineF]
    rw [this]; exact isBigO_zero _ _
  smul_mem' R {P} hP u hu := by
    have hP' := ordAt_iff_isBigO.mp (hP u hu)
    rw [ordAt_iff_isBigO]
    intro μ w hw
    have : lineF (R • P) u w μ = fun s => lineF R u w μ s * lineF P u w μ s := by
      funext s; simp [lineF]
    rw [this]
    simpa using ((analyticAt_lineF R u w μ 0).continuousAt.isBigO_one ℝ).mul (hP' μ w hw)

theorem mem_ordIdealB {n : ℕ} {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ ordIdealB W n E ↔ ∀ u, expG d₀ d₁ B u ∈ E → OrdAt W P n u := Iff.rfl

theorem ordIdealB_anti {n n' : ℕ} (h : n ≤ n') (E : Set (GPt d₀ d₁ B)) :
    ordIdealB W n' E ≤ ordIdealB W n E :=
  fun _ hP u hu μ w hw k hk => hP u hu μ w hw k (hk.trans h)

theorem ordIdealB_mono_set {n : ℕ} {E E' : Set (GPt d₀ d₁ B)} (h : E ⊆ E') :
    ordIdealB W n E' ≤ ordIdealB W n E :=
  fun _ hP u hu => hP u (h hu)

theorem IGsem_le_ordIdealB (n : ℕ) (E : Set (GPt d₀ d₁ B)) : IGsem d₀ d₁ B ≤ ordIdealB W n E := by
  intro P hP u _
  rw [ordAt_iff_isBigO]
  intro μ w _
  have : lineF P u w μ = 0 := by
    funext s; exact mem_IGsem_iff_liftZ.mp hP _ _
  rw [this]; exact isBigO_zero _ _

/-- Cone representatives through the lift. -/
theorem coords_eq_liftZ (u : Tan d₀ d₁ B) (lam : Fin m → ℂˣ) :
    ∃ μ : Fin m → ℂ, (∀ k, μ k ≠ 0) ∧ coords (expG d₀ d₁ B u) lam = liftZ u μ := by
  obtain ⟨lam₀, h0⟩ := coords_expG u
  refine ⟨fun k => (lam k : ℂ) / lam₀ k, fun k => div_ne_zero (Units.ne_zero _) (Units.ne_zero _), ?_⟩
  rw [liftZ_eq_coordsZ h0, coords_eq_coordsZ]
  congr 1
  funext k
  field_simp

theorem ordIdealB_le_vanish (n : ℕ) (E : Set (GPt d₀ d₁ B)) : ordIdealB W n E ≤ vanish E := by
  intro P hP
  refine mem_vanish.mpr fun g hg lam => ?_
  obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) g
  obtain ⟨μ, -, hμ⟩ := coords_eq_liftZ u lam
  have := hP u hg μ 0 W.zero_mem 0 (Nat.zero_le _)
  simpa [lineF, hμ] using this

/-! ### The kernel of `expG` and the canonical lift -/

theorem mem_PerG_of_expG_eq {u u' : Tan d₀ d₁ B} (h : expG d₀ d₁ B u = expG d₀ d₁ B u') :
    u' - u ∈ PerG d₀ d₁ B := by
  have h0 : expG d₀ d₁ B (u' - u) = 0 := by rw [map_sub, h, sub_self]
  rw [expG_apply, expGf] at h0
  refine ⟨congrArg Prod.fst h0, fun j => ?_, fun k => ?_⟩
  · have h1 := congrArg (fun g : GPt d₀ d₁ B => ((Additive.toMul g.2.1 j : ℂˣ) : ℂ)) h0
    simp only [toMul_ofMul, expU, Units.val_mk0] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (by simpa using h1)
    refine ⟨n, ?_⟩
    change u'.2.1 j - u.2.1 j = _
    rw [hn]; ring
  · have h1 : (QuotientAddGroup.mk ((u' - u).blkV k) : (B k).Pt) = 0 :=
      congrArg (fun g : GPt d₀ d₁ B => g.2.2 k) h0
    exact (QuotientAddGroup.eq_zero_iff _).mp h1

/-- The canonical lift of a point: `(x, log y, out p)`. -/
noncomputable def liftG (g : GPt d₀ d₁ B) : Tan d₀ d₁ B :=
  (g.1, fun j => Complex.log ((g.ym j : ℂˣ) : ℂ), fun k => (Quotient.out (g.2.2 k)).1,
    fun k => (Quotient.out (g.2.2 k)).2)

theorem liftG_blkV (g : GPt d₀ d₁ B) (k : Fin m) : (liftG g).blkV k = Quotient.out (g.2.2 k) := rfl

theorem expG_liftG (g : GPt d₀ d₁ B) : expG d₀ d₁ B (liftG g) = g := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change Additive.ofMul _ = g.2.1
    apply Additive.toMul.injective
    funext j
    exact Units.ext (by simp [expU, liftG, GPt.ym, Complex.exp_log (Units.ne_zero _)])
  · funext k
    exact Quotient.out_eq _

theorem coords_one_eq_liftV (g : GPt d₀ d₁ B) : coords g 1 = liftV (liftG g) := by
  funext v
  cases v with
  | x i => rfl
  | y j => simp [coords, liftV, liftG, Complex.exp_log (Units.ne_zero _)]
  | z j =>
    simp [coords, liftV, liftG, Complex.exp_neg, Complex.exp_log (Units.ne_zero _)]
  | e k c => simp [coords, liftV, liftG_blkV, VBlock.rep]

/-! ### Lift independence -/

theorem liftZ_add_per (u : Tan d₀ d₁ B) {ω : Tan d₀ d₁ B} (hω : ω ∈ PerG d₀ d₁ B) (μ c : Fin m → ℂ)
    (hc : ∀ k, (B k).lift (u.blkV k + ω.blkV k) = c k • (B k).lift (u.blkV k)) :
    liftZ (u + ω) μ = liftZ u (μ * c) := by
  obtain ⟨h1, h2, -⟩ := hω
  funext v
  cases v with
  | x i => simp [liftZ, h1]
  | y j =>
    obtain ⟨n, hn⟩ := h2 j
    have : Complex.exp (ω.2.1 j) = 1 := by
      rw [hn, show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    simp [liftZ, Complex.exp_add, this]
  | z j =>
    obtain ⟨n, hn⟩ := h2 j
    have : Complex.exp (-ω.2.1 j) = 1 := by
      rw [hn, show -(2 * Real.pi * Complex.I * n : ℂ) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [liftZ, Complex.exp_add, this]
  | e k b =>
    have := congrFun (hc k) b
    simp only [liftZ, Tan.blkV_add, Pi.mul_apply] at this ⊢
    rw [this, Pi.smul_apply, smul_eq_mul]; ring

theorem blkPt_liftZ (a : Tan d₀ d₁ B) (μ : Fin m → ℂ) (k : Fin m) :
    blkPt (liftZ a μ) k = μ k • (B k).lift (a.blkV k) := by
  funext b; simp [blkPt, liftZ]

theorem continuous_blkV (k : Fin m) : Continuous fun u : Tan d₀ d₁ B => u.blkV k := by
  unfold Tan.blkV; fun_prop

theorem continuous_blkPt_liftZ {X' : Type*} [TopologicalSpace X'] {a : X' → Tan d₀ d₁ B}
    (ha : Continuous a) (μ : Fin m → ℂ) (k : Fin m) : Continuous fun x' => blkPt (liftZ (a x') μ) k := by
  simp_rw [blkPt_liftZ]
  exact (continuous_const (y := μ k)).smul ((B k).continuous_lift.comp ((continuous_blkV k).comp ha))

theorem blkPt_liftZ_one_ne (a : Tan d₀ d₁ B) (k : Fin m) : blkPt (liftZ a 1) k ≠ 0 := by
  rw [blkPt_liftZ]; simpa using (B k).lift_ne_zero _

theorem lineF_eq_mul {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    (u w : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    lineF P u w μ = fun s => (∏ k, μ k ^ d k) * lineF P u w 1 s := by
  funext s
  simp only [lineF]
  rw [← eval_liftZ_mul hP, one_mul]

/-- For multihomogeneous `P` only the scaling `μ = 1` matters. -/
theorem ordAt_iff_one {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ}
    {u : Tan d₀ d₁ B} :
    OrdAt W P n u ↔ ∀ w ∈ W, lineF P u w 1 =O[𝓝 0] fun s => ‖s‖ ^ (n + 1) := by
  rw [ordAt_iff_isBigO]
  refine ⟨fun h w hw => h 1 w hw, fun h μ w hw => ?_⟩
  rw [lineF_eq_mul hP]
  exact (h w hw).const_mul_left _

theorem lineF_one (P : MvPolynomial (Var d₀ d₁ B) ℂ) (u w : Tan d₀ d₁ B) :
    lineF P u w 1 = fun s => eval (liftV (u + s • w)) P := by
  funext s; simp [lineF, liftZ_one]

/-- **Changing the lift by a period** (multihomogeneous `P`). -/
theorem ordAt_add_per {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ}
    {u ω : Tan d₀ d₁ B} (hω : ω ∈ PerG d₀ d₁ B) (h : OrdAt W P n u) : OrdAt W P n (u + ω) := by
  rw [ordAt_iff_one hP] at h ⊢
  intro w hw
  refine IsBigO.trans ?_ (h w hw)
  refine isBigO_eval_blockwise hP (x := (0 : ℂ)) (fun s => liftZ (u + ω + s • w) 1)
    (fun s => liftZ (u + s • w) 1) (fun k => ?_) (fun k => ?_) (fun k => blkPt_liftZ_one_ne _ k)
    (Eventually.of_forall fun s => ?_)
  · exact (continuous_blkPt_liftZ (by fun_prop) 1 k).continuousAt
  · exact (continuous_blkPt_liftZ (by fun_prop) 1 k).continuousAt
  · choose c hc0 hc using fun k => (B k).lift_add_perV (hω.2.2 k) ((u + s • w).blkV k)
    refine ⟨c, ?_⟩
    rw [show u + ω + s • w = (u + s • w) + ω by abel, liftZ_add_per _ hω 1 c hc, liftZ_mul_eq]

/-- **Lift independence**: for multihomogeneous `P`, `OrdGtV` (one lift) is `OrdAt` at every lift. -/
theorem ordGtV_iff {P : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) {n : ℕ}
    {p : GPt d₀ d₁ B} : OrdGtV W P n p ↔ ∀ u, expG d₀ d₁ B u = p → OrdAt W P n u := by
  constructor
  · rintro ⟨u₀, hu₀, h₀⟩ u hu
    have h0' : OrdAt W P n u₀ := by
      rw [ordAt_iff_one hP]
      intro w hw
      rw [lineF_one, ← LSG.MEB.isBigO_pow_iff]
      · exact fun i hi => h₀ w hw i (Nat.lt_succ_iff.mp hi)
      · simpa [lineF_one] using analyticAt_lineF P u₀ w 1 0
    have := ordAt_add_per hP (mem_PerG_of_expG_eq (hu₀.trans hu.symm)) h0'
    rwa [add_sub_cancel] at this
  · intro h
    obtain ⟨u, hu⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) p
    refine ⟨u, hu, fun w hw k hk => ?_⟩
    simpa [lineF_one] using h u hu 1 w hw k hk

theorem mem_ordIdealB_of {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d) {n : ℕ}
    {E : Set (GPt d₀ d₁ B)} (h : ∀ g ∈ E, OrdGtV W Q n g) : Q ∈ ordIdealB W n E :=
  fun u hu => (ordGtV_iff hQ).mp (h _ hu) u rfl

theorem ordGtV_of_mem_ordIdealB {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {n : ℕ} {E : Set (GPt d₀ d₁ B)}
    (hQ : Q ∈ ordIdealB W n E) {g : GPt d₀ d₁ B} (hg : g ∈ E) : OrdGtV W Q n g := by
  obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) g
  refine ⟨u, rfl, fun w hw k hk => ?_⟩
  simpa [lineF_one] using hQ u hg 1 w hw k hk

end LSG.MEBV
