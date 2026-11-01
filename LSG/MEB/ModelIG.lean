/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Model

/-!
# The ideals `IGsem` and `IGexp` of `G` (A4.2, α)

* **`liftZ u μ`**: the analytic lift `(u₀, e^{u₁}, e^{−u₁}, μ_k θ_k(u_{2,k}))`, scalars `μ` allowed to
  vanish; `liftZ_analyticAt` (in `(u, μ)` jointly); **`mem_IGsem_iff_liftZ`**:
  `P ∈ IGsem ↔ P ∘ liftZ ≡ 0`.
* **`IGsem_isPrime`**: `IGsem` is prime, by the identity theorem on the connected space
  `Tan × ℂ^m` (`STAGE_A4` §1.2; the argument of `ME.vanish_H0_isPrime`, now global).
* `blockI k = (gens_k) ⊆ ℂ[X_c : c < N_k]`, `YZ j`, **`IGexp = (Y_j Z_j − 1)_j + Σ_k rename_k (blockI k)`**
  (the explicit ideal, in the shape of `StrongSix.M2.bezout_blocks`).
* `IGexp_le_vanish`: `IGexp ⊆ I(E)` for every `E` (`θ_model` and homogeneity of the generators).
* **`exists_coordsZ_of_IGexp`**: every zero of `IGexp` is `coordsZ g ν` (the field `surj`).
* **`rad_IGexp`**: `IGexp.radical = IGsem` (Nullstellensatz + `surj` + density), and
  `IGsem_eq_vanish_zeroLocus`.
-/

open MvPolynomial Filter Topology

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Homogeneous scaling -/

/-- `Q(c • x) = c^d Q(x)` for `Q` homogeneous of degree `d`. -/
theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {Q : MvPolynomial σ ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) (c : ℂ) (x : σ → ℂ) : eval (c • x) Q = c ^ d * eval x Q := by
  have := eval_scale (κ := Unit) (fun _ _ => 1) (fun _ => c) x (Q := Q) (d := fun _ => d)
    (fun s hs => funext fun _ => by
      rw [← hQ hs, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
        Finset.sum_apply]; rfl)
  simp only [Finset.univ_unique, Finset.prod_singleton, pow_one] at this
  rw [← this]; rfl

/-! ### The analytic lift with scalars -/

/-- **The lift with scalars** `(u₀, e^{u₁}, e^{−u₁}, μ_k θ_k(u_{2,k}))`. -/
noncomputable def liftZ (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => u.1 i
  | .y j => Complex.exp (u.2.1 j)
  | .z j => Complex.exp (-u.2.1 j)
  | .e k c => μ k * (B k).θ (u.2.2 k) c

theorem liftZ_one (u : Tan d₀ d₁ B) : liftZ u 1 = liftB u := by
  funext v; cases v <;> simp [liftZ, liftB]

theorem analyticAt_eval_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : σ → E → ℂ} {p : E} (hf : ∀ v, AnalyticAt ℂ (f v) p) (Q : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun y => eval (fun v => f v y) Q) p := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (hf v)

theorem continuousAt_eval_of {X σ : Type*} [TopologicalSpace X] {f : σ → X → ℂ} {x : X}
    (hf : ∀ v, ContinuousAt (f v) x) (Q : MvPolynomial σ ℂ) :
    ContinuousAt (fun y => eval (fun v => f v y) Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact continuousAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (hf v)

/-- A coordinate of `θ` is analytic. -/
theorem AbBlock.analyticAt_θ_apply (b : AbBlock) (z : Fin b.g → ℂ) (c : Fin b.N) :
    AnalyticAt ℂ (fun w => b.θ w c) z :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin b.N => ℂ) c).analyticAt _).comp
    (b.θ_analytic z)

variable (d₀ d₁ B) in
/-- The parameter space `Tan × ℂ^m` of `liftZ`. -/
abbrev LZ : Type := Tan d₀ d₁ B × (Fin m → ℂ)

/-- The coordinate projections of `LZ` as continuous linear maps. -/
noncomputable def LZx (i : Fin d₀) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℂ _ _).comp
    (ContinuousLinearMap.fst ℂ _ _))

noncomputable def LZy (j : Fin d₁) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)))

noncomputable def LZe (k : Fin m) : LZ d₀ d₁ B →L[ℂ] (Fin (B k).g → ℂ) :=
  (ContinuousLinearMap.proj (φ := fun k => Fin (B k).g → ℂ) k).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)))

noncomputable def LZμ (k : Fin m) : LZ d₀ d₁ B →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℂ _ _)

/-- **The lift is analytic** in `(u, μ)`. -/
theorem liftZ_analyticAt (v : Var d₀ d₁ B) (p : LZ d₀ d₁ B) :
    AnalyticAt ℂ (fun q : LZ d₀ d₁ B => liftZ q.1 q.2 v) p := by
  cases v with
  | x i => exact (LZx i).analyticAt p
  | y j => exact analyticAt_cexp.comp ((LZy j).analyticAt p)
  | z j => exact analyticAt_cexp.comp ((LZy j).analyticAt p).neg
  | e k c =>
    exact ((LZμ k).analyticAt p).mul (((B k).analyticAt_θ_apply _ c).comp ((LZe k).analyticAt p))

theorem analyticAt_eval_liftZ (P : MvPolynomial (Var d₀ d₁ B) ℂ) (p : LZ d₀ d₁ B) :
    AnalyticAt ℂ (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) P) p :=
  analyticAt_eval_of (f := fun v (q : LZ d₀ d₁ B) => liftZ q.1 q.2 v)
    (fun v => liftZ_analyticAt v p) P

/-- `liftZ` in terms of `coordsZ`, given the scalings of `coords_expG`. -/
theorem liftZ_eq_coordsZ {u : Tan d₀ d₁ B} {lam₀ : Fin m → ℂˣ}
    (h : coords (expG d₀ d₁ B u) lam₀ = liftB u) (μ : Fin m → ℂ) :
    liftZ u μ = coordsZ (expG d₀ d₁ B u) fun k => μ k * lam₀ k := by
  funext v
  have hv := congrFun h v
  cases v with
  | x i => exact hv.symm
  | y j => exact hv.symm
  | z j => exact hv.symm
  | e k c =>
    simp only [coords, liftB] at hv
    simp only [liftZ, coordsZ, ← hv]
    ring

/-- **`IGsem` through the lift.** -/
theorem mem_IGsem_iff_liftZ {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ IGsem d₀ d₁ B ↔ ∀ u μ, eval (liftZ u μ) P = 0 := by
  constructor
  · intro hP u μ
    obtain ⟨lam₀, h⟩ := coords_expG u
    rw [liftZ_eq_coordsZ h]
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ (Set.mem_univ _) lam) _
  · intro h
    refine mem_vanish.mpr fun g _ lam => ?_
    obtain ⟨u, rfl⟩ := expG_surjective (d₀ := d₀) (d₁ := d₁) (B := B) g
    obtain ⟨lam₀, h0⟩ := coords_expG u
    have : coords (expG d₀ d₁ B u) lam = liftZ u fun k => (lam k : ℂ) / lam₀ k := by
      rw [liftZ_eq_coordsZ h0, coords_eq_coordsZ]
      congr 1
      funext k
      field_simp
    rw [this]
    exact h _ _

/-- **`IGsem` is prime** (identity theorem on the connected space `Tan × ℂ^m`). -/
theorem IGsem_isPrime : (IGsem d₀ d₁ B).IsPrime := by
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ IGsem d₀ d₁ B := htop ▸ Submodule.mem_top
    have := mem_IGsem_iff_liftZ.mp h1 0 0
    rw [map_one] at this
    exact one_ne_zero this
  have hfh : ∀ q : LZ d₀ d₁ B, eval (liftZ q.1 q.2) P * eval (liftZ q.1 q.2) Q = 0 := fun q => by
    have := mem_IGsem_iff_liftZ.mp hPQ q.1 q.2
    rwa [map_mul] at this
  by_cases hP : P ∈ IGsem d₀ d₁ B
  · exact Or.inl hP
  right
  have : ∃ q : LZ d₀ d₁ B, eval (liftZ q.1 q.2) P ≠ 0 := by
    by_contra hcon
    exact hP (mem_IGsem_iff_liftZ.mpr fun u μ => not_not.mp fun h => hcon ⟨(u, μ), h⟩)
  obtain ⟨q₀, hq₀⟩ := this
  have hev : (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) =ᶠ[𝓝 q₀] 0 := by
    filter_upwards [(analyticAt_eval_liftZ P q₀).continuousAt.eventually_ne hq₀] with q hq
    exact (mul_eq_zero.mp (hfh q)).resolve_left hq
  have han : AnalyticOnNhd ℂ (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) Set.univ :=
    fun q _ => analyticAt_eval_liftZ Q q
  have hpc : IsPreconnected (Set.univ : Set (LZ d₀ d₁ B)) := (convex_univ (𝕜 := ℝ)).isPreconnected
  have hzero : Set.EqOn (fun q : LZ d₀ d₁ B => eval (liftZ q.1 q.2) Q) 0 Set.univ :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc (Set.mem_univ q₀) hev
  refine mem_IGsem_iff_liftZ.mpr fun u μ => ?_
  have := hzero (Set.mem_univ (u, μ))
  simpa using this

theorem IGsem_ne_top : IGsem d₀ d₁ B ≠ ⊤ := (IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)).ne_top

/-! ### The explicit ideal `IGexp` -/

/-- The explicit ideal of the `k`-th block, in `ℂ[X_c : c < N_k]`. -/
noncomputable def AbBlock.blockI (b : AbBlock) : Ideal (MvPolynomial (Fin b.N) ℂ) :=
  Ideal.span {Q | Q ∈ b.gens}

variable (d₀ B) in
/-- `Y_j Z_j − 1`. -/
noncomputable def YZ (j : Fin d₁) : MvPolynomial (Var d₀ d₁ B) ℂ := X (.y j) * X (.z j) - 1

variable (d₀ d₁ B) in
/-- The `G_m` relations as a list. -/
noncomputable def lYZ : List (MvPolynomial (Var d₀ d₁ B) ℂ) := List.ofFn (YZ d₀ B)

theorem lYZ_length : (lYZ d₀ d₁ B).length = d₁ := by simp [lYZ]

variable (d₀ d₁ B) in
/-- **The explicit ideal of `G`**: `(Y_j Z_j − 1)_j + Σ_k rename_k (gens_k)`. -/
noncomputable def IGexp : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Ideal.ofList (lYZ d₀ d₁ B) ⊔ ⨆ k, ((B k).blockI).map (rename (Var.e (d₀ := d₀) (d₁ := d₁) k))

theorem YZ_mem_IGexp (j : Fin d₁) : YZ d₀ B j ∈ IGexp d₀ d₁ B :=
  Ideal.mem_sup_left (Ideal.subset_span (by simp [lYZ]))

theorem rename_mem_IGexp (k : Fin m) {Q : MvPolynomial (Fin (B k).N) ℂ} (hQ : Q ∈ (B k).gens) :
    rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q ∈ IGexp d₀ d₁ B :=
  Ideal.mem_sup_right (Ideal.mem_iSup_of_mem k (Ideal.mem_map_of_mem _ (Ideal.subset_span hQ)))

/-- `IGexp` as the span of its generators. -/
theorem IGexp_eq_span : IGexp d₀ d₁ B = Ideal.span (Set.range (YZ d₀ B) ∪
    {P | ∃ k, ∃ Q ∈ (B k).gens, P = rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q}) := by
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun k => ?_)
    · rw [Ideal.ofList, Ideal.span_le]
      intro P hP
      simp only [lYZ, List.mem_ofFn, Set.mem_setOf_eq] at hP
      obtain ⟨j, rfl⟩ := hP
      exact Ideal.subset_span (Or.inl ⟨j, rfl⟩)
    · rw [AbBlock.blockI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨Q, hQ, rfl⟩
      exact Ideal.subset_span (Or.inr ⟨k, Q, hQ, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨k, Q, hQ, rfl⟩)
    · exact YZ_mem_IGexp j
    · exact rename_mem_IGexp k hQ

/-- An ideal whose generators vanish at `x` vanishes at `x`. -/
theorem eval_eq_zero_of_span {σ : Type*} {s : Set (MvPolynomial σ ℂ)} {x : σ → ℂ}
    (hs : ∀ P ∈ s, eval x P = 0) {P : MvPolynomial σ ℂ} (hP : P ∈ Ideal.span s) :
    eval x P = 0 := by
  have : Ideal.span s ≤ RingHom.ker (eval x) := Ideal.span_le.mpr fun P hP => hs P hP
  exact this hP

theorem eval_rename_e (k : Fin m) (x : Var d₀ d₁ B → ℂ) (Q : MvPolynomial (Fin (B k).N) ℂ) :
    eval x (rename (Var.e (d₀ := d₀) (d₁ := d₁) k) Q) = eval (fun c => x (.e k c)) Q := by
  rw [eval_rename]; rfl

/-- **`IGexp ⊆ I(E)`** for every set of points. -/
theorem IGexp_le_vanish (E : Set (GPt d₀ d₁ B)) : IGexp d₀ d₁ B ≤ vanish E := by
  rw [IGexp_eq_span, Ideal.span_le]
  rintro _ (⟨j, rfl⟩ | ⟨k, Q, hQ, rfl⟩) <;> refine mem_vanish.mpr fun g _ lam => ?_
  · simp [YZ]
  · rw [eval_rename_e]
    obtain ⟨d, -, hd⟩ := (B k).gens_hom Q hQ
    have : (fun c => coords g lam (.e k c)) = (lam k : ℂ) • (B k).rep (g.2.2 k) := by
      funext c; simp
    rw [this, eval_smul_of_isHomogeneous hd, AbBlock.rep, (B k).θ_model _ Q hQ, mul_zero]

theorem IGexp_le_IGsem : IGexp d₀ d₁ B ≤ IGsem d₀ d₁ B := IGexp_le_vanish _

/-- **Every zero of `IGexp` is a cone point** (the field `surj`). -/
theorem exists_coordsZ_of_IGexp {x : Var d₀ d₁ B → ℂ} (hx : ∀ P ∈ IGexp d₀ d₁ B, eval x P = 0) :
    ∃ (g : GPt d₀ d₁ B) (ν : Fin m → ℂ), x = coordsZ g ν := by
  classical
  have hyz : ∀ j, x (.y j) * x (.z j) = 1 := fun j => by
    have := hx _ (YZ_mem_IGexp j)
    simpa [YZ, sub_eq_zero] using this
  have hblk : ∀ k, ∃ (p : (B k).Pt) (ν : ℂ), (fun c => x (.e k c)) = ν • (B k).rep p := by
    intro k
    by_cases h0 : (fun c => x (.e k c)) = 0
    · exact ⟨0, 0, by rw [h0, zero_smul]⟩
    have hz : ∀ Q ∈ (B k).gens, eval (fun c => x (.e k c)) Q = 0 := fun Q hQ => by
      rw [← eval_rename_e (d₀ := d₀) (d₁ := d₁)]; exact hx _ (rename_mem_IGexp k hQ)
    obtain ⟨z, c, hc⟩ := (B k).surj _ h0 hz
    obtain ⟨c', hc', h'⟩ := (B k).rep_mk z
    refine ⟨QuotientAddGroup.mk z, c / c', ?_⟩
    rw [hc, h', smul_smul, div_mul_cancel₀ _ hc']
  choose p ν hpν using hblk
  refine ⟨(fun i => x (.x i), Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j), p), ν, ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j =>
    simp only [coordsZ, GPt.ym]
    have : x (.z j) = (x (.y j))⁻¹ := (eq_inv_of_mul_eq_one_right (hyz j))
    rw [this]; simp
  | e k c => exact congrFun (hpν k) c

/-- **`rad IGexp = IGsem`** (Hilbert's Nullstellensatz, `surj`, density). -/
theorem rad_IGexp : (IGexp d₀ d₁ B).radical = IGsem d₀ d₁ B := by
  apply le_antisymm
  · rw [← (IGsem_isPrime (d₀ := d₀) (d₁ := d₁) (B := B)).radical]
    exact Ideal.radical_mono IGexp_le_IGsem
  · intro P hP
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    obtain ⟨g, ν, rfl⟩ := exists_coordsZ_of_IGexp fun P hP => hx P hP
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP g (Set.mem_univ _) lam) ν

theorem IGexp_ne_top : IGexp d₀ d₁ B ≠ ⊤ :=
  ne_top_of_le_ne_top IGsem_ne_top IGexp_le_IGsem

/-- `IGsem` is the vanishing ideal of the cone points: a polynomial vanishing at every
`coordsZ g ν` lies in `IGsem` (trivially), and conversely. -/
theorem mem_IGsem_iff_coordsZ {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ IGsem d₀ d₁ B ↔ ∀ g ν, eval (coordsZ g ν) P = 0 := by
  constructor
  · intro hP g ν
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP g (Set.mem_univ _) lam) ν
  · intro h
    exact mem_vanish.mpr fun g _ lam => by rw [coords_eq_coordsZ]; exact h g _

end LSG.MEB
