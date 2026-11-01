/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.SubgroupRat
import LSG.ME.ProductGraph

/-!
# Product decomposition, step 2: `lieAlg H = h₀ × U^⊥ × t` (A4.3, β″)

Port of ME's `ProductGraph` to abstract blocks (without ME's `ℚ̄` part: `ObstrDataB` has no rationality condition
on `h₀`). For a Zariski-closed subgroup `H ⊆ G` with Lie algebra `T′ = lieAlg hH`:

* **`eq_zero_of_lattice`**: a `ℂ`-linear form on `T′` vanishing on `T′ ∩ ker π_A`, with purely imaginary values at
  the `u ∈ T′` with `π_A u ∈ perAb`, vanishes on `T′` (it factors through `π_A(T′)`, which is spanned over `ℝ` by
  lattice vectors, `isRatSub_map_piA`).
* `ML hH = {g ∈ G_a^{d₀} × G_m^{d₁} | (g, 0) ∈ H⁰}` is a Zariski-closed subgroup in StrongSix's sense, hence
  `V × T_Λ` (StrongSix's `classify`; `ML_eq_prodSet`).
* **`mem_lieAlg_iff`**, **`lieAlg_projL_mem`** (`π_L(T′) ⊆ T′`), and the **stable names** for the decomposition:
  `h0Of hH = {a | (a, 0, 0) ∈ T′}`, `UOf hH = qspan (latt (ML hH))`, `tOf hH = {z | (0, 0, z) ∈ T′}`;
  **`lieAlg_eq_tanOf`**: `lieAlg hH = tanOf (h0Of hH) (UOf hH) (tOf hH)`; `tOf_eq_map_piA`; **`isRatSub_tOf`**.
-/

open MvPolynomial Set Module
open LSG.W88 (torusLie)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {H : Set (GPt d₀ d₁ B)}

/-! ### The real-span argument -/

/-- **A linear form with imaginary periods on `T′` vanishes.** -/
theorem eq_zero_of_lattice (hH : IsSubgroupG H) (hc : IsZClosed H) (f : Tan d₀ d₁ B →ₗ[ℂ] ℂ)
    (h0 : ∀ u ∈ lieAlg hH, u.2.2 = 0 → f u = 0)
    (hΛ : ∀ u ∈ lieAlg hH, (∀ k, u.2.2 k ∈ (B k).per) → (f u).re = 0)
    {u : Tan d₀ d₁ B} (hu : u ∈ lieAlg hH) : f u = 0 := by
  set T := lieAlg hH
  have hP : IsRatSub (perAb B) (T.map piA) := isRatSub_map_piA hH hc
  set L0 := {z : ∀ k, Fin (B k).g → ℂ | z ∈ T.map piA ∧ z ∈ perAb B}
  have hpre : ∀ z ∈ Submodule.span ℝ L0, ∃ v ∈ T, v.2.2 = z := by
    intro z hz
    have hz' : z ∈ T.map piA := by
      rw [IsRatSub] at hP
      rw [← hP] at hz
      exact hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz'
    exact ⟨v, hv, rfl⟩
  have hspan : ∀ v ∈ T, v.2.2 ∈ Submodule.span ℝ L0 := by
    intro v hv
    rw [IsRatSub] at hP
    rw [← hP]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hre : ∀ z (hz : z ∈ Submodule.span ℝ L0), ∀ v ∈ T, v.2.2 = z → (f v).re = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => rintro v hv rfl; exact hΛ v hv fun k => hx.2 k (Set.mem_univ k)
    | zero => intro v hv h; rw [h0 v hv h, Complex.zero_re]
    | add x y hx hy px py =>
      intro v hv h
      obtain ⟨v₁, hv₁, rfl⟩ := hpre _ hx
      have h2 : (v - v₁).2.2 = y := by
        simp only [Prod.snd_sub, h, add_sub_cancel_left]
      have := py (v - v₁) (T.sub_mem hv hv₁) h2
      rw [show v = v₁ + (v - v₁) by abel, map_add, Complex.add_re, px v₁ hv₁ rfl, this, add_zero]
    | smul a x hx px =>
      intro v hv h
      obtain ⟨v₁, hv₁, rfl⟩ := hpre _ hx
      have h2 : (v - (a : ℂ) • v₁).2.2 = 0 := by
        simp only [Prod.snd_sub, Prod.smul_snd, h, Complex.coe_smul, sub_self]
      have := h0 _ (T.sub_mem hv (T.smul_mem _ hv₁)) h2
      rw [show v = (a : ℂ) • v₁ + (v - (a : ℂ) • v₁) by abel, map_add, this, add_zero, map_smul,
        smul_eq_mul, Complex.re_ofReal_mul, px v₁ hv₁ rfl, mul_zero]
  have h1 : (f u).re = 0 := hre _ (hspan u hu) u hu rfl
  have h2 : (f (Complex.I • u)).re = 0 :=
    hre _ (hspan _ (T.smul_mem _ hu)) _ (T.smul_mem _ hu) rfl
  rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
  exact Complex.ext h1 (by simpa using h2)

/-! ### The linear part `ML` -/

/-- `L ↪ G`, `g ↦ (g, 0)`. -/
noncomputable def inLpt (g : StrongSix.Thm1.GPt ℂ d₀ d₁) : GPt d₀ d₁ B :=
  (g.1, Additive.ofMul g.2, 0)

/-- `ML hH = {g ∈ G_a^{d₀} × G_m^{d₁} | (g, 0) ∈ H⁰}`. -/
def ML (hH : IsSubgroupG H) : Set (StrongSix.Thm1.GPt ℂ d₀ d₁) :=
  {g | inLpt g ∈ H0 hH}

theorem ML_isSubgroup (hH : IsSubgroupG H) : StrongSix.M2.IsSubgroupG (ML hH) where
  one_mem := (H0_isSubgroup hH).zero_mem
  mul_mem g hg h hh := by
    have := (H0_isSubgroup hH).add_mem _ hg _ hh
    change inLpt (B := B) _ ∈ H0 hH
    convert this using 1
    exact Prod.ext rfl (Prod.ext rfl (add_zero 0).symm)
  inv_mem g hg := by
    have := (H0_isSubgroup hH).neg_mem _ hg
    change inLpt (B := B) _ ∈ H0 hH
    convert this using 1
    exact Prod.ext rfl (Prod.ext rfl neg_zero.symm)

variable (B) in
/-- Substituting the (rescaled) identity into the abelian blocks. -/
noncomputable def substL (lam : Fin m → ℂˣ) :
    Var d₀ d₁ B → MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ
  | .x i => X (.inl i)
  | .y j => X (.inr (.inl j))
  | .z j => X (.inr (.inr j))
  | .e k c => C ((lam k : ℂ) * (B k).rep (0 : (B k).Pt) c)

theorem eval_substL (lam : Fin m → ℂˣ) (g : StrongSix.Thm1.GPt ℂ d₀ d₁)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    eval (StrongSix.M2.pt g) (aeval (substL B lam) P) = eval (coords (inLpt (B := B) g) lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    congr 1
    cases v <;> simp [substL, StrongSix.M2.pt, inLpt, GPt.ym]

theorem ML_eq_zeros (hH : IsSubgroupG H) :
    ML hH = StrongSix.M2.zeros
      {Q | ∃ P ∈ vanish (H0 hH), ∃ lam, Q = aeval (substL B lam) P} := by
  have hz := zeros_vanish (isZClosed_H0 hH)
  ext g
  constructor
  · rintro hg _ ⟨P, hP, lam, rfl⟩
    rw [eval_substL]
    exact mem_vanish.mp hP _ hg lam
  · intro h
    change inLpt g ∈ H0 hH
    rw [← hz]
    intro P hP lam
    rw [← eval_substL]
    exact h _ ⟨P, hP, lam, rfl⟩

/-- **`ML = V × T_Λ`** (StrongSix's `classify`). -/
theorem ML_eq_prodSet (hH : IsSubgroupG H) :
    ML hH = StrongSix.M2.prodSet (StrongSix.M2.linV (ML hH)) (StrongSix.M2.latt (ML hH)) :=
  StrongSix.M2.classify (ML_isSubgroup hH) (ML_eq_zeros hH)

/-- `(a, e^b)`. -/
noncomputable def linExp (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) : StrongSix.Thm1.GPt ℂ d₀ d₁ :=
  (a, fun j => expU (b j))

theorem chr_linExp (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) (φ : Fin d₁ → ℤ) :
    StrongSix.M2.chr (linExp a b).2 φ = Complex.exp (∑ j, (φ j : ℂ) * b j) := by
  simp only [StrongSix.M2.chr, linExp, expU, Units.val_mk0, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => (Complex.exp_int_mul _ _).symm

theorem expG_eq_inLpt {u : Tan d₀ d₁ B} (hu : ∀ k, u.2.2 k ∈ (B k).per) :
    expG d₀ d₁ B u = inLpt (linExp u.1 u.2.1) :=
  Prod.ext rfl (Prod.ext rfl (funext fun k => (QuotientAddGroup.eq_zero_iff _).mpr (hu k)))

theorem linExp_mem_ML (hH : IsSubgroupG H) {u : Tan d₀ d₁ B} (hu : u ∈ lieAlg hH)
    (hΛ : ∀ k, u.2.2 k ∈ (B k).per) : linExp u.1 u.2.1 ∈ ML hH := by
  change inLpt _ ∈ H0 hH
  rw [← expG_eq_inLpt hΛ]
  exact expG_mem_H0 hH hu

theorem mem_lieAlg_of_linExp (hH : IsSubgroupG H) (hc : IsZClosed H) {a : Fin d₀ → ℂ}
    {b : Fin d₁ → ℂ} (h : ∀ c : ℂ, linExp (c • a) (c • b) ∈ ML hH) :
    ((a, b, 0) : Tan d₀ d₁ B) ∈ lieAlg hH := by
  rw [mem_lieAlg]
  intro c
  have e : expG d₀ d₁ B (c • ((a, b, 0) : Tan d₀ d₁ B)) = inLpt (linExp (c • a) (c • b)) :=
    expG_eq_inLpt fun k => by simp [(B k).per.zero_mem]
  rw [e]
  exact H0_subset hH hc (h c)

/-! ### The linear forms -/

/-- `u ↦ Σ φⱼ u₁ⱼ`. -/
noncomputable def phiL (φ : Fin d₁ → ℤ) : Tan d₀ d₁ B →ₗ[ℂ] ℂ where
  toFun u := ∑ j, (φ j : ℂ) * u.2.1 j
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_left_comm]

theorem phiL_apply (φ : Fin d₁ → ℤ) (u : Tan d₀ d₁ B) : phiL φ u = ∑ j, (φ j : ℂ) * u.2.1 j :=
  rfl

/-- **The linear part of `T′` lies in `V × (qspan Λ)^⊥`.** -/
theorem linPart_mem (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ B} (hu : u ∈ lieAlg hH) :
    u.1 ∈ StrongSix.M2.linV (ML hH) ∧ ∀ φ ∈ StrongSix.M2.latt (ML hH), phiL φ u = 0 := by
  have h0Λ : ∀ v : Tan d₀ d₁ B, v.2.2 = 0 → ∀ k, v.2.2 k ∈ (B k).per := fun v h k => by
    rw [h]; exact (B k).per.zero_mem
  refine ⟨fun μ hμ => ?_, fun φ hφ => ?_⟩
  · refine eq_zero_of_lattice hH hc (μ.comp (LinearMap.fst ℂ _ _)) (fun v hv h => ?_)
      (fun v hv hl => ?_) hu
    · exact hμ _ (linExp_mem_ML hH hv (h0Λ v h))
    · change (μ v.1).re = 0
      rw [show μ v.1 = 0 from hμ _ (linExp_mem_ML hH hv hl), Complex.zero_re]
  · have hexp : ∀ v ∈ lieAlg hH, (∀ k, v.2.2 k ∈ (B k).per) → Complex.exp (phiL φ v) = 1 :=
      fun v hv hl => by
        rw [phiL_apply, ← chr_linExp v.1]
        exact hφ _ (linExp_mem_ML hH hv hl)
    refine eq_zero_of_lattice hH hc (phiL φ) (fun v hv h => ?_) (fun v hv hl => ?_) hu
    · refine LSG.ME.eq_zero_of_forall_exp fun c => ?_
      rw [← smul_eq_mul, ← map_smul]
      refine hexp _ ((lieAlg hH).smul_mem c hv) fun k => ?_
      simp [h, (B k).per.zero_mem]
    · obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexp v hv hl)
      rw [hn]
      simp

/-- **`(a, b, 0) ∈ T′` for `a ∈ V`, `b ⊥ Λ`.** -/
theorem mem_lieAlg_of_linV (hH : IsSubgroupG H) (hc : IsZClosed H) {a : Fin d₀ → ℂ}
    {b : Fin d₁ → ℂ} (ha : a ∈ StrongSix.M2.linV (ML hH))
    (hb : ∀ φ ∈ StrongSix.M2.latt (ML hH), ∑ j, (φ j : ℂ) * b j = 0) :
    ((a, b, 0) : Tan d₀ d₁ B) ∈ lieAlg hH := by
  refine mem_lieAlg_of_linExp hH hc fun c => ?_
  rw [ML_eq_prodSet hH]
  refine ⟨Submodule.smul_mem _ c ha, fun φ hφ => ?_⟩
  rw [chr_linExp]
  have : ∑ j, (φ j : ℂ) * (c • b) j = c * ∑ j, (φ j : ℂ) * b j := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hb φ hφ, mul_zero, Complex.exp_zero]

/-! ### The decomposition -/

/-- **The product decomposition**, membership form. -/
theorem mem_lieAlg_iff (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ B} :
    u ∈ lieAlg hH ↔ u.1 ∈ StrongSix.M2.linV (ML hH) ∧
      u.2.1 ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (ML hH))) ∧
      inAbL (d₀ := d₀) (d₁ := d₁) u.2.2 ∈ lieAlg hH := by
  rw [LSG.ME.mem_torusLie_qspan]
  have hsplit : u = ((u.1, u.2.1, 0) : Tan d₀ d₁ B) + inAbL u.2.2 := by
    simp [inAbL_apply]
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := linPart_mem hH hc hu
    have hL := mem_lieAlg_of_linV hH hc h1 h2
    refine ⟨h1, h2, ?_⟩
    have : inAbL (d₀ := d₀) (d₁ := d₁) u.2.2 = u - ((u.1, u.2.1, 0) : Tan d₀ d₁ B) := by
      rw [eq_sub_iff_add_eq, add_comm, ← hsplit]
    rw [this]
    exact (lieAlg hH).sub_mem hu hL
  · rintro ⟨h1, h2, h3⟩
    rw [hsplit]
    exact (lieAlg hH).add_mem (mem_lieAlg_of_linV hH hc h1 h2) h3

/-- **`π_L(T′) ⊆ T′`**: the linear part of a vector of `T′` lies in `T′`. -/
theorem lieAlg_projL_mem (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ B}
    (hu : u ∈ lieAlg hH) : ((u.1, u.2.1, 0) : Tan d₀ d₁ B) ∈ lieAlg hH := by
  obtain ⟨h1, h2⟩ := linPart_mem hH hc hu
  exact mem_lieAlg_of_linV hH hc h1 h2

/-- The additive part `h₀ = {a | (a, 0, 0) ∈ T′}`. -/
noncomputable def h0Of (hH : IsSubgroupG H) : Submodule ℂ (Fin d₀ → ℂ) :=
  (lieAlg hH).comap (LinearMap.inl ℂ (Fin d₀ → ℂ) ((Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ)))

/-- The character space `U = qspan (latt (ML hH))` of the toric part. -/
noncomputable def UOf (hH : IsSubgroupG H) : Submodule ℚ (Fin d₁ → ℚ) :=
  StrongSix.M2.qspan (StrongSix.M2.latt (ML hH))

/-- The abelian part `t = {z | (0, 0, z) ∈ T′}`. -/
noncomputable def tOf (hH : IsSubgroupG H) : Submodule ℂ (∀ k, Fin (B k).g → ℂ) :=
  (lieAlg hH).comap (inAbL (d₀ := d₀) (d₁ := d₁))

theorem mem_h0Of {hH : IsSubgroupG H} {a : Fin d₀ → ℂ} :
    a ∈ h0Of hH ↔ ((a, 0, 0) : Tan d₀ d₁ B) ∈ lieAlg hH := Iff.rfl

theorem mem_tOf {hH : IsSubgroupG H} {z : ∀ k, Fin (B k).g → ℂ} :
    z ∈ tOf hH ↔ ((0, 0, z) : Tan d₀ d₁ B) ∈ lieAlg hH := Iff.rfl

/-- `h₀ = linV (ML hH)`. -/
theorem linV_ML_eq (hH : IsSubgroupG H) (hc : IsZClosed H) :
    StrongSix.M2.linV (ML hH) = h0Of hH := by
  ext a
  rw [h0Of, Submodule.mem_comap, LinearMap.inl_apply, mem_lieAlg_iff hH hc]
  have h0 : inAbL (d₀ := d₀) (d₁ := d₁) (0 : ∀ k, Fin (B k).g → ℂ) = 0 := map_zero _
  simp only [Prod.snd_zero, Prod.fst_zero, h0, Submodule.zero_mem, (torusLie _).zero_mem, and_true]

/-- **`T′ = h₀ × U^⊥ × t`** (the product decomposition, stable form). -/
theorem lieAlg_eq_tanOf (hH : IsSubgroupG H) (hc : IsZClosed H) :
    lieAlg hH = tanOf (h0Of hH) (UOf hH) (tOf hH) := by
  ext u
  rw [mem_lieAlg_iff hH hc, linV_ML_eq hH hc]
  simp only [tanOf, Submodule.mem_prod, UOf, tOf, Submodule.mem_comap]

/-- `t = π_A(T′)`. -/
theorem tOf_eq_map_piA (hH : IsSubgroupG H) (hc : IsZClosed H) :
    tOf hH = (lieAlg hH).map (piA (d₀ := d₀) (d₁ := d₁)) := by
  ext z
  constructor
  · intro hz
    exact ⟨_, hz, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hL := lieAlg_projL_mem hH hc hu
    have : inAbL (d₀ := d₀) (d₁ := d₁) (piA u) = u - ((u.1, u.2.1, 0) : Tan d₀ d₁ B) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    change inAbL (piA u) ∈ lieAlg hH
    rw [this]
    exact (lieAlg hH).sub_mem hu hL

/-- **`t` is `perAb`-rational.** -/
theorem isRatSub_tOf (hH : IsSubgroupG H) (hc : IsZClosed H) : IsRatSub (perAb B) (tOf hH) := by
  rw [tOf_eq_map_piA hH hc]
  exact isRatSub_map_piA hH hc

end LSG.MEB
