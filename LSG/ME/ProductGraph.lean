import Mathlib
import LSG.ME.ProductRat
import StrongSix.M2.Index

/-!
# Product decomposition, step 2: no graph part (`K = ℂ`)

For a Zariski-closed subgroup `H ⊆ G(ℂ)` with Lie algebra `T′ = lieAlg H`:

* `ML H = {g ∈ G_a^{d₀} × G_m^{d₁} | (g, 0) ∈ H⁰}` is a Zariski-closed subgroup, hence
  `V × T_Λ` (StrongSix's `classify`; `ML_eq_prodSet`).
* **`eq_zero_of_lattice`**: a `ℂ`-linear form on `T′` vanishing on `T′ ∩ ker π_A`, with purely
  imaginary values at the `u ∈ T′` with `π_A u ∈ Λ`, vanishes on `T′` (it factors through
  `π_A(T′)`, which is spanned over `ℝ` by lattice vectors, `isAbelianTangent_map_piA`; so its real
  part vanishes, and then the form vanishes by `ℂ`-linearity).
* Applied to the linear forms `u ↦ μ(u₀)` (`μ` vanishing on `π₀(ML)`) and
  `u ↦ Σ φⱼ u₁ⱼ` (`φ ∈ latt ML`; `e^{Σ φⱼ u₁ⱼ} = 1` when `π_A u ∈ Λ`) this gives
  **`mem_lieAlg_iff`** and **`lieAlg_eq_prod`**: `T′ = V × (qspan Λ)^⊥ × T′_A`, i.e.
  `T′ = T′_L ⊕ T′_A` (**`lieAlg_projL_mem`**: `π_L(T′) = T′_L`).
* **`exists_subgroupData`**: packaging as `LSG.W88.SubgroupData` with tangent space `T′`, given
  `ℚ̄`-rationality of `h₀ = {a | (a, 0, 0) ∈ T′}` (not automatic over `ℂ`: e.g. the line
  `ℂ·(1, π) ⊆ G_a²`); **`exists_subgroupData_of_le_one`**: automatic for `d₀ ≤ 1`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Set Module
open LSG.W88 (Tan IsAbelianTangent torusLie SubgroupData RationalOverQbar AlgVec)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-! ### The real-span argument -/

/-- **A linear form with imaginary periods on `T′` vanishes.** -/
theorem eq_zero_of_lattice (hH : IsSubgroupG H) (hc : IsZClosed H) (f : Tan d₀ d₁ m →ₗ[ℂ] ℂ)
    (h0 : ∀ u ∈ lieAlg Ls hH hc, u.2.2 = 0 → f u = 0)
    (hΛ : ∀ u ∈ lieAlg Ls hH hc, (∀ k, u.2.2 k ∈ (Ls k).lattice) → (f u).re = 0)
    {u : Tan d₀ d₁ m} (hu : u ∈ lieAlg Ls hH hc) : f u = 0 := by
  set T := lieAlg Ls hH hc
  have hP := isAbelianTangent_map_piA hH hc
  set L0 := {z : Fin m → ℂ | z ∈ T.map piA ∧ ∀ j, z j ∈ (Ls j).lattice}
  have hpre : ∀ z ∈ Submodule.span ℝ L0, ∃ v ∈ T, v.2.2 = z := by
    intro z hz
    have hz' : z ∈ T.map piA := by
      rw [LSG.W88.IsAbelianTangent] at hP
      rw [← hP] at hz
      exact hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz'
    exact ⟨v, hv, rfl⟩
  have hspan : ∀ v ∈ T, v.2.2 ∈ Submodule.span ℝ L0 := by
    intro v hv
    rw [LSG.W88.IsAbelianTangent] at hP
    rw [← hP]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hre : ∀ z (hz : z ∈ Submodule.span ℝ L0), ∀ v ∈ T, v.2.2 = z → (f v).re = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => rintro v hv rfl; exact hΛ v hv hx.2
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
noncomputable def inLpt (g : StrongSix.Thm1.GPt ℂ d₀ d₁) : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) :=
  (g.1, Additive.ofMul g.2, 0)

variable (Ls) in
/-- `ML H = {g ∈ G_a^{d₀} × G_m^{d₁} | (g, 0) ∈ H⁰}`. -/
def ML (hH : IsSubgroupG H) (hc : IsZClosed H) : Set (StrongSix.Thm1.GPt ℂ d₀ d₁) :=
  {g | inLpt g ∈ H0 Ls hH hc}

theorem ML_isSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) :
    StrongSix.M2.IsSubgroupG (ML Ls hH hc) where
  one_mem := (H0_isSubgroup hH hc).zero_mem
  mul_mem g hg h hh := by
    have := (H0_isSubgroup hH hc).add_mem _ hg _ hh
    change inLpt (Ls := Ls) _ ∈ H0 Ls hH hc
    convert this using 1
    exact Prod.ext rfl (Prod.ext rfl (add_zero 0).symm)
  inv_mem g hg := by
    have := (H0_isSubgroup hH hc).neg_mem _ hg
    change inLpt (Ls := Ls) _ ∈ H0 Ls hH hc
    convert this using 1
    exact Prod.ext rfl (Prod.ext rfl neg_zero.symm)

variable (Ls) in
/-- Substituting the (rescaled) identity into the elliptic blocks. -/
noncomputable def substL (lam : Fin m → ℂˣ) :
    Var d₀ d₁ m → MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ
  | .x i => X (.inl i)
  | .y j => X (.inr (.inl j))
  | .z j => X (.inr (.inr j))
  | .e k c => C ((lam k : ℂ) * rep (0 : EPt (g2L Ls) (g3L Ls) k) c)

theorem eval_substL (lam : Fin m → ℂˣ) (g : StrongSix.Thm1.GPt ℂ d₀ d₁)
    (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (StrongSix.M2.pt g) (aeval (substL Ls lam) P) =
      eval (coords (inLpt (Ls := Ls) g) lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    congr 1
    cases v <;> simp [substL, StrongSix.M2.pt, coords, inLpt, GPt.ym]

theorem ML_eq_zeros (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ML Ls hH hc = StrongSix.M2.zeros
      {Q | ∃ P ∈ vanish (H0 Ls hH hc), ∃ lam, Q = aeval (substL Ls lam) P} := by
  have hz := zeros_vanish (isZClosed_H0 (Ls := Ls) hH hc)
  ext g
  constructor
  · rintro hg _ ⟨P, hP, lam, rfl⟩
    rw [eval_substL]
    exact mem_vanish.mp hP _ hg lam
  · intro h
    change inLpt g ∈ H0 Ls hH hc
    rw [← hz]
    intro P hP lam
    rw [← eval_substL]
    exact h _ ⟨P, hP, lam, rfl⟩

/-- **`ML = V × T_Λ`.** -/
theorem ML_eq_prodSet (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ML Ls hH hc = StrongSix.M2.prodSet (StrongSix.M2.linV (ML Ls hH hc))
      (StrongSix.M2.latt (ML Ls hH hc)) :=
  StrongSix.M2.classify (ML_isSubgroup hH hc) (ML_eq_zeros hH hc)

/-- `(a, e^b)`. -/
noncomputable def linExp (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) : StrongSix.Thm1.GPt ℂ d₀ d₁ :=
  (a, fun j => expU (b j))

theorem chr_linExp (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) (φ : Fin d₁ → ℤ) :
    StrongSix.M2.chr (linExp a b).2 φ = Complex.exp (∑ j, (φ j : ℂ) * b j) := by
  simp only [StrongSix.M2.chr, linExp, expU, Units.val_mk0, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => (Complex.exp_int_mul _ _).symm

theorem expG_eq_inLpt {u : Tan d₀ d₁ m} (hu : ∀ k, u.2.2 k ∈ (Ls k).lattice) :
    expG Ls u = inLpt (linExp u.1 u.2.1) :=
  Prod.ext rfl (Prod.ext rfl (funext fun k => expE_of_mem _ (hu k)))

theorem linExp_mem_ML (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ m}
    (hu : u ∈ lieAlg Ls hH hc) (hΛ : ∀ k, u.2.2 k ∈ (Ls k).lattice) :
    linExp u.1 u.2.1 ∈ ML Ls hH hc := by
  change inLpt _ ∈ H0 Ls hH hc
  rw [← expG_eq_inLpt hΛ]
  exact expG_mem_H0 hH hc hu

theorem mem_lieAlg_of_linExp (hH : IsSubgroupG H) (hc : IsZClosed H) {a : Fin d₀ → ℂ}
    {b : Fin d₁ → ℂ} (h : ∀ c : ℂ, linExp (c • a) (c • b) ∈ ML Ls hH hc) :
    ((a, b, 0) : Tan d₀ d₁ m) ∈ lieAlg Ls hH hc := by
  rw [mem_lieAlg]
  intro c
  rw [mem_Htil]
  have e : expG Ls (c • ((a, b, 0) : Tan d₀ d₁ m)) = inLpt (linExp (c • a) (c • b)) :=
    expG_eq_inLpt fun k => by simp
  rw [e]
  exact H0_subset hH hc (h c)

/-! ### The linear forms -/

/-- `u ↦ Σ φⱼ u₁ⱼ`. -/
def phiL (φ : Fin d₁ → ℤ) : Tan d₀ d₁ m →ₗ[ℂ] ℂ where
  toFun u := ∑ j, (φ j : ℂ) * u.2.1 j
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_left_comm]

theorem phiL_apply (φ : Fin d₁ → ℤ) (u : Tan d₀ d₁ m) : phiL φ u = ∑ j, (φ j : ℂ) * u.2.1 j :=
  rfl

theorem eq_zero_of_forall_exp {s : ℂ} (h : ∀ c : ℂ, Complex.exp (c * s) = 1) : s = 0 := by
  by_contra hs
  have := h (Real.pi * Complex.I / s)
  rw [div_mul_cancel₀ _ hs, Complex.exp_pi_mul_I] at this
  norm_num at this

/-- **The linear part of `T′` lies in `V × (qspan Λ)^⊥`.** -/
theorem linPart_mem (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ m}
    (hu : u ∈ lieAlg Ls hH hc) :
    u.1 ∈ StrongSix.M2.linV (ML Ls hH hc) ∧
      ∀ φ ∈ StrongSix.M2.latt (ML Ls hH hc), phiL φ u = 0 := by
  have h0Λ : ∀ v : Tan d₀ d₁ m, v.2.2 = 0 → ∀ k, v.2.2 k ∈ (Ls k).lattice := fun v h k => by
    rw [h]; exact (Ls k).lattice.zero_mem
  refine ⟨fun μ hμ => ?_, fun φ hφ => ?_⟩
  · refine eq_zero_of_lattice hH hc (μ.comp (LinearMap.fst ℂ _ _)) (fun v hv h => ?_)
      (fun v hv hl => ?_) hu
    · exact hμ _ (linExp_mem_ML hH hc hv (h0Λ v h))
    · change (μ v.1).re = 0
      rw [show μ v.1 = 0 from hμ _ (linExp_mem_ML hH hc hv hl), Complex.zero_re]
  · have hexp : ∀ v ∈ lieAlg Ls hH hc, (∀ k, v.2.2 k ∈ (Ls k).lattice) →
        Complex.exp (phiL φ v) = 1 := fun v hv hl => by
      rw [phiL_apply, ← chr_linExp v.1]
      exact hφ _ (linExp_mem_ML hH hc hv hl)
    refine eq_zero_of_lattice hH hc (phiL φ) (fun v hv h => ?_) (fun v hv hl => ?_) hu
    · refine eq_zero_of_forall_exp fun c => ?_
      rw [← smul_eq_mul, ← map_smul]
      refine hexp _ ((lieAlg Ls hH hc).smul_mem c hv) fun k => ?_
      simp [h]
    · obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexp v hv hl)
      rw [hn]
      simp

/-- **`(a, b, 0) ∈ T′` for `a ∈ V`, `b ⊥ Λ`.** -/
theorem mem_lieAlg_of_linV (hH : IsSubgroupG H) (hc : IsZClosed H) {a : Fin d₀ → ℂ}
    {b : Fin d₁ → ℂ} (ha : a ∈ StrongSix.M2.linV (ML Ls hH hc))
    (hb : ∀ φ ∈ StrongSix.M2.latt (ML Ls hH hc), ∑ j, (φ j : ℂ) * b j = 0) :
    ((a, b, 0) : Tan d₀ d₁ m) ∈ lieAlg Ls hH hc := by
  refine mem_lieAlg_of_linExp hH hc fun c => ?_
  rw [ML_eq_prodSet hH hc]
  refine ⟨Submodule.smul_mem _ c ha, fun φ hφ => ?_⟩
  rw [chr_linExp]
  have : ∑ j, (φ j : ℂ) * (c • b) j = c * ∑ j, (φ j : ℂ) * b j := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hb φ hφ, mul_zero, Complex.exp_zero]

/-! ### The decomposition -/

theorem mem_torusLie_qspan {Λ : AddSubgroup (Fin d₁ → ℤ)} {b : Fin d₁ → ℂ} :
    b ∈ torusLie (StrongSix.M2.qspan Λ) ↔ ∀ φ ∈ Λ, ∑ j, (φ j : ℂ) * b j = 0 := by
  constructor
  · intro hb φ hφ
    have := hb _ (Submodule.subset_span ⟨φ, hφ, rfl⟩)
    simpa using this
  · intro hb ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      simpa using hb φ hφ
    | zero => simp
    | add x y _ _ px py => simp [add_mul, Finset.sum_add_distrib, px, py]
    | smul q x _ px =>
      simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_assoc, ← Finset.mul_sum, px,
        mul_zero]

/-- **The product decomposition**, membership form. -/
theorem mem_lieAlg_iff (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ m} :
    u ∈ lieAlg Ls hH hc ↔ u.1 ∈ StrongSix.M2.linV (ML Ls hH hc) ∧
      u.2.1 ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc))) ∧
      inAb (d₀ := d₀) (d₁ := d₁) u.2.2 ∈ lieAlg Ls hH hc := by
  rw [mem_torusLie_qspan]
  have hsplit : u = ((u.1, u.2.1, 0) : Tan d₀ d₁ m) + inAb u.2.2 := by
    simp [inAb]
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := linPart_mem hH hc hu
    have hL := mem_lieAlg_of_linV (m := m) hH hc h1 h2
    refine ⟨h1, h2, ?_⟩
    have : inAb (d₀ := d₀) (d₁ := d₁) u.2.2 = u - ((u.1, u.2.1, 0) : Tan d₀ d₁ m) := by
      rw [eq_sub_iff_add_eq, add_comm, ← hsplit]
    rw [this]
    exact (lieAlg Ls hH hc).sub_mem hu hL
  · rintro ⟨h1, h2, h3⟩
    rw [hsplit]
    exact (lieAlg Ls hH hc).add_mem (mem_lieAlg_of_linV hH hc h1 h2) h3

/-- **`π_L(T′) = T′_L`**: the linear part of a vector of `T′` lies in `T′`. -/
theorem lieAlg_projL_mem (hH : IsSubgroupG H) (hc : IsZClosed H) {u : Tan d₀ d₁ m}
    (hu : u ∈ lieAlg Ls hH hc) : ((u.1, u.2.1, 0) : Tan d₀ d₁ m) ∈ lieAlg Ls hH hc := by
  obtain ⟨h1, h2⟩ := linPart_mem hH hc hu
  exact mem_lieAlg_of_linV hH hc h1 h2

/-- `h₀ = {a | (a, 0, 0) ∈ T′}`. -/
theorem linV_ML_eq (hH : IsSubgroupG H) (hc : IsZClosed H) :
    StrongSix.M2.linV (ML Ls hH hc) =
      (lieAlg Ls hH hc).comap (LinearMap.inl ℂ (Fin d₀ → ℂ) ((Fin d₁ → ℂ) × (Fin m → ℂ))) := by
  ext a
  rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lieAlg_iff hH hc]
  have h0 : inAb (d₀ := d₀) (d₁ := d₁) (0 : Fin m → ℂ) = 0 := rfl
  simp only [Prod.snd_zero, Prod.fst_zero, h0, Submodule.zero_mem, (torusLie _).zero_mem,
    and_true]

/-- **`T′ = h₀ × (qspan Λ)^⊥ × T′_A`.** -/
theorem lieAlg_eq_prod (hH : IsSubgroupG H) (hc : IsZClosed H) :
    lieAlg Ls hH hc =
      ((lieAlg Ls hH hc).comap (LinearMap.inl ℂ (Fin d₀ → ℂ) ((Fin d₁ → ℂ) × (Fin m → ℂ)))).prod
        ((torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))).prod
          ((lieAlg Ls hH hc).comap inAbL)) := by
  rw [← linV_ML_eq hH hc]
  ext u
  rw [mem_lieAlg_iff hH hc]
  simp only [Submodule.mem_prod, Submodule.mem_comap, inAbL_apply]

theorem isAbelianTangent_comap_inAbL (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsAbelianTangent Ls ((lieAlg Ls hH hc).comap (inAbL (d₀ := d₀) (d₁ := d₁))) := by
  obtain ⟨t, hab, ht, -⟩ := exists_abelianTangent_Htil hH hc
  have : t = (lieAlg Ls hH hc).comap (inAbL (d₀ := d₀) (d₁ := d₁)) := by
    ext z; rw [ht z, Submodule.mem_comap, inAbL_apply]
  rw [← this]
  exact hab

/-! ### Packaging as `SubgroupData` -/

/-- **`T′` is the tangent space of a `SubgroupData`**, if `h₀` is `ℚ̄`-rational. -/
theorem exists_subgroupData (hH : IsSubgroupG H) (hc : IsZClosed H)
    (hrat : RationalOverQbar
      ((lieAlg Ls hH hc).comap (LinearMap.inl ℂ (Fin d₀ → ℂ) ((Fin d₁ → ℂ) × (Fin m → ℂ))))) :
    ∃ S : SubgroupData (d0 := d₀) (d1 := d₁) Ls, S.tan = lieAlg Ls hH hc ∧
      S.h0 = (lieAlg Ls hH hc).comap (LinearMap.inl ℂ _ _) ∧
      S.t = (lieAlg Ls hH hc).comap inAbL :=
  ⟨{ h0 := _, U := StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)), t := _,
     h0_rat := hrat, t_ab := isAbelianTangent_comap_inAbL hH hc },
    (lieAlg_eq_prod hH hc).symm, rfl, rfl⟩

/-- Every subspace of `ℂ^{d₀}` is `ℚ̄`-rational when `d₀ ≤ 1`. -/
theorem rationalOverQbar_of_le_one (hd : d₀ ≤ 1) (W : Submodule ℂ (Fin d₀ → ℂ)) :
    RationalOverQbar W := by
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr fun w hw => hw.1)
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
  have : Subsingleton (Fin d₀) := Fin.subsingleton_iff_le_one.mpr hd
  have hone : w = w i • (fun _ => (1 : ℂ)) := by
    funext j; rw [Subsingleton.elim j i]; simp
  have hone' : (w i)⁻¹ • w = fun _ => (1 : ℂ) := by
    have hi' : w i ≠ 0 := hi
    funext j; rw [Subsingleton.elim j i]; simp [inv_mul_cancel₀ hi']
  have hmem : (fun _ => (1 : ℂ)) ∈ W := hone' ▸ W.smul_mem (w i)⁻¹ hw
  rw [hone]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hmem, fun _ => isAlgebraic_one⟩)

/-- **`T′` is the tangent space of a `SubgroupData`** when `d₀ ≤ 1`. -/
theorem exists_subgroupData_of_le_one (hH : IsSubgroupG H) (hc : IsZClosed H) (hd : d₀ ≤ 1) :
    ∃ S : SubgroupData (d0 := d₀) (d1 := d₁) Ls, S.tan = lieAlg Ls hH hc :=
  (exists_subgroupData hH hc (rationalOverQbar_of_le_one hd _)).imp fun _ h => h.1

end LSG.ME
