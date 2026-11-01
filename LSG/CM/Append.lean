/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.CM.Block

/-!
# Abelian subvarieties of `E₁^p × E₂^q` split, and the CM inputs for the product

Curves `Ls = Fin.append Ls₁ Ls₂` on `ℂ^{p+q} = ℂ^p × ℂ^q` (`inl₁`, `inr₂`, `pr₁`, `pr₂`).

* `Splits Ls₁ Ls₂ t`: for every lattice point `λ ∈ t`, its `ℂ^p`-part `(λ₁, 0)` lies in `t`.
* **`splits_of_irrational`**: if `iΛ₁ ⊆ Λ₁` on the first block and `(c i)Λ₂ ⊆ Λ₂` on the second,
  with `c ∈ ℝ` irrational, every abelian tangent splits (`B = B₁ × B₂`: no isogeny between the
  blocks).
  Proof: a `ℚ`-linear `f : ℝ → ℝ` with `f 1 = 0`, `f c⁻¹ = 1` applied to the coordinates w.r.t. the
  period bases gives an additive `Φ` with `Φ(xλ) = f(x)λ` for lattice points `λ`, so `Φ(t) ⊆ t`
  (`t = span_ℝ` of its lattice points), and `Φ(iλ) = (0, c i λ₂)`.
* For a split abelian `t`: `t₁ = inl₁⁻¹ t`, `t₂ = inr₂⁻¹ t` are abelian (`abel_left/right`),
  `T(B^♮) = E₁ T(B₁^♮) + E₂ T(B₂^♮)` (`perTanId_le`, `map_left_le`, `map_right_le`), so
  **`perTanRat_append`** and **`liftAlg_append`** reduce `PerTanRat`, `LiftAlg` to the blocks.
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.W88 LSG.W88.Vec

namespace LSG.CM

variable {p q : ℕ}

/-! ### The two blocks -/

/-- `v ↦ (v, 0)`. -/
noncomputable def inl₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin (p + q) → ℂ) where
  toFun v := Fin.append v 0
  map_add' u v := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c v := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- `v ↦ (0, v)`. -/
noncomputable def inr₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin (p + q) → ℂ) where
  toFun v := Fin.append 0 v
  map_add' u v := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c v := by funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The first block. -/
noncomputable abbrev pr₁ : (Fin (p + q) → ℂ) →ₗ[ℂ] (Fin p → ℂ) :=
  LinearMap.funLeft ℂ ℂ (Fin.castAdd q)

/-- The second block. -/
noncomputable abbrev pr₂ : (Fin (p + q) → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
  LinearMap.funLeft ℂ ℂ (Fin.natAdd p)

@[simp] lemma inl₁_left (v : Fin p → ℂ) (j : Fin p) : inl₁ (q := q) v (Fin.castAdd q j) = v j := by
  simp [inl₁]
@[simp] lemma inl₁_right (v : Fin p → ℂ) (j : Fin q) : inl₁ (q := q) v (Fin.natAdd p j) = 0 := by
  simp [inl₁]
@[simp] lemma inr₂_left (v : Fin q → ℂ) (j : Fin p) : inr₂ (p := p) v (Fin.castAdd q j) = 0 := by
  simp [inr₂]
@[simp] lemma inr₂_right (v : Fin q → ℂ) (j : Fin q) : inr₂ (p := p) v (Fin.natAdd p j) = v j := by
  simp [inr₂]

lemma decomp (v : Fin (p + q) → ℂ) : v = inl₁ (pr₁ v) + inr₂ (pr₂ v) := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

variable (Ls₁ : Fin p → PeriodPair) (Ls₂ : Fin q → PeriodPair)

/-- Lattice points of `t` have their first block in `t`. -/
def Splits (t : Submodule ℂ (Fin (p + q) → ℂ)) : Prop :=
  ∀ l ∈ t, (∀ j, l j ∈ (Fin.append Ls₁ Ls₂ j).lattice) → inl₁ (pr₁ l) ∈ t

variable {Ls₁ Ls₂}

lemma lat_left {l : Fin (p + q) → ℂ} (h : ∀ j, l j ∈ (Fin.append Ls₁ Ls₂ j).lattice) (j : Fin p) :
    l (Fin.castAdd q j) ∈ (Ls₁ j).lattice := by simpa using h (Fin.castAdd q j)

lemma lat_right {l : Fin (p + q) → ℂ} (h : ∀ j, l j ∈ (Fin.append Ls₁ Ls₂ j).lattice) (j : Fin q) :
    l (Fin.natAdd p j) ∈ (Ls₂ j).lattice := by simpa using h (Fin.natAdd p j)

lemma lat_inl {l : Fin p → ℂ} (h : ∀ j, l j ∈ (Ls₁ j).lattice) (i : Fin (p + q)) :
    inl₁ l i ∈ (Fin.append Ls₁ Ls₂ i).lattice := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using h j
  · simp

lemma lat_inr {l : Fin q → ℂ} (h : ∀ j, l j ∈ (Ls₂ j).lattice) (i : Fin (p + q)) :
    inr₂ l i ∈ (Fin.append Ls₁ Ls₂ i).lattice := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simpa using h j

lemma etaV_decomp (l : Fin (p + q) → ℂ) : etaV (Fin.append Ls₁ Ls₂) l =
    inl₁ (etaV Ls₁ (pr₁ l)) + inr₂ (etaV Ls₂ (pr₂ l)) := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [etaV]

lemma etaV_inl (l : Fin p → ℂ) : etaV (Fin.append Ls₁ Ls₂) (inl₁ l) = inl₁ (etaV Ls₁ l) := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [etaV]

lemma etaV_inr (l : Fin q → ℂ) : etaV (Fin.append Ls₁ Ls₂) (inr₂ l) = inr₂ (etaV Ls₂ l) := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [etaV]

/-! ### Splitting -/

section Split

variable {t : Submodule ℂ (Fin (p + q) → ℂ)}

lemma splits_right (hs : Splits Ls₁ Ls₂ t) {l : Fin (p + q) → ℂ} (hlt : l ∈ t)
    (hl : ∀ j, l j ∈ (Fin.append Ls₁ Ls₂ j).lattice) : inr₂ (pr₂ l) ∈ t := by
  have : inr₂ (pr₂ l) = l - inl₁ (pr₁ l) := by
    rw [eq_sub_iff_add_eq, add_comm (inr₂ _)]; exact (decomp _).symm
  rw [this]; exact t.sub_mem hlt (hs l hlt hl)

/-- The coordinate change of `f` along a period basis: `x ω₁ + y ω₂ ↦ f(x) ω₁ + f(y) ω₂`. -/
noncomputable def phiL (f : ℝ →ₗ[ℚ] ℝ) (L : PeriodPair) (z : ℂ) : ℂ :=
  f (L.basis.repr z 0) • L.ω₁ + f (L.basis.repr z 1) • L.ω₂

lemma phiL_add (f : ℝ →ₗ[ℚ] ℝ) (L : PeriodPair) (z w : ℂ) :
    phiL f L (z + w) = phiL f L z + phiL f L w := by
  simp only [phiL, map_add, Finsupp.add_apply, add_smul]; abel

lemma phiL_smul (f : ℝ →ₗ[ℚ] ℝ) (L : PeriodPair) (x : ℝ) {l : ℂ} (hl : l ∈ L.lattice) :
    phiL f L (x • l) = f x • l := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have h : x • ((m : ℂ) * L.ω₁ + n * L.ω₂) = (x * m) • L.basis 0 + (x * n) • L.basis 1 := by
    simp only [basis_zero, basis_one, Complex.real_smul]; push_cast; ring
  have hm : f (x * m) = (m : ℝ) * f x := by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have hn : f (x * n) = (n : ℝ) * f x := by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  rw [phiL, h]
  simp only [map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp only [show ((1 : Fin 2) = 0) ↔ False by decide, show ((0 : Fin 2) = 1) ↔ False by decide,
    ite_true, ite_false, mul_one, mul_zero]
  rw [hm, hn]
  simp only [Complex.real_smul, map_zero]; push_cast; ring

lemma phiL_zero (f : ℝ →ₗ[ℚ] ℝ) (L : PeriodPair) : phiL f L 0 = 0 := by simp [phiL]

/-- **Abelian subvarieties of `E₁^p × E₂^q` split** when `iΛ₁ ⊆ Λ₁`, `(c i)Λ₂ ⊆ Λ₂` with `c`
irrational. -/
theorem splits_of_irrational {c : ℝ} (hc : Irrational c)
    (h₁ : ∀ j, ∀ x ∈ (Ls₁ j).lattice, I * x ∈ (Ls₁ j).lattice)
    (h₂ : ∀ j, ∀ x ∈ (Ls₂ j).lattice, (c : ℂ) * I * x ∈ (Ls₂ j).lattice)
    (hab : IsAbelianTangent (Fin.append Ls₁ Ls₂) t) : Splits Ls₁ Ls₂ t := by
  intro l hlt hl
  -- the `ℚ`-linear functional
  have hc' : c⁻¹ ∉ Submodule.span ℚ ({1} : Set ℝ) := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    exact hc.inv ⟨a, by rw [← ha]; simp [Rat.smul_def]⟩
  obtain ⟨f₀, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc' inferInstance
  have hf1 : f₀ 1 = 0 := by
    have : f₀ 1 ∈ (Submodule.span ℚ ({1} : Set ℝ)).map f₀ :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rw [hfmap] at this; exact this
  let f : ℝ →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp ((f₀ c⁻¹)⁻¹ • f₀)
  have hf1' : f 1 = 0 := by simp [f, hf1]
  have hfc : f c⁻¹ = 1 := by simp [f, inv_mul_cancel₀ hf0]
  -- `Φ`
  let Φ : (Fin (p + q) → ℂ) → (Fin (p + q) → ℂ) := fun v i => phiL f (Fin.append Ls₁ Ls₂ i) (v i)
  have hΦ : ∀ z ∈ Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ (Fin.append Ls₁ Ls₂ j).lattice},
      ∀ x : ℝ, Φ (x • z) ∈ t := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      intro x
      have : Φ (x • z) = ((f x : ℝ) : ℂ) • z := by
        funext i; simp only [Φ, Pi.smul_apply]; rw [phiL_smul f _ x (hz.2 i)]; rfl
      rw [this]; exact t.smul_mem _ hz.1
    | zero => intro x; have : Φ (x • 0) = 0 := by funext i; simp [Φ, phiL_zero]
              rw [this]; exact t.zero_mem
    | add a b _ _ ha hb =>
      intro x
      have : Φ (x • (a + b)) = Φ (x • a) + Φ (x • b) := by
        funext i; simp only [Φ, smul_add, Pi.add_apply, phiL_add]
      rw [this]; exact t.add_mem (ha x) (hb x)
    | smul r a _ ha => intro x; rw [smul_smul]; exact ha (x * r)
  have hIl : I • l ∈ t := t.smul_mem I hlt
  have hmem : I • l ∈ Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ (Fin.append Ls₁ Ls₂ j).lattice} := by
    have : I • l ∈ t.restrictScalars ℝ := hIl
    rwa [hab] at this
  have h1 := hΦ _ hmem 1
  rw [one_smul] at h1
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; rintro rfl; exact hc ⟨0, by simp⟩
  have hΦl : Φ (I • l) = ((c : ℂ) * I) • inr₂ (pr₂ l) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Φ, Pi.smul_apply, smul_eq_mul, inr₂_left, mul_zero, Fin.append_left]
      have := phiL_smul f (Ls₁ j) 1 (h₁ j _ (lat_left hl j))
      rw [one_smul, hf1', zero_smul] at this
      exact this
    · simp only [Φ, Pi.smul_apply, smul_eq_mul, inr₂_right, Fin.append_right,
        LinearMap.funLeft_apply]
      have := phiL_smul f (Ls₂ j) c⁻¹ (h₂ j _ (lat_right hl j))
      rw [hfc, one_smul, Complex.real_smul, Complex.ofReal_inv] at this
      rw [← this]
      congr 1
      field_simp
  rw [hΦl] at h1
  have h2 : inr₂ (pr₂ l) ∈ t := by
    have := t.smul_mem ((c : ℂ) * I)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc0 I_ne_zero), one_smul] at this
  have : inl₁ (pr₁ l) = l - inr₂ (pr₂ l) := by rw [eq_sub_iff_add_eq, ← decomp]
  rw [this]; exact t.sub_mem hlt h2

end Split

/-! ### Reduction to the blocks -/

section Reduce

variable {t : Submodule ℂ (Fin (p + q) → ℂ)}

lemma abel_left (hab : IsAbelianTangent (Fin.append Ls₁ Ls₂) t) (hs : Splits Ls₁ Ls₂ t) :
    IsAbelianTangent Ls₁ (t.comap inl₁) := by
  apply le_antisymm
  · intro x hx
    have hx' : inl₁ x ∈ t.restrictScalars ℝ := hx
    rw [hab] at hx'
    have hmap := Submodule.mem_map_of_mem (f := (pr₁ (p := p) (q := q)).restrictScalars ℝ) hx'
    rw [← Submodule.span_image] at hmap
    have heq : (pr₁ (p := p) (q := q)).restrictScalars ℝ (inl₁ x) = x := by
      funext j; simp
    rw [heq] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨l, ⟨hlt, hl⟩, rfl⟩
    exact ⟨hs l hlt hl, fun j => lat_left hl j⟩
  · rw [Submodule.span_le]; exact fun z hz => hz.1

lemma abel_right (hab : IsAbelianTangent (Fin.append Ls₁ Ls₂) t) (hs : Splits Ls₁ Ls₂ t) :
    IsAbelianTangent Ls₂ (t.comap inr₂) := by
  apply le_antisymm
  · intro x hx
    have hx' : inr₂ x ∈ t.restrictScalars ℝ := hx
    rw [hab] at hx'
    have hmap := Submodule.mem_map_of_mem (f := (pr₂ (p := p) (q := q)).restrictScalars ℝ) hx'
    rw [← Submodule.span_image] at hmap
    have heq : (pr₂ (p := p) (q := q)).restrictScalars ℝ (inr₂ x) = x := by
      funext j; simp
    rw [heq] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨l, ⟨hlt, hl⟩, rfl⟩
    exact ⟨splits_right hs hlt hl, fun j => lat_right hl j⟩
  · rw [Submodule.span_le]; exact fun z hz => hz.1

lemma mem_left (hab : IsAbelianTangent (Fin.append Ls₁ Ls₂) t) (hs : Splits Ls₁ Ls₂ t)
    {z : Fin (p + q) → ℂ} (hz : z ∈ t) : inl₁ (pr₁ z) ∈ t := by
  rw [← span_lat_eq hab] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => exact hs z hz.1 hz.2
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add]; exact t.add_mem ha hb
  | smul r a _ ha => rw [map_smul, map_smul]; exact t.smul_mem r ha

lemma mem_right (hab : IsAbelianTangent (Fin.append Ls₁ Ls₂) t) (hs : Splits Ls₁ Ls₂ t)
    {z : Fin (p + q) → ℂ} (hz : z ∈ t) : inr₂ (pr₂ z) ∈ t := by
  have : inr₂ (pr₂ z) = z - inl₁ (pr₁ z) := by
    rw [eq_sub_iff_add_eq, add_comm (inr₂ _)]; exact (decomp _).symm
  rw [this]; exact t.sub_mem hz (mem_left hab hs hz)

/-- `(p, w) ↦ ((p, 0), (w, 0))`. -/
noncomputable abbrev E₁ : (Fin p → ℂ) × (Fin p → ℂ) →ₗ[ℂ] (Fin (p + q) → ℂ) × (Fin (p + q) → ℂ) :=
  LinearMap.prodMap inl₁ inl₁

/-- `(p, w) ↦ ((0, p), (0, w))`. -/
noncomputable abbrev E₂ : (Fin q → ℂ) × (Fin q → ℂ) →ₗ[ℂ] (Fin (p + q) → ℂ) × (Fin (p + q) → ℂ) :=
  LinearMap.prodMap inr₂ inr₂

lemma map_left_le : (perTanId Ls₁ (t.comap inl₁)).map E₁ ≤ perTanId (Fin.append Ls₁ Ls₂) t := by
  rw [perTanId, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨⟨l, e⟩, ⟨hlt, hl, he⟩, rfl⟩
  simp only at hlt hl he; subst he
  exact Submodule.subset_span ⟨hlt, lat_inl hl, (etaV_inl l).symm⟩

lemma map_right_le : (perTanId Ls₂ (t.comap inr₂)).map E₂ ≤ perTanId (Fin.append Ls₁ Ls₂) t := by
  rw [perTanId, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨⟨l, e⟩, ⟨hlt, hl, he⟩, rfl⟩
  simp only at hlt hl he; subst he
  exact Submodule.subset_span ⟨hlt, lat_inr hl, (etaV_inr l).symm⟩

lemma perTanId_le (hs : Splits Ls₁ Ls₂ t) : perTanId (Fin.append Ls₁ Ls₂) t ≤
    (perTanId Ls₁ (t.comap inl₁)).map E₁ ⊔ (perTanId Ls₂ (t.comap inr₂)).map E₂ := by
  rw [perTanId, Submodule.span_le]
  rintro ⟨l, e⟩ ⟨hlt, hl, he⟩
  simp only at hlt hl he; subst he
  have h1 : (pr₁ l, etaV Ls₁ (pr₁ l)) ∈ perTanId Ls₁ (t.comap inl₁) :=
    Submodule.subset_span ⟨hs l hlt hl, fun j => lat_left hl j, rfl⟩
  have h2 : (pr₂ l, etaV Ls₂ (pr₂ l)) ∈ perTanId Ls₂ (t.comap inr₂) :=
    Submodule.subset_span ⟨splits_right hs hlt hl, fun j => lat_right hl j, rfl⟩
  have : (l, etaV (Fin.append Ls₁ Ls₂) l) = E₁ (pr₁ l, etaV Ls₁ (pr₁ l)) +
      E₂ (pr₂ l, etaV Ls₂ (pr₂ l)) := by
    rw [etaV_decomp]
    refine Prod.ext ?_ rfl
    exact decomp l
  rw [SetLike.mem_coe, this]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem h1) (Submodule.mem_map_of_mem h2)

lemma algVec_inl {v : Fin p → ℂ} (hv : AlgVec v) : AlgVec (inl₁ (q := q) v) := by
  intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hv j
  · simpa using isAlgebraic_zero

lemma algVec_inr {v : Fin q → ℂ} (hv : AlgVec v) : AlgVec (inr₂ (p := p) v) := by
  intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using isAlgebraic_zero
  · simpa using hv j

end Reduce

/-- **`PerTanRat` for `E₁^p × E₂^q`** from the blocks, when abelian tangents split. -/
theorem perTanRat_append (hPT₁ : PerTanRat Ls₁) (hPT₂ : PerTanRat Ls₂)
    (hsplit : ∀ t, IsAbelianTangent (Fin.append Ls₁ Ls₂) t → Splits Ls₁ Ls₂ t) :
    PerTanRat (Fin.append Ls₁ Ls₂) := by
  intro t hab
  have hs := hsplit t hab
  set P := perTanId (Fin.append Ls₁ Ls₂) t
  apply le_antisymm
  · refine (perTanId_le hs).trans (sup_le ?_ ?_)
    · rw [hPT₁ _ (abel_left hab hs), Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨map_left_le (Submodule.mem_map_of_mem hw.1), algVec_inl hw.2.1, algVec_inl hw.2.2⟩
    · rw [hPT₂ _ (abel_right hab hs), Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨map_right_le (Submodule.mem_map_of_mem hw.1), algVec_inr hw.2.1, algVec_inr hw.2.2⟩
  · rw [Submodule.span_le]; exact fun w hw => hw.1

/-- **`LiftAlg` for `E₁^p × E₂^q`** from the blocks, when abelian tangents split. -/
theorem liftAlg_append (hLA₁ : LiftAlg Ls₁) (hLA₂ : LiftAlg Ls₂)
    (hsplit : ∀ t, IsAbelianTangent (Fin.append Ls₁ Ls₂) t → Splits Ls₁ Ls₂ t) :
    LiftAlg (Fin.append Ls₁ Ls₂) := by
  intro t hab z hz hgood
  have hs := hsplit t hab
  obtain ⟨w₁, hw₁, ha₁⟩ := hLA₁ (t.comap inl₁) (abel_left hab hs) (pr₁ z) (mem_left hab hs hz)
    (fun j => by simpa using hgood (Fin.castAdd q j))
  obtain ⟨w₂, hw₂, ha₂⟩ := hLA₂ (t.comap inr₂) (abel_right hab hs) (pr₂ z) (mem_right hab hs hz)
    (fun j => by simpa using hgood (Fin.natAdd p j))
  refine ⟨inl₁ w₁ + inr₂ w₂, ?_, fun i => ?_⟩
  · have : (z, inl₁ w₁ + inr₂ w₂) = E₁ (pr₁ z, w₁) + E₂ (pr₂ z, w₂) :=
      Prod.ext (decomp z) rfl
    rw [this]
    exact Submodule.add_mem _ (map_left_le (Submodule.mem_map_of_mem hw₁))
      (map_right_le (Submodule.mem_map_of_mem hw₂))
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [zetaV] using ha₁ j
    · simpa [zetaV] using ha₂ j

end LSG.CM
