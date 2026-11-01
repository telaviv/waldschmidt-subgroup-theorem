/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Block

/-!
# Vector-extension blocks: the interface of the multiplicity estimate `LSG.MEBV` (M2.md §M2.4a, frozen)

A **vector-extension block** is a commutative algebraic group `B^♮`, an extension of a complex torus
`A = ℂ^g ⧸ per` (an `AbBlock`, the *base*) by one `G_a`, given analytically by an entire lift
`(z, w) ↦ (θ(z), T(z, w))` with values in a projective model in `ℙ^{N + nT − 1}`. The coordinates are
`X_c` (`c : Fin N`, the base model) and `T_t` (`t : Fin nT`, the fibre coordinates). Each fibre coordinate is
attached to a base coordinate `X_{fc t}`, and the lift is linear in the fibre variable `w`:

  `T_t(z, w) = θ_{fc t}(z) · w − Φ(z)_t`   (`Φ` entire), so `∂_w T_t = X_{fc t}`.

For `A_σ̄^♮` (M2): `N = 9`, `nT = 3`, `fc = ![0, 4, 8]`, `Φ(z)_t = ⅓ ∂₀θ_{fc t}(z) − θ_{fc t}(z) ℓ(z)`
(`LSG.JacAn.ThetaData.fibT`), `η = etaB`.

The block is described *semantically*, as `AbBlock` is. Compared with `AbBlock`, the five corrections of the M2.1
spike (M2.md §M2.1.0) are built in:
* **X-only slicing**: the B5 cover `lci_cover` is over the `X`-variables only (the model is not a local complete
  intersection on the irrelevant locus `{X = 0}`); the core slices with forms in the `X`-variables.
* **Hilbert certificate with linear forms**: `hilb_l` is a tuple of `g + 2` linear forms (A-block:
  `(T₀, T₄, T₈, X₀ + X₄ + X₈)`, `hilb_deg = 41`, certified in `LSG/Jac/B6V.lean`; M2.md §M2.4b), not of variables.
* **Fibre flows only for `T_{t}` in its own chart `fc t`** (`WT`, `T_flow`, quadrics in `X`); the other `T_{t'}`
  are eliminated by the Plücker relations `plk`/`T_plk`.
* **`gens` need not generate a saturated ideal** (the A-block's `J_V` misses one cubic `F` supported on `{X = 0}`):
  nothing here asks for it. Surjectivity `surjV` is required only off `{X = 0}`.
* **`τ₀ = 0`** (the identity's fibre coordinate) is *not* a field: the core does not use it. It belongs to the
  M2.6 Taylor package and is proved from `lawV` at the identity.

Not fields, because they are derivable (M2.5 core lemmas): the kernel of the lift (`lift_ker` below), the
additivity of `η` (`η_add`), the local coordinates `(θ_{is}/θ_{i₀}, T_{t₀}/θ_{i₀})` at `0` (block-triangular
Jacobian from `base.coords_locInv`), `∂_w T_t = X_{fc t}`. Anti-affineness (`span_ℂ perV = ⊤`, M2.md N6) is
not a field either: the multiplicity estimate holds for every commutative group (the sanity instance is `G_a`), and
only the consumer/engine needs it.

Only rank-one fibres (`w : ℂ`) are covered; `A_σ̄^♮` and `E^♮` are of this kind.

* `fibOf`, `liftOf`, `gensOf`: the raw shapes used by the fields.
* `biWV`, `evalLawV`, `lformV`: bidegree weights, law evaluation and linear forms over an arbitrary index type.
* `VBlock`: the structure. Derived: `VBlock.Idx`, `T`, `lift`, `gens`, `exists_fc_ne`, `snd_eq_of_lift`, `η_add`,
  `perV`, `lift_add_perV`, `lift_ker`.
-/

open MvPolynomial

namespace LSG.MEBV

open LSG.MEB (AbBlock)

/-! ### Raw shapes -/

/-- The fibre coordinates `T_t(z, w) = θ_{fc t}(z) w − Φ(z)_t`. -/
def fibOf {g N nT : ℕ} (θ : (Fin g → ℂ) → Fin N → ℂ) (fc : Fin nT → Fin N)
    (Φ : (Fin g → ℂ) → Fin nT → ℂ) (z : Fin g → ℂ) (w : ℂ) : Fin nT → ℂ :=
  fun t => θ z (fc t) * w - Φ z t

/-- The lift `(z, w) ↦ (θ(z), T(z, w))` of the exponential of `B^♮`. -/
def liftOf {g N nT : ℕ} (θ : (Fin g → ℂ) → Fin N → ℂ) (fc : Fin nT → Fin N)
    (Φ : (Fin g → ℂ) → Fin nT → ℂ) (p : (Fin g → ℂ) × ℂ) : Fin N ⊕ Fin nT → ℂ :=
  Sum.elim (θ p.1) (fibOf θ fc Φ p.1 p.2)

/-- The generators of the explicit ideal: the base generators (in the `X`-variables) and the fibre ones. -/
noncomputable def gensOf {N nT : ℕ} (gensA : List (MvPolynomial (Fin N) ℂ))
    (gensT : List (MvPolynomial (Fin N ⊕ Fin nT) ℂ)) : List (MvPolynomial (Fin N ⊕ Fin nT) ℂ) :=
  gensA.map (rename Sum.inl) ++ gensT

/-- The bidegree weights on the variables `ι ⊕ ι` of an addition law. -/
def biWV (ι : Type*) : ι ⊕ ι → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

/-- The value of a law `L = (L_k)_k` at `(X, Y)`. -/
noncomputable def evalLawV {ι : Type*} (L : ι → MvPolynomial (ι ⊕ ι) ℂ) (X Y : ι → ℂ) : ι → ℂ :=
  fun k => eval (Sum.elim X Y) (L k)

/-- The linear form `Σ_c α_c X_c`. -/
noncomputable def lformV {ι : Type*} [Fintype ι] (α : ι → ℂ) : MvPolynomial ι ℂ := ∑ c, C (α c) * X c

/-! ### The structure -/

/-- **A vector-extension block** `B^♮` over an abelian block (M2.md §M2.4a). -/
structure VBlock where
  /-- the base abelian block `A` (A-block: `LSG.JacBlock.aBlock`) -/
  base : AbBlock
  /-- the number of fibre coordinates (A-block: 3) -/
  nT : ℕ
  /-- `T_t` is attached to `X_{fc t}` (A-block: `![0, 4, 8]`) -/
  fc : Fin nT → Fin base.N
  /-- every chart of the base carries a fibre coordinate -/
  fc_charts : ∀ c ∈ base.charts, ∃ t, fc t = c
  -- The explicit model (coordinates `X_c`, `T_t`)
  /-- the fibre generators (A-block: the three Plücker quadrics `P₀₄, P₀₈, P₄₈`) -/
  gensT : List (MvPolynomial (Fin base.N ⊕ Fin nT) ℂ)
  gensT_hom : ∀ Q ∈ gensT, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d
  -- Uniformisation of the fibre
  /-- the entire correction `Φ` in `T_t(z, w) = θ_{fc t}(z) w − Φ(z)_t` -/
  Φ : (Fin base.g → ℂ) → Fin nT → ℂ
  Φ_analytic : ∀ z, AnalyticAt ℂ Φ z
  liftT_model : ∀ p : (Fin base.g → ℂ) × ℂ, ∀ Q ∈ gensT, eval (liftOf base.θ fc Φ p) Q = 0
  /-- the fibre periods: `(ω, η ω)`, `ω ∈ per`, are the periods of `B^♮` (A-block: `etaB`) -/
  η : (Fin base.g → ℂ) → ℂ
  lift_per : ∀ ω ∈ base.per, ∀ p : (Fin base.g → ℂ) × ℂ, ∃ c : ℂ, c ≠ 0 ∧
    liftOf base.θ fc Φ (p + (ω, η ω)) = c • liftOf base.θ fc Φ p
  -- Surjectivity off the irrelevant locus `{X = 0}`
  surjV : ∀ Y : Fin base.N ⊕ Fin nT → ℂ, (fun c => Y (Sum.inl c)) ≠ 0 →
    (∀ Q ∈ gensOf base.gens gensT, eval Y Q = 0) →
    ∃ (p : (Fin base.g → ℂ) × ℂ) (c : ℂ), Y = c • liftOf base.θ fc Φ p
  -- Addition laws on `(X, T)`, correct and complete on the image
  /-- the number of laws (A-block: 81, indexed by `(m, c, c′)`) -/
  nLV : ℕ
  /-- the bidegree of the laws (A-block: 3) -/
  ld : ℕ
  lawV : Fin nLV → Fin base.N ⊕ Fin nT →
    MvPolynomial ((Fin base.N ⊕ Fin nT) ⊕ (Fin base.N ⊕ Fin nT)) ℂ
  lawV_hom : ∀ i k, (lawV i k).IsWeightedHomogeneous (biWV (Fin base.N ⊕ Fin nT)) (ld, ld)
  lawV_eq : ∀ i (p q : (Fin base.g → ℂ) × ℂ), ∃ κ : ℂ,
    evalLawV (lawV i) (liftOf base.θ fc Φ p) (liftOf base.θ fc Φ q) = κ • liftOf base.θ fc Φ (p + q)
  lawV_complete : ∀ p q : (Fin base.g → ℂ) × ℂ, ∃ i,
    evalLawV (lawV i) (liftOf base.θ fc Φ p) (liftOf base.θ fc Φ q) ≠ 0
  -- Fibre flows: `T_t` in its own chart `fc t` only
  /-- the flow of `T_t` in the chart `X_{fc t} = 1`, direction `j` (A-block: `⅓ Q_{fc t, j0}`, Lemma K♮) -/
  WT : Fin nT → Fin base.g → MvPolynomial (Fin base.N) ℂ
  WT_hom : ∀ t j, (WT t j).IsHomogeneous 2
  /-- `θ_c ∂_jT_t − T_t ∂_jθ_c = WT_{tj}(θ)`, `c = fc t` (A-block: `ThetaData.fibT_flow`) -/
  T_flow : ∀ t, fc t ∈ base.charts → ∀ (j : Fin base.g) (z : Fin base.g → ℂ) (w : ℂ),
    base.θ z (fc t) * fderiv ℂ (fun z' => fibOf base.θ fc Φ z' w t) z (Pi.single j 1) -
        fibOf base.θ fc Φ z w t * fderiv ℂ base.θ z (Pi.single j 1) (fc t) =
      eval (base.θ z) (WT t j)
  -- Plücker relations (elimination of `T_{t′}` in the chart `fc t`)
  /-- `X_{fc t} T_{t′} − X_{fc t′} T_t = plk_{t t′}(X)` on the image (A-block: `−⅓ W^{(fc t)}_{0, fc t′}`) -/
  plk : Fin nT → Fin nT → MvPolynomial (Fin base.N) ℂ
  plk_hom : ∀ t t', (plk t t').IsHomogeneous 2
  /-- A-block: `ThetaData.fibT_plucker` -/
  T_plk : ∀ (t t' : Fin nT) (z : Fin base.g → ℂ) (w : ℂ),
    base.θ z (fc t) * fibOf base.θ fc Φ z w t' - base.θ z (fc t') * fibOf base.θ fc Φ z w t =
      eval (base.θ z) (plk t t')
  -- The fibre coordinate at the identity: `(θ_{is}/θ_{i₀}, T_{t₀}/θ_{i₀})` are local coordinates at `0`
  t₀ : Fin nT
  fc_t₀ : fc t₀ = base.i₀
  -- B6: Hilbert certificate `S_n = (ℓ_0, …, ℓ_{g+1})·S_{n−1} + I_n` for `n = hilb_deg`, `ℓ_a` linear forms
  hilb_l : Fin (base.g + 2) → Fin base.N ⊕ Fin nT → ℂ
  hilb_deg : ℕ
  hilb : ∀ M : MvPolynomial (Fin base.N ⊕ Fin nT) ℂ, M.IsHomogeneous hilb_deg →
    M ∈ Ideal.span {Q | Q ∈ gensOf base.gens gensT} ⊔ Ideal.span (Set.range fun a => lformV (hilb_l a))
  -- B5: local complete intersection in projective form, with an `X`-only cover
  lci_s : ℕ
  lci_S : Fin lci_s → MvPolynomial (Fin base.N ⊕ Fin nT) ℂ
  lci_F : Fin lci_s → List (MvPolynomial (Fin base.N ⊕ Fin nT) ℂ)
  lci_len : ∀ i, (lci_F i).length + (base.g + 1) + 1 = base.N + nT
  lci_F_le : ∀ i, Ideal.ofList (lci_F i) ≤ Ideal.span {Q | Q ∈ gensOf base.gens gensT}
  lci_mem : ∀ i, ∀ Q ∈ gensOf base.gens gensT, lci_S i * Q ∈ Ideal.ofList (lci_F i)
  lci_cover : ∀ v : Fin base.N, ∃ e : ℕ,
    (X (Sum.inl v) : MvPolynomial (Fin base.N ⊕ Fin nT) ℂ) ^ e ∈
      Ideal.span {Q | Q ∈ gensOf base.gens gensT} ⊔ Ideal.span (Set.range lci_S)

namespace VBlock

variable (b : VBlock)

/-- The dimension of the base. -/
abbrev g : ℕ := b.base.g

/-- The number of base coordinates. -/
abbrev N : ℕ := b.base.N

/-- The coordinates `X_c` (`inl c`) and `T_t` (`inr t`) of the model. -/
abbrev Idx : Type := Fin b.base.N ⊕ Fin b.nT

/-- The fibre coordinates `T_t(z, w)`. -/
def T (z : Fin b.g → ℂ) (w : ℂ) : Fin b.nT → ℂ := fibOf b.base.θ b.fc b.Φ z w

/-- **The lift** `(z, w) ↦ (θ(z), T(z, w))`. -/
def lift (p : (Fin b.g → ℂ) × ℂ) : b.Idx → ℂ := liftOf b.base.θ b.fc b.Φ p

/-- The explicit generators. -/
noncomputable def gens : List (MvPolynomial b.Idx ℂ) := gensOf b.base.gens b.gensT

@[simp] theorem lift_inl (p : (Fin b.g → ℂ) × ℂ) (c : Fin b.N) :
    b.lift p (Sum.inl c) = b.base.θ p.1 c := rfl

@[simp] theorem lift_inr (p : (Fin b.g → ℂ) × ℂ) (t : Fin b.nT) :
    b.lift p (Sum.inr t) = b.base.θ p.1 (b.fc t) * p.2 - b.Φ p.1 t := rfl

theorem T_apply (z : Fin b.g → ℂ) (w : ℂ) (t : Fin b.nT) :
    b.T z w t = b.base.θ z (b.fc t) * w - b.Φ z t := rfl

/-- `T` is affine in `w` with slope `θ_{fc t}`. -/
theorem T_add (z : Fin b.g → ℂ) (w s : ℂ) (t : Fin b.nT) :
    b.T z (w + s) t = b.T z w t + s * b.base.θ z (b.fc t) := by
  simp only [T_apply]; ring

theorem lift_ne_zero (p : (Fin b.g → ℂ) × ℂ) : b.lift p ≠ 0 := fun h =>
  b.base.θ_ne p.1 (funext fun c => by simpa using congrFun h (Sum.inl c))

theorem mem_gens {Q : MvPolynomial b.Idx ℂ} :
    Q ∈ b.gens ↔ (∃ Q' ∈ b.base.gens, rename Sum.inl Q' = Q) ∨ Q ∈ b.gensT := by
  simp [gens, gensOf]

theorem gens_hom : ∀ Q ∈ b.gens, ∃ d, 1 ≤ d ∧ Q.IsHomogeneous d := by
  intro Q hQ
  rcases b.mem_gens.mp hQ with ⟨Q', hQ', rfl⟩ | hQ
  · obtain ⟨d, hd, h⟩ := b.base.gens_hom Q' hQ'
    exact ⟨d, hd, h.rename_isHomogeneous⟩
  · exact b.gensT_hom Q hQ

/-- **The lift lands on the model.** -/
theorem lift_model (p : (Fin b.g → ℂ) × ℂ) : ∀ Q ∈ b.gens, eval (b.lift p) Q = 0 := by
  intro Q hQ
  rcases b.mem_gens.mp hQ with ⟨Q', hQ', rfl⟩ | hQ
  · rw [eval_rename]
    exact b.base.θ_model p.1 Q' hQ'
  · exact b.liftT_model p Q hQ

/-! ### The fibre periods -/

/-- At every point some fibre coordinate's base coordinate is nonzero. -/
theorem exists_fc_ne (z : Fin b.g → ℂ) : ∃ t, b.base.θ z (b.fc t) ≠ 0 := by
  obtain ⟨c, hc, hne⟩ := b.base.chart_cover (b.base.θ z) (b.base.θ_ne z) (b.base.θ_model z)
  obtain ⟨t, rfl⟩ := b.fc_charts c hc
  exact ⟨t, hne⟩

/-- Two lifts over the same base point that are proportional to the same vector have the same fibre
coordinate. -/
theorem snd_eq_of_lift {z : Fin b.g → ℂ} {w w' c c' : ℂ} {L : b.Idx → ℂ}
    (h : b.lift (z, w) = c • L) (h' : b.lift (z, w') = c' • L) : w = w' := by
  obtain ⟨t, ht⟩ := b.exists_fc_ne z
  have e1 := congrFun h (Sum.inl (b.fc t))
  have e1' := congrFun h' (Sum.inl (b.fc t))
  have e2 := congrFun h (Sum.inr t)
  have e2' := congrFun h' (Sum.inr t)
  simp only [lift_inl, lift_inr, Pi.smul_apply, smul_eq_mul] at e1 e1' e2 e2'
  have hL : L (Sum.inl (b.fc t)) ≠ 0 := fun h0 => ht (by rw [e1, h0, mul_zero])
  have hc : c = c' := mul_right_cancel₀ hL (e1.symm.trans e1')
  subst hc
  have : b.base.θ z (b.fc t) * (w - w') = 0 := by linear_combination e2 - e2'
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht)

/-- **`η` is additive on the periods** (derived from `lift_per`). -/
theorem η_add {ω ω' : Fin b.g → ℂ} (hω : ω ∈ b.base.per) (hω' : ω' ∈ b.base.per) :
    b.η (ω + ω') = b.η ω + b.η ω' := by
  obtain ⟨c₁, -, h1⟩ := b.lift_per ω hω 0
  obtain ⟨c₂, -, h2⟩ := b.lift_per ω' hω' (0 + (ω, b.η ω))
  obtain ⟨c₃, -, h3⟩ := b.lift_per (ω + ω') (b.base.per.add_mem hω hω') 0
  change b.lift _ = _ • b.lift _ at h1 h2 h3
  rw [h1, smul_smul] at h2
  have e : (0 + (ω, b.η ω) + (ω', b.η ω') : (Fin b.g → ℂ) × ℂ) = (ω + ω', b.η ω + b.η ω') := by
    ext <;> simp
  have e3 : (0 + (ω + ω', b.η (ω + ω')) : (Fin b.g → ℂ) × ℂ) = (ω + ω', b.η (ω + ω')) := zero_add _
  rw [e] at h2
  rw [e3] at h3
  exact b.snd_eq_of_lift h3 h2

theorem η_zero : b.η 0 = 0 := by
  have h := b.η_add b.base.per.zero_mem b.base.per.zero_mem
  rw [add_zero] at h
  linear_combination -h

theorem η_neg {ω : Fin b.g → ℂ} (hω : ω ∈ b.base.per) : b.η (-ω) = -b.η ω := by
  have h := b.η_add hω (b.base.per.neg_mem hω)
  rw [add_neg_cancel, b.η_zero] at h
  linear_combination -h

/-- **The periods of `B^♮`**: `{(ω, η ω) : ω ∈ per}`. -/
def perV : AddSubgroup ((Fin b.g → ℂ) × ℂ) where
  carrier := {p | p.1 ∈ b.base.per ∧ p.2 = b.η p.1}
  add_mem' {p q} hp hq := by
    refine ⟨b.base.per.add_mem hp.1 hq.1, ?_⟩
    change p.2 + q.2 = b.η (p.1 + q.1)
    rw [b.η_add hp.1 hq.1, hp.2, hq.2]
  zero_mem' := ⟨b.base.per.zero_mem, b.η_zero.symm⟩
  neg_mem' {p} hp := by
    refine ⟨b.base.per.neg_mem hp.1, ?_⟩
    change -p.2 = b.η (-p.1)
    rw [b.η_neg hp.1, hp.2]

theorem mem_perV {p : (Fin b.g → ℂ) × ℂ} : p ∈ b.perV ↔ p.1 ∈ b.base.per ∧ p.2 = b.η p.1 := Iff.rfl

/-- Translation by a period rescales the lift. -/
theorem lift_add_perV {π : (Fin b.g → ℂ) × ℂ} (hπ : π ∈ b.perV) (p : (Fin b.g → ℂ) × ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ b.lift (p + π) = c • b.lift p := by
  have e : π = (π.1, b.η π.1) := Prod.ext rfl hπ.2
  rw [e]
  exact b.lift_per π.1 hπ.1 p

/-- **The kernel of the lift** (derived from `base.θ_ker` and `lift_per`). -/
theorem lift_ker (p q : (Fin b.g → ℂ) × ℂ) (h : ∃ c : ℂ, b.lift q = c • b.lift p) :
    q - p ∈ b.perV := by
  obtain ⟨c, hc⟩ := h
  have hθ : b.base.θ q.1 = c • b.base.θ p.1 := funext fun k => by
    simpa using congrFun hc (Sum.inl k)
  have hω : q.1 - p.1 ∈ b.base.per := b.base.θ_ker p.1 q.1 ⟨c, hθ⟩
  obtain ⟨c', -, h'⟩ := b.lift_per _ hω p
  change b.lift _ = _ • b.lift _ at h'
  have e : p + (q.1 - p.1, b.η (q.1 - p.1)) = (q.1, p.2 + b.η (q.1 - p.1)) := by
    ext <;> simp
  rw [e] at h'
  have hq : b.lift (q.1, q.2) = c • b.lift p := hc
  have h2 := b.snd_eq_of_lift hq h'
  refine ⟨hω, ?_⟩
  change q.2 - p.2 = b.η (q.1 - p.1)
  rw [h2]; ring

end VBlock

end LSG.MEBV
