import Mathlib
import LSG.MEV.SubgroupExp

/-!
# Classification of the Lie algebra of a closed subgroup of `G̃`

`H ⊆ G̃(ℂ)` a Zariski-closed subgroup, `T′ = lieAlg H ⊆ TanG = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^m`.
Notation: `HL = V × T_Λ` the linear subgroup (`LSG.MEV.SubgroupExp`), `U = qspan Λ ⊆ ℚ^{d₁}`,
`t = π_Z(T′) ⊆ ℂ^m` (base projection), `Γ = T′ ∩ (ℂ^{d₀} × 0 × 0 × ℂ^m)` (the vector part, as a
subspace of `ℂ^{d₀} × ℂ^m` via `vecIncl`).

* **`mem_lieAlg_lin_iff`**: `(a, b, 0, w) ∈ T′ ↔ (a, w) ∈ V ∧ b ⊥ Λ`. In particular
  (**`lin_mem_lieAlg_of_Htil`**) every vector `(a, 0, 0, w)` of `H̃` lies in `T′`: a Zariski-closed
  subgroup of the vector group `G_a^{d₀} × (fibres)` is a `ℂ`-subspace.
* **`eq_zero_of_lattice`** (as in `LSG.ME.ProductGraph`): a `ℂ`-linear form on `T′` vanishing on
  `T′ ∩ ker π_Z` with imaginary values at `π_Z⁻¹(Λ)` vanishes, *provided `t` is an abelian tangent*.
* **Torus splitting** (`torus_mem`, `torIncl_mem`, `sub_torIncl_mem`): `π_B(T′) = T′ ∩ B = U^⊥`.
* **`perTanId ⊆ T′`** (`per_mem_lieAlg`, `perTan_map_le`): for `λ ∈ t ∩ Λ`, `(0, 0, λ, η(λ)) ∈ T′`.
  (If `(a, 0, λ, s) ∈ T′`, then `(a, 0, 0, s − η(λ)) = (a, 0, λ, s) − (period) ∈ H̃` is a vector of the
  vector group, hence in `T′`.) No anti-affineness is needed for this inclusion.
* **`lieAlg_eq_tan`**: `T′ = Γ ⊕ U^⊥ ⊕ (perTanId t + …)`, precisely
  `T′ = vecIncl Γ ⊔ torIncl U^⊥ ⊔ g2Incl (perTan Ls 1 t)` — the tangent space of the VECEXT
  family member `T_U × (B̃^♮ + Γ)` (`SubgroupPreV.tan`), and **`exists_subgroupPreV`**.

The one analytic input taken as a hypothesis is **`IsAbelianTangent Ls t`** (`t = π_Z(T′)` is
spanned over `ℝ` by lattice vectors; in the abelian layer this is `isAbelianTangent_map_piA`, a
transcendence-degree count on `H⁰`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (IsAbelianTangent torusLie)
open LSG.W88.Vec (TanV PerV etaV vecIncl torIncl g2Incl perTanId perTan RatPair SubgroupDataV)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m r : ℕ}

/-! ### The family without rationality -/

/-- The data `(U, t, Γ)` of a member `T_U × (B̃ + Γ)` of the VECEXT family, without the
`ℚ̄`-rationality of `Γ` (not automatic over `ℂ`). -/
structure SubgroupPreV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) where
  /-- the character space of the toric part -/
  U : Submodule ℚ (Fin d₁ → ℚ)
  /-- the tangent space of the abelian image `B` -/
  t : Submodule ℂ (Fin m → ℂ)
  /-- the vector part, inside `G_a^{d₀} × (fibre)` -/
  gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))
  t_ab : IsAbelianTangent Ls t

namespace SubgroupPreV

variable {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-- `T_{G'} = Γ + U^⊥ + T_{B̃}` (as `SubgroupDataV.tan`). -/
def tan (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls M) : Submodule ℂ (TanV d₀ d₁ m r) :=
  S.gam.map vecIncl ⊔ (torusLie S.U).map torIncl ⊔ (perTan Ls M S.t).map g2Incl

/-- With a `ℚ̄`-rational `Γ`, a member of the family of `StatementVec`. -/
def toDataV (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls M) (h : RatPair S.gam) :
    SubgroupDataV (d0 := d₀) (d1 := d₁) Ls M :=
  { U := S.U, t := S.t, gam := S.gam, gam_rat := h, t_ab := S.t_ab }

theorem tan_toDataV (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls M) (h : RatPair S.gam) :
    (S.toDataV h).tan = S.tan := rfl

end SubgroupPreV

/-! ### Coordinates -/

/-- The base projection `π_Z(a, b, z, w) = z`. -/
def piZ : TanG d₀ d₁ m →ₗ[ℂ] (Fin m → ℂ) :=
  (LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))

@[simp] theorem piZ_apply (p : TanG d₀ d₁ m) : piZ p = p.2.2.1 := rfl

@[simp] theorem vecIncl_apply (x : (Fin d₀ → ℂ) × (Fin r → ℂ)) :
    (vecIncl x : TanV d₀ d₁ m r) = (x.1, 0, 0, x.2) := rfl

@[simp] theorem torIncl_apply (b : Fin d₁ → ℂ) :
    (torIncl b : TanV d₀ d₁ m r) = (0, b, 0, 0) := rfl

@[simp] theorem g2Incl_apply (x : (Fin m → ℂ) × (Fin r → ℂ)) :
    (g2Incl x : TanV d₀ d₁ m r) = (0, 0, x.1, x.2) := rfl

theorem perTan_one (Ls : Fin m → PeriodPair) (t : Submodule ℂ (Fin m → ℂ)) :
    perTan Ls 1 t = perTanId Ls t := by
  rw [perTan, Matrix.mulVecLin_one, LinearMap.prodMap_id, Submodule.map_id]

theorem fin_append_smul (c : ℂ) (a : Fin d₀ → ℂ) (w : Fin m → ℂ) :
    Fin.append (c • a) (c • w) = c • Fin.append a w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;> simp

variable {Ls : Fin m → PeriodPair} {H : Set (GPtV d₀ d₁ Ls)}

/-! ### The linear part of `T′` -/

section Lin

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **`(a, b, 0, w) ∈ T′ ↔ (a, w) ∈ V ∧ b ⊥ Λ`** (`HL = V × T_Λ`). -/
theorem mem_lieAlg_lin_iff {a : Fin d₀ → ℂ} {b : Fin d₁ → ℂ} {w : Fin m → ℂ} :
    ((a, b, 0, w) : TanG d₀ d₁ m) ∈ lieAlg Ls hH ↔
      Fin.append a w ∈ StrongSix.M2.linV (HL Ls H) ∧
        ∀ φ ∈ StrongSix.M2.latt (HL Ls H), ∑ j, (φ j : ℂ) * b j = 0 := by
  have hsm : ∀ c : ℂ, c • ((a, b, 0, w) : TanG d₀ d₁ m) = (c • a, c • b, 0, c • w) := fun c => by
    simp
  have hmem : ∀ c : ℂ, (expGV Ls (c • ((a, b, 0, w) : TanG d₀ d₁ m)) ∈ H ↔
      linPtV (c • a) (c • w) (c • b) ∈ StrongSix.M2.prodSet (StrongSix.M2.linV (HL Ls H))
        (StrongSix.M2.latt (HL Ls H))) := fun c => by
    rw [hsm, expGV_lin, ← HL_eq_prodSet hH hc]; rfl
  have hsum : ∀ (c : ℂ) (φ : Fin d₁ → ℤ), ∑ j, (φ j : ℂ) * (c • b) j = c * ∑ j, (φ j : ℂ) * b j :=
    fun c φ => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h
    refine ⟨?_, fun φ hφ => LSG.ME.eq_zero_of_forall_exp fun c => ?_⟩
    · have := ((hmem 1).mp (h 1)).1
      simpa [linPtV] using this
    · have := ((hmem c).mp (h c)).2 φ hφ
      change StrongSix.M2.chr (linPtV (c • a) (c • w) (c • b)).2 φ = 1 at this
      rwa [chr_linPtV, hsum] at this
  · rintro ⟨h1, h2⟩ c
    rw [mem_Htil, hmem]
    refine ⟨?_, fun φ hφ => ?_⟩
    · show Fin.append (c • a) (c • w) ∈ _
      rw [fin_append_smul]; exact Submodule.smul_mem _ c h1
    · rw [chr_linPtV, hsum, h2 φ hφ, mul_zero, Complex.exp_zero]

/-- **The vector part**: every vector `(a, 0, 0, w)` of `H̃` lies in `T′`. -/
theorem lin_mem_lieAlg_of_Htil {a : Fin d₀ → ℂ} {w : Fin m → ℂ}
    (h : ((a, 0, 0, w) : TanG d₀ d₁ m) ∈ Htil Ls hH) : ((a, 0, 0, w) : TanG d₀ d₁ m) ∈ lieAlg Ls hH := by
  rw [mem_lieAlg_lin_iff hH hc]
  refine ⟨?_, fun φ _ => by simp⟩
  have hL : linPtV a w 0 ∈ HL Ls H := by
    show inLin Ls _ ∈ H; rw [← expGV_lin]; exact h
  have := StrongSix.M2.subset_prodSet _ hL
  exact this.1

/-- The torus directions `U^⊥` lie in `T′`. -/
theorem torIncl_mem {b : Fin d₁ → ℂ}
    (hb : b ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H)))) :
    (torIncl b : TanG d₀ d₁ m) ∈ lieAlg Ls hH := by
  rw [torIncl_apply, mem_lieAlg_lin_iff hH hc, LSG.ME.mem_torusLie_qspan.symm]
  refine ⟨?_, hb⟩
  have : Fin.append (0 : Fin d₀ → ℂ) (0 : Fin m → ℂ) = 0 := by
    funext i; refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;> simp
  rw [this]; exact Submodule.zero_mem _

end Lin

/-! ### The real-span argument -/

/-- **A linear form with imaginary periods on `T` vanishes**, when `π_Z(T)` is an abelian tangent. -/
theorem eq_zero_of_lattice {T : Submodule ℂ (TanG d₀ d₁ m)}
    (hP : IsAbelianTangent Ls (T.map piZ)) (f : TanG d₀ d₁ m →ₗ[ℂ] ℂ)
    (h0 : ∀ u ∈ T, u.2.2.1 = 0 → f u = 0)
    (hΛ : ∀ u ∈ T, (∀ k, u.2.2.1 k ∈ (Ls k).lattice) → (f u).re = 0)
    {u : TanG d₀ d₁ m} (hu : u ∈ T) : f u = 0 := by
  set L0 := {z : Fin m → ℂ | z ∈ T.map piZ ∧ ∀ j, z j ∈ (Ls j).lattice}
  have hpre : ∀ z ∈ Submodule.span ℝ L0, ∃ v ∈ T, v.2.2.1 = z := by
    intro z hz
    have hz' : z ∈ T.map piZ := by
      rw [IsAbelianTangent] at hP
      rw [← hP] at hz
      exact hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz'
    exact ⟨v, hv, rfl⟩
  have hspan : ∀ v ∈ T, v.2.2.1 ∈ Submodule.span ℝ L0 := by
    intro v hv
    rw [IsAbelianTangent] at hP
    rw [← hP]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hre : ∀ z (hz : z ∈ Submodule.span ℝ L0), ∀ v ∈ T, v.2.2.1 = z → (f v).re = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => rintro v hv rfl; exact hΛ v hv hx.2
    | zero => intro v hv h; rw [h0 v hv h, Complex.zero_re]
    | add x y hx hy px py =>
      intro v hv h
      obtain ⟨v₁, hv₁, rfl⟩ := hpre _ hx
      have h2 : (v - v₁).2.2.1 = y := by
        simp only [Prod.snd_sub, Prod.fst_sub, h, add_sub_cancel_left]
      have := py (v - v₁) (T.sub_mem hv hv₁) h2
      rw [show v = v₁ + (v - v₁) by abel, map_add, Complex.add_re, px v₁ hv₁ rfl, this, add_zero]
    | smul a x hx px =>
      intro v hv h
      obtain ⟨v₁, hv₁, rfl⟩ := hpre _ hx
      have h2 : (v - (a : ℂ) • v₁).2.2.1 = 0 := by
        simp only [Prod.snd_sub, Prod.fst_sub, Prod.smul_snd, Prod.smul_fst, h, Complex.coe_smul,
          sub_self]
      have := h0 _ (T.sub_mem hv (T.smul_mem _ hv₁)) h2
      rw [show v = (a : ℂ) • v₁ + (v - (a : ℂ) • v₁) by abel, map_add, this, add_zero, map_smul,
        smul_eq_mul, Complex.re_ofReal_mul, px v₁ hv₁ rfl, mul_zero]
  have h1 : (f u).re = 0 := hre _ (hspan u hu) u hu rfl
  have h2 : (f (Complex.I • u)).re = 0 :=
    hre _ (hspan _ (T.smul_mem _ hu)) _ (T.smul_mem _ hu) rfl
  rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
  exact Complex.ext h1 (by simpa using h2)

/-! ### Torus splitting -/

/-- `u ↦ Σ φⱼ u₁ⱼ`. -/
def phiV (φ : Fin d₁ → ℤ) : TanG d₀ d₁ m →ₗ[ℂ] ℂ where
  toFun u := ∑ j, (φ j : ℂ) * u.2.1 j
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_left_comm]

theorem phiV_apply (φ : Fin d₁ → ℤ) (u : TanG d₀ d₁ m) : phiV φ u = ∑ j, (φ j : ℂ) * u.2.1 j :=
  rfl

section Split

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
  (hab : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ))
include hc hab

/-- **`π_B(T′) ⊆ U^⊥`.** -/
theorem torus_mem {v : TanG d₀ d₁ m} (hv : v ∈ lieAlg Ls hH) :
    v.2.1 ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H))) := by
  rw [LSG.ME.mem_torusLie_qspan]
  intro φ hφ
  refine eq_zero_of_lattice hab (phiV φ) (fun u hu h => ?_) (fun u hu hl => ?_) hv
  · have hu' : u = ((u.1, u.2.1, 0, u.2.2.2) : TanG d₀ d₁ m) := by
      ext <;> simp [h]
    rw [hu'] at hu
    exact ((mem_lieAlg_lin_iff hH hc).mp hu).2 φ hφ
  · have hm : expGV Ls u ∈ H := lieAlg_le_Htil hu
    rw [expGV_of_lattice hl] at hm
    have := (StrongSix.M2.subset_prodSet _ (show _ ∈ HL Ls H from hm)).2 φ hφ
    rw [chr_linPtV] at this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp this
    rw [phiV_apply, hn]
    simp

/-- The torus part of a vector of `T′` lies in `T′`. -/
theorem torIncl_mem_of {v : TanG d₀ d₁ m} (hv : v ∈ lieAlg Ls hH) :
    (torIncl v.2.1 : TanG d₀ d₁ m) ∈ lieAlg Ls hH :=
  torIncl_mem hH hc (torus_mem hH hc hab hv)

theorem sub_torIncl_mem {v : TanG d₀ d₁ m} (hv : v ∈ lieAlg Ls hH) :
    v - torIncl v.2.1 ∈ lieAlg Ls hH :=
  (lieAlg Ls hH).sub_mem hv (torIncl_mem_of hH hc hab hv)

/-- **`T′ ∩ B = U^⊥`**, `U = qspan Λ`. -/
theorem lieAlg_comap_torIncl :
    (lieAlg Ls hH).comap torIncl = torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H))) := by
  ext b
  rw [Submodule.mem_comap]
  refine ⟨fun h => ?_, fun h => torIncl_mem hH hc h⟩
  simpa using torus_mem hH hc hab h

/-! ### `perTanId(t) ⊆ T′` -/

/-- **The periods over `t` lie in `T′`**: for `λ ∈ t ∩ Λ`, `(0, 0, λ, η(λ)) ∈ T′`. -/
theorem per_mem_lieAlg {l : Fin m → ℂ} (hl : l ∈ (lieAlg Ls hH).map piZ)
    (hΛ : ∀ k, l k ∈ (Ls k).lattice) :
    ((0, 0, l, etaV Ls l) : TanG d₀ d₁ m) ∈ lieAlg Ls hH := by
  obtain ⟨v, hv, hvl⟩ := Submodule.mem_map.mp hl
  rw [piZ_apply] at hvl
  set v' := v - torIncl v.2.1 with hv'
  have hv'T := sub_torIncl_mem hH hc hab hv
  have hper : ((0, 0, l, etaV Ls l) : TanG d₀ d₁ m) ∈ PerV Ls 1 :=
    ⟨rfl, fun _ => ⟨0, by simp⟩, hΛ, (Matrix.one_mulVec _).symm⟩
  have hd : ((v.1, 0, 0, v.2.2.2 - etaV Ls l) : TanG d₀ d₁ m) ∈ lieAlg Ls hH := by
    refine lin_mem_lieAlg_of_Htil hH hc ?_
    have : ((v.1, 0, 0, v.2.2.2 - etaV Ls l) : TanG d₀ d₁ m) =
        v' - ((0, 0, l, etaV Ls l) : TanG d₀ d₁ m) := by
      ext <;> simp [hv', hvl]
    rw [this]
    exact (Htil Ls hH).sub_mem (lieAlg_le_Htil hv'T) (per_le_Htil hH hper)
  have : ((0, 0, l, etaV Ls l) : TanG d₀ d₁ m) =
      v' - ((v.1, 0, 0, v.2.2.2 - etaV Ls l) : TanG d₀ d₁ m) := by
    ext <;> simp [hv', hvl]
  rw [this]
  exact (lieAlg Ls hH).sub_mem hv'T hd

/-- **`T_{B̃^♮} = g2Incl (perTanId t) ⊆ T′`.** -/
theorem perTan_map_le :
    (perTan Ls 1 ((lieAlg Ls hH).map piZ)).map g2Incl ≤ lieAlg Ls hH := by
  rw [perTan_one, Submodule.map_le_iff_le_comap, perTanId, Submodule.span_le]
  rintro ⟨l, s⟩ ⟨hl, hΛ, hs⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, g2Incl_apply]
  simp only at hs ⊢
  rw [hs]
  exact per_mem_lieAlg hH hc hab hl hΛ

end Split

/-! ### The decomposition -/

/-- Over an abelian tangent `t`, every `z ∈ t` has a lift `(z, w) ∈ perTanId t`. -/
theorem exists_perTanId {t : Submodule ℂ (Fin m → ℂ)} (ht : IsAbelianTangent Ls t) {z : Fin m → ℂ}
    (hz : z ∈ t) : ∃ w, (z, w) ∈ perTanId Ls t := by
  have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin m → ℂ)) := hz
  rw [ht] at hz'
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx => exact ⟨etaV Ls x, Submodule.subset_span ⟨hx.1, hx.2, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ px py =>
    obtain ⟨w₁, h₁⟩ := px
    obtain ⟨w₂, h₂⟩ := py
    exact ⟨w₁ + w₂, by simpa using Submodule.add_mem _ h₁ h₂⟩
  | smul a x _ px =>
    obtain ⟨w, h⟩ := px
    refine ⟨(a : ℂ) • w, ?_⟩
    have := Submodule.smul_mem _ (a : ℂ) h
    simpa [Complex.coe_smul] using this

section Decomp

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
  (hab : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ))
include hc hab

/-- **The classification**: `T′ = vecIncl Γ ⊔ torIncl U^⊥ ⊔ g2Incl (perTanId t)`, with
`Γ = T′ ∩ (vector group)`, `U = qspan Λ`, `t = π_Z(T′)`. -/
theorem lieAlg_eq_tan :
    lieAlg Ls hH =
      ((lieAlg Ls hH).comap vecIncl).map vecIncl ⊔
        (torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H)))).map torIncl ⊔
        (perTan Ls 1 ((lieAlg Ls hH).map piZ)).map g2Incl := by
  set T := lieAlg Ls hH
  refine le_antisymm (fun v hv => ?_) (sup_le (sup_le (Submodule.map_comap_le _ _) ?_)
    (perTan_map_le hH hc hab))
  · -- the decomposition of a vector
    have hz : v.2.2.1 ∈ T.map piZ := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    obtain ⟨w, hw⟩ := exists_perTanId hab hz
    have hg : (g2Incl (v.2.2.1, w) : TanG d₀ d₁ m) ∈ T := by
      refine perTan_map_le hH hc hab (Submodule.mem_map.mpr ⟨(v.2.2.1, w), ?_, rfl⟩)
      rwa [perTan_one]
    have hvec : (vecIncl (v.1, v.2.2.2 - w) : TanG d₀ d₁ m) ∈ T := by
      have : (vecIncl (v.1, v.2.2.2 - w) : TanG d₀ d₁ m) =
          (v - torIncl v.2.1) - g2Incl (v.2.2.1, w) := by
        ext <;> simp
      rw [this]
      exact T.sub_mem (sub_torIncl_mem hH hc hab hv) hg
    have hsplit : v = vecIncl (v.1, v.2.2.2 - w) + torIncl v.2.1 + g2Incl (v.2.2.1, w) := by
      ext <;> simp
    rw [hsplit]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ?_) ?_
    · exact Submodule.mem_map.mpr ⟨_, hvec, rfl⟩
    · exact Submodule.mem_map.mpr ⟨_, torus_mem hH hc hab hv, rfl⟩
    · refine Submodule.mem_map.mpr ⟨(v.2.2.1, w), ?_, rfl⟩
      rwa [perTan_one]
  · rintro _ ⟨b, hb, rfl⟩
    exact torIncl_mem hH hc hb

/-- **Packaging**: `T′` is the tangent space of a member of the VECEXT family (without
`ℚ̄`-rationality of `Γ`). -/
theorem exists_subgroupPreV :
    ∃ S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls 1, S.tan = lieAlg Ls hH ∧
      S.U = StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H)) ∧
      S.t = (lieAlg Ls hH).map piZ ∧ S.gam = (lieAlg Ls hH).comap vecIncl :=
  ⟨{ U := _, t := _, gam := _, t_ab := hab }, (lieAlg_eq_tan hH hc hab).symm, rfl, rfl, rfl⟩

end Decomp

end

end LSG.MEV
