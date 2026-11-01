/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVDeg
import LSG.W88.Sec7Rat
import LSG.ME.MainAbAux

/-!
# M2.6.8c: from the obstruction on `G̃_r` to a `ℚ̄`-rational member of `SubgroupDataAV`

For `O : ObstrDataBV d₀ r d₁ B M` (`T̃′ = O.tan ⊇ K_M`) and `T′ = pushTA(T̃′)` (`tanG O`):

* `tan_eq_comap`, `liftTA_mem_tan`, **`t0_eq`**, **`t2_eq`** (`O.t2 = t2G O + m`, `M` onto not needed: `kvec` is
  injective), **`tau_eq`**.
* `tanAV gam U t` (the tangent space of a member, any `gam`), `map_fst_tanAV`, **`finrank_tanAV`**
  (`dim = dim pr₀ Γ + dim U^⊥ + t₂`).
* **`exists_perTanId`** (from `IsRatSub (perBase B) t`), **`decomp_tanG`**, **`tanG_eq`**
  (`T′ = tanAV Γ_full U t`).
* **`exists_subgroupDataAV_rat`** (`r ≤ 1`): `H″ = (U, t, Γ″)`, `Γ″` the span of the algebraic vectors of `Γ_full`,
  has the same `λ` (points of `LamAV` have base parts in `lat`, so no `LiftAlg`: `mem_dataRat_of_lam`), the same
  `δ₁, δ₂` and `δ″ − τ″ ≥ δ − τ`.
-/

open MvPolynomial Module Finset LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88.AVS

open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock ObstrDataBV kerK kvec prLead prB tanOfV vecIncl torIncl g2Incl perTanId perBase)
open LSG.W88.Vec (RatPair AlgPair)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### Projections and members -/

/-- The projection to `ℂ^{d₀}`. -/
def prAA : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.fst ℂ _ _

/-- The projection to the toric coordinates. -/
def prBA : TanAV d₀ d₁ r B →ₗ[ℂ] (Fin d₁ → ℂ) := (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)

variable (B) in
/-- The tangent space `Γ + U^⊥ + T_{B̃}` of a member (any `Γ`). -/
def tanAV (M : Matrix (Fin r) (Fin m) ℂ) (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ)))
    (U : Submodule ℚ (Fin d₁ → ℚ)) (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Submodule ℂ (TanAV d₀ d₁ r B) :=
  gam.map vecInclA ⊔ (torusLie U).map torInclA ⊔ (perTanA B M t).map g2InclA

theorem SubgroupDataAV.tan_eq_tanAV (H : SubgroupDataAV d₀ d₁ B M) : H.tan = tanAV B M H.gam H.U H.t := rfl

theorem map_eq_bot_of_le_kerA {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F]
    [Module ℂ F] {f : E →ₗ[ℂ] F} {p : Submodule ℂ E} (h : p ≤ LinearMap.ker f) : p.map f = ⊥ := by
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_bot]
  exact h hx

section Member

variable (gam : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))) (U : Submodule ℚ (Fin d₁ → ℚ))
  (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ))

/-- `Γ + T_{B̃}`. -/
def tanVA : Submodule ℂ (TanAV d₀ d₁ r B) := gam.map vecInclA ⊔ (perTanA B M t).map g2InclA

theorem tanAV_eq : tanAV B M gam U t = (torusLie U).map torInclA ⊔ tanVA (M := M) gam t := by
  rw [tanAV, tanVA]; ac_rfl

theorem tanVA_le_ker_prBA : tanVA (M := M) (d₁ := d₁) gam t ≤ LinearMap.ker prBA := by
  refine sup_le ?_ ?_ <;> rintro _ ⟨x, -, rfl⟩ <;> rfl

theorem tor_le_ker_prAA : (torusLie U).map torInclA ≤ LinearMap.ker (prAA (d₀ := d₀) (r := r) (B := B)) := by
  rintro _ ⟨x, -, rfl⟩; rfl

theorem map_prAA_tanVA : (tanVA (M := M) (d₁ := d₁) gam t).map prAA = gam.map (LinearMap.fst ℂ _ _) := by
  rw [tanVA, Submodule.map_sup, ← Submodule.map_comp, ← Submodule.map_comp]
  have h1 : (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)).comp vecInclA = LinearMap.fst ℂ _ _ := by
    ext <;> rfl
  have h2 : (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)).comp g2InclA = 0 := by
    ext <;> rfl
  rw [h1, h2, Submodule.map_zero, sup_bot_eq]

theorem map_fst_tanAV : (tanAV B M gam U t).map (LinearMap.fst ℂ _ _) = gam.map (LinearMap.fst ℂ _ _) := by
  change (tanAV B M gam U t).map prAA = _
  rw [tanAV_eq, Submodule.map_sup, map_prAA_tanVA, map_eq_bot_of_le_kerA (tor_le_ker_prAA U),
    bot_sup_eq]

theorem tanAV_inf_ker : tanAV B M gam U t ⊓ (LinearMap.ker prAA ⊓ LinearMap.ker prBA) =
    tanVA (M := M) gam t ⊓ LinearMap.ker prAA := by
  apply le_antisymm
  · rintro v ⟨hv, hA, hB⟩
    rw [tanAV_eq] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨b, -, rfl⟩ := hx
    have hy2 : y.2.1 = 0 := tanVA_le_ker_prBA gam t hy
    have hb : b = 0 := by
      have hb' : b + y.2.1 = 0 := hB
      rwa [hy2, add_zero] at hb'
    subst hb
    simp only [map_zero, zero_add]
    exact ⟨hy, by simpa using hA⟩
  · rintro v ⟨hv, hA⟩
    exact ⟨by rw [tanAV_eq]; exact Submodule.mem_sup_right hv, hA, tanVA_le_ker_prBA gam t hv⟩

/-- **The exponents add up**: `dim T_{G′} = dim pr₀ Γ + dim U^⊥ + t₂`. -/
theorem finrank_tanAV :
    finrank ℂ (tanAV B M gam U t) = finrank ℂ (gam.map (LinearMap.fst ℂ _ _)) + finrank ℂ (torusLie U) +
      finrank ℂ ↥(tanAV B M gam U t ⊓ (LinearMap.ker prAA ⊓ LinearMap.ker prBA)) := by
  have hdis : (torusLie U).map torInclA ⊓ tanVA (M := M) (d₁ := d₁) gam t = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨b, -, rfl⟩, hv⟩
    have : b = 0 := tanVA_le_ker_prBA gam t hv
    simp [this]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq ((torusLie U).map torInclA)
    (tanVA (M := M) (d₁ := d₁) gam t)
  rw [hdis, finrank_bot, add_zero, ← tanAV_eq] at hsup
  have htor : finrank ℂ ((torusLie U).map (torInclA : _ →ₗ[ℂ] TanAV d₀ d₁ r B)) = finrank ℂ (torusLie U) := by
    refine (Submodule.equivMapOfInjective _ ?_ _).finrank_eq.symm
    intro x y h; exact congrArg (fun p : TanAV d₀ d₁ r B => p.2.1) h
  have hrn := LinearMap.finrank_range_add_finrank_ker (prAA.comp (tanVA (M := M) (d₁ := d₁) gam t).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, map_prAA_tanVA] at hrn
  have hker : finrank ℂ (LinearMap.ker (prAA.comp (tanVA (M := M) (d₁ := d₁) gam t).subtype)) =
      finrank ℂ ↥(tanVA (M := M) (d₁ := d₁) gam t ⊓ LinearMap.ker prAA) := by
    rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  rw [hker] at hrn
  rw [tanAV_inf_ker, hsup, htor, ← hrn]
  omega

end Member

/-! ### The push-out of the obstruction -/

section Push

variable (O : ObstrDataBV d₀ r d₁ B M)

/-- `T′ = pushTA(T̃′)`. -/
def tanG : Submodule ℂ (TanAV d₀ d₁ r B) := O.tan.map (pushTA M)

theorem tan_eq_comap : O.tan = (tanG O).comap (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M) := by
  rw [tanG, Submodule.comap_map_eq, ker_pushTA]
  exact (sup_eq_left.mpr O.ker_le).symm

theorem mem_tan_iff {p : LSG.MEBV.Tan (d₀ + r) d₁ B} : p ∈ O.tan ↔ pushTA M p ∈ tanG O := by
  rw [tan_eq_comap O]; rfl

theorem liftTA_mem_tan {x : TanAV d₀ d₁ r B} : liftTA x ∈ O.tan ↔ x ∈ tanG O := by
  rw [mem_tan_iff, pushTA_liftTA]

theorem kvec_injective : Function.Injective (kvec (d₀ := d₀) (d₁ := d₁) (B := B) M) := fun v v' h => by
  exact congrArg (fun p : LSG.MEBV.Tan (d₀ + r) d₁ B => p.2.2.2) h

theorem finrank_kerK : finrank ℂ (kerK d₀ d₁ B M) = m := by
  rw [kerK, LinearMap.finrank_range_of_inj kvec_injective]; simp

theorem t0_eq : O.t0 = finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) := by
  rw [ObstrDataBV.t0, tanG, ← Submodule.map_comp]
  congr 2

/-- The `G`-exponent `t₂ = dim (T′ ∩ ker π₀ ∩ ker π₁)`. -/
def t2G : ℕ := finrank ℂ ↥(tanG O ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓
  LinearMap.ker prBA))

theorem t2_eq : O.t2 = t2G O + m := by
  classical
  set A := O.tan ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) ⊓
    LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B)))
  set B' := tanG O ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA)
  set f := (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M).comp A.subtype
  have hrange : LinearMap.range f = B' := by
    apply le_antisymm
    · rintro _ ⟨⟨p, hpT, hpA, hpB⟩, rfl⟩
      refine ⟨⟨p, hpT, rfl⟩, ?_, ?_⟩
      · change (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M p).1 = 0
        funext i
        exact congrFun (show prLead p = 0 from hpA) i
      · change (pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M p).2.1 = 0
        exact hpB
    · rintro x ⟨hxT, hxA, hxB⟩
      have hxA' : x.1 = 0 := hxA
      have hxB' : x.2.1 = 0 := hxB
      refine ⟨⟨liftTA x, (liftTA_mem_tan O).mpr hxT, ?_, ?_⟩, pushTA_liftTA M x⟩
      · change prLead (liftTA x) = 0
        funext i; simp [prLead, hxA']
      · change (liftTA x).2.1 = 0
        simp [hxB']
  have hker : finrank ℂ (LinearMap.ker f) = m := by
    set φ := A.subtype ∘ₗ (LinearMap.ker f).subtype
    have hφ : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
    have hφr : LinearMap.range φ = kerK d₀ d₁ B M := by
      apply le_antisymm
      · rintro _ ⟨p, rfl⟩
        rw [← ker_pushTA]
        exact LinearMap.mem_ker.mp p.2
      · intro q hq
        have hq' : pushTA (d₀ := d₀) (d₁ := d₁) (B := B) M q = 0 := by
          rw [← ker_pushTA] at hq; exact hq
        obtain ⟨v, rfl⟩ := hq
        have hA : kvec (d₀ := d₀) (d₁ := d₁) (B := B) M v ∈ A := by
          refine ⟨O.ker_le ⟨v, rfl⟩, ?_, ?_⟩
          · change prLead (kvec (d₀ := d₀) (d₁ := d₁) (B := B) M v) = 0
            funext i; simp [kvec, prLead]
          · change (kvec (d₀ := d₀) (d₁ := d₁) (B := B) M v).2.1 = 0
            simp [kvec]
        exact ⟨⟨⟨_, hA⟩, LinearMap.mem_ker.mpr hq'⟩, rfl⟩
    rw [← LinearMap.finrank_range_of_inj hφ, hφr, finrank_kerK]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker] at hrn
  rw [ObstrDataBV.t2, t2G]
  change finrank ℂ A = finrank ℂ B' + m
  omega

theorem tau_eq (W : Submodule ℂ (TanAV d₀ d₁ r B)) :
    finrank ℂ (W.map liftTA) - finrank ℂ ↥(W.map liftTA ⊓ O.tan) =
      finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) := by
  have h1 : finrank ℂ (W.map liftTA) = finrank ℂ W :=
    (Submodule.equivMapOfInjective _ liftTA_injective W).finrank_eq.symm
  have h2 : W.map liftTA ⊓ O.tan = (W ⊓ tanG O).map liftTA := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxT⟩
      exact ⟨x, ⟨hx, (liftTA_mem_tan O).mp hxT⟩, rfl⟩
    · rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (liftTA_mem_tan O).mpr hxT⟩
  have h3 : finrank ℂ ↥((W ⊓ tanG O).map liftTA) = finrank ℂ ↥(W ⊓ tanG O) :=
    (Submodule.equivMapOfInjective _ liftTA_injective _).finrank_eq.symm
  rw [h1, h2, h3]

/-! ### The structure of `T′` -/

theorem perTanId_le_fst (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    perTanId B t ≤ t.comap (LinearMap.fst ℂ _ _) :=
  Submodule.span_le.mpr fun _ hp => hp.1

theorem tan_le_tor : O.tan ≤ (torusLie O.U).comap (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B)) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨x, -, rfl⟩; exact (torusLie O.U).zero_mem
  · rintro _ ⟨b, hb, rfl⟩; exact hb
  · rintro _ ⟨x, -, rfl⟩; exact (torusLie O.U).zero_mem

theorem tan_le_t : O.tan ≤ O.t.comap ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp
    (LinearMap.snd ℂ (Fin (d₀ + r) → ℂ) ((Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ) × (Fin m → ℂ))))) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨x, -, rfl⟩; exact O.t.zero_mem
  · rintro _ ⟨b, -, rfl⟩; exact O.t.zero_mem
  · rintro _ ⟨x, hx, rfl⟩; exact perTanId_le_fst O.t hx

theorem prB_tanG {x : TanAV d₀ d₁ r B} (hx : x ∈ tanG O) : x.2.1 ∈ torusLie O.U := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact tan_le_tor O hp

theorem piZ_tanG {x : TanAV d₀ d₁ r B} (hx : x ∈ tanG O) : x.2.2.1 ∈ O.t := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact tan_le_t O hp

theorem torInclA_mem_tanG {b : Fin d₁ → ℂ} (hb : b ∈ torusLie O.U) :
    (torInclA b : TanAV d₀ d₁ r B) ∈ tanG O := by
  refine ⟨torIncl b, Submodule.mem_sup_left (Submodule.mem_sup_right ⟨b, hb, rfl⟩), ?_⟩
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))) <;>
    simp [torIncl, torInclA]

theorem g2InclA_mem_tanG {z : ∀ k, Fin (B k).g → ℂ} {w : Fin m → ℂ} (h : (z, w) ∈ perTanId B O.t) :
    (g2InclA (z, M.mulVec w) : TanAV d₀ d₁ r B) ∈ tanG O := by
  refine ⟨g2Incl (z, w), Submodule.mem_sup_right ⟨(z, w), h, rfl⟩, ?_⟩
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))) <;>
    simp [g2Incl, g2InclA]

theorem perTanA_le_tanG : (perTanA B M O.t).map g2InclA ≤ tanG O := by
  rintro _ ⟨_, ⟨⟨z, w⟩, h, rfl⟩, rfl⟩
  exact g2InclA_mem_tanG O h

/-- **Every `z ∈ t` has a fibre lift in `perTanId t`** (from `IsRatSub (perBase B) t`). -/
theorem exists_perTanId {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} (ht : IsRatSub (perBase B) t)
    {z : ∀ k, Fin (B k).g → ℂ} (hz : z ∈ t) : ∃ w, (z, w) ∈ perTanId B t := by
  have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (∀ k, Fin (B k).g → ℂ)) := hz
  rw [ht] at hz'
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨etaB B x, Submodule.subset_span ⟨hx.1, fun k => ?_⟩⟩
    exact ⟨hx.2 k (Set.mem_univ k), rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    exact ⟨w + w', by simpa using (perTanId B t).add_mem hw hw'⟩
  | smul c x _ hx =>
    obtain ⟨w, hw⟩ := hx
    refine ⟨(c : ℂ) • w, ?_⟩
    have := (perTanId B t).smul_mem (c : ℂ) hw
    convert this using 1

/-- `Γ_full = T′ ∩ (vector group)`. -/
def gamFull : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ)) := (tanG O).comap vecInclA

theorem decomp_tanG {x : TanAV d₀ d₁ r B} (hx : x ∈ tanG O) :
    ∃ w : Fin m → ℂ, (x.2.2.1, w) ∈ perTanId B O.t ∧ (x.1, x.2.2.2 - M.mulVec w) ∈ gamFull O ∧
      x = vecInclA (x.1, x.2.2.2 - M.mulVec w) + torInclA x.2.1 + g2InclA (x.2.2.1, M.mulVec w) := by
  obtain ⟨w, hw⟩ := exists_perTanId O.t_rat (piZ_tanG O hx)
  have e : x = vecInclA (x.1, x.2.2.2 - M.mulVec w) + torInclA x.2.1 + g2InclA (x.2.2.1, M.mulVec w) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [vecInclA, torInclA, g2InclA]
  refine ⟨w, hw, ?_, e⟩
  change vecInclA (x.1, x.2.2.2 - M.mulVec w) ∈ tanG O
  have : vecInclA (x.1, x.2.2.2 - M.mulVec w) =
      x - torInclA x.2.1 - (g2InclA (x.2.2.1, M.mulVec w) : TanAV d₀ d₁ r B) := by
    rw [e]; refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [vecInclA, torInclA, g2InclA]
  rw [this]
  exact (tanG O).sub_mem ((tanG O).sub_mem hx (torInclA_mem_tanG O (prB_tanG O hx))) (g2InclA_mem_tanG O hw)

/-- **`T′ = Γ_full + U^⊥ + T_{B̃}`.** -/
theorem tanG_eq : tanAV B M (gamFull O) O.U O.t = tanG O := by
  apply le_antisymm
  · refine sup_le (sup_le (Submodule.map_comap_le _ _) ?_) (perTanA_le_tanG O)
    rintro _ ⟨b, hb, rfl⟩
    exact torInclA_mem_tanG O hb
  · intro x hx
    obtain ⟨w, hw, hg, e⟩ := decomp_tanG O hx
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, hg, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
    · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec w), ⟨(x.2.2.1, w), hw, rfl⟩, rfl⟩

end Push

/-! ### The rationality repair -/

section Rat

variable (O : ObstrDataBV d₀ r d₁ B M)

/-- `Γ″`: the span of the algebraic vectors of `Γ_full`. -/
def gamRat : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ)) := Submodule.span ℂ {v | v ∈ gamFull O ∧ AlgPair v}

theorem gamRat_le : gamRat O ≤ gamFull O := Submodule.span_le.mpr fun _ hv => hv.1

theorem gamRat_rat : RatPair (gamRat O) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr fun w hw => hw.1)
  exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hv.2⟩

/-- **The `ℚ̄`-rational member `H″ = (U, t, Γ″)`.** -/
def dataRat : SubgroupDataAV d₀ d₁ B M :=
  { U := O.U, t := O.t, gam := gamRat O, gam_rat := gamRat_rat O, t_rat := O.t_rat }

theorem dataRat_tan_le : (dataRat O).tan ≤ tanG O := by
  rw [← tanG_eq O]
  exact sup_le_sup_right (sup_le_sup_right (Submodule.map_mono (gamRat_le O)) _) _

/-- `r ≤ 1`: the fibre part of `Γ_full` lies in `Γ″`. -/
theorem fib_mem_gamRat (hr : r ≤ 1) {s : Fin r → ℂ} (hs : ((0 : Fin d₀ → ℂ), s) ∈ gamFull O) :
    ((0 : Fin d₀ → ℂ), s) ∈ gamRat O := by
  rcases Nat.lt_or_ge r 1 with h0 | h1
  · have : s = 0 := funext fun i => absurd i.2 (by omega)
    subst this; exact Submodule.zero_mem _
  · have hr1 : r = 1 := by omega
    subst hr1
    by_cases hs0 : s 0 = 0
    · have : s = 0 := funext fun i => by rw [Fin.fin_one_eq_zero i, hs0]; rfl
      subst this; exact Submodule.zero_mem _
    · have e : ((0 : Fin d₀ → ℂ), s) = s 0 • ((0 : Fin d₀ → ℂ), (fun _ => 1 : Fin 1 → ℂ)) := by
        ext i <;> simp [Fin.fin_one_eq_zero]
      have h1' : ((0 : Fin d₀ → ℂ), (fun _ => 1 : Fin 1 → ℂ)) ∈ gamFull O := by
        have : ((0 : Fin d₀ → ℂ), (fun _ => 1 : Fin 1 → ℂ)) = (s 0)⁻¹ • ((0 : Fin d₀ → ℂ), s) := by
          ext i <;> simp [Fin.fin_one_eq_zero, hs0]
        rw [this]; exact (gamFull O).smul_mem _ hs
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨h1', fun i => ?_, fun i => ?_⟩)
      · simpa using isAlgebraic_zero
      · simpa using isAlgebraic_one

theorem tanG_inf_le_dataRat (hr : r ≤ 1) :
    tanG O ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA) ≤
      (dataRat O).tan := by
  rintro x ⟨hx, hA, hB⟩
  have hA' : x.1 = 0 := hA
  have hB' : x.2.1 = 0 := hB
  obtain ⟨w, hw, hg, e⟩ := decomp_tanG O hx
  rw [hA'] at hg
  rw [e, hA', hB']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, fib_mem_gamRat O hr hg, rfl⟩)
  · rw [map_zero]; exact Submodule.zero_mem _
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec w), ⟨(x.2.2.1, w), hw, rfl⟩, rfl⟩

/-- **The vector part becomes rational without changing `λ`** (base parts in `lat`). -/
theorem mem_dataRat_of_lam (An : ∀ k, VBlockAn (B k)) {y : TanAV d₀ d₁ r B}
    (hy : y ∈ LamAV d₀ d₁ An M) {x ω : TanAV d₀ d₁ r B} (hx : x ∈ tanG O) (hω : ω ∈ PerAV d₀ d₁ An M)
    (hxy : y = x + ω) : x ∈ (dataRat O).tan := by
  obtain ⟨hω1, -, hω3, hω4⟩ := hω
  have hxz : x.2.2.1 = y.2.2.1 - ω.2.2.1 := by rw [hxy]; simp
  have hlat : ∀ k, x.2.2.1 k ∈ (An k).an.lat := fun k => by
    rw [hxz]; exact (An k).an.lat.sub_mem (hy.2.2.1 k) (hω3 k)
  have hw : (x.2.2.1, etaB B x.2.2.1) ∈ perTanId B O.t :=
    Submodule.subset_span ⟨piZ_tanG O hx, fun k => ⟨(An k).an.lat_le (hlat k), rfl⟩⟩
  have hvec : (x.1, x.2.2.2 - M.mulVec (etaB B x.2.2.1)) ∈ gamFull O := by
    obtain ⟨-, -, -, -⟩ := decomp_tanG O hx
    change vecInclA (x.1, x.2.2.2 - M.mulVec (etaB B x.2.2.1)) ∈ tanG O
    have : vecInclA (x.1, x.2.2.2 - M.mulVec (etaB B x.2.2.1)) =
        x - torInclA x.2.1 - (g2InclA (x.2.2.1, M.mulVec (etaB B x.2.2.1)) : TanAV d₀ d₁ r B) := by
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [vecInclA, torInclA, g2InclA]
    rw [this]
    exact (tanG O).sub_mem ((tanG O).sub_mem hx (torInclA_mem_tanG O (prB_tanG O hx)))
      (g2InclA_mem_tanG O hw)
  have halg : AlgPair (x.1, x.2.2.2 - M.mulVec (etaB B x.2.2.1)) := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have : x.1 = y.1 := by rw [hxy]; simp [hω1]
      rw [this]; exact hy.1 i
    · have hs : x.2.2.2 - M.mulVec (etaB B x.2.2.1) = sPart M y := by
        have hy4 : y.2.2.2 = x.2.2.2 + ω.2.2.2 := by rw [hxy]; simp
        have he : etaB B y.2.2.1 = etaB B x.2.2.1 + etaB B ω.2.2.1 := by
          funext k
          have hyk : y.2.2.1 k = x.2.2.1 k + ω.2.2.1 k := by rw [hxy]; simp
          simp only [etaB, Pi.add_apply, hyk]
          exact (B k).η_add ((An k).an.lat_le (hlat k)) ((An k).an.lat_le (hω3 k))
        rw [sPart, hy4, hω4, he, Matrix.mulVec_add]; abel
      rw [hs]; exact hy.2.2.2 i
  have e' : x = vecInclA (x.1, x.2.2.2 - M.mulVec (etaB B x.2.2.1)) + torInclA x.2.1 +
      g2InclA (x.2.2.1, M.mulVec (etaB B x.2.2.1)) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [vecInclA, torInclA, g2InclA]
  rw [e']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, Submodule.subset_span ⟨hvec, halg⟩, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec (etaB B x.2.2.1)), ⟨(x.2.2.1, etaB B x.2.2.1), hw, rfl⟩,
      rfl⟩

theorem inf_tanPerAV_eq (An : ∀ k, VBlockAn (B k)) (Y : AddSubgroup (TanAV d₀ d₁ r B))
    (hY : ∀ y ∈ Y, y ∈ LamAV d₀ d₁ An M) :
    Y ⊓ ((dataRat O).tan.toAddSubgroup ⊔ PerAV d₀ d₁ An M) =
      Y ⊓ ((tanG O).toAddSubgroup ⊔ PerAV d₀ d₁ An M) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (sup_le_sup_right (fun x hx => dataRat_tan_le O hx) _)
  · rintro y ⟨hyY, hyT⟩
    refine ⟨hyY, ?_⟩
    obtain ⟨x, hx, ω, hω, rfl⟩ := AddSubgroup.mem_sup.mp hyT
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left
      (show x ∈ (dataRat O).tan from mem_dataRat_of_lam O An (hY _ hyY) hx hω rfl))
      (AddSubgroup.mem_sup_right hω)

/-! ### Codimensions -/

theorem finrank_tanG : finrank ℂ (tanG O) =
    finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + (d₁ - finrank ℚ O.U) + t2G O := by
  have h := finrank_tanAV (M := M) (gamFull O) O.U O.t
  have hf := map_fst_tanAV (M := M) (gamFull O) O.U O.t
  rw [tanG_eq] at h hf
  have ht := LSG.ME.finrank_torusLie O.U
  rw [h, ← hf, t2G]
  omega

theorem dataRat_t2 (hr : r ≤ 1) :
    finrank ℂ ↥((dataRat O).tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓
      LinearMap.ker prBA)) = t2G O := by
  rw [t2G]
  have e : (dataRat O).tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓
      LinearMap.ker prBA) = tanG O ⊓ (LinearMap.ker prAA ⊓ LinearMap.ker prBA) :=
    le_antisymm (inf_le_inf_right _ (dataRat_tan_le O)) (le_inf (tanG_inf_le_dataRat O hr) inf_le_right)
  rw [e]

theorem finrank_dataRat (hr : r ≤ 1) : finrank ℂ (dataRat O).tan =
    finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _)) + (d₁ - finrank ℚ O.U) + t2G O := by
  have h := finrank_tanAV (M := M) (gamRat O) O.U O.t
  have ht := LSG.ME.finrank_torusLie O.U
  have h2 := dataRat_t2 O hr
  change finrank ℂ ↥(tanAV B M (gamRat O) O.U O.t ⊓ (LinearMap.ker prAA ⊓ LinearMap.ker prBA)) = _ at h2
  change finrank ℂ (tanAV B M (gamRat O) O.U O.t) = _
  rw [h, h2]
  omega

theorem t2G_le : t2G O ≤ ∑ k, (B k).g + r := by
  set Bk := tanG O ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA)
  let f : Bk →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ) :=
    (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _) ∘ₗ Bk.subtype
  have hf : Function.Injective f := by
    rintro ⟨x, hx, hxA, hxB⟩ ⟨y, hy, hyA, hyB⟩ h
    have hxA' : x.1 = 0 := hxA
    have hxB' : x.2.1 = 0 := hxB
    have hyA' : y.1 = 0 := hyA
    have hyB' : y.2.1 = 0 := hyB
    have h1 : x.2.2 = y.2.2 := h
    exact Subtype.ext (Prod.ext (hxA'.trans hyA'.symm) (Prod.ext (hxB'.trans hyB'.symm) h1))
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [t2G, Module.finrank_pi_fintype] using this

/-- **The repair.** Same `λ`, `δ₁`, `δ₂`; `δ − τ` does not decrease. -/
theorem exists_subgroupDataAV_rat (hr : r ≤ 1) (An : ∀ k, VBlockAn (B k)) (W : Submodule ℂ (TanAV d₀ d₁ r B))
    (Y : AddSubgroup (TanAV d₀ d₁ r B)) (hY : ∀ y ∈ Y, y ∈ LamAV d₀ d₁ An M) :
    ∃ H : SubgroupDataAV d₀ d₁ B M,
      Y ⊓ (H.tan.toAddSubgroup ⊔ PerAV d₀ d₁ An M) = Y ⊓ ((tanG O).toAddSubgroup ⊔ PerAV d₀ d₁ An M) ∧
      H.δ1 = finrank ℚ O.U ∧ H.δ2 = ∑ k, (B k).g + r - t2G O ∧
      ((d₀ - finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + finrank ℚ O.U + (∑ k, (B k).g + r - t2G O) :
          ℕ) : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) : ℕ) : ℤ) ≤
        (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
  have hR := finrank_dataRat O hr
  have hT := finrank_tanG O
  have hfst : finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _)) ≤
      finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) := by
    have hf := map_fst_tanAV (M := M) (gamFull O) O.U O.t
    rw [tanG_eq] at hf
    rw [hf]
    exact Submodule.finrank_mono (Submodule.map_mono (gamRat_le O))
  have hfd : finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) ≤ d₀ := by
    simpa using Submodule.finrank_le ((tanG O).map (LinearMap.fst ℂ (Fin d₀ → ℂ) _))
  have hU : finrank ℚ O.U ≤ d₁ := by simpa using Submodule.finrank_le O.U
  have h2 := t2G_le O
  have hle := finrank_inf_add_le W (tanG O) (dataRat O).tan (dataRat_tan_le O)
  have hW1 := Submodule.finrank_mono (inf_le_left : W ⊓ tanG O ≤ W)
  have hW2 := Submodule.finrank_mono (inf_le_left : W ⊓ (dataRat O).tan ≤ W)
  refine ⟨dataRat O, inf_tanPerAV_eq O An Y hY, rfl, ?_, ?_⟩
  · change d₀ + d₁ + ∑ k, (B k).g + r - finrank ℂ (dataRat O).tan -
      (d₀ - finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _))) - finrank ℚ O.U = ∑ k, (B k).g + r - t2G O
    rw [hR]; omega
  · change _ ≤ ((d₀ + d₁ + ∑ k, (B k).g + r - finrank ℂ (dataRat O).tan : ℕ) : ℤ) - _
    rw [hR]; rw [hT] at hle; rw [hR] at hle
    omega

end Rat

end LSG.W88.AVS
