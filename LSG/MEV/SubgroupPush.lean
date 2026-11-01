import Mathlib
import LSG.MEV.SubgroupClass

/-!
# Push-out along `M` and W88's projection exponents for the family

* **Push-out** (VECEXT §3.2): `pushM M : T_G̃ → T_G`, `(a, b, z, w) ↦ (a, b, z, M w)`, the tangent map
  of `G̃ → G = G_a^{d₀} × G_m^{d₁} × ((E^m)^♮ pushed along M)`. It maps periods to periods
  (`pushM_per`) and a family member of `G̃` to a family member of `G` (**`tan_push`**:
  `(S.push M).tan = S.tan.map (pushM M)`, with `Γ ↦ (id × M)(Γ)`, `perTanId ↦ perTan M`).
  `ℚ̄`-rationality of `Γ` is preserved for algebraic `M` (`ratPair_map`).
* **Projection exponents** (W88 p. 392) for any member `S` (any `M`):
  `S.tan.map prA = S.gam.map fst` (**`map_prA_tan`**, so `SubgroupDataV.δ0 = d₀ − dim π₀(G′)`),
  `S.tan.map prB = U^⊥` (`map_prB_tan`), and
  **`finrank_tan_eq`**: `dim T_{G′} = t₀ + t₁ + dim (T_{G′} ∩ ker prA ∩ ker prB)` with
  `t₀ = dim π₀`, `t₁ = dim U^⊥`; the last term is W88's `t₂ = dim (perTan t + Γ_fib)` (base and fibre
  directions of `G′ ∩ G₂`).
-/

open Module
open LSG.W88 (IsAbelianTangent torusLie AlgVec)
open LSG.W88.Vec (TanV PerV etaV vecIncl torIncl g2Incl perTanId perTan RatPair AlgPair AlgMat)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m r : ℕ}

/-! ### Push-out -/

/-- `id × M` on `ℂ^{d₀} × ℂ^m`, or on `ℂ^m × ℂ^m`. -/
abbrev idM {n : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) :
    ((Fin n → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] ((Fin n → ℂ) × (Fin r → ℂ)) :=
  LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M)

/-- The tangent map of the push-out `G̃ → G`. -/
def pushM (M : Matrix (Fin r) (Fin m) ℂ) : TanG d₀ d₁ m →ₗ[ℂ] TanV d₀ d₁ m r :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id (idM M))

@[simp] theorem pushM_apply (M : Matrix (Fin r) (Fin m) ℂ) (p : TanG d₀ d₁ m) :
    pushM M p = (p.1, p.2.1, p.2.2.1, M.mulVec p.2.2.2) := rfl

variable {Ls : Fin m → PeriodPair}

theorem pushM_per (M : Matrix (Fin r) (Fin m) ℂ) {p : TanG d₀ d₁ m} (hp : p ∈ PerV Ls 1) :
    pushM M p ∈ PerV Ls M := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h1, h2, h3, ?_⟩
  simp only [pushM_apply, h4, Matrix.one_mulVec]

theorem perTan_eq_map (M : Matrix (Fin r) (Fin m) ℂ) (t : Submodule ℂ (Fin m → ℂ)) :
    perTan Ls M t = (perTan Ls (1 : Matrix (Fin m) (Fin m) ℂ) t).map (idM M) := by
  rw [perTan_one]; rfl

namespace SubgroupPreV

/-- The push-out of a member of the family of `G̃`. -/
def push (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls (1 : Matrix (Fin m) (Fin m) ℂ)) (M : Matrix (Fin r) (Fin m) ℂ) :
    SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls M :=
  { U := S.U, t := S.t, gam := S.gam.map (idM M), t_ab := S.t_ab }

/-- **The push-out of a member is a member**: `(S.push M).tan = (pushM M)(S.tan)`. -/
theorem tan_push (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls (1 : Matrix (Fin m) (Fin m) ℂ)) (M : Matrix (Fin r) (Fin m) ℂ) :
    (S.push M).tan = S.tan.map (pushM M) := by
  have h1 : (pushM (d₀ := d₀) (d₁ := d₁) M).comp vecIncl = vecIncl.comp (idM M) := by
    ext <;> simp
  have h2 : (pushM (d₀ := d₀) (d₁ := d₁) M).comp torIncl = torIncl := by
    ext <;> simp
  have h3 : (pushM (d₀ := d₀) (d₁ := d₁) M).comp g2Incl = g2Incl.comp (idM M) := by
    ext <;> simp
  have e1 : (S.gam.map (idM M)).map (vecIncl : _ →ₗ[ℂ] TanV d₀ d₁ m r) =
      (S.gam.map (vecIncl : _ →ₗ[ℂ] TanG d₀ d₁ m)).map (pushM M) := by
    rw [← Submodule.map_comp, ← Submodule.map_comp, h1]
  have e2 : (torusLie S.U).map (torIncl : _ →ₗ[ℂ] TanV d₀ d₁ m r) =
      ((torusLie S.U).map (torIncl : _ →ₗ[ℂ] TanG d₀ d₁ m)).map (pushM M) := by
    rw [← Submodule.map_comp, h2]
  have e3 : (perTan Ls M S.t).map (g2Incl : _ →ₗ[ℂ] TanV d₀ d₁ m r) =
      ((perTan Ls (1 : Matrix (Fin m) (Fin m) ℂ) S.t).map (g2Incl : _ →ₗ[ℂ] TanG d₀ d₁ m)).map (pushM M) := by
    rw [perTan_eq_map M S.t, ← Submodule.map_comp, ← Submodule.map_comp, h3]
  show (S.gam.map (idM M)).map vecIncl ⊔ _ ⊔ _ = _
  rw [tan, Submodule.map_sup, Submodule.map_sup, ← e1, ← e2, ← e3]
  rfl

end SubgroupPreV

theorem isAlgebraic_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IsAlgebraic ℚ (f i)) :
    IsAlgebraic ℚ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isAlgebraic_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **`ℚ̄`-rationality is preserved by `id × M`** for an algebraic matrix `M`. -/
theorem ratPair_map {n : ℕ} {M : Matrix (Fin r) (Fin m) ℂ} (hM : AlgMat M)
    {Γ : Submodule ℂ ((Fin n → ℂ) × (Fin m → ℂ))} (hΓ : RatPair Γ) : RatPair (Γ.map (idM M)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr fun w hw => hw.1)
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ Submodule.span ℂ {w | w ∈ Γ ∧ AlgPair w} := by rw [← hΓ]; exact hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    refine ⟨Submodule.mem_map_of_mem hx.1, hx.2.1, fun i => ?_⟩
    simp only [idM, LinearMap.prodMap_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact isAlgebraic_sum _ _ fun j _ => (hM i j).mul (hx.2.2 j)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy px py => rw [map_add]; exact Submodule.add_mem _ px py
  | smul a x hx px => rw [map_smul]; exact Submodule.smul_mem _ a px

/-! ### `ker M`-stable subgroups -/

/-- If `H` contains the fibre points `(O, v)`, `v ∈ ker M` (e.g. `H` is the stabiliser of a
`ker M`-stable set), then `T′ ⊇ 0 × 0 × 0 × ker M`. -/
theorem fib_mem_lieAlg {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (M : Matrix (Fin r) (Fin m) ℂ)
    (hfib : ∀ v : Fin m → ℂ, M.mulVec v = 0 → expGV Ls ((0, 0, 0, v) : TanG d₀ d₁ m) ∈ H)
    {v : Fin m → ℂ} (hv : M.mulVec v = 0) : ((0, 0, 0, v) : TanG d₀ d₁ m) ∈ lieAlg Ls hH := by
  intro c
  have : c • ((0, 0, 0, v) : TanG d₀ d₁ m) = (0, 0, 0, c • v) := by simp
  rw [this, mem_Htil]
  exact hfib _ (by rw [Matrix.mulVec_smul, hv, smul_zero])

/-- For `T ⊇ 0 × 0 × 0 × ker M`, `T` is recovered from its push-out: `pushM⁻¹(pushM T) = T`. -/
theorem comap_map_pushM {M : Matrix (Fin r) (Fin m) ℂ} {T : Submodule ℂ (TanG d₀ d₁ m)}
    (hT : ∀ v : Fin m → ℂ, M.mulVec v = 0 → ((0, 0, 0, v) : TanG d₀ d₁ m) ∈ T) :
    (T.map (pushM M)).comap (pushM M) = T := by
  refine le_antisymm (fun p hp => ?_) (Submodule.le_comap_map _ _)
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp hp
  have hk : p - q = ((0, 0, 0, p.2.2.2 - q.2.2.2) : TanG d₀ d₁ m) := by
    have h := congrArg (fun x : TanV d₀ d₁ m r => x) he
    simp only [pushM_apply, Prod.mk.injEq] at h
    ext <;> simp [h.1, h.2.1, h.2.2.1]
  have hv : M.mulVec (p.2.2.2 - q.2.2.2) = 0 := by
    simp only [pushM_apply, Prod.mk.injEq] at he
    rw [Matrix.mulVec_sub, he.2.2.2, sub_self]
  have := T.add_mem hq (hT _ hv)
  rwa [← hk, add_sub_cancel] at this

/-! ### Projection exponents -/

/-- `π₀`. -/
abbrev prA : TanV d₀ d₁ m r →ₗ[ℂ] (Fin d₀ → ℂ) := LinearMap.fst ℂ _ _

/-- `π₁`. -/
abbrev prB : TanV d₀ d₁ m r →ₗ[ℂ] (Fin d₁ → ℂ) :=
  (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)

theorem map_eq_bot_of_le_ker {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F]
    [Module ℂ F] {f : E →ₗ[ℂ] F} {p : Submodule ℂ E} (h : p ≤ LinearMap.ker f) : p.map f = ⊥ := by
  rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_bot]
  exact h hx

namespace SubgroupPreV

variable {M : Matrix (Fin r) (Fin m) ℂ} (S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls M)

/-- The part of `T_{G′}` without the torus: `Γ + T_{B̃}`. -/
def tanV : Submodule ℂ (TanV d₀ d₁ m r) := S.gam.map vecIncl ⊔ (perTan Ls M S.t).map g2Incl

theorem tan_eq : S.tan = (torusLie S.U).map torIncl ⊔ S.tanV := by
  rw [tan, tanV]; ac_rfl

theorem tanV_le_ker_prB : S.tanV ≤ LinearMap.ker prB := by
  refine sup_le ?_ ?_ <;> rintro _ ⟨x, -, rfl⟩ <;> simp

theorem tor_le_ker_prA : (torusLie S.U).map torIncl ≤ LinearMap.ker (prA (d₀ := d₀) (m := m) (r := r)) := by
  rintro _ ⟨x, -, rfl⟩; simp

theorem map_prA_tanV : S.tanV.map prA = S.gam.map (LinearMap.fst ℂ _ _) := by
  rw [tanV, Submodule.map_sup, ← Submodule.map_comp, ← Submodule.map_comp]
  have h1 : (prA (d₀ := d₀) (d₁ := d₁) (m := m) (r := r)).comp vecIncl = LinearMap.fst ℂ _ _ := by
    ext <;> simp
  have h2 : (prA (d₀ := d₀) (d₁ := d₁) (m := m) (r := r)).comp g2Incl = 0 := by
    ext <;> simp
  rw [h1, h2, Submodule.map_zero, sup_bot_eq]

/-- **`π₀(T_{G′}) = π₀(Γ)`**: W88's `d₀′ = dim π₀(G′)` is `dim pr₀ Γ`. -/
theorem map_prA_tan : S.tan.map prA = S.gam.map (LinearMap.fst ℂ _ _) := by
  rw [tan_eq, Submodule.map_sup, map_prA_tanV]
  have : ((torusLie S.U).map torIncl).map (prA (d₀ := d₀) (m := m) (r := r)) = ⊥ :=
    map_eq_bot_of_le_ker (tor_le_ker_prA S)
  rw [this, bot_sup_eq]

/-- **`π₁(T_{G′}) = U^⊥`.** -/
theorem map_prB_tan : S.tan.map prB = torusLie S.U := by
  rw [tan_eq, Submodule.map_sup, map_eq_bot_of_le_ker (tanV_le_ker_prB S),
    sup_bot_eq, ← Submodule.map_comp]
  have : (prB (d₀ := d₀) (d₁ := d₁) (m := m) (r := r)).comp torIncl = LinearMap.id := by
    ext; simp
  rw [this, Submodule.map_id]

theorem disjoint_tor_tanV : (torusLie S.U).map torIncl ⊓ S.tanV = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨b, -, rfl⟩, hv⟩
  have : b = 0 := by simpa using S.tanV_le_ker_prB hv
  simp [this]

theorem tan_inf_ker : S.tan ⊓ (LinearMap.ker prA ⊓ LinearMap.ker prB) = S.tanV ⊓ LinearMap.ker prA := by
  apply le_antisymm
  · rintro v ⟨hv, hA, hB⟩
    rw [tan_eq] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨b, -, rfl⟩ := hx
    have hy' := S.tanV_le_ker_prB hy
    have hy2 : y.2.1 = 0 := by simpa using hy'
    have hb : b = 0 := by
      have hb' : b + y.2.1 = 0 := by simpa using hB
      rwa [hy2, add_zero] at hb'
    subst hb
    simp only [map_zero, zero_add]
    exact ⟨hy, by simpa using hA⟩
  · rintro v ⟨hv, hA⟩
    exact ⟨by rw [tan_eq]; exact Submodule.mem_sup_right hv, hA, S.tanV_le_ker_prB hv⟩

/-- **W88's exponents add up**: `dim T_{G′} = t₀ + t₁ + t₂` with `t₀ = dim π₀`, `t₁ = dim U^⊥`,
`t₂ = dim (T_{G′} ∩ ker π₀ ∩ ker π₁)`. -/
theorem finrank_tan_eq :
    finrank ℂ S.tan = finrank ℂ (S.gam.map (LinearMap.fst ℂ _ _)) + finrank ℂ (torusLie S.U) +
      finrank ℂ ↥(S.tan ⊓ (LinearMap.ker prA ⊓ LinearMap.ker prB)) := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq ((torusLie S.U).map torIncl) S.tanV
  rw [disjoint_tor_tanV, finrank_bot, add_zero, ← tan_eq] at hsup
  have htor : finrank ℂ ((torusLie S.U).map (torIncl : _ →ₗ[ℂ] TanV d₀ d₁ m r)) =
      finrank ℂ (torusLie S.U) := by
    refine (Submodule.equivMapOfInjective _ ?_ _).finrank_eq.symm
    intro x y h; simpa using congrArg (fun p : TanV d₀ d₁ m r => p.2.1) h
  -- rank–nullity for `prA` on `tanV`
  have hrn := LinearMap.finrank_range_add_finrank_ker (prA.comp S.tanV.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, map_prA_tanV] at hrn
  have hker : finrank ℂ (LinearMap.ker (prA.comp S.tanV.subtype)) =
      finrank ℂ ↥(S.tanV ⊓ LinearMap.ker prA) := by
    rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  rw [hker] at hrn
  rw [tan_inf_ker, hsup, htor, ← hrn]
  omega

end SubgroupPreV

end

end LSG.MEV
