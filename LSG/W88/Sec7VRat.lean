/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7VCount
import LSG.W88.Sec7Rat
import LSG.ME.MainAbAux

/-!
# W88 §7 for the class `𝒞`: from the obstruction on `G̃_r` to a `ℚ̄`-rational subgroup of `G`

For `O : ObstrDataV` with `T̃′ = O.tan ⊇ K_M` and `T′ = pushT(T̃′)` (`tanG O`):

* **Exponents** (`t0_eq`, `t2_eq`, `tau_eq`): `O.t0 = dim π₀ T′`,
  `O.t2 = dim (T′ ∩ ker π₀ ∩ ker π₁) + m`,
  and `dim W̃ − dim (W̃ ∩ T̃′) = dim W − dim (W ∩ T′)` for `W̃ = liftT W`.
* **`tanG_eq`**: `T′ = Γ_full ⊕ U^⊥ ⊕ perTan_M(t)`, `Γ_full = T′ ∩ (vector group)`.
* **Rationality repair** (`exists_subgroupDataV_rat`), under `r ≤ 1` and `LiftAlg`: with
  `Γ″ = span_ℂ` of the algebraic vectors of `Γ_full`, the member `H″ = (U, t, Γ″)` of
  `SubgroupDataV`
  has the same `λ` (`LiftAlg` makes the vector component of `y ∈ Y ∩ (T′ + Ω)` algebraic), the same
  `δ₁, δ₂` (`r ≤ 1`: the fibre part of `Γ_full` is `0` or the whole fibre, hence rational), and
  `δ″ − τ″ ≥ δ − τ`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module LSG.MEV
open LSG.W88.Vec (TanV PerV LamV AlgMat etaV zetaV vecIncl torIncl g2Incl perTanId perTan RatPair
  AlgPair SubgroupDataV LiftAlg)
open LSG.ME (g2L g3L)

noncomputable section

namespace LSG.W88

variable {d0 r d1 m : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### The push-out of the obstruction -/

section Push

variable (O : ObstrDataV d0 r d1 Ls M)

theorem tan_eq_comap : O.tan = (tanG O).comap (pushT (d0 := d0) (d1 := d1) M) := by
  rw [tanG, Submodule.comap_map_eq, ker_pushT]
  exact (sup_eq_left.mpr O.ker_le).symm

theorem mem_tan_iff {p : TanG (d0 + r) d1 m} : p ∈ O.tan ↔ pushT M p ∈ tanG O := by
  rw [tan_eq_comap O]; rfl

theorem liftT_mem_tan {x : TanV d0 d1 m r} : liftT x ∈ O.tan ↔ x ∈ tanG O := by
  rw [mem_tan_iff, pushT_liftT]

theorem kvec_injective : Function.Injective (kvec (d₀ := d0) (d₁ := d1) M) := fun v v' h => by
  have := congrArg (fun p : TanG (d0 + r) d1 m => p.2.2.2) h
  simpa [kvec] using this

theorem finrank_kerK : finrank ℂ (kerK (d₀ := d0) (d₁ := d1) M) = m := by
  rw [kerK, LinearMap.finrank_range_of_inj kvec_injective]; simp

theorem t0_eq : O.t0 = finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) := by
  rw [ObstrDataV.t0, tanG, ← Submodule.map_comp]
  congr 2

/-- The `G`-exponent `t₂ = dim (T′ ∩ ker π₀ ∩ ker π₁)`. -/
def t2G : ℕ := finrank ℂ ↥(tanG O ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
  LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r))))

theorem t2_eq : O.t2 = t2G O + m := by
  classical
  set A := O.tan ⊓ (LinearMap.ker (prLead (d₀ := d0) (r := r) (d₁ := d1) (m := m)) ⊓
    LinearMap.ker (prB (d₀ := d0 + r) (d₁ := d1) (m := m) (r := m)))
  set B := tanG O ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
    LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r)))
  set f := (pushT (d0 := d0) (d1 := d1) M).comp A.subtype
  have hrange : LinearMap.range f = B := by
    apply le_antisymm
    · rintro _ ⟨⟨p, hpT, hpA, hpB⟩, rfl⟩
      refine ⟨⟨p, hpT, rfl⟩, ?_, ?_⟩
      · change (pushT (d0 := d0) (d1 := d1) M p).1 = 0
        funext i
        have := congrFun (show prLead p = 0 from hpA) i
        simpa using this
      · change (pushT (d0 := d0) (d1 := d1) M p).2.1 = 0
        exact hpB
    · rintro x ⟨hxT, hxA, hxB⟩
      have hxA' : x.1 = 0 := hxA
      have hxB' : x.2.1 = 0 := hxB
      refine ⟨⟨liftT x, (liftT_mem_tan O).mpr hxT, ?_, ?_⟩, pushT_liftT M x⟩
      · change prLead (liftT x) = 0
        funext i; simp [hxA']
      · change (liftT x).2.1 = 0
        simp [hxB']
  have hker : finrank ℂ (LinearMap.ker f) = m := by
    set φ := A.subtype ∘ₗ (LinearMap.ker f).subtype
    have hφ : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
    have hφr : LinearMap.range φ = kerK (d₀ := d0) (d₁ := d1) M := by
      apply le_antisymm
      · rintro _ ⟨p, rfl⟩
        rw [← ker_pushT]
        exact LinearMap.mem_ker.mp p.2
      · intro q hq
        have hq' : pushT (d0 := d0) (d1 := d1) M q = 0 := by
          rw [← ker_pushT] at hq; exact hq
        obtain ⟨v, rfl⟩ := hq
        have hA : kvec (d₀ := d0) (d₁ := d1) M v ∈ A := by
          refine ⟨O.ker_le ⟨v, rfl⟩, ?_, ?_⟩
          · change prLead (kvec (d₀ := d0) (d₁ := d1) M v) = 0
            funext i; simp [kvec]
          · change (kvec (d₀ := d0) (d₁ := d1) M v).2.1 = 0
            simp [kvec]
        exact ⟨⟨⟨_, hA⟩, LinearMap.mem_ker.mpr hq'⟩, rfl⟩
    rw [← LinearMap.finrank_range_of_inj hφ, hφr, finrank_kerK]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker] at hrn
  rw [ObstrDataV.t2, t2G]
  change finrank ℂ A = finrank ℂ B + m
  omega

theorem tau_eq (W : Submodule ℂ (TanV d0 d1 m r)) :
    finrank ℂ (W.map liftT) - finrank ℂ ↥(W.map liftT ⊓ O.tan) =
      finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) := by
  have h1 : finrank ℂ (W.map liftT) = finrank ℂ W :=
    (Submodule.equivMapOfInjective _ liftT_injective W).finrank_eq.symm
  have h2 : W.map liftT ⊓ O.tan = (W ⊓ tanG O).map liftT := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxT⟩
      exact ⟨x, ⟨hx, (liftT_mem_tan O).mp hxT⟩, rfl⟩
    · rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (liftT_mem_tan O).mpr hxT⟩
  have h3 : finrank ℂ ↥((W ⊓ tanG O).map liftT) = finrank ℂ ↥(W ⊓ tanG O) :=
    (Submodule.equivMapOfInjective _ liftT_injective _).finrank_eq.symm
  rw [h1, h2, h3]

/-! ### The structure of `T′` -/

theorem prB_tanG {x : TanV d0 d1 m r} (hx : x ∈ tanG O) : x.2.1 ∈ torusLie O.S.U := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact prB_mem_torusLie O hp

theorem piZ_tanG {x : TanV d0 d1 m r} (hx : x ∈ tanG O) : x.2.2.1 ∈ O.S.t := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact tan_map_piZ_le O ⟨p, hp, rfl⟩

theorem torIncl_mem_tanG {b : Fin d1 → ℂ} (hb : b ∈ torusLie O.S.U) :
    (torIncl b : TanV d0 d1 m r) ∈ tanG O := by
  refine ⟨torIncl b, Submodule.mem_sup_left (Submodule.mem_sup_right ⟨b, hb, rfl⟩), ?_⟩
  ext <;> simp

theorem g2Incl_mem_tanG {z w : Fin m → ℂ} (h : (z, w) ∈ perTanId Ls O.S.t) :
    (g2Incl (z, M.mulVec w) : TanV d0 d1 m r) ∈ tanG O :=
  ⟨g2Incl (z, w), g2Incl_perTanId_mem O h, by ext <;> simp⟩

theorem perTan_le_tanG : (perTan Ls M O.S.t).map g2Incl ≤ tanG O := by
  rintro _ ⟨_, ⟨⟨z, w⟩, h, rfl⟩, rfl⟩
  exact g2Incl_mem_tanG O h

/-- `Γ_full = T′ ∩ (vector group)`. -/
def gamFull : Submodule ℂ ((Fin d0 → ℂ) × (Fin r → ℂ)) := (tanG O).comap vecIncl

/-- The decomposition of an element of `T′`. -/
theorem decomp_tanG {x : TanV d0 d1 m r} (hx : x ∈ tanG O) :
    ∃ w : Fin m → ℂ, (x.2.2.1, w) ∈ perTanId Ls O.S.t ∧
      (x.1, x.2.2.2 - M.mulVec w) ∈ gamFull O ∧
      x = vecIncl (x.1, x.2.2.2 - M.mulVec w) + torIncl x.2.1 + g2Incl (x.2.2.1, M.mulVec w) := by
  obtain ⟨w, hw⟩ := exists_perTanId O.S.t_ab (piZ_tanG O hx)
  have e : x = vecIncl (x.1, x.2.2.2 - M.mulVec w) + torIncl x.2.1 +
      g2Incl (x.2.2.1, M.mulVec w) := by
    ext <;> simp
  refine ⟨w, hw, ?_, e⟩
  change vecIncl (x.1, x.2.2.2 - M.mulVec w) ∈ tanG O
  have : vecIncl (x.1, x.2.2.2 - M.mulVec w) =
      x - torIncl x.2.1 - (g2Incl (x.2.2.1, M.mulVec w) : TanV d0 d1 m r) := by
    rw [e]; ext <;> simp
  rw [this]
  exact (tanG O).sub_mem ((tanG O).sub_mem hx (torIncl_mem_tanG O (prB_tanG O hx)))
    (g2Incl_mem_tanG O hw)

/-- The member of the family of `G` (no rationality) with tangent space `T′`. -/
def preG : SubgroupPreV (d₀ := d0) (d₁ := d1) Ls M :=
  { U := O.S.U, t := O.S.t, gam := gamFull O, t_ab := O.S.t_ab }

theorem preG_tan : (preG O).tan = tanG O := by
  apply le_antisymm
  · refine sup_le (sup_le (Submodule.map_comap_le _ _) ?_) (perTan_le_tanG O)
    rintro _ ⟨b, hb, rfl⟩
    exact torIncl_mem_tanG O hb
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

variable (O : ObstrDataV d0 r d1 Ls M)

/-- `Γ″`: the span of the algebraic vectors of `Γ_full`. -/
def gamRat : Submodule ℂ ((Fin d0 → ℂ) × (Fin r → ℂ)) :=
  Submodule.span ℂ {v | v ∈ gamFull O ∧ AlgPair v}

theorem gamRat_le : gamRat O ≤ gamFull O := Submodule.span_le.mpr fun _ hv => hv.1

theorem gamRat_rat : RatPair (gamRat O) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr fun w hw => hw.1)
  exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hv.2⟩

/-- **The `ℚ̄`-rational subgroup `H″ = (U, t, Γ″)`.** -/
def dataRat : SubgroupDataV (d0 := d0) (d1 := d1) Ls M :=
  { U := O.S.U, t := O.S.t, gam := gamRat O, gam_rat := gamRat_rat O, t_ab := O.S.t_ab }

theorem dataRat_tan_le : (dataRat O).tan ≤ tanG O := by
  rw [← preG_tan O]
  exact sup_le_sup_right (sup_le_sup_right (Submodule.map_mono (gamRat_le O)) _) _

/-- `r ≤ 1`: the fibre part of `Γ_full` lies in `Γ″`. -/
theorem fib_mem_gamRat (hr : r ≤ 1) {s : Fin r → ℂ} (hs : ((0 : Fin d0 → ℂ), s) ∈ gamFull O) :
    ((0 : Fin d0 → ℂ), s) ∈ gamRat O := by
  rcases Nat.lt_or_ge r 1 with h0 | h1
  · have : s = 0 := funext fun i => absurd i.2 (by omega)
    subst this; exact Submodule.zero_mem _
  · have hr1 : r = 1 := by omega
    subst hr1
    by_cases hs0 : s 0 = 0
    · have : s = 0 := funext fun i => by rw [Fin.fin_one_eq_zero i, hs0]; rfl
      subst this; exact Submodule.zero_mem _
    · have e : ((0 : Fin d0 → ℂ), s) = s 0 • ((0 : Fin d0 → ℂ), (fun _ => 1 : Fin 1 → ℂ)) := by
        ext i <;> simp [Fin.fin_one_eq_zero]
      have h1' : ((0 : Fin d0 → ℂ), (fun _ => 1 : Fin 1 → ℂ)) ∈ gamFull O := by
        have : ((0 : Fin d0 → ℂ), (fun _ => 1 : Fin 1 → ℂ)) =
            (s 0)⁻¹ • ((0 : Fin d0 → ℂ), s) := by
          ext i <;> simp [Fin.fin_one_eq_zero, hs0]
        rw [this]; exact (gamFull O).smul_mem _ hs
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨h1', fun i => ?_, fun i => ?_⟩)
      · simpa using isAlgebraic_zero
      · simpa using isAlgebraic_one

theorem tanG_inf_le_dataRat (hr : r ≤ 1) :
    tanG O ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
      LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r))) ≤ (dataRat O).tan := by
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

/-- **The `G_a`/graph part becomes rational without changing `λ`** (`LiftAlg`). -/
theorem mem_dataRat_of_lam (hLA : LiftAlg Ls) (hM : AlgMat M) {y : TanV d0 d1 m r}
    (hy : y ∈ LamV Ls M) {x ω : TanV d0 d1 m r} (hx : x ∈ tanG O) (hω : ω ∈ PerV Ls M)
    (hxy : y = x + ω) : x ∈ (dataRat O).tan := by
  obtain ⟨hω1, -, hω3, hω4⟩ := hω
  -- the base point is algebraic
  have hz : ∀ j, x.2.2.1 j ∈ (Ls j).lattice ∨ IsAlgebraic ℚ ((Ls j).weierstrassP (x.2.2.1 j)) := by
    intro j
    have hxj : x.2.2.1 j = y.2.2.1 j - ω.2.2.1 j := by rw [hxy]; simp
    rcases hy.2.2.1 j with h | h
    · exact Or.inl (hxj ▸ (Ls j).lattice.sub_mem h (hω3 j))
    · refine Or.inr ?_
      have hp := (Ls j).weierstrassP_add_coe (y.2.2.1 j - ω.2.2.1 j) ⟨_, hω3 j⟩
      simp only [sub_add_cancel] at hp
      rw [hxj, ← hp]; exact h
  obtain ⟨w, hw, hwalg⟩ := hLA O.S.t O.S.t_ab x.2.2.1 (piZ_tanG O hx) hz
  have hzeta : zetaV Ls y.2.2.1 = zetaV Ls x.2.2.1 + etaV Ls ω.2.2.1 := by
    funext j
    have hyj : y.2.2.1 j = x.2.2.1 j + ω.2.2.1 j := by rw [hxy]; simp
    simp only [zetaV, etaV, Pi.add_apply, hyj]
    exact zeta_add (Ls j) (hω3 j) _
  -- the vector component
  have hvec : (x.1, x.2.2.2 - M.mulVec w) ∈ gamFull O := by
    change vecIncl (x.1, x.2.2.2 - M.mulVec w) ∈ tanG O
    have : vecIncl (x.1, x.2.2.2 - M.mulVec w) =
        x - torIncl x.2.1 - (g2Incl (x.2.2.1, M.mulVec w) : TanV d0 d1 m r) := by ext <;> simp
    rw [this]
    exact (tanG O).sub_mem ((tanG O).sub_mem hx (torIncl_mem_tanG O (prB_tanG O hx)))
      (g2Incl_mem_tanG O hw)
  have halg : AlgPair (x.1, x.2.2.2 - M.mulVec w) := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have : x.1 = y.1 := by rw [hxy]; simp [hω1]
      rw [this]; exact hy.1 i
    · have hs : x.2.2.2 - M.mulVec w =
          (y.2.2.2 - M.mulVec (zetaV Ls y.2.2.1)) - M.mulVec (w - zetaV Ls x.2.2.1) := by
        have hy4 : y.2.2.2 = x.2.2.2 + ω.2.2.2 := by rw [hxy]; simp
        rw [hy4, hω4, hzeta, Matrix.mulVec_add, Matrix.mulVec_sub]; abel
      rw [hs]
      refine (hy.2.2.2 i).sub ?_
      simp only [Matrix.mulVec, dotProduct]
      exact isAlgebraic_sum _ _ fun j _ => (hM i j).mul (hwalg j)
  obtain ⟨-, -, -, e⟩ := decomp_tanG O hx
  have e' : x = vecIncl (x.1, x.2.2.2 - M.mulVec w) + torIncl x.2.1 +
      g2Incl (x.2.2.1, M.mulVec w) := by ext <;> simp
  rw [e']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      ⟨_, Submodule.subset_span ⟨hvec, halg⟩, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, prB_tanG O hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨(x.2.2.1, M.mulVec w), ⟨(x.2.2.1, w), hw, rfl⟩, rfl⟩

theorem inf_tanPerV_eq (hLA : LiftAlg Ls) (hM : AlgMat M) (Y : AddSubgroup (TanV d0 d1 m r))
    (hY : ∀ y ∈ Y, y ∈ LamV Ls M) :
    Y ⊓ ((dataRat O).tan.toAddSubgroup ⊔ PerV Ls M) = Y ⊓ ((tanG O).toAddSubgroup ⊔ PerV Ls M) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (sup_le_sup_right (fun x hx => dataRat_tan_le O hx) _)
  · rintro y ⟨hyY, hyT⟩
    refine ⟨hyY, ?_⟩
    obtain ⟨x, hx, ω, hω, rfl⟩ := AddSubgroup.mem_sup.mp hyT
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left
      (show x ∈ (dataRat O).tan from mem_dataRat_of_lam O hLA hM (hY _ hyY) hx hω rfl))
      (AddSubgroup.mem_sup_right hω)

/-! ### Codimensions -/

theorem finrank_gamFull_fst :
    finrank ℂ ((gamFull O).map (LinearMap.fst ℂ _ _)) =
      finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) := by
  have := (preG O).map_prA_tan
  rw [preG_tan] at this
  rw [show gamFull O = (preG O).gam from rfl, ← this]

theorem finrank_tanG : finrank ℂ (tanG O) =
    finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + (d1 - finrank ℚ O.S.U) + t2G O := by
  have h := (preG O).finrank_tan_eq
  rw [preG_tan] at h
  change finrank ℂ (tanG O) = finrank ℂ ((gamFull O).map (LinearMap.fst ℂ _ _)) +
    finrank ℂ (torusLie O.S.U) + t2G O at h
  have ht := LSG.ME.finrank_torusLie O.S.U
  rw [h, finrank_gamFull_fst O]
  omega

theorem dataRat_t2 (hr : r ≤ 1) :
    finrank ℂ ↥((dataRat O).tan ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
      LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r)))) = t2G O := by
  rw [t2G]
  have e : (dataRat O).tan ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
      LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r))) =
      tanG O ⊓ (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
      LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r))) :=
    le_antisymm (inf_le_inf_right _ (dataRat_tan_le O))
      (le_inf (tanG_inf_le_dataRat O hr) inf_le_right)
  rw [e]

theorem finrank_dataRat (hr : r ≤ 1) : finrank ℂ (dataRat O).tan =
    finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _)) + (d1 - finrank ℚ O.S.U) + t2G O := by
  have h := SubgroupPreV.finrank_tan_eq (d₀ := d0) (d₁ := d1)
    ({ U := O.S.U, t := O.S.t, gam := gamRat O, t_ab := O.S.t_ab } :
      SubgroupPreV (d₀ := d0) (d₁ := d1) Ls M)
  have ht := LSG.ME.finrank_torusLie O.S.U
  have h2 := dataRat_t2 O hr
  change finrank ℂ (dataRat O).tan = finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _)) +
    finrank ℂ (torusLie O.S.U) + finrank ℂ ↥((dataRat O).tan ⊓
      (LinearMap.ker (prA (d₀ := d0) (d₁ := d1) (m := m) (r := r)) ⊓
      LinearMap.ker (prB (d₀ := d0) (d₁ := d1) (m := m) (r := r)))) at h
  rw [h, h2]
  omega

/-- **The repair.** Same `λ`, `δ₁`, `δ₂`; `δ − τ` does not decrease. -/
theorem exists_subgroupDataV_rat (hr : r ≤ 1) (hLA : LiftAlg Ls) (hM : AlgMat M)
    (W : Submodule ℂ (TanV d0 d1 m r)) (Y : AddSubgroup (TanV d0 d1 m r))
    (hY : ∀ y ∈ Y, y ∈ LamV Ls M) (hdim : t2G O ≤ m + r) :
    ∃ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M,
      Y ⊓ (H.tan.toAddSubgroup ⊔ PerV Ls M) = Y ⊓ ((tanG O).toAddSubgroup ⊔ PerV Ls M) ∧
      H.δ1 = finrank ℚ O.S.U ∧ H.δ2 = m + r - t2G O ∧
      ((d0 - finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) + finrank ℚ O.S.U + (m + r - t2G O) :
          ℕ) : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ tanG O) : ℕ) : ℤ) ≤
        (H.δ : ℤ) - ((finrank ℂ W - finrank ℂ ↥(W ⊓ H.tan) : ℕ) : ℤ) := by
  have hR := finrank_dataRat O hr
  have hT := finrank_tanG O
  have hfst : finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _)) ≤
      finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) := by
    rw [← finrank_gamFull_fst O]
    exact Submodule.finrank_mono (Submodule.map_mono (gamRat_le O))
  have hfd : finrank ℂ ((tanG O).map (LinearMap.fst ℂ _ _)) ≤ d0 := by
    simpa using Submodule.finrank_le ((tanG O).map (LinearMap.fst ℂ (Fin d0 → ℂ) _))
  have hU : finrank ℚ O.S.U ≤ d1 := by simpa using Submodule.finrank_le O.S.U
  have hle := finrank_inf_add_le W (tanG O) (dataRat O).tan (dataRat_tan_le O)
  have hW1 := Submodule.finrank_mono (inf_le_left : W ⊓ tanG O ≤ W)
  have hW2 := Submodule.finrank_mono (inf_le_left : W ⊓ (dataRat O).tan ≤ W)
  refine ⟨dataRat O, inf_tanPerV_eq O hLA hM Y hY, rfl, ?_, ?_⟩
  · change d0 + d1 + m + r - finrank ℂ (dataRat O).tan -
      (d0 - finrank ℂ ((gamRat O).map (LinearMap.fst ℂ _ _))) - finrank ℚ O.S.U = m + r - t2G O
    rw [hR]; omega
  · change _ ≤ ((d0 + d1 + m + r - finrank ℂ (dataRat O).tan : ℕ) : ℤ) - _
    rw [hR]; rw [hT] at hle; rw [hR] at hle
    omega

end Rat

end LSG.W88
