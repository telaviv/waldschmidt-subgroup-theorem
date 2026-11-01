/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOnto
import LSG.W88.V5dPer
import LSG.W88.V5dFrame2
import LSG.CM.Inst
import LSG.CM.Block
import LSG.W88.V5dOntoMain
import LSG.W88.V5dMXPMain


/-!
# Non-vacuity of the vector-extension statements (sanity derivations)

From each of `theorem41VecLA_onto`, `theorem41Vec2` and `hyperplaneKappaVec_uncond` we derive that `η(ω₁)` is not an
algebraic multiple of `ω₁` (for the lemniscatic lattice: `π/ϖ² ∉ ℚ̄`, a case of Masser's theorem), on
`G = E^♮` (`d₀ = d₁ = 0`, `m = r = 1`, `M = 1`) with `V = W = ℂ(1, β)` and `Y = ℤ(ω₁, η₁)`; the contradiction comes
from Legendre's relation. Written by the vector-statement review (`REVIEW_STATEMENT_VEC.md`, appendix).
-/

open Module Complex LSG.W88 LSG.W88.Vec

namespace LSG.W88.SanityVec

abbrev T := TanV 0 0 1 1

noncomputable def u0 (β : ℂ) : T := (0, 0, ![1], ![β])

theorem u0_ne (β : ℂ) : u0 β ≠ 0 := by
  intro h
  have := congrArg (fun p : T => p.2.2.1 0) h
  simp [u0] at this

theorem rk_zmultiples {E : Type*} [AddCommGroup E] [Module ℚ E] {u : E} (hu : u ≠ 0) :
    rk (AddSubgroup.zmultiples u) = 1 := by
  unfold rk
  have : Submodule.span ℚ (AddSubgroup.zmultiples u : Set E) = ℚ ∙ u := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe]
      rw [show (k • u : E) = (k : ℚ) • u by rw [Int.cast_smul_eq_zsmul]]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span (AddSubgroup.mem_zmultiples u)
  rw [this, finrank_span_singleton hu]

/-- Periods are logarithms of algebraic points (here `d₀ = d₁ = 0`). -/
theorem perV_le_lamV {m r : ℕ} (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    {p : TanV 0 0 m r} (hp : p ∈ PerV Ls M) : p ∈ LamV Ls M := by
  obtain ⟨-, -, hlat, hs⟩ := hp
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun j => Or.inl (hlat j), ?_⟩
  have hz : zetaV Ls p.2.2.1 = etaV Ls p.2.2.1 := by
    funext j; exact zeta_of_mem_lattice (Ls j) (hlat j)
  rw [hz, ← hs, sub_self]
  intro i; simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0 : ℂ))

noncomputable def Ls1 (L : PeriodPair) : Fin 1 → PeriodPair := fun _ => L
noncomputable def M1 : Matrix (Fin 1) (Fin 1) ℂ := 1
noncomputable def V1 (β : ℂ) : Submodule ℂ T := ℂ ∙ u0 β

theorem V1_dim (β : ℂ) : finrank ℂ (V1 β) = 1 := finrank_span_singleton (u0_ne β)

theorem V1_fib (β : ℂ) : V1 β ⊓ fibreV = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvF⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
  have := (LSG.W88.V5d.mem_fibreV_iff.mp hvF).2.2
  have hc : c = 0 := by simpa [u0] using congrFun this 0
  simp [hc]

theorem tan_ne (L : PeriodPair) (β : ℂ) (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (Ls1 L) M1) (hVeq : V1 β = H.tan) : False := by
  classical
  have hVdim := V1_dim β
  by_cases ht : H.t = ⊥
  · -- `T_{G'}` lies in the fibre
    have hle : H.tan ≤ fibreV := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨p, -, rfl⟩
        exact LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, rfl⟩
      · rintro _ ⟨p, -, rfl⟩
        exact LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, rfl⟩
      · rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, rfl⟩ := hp
        have h1 := LSG.W88.V5d.fst_mem_of_mem_perTanId (Ls1 L) hq
        rw [ht] at h1
        refine LSG.W88.V5d.mem_fibreV_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
        exact (Submodule.mem_bot ℂ).mp h1
    have h2 : V1 β ⊓ fibreV = V1 β := inf_eq_left.mpr (hVeq ▸ hle)
    rw [V1_fib] at h2
    have := congrArg (fun S : Submodule ℂ T => finrank ℂ S) h2
    simp [hVdim] at this
  · -- `t = ⊤`: the second period lies in `V`, contradicting Legendre
    have htop : H.t = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : 0 < finrank ℂ H.t := Nat.pos_of_ne_zero fun h0 =>
        ht (Submodule.finrank_eq_zero.mp h0)
      have h2 := Submodule.finrank_le H.t
      simp at h2 ⊢; omega
    let q : (Fin 1 → ℂ) × (Fin 1 → ℂ) := (![L.ω₂], etaV (Ls1 L) ![L.ω₂])
    have hq : q ∈ perTanId (Ls1 L) H.t := Submodule.subset_span
      ⟨by rw [htop]; trivial, fun j => by simpa [q, Ls1] using L.ω₂_mem_lattice, rfl⟩
    have hmem : g2Incl ((LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M1)) q) ∈ H.tan :=
      Submodule.mem_sup_right ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [← hVeq] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have e1 := congrArg (fun p : T => p.2.2.1 0) hc
    have e2 := congrArg (fun p : T => p.2.2.2 0) hc
    simp [u0, q, M1, etaV, Ls1] at e1 e2
    have hleg := LSG.Weierstrass.legendre_ne_zero L
    apply hleg
    rw [hη, ← e2, ← e1]; ring

/-- Analysis of the subgroup produced by the theorem. -/
theorem H_false (L : PeriodPair) (β : ℂ) (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁)
    (Y : AddSubgroup T) (hrkY : rk Y = 1) (hYP : Y ≤ PerV (Ls1 L) M1)
    (H : SubgroupDataV (d0 := 0) (d1 := 0) (Ls1 L) M1) (hprop : H.Proper)
    (hτ : finrank ℂ (V1 β) - finrank ℂ ↥(V1 β ⊓ H.tan) < H.δ)
    (hineq : (((rk Y - rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV (Ls1 L) M1)) + H.δ1 + 2 * H.δ2 : ℕ) : ℤ) *
        ((0 + 0 + 1 + 1 : ℕ) - finrank ℂ (V1 β) : ℤ) ≤
      ((H.δ : ℤ) - (finrank ℂ (V1 β) - finrank ℂ ↥(V1 β ⊓ H.tan) : ℕ)) *
        ((0 + 2 * (1 + 1) : ℕ) - rk (Y ⊓ PerV (Ls1 L) M1) : ℤ))) : False := by
  classical
  have hVdim := V1_dim β
  have hYPer : Y ⊓ PerV (Ls1 L) M1 = Y := inf_eq_left.mpr hYP
  have hδ0 : H.δ0 = 0 := by simp [SubgroupDataV.δ0]
  have hδ1 : H.δ1 = 0 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupDataV.δ1] using this
  have hδ2 : H.δ2 = H.δ := by simp [SubgroupDataV.δ2, hδ0, hδ1]
  have hδdef : H.δ = 2 - finrank ℂ H.tan := rfl
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ PerV (Ls1 L) M1)) = 1 := by
    rw [inf_eq_left.mpr (hYP.trans le_sup_right), hrkY]
  rw [hrkY, hlam, hδ1, hδ2, hYPer, hrkY, hVdim] at hineq
  have hb1 : finrank ℂ ↥(V1 β ⊓ H.tan) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : V1 β ⊓ H.tan ≤ V1 β); omega
  rw [hVdim] at hτ
  have hb : finrank ℂ ↥(V1 β ⊓ H.tan) = 1 := by push_cast at hineq; omega
  have hδpos : 1 ≤ H.δ := by omega
  have hVt : V1 β ≤ H.tan := by
    have h1 : finrank ℂ (V1 β) ≤ finrank ℂ ↥(V1 β ⊓ H.tan) := by omega
    have := Submodule.eq_of_le_of_finrank_le (inf_le_left : V1 β ⊓ H.tan ≤ V1 β) h1
    rw [← this]; exact inf_le_right
  have htan_le : finrank ℂ H.tan ≤ 1 := by omega
  have hVeq : V1 β = H.tan := Submodule.eq_of_le_of_finrank_le hVt (htan_le.trans hVdim.ge)
  exact tan_ne L β hη H hVeq

/-- **Sanity derivation from the proved `Theorem41VecLAOnto`** (`G = E^♮`, `d₀ = d₁ = 0`, `m = r = 1`,
`M = 1`, `V = W = ℂ(1, β)`, `Y = ℤ(ω₁, η(ω₁))`, `κ = 1`): `η(ω₁)` is not an algebraic multiple of `ω₁`. -/
theorem eta_ne_alg_mul (hT : Theorem41VecLAOnto) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (hLA : LiftAlg (Ls1 L))
    (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁) : False := by
  classical
  have hω0 : L.ω₁ ≠ 0 := by
    intro h; have := L.indep.ne_zero 0; simp [h] at this
  have hy0 : (L.ω₁ : ℂ) • u0 β ≠ 0 := smul_ne_zero hω0 (u0_ne β)
  have hyV : (L.ω₁ : ℂ) • u0 β ∈ V1 β := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hyP : (L.ω₁ : ℂ) • u0 β ∈ PerV (Ls1 L) M1 := by
    refine ⟨Subsingleton.elim _ _, fun i => i.elim0, fun j => ?_, ?_⟩
    · simpa [u0, Ls1] using L.ω₁_mem_lattice
    · funext i
      fin_cases i
      simp [u0, M1, etaV, Ls1, hη, mul_comm]
  have hYP : AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β) ≤ PerV (Ls1 L) M1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    exact zsmul_mem hyP k
  have hrkY := rk_zmultiples hy0
  have hrat : RatSubV (V1 β) := by
    apply le_antisymm
    · rw [V1, Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, fun i => i.elim0,
        fun i => i.elim0, ?_, ?_⟩
      · intro i; fin_cases i; simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · intro i; fin_cases i; simpa [u0] using hβ
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hM : AlgMat M1 := by
    intro i j; fin_cases i; fin_cases j; simpa [M1] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  have hSurj : Function.Surjective M1.mulVec := fun x => ⟨x, by simp [M1]⟩
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 0 0 1 1 (Ls1 L) M1 (fun _ => ⟨hg₂, hg₃⟩) hM le_rfl hLA hSurj
    (V1 β) (V1 β) (AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β))
    (by rw [V1_dim]; norm_num) le_rfl hrat (V1_fib β)
    ((AddSubgroup.fg_iff _).mpr ⟨{(L.ω₁ : ℂ) • u0 β},
      (AddSubgroup.zmultiples_eq_closure _).symm, Set.finite_singleton _⟩)
    (fun z hz => ⟨by
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
        exact zsmul_mem hyV k, perV_le_lamV (Ls1 L) M1 (hYP hz)⟩)
    (by rw [inf_eq_left.mpr hYP, hrkY, V1_dim]; norm_num)
  exact H_false L β hη _ hrkY hYP H hprop hτ hineq

theorem eta_ne_alg_mul_lem (hg₂ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₃) (β : ℂ) (hβ : IsAlgebraic ℚ β) :
    LSG.Weierstrass.eta LSG.W88.MStarCopy.lemniscatic LSG.W88.MStarCopy.lemniscatic.ω₁ ≠
      β * LSG.W88.MStarCopy.lemniscatic.ω₁ :=
  fun h => eta_ne_alg_mul theorem41VecLA_onto _ hg₂ hg₃
    (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem) β hβ h

theorem eta_ne_alg_mul2 (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (hLA : LiftAlg (Ls1 L)) (hPT : PerTanRat (Ls1 L))
    (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta L L.ω₁ = β * L.ω₁) : False := by
  classical
  have hω0 : L.ω₁ ≠ 0 := by
    intro h; have := L.indep.ne_zero 0; simp [h] at this
  have hy0 : (L.ω₁ : ℂ) • u0 β ≠ 0 := smul_ne_zero hω0 (u0_ne β)
  have hyV : (L.ω₁ : ℂ) • u0 β ∈ V1 β := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hyP : (L.ω₁ : ℂ) • u0 β ∈ PerV (Ls1 L) M1 := by
    refine ⟨Subsingleton.elim _ _, fun i => i.elim0, fun j => ?_, ?_⟩
    · simpa [u0, Ls1] using L.ω₁_mem_lattice
    · funext i
      fin_cases i
      simp [u0, M1, etaV, Ls1, hη, mul_comm]
  have hYP : AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β) ≤ PerV (Ls1 L) M1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    exact zsmul_mem hyP k
  have hrkY := rk_zmultiples hy0
  have hrat : RatSubV (V1 β) := by
    apply le_antisymm
    · rw [V1, Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, fun i => i.elim0,
        fun i => i.elim0, ?_, ?_⟩
      · intro i; fin_cases i; simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · intro i; fin_cases i; simpa [u0] using hβ
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hM : AlgMat M1 := by
    intro i j; fin_cases i; fin_cases j; simpa [M1] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  have hSurj : Function.Surjective M1.mulVec := fun x => ⟨x, by simp [M1]⟩
  obtain ⟨H, hprop, hτ, hineq⟩ := LSG.W88.theorem41Vec2 0 0 1 1 (Ls1 L) M1 (fun _ => ⟨hg₂, hg₃⟩) hM rfl (by norm_num) hLA hPT
    (V1 β) (V1 β) (AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β))
    (by rw [V1_dim]; norm_num) le_rfl hrat (by rw [V1_fib]; simp)
    ((AddSubgroup.fg_iff _).mpr ⟨{(L.ω₁ : ℂ) • u0 β},
      (AddSubgroup.zmultiples_eq_closure _).symm, Set.finite_singleton _⟩)
    (fun z hz => ⟨by
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
        exact zsmul_mem hyV k, perV_le_lamV (Ls1 L) M1 (hYP hz)⟩)
    (by rw [inf_eq_left.mpr hYP, hrkY, V1_dim]; norm_num)
  exact H_false L β hη _ hrkY hYP H hprop hτ hineq

theorem eta_ne_alg_mul_lem2 (hg₂ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₃) (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta LSG.W88.MStarCopy.lemniscatic LSG.W88.MStarCopy.lemniscatic.ω₁ =
      β * LSG.W88.MStarCopy.lemniscatic.ω₁) : False :=
  eta_ne_alg_mul2 _ hg₂ hg₃ (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem)
    (LSG.CM.perTanRat_block (p := 1) LSG.CM.cmLem) β hβ hη

/-- The same from the proved `HyperplaneKappaVec` (W88 §5d, hyperplane `V = W = ℂ(1, β)` in `T(E^♮)`). -/
theorem eta_ne_alg_mul_5d (hg₂ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ LSG.W88.MStarCopy.lemniscatic.g₃) (β : ℂ) (hβ : IsAlgebraic ℚ β)
    (hη : LSG.Weierstrass.eta LSG.W88.MStarCopy.lemniscatic LSG.W88.MStarCopy.lemniscatic.ω₁ =
      β * LSG.W88.MStarCopy.lemniscatic.ω₁) : False := by
  classical
  set L := LSG.W88.MStarCopy.lemniscatic
  have hω0 : L.ω₁ ≠ 0 := by
    intro h; have := L.indep.ne_zero 0; simp [h] at this
  have hy0 : (L.ω₁ : ℂ) • u0 β ≠ 0 := smul_ne_zero hω0 (u0_ne β)
  have hyV : (L.ω₁ : ℂ) • u0 β ∈ V1 β := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hyP : (L.ω₁ : ℂ) • u0 β ∈ PerV (Ls1 L) M1 := by
    refine ⟨Subsingleton.elim _ _, fun i => i.elim0, fun j => ?_, ?_⟩
    · simpa [u0, Ls1] using L.ω₁_mem_lattice
    · funext i
      fin_cases i
      simp [u0, M1, etaV, Ls1, hη, mul_comm]
  have hYP : AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β) ≤ PerV (Ls1 L) M1 := by
    intro z hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    exact zsmul_mem hyP k
  have hrkY := rk_zmultiples hy0
  have hrat : RatSubV (V1 β) := by
    apply le_antisymm
    · rw [V1, Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, fun i => i.elim0,
        fun i => i.elim0, ?_, ?_⟩
      · intro i; fin_cases i; simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · intro i; fin_cases i; simpa [u0] using hβ
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hM : AlgMat M1 := by
    intro i j; fin_cases i; fin_cases j; simpa [M1] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  obtain ⟨H, hne, hle⟩ := LSG.W88.V5d.hyperplaneKappaVec_uncond 0 0 1 1 (Ls1 L) M1
    (fun _ => ⟨hg₂, hg₃⟩) hM le_rfl (LSG.CM.liftAlg_block (p := 1) hg₂ hg₃ LSG.CM.cmLem)
    (LSG.CM.perTanRat_block (p := 1) LSG.CM.cmLem)
    (V1 β) (V1 β) (AddSubgroup.zmultiples ((L.ω₁ : ℂ) • u0 β))
    (by rw [V1_dim]) le_rfl hrat
    ((AddSubgroup.fg_iff _).mpr ⟨{(L.ω₁ : ℂ) • u0 β},
      (AddSubgroup.zmultiples_eq_closure _).symm, Set.finite_singleton _⟩)
    (fun z hz => ⟨by
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
        exact zsmul_mem hyV k, perV_le_lamV (Ls1 L) M1 (hYP hz)⟩)
    (by rw [inf_eq_left.mpr hYP, hrkY, V1_dim]; norm_num)
  have h1 : 1 ≤ finrank ℂ H.tan := Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  have hVeq : H.tan = V1 β := Submodule.eq_of_le_of_finrank_le hle ((V1_dim β).le.trans h1)
  exact tan_ne L β hη H hVeq.symm

end LSG.W88.SanityVec

