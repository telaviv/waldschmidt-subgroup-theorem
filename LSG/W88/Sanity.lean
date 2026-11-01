/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Main
open Module LSG.W88 Complex

/-!
# Sanity checks: classical theorems as instances of `Theorem41Abelian`

Gel'fond–Schneider (`G = G_m²`, `V = W = ℂ(1, b)`) and Schneider's period theorem (`G = G_a × E`)
derived from `LSG.W88.theorem41Abelian`, as evidence that the formal statement has teeth
(`REVIEW_STATEMENT.md`).
-/

namespace LSG.W88.Sanity

noncomputable def u0 (b : ℂ) : Tan 0 2 0 := ((0 : Fin 0 → ℂ), ![1, b], (0 : Fin 0 → ℂ))

theorem u0_ne (b : ℂ) : u0 b ≠ 0 := by
  intro h
  have := congrArg (fun p : Tan 0 2 0 => p.2.1 0) h
  simp [u0] at this

theorem alg_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (k : ℤ) : IsAlgebraic ℚ (z ^ k) := by
  have : z ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hz
  exact mem_algebraicClosure_iff.mp (zpow_mem this k)

theorem rk_bot {E : Type*} [AddCommGroup E] [Module ℚ E] : rk (⊥ : AddSubgroup E) = 0 := by
  simp [rk, AddSubgroup.coe_bot]

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

/-- **Gelfond–Schneider from `Theorem41Abelian`** (G = G_m², d₀ = m = 0, V = W = ℂ(1,b),
Y = ℤ·(x, bx)): if `x ≠ 0`, `e^x` algebraic, `b` algebraic irrational, then `e^{bx}` is
transcendental. -/
theorem gelfondSchneider_of (hT : Theorem41Abelian) (x b : ℂ) (hx : x ≠ 0)
    (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ q)
    (ha : IsAlgebraic ℚ (exp x)) (hc : IsAlgebraic ℚ (exp (b * x))) : False := by
  let Ls : Fin 0 → PeriodPair := Fin.elim0
  let V : Submodule ℂ (Tan 0 2 0) := ℂ ∙ u0 b
  let u : Tan 0 2 0 := x • u0 b
  let Y : AddSubgroup (Tan 0 2 0) := AddSubgroup.zmultiples u
  have hu0 := u0_ne b
  have hu : u ≠ 0 := smul_ne_zero hx hu0
  have hVdim : finrank ℂ V = 1 := finrank_span_singleton hu0
  have huV : u ∈ V := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- components of k • u
  have hcomp : ∀ k : ℤ, ∀ i, (k • u).2.1 i = (k : ℂ) * x * ![1, b] i := by
    intro k i
    fin_cases i <;> simp [u, u0, zsmul_eq_mul] <;> ring
  -- V is ℚ̄-rational
  have hrat : RationalOverQbarTan V := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, ?_, ?_, ?_⟩
      · exact fun i => i.elim0
      · intro i; fin_cases i
        · simpa [u0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
        · simpa [u0] using hb
      · exact fun i => i.elim0
    · exact Submodule.span_le.mpr fun w hw => hw.1
  -- Y ∩ Ω = 0
  have hYPer : Y ⊓ Per Ls = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyP⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hyY
    obtain ⟨-, hP1, -⟩ := hyP
    by_cases hk : k = 0
    · simp [hk]
    exfalso
    obtain ⟨n0, hn0⟩ := hP1 0
    obtain ⟨n1, hn1⟩ := hP1 1
    rw [hcomp] at hn0 hn1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hn0 hn1
    have hkx : (k : ℂ) * x ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hx
    have hn0' : (n0 : ℂ) ≠ 0 := by
      intro h; apply hkx; rw [hn0, h]; simp
    have : (k : ℂ) * x * b * (n0 : ℂ) = (k : ℂ) * x * (n1 : ℂ) := by
      calc (k : ℂ) * x * b * n0 = (k * x * b) * n0 := by ring
        _ = (2 * Real.pi * I * n1) * n0 := by rw [hn1]
        _ = (2 * Real.pi * I * n0) * n1 := by ring
        _ = (k : ℂ) * x * n1 := by rw [hn0]
    have hbn : b * n0 = n1 := mul_left_cancel₀ hkx (by linear_combination this)
    apply hbq ((n1 : ℚ) / n0)
    push_cast
    rw [eq_div_iff hn0']; exact hbn
  have hrkYPer : rk (Y ⊓ Per Ls) = 0 := by rw [hYPer]; exact rk_bot
  have hrkY : rk Y = 1 := rk_zmultiples hu
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 0 2 0 Ls (fun j => j.elim0) V V Y
    (by rw [hVdim]; norm_num) le_rfl hrat
    ((AddSubgroup.fg_iff _).mpr ⟨{u}, (AddSubgroup.zmultiples_eq_closure u).symm,
      Set.finite_singleton u⟩)
    (by
      intro y hy
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      refine ⟨zsmul_mem huV k, fun i => i.elim0, fun i => ?_, fun j => j.elim0⟩
      rw [hcomp]
      fin_cases i
      · simpa [exp_int_mul] using alg_zpow ha k
      · have := alg_zpow hc k
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [show (k : ℂ) * x * b = k * (b * x) by ring, exp_int_mul]; exact this)
    (by rw [hrkYPer, hVdim])
  -- structure of H for d₀ = m = 0
  have hδ0 : H.δ0 = 0 := by simp [SubgroupData.δ0]
  have hδ2 : H.δ2 = 0 := by simp [SubgroupData.δ2]
  have hδ : H.δ = H.δ1 := by simp [SubgroupData.δ, hδ0, hδ2]
  have hU : H.U ≠ ⊥ := by
    intro h
    apply hprop
    rw [hδ, SubgroupData.δ1, h, finrank_bot]
  -- u0 b ∉ T_{G'}
  have hnot : u0 b ∉ H.tan := by
    intro hmem
    have h2 : ![1, b] ∈ torusLie H.U := hmem.2.1
    obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have he := h2 φ hφU
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at he
    by_cases h1 : φ 1 = 0
    · apply hφ0
      have h0 : φ 0 = 0 := by
        rw [h1] at he; push_cast at he; simpa using he
      funext i; fin_cases i <;> simp [h0, h1]
    · apply hbq (-(φ 0) / φ 1)
      have h1' : (φ 1 : ℂ) ≠ 0 := by exact_mod_cast h1
      push_cast
      field_simp
      linear_combination he
  have hWtan : V ⊓ H.tan = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvT⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
    by_cases hc0 : c = 0
    · simp [hc0]
    · exact absurd (by simpa [hc0] using H.tan.smul_mem c⁻¹ hvT) hnot
  have hτ1 : finrank ℂ V - finrank ℂ ↥(V ⊓ H.tan) = 1 := by
    rw [hWtan, finrank_bot, hVdim]
  -- so δ₁ = 2, U = ⊤
  have hδ1le : H.δ1 ≤ 2 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupData.δ1] using this
  have hδ1 : H.δ1 = 2 := by rw [hτ1, hδ] at hτ; omega
  have hUtop : H.U = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa [SubgroupData.δ1] using hδ1)
  have htan : H.tan = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨-, hp2, -⟩ := hp
    have hz : p.2.1 = 0 := by
      funext i
      have := hp2 (Pi.single i 1) (by rw [hUtop]; trivial)
      fin_cases i <;> simpa [Fin.sum_univ_two, Pi.single_apply] using this
    have h1 : p.1 = 0 := Subsingleton.elim _ _
    have h3 : p.2.2 = 0 := Subsingleton.elim _ _
    exact (Submodule.mem_bot ℂ).mpr (Prod.ext h1 (Prod.ext hz h3))
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) = 0 := by
    rw [htan, Submodule.bot_toAddSubgroup, bot_sup_eq]; exact hrkYPer
  rw [hrkY, hlam, hδ1, hδ2, hτ1, hδ, hδ1, hrkYPer, hVdim] at hineq
  norm_num at hineq

/-- Instantiated with the proved theorem. -/
theorem gelfondSchneider (x b : ℂ) (hx : x ≠ 0)
    (hb : IsAlgebraic ℚ b) (hbq : ∀ q : ℚ, b ≠ q)
    (ha : IsAlgebraic ℚ (exp x)) : Transcendental ℚ (exp (b * x)) :=
  fun hc => gelfondSchneider_of theorem41Abelian x b hx hb hbq ha hc


noncomputable def e0 : Tan 1 0 1 := (![1], (0 : Fin 0 → ℂ), ![1])

theorem e0_ne : e0 ≠ 0 := by
  intro h
  have := congrArg (fun p : Tan 1 0 1 => p.1 0) h
  simp [e0] at this

/-- **Schneider's period theorem from `Theorem41Abelian`** (G = G_a × E, d₀ = m = 1, d₁ = 0,
V = W = ℂ(1,1), Y = ℤ·(ω, ω)). -/
theorem period_of (hT : Theorem41Abelian) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (ω : ℂ) (hω : ω ∈ L.lattice) (hω0 : ω ≠ 0)
    (halg : IsAlgebraic ℚ ω) : False := by
  let Ls : Fin 1 → PeriodPair := fun _ => L
  let V : Submodule ℂ (Tan 1 0 1) := ℂ ∙ e0
  let u : Tan 1 0 1 := ω • e0
  let Y : AddSubgroup (Tan 1 0 1) := AddSubgroup.zmultiples u
  have hu : u ≠ 0 := smul_ne_zero hω0 e0_ne
  have hVdim : finrank ℂ V = 1 := finrank_span_singleton e0_ne
  have huV : u ∈ V := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hc1 : ∀ k : ℤ, (k • u).1 0 = (k : ℂ) * ω := by intro k; simp [u, e0, zsmul_eq_mul]
  have hc3 : ∀ k : ℤ, (k • u).2.2 0 = (k : ℂ) * ω := by intro k; simp [u, e0, zsmul_eq_mul]
  have hrat : RationalOverQbarTan V := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ⟨Submodule.mem_span_singleton_self _, ?_, ?_, ?_⟩
      · intro i; fin_cases i; simpa [e0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
      · exact fun i => i.elim0
      · intro i; fin_cases i; simpa [e0] using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
    · exact Submodule.span_le.mpr fun w hw => hw.1
  have hYPer : Y ⊓ Per Ls = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyP⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hyY
    obtain ⟨h1, -, -⟩ := hyP
    have := congrFun h1 0
    rw [hc1] at this
    have hk : (k : ℂ) = 0 := by simpa [hω0] using this
    have hk' : k = 0 := by exact_mod_cast hk
    simp [hk']
  have hrkYPer : rk (Y ⊓ Per Ls) = 0 := by rw [hYPer]; exact rk_bot
  have hrkY : rk Y = 1 := rk_zmultiples hu
  obtain ⟨H, hprop, hτ, hineq⟩ := hT 1 0 1 Ls (fun _ => ⟨hg₂, hg₃⟩) V V Y
    (by rw [hVdim]; norm_num) le_rfl hrat
    ((AddSubgroup.fg_iff _).mpr ⟨{u}, (AddSubgroup.zmultiples_eq_closure u).symm,
      Set.finite_singleton u⟩)
    (by
      intro y hy
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      refine ⟨zsmul_mem huV k, fun i => ?_, fun i => i.elim0, fun j => Or.inl ?_⟩
      · fin_cases i
        show IsAlgebraic ℚ ((k • u).1 0)
        rw [hc1]
        exact mem_algebraicClosure_iff.mp (mul_mem
          (mem_algebraicClosure_iff.mpr (isAlgebraic_intCast k)) (mem_algebraicClosure_iff.mpr halg))
      · fin_cases j
        show (k • u).2.2 0 ∈ L.lattice
        rw [hc3]
        rw [show (k : ℂ) * ω = k • ω by simp [zsmul_eq_mul]]
        exact zsmul_mem hω k)
    (by rw [hrkYPer, hVdim])
  have hδ1 : H.δ1 = 0 := by
    have := Submodule.finrank_le H.U
    simpa [SubgroupData.δ1] using this
  have hh0le : finrank ℂ H.h0 ≤ 1 := by simpa using Submodule.finrank_le H.h0
  have htle : finrank ℂ H.t ≤ 1 := by simpa using Submodule.finrank_le H.t
  have hnot : e0 ∉ H.tan := by
    intro hmem
    obtain ⟨hh, -, ht⟩ := hmem
    have a1 : H.h0 ≠ ⊥ := fun h => by
      rw [h] at hh
      have := congrFun ((Submodule.mem_bot ℂ).mp hh) 0; simp [e0] at this
    have a2 : H.t ≠ ⊥ := fun h => by
      rw [h] at ht
      have := congrFun ((Submodule.mem_bot ℂ).mp ht) 0; simp [e0] at this
    have b1 : 0 < finrank ℂ H.h0 := Nat.pos_of_ne_zero fun h => a1 (Submodule.finrank_eq_zero.mp h)
    have b2 : 0 < finrank ℂ H.t := Nat.pos_of_ne_zero fun h => a2 (Submodule.finrank_eq_zero.mp h)
    apply hprop
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1]
    omega
  have hWtan : V ⊓ H.tan = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvT⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvV
    by_cases hc0 : c = 0
    · simp [hc0]
    · exact absurd (by simpa [hc0] using H.tan.smul_mem c⁻¹ hvT) hnot
  have hτ1 : finrank ℂ V - finrank ℂ ↥(V ⊓ H.tan) = 1 := by
    rw [hWtan, finrank_bot, hVdim]
  rw [hτ1] at hτ
  have hh0 : finrank ℂ H.h0 = 0 := by
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1] at hτ; omega
  have ht0 : finrank ℂ H.t = 0 := by
    simp only [SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ2, hδ1] at hτ; omega
  have hδ0 : H.δ0 = 1 := by simp [SubgroupData.δ0, hh0]
  have hδ2 : H.δ2 = 1 := by simp [SubgroupData.δ2, ht0]
  have hδ : H.δ = 2 := by simp [SubgroupData.δ, hδ0, hδ1, hδ2]
  have htan : H.tan = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨hp1, -, hp3⟩ := hp
    rw [Submodule.finrank_eq_zero.mp hh0] at hp1
    rw [Submodule.finrank_eq_zero.mp ht0] at hp3
    replace hp1 := (Submodule.mem_bot ℂ).mp hp1
    replace hp3 := (Submodule.mem_bot ℂ).mp hp3
    exact (Submodule.mem_bot ℂ).mpr (Prod.ext hp1 (Prod.ext (Subsingleton.elim _ _) hp3))
  have hlam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) = 0 := by
    rw [htan, Submodule.bot_toAddSubgroup, bot_sup_eq]; exact hrkYPer
  rw [hrkY, hlam, hδ1, hδ2, hτ1, hδ, hrkYPer, hVdim] at hineq
  norm_num at hineq

theorem period_transcendental' (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (ω : ℂ) (hω : ω ∈ L.lattice) (hω0 : ω ≠ 0) :
    Transcendental ℚ ω :=
  fun h => period_of theorem41Abelian L hg₂ hg₃ ω hω hω0 h

end LSG.W88.Sanity

