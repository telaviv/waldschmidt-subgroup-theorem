/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dA

/-!
# W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × A^r` in `TanA` coordinates

**`theorem41AbVarPer : Theorem41AbVarPer`** (`StatementAbVar.lean`): the generic `theorem41B_of` (`AbVarSec7.lean`)
for the block family `B = fun _ : Fin r => aBlock`, with `MultEstB` (`LSG.MEB.multEstB_holds`) and the packages
`aBlockAnF`, `tayAll_aBlockW`.

The coordinate translation is the one of `AbVar5dA.lean`: `MEB.Tan d₀ d₁ B = TanA d₀ d₁ r`, `LamB = LamA`,
`PerL = PerA` and `RationalOverQbarB = RationalOverQbarA` hold definitionally; `Σ_k aBlock.g = 2r`;
`TorInjA ⇒ TorInjB` (`span_perL`); `SubgroupDataB ⇒ SubgroupDataA` (`isRatSub_perAb_iff`), with the same `tan`,
`δ₀`, `δ₁` and, after `Σ_k 2 = 2r`, the same `δ₂`.
-/

open Module LSG.AuxA LSG.JacBlock

noncomputable section

namespace LSG.W88

open LSG.MEB (PerL perAbL)

/-- **W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × A^r`, rational-period `A`-parts, under (NR) and (TorInj).** -/
theorem theorem41AbVarPer : Theorem41AbVarPer := by
  intro d0 d1 r V W Y hn hWV hW hYfg hYVL hTor hNR
  have h41 := theorem41B_of LSG.MEB.multEstB_holds (aBlockAnF r) (tayAll_aBlockW r)
  have hΛle : ∀ k, latF (aBlockAnF r) k ≤ ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_le
  have hΛ : ∀ k, IsNsmulIn (latF (aBlockAnF r) k) ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_nsmul
  have hspan := LSG.MEB.span_perL (d₀ := d0) (d₁ := d1) hΛle hΛ
  have hsum : ∑ _k : Fin r, aBlock.g = 2 * r := by
    change ∑ _k : Fin r, (2 : ℕ) = 2 * r
    simp [mul_comm]
  have hTor' : TorInjB (d₀ := d0) (d₁ := d1) (B := fun _ : Fin r => aBlock) V :=
    fun v hv hP h1 => hTor v hv (by rw [← hspan] at hP; exact hP) h1
  obtain ⟨H, hP, hτ, hineq⟩ := h41 d0 d1 V W Y (by rw [hsum]; exact hn) hWV hW hYfg hYVL hTor' hNR
  have hset : {z | z ∈ H.t ∧ z ∈ perAbL (latF (aBlockAnF r))} =
      {z : Fin r → Fin 2 → ℂ | z ∈ H.t ∧ ∀ j, z j ∈ LSG.JacAn.latt} := by
    ext z
    simp only [Set.mem_ofPred_eq, perAbL, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    rfl
  have htab : IsAbelianTangentA H.t := by
    have := (LSG.MEB.isRatSub_perAb_iff hΛle hΛ H.t).mpr H.t_rat
    unfold LSG.MEB.IsRatSub at this
    unfold IsAbelianTangentA
    exact this.trans (congrArg (Submodule.span ℝ) hset)
  set H' : SubgroupDataA d0 d1 r := ⟨H.h0, H.U, H.t, H.h0_rat, htab⟩ with hH'
  have hδ2 : H'.δ2 = H.δ2 := by
    change 2 * r - finrank ℂ H.t = (∑ _k : Fin r, aBlock.g) - finrank ℂ H.t
    rw [hsum]
  have hδ : H'.δ = H.δ := by
    change H.δ0 + H.δ1 + H'.δ2 = H.δ0 + H.δ1 + H.δ2
    rw [hδ2]
  refine ⟨H', ?_, ?_, ?_⟩
  · change H'.δ ≠ 0
    rw [hδ]; exact hP
  · rw [hδ]; exact hτ
  · rw [hδ, hδ2]
    rw [hsum] at hineq
    exact hineq

end LSG.W88
