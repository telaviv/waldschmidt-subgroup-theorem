/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVar5dPivot
import LSG.JacBlock.PackagesW88
import LSG.MEB.SubgroupMain

/-!
# A5.9f: the §5d engine for `G_a^{d₀} × G_m^{d₁} × A^r` in `TanA` coordinates

**`hyperplaneKappaAbVar_of_rat`**: `HyperplaneKappaAbVar` (`StatementAbVar.lean`) from `hyperplaneKappaB_of_ME` for
`B = fun _ : Fin r => aBlock`, with `MultEstB` (`LSG.MEB.multEstB_holds`), the packages `aBlockAnF`, `tayAll_aBlockW`,
and the one remaining hypothesis `hratA`: for `ℚ̄`-rational `W` and a subgroup `H`, `W ∩ T_H` is `ℚ̄`-rational
(CM rationality of the abelian subvarieties of `A^r`).

The coordinates agree definitionally (`aBlock.g = 2`, `MEB.Tan d₀ d₁ (fun _ => aBlock) = TanA d₀ d₁ r`,
`aBlockAn.lat = latt`), so `LamA = LamB`, `PerA = PerL`, `AlgTanA = AlgTanB` by `rfl`. Converted: `d₂ = Σ_k 2 = 2r`,
`TorInjA ⇒ TorInjB` (`span_perL`), `SubgroupDataB ⇒ SubgroupDataA` (`isRatSub_perAb_iff`).
-/

open Module LSG.AuxA LSG.JacBlock

noncomputable section

namespace LSG.W88

open LSG.MEB (PerL perAbL)

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × A^r` on toric-injective hyperplanes**, given the rationality of `W ∩ T_H`. -/
theorem hyperplaneKappaAbVar_of_rat
    (hratA : ∀ (d0 d1 r : ℕ) (W : Submodule ℂ (MEB.Tan d0 d1 (fun _ : Fin r => aBlock)))
      (H : SubgroupDataB d0 d1 (fun _ : Fin r => aBlock)),
      RationalOverQbarB W → RationalOverQbarB (W ⊓ H.tan)) :
    HyperplaneKappaAbVar := by
  intro d0 d1 r
  have h := hyperplaneKappaB_of_ME (d₀ := d0) (d₁ := d1) LSG.MEB.multEstB_holds (aBlockAnF r)
    (tayAll_aBlockW r) (hratA d0 d1 r)
  have hΛle : ∀ k, latF (aBlockAnF r) k ≤ ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_le
  have hΛ : ∀ k, IsNsmulIn (latF (aBlockAnF r) k) ((fun _ : Fin r => aBlock) k).per :=
    fun k => (aBlockAnF r k).lat_nsmul
  have hspan := LSG.MEB.span_perL (d₀ := d0) (d₁ := d1) hΛle hΛ
  intro V W n y hV hWV hW hgood hy hineq
  have hgood' : TorInjB (d₀ := d0) (d₁ := d1) (B := fun _ : Fin r => aBlock) V :=
    fun v hv hP h1 => hgood v hv (by rw [← hspan] at hP; exact hP) h1
  have h2 : (gmB d0 d1 (aBlockAnF r)).d₂ = 2 * r := by
    change ∑ _k : Fin r, (2 : ℕ) = 2 * r
    simp [mul_comm]
  obtain ⟨S, ⟨H, rfl⟩, hne, hle⟩ := h V W n y hV hWV hW hgood' hy (by
    rw [h2]; exact hineq)
  have hset : {z | z ∈ H.t ∧ z ∈ perAbL (latF (aBlockAnF r))} =
      {z : Fin r → Fin 2 → ℂ | z ∈ H.t ∧ ∀ j, z j ∈ LSG.JacAn.latt} := by
    ext z
    simp only [Set.mem_setOf_eq, perAbL, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    rfl
  have htab : IsAbelianTangentA H.t := by
    have := (LSG.MEB.isRatSub_perAb_iff hΛle hΛ H.t).mpr H.t_rat
    unfold LSG.MEB.IsRatSub at this
    unfold IsAbelianTangentA
    exact this.trans (congrArg (Submodule.span ℝ) hset)
  exact ⟨H.tan, ⟨⟨H.h0, H.U, H.t, H.h0_rat, htab⟩, rfl⟩, hne, hle⟩

end LSG.W88
