/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dFrame

/-!
# Frames of members, continued: periods, logarithms, subgroups, `LiftAlg` for sub-families

For a frame `F` of a member `H` (`V5dFrame`):
* `map_span_per`: `Psi(span_ℚ Ω(G_H)) = span_ℚ Ω(G) ∩ T_{G'}` (so `κ`, `λ` are unchanged by
  transport);
* `Phi_mem_lamV`: `Phi` maps `Λ(G) ∩ T_{G'}` into `Λ(G_H)` (uses `LiftAlg`);
* `Psi_mem_fibreV`: fibre to fibre;
* `push`: a member `H_s` of `G_H` gives a member of `G` with `T = Psi(T_{H_s})` (`push_tan`), the
  same
  `dim pr₀ Γ` and `dim U^⊥`;
* `liftAlg_comp`: `LiftAlg Ls → LiftAlg (Ls ∘ ι)` for injective `ι` (via extension by zero).
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

variable (Ls M d0 d1) in
/-- `span_ℚ Ω(G)`. -/
noncomputable abbrev OmV : Submodule ℚ (TanV d0 d1 m r) :=
  Submodule.span ℚ ((PerV (d0 := d0) (d1 := d1) Ls M : AddSubgroup (TanV d0 d1 m r)) :
    Set (TanV d0 d1 m r))

/-- Rational toric periods lie in `span_ℚ Ω`. -/
lemma torPer_mem (q : Fin d1 → ℚ) :
    (((0 : Fin d0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL d1 q, (0 : Fin m → ℂ), (0 : Fin r → ℂ)) :
      TanV d0 d1 m r) ∈ OmV d0 d1 Ls M := by
  have : (((0 : Fin d0 → ℂ), (2 * Real.pi * I : ℂ) • K11.castL d1 q, (0 : Fin m → ℂ),
      (0 : Fin r → ℂ)) : TanV d0 d1 m r) = ∑ j, q j • (((0 : Fin d0 → ℂ),
        (Pi.single j (2 * Real.pi * I) : Fin d1 → ℂ), (0 : Fin m → ℂ), (0 : Fin r → ℂ)) :
          TanV d0 d1 m r) := by
    refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext ?_ (Prod.ext (by simp [Prod.snd_sum])
      (by simp [Prod.snd_sum])))
    ext i; simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply, Rat.smul_def,
      mul_comm, K11.castL]
  rw [this]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨rfl, fun i => ⟨if i = j then 1 else 0, ?_⟩, fun _ => (Ls _).lattice.zero_mem, ?_⟩
  · change (Pi.single j (2 * Real.pi * I) : Fin d1 → ℂ) i = _
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · change (0 : Fin r → ℂ) = M.mulVec (etaV Ls 0)
    rw [etaV_zero', Matrix.mulVec_zero]

lemma torPer_eq {x : Fin d1 → ℂ} (hx : ∀ i, ∃ k : ℤ, x i = 2 * Real.pi * I * k) :
    ∃ q : Fin d1 → ℚ, x = (2 * Real.pi * I : ℂ) • K11.castL d1 q := by
  choose k hk using hx
  exact ⟨fun i => (k i : ℚ), by ext i; simp [hk i, K11.castL, mul_comm]⟩

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

lemma latVec_lift_of {μ : Fin (fg H) → ℂ} (hμ : LatVec F.LsH μ) :
    ∃ n : ℕ, n ≠ 0 ∧ LatVec Ls (F.c.lift (n • μ)) :=
  F.c.exists_nsmul_lift_mem H.t_ab hμ

include F in
lemma mem_t_of_tan {y : TanV d0 d1 m r} (hy : y ∈ H.tan) : y.2.2.1 ∈ H.t := by
  rw [← F.Psi_Phi hy, Psi_apply]; exact F.c.lift_mem _

/-- `Psi` on the period of `(μ, η_J(μ))` (one copy of `ℂ^g`). -/
lemma Psi_per (k : Fin (fk1 H) → ℂ) (μ : Fin (fg H) → ℂ) :
    F.Psi (0, k, μ, F.MH.mulVec (etaV F.LsH μ)) =
      ((0, (K11.cm F.C).mulVec k, 0, 0) : TanV d0 d1 m r) +
        (0, 0, F.c.lift μ, M.mulVec (F.K μ + F.N (etaV F.LsH μ))) := by
  rw [Psi_apply, F.Fm_MH]
  refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) ?_))
  simp [Matrix.mulVec_add]

/-- **Periods**: `Psi(span_ℚ Ω(G_H)) = span_ℚ Ω(G) ∩ T_{G'}`. -/
theorem map_span_per :
    (OmV (fk0 H) (fk1 H) F.LsH F.MH).map (F.Psi.restrictScalars ℚ) =
      OmV d0 d1 Ls M ⊓ H.tan.restrictScalars ℚ := by
  apply le_antisymm
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨?_, F.Psi_mem_tan x⟩
    obtain ⟨q, hq⟩ := torPer_eq h2
    have hx : x = (0, x.2.1, x.2.2.1, F.MH.mulVec (etaV F.LsH x.2.2.1)) :=
      Prod.ext h1 (Prod.ext rfl (Prod.ext rfl h4))
    change F.Psi x ∈ _
    rw [hx, Psi_per]
    refine Submodule.add_mem _ ?_ ?_
    · rw [hq, Matrix.mulVec_smul, K11.cm_mulVec_castL]; exact torPer_mem _
    · obtain ⟨n, hn, hlat⟩ := F.latVec_lift_of h3
      refine K11.mem_span_of_nsmul_mem _ (Nat.pos_of_ne_zero hn) ?_
      have hl := F.c.lift_mem (n • x.2.2.1)
      have he := etaV_eq_of_mem F.c H.t_ab hl hlat
      rw [F.c.proj_lift] at he
      have hη : etaV F.LsH (n • x.2.2.1) = n • etaV F.LsH x.2.2.1 := by
        rw [← natCast_zsmul, etaV_zsmul F.LsH h3, natCast_zsmul]
      have e : n • (((0 : Fin d0 → ℂ), (0 : Fin d1 → ℂ), F.c.lift x.2.2.1,
          M.mulVec (F.K x.2.2.1 + F.N (etaV F.LsH x.2.2.1))) : TanV d0 d1 m r) =
          (0, 0, F.c.lift (n • x.2.2.1), M.mulVec (etaV Ls (F.c.lift (n • x.2.2.1)))) := by
        rw [he, hη]
        refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext ?_ ?_))
        · change n • F.c.lift x.2.2.1 = F.c.lift (n • x.2.2.1); rw [map_nsmul]
        · change n • M.mulVec (F.K x.2.2.1 + F.N (etaV F.LsH x.2.2.1)) =
            M.mulVec (F.K (n • x.2.2.1) + F.N (n • etaV F.LsH x.2.2.1))
          rw [map_nsmul, map_nsmul, ← smul_add, Matrix.mulVec_smul]
      rw [e]
      exact ⟨rfl, fun i => ⟨0, by simp⟩, hlat, rfl⟩
  · rintro y ⟨hyP, hyT⟩
    obtain ⟨n, hn, hny⟩ := K11.exists_nsmul_mem_of_mem_span _ hyP
    have hnyT : n • y ∈ H.tan := H.tan.smul_of_tower_mem n hyT
    obtain ⟨h1, h2, h3, h4⟩ := hny
    have hlt := F.mem_t_of_tan hnyT
    have he := etaV_eq_of_mem F.c H.t_ab hlt h3
    obtain ⟨q, hq⟩ := torPer_eq h2
    have hPhi : F.Phi (n • y) ∈ OmV (fk0 H) (fk1 H) F.LsH F.MH := by
      rw [Phi_apply]
      have e : ((F.Bm (n • y).1, (K11.cm F.D).mulVec (n • y).2.1, LSG.CM.proj F.c.ι (n • y).2.2.1,
          F.Fl ((n • y).2.2.2 - F.G (F.Bm (n • y).1) -
            M.mulVec (F.K (LSG.CM.proj F.c.ι (n • y).2.2.1)))) :
            TanV (fk0 H) (fk1 H) (fg H) (ff H)) =
          (0, (2 * Real.pi * I : ℂ) • K11.castL (fk1 H) (F.D.mulVec q), 0, 0) +
          (0, 0, LSG.CM.proj F.c.ι (n • y).2.2.1,
            F.MH.mulVec (etaV F.LsH (LSG.CM.proj F.c.ι (n • y).2.2.1))) := by
        rw [h1, h4, he, hq, F.MH_mulVec]
        refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext (by simp) ?_))
        · simp [Matrix.mulVec_smul, K11.cm_mulVec_castL]
        · simp [Matrix.mulVec_add]
      rw [e]
      refine Submodule.add_mem _ (torPer_mem _) (Submodule.subset_span ?_)
      exact ⟨rfl, fun i => ⟨0, by simp⟩, fun k => h3 (F.c.ι k), by simp⟩
    have : y = F.Psi ((n : ℚ)⁻¹ • F.Phi (n • y)) := by
      rw [LinearMap.map_smul_of_tower, F.Psi_Phi hnyT, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    exact ⟨_, Submodule.smul_mem _ _ hPhi, this.symm⟩

/-- **Logarithms**: `Phi(Λ(G) ∩ T_{G'}) ⊂ Λ(G_H)`. -/
theorem Phi_mem_lamV (hM : AlgMat M) (hLA : LiftAlg Ls) {y : TanV d0 d1 m r}
    (hyL : y ∈ LamV Ls M) (hyT : y ∈ H.tan) : F.Phi y ∈ LamV F.LsH F.MH := by
  obtain ⟨ha, hb, hz, hs⟩ := hyL
  have hzt := F.mem_t_of_tan hyT
  obtain ⟨w, hw, hwalg⟩ := hLA H.t H.t_ab y.2.2.1 hzt hz
  set p := LSG.CM.proj F.c.ι y.2.2.1 with hp
  set pw := LSG.CM.proj F.c.ι w with hpw
  have hweq : w = F.K p + F.N pw := congrArg Prod.snd (perTanId_eq F.c H.t_ab hw)
  have hMw : M.mulVec w = M.mulVec (F.K p) + M.mulVec (F.N pw) := by
    rw [hweq, Matrix.mulVec_add]
  rw [Phi_apply, ← hp]
  refine ⟨F.algB _ ha, fun i => K5d.exp_cm_mulVec F.D hb i, fun k => hz (F.c.ι k), ?_⟩
  have h1 : AlgVec (y.2.2.2 - M.mulVec w) := by
    have := algVec_sub hs (algLin_mat hM _ hwalg)
    convert this using 1
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_sub]; abel
  have h2 : AlgVec (pw - zetaV F.LsH p) := by
    have := algLin_proj F.c.ι _ hwalg
    convert this using 1
    rw [map_sub]; rfl
  have h3 := algVec_add (F.algFl _ (algVec_sub h1 (F.algG _ (F.algB _ ha))))
    (algLin_mat (F.algMat_MH hM) _ h2)
  convert h3 using 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_sub, hMw]
  simp only [F.MH_mulVec, map_sub, map_add]
  abel

lemma Psi_fibre (σ : Fin (ff H) → ℂ) : F.Psi (0, 0, 0, σ) = (0, 0, 0, F.Fm σ) := by
  rw [Psi_apply]; simp

end Frame

lemma mem_fibreV_iff {x : TanV d0 d1 m r} :
    x ∈ (fibreV : Submodule ℂ (TanV d0 d1 m r)) ↔ x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 := by
  constructor
  · rintro ⟨s, rfl⟩; simp [vecIncl_apply]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x.2.2.2, Prod.ext (by simp [h1]) (Prod.ext (by simp [h2]) (Prod.ext (by simp [h3]) rfl))⟩

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

/-- **Fibre**: `V ∩ fibre = 0` is inherited by `Psi⁻¹ V`. -/
lemma comap_inf_fibreV {V : Submodule ℂ (TanV d0 d1 m r)} (hV : V ⊓ fibreV = ⊥) :
    V.comap F.Psi ⊓ fibreV = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, mem_fibreV_iff] at hx
  obtain ⟨hxV, hxF⟩ := hx
  have hx : x = (0, 0, 0, x.2.2.2) := Prod.ext hxF.1 (Prod.ext hxF.2.1 (Prod.ext hxF.2.2 rfl))
  have hmem : F.Psi x ∈ V ⊓ fibreV := by
    refine Submodule.mem_inf.mpr ⟨hxV, ?_⟩
    rw [hx, F.Psi_fibre, mem_fibreV_iff]; simp
  rw [hV, Submodule.mem_bot] at hmem
  rw [Submodule.mem_bot]
  exact F.Psi_injective (by rw [hmem, map_zero])

end Frame


end LSG.W88.V5d
