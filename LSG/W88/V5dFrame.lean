/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dPer

/-!
# Frames of members `G' = T_U × (B̃ + Γ)`: `T_{G'}` as the tangent space of a class-`𝒞` group

For a member `H` of the subgroup family of `G = G_a^{d₀} × G_m^{d₁} × G₂` (`SubgroupDataV`), a
`Frame H`
is the coordinate data of the isomorphism `G_H → G'` from the class-`𝒞` group
`G_H = G_a^{k₀} × G_m^{k₁} × ((∏ₖ E_{ι k})^♮ pushed out along M_H : ℂ^g → ℂ^f)`:
* `A, Bm, G`: a `ℚ̄`-frame of `pr₀ Γ` (`k₀ = dim pr₀ Γ`) with left inverse `Bm` and a section `a ↦
  (A a, G a) ∈ Γ`;
* `C, D`: a `ℚ`-frame of `annQ U` (`k₁ = dim U^⊥`);
* a chart `c` of `t` (`g = dim t`), with `perK`, `perN` from `V5dPer`;
* `Fm, Fl`: a `ℚ̄`-frame of `V_f = M(fib B^♮) + Γ_fib ⊂ ℂ^r` (`f = dim V_f`, rational since `r ≤
  1`).
The isomorphism is `Psi (a, b, μ, σ) = (A a, C b, lift μ, G a + M κ_t(μ) + Fm σ)` (`range_Psi`),
with left
inverse `Phi`; `M_H = Fl ∘ M ∘ perN`. Consequences: `finrank_tan` (`dim T_{G'} = k₀ + k₁ + g + f`),
algebraicity of `Psi`, `Phi`, `M_H`.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

@[simp] lemma vecIncl_apply (p : (Fin d0 → ℂ) × (Fin r → ℂ)) :
    (vecIncl p : TanV d0 d1 m r) = (p.1, 0, 0, p.2) := rfl
@[simp] lemma torIncl_apply (x : Fin d1 → ℂ) : (torIncl x : TanV d0 d1 m r) = (0, x, 0, 0) := rfl
@[simp] lemma g2Incl_apply (p : (Fin m → ℂ) × (Fin r → ℂ)) :
    (g2Incl p : TanV d0 d1 m r) = (0, 0, p.1, p.2) := rfl

variable (Ls) in
/-- The fibre of `B^♮ → B`: `{w | (0, w) ∈ perTanId t}`. -/
noncomputable def fibId (t : Submodule ℂ (Fin m → ℂ)) : Submodule ℂ (Fin m → ℂ) :=
  (perTanId Ls t).comap (LinearMap.inr ℂ _ _)

/-- `V_f = M(fib B^♮) + Γ_fib ⊂ ℂ^r`, the fibre part of `G' ∩ G₂`. -/
noncomputable def Vf (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : Submodule ℂ (Fin r → ℂ) :=
  (fibId Ls H.t).map M.mulVecLin ⊔ H.gam.comap (LinearMap.inr ℂ _ _)

/-- `k₀ = dim pr₀ Γ`. -/
noncomputable abbrev fk0 (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : ℕ :=
  finrank ℂ (H.gam.map (LinearMap.fst ℂ (Fin d0 → ℂ) (Fin r → ℂ)))
/-- `k₁ = dim U^⊥`. -/
noncomputable abbrev fk1 (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : ℕ :=
  finrank ℚ (K11.annQ H.U)
/-- `g = dim t`. -/
noncomputable abbrev fg (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : ℕ := finrank ℂ H.t
/-- `f = dim V_f`. -/
noncomputable abbrev ff (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : ℕ := finrank ℂ (Vf H)

/-- **A frame of a member** (see the module docstring). -/
structure Frame (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) where
  c : LSG.CM.Chart H.t
  A : (Fin (fk0 H) → ℂ) →ₗ[ℂ] (Fin d0 → ℂ)
  Bm : (Fin d0 → ℂ) →ₗ[ℂ] (Fin (fk0 H) → ℂ)
  G : (Fin (fk0 H) → ℂ) →ₗ[ℂ] (Fin r → ℂ)
  C : Matrix (Fin d1) (Fin (fk1 H)) ℚ
  D : Matrix (Fin (fk1 H)) (Fin d1) ℚ
  Fm : (Fin (ff H) → ℂ) →ₗ[ℂ] (Fin r → ℂ)
  Fl : (Fin r → ℂ) →ₗ[ℂ] (Fin (ff H) → ℂ)
  BA : ∀ a, Bm (A a) = a
  rangeA : LinearMap.range A = H.gam.map (LinearMap.fst ℂ _ _)
  AG : ∀ a, (A a, G a) ∈ H.gam
  DC : D * C = 1
  rangeC : LinearMap.range C.mulVecLin = K11.annQ H.U
  FlFm : ∀ σ, Fl (Fm σ) = σ
  rangeFm : LinearMap.range Fm = Vf H
  algA : AlgLin A
  algB : AlgLin Bm
  algG : AlgLin G
  algFm : AlgLin Fm
  algFl : AlgLin Fl
  algK : AlgLin (perK c H.t_ab)
  algN : AlgLin (perN c H.t_ab)
  algLift : AlgLin c.lift

/-- A `ℚ̄`-frame of `pr₀ Γ` with an algebraic section into `Γ`. -/
lemma exists_secFrame {a b : ℕ} {Γ : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hΓ : RatPair Γ) :
    ∃ (A : (Fin (finrank ℂ (Γ.map (LinearMap.fst ℂ _ _))) → ℂ) →ₗ[ℂ] (Fin a → ℂ))
      (Bm : (Fin a → ℂ) →ₗ[ℂ] (Fin (finrank ℂ (Γ.map (LinearMap.fst ℂ _ _))) → ℂ))
      (G : (Fin (finrank ℂ (Γ.map (LinearMap.fst ℂ _ _))) → ℂ) →ₗ[ℂ] (Fin b → ℂ)),
      (∀ x, Bm (A x) = x) ∧ LinearMap.range A = Γ.map (LinearMap.fst ℂ _ _) ∧
      (∀ x, (A x, G x) ∈ Γ) ∧ AlgLin A ∧ AlgLin Bm ∧ AlgLin G := by
  classical
  set k := finrank ℂ (Γ.map (LinearMap.fst ℂ (Fin a → ℂ) (Fin b → ℂ)))
  have hrat0 : RationalOverQbar (Γ.map (LinearMap.fst ℂ (Fin a → ℂ) (Fin b → ℂ))) := by
    apply le_antisymm
    · conv_lhs => rw [hΓ]
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.subset_span ⟨⟨s, hs.1, rfl⟩, hs.2.1⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  obtain ⟨A0, B0, hBA, hA⟩ := K5d.exists_algFrame _ hrat0
  have hcol : ∀ j : Fin k, ∃ s, s ∈ Γ ∧ AlgPair s ∧
      LinearMap.fst ℂ (Fin a → ℂ) (Fin b → ℂ) s = (K5d.cmK K11.Kq A0).mulVec (Pi.single j 1) := by
    intro j
    have hmem : (K5d.cmK K11.Kq A0).mulVec (Pi.single j 1) ∈
        Γ.map (LinearMap.fst ℂ (Fin a → ℂ) (Fin b → ℂ)) := by
      have h := LinearMap.mem_range_self (K5d.cmK K11.Kq A0).mulVecLin (Pi.single j 1)
      rw [hA] at h; exact h
    obtain ⟨s, hs, hsa, hP⟩ := exists_alg_preimage hΓ (LinearMap.fst ℂ _ _)
      (fun v hv i => hv.1 i) hmem (algLin_cmK A0 _ (algVec_single j))
    exact ⟨s, hs, hsa, hP⟩
  choose s hs hsalg hsfst using hcol
  let Gm : Matrix (Fin b) (Fin k) ℂ := Matrix.of fun i j => (s j).2 i
  have hGa : AlgMat Gm := fun i j => (hsalg j).2 i
  refine ⟨(K5d.cmK K11.Kq A0).mulVecLin, (K5d.cmK K11.Kq B0).mulVecLin, Gm.mulVecLin,
    fun x => K5d.mulVec_left_invK hBA x, hA, fun x => ?_, algLin_cmK A0, algLin_cmK B0,
    algLin_mat hGa⟩
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin k → ℂ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  have : ((K5d.cmK K11.Kq A0).mulVecLin x, Gm.mulVecLin x) = ∑ j, x j • s j := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVecLin_apply, ← hsfst j]; rfl
    · simp only [Prod.snd_sum, Prod.smul_snd]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      funext i
      simp [Gm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hs j)

/-- **Every member has a frame** (`r ≤ 1`: `V_f` is rational; `PerTanRat`: `κ_t`, `N`, `lift`
algebraic). -/
theorem exists_frame (hr : r ≤ 1) (hPT : PerTanRat Ls)
    (H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M) : Nonempty (Frame H) := by
  obtain ⟨c0⟩ := LSG.CM.nonempty_chart H.t
  obtain ⟨A0, B0, G0, hBA, hA, hAG, hAa, hBa, hGa⟩ := exists_secFrame H.gam_rat
  obtain ⟨C0, D0, hDC, hC⟩ := K11.exists_frame (K11.annQ H.U)
  obtain ⟨F0, L0, hLF, hF⟩ := K5d.exists_algFrame (Vf H) (rational_of_le_one hr _)
  exact ⟨{
    c := c0, A := A0, Bm := B0, G := G0, C := C0, D := D0,
    Fm := (K5d.cmK K11.Kq F0).mulVecLin, Fl := (K5d.cmK K11.Kq L0).mulVecLin,
    BA := hBA, rangeA := hA, AG := hAG, DC := hDC, rangeC := hC,
    FlFm := fun σ => K5d.mulVec_left_invK hLF σ, rangeFm := hF,
    algA := hAa, algB := hBa, algG := hGa, algFm := algLin_cmK F0, algFl := algLin_cmK L0,
    algK := algLin_perK c0 H.t_ab (hPT _ H.t_ab), algN := algLin_perN c0 H.t_ab (hPT _ H.t_ab),
    algLift := algLin_lift c0 H.t_ab (hPT _ H.t_ab) }⟩

namespace Frame

variable {H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H)

/-- `κ_t`. -/
noncomputable abbrev K := perK F.c H.t_ab
/-- `fib(B^♮) ≅ ℂ^g`. -/
noncomputable abbrev N := perN F.c H.t_ab

/-- The curves of `G_H`. -/
abbrev LsH : Fin (fg H) → PeriodPair := Ls ∘ F.c.ι

/-- The push-out matrix of `G_H`: `M_H = Fl ∘ M ∘ N`. -/
noncomputable def MH : Matrix (Fin (ff H)) (Fin (fg H)) ℂ :=
  LinearMap.toMatrix' (F.Fl ∘ₗ M.mulVecLin ∘ₗ F.N)

lemma MH_mulVec (y : Fin (fg H) → ℂ) : F.MH.mulVec y = F.Fl (M.mulVec (F.N y)) := by
  rw [MH, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl

lemma algMat_MH (hM : AlgMat M) : AlgMat F.MH :=
  algMat_toMatrix' (F.algFl.comp ((algLin_mat hM).comp F.algN))

/-- The tangent map `T(G_H) → T(G)`. -/
noncomputable def Psi : TanV (fk0 H) (fk1 H) (fg H) (ff H) →ₗ[ℂ] TanV d0 d1 m r :=
  (F.A ∘ₗ LinearMap.fst ℂ _ _).prod
    (((K11.cm F.C).mulVecLin ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).prod
      ((F.c.lift ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).prod
        (F.G ∘ₗ LinearMap.fst ℂ _ _ +
          M.mulVecLin ∘ₗ F.K ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ +
          F.Fm ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _)))

lemma Psi_apply (x : TanV (fk0 H) (fk1 H) (fg H) (ff H)) :
    F.Psi x = (F.A x.1, (K11.cm F.C).mulVec x.2.1, F.c.lift x.2.2.1,
      F.G x.1 + M.mulVec (F.K x.2.2.1) + F.Fm x.2.2.2) := rfl

/-- Its left inverse `T(G) → T(G_H)`. -/
noncomputable def Phi : TanV d0 d1 m r →ₗ[ℂ] TanV (fk0 H) (fk1 H) (fg H) (ff H) :=
  (F.Bm ∘ₗ LinearMap.fst ℂ _ _).prod
    (((K11.cm F.D).mulVecLin ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).prod
      ((LSG.CM.proj F.c.ι ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).prod
        (F.Fl ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ -
          F.G ∘ₗ F.Bm ∘ₗ LinearMap.fst ℂ _ _ -
          M.mulVecLin ∘ₗ F.K ∘ₗ LSG.CM.proj F.c.ι ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ
            LinearMap.snd ℂ _ _))))

lemma Phi_apply (y : TanV d0 d1 m r) :
    F.Phi y = (F.Bm y.1, (K11.cm F.D).mulVec y.2.1, LSG.CM.proj F.c.ι y.2.2.1,
      F.Fl (y.2.2.2 - F.G (F.Bm y.1) - M.mulVec (F.K (LSG.CM.proj F.c.ι y.2.2.1)))) := rfl

lemma Phi_Psi (x : TanV (fk0 H) (fk1 H) (fg H) (ff H)) : F.Phi (F.Psi x) = x := by
  rw [Phi_apply, Psi_apply]
  simp only [F.BA, K11.mulVec_left_inv F.DC, F.c.proj_lift]
  have e : ∀ a b c : Fin r → ℂ, a + b + c - a - b = c := by intros; abel
  rw [e, F.FlFm]

lemma Psi_injective : Function.Injective F.Psi := fun x y h => by
  rw [← F.Phi_Psi x, ← F.Phi_Psi y, h]

lemma Fm_Fl {s : Fin r → ℂ} (hs : s ∈ Vf H) : F.Fm (F.Fl s) = s := by
  rw [← F.rangeFm] at hs
  obtain ⟨σ, rfl⟩ := hs
  rw [F.FlFm]

lemma N_mem_fibId (x : Fin (fg H) → ℂ) : F.N x ∈ fibId Ls H.t := by
  have := mem_perTanId_lift F.c H.t_ab 0 x
  simp only [map_zero, zero_add] at this
  exact this

lemma MN_mem_Vf (x : Fin (fg H) → ℂ) : M.mulVec (F.N x) ∈ Vf H :=
  Submodule.mem_sup_left ⟨_, F.N_mem_fibId x, rfl⟩

lemma Fm_MH (y : Fin (fg H) → ℂ) : F.Fm (F.MH.mulVec y) = M.mulVec (F.N y) := by
  rw [MH_mulVec, F.Fm_Fl (F.MN_mem_Vf y)]

lemma A_Bm {a : Fin d0 → ℂ} (ha : a ∈ H.gam.map (LinearMap.fst ℂ _ _)) : F.A (F.Bm a) = a := by
  rw [← F.rangeA] at ha
  obtain ⟨x, rfl⟩ := ha
  rw [F.BA]

lemma torusLie_eq_range : torusLie H.U = LinearMap.range (K11.cm F.C).mulVecLin := by
  rw [K5d.torusLie_eq_annC, K11.annC_eq_cspan, K11.cspan_eq_range F.rangeC]

/-- **`range Psi = T_{G'}`.** -/
theorem range_Psi : LinearMap.range F.Psi = H.tan := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Psi_apply]
    have hVf := F.rangeFm ▸ LinearMap.mem_range_self F.Fm x.2.2.2
    obtain ⟨u, ⟨w, hw, rfl⟩, γ, hγ, hsum⟩ := Submodule.mem_sup.mp hVf
    have e : ((F.A x.1, (K11.cm F.C).mulVec x.2.1, F.c.lift x.2.2.1,
        F.G x.1 + M.mulVec (F.K x.2.2.1) + F.Fm x.2.2.2) : TanV d0 d1 m r) =
        (vecIncl (F.A x.1, F.G x.1) + vecIncl (0, γ)) + torIncl ((K11.cm F.C).mulVec x.2.1) +
          (g2Incl (F.c.lift x.2.2.1, M.mulVec (F.K x.2.2.1)) + g2Incl (0, M.mulVec w)) := by
      rw [← hsum]
      simp only [vecIncl_apply, torIncl_apply, g2Incl_apply, Matrix.mulVecLin_apply]
      refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) ?_))
      simp only [Prod.snd_add, add_zero]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.add_mem _ ⟨_, F.AG x.1, rfl⟩ ⟨_, hγ, rfl⟩))) (Submodule.mem_sup_left
        (Submodule.mem_sup_right ⟨_, ?_, rfl⟩))) (Submodule.mem_sup_right (Submodule.add_mem _
          ⟨_, ⟨_, mem_perTanId_lift F.c H.t_ab x.2.2.1 0, rfl⟩, ?_⟩ ⟨_, ⟨_, hw, rfl⟩, rfl⟩))
    · rw [F.torusLie_eq_range]; exact ⟨_, rfl⟩
    · simp
  · refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨γ, hγ, rfl⟩
      have h0 : γ.1 ∈ H.gam.map (LinearMap.fst ℂ _ _) := ⟨γ, hγ, rfl⟩
      set a := F.Bm γ.1
      have hfib : γ.2 - F.G a ∈ Vf H := by
        refine Submodule.mem_sup_right ?_
        change ((0 : Fin d0 → ℂ), γ.2 - F.G a) ∈ H.gam
        have : ((0 : Fin d0 → ℂ), γ.2 - F.G a) = γ - (F.A a, F.G a) := by
          refine Prod.ext ?_ rfl
          simp only [Prod.fst_sub, a, F.A_Bm h0, sub_self]
        rw [this]; exact Submodule.sub_mem _ hγ (F.AG a)
      refine ⟨(a, 0, 0, F.Fl (γ.2 - F.G a)), ?_⟩
      rw [Psi_apply, F.Fm_Fl hfib, vecIncl_apply]
      refine Prod.ext (F.A_Bm h0) (Prod.ext (by simp) (Prod.ext (by simp) ?_))
      simp
    · rintro _ ⟨v, hv, rfl⟩
      rw [F.torusLie_eq_range] at hv
      obtain ⟨b, rfl⟩ := hv
      exact ⟨(0, b, 0, 0), by rw [Psi_apply]; simp⟩
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hp
      have he := perTanId_eq F.c H.t_ab hq
      set μ := LSG.CM.proj F.c.ι q.1
      set y := LSG.CM.proj F.c.ι q.2
      refine ⟨(0, 0, μ, F.Fl (M.mulVec (F.N y))), ?_⟩
      rw [Psi_apply, F.Fm_Fl (F.MN_mem_Vf y), g2Incl_apply]
      conv_rhs => rw [he]
      refine Prod.ext (by simp) (Prod.ext (by simp) (Prod.ext (by simp) ?_))
      simp [Matrix.mulVec_add]

lemma Psi_mem_tan (x : TanV (fk0 H) (fk1 H) (fg H) (ff H)) : F.Psi x ∈ H.tan := by
  rw [← F.range_Psi]; exact ⟨x, rfl⟩

lemma Psi_Phi {y : TanV d0 d1 m r} (hy : y ∈ H.tan) : F.Psi (F.Phi y) = y := by
  rw [← F.range_Psi] at hy
  obtain ⟨x, rfl⟩ := hy
  rw [F.Phi_Psi]

lemma tan_eq_map : H.tan = (⊤ : Submodule ℂ (TanV (fk0 H) (fk1 H) (fg H) (ff H))).map F.Psi := by
  rw [Submodule.map_top, F.range_Psi]

include F in
/-- **`dim T_{G'} = k₀ + k₁ + g + f`.** -/
theorem finrank_tan : finrank ℂ H.tan = fk0 H + fk1 H + fg H + ff H := by
  rw [← F.range_Psi, LinearMap.finrank_range_of_inj F.Psi_injective]
  simp [Module.finrank_prod, add_assoc]

lemma algVecV_Psi (hM : AlgMat M) {x : TanV (fk0 H) (fk1 H) (fg H) (ff H)} (hx : AlgVecV x) :
    AlgVecV (F.Psi x) := by
  rw [Psi_apply]
  exact ⟨F.algA _ hx.1, K5d.algVec_cm_mulVec F.C hx.2.1, F.algLift _ hx.2.2.1,
    algVec_add (algVec_add (F.algG _ hx.1) (algLin_mat hM _ (F.algK _ hx.2.2.1)))
      (F.algFm _ hx.2.2.2)⟩

lemma algVecV_Phi (hM : AlgMat M) {y : TanV d0 d1 m r} (hy : AlgVecV y) : AlgVecV (F.Phi y) := by
  rw [Phi_apply]
  exact ⟨F.algB _ hy.1, K5d.algVec_cm_mulVec F.D hy.2.1, algLin_proj _ _ hy.2.2.1,
    F.algFl _ (algVec_sub (algVec_sub hy.2.2.2 (F.algG _ (F.algB _ hy.1)))
      (algLin_mat hM _ (F.algK _ (algLin_proj _ _ hy.2.2.1))))⟩

/-- `T_{G'} = ker (id − Psi ∘ Phi)`, an algebraic endomorphism. -/
lemma tan_eq_ker : H.tan = LinearMap.ker (LinearMap.id - F.Psi ∘ₗ F.Phi) := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, sub_eq_zero]
  constructor
  · intro hy; exact (F.Psi_Phi hy).symm
  · intro hy; rw [hy]; exact F.Psi_mem_tan _

include F in
/-- **`W ⊓ T_{G'}` is rational** for rational `W`. -/
lemma ratV_inf_tan (hM : AlgMat M) {W : Submodule ℂ (TanV d0 d1 m r)} (hW : RatSubV W) :
    RatSubV (W ⊓ H.tan) := by
  rw [F.tan_eq_ker]
  refine ratV_inf_ker_endo hW fun v hv => ?_
  have h1 := F.algVecV_Psi hM (F.algVecV_Phi hM hv)
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  exact ⟨algVec_sub hv.1 h1.1, algVec_sub hv.2.1 h1.2.1, algVec_sub hv.2.2.1 h1.2.2.1,
    algVec_sub hv.2.2.2 h1.2.2.2⟩

end Frame

end LSG.W88.V5d
