/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupRat
import LSG.ME.ProductGraph

/-!
# Classification of the Lie algebra of a closed subgroup of `G̃` (M2.5 β′; template `LSG.MEV.SubgroupClass`)

`H ⊆ G̃` Zariski closed, `T′ = lieAlg H ⊆ Tan = ℂ^{d₀} × ℂ^{d₁} × ∏ ℂ^{g_k} × ℂ^m`.

* The linear subgroup: `inLin : G_a^{d₀+m} × G_m^{d₁} → G̃`, `((a, w), y) ↦ (a, y, (0, w_k) mod perV_k)`;
  `HL H = inLin⁻¹(H)` is Zariski closed in StrongSix's sense (substitute the affine lift `lift (0, w)`), hence
  `V × T_Λ` (**`HL_eq_prodSet`**, StrongSix's `classify`).
* **`mem_lieAlg_lin_iff`**: `(a, b, 0, w) ∈ T′ ↔ (a, w) ∈ V ∧ b ⊥ Λ`; **`lin_mem_lieAlg_of_Htil`**.
* **`eq_zero_of_lattice`** (with `isRatSub_map_piB`), torus splitting **`torus_mem`**.
* **`perTanId ⊆ T′`** (`per_mem_lieAlg`, `perTanId_map_le`), `exists_perTanId`.
* **`lieAlg_eq_tanV`**: `T′ = tanOfV (gamOf H) (UOf H) (tOf H)` with `gamOf = T′ ∩ (vector group)`,
  `UOf = qspan Λ`, `tOf = π_base(T′)`; **`isRatSub_tOf`**.
-/

open MvPolynomial Set Module
open LSG.W88 (torusLie)

namespace LSG.MEBV

open LSG.MEB (IsRatSub perAb)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### The linear subgroup `G_a^{d₀} × G_m^{d₁} × (fibres over 0)` -/

/-- The points of the linear group `G_a^{d₀+m} × G_m^{d₁}` (StrongSix). -/
abbrev LPt (d₀ d₁ m : ℕ) := StrongSix.Thm1.GPt ℂ (d₀ + m) d₁

variable (B) in
/-- `((a, w), y) ↦ (a, y, (0, w_k))`. -/
def inLin (g : LPt d₀ d₁ m) : GPt d₀ d₁ B :=
  (fun i => g.1 (Fin.castAdd m i), Additive.ofMul g.2,
    fun k => (QuotientAddGroup.mk ((0 : Fin (B k).g → ℂ), g.1 (Fin.natAdd d₀ k)) : (B k).Pt))

theorem inLin_zero : inLin B (StrongSix.Thm1.GPt.zero : LPt d₀ d₁ m) = 0 :=
  Prod.ext rfl (Prod.ext rfl (funext fun _ => by
    simp only [StrongSix.Thm1.GPt.zero, Pi.zero_apply]; rfl))

theorem inLin_gmul (g h : LPt d₀ d₁ m) :
    inLin B (StrongSix.M2.gmul g h) = inLin B g + inLin B h := by
  refine Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))
  change (QuotientAddGroup.mk (0, (g.1 + h.1) (Fin.natAdd d₀ k)) : (B k).Pt) =
    QuotientAddGroup.mk (0, g.1 (Fin.natAdd d₀ k)) + QuotientAddGroup.mk (0, h.1 (Fin.natAdd d₀ k))
  rw [← QuotientAddGroup.mk_add, Prod.mk_add_mk, add_zero]; rfl

theorem inLin_ginv (g : LPt d₀ d₁ m) : inLin B (StrongSix.M2.ginv g) = -inLin B g := by
  refine Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))
  change (QuotientAddGroup.mk (0, (-g.1) (Fin.natAdd d₀ k)) : (B k).Pt) =
    -QuotientAddGroup.mk (0, g.1 (Fin.natAdd d₀ k))
  rw [← QuotientAddGroup.mk_neg, Prod.neg_mk, neg_zero]; rfl

variable (B) in
/-- `HL H = inLin⁻¹(H)`. -/
def HL (H : Set (GPt d₀ d₁ B)) : Set (LPt d₀ d₁ m) := {g | inLin B g ∈ H}

variable {H : Set (GPt d₀ d₁ B)}

theorem HL_isSubgroup (hH : IsSubgroupG H) : StrongSix.M2.IsSubgroupG (HL B H) where
  one_mem := by show inLin B _ ∈ H; rw [inLin_zero]; exact hH.zero_mem
  mul_mem g hg h hh := by
    show inLin B _ ∈ H; rw [inLin_gmul]; exact hH.add_mem _ hg _ hh
  inv_mem g hg := by show inLin B _ ∈ H; rw [inLin_ginv]; exact hH.neg_mem _ hg

variable (B) in
/-- Substituting the affine lift `lift (0, w_k)` into the blocks. -/
noncomputable def substV : Var d₀ d₁ B → MvPolynomial (StrongSix.M2.V3 (d₀ + m) d₁) ℂ
  | .x i => X (.inl (Fin.castAdd m i))
  | .y j => X (.inr (.inl j))
  | .z j => X (.inr (.inr j))
  | .e k (Sum.inl c) => C ((B k).base.θ 0 c)
  | .e k (Sum.inr t) => C ((B k).base.θ 0 ((B k).fc t)) * X (.inl (Fin.natAdd d₀ k)) - C ((B k).Φ 0 t)

/-- The substituted point is a cone representative of `inLin g`. -/
theorem exists_substV_eq (g : LPt d₀ d₁ m) : ∃ lam : Fin m → ℂˣ,
    (fun v => eval (StrongSix.M2.pt g) (substV B v)) = coords (inLin B g) lam := by
  choose c hc h using fun k => (B k).rep_mk ((0 : Fin (B k).g → ℂ), g.1 (Fin.natAdd d₀ k))
  refine ⟨fun k => (Units.mk0 (c k) (hc k))⁻¹, funext fun v => ?_⟩
  cases v with
  | x i => simp [substV, coords, inLin, StrongSix.M2.pt]
  | y j => simp [substV, coords, inLin, StrongSix.M2.pt, GPt.ym]
  | z j => simp [substV, coords, inLin, StrongSix.M2.pt, GPt.ym]
  | e k a =>
    simp only [coords, inLin]
    rw [h k]
    cases a with
    | inl c' => simp [substV, hc k]
    | inr t => simp [substV, hc k, StrongSix.M2.pt]

theorem HL_eq_zeros (hc : IsZClosed H) :
    HL B H = StrongSix.M2.zeros {Q | ∃ P ∈ homogVanish H, Q = bind₁ (substV B) P} := by
  ext g
  constructor
  · rintro hg _ ⟨P, hP, rfl⟩
    obtain ⟨lam, hlam⟩ := exists_substV_eq (B := B) g
    rw [LSG.MEB.eval_bind₁', hlam]
    exact mem_vanish.mp hP.1 _ hg lam
  · intro h
    change inLin B g ∈ H
    rw [← zeros_homogVanish hc]
    intro P hP lam
    obtain ⟨lam', hlam⟩ := exists_substV_eq (B := B) g
    obtain ⟨d, hd⟩ := hP.2
    refine (eval_coords_eq_zero_iff hd _ lam' lam).mp ?_
    rw [← hlam, ← LSG.MEB.eval_bind₁']
    exact h _ ⟨P, hP, rfl⟩

/-- **`HL H = V × T_Λ`** (Roy's classification of algebraic subgroups of linear groups). -/
theorem HL_eq_prodSet (hH : IsSubgroupG H) (hc : IsZClosed H) :
    HL B H = StrongSix.M2.prodSet (StrongSix.M2.linV (HL B H)) (StrongSix.M2.latt (HL B H)) :=
  StrongSix.M2.classify (HL_isSubgroup hH) (HL_eq_zeros hc)

/-! ### `exp` at base-lattice points -/

/-- The linear point `((a, w), e^b)`. -/
noncomputable def linPtV (a : Fin d₀ → ℂ) (w : Fin m → ℂ) (b : Fin d₁ → ℂ) : LPt d₀ d₁ m :=
  (Fin.append a w, fun j => expU (b j))

theorem chr_linPtV (a : Fin d₀ → ℂ) (w : Fin m → ℂ) (b : Fin d₁ → ℂ) (φ : Fin d₁ → ℤ) :
    StrongSix.M2.chr (linPtV a w b).2 φ = Complex.exp (∑ j, (φ j : ℂ) * b j) := by
  simp only [StrongSix.M2.chr, linPtV, expU, Units.val_mk0, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => (Complex.exp_int_mul _ _).symm

/-- `η` on a base vector, blockwise. -/
noncomputable def etaB (B : Fin m → VBlock) (z : ∀ k, Fin (B k).g → ℂ) : Fin m → ℂ := fun k => (B k).η (z k)

/-- **`exp` at a base-lattice point**: `expG (a, b, z, w) = inLin ((a, w − η(z)), e^b)`. -/
theorem expG_of_lattice {p : Tan d₀ d₁ B} (hz : ∀ k, p.2.2.1 k ∈ (B k).base.per) :
    expG d₀ d₁ B p = inLin B (linPtV p.1 (p.2.2.2 - etaB B p.2.2.1) p.2.1) := by
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (funext fun k => ?_))
  · simp [inLin, linPtV, expG_apply, expGf]
  · change (QuotientAddGroup.mk (p.blkV k) : (B k).Pt) = QuotientAddGroup.mk (0, _)
    rw [QuotientAddGroup.eq]
    refine ⟨by simpa [Tan.blkV] using (B k).base.per.neg_mem (hz k), ?_⟩
    simp only [Tan.blkV, linPtV, Fin.append_right, Prod.snd_add, Prod.snd_neg, Prod.fst_add, Prod.fst_neg,
      add_zero, Pi.sub_apply, etaB]
    rw [(B k).η_neg (hz k)]; ring

theorem expG_lin (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) (w : Fin m → ℂ) :
    expG d₀ d₁ B ((a, b, 0, w) : Tan d₀ d₁ B) = inLin B (linPtV a w b) := by
  rw [expG_of_lattice (fun k => (B k).base.per.zero_mem)]
  congr 2
  funext k
  simp [etaB, (B k).η_zero]

theorem fin_append_smul (c : ℂ) (a : Fin d₀ → ℂ) (w : Fin m → ℂ) :
    Fin.append (c • a) (c • w) = c • Fin.append a w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;> simp

/-! ### The linear part of `T′` -/

section Lin

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **`(a, b, 0, w) ∈ T′ ↔ (a, w) ∈ V ∧ b ⊥ Λ`** (`HL = V × T_Λ`). -/
theorem mem_lieAlg_lin_iff {a : Fin d₀ → ℂ} {b : Fin d₁ → ℂ} {w : Fin m → ℂ} :
    ((a, b, 0, w) : Tan d₀ d₁ B) ∈ lieAlg hH ↔
      Fin.append a w ∈ StrongSix.M2.linV (HL B H) ∧
        ∀ φ ∈ StrongSix.M2.latt (HL B H), ∑ j, (φ j : ℂ) * b j = 0 := by
  have hsm : ∀ c : ℂ, c • ((a, b, 0, w) : Tan d₀ d₁ B) = (c • a, c • b, 0, c • w) := fun c => by
    simp
  have hmem : ∀ c : ℂ, (expG d₀ d₁ B (c • ((a, b, 0, w) : Tan d₀ d₁ B)) ∈ H ↔
      linPtV (c • a) (c • w) (c • b) ∈ StrongSix.M2.prodSet (StrongSix.M2.linV (HL B H))
        (StrongSix.M2.latt (HL B H))) := fun c => by
    rw [hsm, expG_lin, ← HL_eq_prodSet hH hc]; rfl
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
      rwa [chr_linPtV, hsum] at this
  · rintro ⟨h1, h2⟩ c
    rw [mem_Htil, hmem]
    refine ⟨?_, fun φ hφ => ?_⟩
    · show Fin.append (c • a) (c • w) ∈ _
      rw [fin_append_smul]; exact Submodule.smul_mem _ c h1
    · rw [chr_linPtV, hsum, h2 φ hφ, mul_zero, Complex.exp_zero]

/-- **The vector part**: every vector `(a, 0, 0, w)` of `H̃` lies in `T′`. -/
theorem lin_mem_lieAlg_of_Htil {a : Fin d₀ → ℂ} {w : Fin m → ℂ}
    (h : ((a, 0, 0, w) : Tan d₀ d₁ B) ∈ Htil hH) : ((a, 0, 0, w) : Tan d₀ d₁ B) ∈ lieAlg hH := by
  rw [mem_lieAlg_lin_iff hH hc]
  refine ⟨?_, fun φ _ => by simp⟩
  have hL : linPtV a w 0 ∈ HL B H := by
    show inLin B _ ∈ H; rw [← expG_lin]; exact h
  exact (StrongSix.M2.subset_prodSet _ hL).1

/-- The torus directions `U^⊥` lie in `T′`. -/
theorem torIncl_mem {b : Fin d₁ → ℂ}
    (hb : b ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL B H)))) :
    (torIncl b : Tan d₀ d₁ B) ∈ lieAlg hH := by
  change ((0, b, 0, 0) : Tan d₀ d₁ B) ∈ lieAlg hH
  rw [mem_lieAlg_lin_iff hH hc, LSG.ME.mem_torusLie_qspan.symm]
  refine ⟨?_, hb⟩
  have : Fin.append (0 : Fin d₀ → ℂ) (0 : Fin m → ℂ) = 0 := by
    funext i; refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;> simp
  rw [this]; exact Submodule.zero_mem _

end Lin

/-! ### The real-span argument -/

/-- **A linear form with imaginary periods on `T` vanishes**, when `π_base(T)` is rational. -/
theorem eq_zero_of_lattice {T : Submodule ℂ (Tan d₀ d₁ B)}
    (hP : IsRatSub (perBase B) (T.map piB)) (f : Tan d₀ d₁ B →ₗ[ℂ] ℂ)
    (h0 : ∀ u ∈ T, u.2.2.1 = 0 → f u = 0)
    (hΛ : ∀ u ∈ T, (∀ k, u.2.2.1 k ∈ (B k).base.per) → (f u).re = 0)
    {u : Tan d₀ d₁ B} (hu : u ∈ T) : f u = 0 := by
  set L0 := {z : ∀ k, Fin (B k).g → ℂ | z ∈ T.map piB ∧ z ∈ perBase B}
  have hpre : ∀ z ∈ Submodule.span ℝ L0, ∃ v ∈ T, v.2.2.1 = z := by
    intro z hz
    have hz' : z ∈ T.map piB := by
      rw [IsRatSub] at hP
      rw [← hP] at hz
      exact hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz'
    exact ⟨v, hv, rfl⟩
  have hspan : ∀ v ∈ T, v.2.2.1 ∈ Submodule.span ℝ L0 := by
    intro v hv
    rw [IsRatSub] at hP
    rw [← hP]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hre : ∀ z (hz : z ∈ Submodule.span ℝ L0), ∀ v ∈ T, v.2.2.1 = z → (f v).re = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => rintro v hv rfl; exact hΛ v hv fun k => hx.2 k (Set.mem_univ k)
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
def phiV (φ : Fin d₁ → ℤ) : Tan d₀ d₁ B →ₗ[ℂ] ℂ where
  toFun u := ∑ j, (φ j : ℂ) * u.2.1 j
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_left_comm]

theorem phiV_apply (φ : Fin d₁ → ℤ) (u : Tan d₀ d₁ B) : phiV φ u = ∑ j, (φ j : ℂ) * u.2.1 j :=
  rfl

section Split

variable (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **`π_B(T′) ⊆ U^⊥`.** -/
theorem torus_mem {v : Tan d₀ d₁ B} (hv : v ∈ lieAlg hH) :
    v.2.1 ∈ torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL B H))) := by
  rw [LSG.ME.mem_torusLie_qspan]
  intro φ hφ
  refine eq_zero_of_lattice (isRatSub_map_piB hH hc) (phiV φ) (fun u hu h => ?_)
    (fun u hu hl => ?_) hv
  · have hu' : u = ((u.1, u.2.1, 0, u.2.2.2) : Tan d₀ d₁ B) := by
      ext <;> simp [h]
    rw [hu'] at hu
    exact ((mem_lieAlg_lin_iff hH hc).mp hu).2 φ hφ
  · have hm : expG d₀ d₁ B u ∈ H := lieAlg_le_Htil hH hu
    rw [expG_of_lattice hl] at hm
    have := (StrongSix.M2.subset_prodSet _ (show _ ∈ HL B H from hm)).2 φ hφ
    rw [chr_linPtV] at this
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp this
    rw [phiV_apply, hn]
    simp

theorem sub_torIncl_mem {v : Tan d₀ d₁ B} (hv : v ∈ lieAlg hH) :
    v - torIncl v.2.1 ∈ lieAlg hH :=
  (lieAlg hH).sub_mem hv (torIncl_mem hH hc (torus_mem hH hc hv))

/-! ### `perTanId(t) ⊆ T′` -/

/-- **The periods over `t` lie in `T′`**: for `λ ∈ t ∩ Λ`, `(0, 0, λ, η(λ)) ∈ T′`. -/
theorem per_mem_lieAlg {l : ∀ k, Fin (B k).g → ℂ} (hl : l ∈ (lieAlg hH).map piB)
    (hΛ : ∀ k, l k ∈ (B k).base.per) :
    ((0, 0, l, etaB B l) : Tan d₀ d₁ B) ∈ lieAlg hH := by
  obtain ⟨v, hv, hvl⟩ := Submodule.mem_map.mp hl
  rw [piB_apply] at hvl
  set v' := v - torIncl v.2.1 with hv'
  have hv'T := sub_torIncl_mem hH hc hv
  have hper : ((0, 0, l, etaB B l) : Tan d₀ d₁ B) ∈ PerG d₀ d₁ B :=
    ⟨rfl, fun _ => ⟨0, by simp⟩, fun k => ⟨hΛ k, rfl⟩⟩
  have hd : ((v.1, 0, 0, v.2.2.2 - etaB B l) : Tan d₀ d₁ B) ∈ lieAlg hH := by
    refine lin_mem_lieAlg_of_Htil hH hc ?_
    have : ((v.1, 0, 0, v.2.2.2 - etaB B l) : Tan d₀ d₁ B) =
        v' - ((0, 0, l, etaB B l) : Tan d₀ d₁ B) := by
      ext <;> simp [hv', hvl, torIncl]
    rw [this]
    exact (Htil hH).sub_mem (lieAlg_le_Htil hH hv'T) (PerG_le_Htil hH hper)
  have : ((0, 0, l, etaB B l) : Tan d₀ d₁ B) =
      v' - ((v.1, 0, 0, v.2.2.2 - etaB B l) : Tan d₀ d₁ B) := by
    ext <;> simp [hv', hvl, torIncl]
  rw [this]
  exact (lieAlg hH).sub_mem hv'T hd

/-- **`g2Incl (perTanId t) ⊆ T′`.** -/
theorem perTanId_map_le : (perTanId B ((lieAlg hH).map piB)).map g2Incl ≤ lieAlg hH := by
  rw [Submodule.map_le_iff_le_comap, perTanId, Submodule.span_le]
  rintro ⟨l, s⟩ ⟨hl, hΛ⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  have hs : s = etaB B l := funext fun k => (hΛ k).2
  have := per_mem_lieAlg hH hc hl fun k => (hΛ k).1
  rw [hs]
  exact this

end Split

/-! ### The decomposition -/

/-- Over a rational `t`, every `z ∈ t` has a lift `(z, w) ∈ perTanId t`. -/
theorem exists_perTanId {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} (ht : IsRatSub (perBase B) t)
    {z : ∀ k, Fin (B k).g → ℂ} (hz : z ∈ t) : ∃ w, (z, w) ∈ perTanId B t := by
  have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (∀ k, Fin (B k).g → ℂ)) := hz
  rw [ht] at hz'
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx =>
    exact ⟨etaB B x, Submodule.subset_span ⟨hx.1, fun k => ⟨hx.2 k (Set.mem_univ k), rfl⟩⟩⟩
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

/-- The vector part `Γ = T′ ∩ (G_a^{d₀} × fibres)`. -/
noncomputable def gamOf (hH : IsSubgroupG H) : Submodule ℂ ((Fin d₀ → ℂ) × (Fin m → ℂ)) := (lieAlg hH).comap vecIncl

/-- The toric data `U = qspan Λ`. -/
noncomputable def UOf (_hH : IsSubgroupG H) : Submodule ℚ (Fin d₁ → ℚ) :=
  StrongSix.M2.qspan (StrongSix.M2.latt (HL B H))

/-- The base part `t = π_base(T′)`. -/
noncomputable def tOf (hH : IsSubgroupG H) : Submodule ℂ (∀ k, Fin (B k).g → ℂ) := (lieAlg hH).map piB

theorem isRatSub_tOf (hH : IsSubgroupG H) (hc : IsZClosed H) : IsRatSub (perBase B) (tOf hH) :=
  isRatSub_map_piB hH hc

/-- **The classification**: `T′ = vecIncl Γ ⊔ torIncl U^⊥ ⊔ g2Incl (perTanId t)`. -/
theorem lieAlg_eq_tanV (hH : IsSubgroupG H) (hc : IsZClosed H) :
    lieAlg hH = tanOfV d₀ d₁ B (gamOf hH) (UOf hH) (tOf hH) := by
  set T := lieAlg hH
  have hab := isRatSub_map_piB hH hc
  refine le_antisymm (fun v hv => ?_) (sup_le (sup_le (Submodule.map_comap_le _ _) ?_)
    (perTanId_map_le hH hc))
  · have hz : v.2.2.1 ∈ T.map piB := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    obtain ⟨w, hw⟩ := exists_perTanId hab hz
    have hg : (g2Incl (v.2.2.1, w) : Tan d₀ d₁ B) ∈ T :=
      perTanId_map_le hH hc (Submodule.mem_map.mpr ⟨(v.2.2.1, w), hw, rfl⟩)
    have hvec : (vecIncl (v.1, v.2.2.2 - w) : Tan d₀ d₁ B) ∈ T := by
      have : (vecIncl (v.1, v.2.2.2 - w) : Tan d₀ d₁ B) =
          (v - torIncl v.2.1) - g2Incl (v.2.2.1, w) := by
        ext <;> simp [vecIncl, torIncl, g2Incl]
      rw [this]
      exact T.sub_mem (sub_torIncl_mem hH hc hv) hg
    have hsplit : v = vecIncl (v.1, v.2.2.2 - w) + torIncl v.2.1 + g2Incl (v.2.2.1, w) := by
      ext <;> simp [vecIncl, torIncl, g2Incl]
    rw [hsplit]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ?_) ?_
    · exact Submodule.mem_map.mpr ⟨_, hvec, rfl⟩
    · exact Submodule.mem_map.mpr ⟨_, torus_mem hH hc hv, rfl⟩
    · exact Submodule.mem_map.mpr ⟨(v.2.2.1, w), hw, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact torIncl_mem hH hc hb

end LSG.MEBV
