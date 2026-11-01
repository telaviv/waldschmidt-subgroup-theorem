/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dOnto
import LSG.W88.V5dMain

/-!
# The frame groups with `f = 1`, `M_H = 0`: Theorem 4.1 via the `r = 0` presentation

In the §5d engine (`V5dMain.lean`) Theorem 4.1 is applied to the class-`𝒞` group `G_H` of a frame of
the maximiser, with push-out matrix `M_H : ℂ^g → ℂ^f`, `f ≤ 1`. `M_H` is onto unless `f = 1` and
`M_H = 0`; then `G_H = G_a^{k₀} × G_m^{k₁} × E^g × G_a`, whose other class-`𝒞` presentation is
`G_a^{k₀+1} × G_m^{k₁} × E^g` (`r = 0`, the fibre counted as an extra `G_a`). This file:

* `swE : TanV k₀ k₁ g 1 ≃ TanV (k₀+1) k₁ g 0`, `(a, b, z, s) ↦ (a ++ s, b, z, ·)`; periods,
  logarithms and members correspond (`perV_sw`, `lamV_sw`, `subSw`, `map_tan_subSw`);
* **`concl41_sw`**: for `codim V = 1`, `Concl41` for the `r = 0` presentation gives `Concl41`
  for the `r = 1, M = 0` one. Bookkeeping: `δ`, `δ₁`, `τ`, `λ`, `κ` are unchanged, `δ₂` grows by
  at most `1` (`δ₀` drops by at most `1`), and `d₁ + 2d₂ − κ` grows by exactly `2`; with `q = 1`
  and `δ − τ ≥ 1` the extra `2` on the left is paid by `2(δ − τ)` on the right;
* `concl41_swOnto` (from `Theorem41VecLAOnto` at `r = 0`, under the `r = 0` (NR)
  `k₁ + 2(k₀ + 1) + κ ≤ 2 dim V`) and `concl41_swLin` (`g = 0`, Roy, no (NR));
* `corner_falseV'`: `corner_falseV` with `f = 0` weakened to `M_H = 0` (periods in `T_{G'}` then
  have no fibre component, `omV_snd_eq_zero`).
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

/-! ### `ℂ^{k₀} × ℂ^1 ≅ ℂ^{k₀+1}` -/

section Append

variable {k0 : ℕ}

lemma append_add' (a a' : Fin k0 → ℂ) (s s' : Fin 1 → ℂ) :
    Fin.append (a + a') (s + s') = Fin.append a s + Fin.append a' s' := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma append_smul' (c : ℂ) (a : Fin k0 → ℂ) (s : Fin 1 → ℂ) :
    Fin.append (c • a) (c • s) = c • Fin.append a s := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma append_zero' : Fin.append (0 : Fin k0 → ℂ) (0 : Fin 1 → ℂ) = 0 := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

lemma append_eq_zero' {a : Fin k0 → ℂ} {s : Fin 1 → ℂ} : Fin.append a s = 0 ↔ a = 0 ∧ s = 0 := by
  constructor
  · intro h
    exact ⟨funext fun j => by simpa using congrFun h (Fin.castAdd 1 j),
      funext fun j => by simpa using congrFun h (Fin.natAdd k0 j)⟩
  · rintro ⟨rfl, rfl⟩; exact append_zero'

lemma algVec_append' {a : Fin k0 → ℂ} {s : Fin 1 → ℂ} :
    AlgVec (Fin.append a s) ↔ AlgVec a ∧ AlgVec s := by
  constructor
  · intro h
    exact ⟨fun j => by simpa using h (Fin.castAdd 1 j), fun j => by simpa using h (Fin.natAdd k0 j)⟩
  · rintro ⟨ha, hs⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using ha j
    · simpa using hs j

end Append

variable {k0 k1 g : ℕ}

/-- `(a, b, z, s) ↦ (a ++ s, b, z, ·)`. -/
noncomputable def swE : TanV k0 k1 g 1 ≃ₗ[ℂ] TanV (k0 + 1) k1 g 0 where
  toFun p := (Fin.append p.1 p.2.2.2, p.2.1, p.2.2.1, 0)
  invFun x := (fun i => x.1 (Fin.castAdd 1 i), x.2.1, x.2.2.1, fun i => x.1 (Fin.natAdd k0 i))
  map_add' _ _ := Prod.ext (append_add' _ _ _ _) (Prod.ext rfl (Prod.ext rfl fin0_eq))
  map_smul' _ _ := Prod.ext (append_smul' _ _ _) (Prod.ext rfl (Prod.ext rfl fin0_eq))
  left_inv _ := Prod.ext (funext fun _ => Fin.append_left _ _ _)
    (Prod.ext rfl (Prod.ext rfl (funext fun _ => Fin.append_right _ _ _)))
  right_inv _ := Prod.ext Fin.append_castAdd_natAdd (Prod.ext rfl (Prod.ext rfl fin0_eq))

lemma swE_apply (p : TanV k0 k1 g 1) :
    swE p = (Fin.append p.1 p.2.2.2, p.2.1, p.2.2.1, (0 : Fin 0 → ℂ)) := rfl

/-- `(x, ·) ↦ (x_{<k₀}, x_{k₀})` on the vector parts. -/
def gsw : ((Fin (k0 + 1) → ℂ) × (Fin 0 → ℂ)) →ₗ[ℂ] ((Fin k0 → ℂ) × (Fin 1 → ℂ)) where
  toFun w := (fun i => w.1 (Fin.castAdd 1 i), fun i => w.1 (Fin.natAdd k0 i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma ratPair_map_of {a b a' b' : ℕ} {Γ : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hΓ : RatPair Γ)
    (f : ((Fin a → ℂ) × (Fin b → ℂ)) →ₗ[ℂ] ((Fin a' → ℂ) × (Fin b' → ℂ)))
    (hf : ∀ w, AlgPair w → AlgPair (f w)) : RatPair (Γ.map f) := by
  apply le_antisymm
  · conv_lhs => rw [hΓ]
    rw [Submodule.map_span]
    exact Submodule.span_mono (by rintro _ ⟨w, hw, rfl⟩; exact ⟨⟨w, hw.1, rfl⟩, hf w hw.2⟩)
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- `dim pr₀ Γ` does not grow under `gsw`. -/
lemma finrank_fst_gsw (Γ : Submodule ℂ ((Fin (k0 + 1) → ℂ) × (Fin 0 → ℂ))) :
    finrank ℂ ((Γ.map gsw).map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 1 → ℂ))) ≤
      finrank ℂ (Γ.map (LinearMap.fst ℂ _ _)) := by
  have e : (Γ.map gsw).map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 1 → ℂ)) =
      (Γ.map (LinearMap.fst ℂ _ _)).map (LinearMap.funLeft ℂ ℂ (Fin.castAdd 1)) := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]; rfl
  rw [e]; exact Submodule.finrank_map_le _ _

section Sw

variable (Ls : Fin g → PeriodPair) (M1 : Matrix (Fin 1) (Fin g) ℂ)

/-- The member of the `r = 1` presentation attached to a member of the `r = 0` presentation. -/
noncomputable def subSw
    (H0 : SubgroupDataV (d0 := k0 + 1) (d1 := k1) Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) :
    SubgroupDataV (d0 := k0) (d1 := k1) Ls M1 where
  U := H0.U
  t := H0.t
  gam := H0.gam.map gsw
  gam_rat := ratPair_map_of H0.gam_rat gsw fun _ hw => ⟨fun _ => hw.1 _, fun _ => hw.1 _⟩
  t_ab := H0.t_ab

variable {Ls M1}

lemma map_tan_subSw (hM1 : ∀ y, M1.mulVec y = 0)
    (H0 : SubgroupDataV (d0 := k0 + 1) (d1 := k1) Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) :
    (subSw Ls M1 H0).tan.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap = H0.tan := by
  have e1 : ((H0.gam.map gsw).map (vecIncl (d1 := k1) (m := g))).map
      (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap = H0.gam.map vecIncl := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun w => Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl fin0_eq))
    exact Fin.append_castAdd_natAdd
  have e2 : ((torusLie H0.U).map (torIncl (d0 := k0) (m := g) (r := 1))).map
      (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap = (torusLie H0.U).map torIncl := by
    rw [← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun w => Prod.ext append_zero' (Prod.ext rfl (Prod.ext rfl fin0_eq))
  have e3 : ((perTan Ls M1 H0.t).map (g2Incl (d0 := k0) (d1 := k1))).map
      (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap =
      (perTan Ls (0 : Matrix (Fin 0) (Fin g) ℂ) H0.t).map g2Incl := by
    simp only [perTan]
    rw [← Submodule.map_comp, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun p => Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl fin0_eq))
    change Fin.append (0 : Fin k0 → ℂ) (M1.mulVec p.2) = 0
    rw [hM1]; exact append_zero'
  change ((H0.gam.map gsw).map vecIncl ⊔ (torusLie H0.U).map torIncl ⊔
    (perTan Ls M1 H0.t).map g2Incl).map _ = _
  rw [Submodule.map_sup, Submodule.map_sup, e1, e2, e3]; rfl

variable (Ls M1) in
lemma perV_sw (hM1 : ∀ y, M1.mulVec y = 0) :
    (PerV (d0 := k0 + 1) (d1 := k1) Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) =
      (PerV (d0 := k0) (d1 := k1) Ls M1).map
        (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap.toAddMonoidHom := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨swE.symm x, ⟨?_, h2, h3, ?_⟩, swE.apply_symm_apply x⟩
    · funext i; exact congrFun h1 (Fin.castAdd 1 i)
    · rw [hM1]; funext i; exact congrFun h1 (Fin.natAdd k0 i)
  · rintro ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨append_eq_zero'.mpr ⟨h1, by rw [h4, hM1]⟩, h2, h3, fin0_eq⟩

lemma lamV_sw (hM1 : ∀ y, M1.mulVec y = 0) {y : TanV k0 k1 g 1} (hy : y ∈ LamV Ls M1) :
    swE y ∈ LamV Ls (0 : Matrix (Fin 0) (Fin g) ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  rw [hM1, sub_zero] at h4
  exact ⟨algVec_append'.mpr ⟨h1, h4⟩, h2, h3, fun i => i.elim0⟩

/-- The transported data satisfy the premises of Theorem 4.1 for the `r = 0` presentation. -/
lemma sw_premises (hM1 : ∀ y, M1.mulVec y = 0) (V W : Submodule ℂ (TanV k0 k1 g 1))
    (Y : AddSubgroup (TanV k0 k1 g 1)) (hq : finrank ℂ V + 1 = k0 + k1 + g + 1) (hWV : W ≤ V)
    (hWrat : RatSubV W) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M1) :
    finrank ℂ (V.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap) < k0 + 1 + k1 + g + 0 ∧
      W.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap ≤ V.map swE.toLinearMap ∧
      RatSubV (W.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap) ∧
      V.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap ⊓ fibreV = ⊥ ∧
      (Y.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap.toAddMonoidHom).FG ∧
      (∀ y ∈ Y.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap.toAddMonoidHom,
        y ∈ V.map swE.toLinearMap ∧ y ∈ LamV Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) ∧
      finrank ℂ (V.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap) = finrank ℂ V ∧
      rk (Y.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap.toAddMonoidHom ⊓
        PerV Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) = rk (Y ⊓ PerV Ls M1) := by
  classical
  set e := (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap with he
  have einj : Function.Injective e := swE.injective
  have hfV : finrank ℂ (V.map e) = finrank ℂ V := K5d.finrank_map_inj einj V
  refine ⟨by omega, Submodule.map_mono hWV, ?_, ?_, K11.fg_map_addSubgroup hYfg _, ?_, hfV, ?_⟩
  · rw [hWrat, Submodule.map_span]
    refine ratV_of_span _ ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hw.2
    exact ⟨algVec_append'.mpr ⟨h1, h4⟩, h2, h3, fun i => i.elim0⟩
  · rw [eq_bot_iff]
    rintro x ⟨-, ⟨s, rfl⟩⟩
    rw [Submodule.mem_bot, fin0_eq (x := s) (y := 0), map_zero]
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, (hY y hy).1, rfl⟩, lamV_sw hM1 (hY y hy).2⟩
  · rw [perV_sw Ls M1 hM1, ← AddSubgroup.map_inf_eq _ _ _ einj,
      LSG.CM.rk_map_of_injective _ einj]

set_option maxHeartbeats 400000 in -- many `finrank`/`rk` rewrites
/-- **Theorem 4.1 for the `r = 1, M = 0` presentation from the `r = 0` one** (`codim V = 1`). -/
theorem concl41_sw (hM1 : ∀ y, M1.mulVec y = 0) (V W : Submodule ℂ (TanV k0 k1 g 1))
    (Y : AddSubgroup (TanV k0 k1 g 1)) (hq : finrank ℂ V + 1 = k0 + k1 + g + 1)
    (hC : Concl41 Ls (0 : Matrix (Fin 0) (Fin g) ℂ)
      (V.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap) (W.map swE.toLinearMap)
      (Y.map (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap.toAddMonoidHom)) :
    Concl41 Ls M1 V W Y := by
  classical
  set e := (swE (k0 := k0) (k1 := k1) (g := g)).toLinearMap with he
  have einj : Function.Injective e := swE.injective
  set φ := e.toAddMonoidHom with hφ
  have hφ' : Function.Injective φ := einj
  obtain ⟨H0, hprop, hτ, hin⟩ := hC
  set H1 := subSw Ls M1 H0 with hH1
  have hT : H1.tan.map e = H0.tan := map_tan_subSw hM1 H0
  have hfT : finrank ℂ H1.tan = finrank ℂ H0.tan := by rw [← hT, K5d.finrank_map_inj einj]
  have hfV : finrank ℂ (V.map e) = finrank ℂ V := K5d.finrank_map_inj einj V
  have hfW : finrank ℂ (W.map e) = finrank ℂ W := K5d.finrank_map_inj einj W
  have hWinf : finrank ℂ ↥(W.map e ⊓ H0.tan) = finrank ℂ ↥(W ⊓ H1.tan) := by
    rw [← hT, ← Submodule.map_inf _ einj, K5d.finrank_map_inj einj]
  have hP := perV_sw (k0 := k0) (k1 := k1) Ls M1 hM1
  have rkY : rk (Y.map φ) = rk Y := LSG.CM.rk_map_of_injective φ hφ' Y
  have rkP : rk (Y.map φ ⊓ PerV Ls (0 : Matrix (Fin 0) (Fin g) ℂ)) = rk (Y ⊓ PerV Ls M1) := by
    rw [hP, ← AddSubgroup.map_inf_eq _ _ φ hφ', LSG.CM.rk_map_of_injective φ hφ']
  have rkT : rk (Y.map φ ⊓ (H0.tan.toAddSubgroup ⊔ PerV Ls (0 : Matrix (Fin 0) (Fin g) ℂ))) =
      rk (Y ⊓ (H1.tan.toAddSubgroup ⊔ PerV Ls M1)) := by
    have : H0.tan.toAddSubgroup = H1.tan.toAddSubgroup.map φ := by rw [← hT]; rfl
    rw [this, hP, ← AddSubgroup.map_sup, ← AddSubgroup.map_inf_eq _ _ φ hφ',
      LSG.CM.rk_map_of_injective φ hφ']
  -- codimensions: `δ`, `δ₁` unchanged, `δ₀` drops by at most one
  have hδ : H1.δ = H0.δ := by simp only [SubgroupDataV.δ, hfT]; omega
  have hδ1 : H1.δ1 = H0.δ1 := rfl
  have hδ0 : H0.δ0 ≤ H1.δ0 + 1 := by
    have h1 := finrank_fst_gsw (k0 := k0) H0.gam
    have h2 := finrank_gam_fst_le H1
    simp only [SubgroupDataV.δ0]
    change _ ≤ k0 - finrank ℂ ((H0.gam.map gsw).map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 1 → ℂ))) + 1
    change finrank ℂ ((H0.gam.map gsw).map (LinearMap.fst ℂ (Fin k0 → ℂ) (Fin 1 → ℂ))) ≤ k0 at h2
    omega
  have hδ2 : H1.δ2 ≤ H0.δ2 + 1 := by
    simp only [SubgroupDataV.δ2]; rw [hδ, hδ1]; omega
  refine ⟨H1, ?_, ?_, ?_⟩
  · change H1.δ ≠ 0; rw [hδ]; exact hprop
  · rw [hδ, ← hfW, ← hWinf]; exact hτ
  · rw [rkY, rkT, rkP, hfV, hfW, hWinf] at hin
    rw [hfW, hWinf] at hτ
    rw [hδ, hδ1]
    generalize finrank ℂ W - finrank ℂ ↥(W ⊓ H1.tan) = τ at hin hτ ⊢
    generalize rk Y - rk (Y ⊓ (H1.tan.toAddSubgroup ⊔ PerV Ls M1)) = lam at hin ⊢
    generalize rk (Y ⊓ PerV Ls M1) = κ at hin ⊢
    have hq0 : ((k0 + 1 + k1 + g + 0 : ℕ) : ℤ) - (finrank ℂ V : ℤ) = 1 := by omega
    have hq1 : ((k0 + k1 + g + 1 : ℕ) : ℤ) - (finrank ℂ V : ℤ) = 1 := by omega
    rw [hq0, mul_one] at hin
    rw [hq1, mul_one]
    have hpos : (1 : ℤ) ≤ (H0.δ : ℤ) - τ := by omega
    have e2 : (((k1 + 2 * (g + 1) : ℕ) : ℤ) - κ) = (((k1 + 2 * (g + 0) : ℕ) : ℤ) - κ) + 2 := by
      push_cast; ring
    have hδ2' : (H1.δ2 : ℤ) ≤ H0.δ2 + 1 := by exact_mod_cast hδ2
    rw [e2, mul_add]
    push_cast at hin ⊢
    nlinarith

end Sw

/-! ### The wrappers used by the engine (`f` a variable, `f = 1`) -/

/-- **`f = 1`, `M_H = 0`, (NR) of the `r = 0` presentation**: Theorem 4.1 from
`Theorem41VecLAOnto` at `r = 0`. -/
theorem concl41_swOnto (h41o : Theorem41VecLAOnto) {f : ℕ} (hf : f = 1) {Ls : Fin g → PeriodPair}
    (hLs : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃) (hLA : LiftAlg Ls)
    (M1 : Matrix (Fin f) (Fin g) ℂ) (hM1 : ∀ y, M1.mulVec y = 0)
    (V W : Submodule ℂ (TanV k0 k1 g f)) (Y : AddSubgroup (TanV k0 k1 g f))
    (hq : finrank ℂ V + 1 = k0 + k1 + g + f) (hWV : W ≤ V) (hWrat : RatSubV W) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M1)
    (hNR : k1 + 2 * (k0 + 1) + rk (Y ⊓ PerV Ls M1) ≤ 2 * finrank ℂ V) : Concl41 Ls M1 V W Y := by
  subst hf
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := sw_premises hM1 V W Y hq hWV hWrat hYfg hY
  exact concl41_sw hM1 V W Y hq (h41o (k0 + 1) k1 g 0 Ls 0 hLs (fun i => i.elim0) (Nat.zero_le _)
    hLA (fun _ => ⟨0, fin0_eq⟩) _ _ _ p1 p2 p3 p4 p5 p6 (by rw [p7, p8]; omega))

/-- **`f = 1`, `g = 0`** (`G_H = G_a^{k₀+1} × G_m^{k₁}`): Theorem 4.1 without (NR) (Roy). -/
theorem concl41_swLin {f : ℕ} (hf : f = 1) (hg : g = 0) (Ls : Fin g → PeriodPair)
    (M1 : Matrix (Fin f) (Fin g) ℂ) (V W : Submodule ℂ (TanV k0 k1 g f))
    (Y : AddSubgroup (TanV k0 k1 g f)) (hq : finrank ℂ V + 1 = k0 + k1 + g + f) (hWV : W ≤ V)
    (hWrat : RatSubV W) (hYfg : Y.FG) (hY : ∀ y ∈ Y, y ∈ V ∧ y ∈ LamV Ls M1) :
    Concl41 Ls M1 V W Y := by
  subst hf hg
  have hM1 : ∀ y, M1.mulVec y = 0 := fun y => funext fun i => by simp [Matrix.mulVec, dotProduct]
  obtain ⟨p1, p2, p3, -, p5, p6, -, -⟩ := sw_premises hM1 V W Y hq hWV hWrat hYfg hY
  exact concl41_sw hM1 V W Y hq (concl41_lin rfl rfl Ls 0 _ _ _ p1 p2 p3 p5 p6)

/-- A non-onto `f × g` matrix with `f = 1` is zero. -/
lemma mulVec_eq_zero_of_not_surj {f : ℕ} (hf : f = 1) {A : Matrix (Fin f) (Fin g) ℂ}
    (h : ¬ Function.Surjective A.mulVec) : ∀ y, A.mulVec y = 0 := by
  subst hf
  intro y
  by_contra hy
  apply h
  intro t
  have hy0 : A.mulVec y 0 ≠ 0 := fun h0 =>
    hy (funext fun i => by rw [Subsingleton.elim i 0]; exact h0)
  refine ⟨(t 0 / A.mulVec y 0) • y, funext fun i => ?_⟩
  rw [Subsingleton.elim i 0, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hy0]

/-! ### The corner with `M_H = 0` -/

variable {d0 d1 m r : ℕ} {Ls : Fin m → PeriodPair} {M : Matrix (Fin r) (Fin m) ℂ}

/-- For `M = 0`, rational combinations of periods have no fibre component. -/
lemma omV_snd_eq_zero (hM : ∀ y, M.mulVec y = 0) {x : TanV d0 d1 m r}
    (hx : x ∈ OmV d0 d1 Ls M) : x.2.2.2 = 0 := by
  let p : TanV d0 d1 m r →ₗ[ℚ] (Fin r → ℂ) :=
    LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  have : OmV d0 d1 Ls M ≤ LinearMap.ker p := by
    rw [Submodule.span_le]
    rintro y ⟨-, -, -, h4⟩
    change y.2.2.2 = 0
    rw [h4, hM]
  exact this hx

/-- **The (NR) corner** with `f = 0` weakened to `M_H = 0` (`corner_falseV` otherwise verbatim):
`M_H = 0`, `dim t ≥ 1`, and a `ℚ`-space `X ⊂ span Ω ∩ T_{G'} ∩ V` of dimension
`≥ dim U^⊥ + 2 dim t − 1`. Then `V ⊇ T_{B̃}`. -/
theorem corner_falseV' {H' : SubgroupDataV (d0 := d0) (d1 := d1) Ls M} (F : Frame H')
    (hMH : ∀ y, F.MH.mulVec y = 0) (hg : 1 ≤ fg H') (V : Submodule ℂ (TanV d0 d1 m r))
    (hno : ∀ H : SubgroupDataV (d0 := d0) (d1 := d1) Ls M, H.tan ≤ V → H.tan = ⊥)
    (X : Submodule ℚ (TanV d0 d1 m r)) (hXΩ : X ≤ OmV d0 d1 Ls M ⊓ H'.tan.restrictScalars ℚ)
    (hXV : X ≤ V.restrictScalars ℚ)
    (hX : finrank ℂ (torusLie H'.U) + 2 * fg H' ≤ finrank ℚ X + 1) : False := by
  classical
  have : FiniteDimensional ℚ X := Submodule.finiteDimensional_of_le (hXΩ.trans inf_le_left)
  let p₂ : TanV d0 d1 m r →ₗ[ℚ] (Fin d1 → ℂ) := LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  let p₃ : TanV d0 d1 m r →ₗ[ℚ] (Fin m → ℂ) :=
    LinearMap.fst ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _ ∘ₗ LinearMap.snd ℚ _ _
  let g2π : (Fin d1 → ℚ) →ₗ[ℚ] (Fin d1 → ℂ) :=
    (2 * Real.pi * I : ℂ) • (K11.castL d1).restrictScalars ℚ
  -- the toric image has dimension `≤ dim U^⊥`
  have himg : X.map p₂ ≤ (K11.annQ H'.U).map g2π := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, ⟨q, hq⟩, -, -⟩ := mem_OmV (hXΩ hx).1
    have hb : x.2.1 ∈ torusLie H'.U := (tan_le_prod H' (hXΩ hx).2).2.1
    rw [hq] at hb
    exact ⟨q, K5d.castL_mem_torusLie_iff.mp hb, by simp [g2π, p₂, hq]⟩
  have hgdim : finrank ℚ ↥((K11.annQ H'.U).map g2π) ≤ finrank ℂ (torusLie H'.U) := by
    have h1 := K11.finrank_annQ H'.U
    have h2 := K5d.finrank_torusLie H'.U
    have h3 := Submodule.finrank_map_le g2π (K11.annQ H'.U)
    omega
  set K₁ := X ⊓ LinearMap.ker p₂ with hK₁
  have : FiniteDimensional ℚ K₁ := Submodule.finiteDimensional_of_le inf_le_left
  have hK₁dim : finrank ℚ X ≤ finrank ℚ K₁ + finrank ℂ (torusLie H'.U) := by
    have e1 := K5d.finrank_map_add_inf_ker p₂ X
    rw [← hK₁] at e1
    have e2 := Submodule.finrank_mono himg
    omega
  set K := K₁.map p₃ with hK
  have hKinj : K₁ ⊓ LinearMap.ker p₃ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxX, hx2⟩, hx3⟩
    rw [Submodule.mem_bot]
    have h := mem_OmV (hXΩ hxX).1
    have h3 : x.2.2.1 = 0 := hx3
    exact Prod.ext h.1 (Prod.ext hx2 (Prod.ext h3 (h.2.2.2 h3)))
  have hKdim : finrank ℚ K = finrank ℚ K₁ := by
    have := K5d.finrank_map_add_inf_ker p₃ K₁
    rw [hKinj, finrank_bot] at this; omega
  have hKlat : K ≤ K5d.latQ Ls := by
    rintro _ ⟨x, ⟨hxX, -⟩, rfl⟩
    exact (mem_OmV (hXΩ hxX).1).2.2.1
  have hKt : K ≤ H'.t.restrictScalars ℚ := by
    rintro _ ⟨x, ⟨hxX, -⟩, rfl⟩
    exact F.mem_t_of_tan (hXΩ hxX).2
  -- the map `L z = (0, 0, lift(z ∘ ι), M κ_t(z ∘ ι))`
  let L : (Fin m → ℂ) →ₗ[ℂ] TanV d0 d1 m r :=
    (0 : (Fin m → ℂ) →ₗ[ℂ] (Fin d0 → ℂ)).prod ((0 : (Fin m → ℂ) →ₗ[ℂ] (Fin d1 → ℂ)).prod
      ((F.c.lift ∘ₗ LSG.CM.proj F.c.ι).prod (M.mulVecLin ∘ₗ F.K ∘ₗ LSG.CM.proj F.c.ι)))
  have hL : ∀ z, L z =
      (0, 0, F.c.lift (LSG.CM.proj F.c.ι z), M.mulVec (F.K (LSG.CM.proj F.c.ι z))) :=
    fun z => rfl
  have hxform : ∀ x ∈ K₁, x = L (p₃ x) := by
    rintro x ⟨hxX, hx2⟩
    have hx2' : x.2.1 = 0 := hx2
    have hmem := hXΩ hxX
    rw [← F.map_span_per] at hmem
    obtain ⟨x', hx', rfl⟩ := hmem
    have hs : x'.2.2.2 = 0 := omV_snd_eq_zero hMH hx'
    have ha : x'.1 = 0 := (mem_OmV hx').1
    change (K11.cm F.C).mulVec x'.2.1 = 0 at hx2'
    change F.Psi x' = L (F.c.lift x'.2.2.1)
    rw [hL, F.c.proj_lift, Frame.Psi_apply, ha, hs, hx2']
    simp
  -- `span_ℂ K = t`
  set S := Submodule.span ℂ (K : Set (Fin m → ℂ)) with hS
  have hSt : S ≤ H'.t := Submodule.span_le.mpr fun z hz => hKt hz
  have hreal : finrank ℚ K ≤ 2 * finrank ℂ S := by
    refine (K5d.finrank_le_real Ls K hKlat).trans ?_
    rw [← K5d.finrank_real_restrict]
    refine Submodule.finrank_mono ?_
    rw [Submodule.span_le]; intro z hz; exact Submodule.subset_span hz
  have hSdim : finrank ℂ S ≤ finrank ℂ H'.t := Submodule.finrank_mono hSt
  have hSeq : S = H'.t := Submodule.eq_of_le_of_finrank_eq hSt (by simp only [fg] at hX; omega)
  -- `L(t) ⊂ V`
  have hLV : H'.t.map L ≤ V := by
    rw [← hSeq, hS, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨z, ⟨x, hxK₁, rfl⟩, rfl⟩
    rw [← hxform x hxK₁]
    exact hXV hxK₁.1
  -- the subgroup `0 × 0 × B̃`
  have hgam : RatPair (⊥ : Submodule ℂ ((Fin d0 → ℂ) × (Fin r → ℂ))) :=
    le_antisymm bot_le (Submodule.span_le.mpr fun _ hw => hw.1)
  let Hab : SubgroupDataV (d0 := d0) (d1 := d1) Ls M :=
    { U := ⊤, t := H'.t, gam := ⊥, gam_rat := hgam, t_ab := H'.t_ab }
  have hle : Hab.tan ≤ V := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨γ, hγ, rfl⟩
      rw [(Submodule.mem_bot ℂ).mp hγ, map_zero]; exact V.zero_mem
    · rintro _ ⟨v, hv, rfl⟩
      change v ∈ torusLie (⊤ : Submodule ℚ (Fin d1 → ℚ)) at hv
      rw [K5d.torusLie_top, Submodule.mem_bot] at hv
      rw [hv, map_zero]; exact V.zero_mem
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have he := perTanId_eq F.c H'.t_ab hp
      have hMN : M.mulVec (F.N (LSG.CM.proj F.c.ι p.2)) = 0 := by
        rw [← F.Fm_MH, hMH, map_zero]
      have : g2Incl ((LinearMap.prodMap LinearMap.id M.mulVecLin) p) =
          L (F.c.lift (LSG.CM.proj F.c.ι p.1)) := by
        conv_lhs => rw [he]
        rw [hL, F.c.proj_lift]
        simp [Matrix.mulVec_add, hMN]
      rw [this]
      exact hLV ⟨_, F.c.lift_mem _, rfl⟩
  have hbot := hno Hab hle
  -- but `T_{B̃} ≠ 0`
  set μ₀ : Fin (fg H') → ℂ := Pi.single ⟨0, hg⟩ 1
  have hmem : g2Incl ((LinearMap.prodMap LinearMap.id M.mulVecLin)
      (F.c.lift μ₀, F.K μ₀ + F.N 0)) ∈ Hab.tan :=
    Submodule.mem_sup_right ⟨_, ⟨_, mem_perTanId_lift F.c H'.t_ab μ₀ 0, rfl⟩, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  have h3 : F.c.lift μ₀ = 0 := congrArg (fun p => p.2.2.1) hmem
  have : μ₀ = 0 := by rw [← F.c.proj_lift μ₀, h3, map_zero]
  have h1 := congrFun this ⟨0, hg⟩
  simp [μ₀] at h1

end LSG.W88.V5d
