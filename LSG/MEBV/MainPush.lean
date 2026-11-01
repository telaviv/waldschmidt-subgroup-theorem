/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Main

/-!
# `MultEstV` from the estimate on `G̃` (the push-out bookkeeping; template `LSG.MEV.MainVecPush`)

`G = G̃_r / K_M` (`Stmt.lean`), `M` onto.
* `K_M`-invariance of `P` (`InvarKV`) makes the analytic order invariant under `exp(K_M)` (`ordGtV_add_kvec`), so
  `MultEstGV` with `Kv = K_M` gives an obstruction `O` with `K_M ⊆ O.tan`;
* the exponents: with `K_M ⊆ T̃′` and `M` onto, `ex0 T̃′ = t0 + r` (`finrank_map_prA_eq`) and
  `t2 = ex2 T̃′ + r` (`finrank_t2_eq`);
* **`multEstV_of_GV : MultEstGV → MultEstV`**;
* **`multEstV_of_wust : MEBVInputs → (∀ d₀ d₁ m B, WustInput d₀ d₁ B) → MultEstV`** (with `Main.multEstGV_of`).
  When β's `wust_of_tz : TZPropV O → WustPropV O` lands, `multEstV_of : MEBVInputs → MultEstV` is one line.
-/

open MvPolynomial Module LSG.W88

namespace LSG.MEBV

open LSG.MEB (Blk DfunB)

variable {d₀ r d₁ m : ℕ} {B : Fin m → VBlock}

/-! ### Linear algebra of the exponents -/

theorem kvec_apply' (M : Matrix (Fin r) (Fin m) ℂ) (u : Fin m → ℂ) :
    kvec (d₀ := d₀) (d₁ := d₁) (B := B) M u = (Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u), 0, 0, u) := rfl

theorem finrank_ker_funLeft_castAdd' :
    finrank ℂ ↥(LinearMap.ker (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r)))) =
      r := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r)))
  have hs : LinearMap.range (LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r))) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _
      (Fin.castAdd_injective d₀ r))
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

/-- **`ex0 T̃′ = t0 + r`** for `K_M ⊆ T̃′`, `M` onto. -/
theorem finrank_map_prA_eq {M : Matrix (Fin r) (Fin m) ℂ} (hM : Function.Surjective M.mulVec)
    {T : Submodule ℂ (Tan (d₀ + r) d₁ B)} (hK : kerK d₀ d₁ B M ≤ T) :
    ex0 T = finrank ℂ (T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B))) + r := by
  classical
  set f := LinearMap.funLeft ℂ ℂ (Fin.castAdd r : Fin d₀ → Fin (d₀ + r))
  set U := T.map (prA : Tan (d₀ + r) d₁ B →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
  have hker : LinearMap.ker f ≤ U := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨u, hu⟩ := hM (-(fun i => x (Fin.natAdd d₀ i)))
    refine ⟨kvec M u, hK ⟨u, rfl⟩, ?_⟩
    rw [prA_apply, kvec_apply', hu, neg_neg]
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have := congrFun hx i
      simp only [f, LinearMap.funLeft_apply, Pi.zero_apply] at this
      simp [this]
    · simp
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hker).finrank_eq, finrank_ker_funLeft_castAdd'] at h
  have e : U.map f = T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) := by
    rw [← Submodule.map_comp]; rfl
  rw [e] at h
  change finrank ℂ U = _
  omega

/-- **`t2 = ex2 T̃′ + r`** for `K_M ⊆ T̃′`, `M` onto. -/
theorem finrank_t2_eq {M : Matrix (Fin r) (Fin m) ℂ} (hM : Function.Surjective M.mulVec)
    {T : Submodule ℂ (Tan (d₀ + r) d₁ B)} (hK : kerK d₀ d₁ B M ≤ T) :
    finrank ℂ ↥(T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B)))) = ex2 T + r := by
  classical
  set T₂ := T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B)))
  set T₃ := T ⊓ (LinearMap.ker (prA : Tan (d₀ + r) d₁ B →ₗ[ℂ] (Fin (d₀ + r) → ℂ)) ⊓
      LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (B := B)))
  set g := (LinearMap.funLeft ℂ ℂ (Fin.natAdd d₀ : Fin r → Fin (d₀ + r))).comp
    (prA : Tan (d₀ + r) d₁ B →ₗ[ℂ] (Fin (d₀ + r) → ℂ))
  have hkvec : ∀ u, kvec (d₀ := d₀) (d₁ := d₁) (B := B) M u ∈ T₂ := fun u => by
    refine ⟨hK ⟨u, rfl⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      simp [prLead, kvec_apply']
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      rfl
  have hle : T₃ ≤ T₂ := by
    rintro x ⟨hxT, hxA, hxB⟩
    refine ⟨hxT, ?_, hxB⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hxA ⊢
    funext i
    exact congrFun hxA (Fin.castAdd r i)
  have hrange : LinearMap.range (g.domRestrict T₂) = ⊤ := by
    rw [eq_top_iff]
    intro b _
    obtain ⟨u, hu⟩ := hM (-b)
    refine ⟨⟨kvec M u, hkvec u⟩, ?_⟩
    funext i
    show Fin.append (0 : Fin d₀ → ℂ) (-M.mulVec u) (Fin.natAdd d₀ i) = b i
    simp [hu]
  have hkerg : LinearMap.ker (g.domRestrict T₂) = T₃.comap T₂.subtype := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply]
    obtain ⟨hxT, hxL, hxB⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hxL
    constructor
    · intro h0
      refine ⟨hxT, ?_, hxB⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · exact congrFun hxL i
      · exact congrFun h0 i
    · rintro ⟨-, hxA, -⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hxA
      funext i
      exact congrFun hxA (Fin.natAdd d₀ i)
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict T₂)
  rw [hrange, finrank_top, Module.finrank_fin_fun, hkerg,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h
  show finrank ℂ ↥T₂ = finrank ℂ ↥T₃ + r
  exact h.symm.trans (Nat.add_comm _ _)

/-! ### `K_M`-invariance of the order -/

/-- Translation by `exp(K_M)` preserves the analytic order of a `K_M`-invariant polynomial. -/
theorem ordGtV_add_kvec {M : Matrix (Fin r) (Fin m) ℂ} {P : MvPolynomial (Var (d₀ + r) d₁ B) ℂ}
    (hInv : InvarKV M P) (W : Submodule ℂ (Tan (d₀ + r) d₁ B)) (n : ℕ) (y : GPt (d₀ + r) d₁ B)
    (v : Fin m → ℂ) (hy : OrdGtV W P n y) :
    OrdGtV W P n (y + expG (d₀ + r) d₁ B (kvec M v)) := by
  obtain ⟨u, hu, h⟩ := hy
  refine ⟨u + kvec M v, by rw [map_add, hu], fun w hw k hk => ?_⟩
  have e : (fun s : ℂ => eval (liftV (u + kvec M v + s • w)) P) =
      fun s : ℂ => eval (liftV (u + s • w)) P := by
    funext s
    rw [show u + kvec M v + s • w = (u + s • w) + kvec M v by abel]
    exact hInv _ v
  rw [e]
  exact h w hw k hk

/-! ### The push-out -/

/-- **`MultEstV` from the estimate on `G̃`.** -/
theorem multEstV_of_GV (hG : MultEstGV) : MultEstV := by
  intro d₀ r d₁ m B M hM
  obtain ⟨C, hC⟩ := hG (d₀ + r) d₁ m B
  refine ⟨C, fun W S P T D₀ D₁ D₂ hS hPh hPD _hTr hInv hPI hT hD₀ hD₁ hD₂ hvan => ?_⟩
  classical
  have hK : ∀ v ∈ kerK d₀ d₁ B M, ∀ (y : GPt (d₀ + r) d₁ B) (n : ℕ), OrdGtV W P n y →
      OrdGtV W P n (y + expG (d₀ + r) d₁ B v) := by
    rintro _ ⟨u, rfl⟩ y n hy
    exact ordGtV_add_kvec hInv W n y u hy
  obtain ⟨O, hprop, hKs, hineq⟩ := hC W S P T D₀ D₁ D₂ (kerK d₀ d₁ B M) hS hPh hPD hPI hT hD₀ hD₁ hD₂
    hvan hK
  let O' : ObstrDataBV d₀ r d₁ B M :=
    { U := O.U, t := O.t, t_rat := O.t_rat, gam := O.gam, grp := O.grp, grp_eq := O.grp_eq,
      grp_sub := O.grp_sub, grp_closed := O.grp_closed, lie := O.lie, ker_le := hKs,
      htil := O.htil }
  have hOtan : O'.tan = O.tan := rfl
  refine ⟨O', hprop, fun F hFS hFd => ?_⟩
  have h1 := hineq F hFS hFd
  have hex0 : ex0 O.tan = O'.t0 + r := by
    rw [finrank_map_prA_eq hM hKs]; rfl
  have hex2 : O'.t2 = ex2 O.tan + r := finrank_t2_eq hM hKs
  rw [hex0] at h1
  rw [hex2, hOtan]
  change T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O'.t0 *
      D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ (ex2 O.tan + r) ≤ _
  have hD0r : 0 < D₀ ^ r := pow_pos (by omega) r
  refine Nat.le_of_mul_le_mul_right ?_ hD0r
  calc T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ O'.t0 *
          D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ (ex2 O.tan + r) * D₀ ^ r
      = (T ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ O.tan)) * F.card * D₀ ^ (O'.t0 + r) *
          D₁ ^ (d₁ - finrank ℚ O.U) * D₂ ^ ex2 O.tan) * D₂ ^ r := by ring
    _ ≤ (C * D₀ ^ (d₀ + r) * D₁ ^ d₁ * D₂ ^ (∑ k, ((B k).g + 1))) * D₂ ^ r :=
        Nat.mul_le_mul_right _ h1
    _ = C * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (∑ k, ((B k).g + 1) + r) * D₀ ^ r := by ring

/-- **`MultEstV` from the subgroup layer and the sliced Wüstholz lemma.** -/
theorem multEstV_of_wust (hin : MEBVInputs)
    (hW : ∀ (d₀ d₁ m : ℕ) (B : Fin m → VBlock), WustInput d₀ d₁ B) : MultEstV :=
  multEstV_of_GV (multEstGV_of hin hW)

end LSG.MEBV
