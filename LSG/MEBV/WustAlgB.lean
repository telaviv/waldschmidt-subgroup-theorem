/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SliceWust
import LSG.MEBV.DerivOrd
import LSG.MEBV.WustHyp
import LSG.MEB.WustAlgB

/-!
# Derivation algebra for Wüstholz (M2.5, β)

The `VBlock` analogue of `LSG.MEB.WustAlgB`, for the chart derivations `Dh ch w` of `LSG.MEBV.Deriv`.

* `VBlock.bCoef_add`, `VBlock.bCoef_smul`, `DhCoef_add`, `DhCoef_smul`, **`Dh_add_apply`**, **`Dh_smul_apply`**:
  `Dh ch w` is linear in `w`; `pairL ch x P : Tan →ₗ[ℂ] ℂ`, `w ↦ (Dh ch w P)(x)`.
* `Dh_X`, **`Eul_Dh`**: `[Eul_k, Dh ch w] = 2 • Dh ch w` (the derivations raise block degrees by two).
* **`homOrd_le_VOg`**: `homOrd W n E ≤ VOg Dmix (Wmix W) I(E) n` (`homOrd` is α's, `LSG.MEBV.WustHyp`).
* Biorthogonal families: MEB's generic `LSG.MEB.exists_biorth` is used as is.
-/

open MvPolynomial Module

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Linearity of `Dh` in the direction -/

theorem VBlock.bCoef_add (b : VBlock) (t : Fin b.nT) (ζ ζ' : Fin b.g → ℂ) (ω ω' : ℂ) (a : b.Idx) :
    b.bCoef t (ζ + ζ') (ω + ω') a = b.bCoef t ζ ω a + b.bCoef t ζ' ω' a := by
  cases a with
  | inl l => simp only [bCoef, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]
  | inr t' => simp only [bCoef, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]; ring

theorem VBlock.bCoef_smul (b : VBlock) (t : Fin b.nT) (c : ℂ) (ζ : Fin b.g → ℂ) (ω : ℂ) (a : b.Idx) :
    b.bCoef t (c • ζ) (c * ω) a = C c * b.bCoef t ζ ω a := by
  cases a with
  | inl l =>
    simp only [bCoef, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  | inr t' =>
    simp only [bCoef, Pi.smul_apply, smul_eq_mul, map_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring

theorem DhCoef_add (ch : ∀ k, Fin (B k).nT) (w w' : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    DhCoef ch (w + w') v = DhCoef ch w v + DhCoef ch w' v := by
  cases v with
  | x i => simp [DhCoef, add_mul]
  | y j => simp [DhCoef, add_mul]
  | z j => simp only [DhCoef, Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add]; ring
  | e k a =>
    simp only [DhCoef, Prod.snd_add, Prod.fst_add, Pi.add_apply, VBlock.bCoef_add, map_add, mul_add]

theorem DhCoef_smul (ch : ∀ k, Fin (B k).nT) (c : ℂ) (w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    DhCoef ch (c • w) v = C c * DhCoef ch w v := by
  cases v with
  | x i => simp only [DhCoef, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul]; ring
  | y j => simp only [DhCoef, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul]; ring
  | z j => simp only [DhCoef, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul]; ring
  | e k a =>
    simp only [DhCoef, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, VBlock.bCoef_smul,
      map_mul, rename_C]
    ring

theorem Dh_add_apply (ch : ∀ k, Fin (B k).nT) (w w' : Tan d₀ d₁ B)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) : Dh ch (w + w') P = Dh ch w P + Dh ch w' P := by
  simp only [Dh_apply, DhCoef_add, add_mul, Finset.sum_add_distrib]

theorem Dh_smul_apply (ch : ∀ k, Fin (B k).nT) (c : ℂ) (w : Tan d₀ d₁ B)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) : Dh ch (c • w) P = C c * Dh ch w P := by
  simp only [Dh_apply, DhCoef_smul, Finset.mul_sum, mul_assoc]

theorem Dh_C_mul (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) (c : ℂ)
    (x : MvPolynomial (Var d₀ d₁ B) ℂ) : Dh ch w (C c * x) = C c * Dh ch w x := by
  have h0 : Dh ch w (C c) = 0 := by
    rw [← MvPolynomial.algebraMap_eq]; exact Derivation.map_algebraMap _ _
  rw [Derivation.leibniz, h0, smul_zero, add_zero, smul_eq_mul]

/-- The pairing `w ↦ (Dh ch w P)(x)`, linear in `w`. -/
noncomputable def pairL (ch : ∀ k, Fin (B k).nT) (x : Var d₀ d₁ B → ℂ)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) : Tan d₀ d₁ B →ₗ[ℂ] ℂ where
  toFun w := eval x (Dh ch w P)
  map_add' w w' := by rw [Dh_add_apply, map_add]
  map_smul' c w := by rw [Dh_smul_apply, map_mul, eval_C]; rfl

theorem pairL_apply (ch : ∀ k, Fin (B k).nT) (x : Var d₀ d₁ B → ℂ)
    (P : MvPolynomial (Var d₀ d₁ B) ℂ) (w : Tan d₀ d₁ B) : pairL ch x P w = eval x (Dh ch w P) :=
  rfl

/-! ### `[Eul_k, Dh] = 2 Dh` -/

theorem Dh_X (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B) (v : Var d₀ d₁ B) :
    Dh ch w (X v) = DhCoef ch w v := by
  classical
  rw [Dh_apply, Finset.sum_eq_single v (fun b _ hb => by rw [pderiv_X_of_ne (Ne.symm hb), mul_zero])
    (by simp)]
  simp

/-- **`[Eul_k, Dh] = 2 • Dh`.** -/
theorem Eul_Dh (k : Fin m) (ch : ∀ k, Fin (B k).nT) (w : Tan d₀ d₁ B)
    (x : MvPolynomial (Var d₀ d₁ B) ℂ) :
    Eul k (Dh ch w x) = Dh ch w (Eul k x) + 2 • Dh ch w x := by
  have h : ⁅(Eul (d₀ := d₀) (d₁ := d₁) (B := B) k :
      Derivation ℂ (MvPolynomial (Var d₀ d₁ B) ℂ) _), Dh ch w⁆ = (2 : ℕ) • Dh ch w := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Dh_X, Eul_apply k (isWH_DhCoef ch w k v), Eul_X, map_nsmul,
      Dh_X, Derivation.smul_apply, Dh_X, add_smul, add_sub_cancel_right]
  have h' := congrArg (fun D : Derivation ℂ _ _ => D x) h
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at h'
  rw [← h']
  abel

/-! ### The order bridge -/

/-- **The order bridge**: `homOrd W n E ≤ VOg Dmix (Wmix W) I(E) n`. -/
theorem homOrd_le_VOg (W : Submodule ℂ (Tan d₀ d₁ B)) (n : ℕ) (E : Set (GPt d₀ d₁ B)) :
    homOrd W n E ≤ LSG.ME.VOg Dmix (Wmix W) (vanish E) n := by
  refine Ideal.span_le.mpr ?_
  rintro Q ⟨hQ, d, hd⟩ l hl hlen
  exact DL_Dmix_mem_vanish hl hd hlen hQ

end LSG.MEBV
