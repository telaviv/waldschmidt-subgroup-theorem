/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.StatementVec
import LSG.W88.K5dMain

/-!
# `ℚ̄`-structures on `TanV d₀ d₁ m r` (for the §5d engine of the vector-extension class)

* `AlgLin f`: a linear map `ℂ^a → ℂ^b` sending algebraic vectors to algebraic vectors; closure under
  composition, matrices over `ℚ̄` (`cmK`) and over `ℚ`; `algMat_toMatrix'`.
* `AlgEndV E`: the same for endomorphisms of `TanV`; `ratV_inf_ker_endo`: `W ⊓ ker E` is
  `ℚ̄`-rational for `W` rational and `E` algebraic (via the coordinate forms of `TanV`).
* `ratV_of_span`, `ratV_map`: rationality of spans of algebraic vectors and of images.
* `rational_of_le_one`: every subspace of `ℂ^r`, `r ≤ 1`, is `ℚ̄`-rational.
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

/-! ### Algebraic vectors -/

lemma algVec_zero {n : ℕ} : AlgVec (0 : Fin n → ℂ) := fun _ => by simpa using isAlgebraic_zero

lemma algVec_add {n : ℕ} {u v : Fin n → ℂ} (hu : AlgVec u) (hv : AlgVec v) : AlgVec (u + v) :=
  fun i => by
    simp only [Pi.add_apply, ← K11.mem_Kq]
    exact K11.Kq.add_mem (K11.mem_Kq.mpr (hu i)) (K11.mem_Kq.mpr (hv i))

lemma algVec_neg {n : ℕ} {u : Fin n → ℂ} (hu : AlgVec u) : AlgVec (-u) :=
  fun i => by
    simp only [Pi.neg_apply, ← K11.mem_Kq]
    exact K11.Kq.neg_mem (K11.mem_Kq.mpr (hu i))

lemma algVec_sub {n : ℕ} {u v : Fin n → ℂ} (hu : AlgVec u) (hv : AlgVec v) : AlgVec (u - v) := by
  rw [sub_eq_add_neg]; exact algVec_add hu (algVec_neg hv)

lemma algVec_smul {n : ℕ} {c : ℂ} (hc : IsAlgebraic ℚ c) {u : Fin n → ℂ} (hu : AlgVec u) :
    AlgVec (c • u) :=
  fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, ← K11.mem_Kq]
    exact K11.Kq.mul_mem (K11.mem_Kq.mpr hc) (K11.mem_Kq.mpr (hu i))

lemma algVec_single {n : ℕ} (i : Fin n) : AlgVec (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
  intro j; by_cases h : j = i
  · subst h; simpa using isAlgebraic_one
  · simpa [h] using isAlgebraic_zero

lemma algVec_sum {n : ℕ} {ι : Type*} (s : Finset ι) (u : ι → Fin n → ℂ)
    (hu : ∀ i ∈ s, AlgVec (u i)) : AlgVec (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using algVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact algVec_add (hu a (Finset.mem_insert_self _ _))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

lemma algVecV_zero {d0 d1 m r : ℕ} : AlgVecV (0 : TanV d0 d1 m r) :=
  ⟨algVec_zero, algVec_zero, algVec_zero, algVec_zero⟩

lemma algVecV_sub_smul {d0 d1 m r : ℕ} {v w : TanV d0 d1 m r} (hv : AlgVecV v) (hw : AlgVecV w)
    {c : ℂ} (hc : IsAlgebraic ℚ c) : AlgVecV (v - c • w) :=
  ⟨algVec_sub hv.1 (algVec_smul hc hw.1), algVec_sub hv.2.1 (algVec_smul hc hw.2.1),
    algVec_sub hv.2.2.1 (algVec_smul hc hw.2.2.1), algVec_sub hv.2.2.2 (algVec_smul hc hw.2.2.2)⟩

/-! ### Algebraic linear maps -/

/-- A linear map sending algebraic vectors to algebraic vectors. -/
def AlgLin {a b : ℕ} (f : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) : Prop := ∀ x, AlgVec x → AlgVec (f x)

lemma algLin_id {a : ℕ} : AlgLin (LinearMap.id : (Fin a → ℂ) →ₗ[ℂ] (Fin a → ℂ)) := fun _ h => h

lemma algLin_zero {a b : ℕ} : AlgLin (0 : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) :=
  fun _ _ => by simpa using algVec_zero

lemma AlgLin.comp {a b c : ℕ} {f : (Fin b → ℂ) →ₗ[ℂ] (Fin c → ℂ)}
    {g : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)}
    (hf : AlgLin f) (hg : AlgLin g) : AlgLin (f ∘ₗ g) := fun x hx => hf _ (hg x hx)

lemma AlgLin.add {a b : ℕ} {f g : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)} (hf : AlgLin f) (hg : AlgLin g) :
    AlgLin (f + g) := fun x hx => algVec_add (hf x hx) (hg x hx)

lemma AlgLin.sub {a b : ℕ} {f g : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)} (hf : AlgLin f) (hg : AlgLin g) :
    AlgLin (f - g) := fun x hx => algVec_sub (hf x hx) (hg x hx)

lemma algLin_cmK {a b : ℕ} (A : Matrix (Fin a) (Fin b) K11.Kq) :
    AlgLin (K5d.cmK K11.Kq A).mulVecLin := fun _ hx => K5d.algVec_cmK_mulVec A hx

lemma algLin_cm {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) : AlgLin (K11.cm C).mulVecLin :=
  fun _ hx => K5d.algVec_cm_mulVec C hx

lemma algLin_mat {a b : ℕ} {M : Matrix (Fin b) (Fin a) ℂ} (hM : AlgMat M) : AlgLin M.mulVecLin := by
  intro x hx i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, ← K11.mem_Kq]
  exact K11.Kq.sum_mem fun j _ => K11.Kq.mul_mem (K11.mem_Kq.mpr (hM i j)) (K11.mem_Kq.mpr (hx j))

lemma algMat_toMatrix' {a b : ℕ} {f : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)} (hf : AlgLin f) :
    AlgMat (LinearMap.toMatrix' f) := by
  intro i j
  rw [LinearMap.toMatrix'_apply]
  exact hf _ (algVec_single j) i

lemma algLin_proj {a b : ℕ} (ι : Fin a → Fin b) : AlgLin (LSG.CM.proj ι) := fun _ hx i => hx (ι i)

/-! ### Rationality in `TanV` -/

variable {d0 d1 m r : ℕ}

/-- A linear form on `TanV` with algebraic values at algebraic vectors. -/
def AlgFormV (f : TanV d0 d1 m r →ₗ[ℂ] ℂ) : Prop := ∀ v, AlgVecV v → IsAlgebraic ℚ (f v)

/-- An endomorphism of `TanV` preserving algebraic vectors. -/
def AlgEndV (E : TanV d0 d1 m r →ₗ[ℂ] TanV d0 d1 m r) : Prop := ∀ v, AlgVecV v → AlgVecV (E v)

lemma ratV_iff (W : Submodule ℂ (TanV d0 d1 m r)) :
    (∃ S : Set (TanV d0 d1 m r), (∀ v ∈ S, AlgVecV v) ∧ W = Submodule.span ℂ S) ↔ RatSubV W := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    apply le_antisymm
    · exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hS v hv⟩
    · exact Submodule.span_le.mpr fun _ hw => hw.1
  · intro h; exact ⟨_, fun v hv => hv.2, h⟩

lemma ratV_of_span (S : Set (TanV d0 d1 m r)) (hS : ∀ v ∈ S, AlgVecV v) :
    RatSubV (Submodule.span ℂ S) := (ratV_iff _).mp ⟨S, hS, rfl⟩

lemma ratV_inf_ker {W : Submodule ℂ (TanV d0 d1 m r)} (hW : RatSubV W)
    {f : TanV d0 d1 m r →ₗ[ℂ] ℂ} (hf : AlgFormV f) : RatSubV (W ⊓ LinearMap.ker f) := by
  classical
  rw [← ratV_iff] at hW ⊢
  obtain ⟨S, hSalg, rfl⟩ := hW
  by_cases h : ∀ s ∈ S, f s = 0
  · refine ⟨S, hSalg, ?_⟩
    refine inf_eq_left.mpr (Submodule.span_le.mpr fun s hs => ?_)
    exact LinearMap.mem_ker.mpr (h s hs)
  push Not at h
  obtain ⟨s₀, hs₀, hfs₀⟩ := h
  let g : TanV d0 d1 m r → TanV d0 d1 m r := fun s => s - (f s / f s₀) • s₀
  refine ⟨g '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine algVecV_sub_smul (hSalg s hs) (hSalg s₀ hs₀) ?_
    rw [← K11.mem_Kq]
    exact K11.Kq.div_mem (K11.mem_Kq.mpr (hf s (hSalg s hs)))
      (K11.mem_Kq.mpr (hf s₀ (hSalg s₀ hs₀)))
  apply le_antisymm
  · rintro w ⟨hw, hwk⟩
    have key : ∀ w ∈ Submodule.span ℂ S, g w ∈ Submodule.span ℂ (g '' S) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp [g]
      | add x y _ _ hx hy =>
        have : g (x + y) = g x + g y := by
          simp only [g, map_add, add_div, add_smul]; abel
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have : g (c • x) = c • g x := by
          simp only [g, map_smul, smul_eq_mul, smul_sub, smul_smul, mul_div_assoc]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key w hw
    rwa [show g w = w by simp [g, LinearMap.mem_ker.mp hwk]] at this
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hs)
      (Submodule.smul_mem _ _ (Submodule.subset_span hs₀)), ?_⟩
    change g s ∈ LinearMap.ker f
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfs₀, sub_self]

lemma ratV_inf_finsetInf {W : Submodule ℂ (TanV d0 d1 m r)} (hW : RatSubV W) {ι : Type*}
    (f : ι → TanV d0 d1 m r →ₗ[ℂ] ℂ) (hf : ∀ i, AlgFormV (f i)) (s : Finset ι) :
    RatSubV (W ⊓ s.inf fun i => LinearMap.ker (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert a s _ ih =>
    rw [Finset.inf_insert, inf_comm (LinearMap.ker (f a)), ← inf_assoc]
    exact ratV_inf_ker ih (hf a)

/-- The coordinate forms of `TanV`. -/
noncomputable def coordV : (Fin d0 ⊕ Fin d1 ⊕ Fin m ⊕ Fin r) → (TanV d0 d1 m r →ₗ[ℂ] ℂ)
  | Sum.inl i => (LinearMap.proj i).comp (LinearMap.fst ℂ _ _)
  | Sum.inr (Sum.inl i) =>
    (LinearMap.proj i).comp ((LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _))
  | Sum.inr (Sum.inr (Sum.inl i)) => (LinearMap.proj i).comp ((LinearMap.fst ℂ _ _).comp
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))
  | Sum.inr (Sum.inr (Sum.inr i)) => (LinearMap.proj i).comp ((LinearMap.snd ℂ _ _).comp
      ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)))

lemma eq_zero_of_coordV {x : TanV d0 d1 m r} (h : ∀ i, coordV i x = 0) : x = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i; exact h (Sum.inl i)
  · funext i; exact h (Sum.inr (Sum.inl i))
  · funext i; exact h (Sum.inr (Sum.inr (Sum.inl i)))
  · funext i; exact h (Sum.inr (Sum.inr (Sum.inr i)))

lemma algFormV_coordV_comp {E : TanV d0 d1 m r →ₗ[ℂ] TanV d0 d1 m r} (hE : AlgEndV E) :
    ∀ i, AlgFormV ((coordV i).comp E) := by
  intro i v hv
  have h := hE v hv
  rcases i with i | i | i | i
  · exact h.1 i
  · exact h.2.1 i
  · exact h.2.2.1 i
  · exact h.2.2.2 i

/-- **`W ⊓ ker E` is rational** for `W` rational and `E` an algebraic endomorphism. -/
lemma ratV_inf_ker_endo {W : Submodule ℂ (TanV d0 d1 m r)} (hW : RatSubV W)
    {E : TanV d0 d1 m r →ₗ[ℂ] TanV d0 d1 m r} (hE : AlgEndV E) : RatSubV (W ⊓ LinearMap.ker E) := by
  classical
  have h := ratV_inf_finsetInf hW (fun i => (coordV i).comp E) (algFormV_coordV_comp hE)
    Finset.univ
  convert h using 2
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_implies, LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro hx i; rw [hx, map_zero]
  · intro hx; exact eq_zero_of_coordV hx

/-! ### Rationality in `ℂ^a × ℂ^b` -/

lemma ratPair_of_span {a b : ℕ} (S : Set ((Fin a → ℂ) × (Fin b → ℂ))) (hS : ∀ v ∈ S, AlgPair v) :
    RatPair (Submodule.span ℂ S) := by
  apply le_antisymm
  · exact Submodule.span_mono fun v hv => ⟨Submodule.subset_span hv, hS v hv⟩
  · exact Submodule.span_le.mpr fun _ hw => hw.1

/-- Every subspace of `ℂ^r` with `r ≤ 1` is rational. -/
lemma rational_of_le_one {n : ℕ} (hn : n ≤ 1) (S : Submodule ℂ (Fin n → ℂ)) :
    RationalOverQbar S := by
  classical
  have hle : finrank ℂ S ≤ n := (Submodule.finrank_le S).trans (by simp)
  rcases Nat.eq_zero_or_pos (finrank ℂ S) with h0 | hpos
  · rw [Submodule.finrank_eq_zero.mp h0]; exact K5d.rational_bot
  · have htop : S = ⊤ := Submodule.eq_top_of_finrank_eq (by simp; omega)
    rw [htop]
    apply le_antisymm _ le_top
    intro v _
    have : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℂ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨Submodule.mem_top, algVec_single i⟩)

lemma rational_top {n : ℕ} : RationalOverQbar (⊤ : Submodule ℂ (Fin n → ℂ)) := by
  apply le_antisymm _ le_top
  intro v _
  have : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℂ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨Submodule.mem_top, algVec_single i⟩)

end LSG.W88.V5d
