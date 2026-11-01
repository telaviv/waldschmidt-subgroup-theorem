/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Statement
import LSG.W88.K11Omega

/-!
# Linear algebra over a subfield `K ⊂ ℂ` (for the §5d deduction on `G_a^{d₀} × G_m^{d₁} × ∏ E_j`)

Matrices with entries in a subfield `K` (in practice `K = ℚ̄`, `Kq`):
* `rightInv_of_surjective`: a `K`-matrix that is surjective over `ℂ` has a right inverse over `K`;
* `ker_eq_span_cols`: its kernel over `ℂ` is spanned by vectors with coordinates in `K`;
* `exists_algFrame`: a `ℚ̄`-rational subspace of `ℂ^n` is the column space of a `ℚ̄`-matrix with a
  `ℚ̄`-left inverse.
-/

open Module Matrix

namespace LSG.W88.K5d

variable (K : Subfield ℂ)

/-- Entrywise inclusion of a `K`-matrix. -/
noncomputable def cmK {p n : ℕ} (S : Matrix (Fin p) (Fin n) K) : Matrix (Fin p) (Fin n) ℂ := S.map K.subtype

/-- Inclusion of a `K`-vector. -/
noncomputable def vK {n : ℕ} (v : Fin n → K) : Fin n → ℂ := fun j => (v j : ℂ)

variable {K}

lemma cmK_mul {a b c : ℕ} (S : Matrix (Fin a) (Fin b) K) (T : Matrix (Fin b) (Fin c) K) :
    cmK K (S * T) = cmK K S * cmK K T :=
  Matrix.map_mul (f := K.subtype)

lemma cmK_one {a : ℕ} : cmK K (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  simp [cmK]

lemma cmK_sub {a b : ℕ} (S T : Matrix (Fin a) (Fin b) K) : cmK K (S - T) = cmK K S - cmK K T := by
  ext i j; simp [cmK]

lemma cmK_mulVec {a b : ℕ} (S : Matrix (Fin a) (Fin b) K) (v : Fin b → K) :
    (cmK K S).mulVec (vK K v) = vK K (S.mulVec v) := by
  ext i; simp [cmK, vK, Matrix.mulVec, dotProduct]

lemma vK_injective {n : ℕ} : Function.Injective (vK K (n := n)) := by
  intro a b h; funext j; exact Subtype.ext (congrFun h j)

/-- A `K`-matrix which is surjective over `ℂ` has a right inverse over `K`. -/
lemma rightInv_of_surjective {p n : ℕ} (S : Matrix (Fin p) (Fin n) K)
    (hS : Function.Surjective (cmK K S).mulVec) : ∃ R : Matrix (Fin n) (Fin p) K, S * R = 1 := by
  classical
  have hinj : LinearMap.ker Sᵀ.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Matrix.mulVecLin_apply] at hc
    funext i
    obtain ⟨x, hx⟩ := hS (Pi.single i 1)
    have hz : ∀ j, ∑ i', ((c i' : K) : ℂ) * ((S i' j : K) : ℂ) = 0 := by
      intro j
      have := congrFun hc j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
      have h2 : ((∑ i', S i' j * c i' : K) : ℂ) = 0 := by rw [this]; rfl
      simpa [mul_comm] using h2
    have key : ∑ i', ((c i' : K) : ℂ) * ((cmK K S).mulVec x) i' =
        ∑ j, (∑ i', ((c i' : K) : ℂ) * ((S i' j : K) : ℂ)) * x j := by
      simp only [cmK, Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [hz, zero_mul, Finset.sum_const_zero] at key
    rw [hx] at key
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at key
    exact_mod_cast key
  obtain ⟨g, hg⟩ := Sᵀ.mulVecLin.exists_leftInverse_of_injective hinj
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin'] at this
  have h2 := congrArg Matrix.transpose this
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h2

/-- If `S R = 1` over `K`, the kernel of `S` over `ℂ` is spanned by the columns of `1 − R S`,
which have coordinates in `K`. -/
lemma ker_eq_span_cols {p n : ℕ} (S : Matrix (Fin p) (Fin n) K) (R : Matrix (Fin n) (Fin p) K)
    (hSR : S * R = 1) :
    LinearMap.ker (cmK K S).mulVecLin =
      Submodule.span ℂ (Set.range fun j => vK K (fun i => ((1 : Matrix (Fin n) (Fin n) K) - R * S) i j)) := by
  have hcol : ∀ j, (cmK K (1 - R * S)).col j = vK K (fun i => ((1 : Matrix (Fin n) (Fin n) K) - R * S) i j) := by
    intro j; ext i; simp [vK, cmK, Matrix.col]
  have hSP : cmK K S * cmK K (1 - R * S) = 0 := by
    rw [← cmK_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSR, Matrix.one_mul,
      sub_self]; simp [cmK]
  have hrange : Set.range (cmK K (1 - R * S)).col =
      Set.range fun j => vK K (fun i => ((1 : Matrix (Fin n) (Fin n) K) - R * S) i j) := by
    ext v; simp only [Set.mem_range, hcol]
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    have : x = (cmK K (1 - R * S)).mulVec x := by
      rw [cmK_sub, cmK_one, Matrix.sub_mulVec, Matrix.one_mulVec, cmK_mul, ← Matrix.mulVec_mulVec,
        hx, Matrix.mulVec_zero, sub_zero]
    rw [this, ← hrange, ← Matrix.range_mulVecLin]
    exact ⟨x, rfl⟩
  · rw [Submodule.span_le, ← hrange]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have : (cmK K S).mulVec ((cmK K (1 - R * S)).col j) = (cmK K S * cmK K (1 - R * S)).col j := by
      ext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.col]
    rw [this, hSP]; rfl

/-- A `ℚ̄`-rational subspace of `ℂ^n` is the column space of a `ℚ̄`-matrix with a `ℚ̄`-left inverse. -/
lemma exists_algFrame {n : ℕ} (h : Submodule ℂ (Fin n → ℂ)) (hrat : RationalOverQbar h) :
    ∃ (A : Matrix (Fin n) (Fin (finrank ℂ h)) K11.Kq) (B : Matrix (Fin (finrank ℂ h)) (Fin n) K11.Kq),
      B * A = 1 ∧ LinearMap.range (cmK K11.Kq A).mulVecLin = h := by
  classical
  set S : Set (Fin n → ℂ) := {w | w ∈ h ∧ LSG.W88.AlgVec w} with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have : Finite b := hli.finite
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = finrank ℂ h := by
    have := finrank_span_set_eq_card hli
    rw [hspan, ← hrat] at this
    rw [this, Set.toFinset_card]
  let e : Fin (finrank ℂ h) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℂ h) → Fin n → ℂ := fun j => (e j : Fin n → ℂ)
  have ha : ∀ j, a j ∈ S := fun j => hbS (e j).2
  let A : Matrix (Fin n) (Fin (finrank ℂ h)) K11.Kq :=
    Matrix.of fun i j => ⟨a j i, K11.mem_Kq.mpr ((ha j).2 i)⟩
  have hAcol : ∀ c : Fin (finrank ℂ h) → ℂ, (cmK K11.Kq A).mulVec c = ∑ j, c j • a j := by
    intro c; ext i
    simp only [cmK, A, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
      Subfield.coe_subtype, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hlia : LinearIndependent ℂ a := hli.comp e e.injective
  have hinj : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Matrix.mulVecLin_apply] at hc
    have h1 := cmK_mulVec A c
    rw [hc, hAcol] at h1
    have h0 : vK K11.Kq (0 : Fin n → K11.Kq) = 0 := by ext; simp [vK]
    rw [h0] at h1
    have := Fintype.linearIndependent_iff.mp hlia (vK K11.Kq c) h1
    funext j; exact Subtype.ext (this j)
  obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective hinj
  refine ⟨A, LinearMap.toMatrix' g, ?_, ?_⟩
  · have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  · apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, hAcol]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (ha j).1
    · have hle : Submodule.span ℂ b ≤ LinearMap.range (cmK K11.Kq A).mulVecLin := by
        rw [Submodule.span_le]
        intro w hw
        obtain ⟨j, hj⟩ := e.surjective ⟨w, hw⟩
        refine ⟨Pi.single j 1, ?_⟩
        rw [Matrix.mulVecLin_apply, hAcol]
        simp [Pi.single_apply, a, hj]
      intro w hw
      rw [hrat, ← hspan] at hw
      exact hle hw

end LSG.W88.K5d
