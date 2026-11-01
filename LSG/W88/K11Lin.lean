/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Rational linear algebra for the §5d deduction (`Thm11Kappa` from Thm 4.1)

* `castL n : ℚ^n →ₗ[ℚ] ℂ^n` and `cspan M` (the `ℂ`-span of a `ℚ`-subspace `M ⊂ ℚ^n`; this is the
  first factor of `lean_mstar`'s `tangentSub`).
* `exists_frame`: a `ℚ`-subspace `M ⊂ ℚ^n` is the column space of an `n × dim M` matrix `C` with a
  rational left inverse `D` (`D * C = 1`). Consequences: `cspan M` is the column space of `C` over
  `ℂ`, `dim_ℂ cspan M = dim_ℚ M`, and a rational vector in `cspan M` lies in `M`.
* `annQ U` (rational annihilator) and `annC U` (its complex version, same body as
  `LSG.W88.torusLie`): `finrank_annQ` (`dim annQ U + dim U = n`), `annC_eq_cspan`
  (`annC U = cspan (annQ U)`), `annQ_annQ`, `cspan_eq_annC`.
* `span_inf_addSubgroup`: `span_ℚ (A ⊓ B) = span_ℚ A ⊓ span_ℚ B` for additive subgroups.
* `finrank_le_of_le_sup`, `finrank_le_of_le`: two finite-dimensional rank inequalities in a
  possibly infinite-dimensional `ℚ`-space.
-/

open Module Matrix

namespace LSG.W88.K11

/-! ### Casting rational vectors -/

/-- The inclusion `ℚ^n → ℂ^n`. -/
def castL (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℂ) where
  toFun l := fun j => ((l j : ℚ) : ℂ)
  map_add' a b := by ext j; simp
  map_smul' c a := by ext j; simp [Rat.smul_def]

@[simp] lemma castL_apply {n : ℕ} (l : Fin n → ℚ) (j : Fin n) : castL n l j = ((l j : ℚ) : ℂ) := rfl

lemma castL_injective (n : ℕ) : Function.Injective (castL n) := by
  intro a b h; ext j; have := congrFun h j; simpa using this

/-- The `ℂ`-span of a `ℚ`-subspace of `ℚ^n` (same body as the first factor of `tangentSub`). -/
noncomputable def cspan {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun l : Fin n → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (M : Set (Fin n → ℚ)))

lemma cspan_eq {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    cspan M = Submodule.span ℂ (castL n '' (M : Set (Fin n → ℚ))) := rfl

lemma castL_mem_cspan {n : ℕ} {M : Submodule ℚ (Fin n → ℚ)} {q : Fin n → ℚ} (hq : q ∈ M) :
    castL n q ∈ cspan M := Submodule.subset_span ⟨q, hq, rfl⟩

lemma cspan_span {n : ℕ} (S : Set (Fin n → ℚ)) :
    cspan (Submodule.span ℚ S) = Submodule.span ℂ (castL n '' S) := by
  rw [cspan_eq]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (Set.image_mono
    Submodule.subset_span))
  have h1 : (castL n '' (Submodule.span ℚ S : Set (Fin n → ℚ))) =
      ((Submodule.span ℚ S).map (castL n) : Set (Fin n → ℂ)) := rfl
  rw [h1, Submodule.map_span]
  exact Submodule.span_le_restrictScalars ℚ ℂ _

lemma cspan_bot {n : ℕ} : cspan (⊥ : Submodule ℚ (Fin n → ℚ)) = ⊥ := by
  rw [← Submodule.span_empty, cspan_span]; simp

/-! ### Matrices -/

/-- Entrywise cast of a rational matrix. -/
noncomputable def cm {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) : Matrix (Fin a) (Fin b) ℂ :=
  C.map (Rat.castHom ℂ)

lemma cm_mulVec_castL {a b : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) (q : Fin b → ℚ) :
    (cm C).mulVec (castL b q) = castL a (C.mulVec q) := by
  ext i; simp [cm, Matrix.mulVec, dotProduct]

lemma cm_mul {a b c : ℕ} (C : Matrix (Fin a) (Fin b) ℚ) (D : Matrix (Fin b) (Fin c) ℚ) :
    cm (C * D) = cm C * cm D :=
  Matrix.map_mul (f := Rat.castHom ℂ)

lemma cm_one {a : ℕ} : cm (1 : Matrix (Fin a) (Fin a) ℚ) = 1 := by
  simp [cm]

lemma mulVec_left_inv {a b : ℕ} {C : Matrix (Fin a) (Fin b) ℚ} {D : Matrix (Fin b) (Fin a) ℚ}
    (hDC : D * C = 1) (x : Fin b → ℂ) : (cm D).mulVec ((cm C).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← cm_mul, hDC, cm_one, Matrix.one_mulVec]

lemma cm_injective {a b : ℕ} {C : Matrix (Fin a) (Fin b) ℚ} {D : Matrix (Fin b) (Fin a) ℚ}
    (hDC : D * C = 1) : Function.Injective (cm C).mulVec := by
  intro x y h
  rw [← mulVec_left_inv hDC x, ← mulVec_left_inv hDC y, h]

lemma ratMulVec_injective {a b : ℕ} {C : Matrix (Fin a) (Fin b) ℚ} {D : Matrix (Fin b) (Fin a) ℚ}
    (hDC : D * C = 1) : Function.Injective C.mulVec := by
  intro x y h
  have := congrArg D.mulVec h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec,
    Matrix.one_mulVec] at this

lemma exists_frame {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    ∃ (C : Matrix (Fin n) (Fin (finrank ℚ M)) ℚ) (D : Matrix (Fin (finrank ℚ M)) (Fin n) ℚ),
      D * C = 1 ∧ LinearMap.range C.mulVecLin = M := by
  classical
  set r := finrank ℚ M
  let bM := Module.finBasis ℚ M
  let C : Matrix (Fin n) (Fin r) ℚ := Matrix.of fun j i => (bM i : Fin n → ℚ) j
  have hCv : ∀ c, C.mulVec c = ∑ i, c i • (bM i : Fin n → ℚ) := by
    intro c; ext j; simp [C, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hrange : LinearMap.range C.mulVecLin = M := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, hCv]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bM i).2
    · intro m hm
      refine ⟨fun i => bM.repr ⟨m, hm⟩ i, ?_⟩
      rw [Matrix.mulVecLin_apply, hCv]
      have := bM.sum_repr ⟨m, hm⟩
      have h2 := congrArg Subtype.val this
      rw [Submodule.coe_sum] at h2
      simpa only [Submodule.coe_smul] using h2
  have hinj : LinearMap.ker C.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Matrix.mulVecLin_apply, hCv] at hc
    have hli : LinearIndependent ℚ (fun i => (bM i : Fin n → ℚ)) :=
      bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    exact funext (Fintype.linearIndependent_iff.mp hli c hc)
  obtain ⟨g, hg⟩ := C.mulVecLin.exists_leftInverse_of_injective hinj
  refine ⟨C, LinearMap.toMatrix' g, ?_, hrange⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin'] at this

/-- The column space of `cm C` is `cspan` of the column space of `C`. -/
lemma cspan_eq_range {n r : ℕ} {M : Submodule ℚ (Fin n → ℚ)} {C : Matrix (Fin n) (Fin r) ℚ}
    (hC : LinearMap.range C.mulVecLin = M) : cspan M = LinearMap.range (cm C).mulVecLin := by
  apply le_antisymm
  · rw [cspan_eq, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [← hC] at hm
    obtain ⟨c, rfl⟩ := hm
    exact ⟨castL r c, by rw [Matrix.mulVecLin_apply, cm_mulVec_castL]; rfl⟩
  · rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : (cm C).col i = castL n (C.mulVec (Pi.single i 1)) := by
      ext j; simp [cm, Matrix.col]
    rw [this]
    exact castL_mem_cspan (hC ▸ ⟨_, rfl⟩)

lemma finrank_cspan {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) :
    finrank ℂ (cspan M) = finrank ℚ M := by
  obtain ⟨C, D, hDC, hC⟩ := exists_frame M
  rw [cspan_eq_range hC, LinearMap.finrank_range_of_inj (cm_injective hDC)]
  simp

lemma mem_of_castL_mem_cspan {n : ℕ} {M : Submodule ℚ (Fin n → ℚ)} {q : Fin n → ℚ}
    (hq : castL n q ∈ cspan M) : q ∈ M := by
  obtain ⟨C, D, hDC, hC⟩ := exists_frame M
  rw [cspan_eq_range hC] at hq
  obtain ⟨x, hx⟩ := hq
  rw [Matrix.mulVecLin_apply] at hx
  have hx' : x = castL _ (D.mulVec q) := by
    rw [← cm_mulVec_castL, ← hx, mulVec_left_inv hDC]
  rw [hx', cm_mulVec_castL] at hx
  rw [← hC, ← castL_injective n hx]
  exact ⟨_, rfl⟩

lemma cspan_top {n : ℕ} : cspan (⊤ : Submodule ℚ (Fin n → ℚ)) = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [finrank_cspan]; simp)

/-! ### Rational annihilators -/

/-- The rational annihilator `{q | ∀ φ ∈ U, Σ φⱼ qⱼ = 0}`. -/
def annQ {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) : Submodule ℚ (Fin n → ℚ) where
  carrier := {q | ∀ φ ∈ U, ∑ j, φ j * q j = 0}
  add_mem' {a b} ha hb φ hφ := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := by simp
  smul_mem' c v hv φ hφ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, φ j * (c * v j)) = c * ∑ j, φ j * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hv φ hφ, mul_zero]

/-- The complex annihilator (same body as `LSG.W88.torusLie`). -/
def annC {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ φ ∈ U, ∑ j, (φ j : ℂ) * v j = 0}
  add_mem' {a b} ha hb φ hφ := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' φ _ := by simp
  smul_mem' c v hv φ hφ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ j, (φ j : ℂ) * (c * v j)) = c * ∑ j, (φ j : ℂ) * v j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hv φ hφ, mul_zero]

/-- With `U = range C`, `annQ U = ker Cᵀ` and `annC U = ker (cm C)ᵀ`. -/
lemma annQ_eq_ker {n r : ℕ} {U : Submodule ℚ (Fin n → ℚ)} {C : Matrix (Fin n) (Fin r) ℚ}
    (hC : LinearMap.range C.mulVecLin = U) : annQ U = LinearMap.ker Cᵀ.mulVecLin := by
  ext q
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hq; ext i
    have := hq (C.mulVec (Pi.single i 1)) (hC ▸ ⟨_, rfl⟩)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply] using this
  · intro hq φ hφ
    rw [← hC] at hφ
    obtain ⟨c, rfl⟩ := hφ
    have : ∑ j, (C.mulVec c) j * q j = ∑ i, c i * (Cᵀ.mulVec q) i := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
        fun _ _ => by ring
    simp only [Matrix.mulVecLin_apply]
    rw [this, hq]; simp

lemma annC_eq_ker {n r : ℕ} {U : Submodule ℚ (Fin n → ℚ)} {C : Matrix (Fin n) (Fin r) ℚ}
    (hC : LinearMap.range C.mulVecLin = U) : annC U = LinearMap.ker (cm C)ᵀ.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv; ext i
    have := hv (C.mulVec (Pi.single i 1)) (hC ▸ ⟨_, rfl⟩)
    simpa [cm, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply] using this
  · intro hv φ hφ
    rw [← hC] at hφ
    obtain ⟨c, rfl⟩ := hφ
    have : ∑ j, ((C.mulVec c) j : ℂ) * v j = ∑ i, (c i : ℂ) * ((cm C)ᵀ.mulVec v) i := by
      simp only [cm, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
        Finset.mul_sum, Finset.sum_mul, Rat.cast_sum, Rat.cast_mul, Rat.coe_castHom]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
        fun _ _ => by ring
    simp only [Matrix.mulVecLin_apply]
    rw [this, hv]; simp

lemma finrank_annQ {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) :
    finrank ℚ (annQ U) + finrank ℚ U = n := by
  obtain ⟨C, D, hDC, hC⟩ := exists_frame U
  rw [annQ_eq_ker hC]
  have hsurj : LinearMap.range Cᵀ.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x; refine ⟨Dᵀ.mulVec x, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hDC,
      Matrix.transpose_one, Matrix.one_mulVec]
  have := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [hsurj, finrank_top] at this
  simp only [finrank_fin_fun] at this
  omega

lemma finrank_annC {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) :
    finrank ℂ (annC U) + finrank ℚ U = n := by
  obtain ⟨C, D, hDC, hC⟩ := exists_frame U
  rw [annC_eq_ker hC]
  have hsurj : LinearMap.range (cm C)ᵀ.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x; refine ⟨(cm D)ᵀ.mulVec x, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← cm_mul, hDC,
      cm_one, Matrix.transpose_one, Matrix.one_mulVec]
  have := LinearMap.finrank_range_add_finrank_ker (cm C)ᵀ.mulVecLin
  rw [hsurj, finrank_top] at this
  simp only [finrank_fin_fun] at this
  omega

lemma cspan_annQ_le {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) : cspan (annQ U) ≤ annC U := by
  rw [cspan_eq, Submodule.span_le]
  rintro _ ⟨q, hq, rfl⟩ φ hφ
  have := hq φ hφ
  have h2 : ((∑ j, φ j * q j : ℚ) : ℂ) = 0 := by rw [this]; simp
  simpa using h2

lemma annC_eq_cspan {n : ℕ} (U : Submodule ℚ (Fin n → ℚ)) : annC U = cspan (annQ U) := by
  refine (Submodule.eq_of_le_of_finrank_eq (cspan_annQ_le U) ?_).symm
  have h1 := finrank_annQ U
  have h2 := finrank_annC U
  rw [finrank_cspan]; omega

lemma annQ_annQ {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) : annQ (annQ M) = M := by
  refine (Submodule.eq_of_le_of_finrank_eq (show M ≤ annQ (annQ M) from fun q hq φ hφ => ?_)
    ?_).symm
  · rw [← hφ q hq]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · have h1 := finrank_annQ M
    have h2 := finrank_annQ (annQ M)
    omega

/-- `cspan M` is cut out by the rational linear forms of `annQ M`. -/
lemma cspan_eq_annC {n : ℕ} (M : Submodule ℚ (Fin n → ℚ)) : cspan M = annC (annQ M) := by
  rw [annC_eq_cspan, annQ_annQ]

/-! ### `ℚ`-spans of additive subgroups -/

section SpanInf

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

lemma exists_nsmul_mem_of_mem_span (A : AddSubgroup E) {x : E}
    (hx : x ∈ Submodule.span ℚ (A : Set E)) : ∃ n : ℕ, 0 < n ∧ n • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e1 : (n * m) • x = m • (n • x) := by rw [smul_smul, mul_comm]
    have e2 : (n * m) • y = n • (m • y) := by rw [smul_smul]
    rw [smul_add, e1, e2]
    exact A.add_mem (A.nsmul_mem hnx m) (A.nsmul_mem hmy n)
  | smul q x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, ?_⟩
    have : (q.den * n) • (q • x) = q.num • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ n, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_comm (q.den : ℚ) n, mul_assoc, Rat.den_mul_eq_num]; ring
    rw [this]; exact A.zsmul_mem hnx _

lemma mem_span_of_nsmul_mem (A : AddSubgroup E) {x : E} {n : ℕ} (hn : 0 < n) (h : n • x ∈ A) :
    x ∈ Submodule.span ℚ (A : Set E) := by
  have : x = (n : ℚ)⁻¹ • (n • x) := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
      one_smul]
  rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span h)

lemma span_inf_addSubgroup (A B : AddSubgroup E) :
    Submodule.span ℚ ((A ⊓ B : AddSubgroup E) : Set E) =
      Submodule.span ℚ (A : Set E) ⊓ Submodule.span ℚ (B : Set E) := by
  apply le_antisymm
  · exact le_inf (Submodule.span_mono inf_le_left) (Submodule.span_mono inf_le_right)
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨n, hn, hnx⟩ := exists_nsmul_mem_of_mem_span A hxA
    obtain ⟨m, hm, hmx⟩ := exists_nsmul_mem_of_mem_span B hxB
    have e1 : (n * m) • x = m • (n • x) := by rw [smul_smul, mul_comm]
    have e2 : (n * m) • x = n • (m • x) := by rw [smul_smul]
    refine mem_span_of_nsmul_mem _ (Nat.mul_pos hn hm) ⟨?_, ?_⟩
    · change (n * m) • x ∈ A; rw [e1]; exact A.nsmul_mem hnx m
    · change (n * m) • x ∈ B; rw [e2]; exact B.nsmul_mem hmx n

lemma span_sup_addSubgroup (A B : AddSubgroup E) :
    Submodule.span ℚ ((A ⊔ B : AddSubgroup E) : Set E) =
      Submodule.span ℚ (A : Set E) ⊔ Submodule.span ℚ (B : Set E) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    have : A ⊔ B ≤ (Submodule.span ℚ (A : Set E) ⊔ Submodule.span ℚ (B : Set E)).toAddSubgroup :=
      sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span hx))
        (fun x hx => Submodule.mem_sup_right (Submodule.subset_span hx))
    exact this
  · exact sup_le (Submodule.span_mono (SetLike.coe_mono le_sup_left))
      (Submodule.span_mono (SetLike.coe_mono le_sup_right))

lemma span_submodule_coe {F : Type*} [AddCommGroup F] [Module ℂ F] [Module ℚ F]
    [IsScalarTower ℚ ℂ F] (S : Submodule ℂ F) :
    Submodule.span ℚ ((S.toAddSubgroup : AddSubgroup F) : Set F) = S.restrictScalars ℚ := by
  rw [show ((S.toAddSubgroup : AddSubgroup F) : Set F) =
    ((S.restrictScalars ℚ : Submodule ℚ F) : Set F) from rfl]
  exact Submodule.span_eq _

/-! ### Finite-dimensional rank inequalities -/

/-- If `Z ≤ A ⊔ B` with `Z`, `B` finite-dimensional, then
`dim Z + dim (B ⊓ A) ≤ dim B + dim (Z ⊓ A)`. -/
lemma finrank_le_of_le_sup (Z A B : Submodule ℚ E) [FiniteDimensional ℚ Z] [FiniteDimensional ℚ B]
    (h : Z ≤ A ⊔ B) :
    finrank ℚ Z + finrank ℚ ↥(B ⊓ A) ≤ finrank ℚ B + finrank ℚ ↥(Z ⊓ A) := by
  set A' := A ⊓ (Z ⊔ B)
  have hZA' : Z ≤ A' ⊔ B := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h hz)
    refine Submodule.mem_sup.mpr ⟨a, ⟨ha, ?_⟩, b, hb, rfl⟩
    have : a = (a + b) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hb)
  have : FiniteDimensional ℚ ↥(Z ⊔ B) := Submodule.finiteDimensional_sup _ _
  have : FiniteDimensional ℚ A' := Submodule.finiteDimensional_of_le inf_le_right
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq Z A'
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq B A'
  have hZinf : Z ⊓ A' = Z ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans le_sup_left))
  have hBinf : B ⊓ A' = B ⊓ A := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans le_sup_right))
  have hle : finrank ℚ ↥(Z ⊔ A') ≤ finrank ℚ ↥(B ⊔ A') := by
    have : FiniteDimensional ℚ ↥(B ⊔ A') := Submodule.finiteDimensional_sup _ _
    exact Submodule.finrank_mono (sup_le (hZA'.trans (sup_comm A' B).le) le_sup_right)
  rw [hZinf] at e1; rw [hBinf] at e2
  omega

/-- If `A' ≤ A` (finite-dimensional), then `dim A' + dim (A ⊓ B) ≤ dim A + dim (A' ⊓ B)`. -/
lemma finrank_le_of_le (A' A B : Submodule ℚ E) [FiniteDimensional ℚ A] (h : A' ≤ A) :
    finrank ℚ A' + finrank ℚ ↥(A ⊓ B) ≤ finrank ℚ A + finrank ℚ ↥(A' ⊓ B) := by
  have : FiniteDimensional ℚ A' := Submodule.finiteDimensional_of_le h
  have : FiniteDimensional ℚ ↥(A ⊓ B) := Submodule.finiteDimensional_of_le inf_le_left
  have e := Submodule.finrank_sup_add_finrank_inf_eq A' (A ⊓ B)
  have h1 : A' ⊓ (A ⊓ B) = A' ⊓ B := by
    rw [← inf_assoc, inf_eq_left.mpr h]
  have h2 : finrank ℚ ↥(A' ⊔ A ⊓ B) ≤ finrank ℚ A :=
    Submodule.finrank_mono (sup_le h inf_le_left)
  rw [h1] at e
  omega

end SpanInf

end LSG.W88.K11
