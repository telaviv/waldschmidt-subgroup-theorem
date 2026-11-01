import LSG.ME.SmoothDeriv

/-!
# Smooth points of irreducible affine varieties in characteristic 0

Let `K` be a field of characteristic `0`, `σ` a finite type and `p ⊆ K[X_σ]` a prime ideal, with
`e = trdeg_K (K[X_σ]/p)`.  The Zariski tangent space of `Z(p)` at `a ∈ K^σ` is
`T_a = {v | ∀ f ∈ p, Σ_i v_i (∂_i f)(a) = 0}` (`tangentSpace`).  We prove:

* `trdeg_le_finrank_tangentSpace`: `e ≤ dim T_a` for every `a ∈ Z(p)`;
* `exists_smooth_point` (`K` algebraically closed): for every `h ∉ p` there is `a ∈ Z(p)` with
  `h(a) ≠ 0` and `dim T_a = e` (so smooth points are Zariski dense in `Z(p)`).

Proof.  Let `x ∈ L^σ` be the generic point (`L = Frac(K[X]/p)`), and choose coordinates
`g : ι ↪ σ` with `x ∘ g` a transcendence basis of `L/K` (`exists_coord_transcendenceBasis`).

* Lower bound: the derivations `D_k` of `L` with `D_k (x_{g l}) = δ_{kl}`
  (`exists_derivation_transcendenceBasis`) give `e` vectors `(D_k x_i)_i` orthogonal to all
  gradients `∇f(x)`, `f ∈ p`.  If `∇f_1(a), …, ∇f_m(a)` are independent, a polynomial `m × m`
  determinant witnesses that `∇f_1(x), …, ∇f_m(x)` are independent over `L`, so `m + e ≤ |σ|`.
* Upper bound: for `j ∉ range g` there is `G_j ∈ p` in the variables `x_{g(ι)}, x_j` with
  `∂_j G_j ∉ p` (`exists_separable_relation`).  By the Nullstellensatz some `a ∈ Z(p)` has
  `h(a) ∏_j (∂_j G_j)(a) ≠ 0`; there `v ↦ v ∘ g` is injective on `T_a`.
-/

namespace LSG.ME

open MvPolynomial

noncomputable section

universe u v

variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

/-- The Zariski tangent space at `a` of the zero set of an ideal `p ⊆ K[X_σ]`. -/
def tangentSpace (p : Ideal (MvPolynomial σ K)) (a : σ → K) : Submodule K (σ → K) where
  carrier := {v | ∀ f ∈ p, ∑ i, v i * eval a (pderiv i f) = 0}
  add_mem' {v w} hv hw f hf := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hv f hf,
      hw f hf, add_zero]
  zero_mem' f _ := by simp
  smul_mem' c v hv f hf := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
      hv f hf, mul_zero]

theorem mem_tangentSpace {p : Ideal (MvPolynomial σ K)} {a v : σ → K} :
    v ∈ tangentSpace p a ↔ ∀ f ∈ p, ∑ i, v i * eval a (pderiv i f) = 0 := Iff.rfl

/-! ### Auxiliary polynomial lemmas -/

omit [Fintype σ] in
theorem pderiv_rename_of_notMem_range {ι : Type*} (g : ι → σ) {i : σ} (hi : i ∉ Set.range g)
    (c : MvPolynomial ι K) : pderiv i (rename g c) = 0 := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k h =>
    rw [map_mul, rename_X, Derivation.leibniz, h, pderiv_X_of_ne (fun e => hi ⟨k, e⟩)]
    simp

omit [Fintype σ] in
theorem pderiv_eval₂_X {ι : Type*} (ρ : MvPolynomial ι K →+* MvPolynomial σ K) (i j : σ)
    (hρ : ∀ c, pderiv i (ρ c) = 0) (N : Polynomial (MvPolynomial ι K)) :
    pderiv i (N.eval₂ ρ (X j)) = (Polynomial.derivative N).eval₂ ρ (X j) * pderiv i (X j) := by
  induction N using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq, add_mul]
  | monomial n c =>
    rw [Polynomial.eval₂_monomial, Polynomial.derivative_monomial, Polynomial.eval₂_monomial,
      Derivation.leibniz, hρ, smul_zero, add_zero, Derivation.leibniz_pow]
    simp only [map_mul, map_natCast, smul_eq_mul, nsmul_eq_mul]
    ring

/-! ### The generic point -/

section generic

variable (p : Ideal (MvPolynomial σ K))

/-- The function field `Frac(K[X_σ]/p)`. -/
abbrev GenField := FractionRing (MvPolynomial σ K ⧸ p)

/-- The generic point of `Z(p)`, with coordinates in the function field. -/
def genPt : σ → GenField p :=
  fun i => algebraMap (MvPolynomial σ K ⧸ p) (GenField p) (Ideal.Quotient.mk p (X i))

omit [Fintype σ] in
theorem aeval_genPt (f : MvPolynomial σ K) :
    aeval (genPt p) f = algebraMap _ (GenField p) (Ideal.Quotient.mk p f) := by
  have : (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p) (GenField p)).comp
      (Ideal.Quotient.mkₐ K p) = aeval (genPt p) := by
    ext i
    simp [genPt]
  rw [← this]
  rfl

variable [p.IsPrime]

omit [Fintype σ] [p.IsPrime] in
theorem aeval_genPt_eq_zero_iff {f : MvPolynomial σ K} : aeval (genPt p) f = 0 ↔ f ∈ p := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype σ] in
/-- A transcendence basis of the function field among the coordinate functions. -/
theorem exists_coord_transcendenceBasis [Finite σ] :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (g : ι → σ), Function.Injective g ∧
      IsTranscendenceBasis K (genPt p ∘ g) ∧
      (Fintype.card ι : Cardinal) = Algebra.trdeg K (MvPolynomial σ K ⧸ p) := by
  set A := MvPolynomial σ K ⧸ p
  let xA : σ → A := fun i => Ideal.Quotient.mk p (X i)
  have : FaithfulSMul K A :=
    (faithfulSMul_iff_algebraMap_injective K A).mpr (algebraMap K A).injective
  have hmk : aeval xA = Ideal.Quotient.mkₐ K p := by
    ext i
    rw [aeval_X]
    rfl
  have htop : ∀ a : A, a ∈ Algebra.adjoin K (Set.range xA) := by
    intro a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨f, by rw [hmk]; rfl⟩
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xA)) A :=
    ⟨fun a => by
      simpa using isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range xA)) (A := A)
        ⟨a, htop a⟩⟩
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range xA)
  have hpre : ∀ a : t, ∃ i, xA i = a := fun a => hts a.2
  choose g hg using hpre
  have ginj : Function.Injective g := fun a b h => Subtype.ext (by rw [← hg a, ← hg b, h])
  have : Finite t := Finite.of_injective g ginj
  let _ : Fintype t := Fintype.ofFinite t
  have : Algebra.IsAlgebraic A (GenField p) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have hL := ht.algebraMap_comp (A := GenField p)
  refine ⟨t, inferInstance, g, ginj, ?_, ?_⟩
  · convert hL using 1
    funext a
    simp only [Function.comp_apply, genPt]
    rw [← hg a]
  · rw [← Cardinal.mk_fintype]
    exact ht.cardinalMk_eq_trdeg

/-! ### Lower bound `e ≤ dim T_a` -/

theorem trdeg_le_finrank_tangentSpace [CharZero K] (a : σ → K) (ha : a ∈ zeroLocus K p) :
    (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat ≤ Module.finrank K (tangentSpace p a) := by
  classical
  obtain ⟨ι, _, g, -, hb, hcard⟩ := exists_coord_transcendenceBasis p
  rw [← hcard, Cardinal.toNat_natCast]
  set L := GenField p
  set x := genPt p
  have ha' : ∀ f ∈ p, eval a f = 0 := fun f hf => by simpa using ha f hf
  -- derivations of `L` dual to the transcendence basis
  have hD := fun k => exists_derivation_transcendenceBasis hb k
  choose D hD using hD
  have hchain : ∀ f ∈ p, ∀ k, ∑ i, aeval x (pderiv i f) * D k (x i) = 0 := by
    intro f hf k
    rw [← derivation_aeval_sum, (aeval_genPt_eq_zero_iff p).2 hf, map_zero]
  -- a basis of the span of the gradients at `a`
  let grad : MvPolynomial σ K → σ → K := fun f i => eval a (pderiv i f)
  obtain ⟨B, hBS, hspan, hli⟩ := exists_linearIndependent K (grad '' (p : Set _))
  have : Finite B := hli.finite
  let _ : Fintype B := Fintype.ofFinite B
  have hf : ∀ u : B, ∃ f ∈ p, grad f = u := fun u => hBS u.2
  choose f hfp hfu using hf
  let M : Matrix B σ K := Matrix.of fun u i => (u : σ → K) i
  -- the tangent space is the kernel of `M`
  have hT : tangentSpace p a = LinearMap.ker M.mulVecLin := by
    ext v
    rw [mem_tangentSpace, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro hv
      funext u
      have := hv (f u) (hfp u)
      simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
      rw [← hfu u]
      simpa [grad, mul_comm] using this
    · intro hv g' hg'
      let ℓ : (σ → K) →ₗ[K] K :=
        { toFun := fun w => ∑ i, v i * w i
          map_add' := fun w w' => by simp [mul_add, Finset.sum_add_distrib]
          map_smul' := fun c w => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring }
      have hB : (B : Set (σ → K)) ⊆ LinearMap.ker ℓ := by
        intro u hu
        have := congrFun hv ⟨u, hu⟩
        simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Pi.zero_apply] at this
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, ℓ]
        rw [← this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      have hmem : grad g' ∈ Submodule.span K (B : Set (σ → K)) :=
        hspan ▸ Submodule.subset_span ⟨g', hg', rfl⟩
      exact (Submodule.span_le.2 hB) hmem
  -- rank of `M`
  have hrankM : M.rank = Fintype.card B := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact finrank_span_eq_card hli
  have hsurj : Function.Surjective M.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, ← hrankM]
    rfl
  have hv : ∀ u' : B, ∃ w : σ → K, Matrix.mulVec M w = Pi.single u' 1 := fun u' => hsurj _
  choose vv hvv using hv
  let V : Matrix σ B K := Matrix.of fun i u' => vv u' i
  have hMV : ∀ u u' : B, ∑ i, (u : σ → K) i * V i u' = if u = u' then 1 else 0 := by
    intro u u'
    have := congrFun (hvv u') u
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply] at this
    change ∑ i, (u : σ → K) i * vv u' i = _
    rw [this, Pi.single_apply]
  -- the polynomial determinant
  let Np : Matrix B B (MvPolynomial σ K) :=
    Matrix.of fun u u' => ∑ i, pderiv i (f u) * C (V i u')
  have hevalN : (eval a).mapMatrix Np = 1 := by
    ext u u'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Np, Matrix.of_apply, map_sum,
      map_mul, eval_C, Matrix.one_apply]
    rw [← hMV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hfu u]
  have hΔp : Np.det ∉ p := by
    intro h
    have h1 := ha' _ h
    rw [RingHom.map_det, hevalN, Matrix.det_one] at h1
    exact one_ne_zero h1
  have hΔL : aeval x Np.det ≠ 0 := fun h => hΔp ((aeval_genPt_eq_zero_iff p).1 h)
  -- over the function field
  let ML : Matrix B σ L := Matrix.of fun u i => aeval x (pderiv i (f u))
  let VL : Matrix σ B L := V.map (algebraMap K L)
  have hNL : (aeval x).toRingHom.mapMatrix Np = ML * VL := by
    ext u u'
    simp [Np, ML, VL, Matrix.mul_apply]
    rfl
  have hdet : (ML * VL).det ≠ 0 := by
    rw [← hNL, ← RingHom.map_det]
    exact hΔL
  have hrankNL : (ML * VL).rank = Fintype.card B :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hrankML : Fintype.card B ≤ ML.rank := hrankNL ▸ Matrix.rank_mul_le_left _ _
  let W : Matrix ι σ L := Matrix.of fun k i => D k (x i)
  have hMW : ML * W.transpose = 0 := by
    ext u k
    simpa [Matrix.mul_apply, ML, W] using hchain _ (hfp u) k
  let Q : Matrix σ ι L := Matrix.of fun i l => if i = g l then 1 else 0
  have hWQ : W * Q = 1 := by
    ext k l
    simp only [Matrix.mul_apply, W, Q, Matrix.of_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
    have := hD k l
    simp only [Function.comp_apply] at this
    rw [this]
    exact if_congr eq_comm rfl rfl
  have hrankW : Fintype.card ι ≤ W.transpose.rank := by
    rw [Matrix.rank_transpose]
    calc Fintype.card ι = (1 : Matrix ι ι L).rank := Matrix.rank_one.symm
      _ = (W * Q).rank := by rw [hWQ]
      _ ≤ W.rank := Matrix.rank_mul_le_left _ _
  have hle : LinearMap.range W.transpose.mulVecLin ≤ LinearMap.ker ML.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hMW, Matrix.zero_mulVec]
  have h1 : W.transpose.rank ≤ Module.finrank L (LinearMap.ker ML.mulVecLin) :=
    Submodule.finrank_mono hle
  have hrnL : ML.rank + Module.finrank L (LinearMap.ker ML.mulVecLin) = Fintype.card σ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := L)]
    exact LinearMap.finrank_range_add_finrank_ker _
  have hrnK : M.rank + Module.finrank K (LinearMap.ker M.mulVecLin) = Fintype.card σ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K)]
    exact LinearMap.finrank_range_add_finrank_ker _
  rw [hT]
  omega

/-! ### Existence of smooth points -/

/-- **Smooth points are dense.** For every `h ∉ p` there is a point `a ∈ Z(p)` with `h(a) ≠ 0` at
which the Zariski tangent space has dimension `trdeg_K (K[X]/p)`. -/
theorem exists_smooth_point [IsAlgClosed K] [CharZero K] (h : MvPolynomial σ K) (hh : h ∉ p) :
    ∃ a ∈ zeroLocus K p, eval a h ≠ 0 ∧
      Module.finrank K (tangentSpace p a) = (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat := by
  classical
  obtain ⟨ι, _, g, -, hb, hcard⟩ := exists_coord_transcendenceBasis p
  have he : (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat = Fintype.card ι := by
    rw [← hcard, Cardinal.toNat_natCast]
  set x := genPt p
  have hN := fun j => exists_separable_relation hb (x j)
  choose N hN0 hN1 using hN
  let ρ : MvPolynomial ι K →+* MvPolynomial σ K := (rename g).toRingHom
  let G : σ → MvPolynomial σ K := fun j => (N j).eval₂ ρ (X j)
  have hc : (aeval x).toRingHom.comp ρ = (aeval (x ∘ g)).toRingHom := by
    ext c
    · simp [ρ]
    · simp [ρ]
  have hev : ∀ (j : σ) (q : Polynomial (MvPolynomial ι K)),
      aeval x (q.eval₂ ρ (X j)) = q.eval₂ (aeval (x ∘ g)).toRingHom (x j) := by
    intro j q
    have := Polynomial.hom_eval₂ q ρ (aeval x).toRingHom (X j)
    rw [hc] at this
    simpa using this
  have hGp : ∀ j, G j ∈ p := fun j =>
    (aeval_genPt_eq_zero_iff p).1 (by rw [hev]; exact hN0 j)
  have hGi : ∀ j i, i ∉ Set.range g → i ≠ j → pderiv i (G j) = 0 := by
    intro j i hi hij
    rw [pderiv_eval₂_X ρ i j (pderiv_rename_of_notMem_range g hi), pderiv_X_of_ne (Ne.symm hij),
      mul_zero]
  have hGj : ∀ j, j ∉ Set.range g → aeval x (pderiv j (G j)) ≠ 0 := by
    intro j hj
    rw [pderiv_eval₂_X ρ j j (pderiv_rename_of_notMem_range g hj), pderiv_X_self, mul_one, hev]
    exact hN1 j
  let S := Finset.univ.filter (fun j => j ∉ Set.range g)
  let Δ := h * ∏ j ∈ S, pderiv j (G j)
  have hΔ : Δ ∉ p := by
    intro hΔ
    have := (aeval_genPt_eq_zero_iff p).2 hΔ
    rw [map_mul, map_prod] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hh ((aeval_genPt_eq_zero_iff p).1 h1)
    · obtain ⟨j, hjS, hj⟩ := Finset.prod_eq_zero_iff.1 h1
      exact hGj j (Finset.mem_filter.1 hjS).2 hj
  -- Nullstellensatz
  have hrad : vanishingIdeal K (zeroLocus K p) = p := by
    rw [vanishingIdeal_zeroLocus_eq_radical, (inferInstance : p.IsPrime).radical]
  have hΔ' : Δ ∉ vanishingIdeal K (zeroLocus K p) := by rw [hrad]; exact hΔ
  rw [mem_vanishingIdeal_iff, not_forall₂] at hΔ'
  obtain ⟨a, ha, haΔ⟩ := hΔ'
  have haΔ' : eval a Δ ≠ 0 := by simpa using haΔ
  have hah : eval a h ≠ 0 := fun h0 => haΔ' (by simp [Δ, h0])
  have haG : ∀ j ∈ S, eval a (pderiv j (G j)) ≠ 0 := by
    intro j hj h0
    apply haΔ'
    simp only [Δ, map_mul, map_prod]
    rw [Finset.prod_eq_zero hj h0, mul_zero]
  refine ⟨a, ha, hah, le_antisymm ?_ (trdeg_le_finrank_tangentSpace p a ha)⟩
  rw [he]
  -- restriction to the coordinates `g` is injective on `T_a`
  let res : tangentSpace p a →ₗ[K] (ι → K) :=
    (LinearMap.funLeft K K g).comp (tangentSpace p a).subtype
  have hinj : Function.Injective res := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ l, (v : σ → K) (g l) = 0 := fun l => by
      simpa [res, LinearMap.funLeft_apply] using congrFun hv l
    ext j
    by_cases hj : j ∈ Set.range g
    · obtain ⟨l, rfl⟩ := hj
      simpa using hv' l
    · have hT := v.2 (G j) (hGp j)
      rw [Finset.sum_eq_single j] at hT
      · have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
        simpa using (mul_eq_zero.1 hT).resolve_right (haG j hjS)
      · intro i _ hij
        by_cases hi : i ∈ Set.range g
        · obtain ⟨l, rfl⟩ := hi
          simp [hv' l]
        · rw [hGi j i hi hij]
          simp
      · simp
  calc Module.finrank K (tangentSpace p a) ≤ Module.finrank K (ι → K) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card K

/-- **Existence of a smooth point** on an irreducible affine variety in characteristic `0`. -/
theorem exists_smooth_point' [IsAlgClosed K] [CharZero K] :
    ∃ a ∈ zeroLocus K p,
      Module.finrank K (tangentSpace p a) = (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat := by
  have h1 : (1 : MvPolynomial σ K) ∉ p := fun h1 =>
    (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨a, ha, -, h⟩ := exists_smooth_point p 1 h1
  exact ⟨a, ha, h⟩

end generic

end

end LSG.ME
