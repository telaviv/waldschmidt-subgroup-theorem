import Mathlib

/-!
# Derivations and separable relations over a transcendence basis (characteristic 0)

Field-theoretic input for the existence of smooth points (`LSG.ME.SmoothPoint`).

Let `K` be a field of characteristic `0`, `L/K` a field extension and `b : ι → L` a transcendence
basis of `L/K`.  Write `P = K[X_ι]`, `F' = Frac P`; then `L/F'` is algebraic, hence separable,
hence formally étale, and `P → L` is formally étale.  Consequently

* `Ω[L⁄K]` has the `L`-basis `(d b_i)_i` (`kaehlerBasisOfTranscendenceBasis`), so that for each
  `k : ι` there is a `K`-derivation `D_k : L → L` with `D_k (b_l) = δ_{kl}`
  (`exists_derivation_transcendenceBasis`);
* every `y : L` satisfies a polynomial relation `N(y) = 0` with `N ∈ P[T]` and `N'(y) ≠ 0`
  (`exists_separable_relation`): clear the denominators of the (separable) minimal polynomial of
  `y` over `F'`.

We also record the chain rule `D (f(x)) = Σ_i (∂_i f)(x) · D(x_i)` (`derivation_aeval_sum`).
-/

namespace LSG.ME

open MvPolynomial

noncomputable section

/-- Chain rule for a derivation applied to a polynomial expression. -/
theorem derivation_aeval_sum {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]
    (D : Derivation K L L) (x : σ → L) (f : MvPolynomial σ K) :
    D (aeval x f) = ∑ i, aeval x (pderiv i f) * D (x i) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k h =>
    have e : ∀ i, aeval x (pderiv i (p * X k)) * D (x i) =
        x k * (aeval x (pderiv i p) * D (x i)) + (if k = i then aeval x p * D (x k) else 0) := by
      intro i
      rw [Derivation.leibniz, pderiv_X]
      by_cases hik : k = i
      · subst hik; simp; ring
      · simp [hik, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum, ← h,
      Finset.sum_ite_eq]
    simp [Derivation.leibniz]
    ring

variable {K L ι : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {b : ι → L}

/-- The embedding `Frac K[X_ι] → L` determined by an algebraically independent family. -/
def ratEmb (hb : AlgebraicIndependent K b) : FractionRing (MvPolynomial ι K) →ₐ[K] L :=
  (IntermediateField.adjoin K (Set.range b)).val.comp hb.aevalEquivField.toAlgHom

omit [CharZero K] in
theorem ratEmb_algebraMap (hb : AlgebraicIndependent K b) (f : MvPolynomial ι K) :
    ratEmb hb (algebraMap _ _ f) = aeval b f := by
  simp [ratEmb]

section setup

variable (hb : IsTranscendenceBasis K b)
include hb

local notation "P" => MvPolynomial ι K
local notation "F'" => FractionRing (MvPolynomial ι K)

/-- `F'`-algebra structure on `L` (local). -/
abbrev algF (hb : IsTranscendenceBasis K b) : Algebra F' L := (ratEmb hb.1).toRingHom.toAlgebra

/-- `P`-algebra structure on `L` (local). -/
abbrev algP (_hb : IsTranscendenceBasis K b) : Algebra P L := (aeval b).toRingHom.toAlgebra

omit [CharZero K] in
theorem algebraMap_algP (f : P) :
    @algebraMap P L _ _ (algP hb) f = aeval b f := rfl

omit [CharZero K] in
theorem towers :
    letI := algF hb; letI := algP hb
    IsScalarTower K F' L ∧ IsScalarTower K P L ∧ IsScalarTower P F' L ∧
      Algebra.IsAlgebraic F' L := by
  let _ := algF hb; let _ := algP hb
  refine ⟨.of_algebraMap_eq fun c => ((ratEmb hb.1).commutes c).symm,
    .of_algebraMap_eq fun c => ((aeval b).commutes c).symm,
    .of_algebraMap_eq fun f => (ratEmb_algebraMap hb.1 f).symm, ?_⟩
  -- algebraicity, transported from the intermediate field `K(b)`
  set E := IntermediateField.adjoin K (Set.range b)
  have hE : Algebra.IsAlgebraic E L := hb.isAlgebraic_field
  let _ : Algebra E F' := hb.1.aevalEquivField.symm.toRingHom.toAlgebra
  have : IsScalarTower E F' L := .of_algebraMap_eq fun e => by
    change (e : L) = ratEmb hb.1 (hb.1.aevalEquivField.symm e)
    simp [ratEmb]
  exact Algebra.IsAlgebraic.extendScalars (R := E) hb.1.aevalEquivField.symm.injective

theorem formallyEtale :
    letI := algP hb
    Algebra.FormallyEtale P L := by
  let _ := algF hb; let _ := algP hb
  obtain ⟨_, _, _, _⟩ := towers hb
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have : Algebra.IsSeparable F' L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyEtale F' L := Algebra.FormallyEtale.of_isSeparable F' L
  have : Algebra.FormallyEtale P F' :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  exact Algebra.FormallyEtale.comp P F' L

/-- The `L`-basis `(d b_i)_i` of `Ω[L⁄K]`. -/
def kaehlerBasisOfTranscendenceBasis : Module.Basis ι L Ω[L⁄K] :=
  letI := algP hb
  haveI := (towers hb).2.1
  haveI := formallyEtale hb
  ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange L).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K P L)

theorem kaehlerBasisOfTranscendenceBasis_apply (i : ι) :
    kaehlerBasisOfTranscendenceBasis hb i = KaehlerDifferential.D K L (b i) := by
  let _ := algP hb
  have := (towers hb).2.1
  have := formallyEtale hb
  have h1 : KaehlerDifferential.mvPolynomialBasis K ι i = KaehlerDifferential.D K P (X i) := by
    apply (KaehlerDifferential.mvPolynomialBasis K ι).repr.injective
    rw [Module.Basis.repr_self, KaehlerDifferential.mvPolynomialBasis_repr_D_X]
  have h2 := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K P L (X i)
  rw [LinearEquiv.symm_apply_eq] at h2
  simp only [kaehlerBasisOfTranscendenceBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, h1]
  rw [← h2, algebraMap_algP, aeval_X]

/-- For each `k`, a `K`-derivation `D_k` of `L` with `D_k (b_l) = δ_{kl}`. -/
theorem exists_derivation_transcendenceBasis [DecidableEq ι] (k : ι) :
    ∃ D : Derivation K L L, ∀ l, D (b l) = if l = k then 1 else 0 := by
  refine ⟨((kaehlerBasisOfTranscendenceBasis hb).coord k).compDer (KaehlerDifferential.D K L),
    fun l => ?_⟩
  change ((kaehlerBasisOfTranscendenceBasis hb).coord k) (KaehlerDifferential.D K L (b l)) = _
  rw [← kaehlerBasisOfTranscendenceBasis_apply hb,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- Every element of `L` satisfies a relation `N(y) = 0`, `N ∈ K[X_ι][T]`, with `N'(y) ≠ 0`. -/
theorem exists_separable_relation (y : L) :
    ∃ N : Polynomial (MvPolynomial ι K),
      Polynomial.eval₂ (aeval b).toRingHom y N = 0 ∧
      Polynomial.eval₂ (aeval b).toRingHom y (Polynomial.derivative N) ≠ 0 := by
  let _ := algF hb; let _ := algP hb
  obtain ⟨_, _, _, _⟩ := towers hb
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have : Algebra.IsSeparable F' L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set μ := minpoly F' y
  have hsep : μ.Separable := Algebra.IsSeparable.isSeparable F' y
  have hμ : Polynomial.aeval y μ = 0 := minpoly.aeval F' y
  have hd := hsep.aeval_derivative_ne_zero hμ
  obtain ⟨c, hc, hN⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors P) μ
  set N := IsLocalization.integerNormalization (nonZeroDivisors P) μ
  have hc' : algebraMap P F' c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective P F')).2 (nonZeroDivisors.ne_zero hc)
  have key : ∀ q : Polynomial P,
      Polynomial.eval₂ (aeval b).toRingHom y q = Polynomial.aeval y (q.map (algebraMap P F')) := by
    intro q
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
    rfl
  have hsmul : (c • μ : Polynomial F') = Polynomial.C (algebraMap P F' c) * μ := by
    rw [← IsScalarTower.algebraMap_smul F' c μ, Polynomial.smul_eq_C_mul]
  refine ⟨N, ?_, ?_⟩
  · rw [key, hN, hsmul, map_mul, hμ, mul_zero]
  · rw [key, ← Polynomial.derivative_map, hN, hsmul, Polynomial.derivative_C_mul, map_mul,
      Polynomial.aeval_C]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap F' L).injective).2 hc') hd

end setup

end

end LSG.ME
