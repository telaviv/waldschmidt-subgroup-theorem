import Mathlib
import LSG.ME.MainAbSlice
import LSG.ME.PhOpHom
import LSG.ME.WustId
import LSG.W88.K11Lin

/-!
# Auxiliary lemmas for the assembly of `MultEstAb` (STAGE2 §11, S6)

* `DLmix_IG`, `IG_le_VOg_mix`: words in all charts preserve `I_G`.
* `exists_reps_G`: distinct coset representatives.
* `coords_nscal_univ`, `finrank_torusLie`.
* `HasData.addShift'`, **`deg_le_of_hfun'`** (generic form of StrongSix's `deg_le_of_hfun`),
  **`lower_deg`** (a polynomial lower bound through `t ↦ 2t + c`).
* `lin3` (the polynomial `N (a t + 1)^h (b t + 1)^r (c t + 1)^s`) and its data.
* **`hfun_P_coset_ge`**: the sliced lower bound for a coset of `H⁰` with the factor `(tD₂+1)^m`
  cancelled: `(tD₀/t₀+1)^{t₀} (tD₁/t₁+1)^{t₁} (tD₂+1)^{t₂} ≤ 4^m · H(vanishP univ α I(a + H⁰); 2t)`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan IsAbelianTangent)
open StrongSix.M2 (FLE hfun hdata HasData DL DL_cons)

namespace LSG.ME

/-! ### `I_G` and mixed words -/

section IGmix

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem DLmix_IG (l : List ((Fin m → Fin 3) × Tan d₀ d₁ m)) {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    DL (Dmix Ls) l P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  induction l generalizing P with
  | nil => simpa using hP
  | cons p l ih => rw [DL_cons]; exact ih (Dh_IG two_ne_zero p.1 p.2 hP)

theorem IG_le_VOg_mix (W : Submodule ℂ (Tan d₀ d₁ m)) (n : ℕ)
    (E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ VOg (Dmix Ls) (Wmix W) (vanish E) n :=
  fun _ hx l _ _ => IG_le_vanish two_ne_zero E (DLmix_IG l hx)

end IGmix

/-! ### Coset representatives -/

section Reps

variable {K : Type*} [Field K] [DecidableEq K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

theorem gtransl_eq_of_sub_mem {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsSubgroupG H)
    {a b : GPt K d₀ d₁ g₂ g₃} (h : a - b ∈ H) : gtransl a H = gtransl b H := by
  ext x
  rw [mem_gtransl, mem_gtransl]
  constructor
  · intro hx
    have := hH.add_mem _ hx _ h
    rwa [show x - a + (a - b) = x - b by abel] at this
  · intro hx
    have := hH.add_mem _ hx _ (hH.neg_mem _ h)
    rwa [show x - b + -(a - b) = x - a by abel] at this

/-- **Distinct coset representatives.** -/
theorem exists_reps_G {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsSubgroupG H)
    (T' : Finset (GPt K d₀ d₁ g₂ g₃)) :
    ∃ Rs ⊆ T', (⋃ a ∈ Rs, gtransl a H) = (⋃ a ∈ T', gtransl a H) ∧
      ∀ a ∈ Rs, ∀ b ∈ Rs, a ≠ b → a - b ∉ H := by
  classical
  induction T' using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | insert t T' ht ih =>
    obtain ⟨Rs, hsub, hU, hd⟩ := ih
    by_cases hc : ∃ a ∈ Rs, t - a ∈ H
    · obtain ⟨a, ha, hat⟩ := hc
      refine ⟨Rs, hsub.trans (Finset.subset_insert _ _), ?_, hd⟩
      rw [Finset.set_biUnion_insert, ← hU, gtransl_eq_of_sub_mem hH hat]
      exact (Set.union_eq_right.mpr
        (Set.subset_iUnion₂ (s := fun a (_ : a ∈ Rs) => gtransl a H) a ha)).symm
    · push Not at hc
      refine ⟨insert t Rs, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, hU]
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · exact absurd rfl hab
          · exact hc b hb'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · intro hmem
            apply hc a ha'
            have := hH.neg_mem _ hmem
            rwa [neg_sub] at this
          · exact hd a ha' b hb' hab

omit [DecidableEq K] in
theorem coords_nscal_univ {α : Fin m → K} {g : GPt K d₀ d₁ g₂ g₃} (hg : ∀ k, lval α g k ≠ 0)
    (lam : Fin m → Kˣ) : coords g (nscal Finset.univ α g lam) = nrm α g := by
  unfold nrm
  congr 1
  funext k
  apply Units.ext
  rw [nscal_mem (Finset.mem_univ k) (hg k)]
  simp [hg k]

end Reps

theorem finrank_torusLie {d₁ : ℕ} (U : Submodule ℚ (Fin d₁ → ℚ)) :
    finrank ℂ (LSG.W88.torusLie U) + finrank ℚ U = d₁ :=
  LSG.W88.K11.finrank_annC U

/-! ### Data -/

theorem HasData.addShift' {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) (e : ℕ) :
    HasData (fun k => f (k + e)) a c := by
  induction e with
  | zero => simpa using h
  | succ e ih =>
    refine StrongSix.M2.hasData_congr ih.shift (Filter.Eventually.of_forall fun k => ?_)
    change f (k + 1 + e) = f (k + (e + 1))
    congr 1
    omega

section Generic

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] (β : σ → ι)
  (D : ι → ℕ) {K : Type*} [Field K]

/-- **Comparison of degrees** (generic `deg_le_of_hfun`). -/
theorem deg_le_of_hfun' {J A : Ideal (MvPolynomial σ K)} (hJ : J ≠ ⊤) (hA : A ≠ ⊤)
    (hdimEq : (hdata β D K A).1 = (hdata β D K J).1) {κ c : ℕ} (hκ : 1 ≤ κ)
    (h : ∀ t, κ * hfun β D K J t ≤ hfun β D K A (t + c)) :
    (κ : ℤ) * (hdata β D K J).2 ≤ (hdata β D K A).2 := by
  have hf := (StrongSix.M2.hdata_spec β D K hJ).smul (κ := (κ : ℤ))
    (by exact_mod_cast (by omega : κ ≠ 0))
  have hg := HasData.addShift' (StrongSix.M2.hdata_spec β D K hA) c
  rcases hf.compare hg (Filter.Eventually.of_forall fun t => by exact_mod_cast h t)
      (Filter.Eventually.of_forall fun _ => by positivity) with h1 | ⟨-, h2⟩
  · omega
  · exact h2

end Generic

/-- **A polynomial lower bound through `t ↦ 2t + c`.** -/
theorem lower_deg {g : ℕ → ℤ} {a : ℕ} {c : ℤ} (hg : HasData g a c) {P : Polynomial ℤ}
    (hP : P ≠ 0) {C : ℤ} (hC : 0 < C) {c₁ : ℕ}
    (hle : ∀ t : ℕ, P.eval (t : ℤ) ≤ C * g (2 * t + c₁))
    (hnn : ∀ t : ℕ, 0 ≤ P.eval (t : ℤ)) :
    P.natDegree ≤ a ∧ (a = P.natDegree →
      P.leadingCoeff * P.natDegree.factorial ≤ C * (2 ^ a * c)) := by
  have hp := StrongSix.M2.hasData_poly hP
  have hG := StrongSix.M2.HasData.smul (HasData.comp_two (HasData.addShift' hg c₁)) hC.ne'
  rcases hp.compare hG (Filter.Eventually.of_forall fun t => by
      simpa using hle t) (Filter.Eventually.of_forall hnn) with h | ⟨h, h'⟩
  · exact ⟨h.le, fun e => by omega⟩
  · exact ⟨h.le, fun _ => h'⟩

/-- `N (a X + 1)^h (b X + 1)^r (c X + 1)^s`. -/
noncomputable def lin3 (N a b c h r s : ℕ) : Polynomial ℤ :=
  Polynomial.C (N : ℤ) * (Polynomial.C (a : ℤ) * Polynomial.X + 1) ^ h *
    (Polynomial.C (b : ℤ) * Polynomial.X + 1) ^ r * (Polynomial.C (c : ℤ) * Polynomial.X + 1) ^ s

theorem lin3_eval (N a b c h r s t : ℕ) :
    (lin3 N a b c h r s).eval (t : ℤ) =
      ((N * (a * t + 1) ^ h * (b * t + 1) ^ r * (c * t + 1) ^ s : ℕ) : ℤ) := by
  simp [lin3]

theorem lin3_data {N a b c : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (h r s : ℕ) :
    lin3 N a b c h r s ≠ 0 ∧ (lin3 N a b c h r s).natDegree = h + r + s ∧
      (lin3 N a b c h r s).leadingCoeff = (N : ℤ) * a ^ h * b ^ r * c ^ s := by
  have lin : ∀ x : ℕ, 1 ≤ x → (Polynomial.C (x : ℤ) * Polynomial.X + 1).natDegree = 1 ∧
      (Polynomial.C (x : ℤ) * Polynomial.X + 1).leadingCoeff = (x : ℤ) ∧
      Polynomial.C (x : ℤ) * Polynomial.X + 1 ≠ 0 := fun x hx => by
    have hx0 : (x : ℤ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
    have h1 := Polynomial.natDegree_linear (b := (1 : ℤ)) hx0
    rw [map_one] at h1
    have h2 := Polynomial.leadingCoeff_linear (b := (1 : ℤ)) hx0
    rw [map_one] at h2
    refine ⟨h1, h2, fun h0 => ?_⟩
    rw [h0, Polynomial.natDegree_zero] at h1
    omega
  obtain ⟨a1, a2, a3⟩ := lin a ha
  obtain ⟨b1, b2, b3⟩ := lin b hb
  obtain ⟨c1, c2, c3⟩ := lin c hc
  have hN0 : Polynomial.C (N : ℤ) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]; exact_mod_cast (by omega : N ≠ 0)
  have h0 : lin3 N a b c h r s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 (pow_ne_zero _ a3)) (pow_ne_zero _ b3))
      (pow_ne_zero _ c3)
  refine ⟨h0, ?_, ?_⟩
  · rw [lin3, Polynomial.natDegree_mul (mul_ne_zero (mul_ne_zero hN0 (pow_ne_zero _ a3))
      (pow_ne_zero _ b3)) (pow_ne_zero _ c3), Polynomial.natDegree_mul (mul_ne_zero hN0
      (pow_ne_zero _ a3)) (pow_ne_zero _ b3), Polynomial.natDegree_mul hN0 (pow_ne_zero _ a3),
      Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, a1, b1, c1]
    ring
  · rw [lin3, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_pow,
      Polynomial.leadingCoeff_pow, a2, b2, c2]

/-! ### The sliced lower bound for a coset of `H⁰` -/

section Coset

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

theorem finrank_le_m (t : Submodule ℂ (Fin m → ℂ)) : finrank ℂ t ≤ m := by
  have := Submodule.finrank_le t
  rwa [Module.finrank_fin_fun] at this

/-- **The sliced lower bound for a coset of `H⁰`** (the factor `(tD₂+1)^m` cancelled). -/
theorem hfun_P_coset_ge (hH : IsSubgroupG H) (hc : IsZClosed H) (α : Fin m → ℂ)
    (a : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))
    (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH hc))) (D₀ D₁ D₂ : ℕ) :
    ∃ tAb : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls tAb ∧
      (∀ z, z ∈ tAb ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc) ∧ ∀ t,
      (t * D₀ / finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) + 1) ^
          finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) *
        (t * D₁ / (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) + 1) ^
          (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) *
        (t * D₂ + 1) ^ finrank ℂ tAb ≤
      4 ^ m * hfun blk (Dfun D₀ D₁ D₂) ℂ
        (vanishP Finset.univ α (gtransl a (H0 Ls hH hc))) (2 * t) := by
  classical
  have hH0 := H0_isSubgroup hH hc
  have hc0 := isZClosed_H0 (Ls := Ls) hH hc
  obtain ⟨tAb0, hab0, htAb0, -⟩ := exists_abelianTangent_Htil hH0 hc0
  have htAb : ∀ z, z ∈ tAb0 ↔ inAb (d₀ := d₀) (d₁ := d₁) z ∈ lieAlg Ls hH hc := fun z =>
    (htAb0 z).trans (mem_lieAlg_H0 hH hc)
  refine ⟨tAb0, hab0, htAb, fun t => ?_⟩
  obtain ⟨tAb, -, htAb', hle⟩ := hfun_H0_ge'' hH hc _ _ (prodSet_ML_subset_projL hH hc)
    D₀ D₁ D₂ t
  have hrank : finrank ℂ tAb = finrank ℂ tAb0 := by
    have : tAb = tAb0 := by ext z; rw [htAb', htAb]
    rw [this]
  rw [hrank] at hle
  have hp0 := vanish_H0_isPrime (Ls := Ls) hH hc
  have hpa := vanish_gtransl_isPrime two_ne_zero (discr_g2L Ls) hc0 hp0 a
  have h2 := hfun_le_transl two_ne_zero (discr_g2L Ls) (Dfun D₀ D₁ D₂) (H0 Ls hH hc) a t
  have h3 := hfun_le_of_hom α hpa hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs)
    (Dfun D₀ D₁ D₂) (2 * t)
  have hprod : ∏ k : Fin m, (2 * t * Dfun (m := m) D₀ D₁ D₂ (.e k) + 1) = (2 * t * D₂ + 1) ^ m := by
    simp [Dfun]
  rw [hprod] at h3
  set X := (t * D₀ / finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) + 1) ^
      finrank ℂ (StrongSix.M2.linV (ML Ls hH hc)) *
    (t * D₁ / (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc)))) + 1) ^
      (d₁ - finrank ℚ (StrongSix.M2.qspan (StrongSix.M2.latt (ML Ls hH hc))))
  set y := t * D₂ + 1
  set r := finrank ℂ tAb0
  set hP := hfun blk (Dfun D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a (H0 Ls hH hc))) (2 * t)
  have hr : r ≤ m := finrank_le_m tAb0
  have hy : 0 < y := Nat.succ_pos _
  have h2y : 2 * t * D₂ + 1 ≤ 2 * y := by simp only [y]; nlinarith
  have hlhs : X * ((y ^ 2) ^ r * y ^ (m - r)) = X * y ^ r * y ^ m := by
    rw [← pow_mul, show y ^ m = y ^ r * y ^ (m - r) by rw [← pow_add, Nat.add_sub_cancel' hr]]
    ring
  have hchain : X * y ^ r * y ^ m ≤ 4 ^ m * hP * y ^ m := by
    calc X * y ^ r * y ^ m = X * ((y ^ 2) ^ r * y ^ (m - r)) := hlhs.symm
      _ ≤ hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (H0 Ls hH hc)) t := by
          rw [← mul_assoc]; exact hle
      _ ≤ 2 ^ m * hfun blk (Dfun D₀ D₁ D₂) ℂ (vanish (gtransl a (H0 Ls hH hc))) (2 * t) := h2
      _ ≤ 2 ^ m * ((2 * t * D₂ + 1) ^ m * hP) := Nat.mul_le_mul_left _ h3
      _ ≤ 2 ^ m * ((2 * y) ^ m * hP) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2y m))
      _ = 4 ^ m * hP * y ^ m := by
          rw [mul_pow, show (4 : ℕ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]; ring
  exact Nat.le_of_mul_le_mul_right hchain (pow_pos hy m)

end Coset

/-! ### Linear algebra and coverings -/

theorem finrank_submodule_prod {R M N : Type*} [Field R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N)
    [FiniteDimensional R p] [FiniteDimensional R q] :
    finrank R ↥(p.prod q) = finrank R p + finrank R q := by
  let e : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩,
        ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_prod]

section Cover

variable {K : Type*} [Field K] [DecidableEq K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- Translates of `GV` as unions of cosets of `H ⊆ GV`. -/
theorem biUnion_gtransl_cover {H GV : Set (GPt K d₀ d₁ g₂ g₃)}
    (hGV : IsSubgroupG GV) (hHGV : H ⊆ GV) (Rc : Finset (GPt K d₀ d₁ g₂ g₃))
    (hRc : ∀ c ∈ Rc, c ∈ GV) (hcov : GV ⊆ ⋃ c ∈ Rc, gtransl c H) (X : Finset (GPt K d₀ d₁ g₂ g₃)) :
    (⋃ a ∈ X, gtransl a GV) = ⋃ b ∈ (X ×ˢ Rc).image (fun p => p.2 + p.1), gtransl b H := by
  classical
  ext x
  simp only [Set.mem_iUnion, mem_gtransl, Finset.mem_image, Finset.mem_product, exists_prop]
  constructor
  · rintro ⟨a, ha, hxa⟩
    have := hcov hxa
    simp only [Set.mem_iUnion, mem_gtransl, exists_prop] at this
    obtain ⟨c, hc, hxc⟩ := this
    refine ⟨c + a, ⟨(a, c), ⟨ha, hc⟩, rfl⟩, ?_⟩
    rwa [show x - (c + a) = x - a - c by abel]
  · rintro ⟨b, ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩, hx⟩
    refine ⟨a, ha, ?_⟩
    have := hGV.add_mem _ (hHGV hx) _ (hRc c hc)
    rwa [show x - (c + a) + c = x - a by abel] at this

end Cover

/-! ### The final arithmetic -/

/-- The constant of `MultEstAb`. -/
def CstAb (d₀ d₁ m : ℕ) : ℕ :=
  (d₀ + d₁ + m) ^ (d₀ + d₁ + m) * d₀ ^ d₀ * d₁ ^ d₁ * 4 ^ m * 2 ^ (d₀ + d₁ + m) *
    (d₀ + d₁ + m).factorial * 4 ^ d₀ * 8 ^ d₁ * 12 ^ m

theorem pow_self_mono {a b : ℕ} (h : a ≤ b) : a ^ a ≤ b ^ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.one_le_pow _ _ hb
  · exact (Nat.pow_le_pow_left h a).trans (Nat.pow_le_pow_right (by omega) h)

theorem final_arith_ab {d₀ d₁ m ℓ e t₀ t₁ t₂ T nF nR k D₀ D₁ D₂ κ : ℕ} {deg0 degA degIG : ℤ}
    (hℓ : ℓ ≤ d₀ + d₁ + m) (he : e ≤ d₀ + d₁ + m) (hκ : κ ≤ d₀ ^ d₀ * d₁ ^ d₁)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (h0 : 0 ≤ deg0)
    (A1 : ((nR * (4 * D₀) ^ t₀ * (4 * D₁) ^ t₁ * (4 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * 4 ^ m : ℕ) : ℤ) * (2 ^ e * deg0))
    (A2 : (((k + 1) ^ ℓ : ℕ) : ℤ) * deg0 ≤ degA) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ (((d₀ + d₁ + m).factorial * (4 * D₀) ^ d₀ * (2 * (4 * D₁)) ^ d₁ *
      (12 * D₂) ^ m : ℕ) : ℤ)) :
    T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ CstAb d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m := by
  set n := d₀ + d₁ + m
  set X := (4 * D₀) ^ t₀ * (4 * D₁) ^ t₁ * (4 * D₂) ^ t₂
  set L := ℓ ^ ℓ
  set P := (k + 1) ^ ℓ
  have hDX : D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ X := by
    simp only [X]
    gcongr <;> omega
  have hfac : 1 ≤ e.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)
  have s1 : T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ L * P * (nR * X * e.factorial) := by
    calc T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ = T ^ ℓ * nF * (D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂) := by
          ring
      _ ≤ (L * P) * nR * (X * e.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul hT hF) (hDX.trans (Nat.le_mul_of_pos_right _ hfac))
      _ = L * P * (nR * X * e.factorial) := by ring
  have hdA : 0 ≤ degA := le_trans (mul_nonneg (by positivity) h0) A2
  have s2 : ((L * P * (nR * X * e.factorial) : ℕ) : ℤ) ≤
      (L : ℤ) * κ * 4 ^ m * 2 ^ e * degIG := by
    have hA1 : ((nR * X * e.factorial : ℕ) : ℤ) ≤ ((κ * 4 ^ m : ℕ) : ℤ) * (2 ^ e * deg0) := by
      simpa [X, mul_assoc] using A1
    calc ((L * P * (nR * X * e.factorial) : ℕ) : ℤ)
        = (L : ℤ) * P * ((nR * X * e.factorial : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (L : ℤ) * P * (((κ * 4 ^ m : ℕ) : ℤ) * (2 ^ e * deg0)) := by gcongr
      _ = (L : ℤ) * κ * 4 ^ m * 2 ^ e * ((P : ℤ) * deg0) := by push_cast; ring
      _ ≤ (L : ℤ) * κ * 4 ^ m * 2 ^ e * degA :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast A2) (by positivity)
      _ ≤ (L : ℤ) * κ * 4 ^ m * 2 ^ e * degIG := by gcongr
  have s3 : (L : ℤ) * κ * 4 ^ m * 2 ^ e * degIG ≤
      ((CstAb d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m : ℕ) : ℤ) := by
    have hL : L ≤ n ^ n := pow_self_mono hℓ
    have h2e : 2 ^ e ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) he
    calc (L : ℤ) * κ * 4 ^ m * 2 ^ e * degIG
        ≤ (L : ℤ) * κ * 4 ^ m * 2 ^ e * (((d₀ + d₁ + m).factorial * (4 * D₀) ^ d₀ *
            (2 * (4 * D₁)) ^ d₁ * (12 * D₂) ^ m : ℕ) : ℤ) := by gcongr
      _ = (((L * κ * 4 ^ m * 2 ^ e) * ((d₀ + d₁ + m).factorial * (4 * D₀) ^ d₀ *
            (2 * (4 * D₁)) ^ d₁ * (12 * D₂) ^ m) : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((CstAb d₀ d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          have e1 : (2 * (4 * D₁)) ^ d₁ = 8 ^ d₁ * D₁ ^ d₁ := by rw [← mul_assoc, mul_pow]; norm_num
          rw [mul_pow, e1, mul_pow, CstAb]
          calc L * κ * 4 ^ m * 2 ^ e * ((d₀ + d₁ + m).factorial * (4 ^ d₀ * D₀ ^ d₀) *
                (8 ^ d₁ * D₁ ^ d₁) * (12 ^ m * D₂ ^ m))
              = (L * κ * 2 ^ e) * (4 ^ m * (d₀ + d₁ + m).factorial * 4 ^ d₀ * 8 ^ d₁ * 12 ^ m *
                  D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m) := by ring
            _ ≤ (n ^ n * (d₀ ^ d₀ * d₁ ^ d₁) * 2 ^ n) * (4 ^ m * (d₀ + d₁ + m).factorial *
                  4 ^ d₀ * 8 ^ d₁ * 12 ^ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ m) := by gcongr
            _ = _ := by ring
  exact_mod_cast (show ((T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ : ℕ) : ℤ) ≤ _ from
    (Nat.cast_le.mpr s1).trans (s2.trans s3))

end LSG.ME
