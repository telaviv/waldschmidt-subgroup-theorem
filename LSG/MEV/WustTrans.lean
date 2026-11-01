import Mathlib
import LSG.MEV.WustPair
import LSG.MEV.WustCoset
import LSG.ME.WustAlg
import StrongSix.M2.Pairing

/-!
# Wüstholz transversals for unions of cosets of `H⁰` and Wüstholz's lemma (vector extensions)

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)`, `W ⊆ Lie G̃` (`LieV` coordinates) and
`ℓ = dim W − dim (W ∩ lieAlg H)`:

* `exists_dual` (linear algebra): if no nontrivial combination of `w₁..w_ℓ` is in the left kernel
  of a pairing, there is a dual family.
* **`exists_dirs`**: `w₁..w_ℓ ∈ W` with no nontrivial combination in `lieAlg H` (biorthogonality
  of the identity pairing, `exists_biorth`, whose kernel is `lieAlg H`, `mem_lieAlgL_of_ker`).
* **`exists_coset_data`**: for every `a`, `T₁..T_ℓ ∈ I(a + H⁰)`, `N ∉ I(a + H⁰)` with
  `Dhc_{chartsV a}(wᵢ) Tⱼ − δᵢⱼ N ∈ I(a + H⁰)`. The data are built **at each coset directly**
  (dual family of the pairing `π_a` + adjugate, `N = det`, equal to `1` at `coords a 1`); the left
  kernel of `π_a` lies in `lieAlg H` for every `a` (`mem_lieAlgL_of_ker`), which replaces the
  abelian transport by translation identities. The chart at `a` is the canonical one (`V` at `O`,
  `W` elsewhere), so `2`-torsion cosets cause no degeneracy.
* **`exists_transversalsV`**: for distinct cosets `a + H⁰` (`a ∈ R`), `E = ⋃ (a + H⁰)`: glued
  derivations `Dᵢ = Σ_{a ∈ R} B_a • Dhc (chartsV a) wᵢ`, `Qⱼ ∈ I(E)`, `M` a non-zero-divisor
  modulo `I(E)` with `Dᵢ Qⱼ − δᵢⱼ M ∈ I(E)` (`LSG.ME.glue`).
* **`wustholz_cosetsV`**: `(k+1)^ℓ · H(I(E); t) ≤ H(A; t + S₀ c₀)` for every `A` vanishing to order
  `> S₀` modulo `I(E)` along `W` in all charts (`A ≤ VOg DmixV (WmixV W) (I(E)) S₀`, the output
  format of `mem_VOg_mixV`), `ℓ k ≤ S₀`, with `c₀` independent of `A`, `S₀`, `k`, `t`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk VOg)
open StrongSix.M2 (DL DL_cons hfun FLE)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Dual families -/

theorem exists_dual {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (φ : M →ₗ[ℂ] N →ₗ[ℂ] ℂ) {ℓ : ℕ} (w : Fin ℓ → M)
    (hw : ∀ c : Fin ℓ → ℂ, φ (∑ i, c i • w i) = 0 → c = 0) :
    ∃ P : Fin ℓ → N, ∀ i j, φ (w i) (P j) = if i = j then 1 else 0 := by
  classical
  set Ψ : N →ₗ[ℂ] (Fin ℓ → ℂ) := LinearMap.pi fun i => φ (w i) with hΨ
  have hΨa : ∀ n i, Ψ n i = φ (w i) n := fun n i => rfl
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    set c : Fin ℓ → ℂ := fun i => f (Pi.single i 1)
    have hfx : ∀ x : Fin ℓ → ℂ, f x = ∑ i, x i * c i := by
      intro x
      have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin ℓ → ℂ) := by
        ext j; simp [Pi.single_apply]
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, smul_eq_mul, c]
    have hφ : φ (∑ i, c i • w i) = 0 := by
      refine LinearMap.ext fun n => ?_
      have h1 := hf (LinearMap.mem_range_self Ψ n)
      rw [LinearMap.mem_ker, hfx] at h1
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => by rw [hΨa]; ring
    have hc := hw c hφ
    apply hf0
    refine LinearMap.pi_ext fun i x => ?_
    rw [hfx]
    simp [hc]
  choose P hP using fun j => hsurj (Pi.single j (1 : ℂ))
  refine ⟨P, fun i j => ?_⟩
  have := congrFun (hP j) i
  rw [hΨa] at this
  rw [this, Pi.single_apply]

/-! ### Directions and coset data -/

section Trans

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **Directions**: `ℓ` vectors of `W` no nontrivial combination of which lies in `lieAlg H`. -/
theorem exists_dirs (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) :
    ∃ w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → LieV ℂ d₀ d₁ m,
      (∀ i, w i ∈ W) ∧ ∀ c : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → ℂ,
        ∑ i, c i • w i ∈ lieAlgL Ls hH → c = 0 := by
  classical
  set φ := pairV Ls (chartsV (0 : GPtV d₀ d₁ Ls)) (coords (0 : GPtV d₀ d₁ Ls) 1)
    (vanish (H0 Ls hH))
  have hker : LinearMap.ker φ ≤ lieAlgL Ls hH := by
    intro w hw
    refine mem_lieAlgL_of_ker hH hc 0 fun P hP => ?_
    rw [gtransl_zero] at hP
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hw) ⟨P, hP⟩
    rw [pairV_apply] at this
    exact this
  have hle : finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH) ≤
      finrank ℂ W - finrank ℂ ↥(W ⊓ LinearMap.ker φ) := by
    have : finrank ℂ ↥(W ⊓ LinearMap.ker φ) ≤ finrank ℂ ↥(W ⊓ lieAlgL Ls hH) :=
      Submodule.finrank_mono (inf_le_inf_left _ hker)
    omega
  obtain ⟨w, P, hwW, hwP⟩ := StrongSix.M2.exists_biorth φ W _ hle
  refine ⟨w, hwW, fun c hcl => funext fun j => ?_⟩
  have h0 := eval_Dv_zero_of_mem hH hc hcl (P j).2
  have e : φ (∑ i, c i • w i) (P j) = c j := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, hwP]
    simp
  rw [← e, pairV_apply]
  exact h0

/-- **Transversal data at one coset**, for directions with no combination in `lieAlg H`. -/
theorem exists_coset_data {ℓ : ℕ} (w : Fin ℓ → LieV ℂ d₀ d₁ m)
    (hw : ∀ c : Fin ℓ → ℂ, ∑ i, c i • w i ∈ lieAlgL Ls hH → c = 0) (a : GPtV d₀ d₁ Ls) :
    ∃ (T : Fin ℓ → MvPolynomial (Var d₀ d₁ m) ℂ) (N : MvPolynomial (Var d₀ d₁ m) ℂ),
      (∀ j, T j ∈ vanish (gtransl a (H0 Ls hH))) ∧ N ∉ vanish (gtransl a (H0 Ls hH)) ∧
      ∀ i j, Dhc Ls (chartsV a) (w i) (T j) - (if i = j then N else 0) ∈
        vanish (gtransl a (H0 Ls hH)) := by
  classical
  set C := gtransl a (H0 Ls hH)
  have haC : a ∈ C := ⟨0, (H0_isSubgroup hH).zero_mem, zero_add a⟩
  set φ := pairV Ls (chartsV a) (coords a 1) (vanish C)
  obtain ⟨P, hP⟩ := exists_dual φ w fun c hc0 => hw c (mem_lieAlgL_of_ker hH hc a fun Q hQ => by
    have := LinearMap.congr_fun hc0 ⟨Q, hQ⟩
    rwa [pairV_apply] at this)
  set A : Matrix (Fin ℓ) (Fin ℓ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    fun i j => Dhc Ls (chartsV a) (w i) (P j)
  have hA0 : ∀ i j, eval (coords a 1) (A i j) = if i = j then 1 else 0 := by
    intro i j
    have h1 := eval_DL_Dhc_chartsV (Ls := Ls) a [w i] (P j : MvPolynomial (Var d₀ d₁ m) ℂ)
    simp only [DL_cons, StrongSix.M2.DL_nil] at h1
    rw [show A i j = Dhc Ls (chartsV a) (w i) (P j) from rfl, h1, ← hP i j, pairV_apply]
  refine ⟨fun j => ∑ k, (P k : MvPolynomial (Var d₀ d₁ m) ℂ) * A.adjugate k j, A.det,
    fun j => Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (P k).2, fun hmem => ?_,
    fun i j => ?_⟩
  · have h1 := mem_vanish.mp hmem a haC 1
    rw [RingHom.map_det] at h1
    have : (eval (coords a 1)).mapMatrix A = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hA0, Matrix.one_apply]
    rw [this, Matrix.det_one] at h1
    exact one_ne_zero h1
  · have hmul := congrFun (congrFun (Matrix.mul_adjugate A) i) j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hmul
    have e : Dhc Ls (chartsV a) (w i)
        (∑ k, (P k : MvPolynomial (Var d₀ d₁ m) ℂ) * A.adjugate k j) -
        (if i = j then A.det else 0) =
        ∑ k, (P k : MvPolynomial (Var d₀ d₁ m) ℂ) * Dhc Ls (chartsV a) (w i) (A.adjugate k j) := by
      rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      have : ∑ k, A.adjugate k j * Dhc Ls (chartsV a) (w i) (P k) =
          if i = j then A.det else 0 := by
        calc ∑ k, A.adjugate k j * Dhc Ls (chartsV a) (w i) (P k)
            = ∑ k, A i k * A.adjugate k j := Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = _ := hmul
          _ = _ := by split_ifs <;> simp
      rw [this]; ring
    rw [e]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (P k).2

/-! ### Gluing over finitely many cosets -/

/-- **Wüstholz transversals for a finite union of cosets of `H⁰`.** -/
theorem exists_transversalsV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → LieV ℂ d₀ d₁ m)
      (B : GPtV d₀ d₁ Ls → MvPolynomial (Var d₀ d₁ m) ℂ)
      (Q : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (M : MvPolynomial (Var d₀ d₁ m) ℂ),
      (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) ∧
      (∀ i j, (∑ a ∈ R, B a • Dhc Ls (chartsV a) (w i)) (Q j) -
        (if i = j then M else 0) ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) ∧
      ∀ x, M * x ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH)) →
        x ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH)) := by
  classical
  obtain ⟨w, hwW, hwind⟩ := exists_dirs hH hc W
  choose T N hT hN hTδ using exists_coset_data hH hc w hwind
  set V := H0 Ls hH
  have hV : IsZClosed V := isZClosed_H0 hH
  have hVp : (vanish V).IsPrime := vanish_H0_isPrime hH
  have hpC : ∀ a, (vanish (gtransl a V)).IsPrime := fun a => vanish_gtransl_isPrime hV hVp a
  have hsep : ∀ a b : GPtV d₀ d₁ Ls, ∃ f : MvPolynomial (Var d₀ d₁ m) ℂ,
      a ∈ R → b ∈ R → a ≠ b → f ∈ vanish (gtransl b V) ∧ f ∉ vanish (gtransl a V) := by
    intro a b
    by_cases h : a ∈ R ∧ b ∈ R ∧ a ≠ b
    · obtain ⟨f, hf1, hf2⟩ := exists_sep_projV (isZClosed_gtransl hV b)
        (not_gtransl_subsetV (H0_isSubgroup hH) (hdist a h.1 b h.2.1 h.2.2))
      exact ⟨f, fun _ _ _ => ⟨hf1, hf2⟩⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose f hf using hsep
  let B : GPtV d₀ d₁ Ls → MvPolynomial (Var d₀ d₁ m) ℂ := fun a => ∏ b ∈ R.erase a, f a b
  have hB : ∀ a ∈ R, B a ∉ vanish (gtransl a V) := by
    intro a ha hmem
    obtain ⟨b, hb, hfb⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpC a)).mp hmem
    exact (hf a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).2 hfb
  have hBo : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → B a ∈ vanish (gtransl b V) := by
    intro a ha b hb hab
    have hbe : b ∈ R.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    rw [show B a = f a b * ∏ x ∈ (R.erase a).erase b, f a x from
      (Finset.mul_prod_erase _ _ hbe).symm]
    exact Ideal.mul_mem_right _ _ (hf a b ha hb hab).1
  have hg := LSG.ME.glue (K := ℂ) R (fun a => vanish (gtransl a V)) (fun a _ => hpC a)
    (fun a i => Dhc Ls (chartsV a) (w i)) T N B (fun a _ => hT a) (fun a _ => hTδ a)
    (fun a _ => hN a) hB hBo
  refine ⟨w, B, fun j => ∑ a ∈ R, B a ^ 2 * T a j, ∑ a ∈ R, B a ^ 3 * N a, hwW, fun j => ?_,
    fun i j => ?_, fun x hx => ?_⟩
  · exact (mem_vanish_biUnionV R _).mpr fun a ha => (hg a ha).1 j
  · exact (mem_vanish_biUnionV R _).mpr fun a ha => (hg a ha).2.1 i j
  · refine (mem_vanish_biUnionV R _).mpr fun a ha => ?_
    exact ((hpC a).mem_or_mem ((mem_vanish_biUnionV R _).mp hx a ha)).resolve_left (hg a ha).2.2

/-! ### Wüstholz's lemma -/

/-- **Wüstholz's lemma for `I(E)`, `E` a finite union of distinct cosets of `H⁰`** (vector
extensions): `(k+1)^ℓ · H(I(E); t) ≤ H(A; t + S₀ c₀)`. -/
theorem wustholz_cosetsV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) * k ≤ S0 →
      A ≤ VOg (DmixV Ls) (WmixV W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) S0 → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) *
          hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) t ≤
        hfun blk D ℂ A (t + S0 * c0) := by
  classical
  obtain ⟨w, B, Q, M, hwW, hQ, hδ, hM⟩ := exists_transversalsV hH hc W R hdist
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' blk hD Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  set Dv := fun i => ∑ a ∈ R, B a • Dhc Ls (chartsV a) (w i)
  have hD' : ∀ i (n : ℕ) x, x ∈ VOg (DmixV Ls) (WmixV W)
      (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) (n + 1) →
      Dv i x ∈ VOg (DmixV Ls) (WmixV W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) n :=
    fun i n x hx => LSG.ME.glued_mem_VOg (Dv := DmixV Ls) R B (fun a => (chartsV a, w i))
      (fun a _ => hwW i) hx
  exact LSG.ME.wustholzM' blk D Dv hQ hδ hM hQdeg hk
    (fun x hx l hl => LSG.ME.DL_glued_mem Dv hD' l (hA hx) hl) t

end Trans

end

end LSG.MEV
