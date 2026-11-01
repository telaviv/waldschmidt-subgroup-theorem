import Mathlib
import LSG.ME.SliceWust

/-!
# The sliced Wüstholz lemma for finite unions of cosets of `H⁰` (STAGE2 §11.3, item S4)

For `E = ⋃_{a ∈ R} (a + H⁰)` (distinct cosets), `α` with `ℓ_k ∉ I(a + H⁰)` for all `a ∈ R`, `k`
(genericity), `W ⊆ Lie G` and `ℓ = dim W − dim (W ∩ lieAlg H)`:

  **`wustholz_cosets_sl`**: `(k+1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S₀ c₀)`

for every ideal `A ≤ VOg Dmix (Wmix W) I(E) S₀` (the hypothesis of `wustholz_cosets`), `ℓ k ≤ S₀`,
with `c₀` independent of `A`, `S₀`, `k`, `t` (it depends on `H, W, R, D, α`).

Ingredients beyond `wustholz_cosets`:
* `exists_identity_data_hom`: `exists_identity_data` with `N` multihomogeneous (`N = det`).
* `transport_hom`: `transport` with `N′ = Lc_{chartAt σ} · τ N` multihomogeneous of degree
  `1 + 2e`, independent of the coset.
* `exists_hom_sep`: multihomogeneous separators (components of separators).
* **`exists_transversals_sl`**: transversal data with a **multihomogeneous** multiplier
  `M = Σ_a B_a³ N′_a` (separators balanced to a common degree by powers `ℓ^c`, which uses
  `ℓ_k ∉ I(a + H⁰)`), `M ∉ I(a + H⁰)` for all `a ∈ R`; by `nzd_sl`, `M` is a non-zero-divisor
  modulo `sl α I(E)`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan)
open StrongSix.M2 (FLE hfun DL DL_cons)

namespace LSG.ME

theorem isWH_of_isHomE {K : Type*} [Field K] {d₀ d₁ m : ℕ} {P : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hP : IsHomE P d) : IsWeightedHomogeneous wV P d :=
  isWeightedHomogeneous_wV fun k => by rw [← wk_eq_wE]; exact hP k

/-! ### Homogeneous separators and transport -/

section General

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- **Multihomogeneous separators.** -/
theorem exists_hom_sep [Infinite K] {C₁ C₂ : Set (GPt K d₀ d₁ g₂ g₃)} (hC₂ : IsZClosed C₂)
    (h : ¬ C₁ ⊆ C₂) : ∃ (e : Fin m → ℕ) (f : MvPolynomial (Var d₀ d₁ m) K),
      IsWeightedHomogeneous wV f e ∧ f ∈ vanish C₂ ∧ f ∉ vanish C₁ := by
  obtain ⟨f, hf2, hf1⟩ := exists_sep_proj hC₂ h
  obtain ⟨s, hs⟩ := sum_multiComp f
  by_contra hcon
  push Not at hcon
  apply hf1
  rw [hs]
  exact Ideal.sum_mem _ fun e _ => hcon e _
    (weightedHomogeneousComponent_isWeightedHomogeneous e f) (multiComp_mem_vanish e hf2)

theorem isHomE_Lc (ch : Fin m → Fin 3) :
    IsHomE (Lc d₀ d₁ ch : MvPolynomial (Var d₀ d₁ m) K) 1 := fun k => Lc_isWH ch k

variable [DecidableEq K] [CharZero K] (h2 : (2 : K) ≠ 0)
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Transport with a multihomogeneous multiplier** (`transport` + degree bookkeeping). -/
theorem transport_hom [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (h0 : (0 : GPt K d₀ d₁ g₂ g₃) ∈ V) {ℓ : ℕ}
    (w : Fin ℓ → LieE K d₀ d₁ m) (T : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K)
    (N : MvPolynomial (Var d₀ d₁ m) K) {d e : Fin m → ℕ} (hTh : ∀ j, IsHomE (T j) d)
    (hT : ∀ j, T j ∈ vanish V) (hN : N ∉ vanish V) (hNh : IsHomE N e)
    (hTδ : ∀ i j, Dh g₂ g₃ (fun _ => 1) (w i) (T j) - (if i = j then N else 0) ∈ vanish V)
    (σ : GPt K d₀ d₁ g₂ g₃) :
    ∃ (T' : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K) (N' : MvPolynomial (Var d₀ d₁ m) K),
      (∀ j, T' j ∈ vanish (gtransl σ V)) ∧ N' ∉ vanish (gtransl σ V) ∧ IsHomE N' (1 + 2 • e) ∧
      ∀ i j, Dh g₂ g₃ (chartAt σ) (w i) (T' j) - (if i = j then N' else 0) ∈
        vanish (gtransl σ V) := by
  obtain ⟨c, hc⟩ := exists_transl_notMem h2 hΔ σ hN
  set C := gtransl σ V
  set τ' := τ g₂ g₃ (-σ) c
  set L1 : MvPolynomial (Var d₀ d₁ m) K := Lc d₀ d₁ (fun _ => 1)
  set Lσ : MvPolynomial (Var d₀ d₁ m) K := Lc d₀ d₁ (chartAt σ)
  have hpC : (vanish C).IsPrime := vanish_gtransl_isPrime h2 hΔ hV hp σ
  have hσC : σ ∈ C := mem_gtransl.mpr (by simpa using h0)
  have hτ : ∀ {P}, P ∈ vanish V → τ' P ∈ vanish C := fun hP =>
    transl_mem_vanish_gtransl h2 hΔ σ c hP
  refine ⟨fun j => τ' L1 * τ' (T j), Lσ * τ' N, fun j => Ideal.mul_mem_left _ _ (hτ (hT j)),
    fun hmem => ?_, (isHomE_Lc (chartAt σ)).mul' (isHomE_transl hNh (-σ) c), fun i j => ?_⟩
  · rcases hpC.mem_or_mem hmem with h | h
    · exact eval_Lc_chartAt_ne σ 1 (mem_vanish.mp h σ hσC 1)
    · exact hc h
  · have hid := IG_le_vanish h2 C (tr_id h2 (chartAt_ne_zero σ)
      (fun _ => (by decide : (1 : Fin 3) ≠ 0)) (-σ) c (w i) (hTh j))
    have h1 := Ideal.mul_mem_left _ Lσ (hτ (hTδ i j))
    have h3 : ∑ k, te g₂ g₃ (-σ) c (chartAt σ) (fun _ => 1) (w i) k * (d k • τ' (T j)) ∈
        vanish C :=
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (by
        rw [nsmul_eq_mul]; exact Ideal.mul_mem_left _ _ (hτ (hT j)))
    have h4 := Ideal.mul_mem_right (Dh g₂ g₃ (chartAt σ) (w i) (τ' L1)) _ (hτ (hT j))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ hid h1) h3) h4
    convert this using 1
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sub]
    split_ifs <;> (try simp only [map_zero, sub_zero]) <;> ring

end General

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-! ### Identity data with a multihomogeneous multiplier -/

/-- `exists_identity_data` with `N` multihomogeneous (same proof; `N = det A`). -/
theorem exists_identity_data_hom (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → Tan d₀ d₁ m)
      (T : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (N : MvPolynomial (Var d₀ d₁ m) ℂ) (d e : Fin m → ℕ),
      (∀ i, w i ∈ W) ∧ (∀ j, IsHomE (T j) d) ∧ (∀ j, T j ∈ vanish (H0 Ls hH hc)) ∧
      N ∉ vanish (H0 Ls hH hc) ∧ IsHomE N e ∧
      ∀ i j, Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (T j) - (if i = j then N else 0) ∈
        vanish (H0 Ls hH hc) := by
  classical
  set V := H0 Ls hH hc
  set ℓ := finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)
  have h0V : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ V := (H0_isSubgroup hH hc).zero_mem
  have hle : ℓ ≤ finrank ℂ W - finrank ℂ ↥(W ⊓ LinearMap.ker (pairing0 Ls V)) := by
    have : finrank ℂ ↥(W ⊓ LinearMap.ker (pairing0 Ls V)) ≤ finrank ℂ ↥(W ⊓ lieAlg Ls hH hc) :=
      Submodule.finrank_mono (inf_le_inf_left _ (ker_pairing0_le hH hc))
    omega
  obtain ⟨w, c, hwW, hwc⟩ := StrongSix.M2.exists_biorth (pairing0 Ls V) W ℓ hle
  obtain ⟨d, P, hPh, hPV, hPev⟩ := exists_hom_lift h0V (fun j => (c j : MvPolynomial _ ℂ))
    (fun j => (c j).2)
  set A : Matrix (Fin ℓ) (Fin ℓ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    fun i j => Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (P j)
  have hA0 : ∀ i j, eval (aId Ls d₀ d₁) (A i j) = if i = j then 1 else 0 := by
    intro i j
    rw [show A i j = Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (P j) from rfl, hPev, ← hwc i j]
    rfl
  have hAh : ∀ i j, IsHomE (A i j) (d + 1) := fun i j => isHomE_Dh (hPh j) _ _
  refine ⟨w, fun j => ∑ k, P k * A.adjugate k j, A.det, d + (ℓ - 1) • (d + 1), ℓ • (d + 1), hwW,
    fun j => ?_, fun j => Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hPV k),
    fun hmem => ?_, isHomE_det A hAh, fun i j => ?_⟩
  · rw [← mem_homSub]
    exact Submodule.sum_mem _ fun k _ => mem_homSub.mpr
      ((hPh k).mul' (isHomE_adjugate A hAh k j))
  · have h1 := mem_vanish.mp hmem 0 h0V 1
    rw [RingHom.map_det] at h1
    have : (eval (aId Ls d₀ d₁)).mapMatrix A = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hA0, Matrix.one_apply]
    exact one_ne_zero (h1.symm.trans (by rw [show coords 0 1 = aId Ls d₀ d₁ from rfl, this,
      Matrix.det_one]) |>.symm)
  · have hmul := congrFun (congrFun (Matrix.mul_adjugate A) i) j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hmul
    have e : Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (∑ k, P k * A.adjugate k j) -
        (if i = j then A.det else 0) =
        ∑ k, P k * Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (A.adjugate k j) := by
      rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      have : ∑ k, A.adjugate k j * Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (P k) =
          if i = j then A.det else 0 := by
        calc ∑ k, A.adjugate k j * Dh (g2L Ls) (g3L Ls) (fun _ => 1) (w i) (P k)
            = ∑ k, A i k * A.adjugate k j := Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = _ := hmul
          _ = _ := by split_ifs <;> simp
      rw [this]; ring
    rw [e]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hPV k)

/-! ### Transversals with a multihomogeneous multiplier -/

/-- **Wüstholz transversals with a multihomogeneous multiplier** for a finite union of distinct
cosets of `H⁰` (given `ℓ_k ∉ I(a + H⁰)`): glued derivations `Dᵢ = Σ_a B_a • Dh (chartAt a) wᵢ`,
`Qⱼ ∈ I(E)`, `Dᵢ Qⱼ − δᵢⱼ M ∈ I(E)`, `M` multihomogeneous with `M ∉ I(a + H⁰)` (`a ∈ R`). -/
theorem exists_transversals_sl (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) (R : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH hc) (α : Fin m → ℂ)
    (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH hc))) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → Tan d₀ d₁ m)
      (B : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (Q : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (M : MvPolynomial (Var d₀ d₁ m) ℂ) (μ : Fin m → ℕ),
      (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) ∧
      (∀ i j, (∑ a ∈ R, B a • Dh (g2L Ls) (g3L Ls) (chartAt a) (w i)) (Q j) -
        (if i = j then M else 0) ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) ∧
      IsWeightedHomogeneous wV M μ ∧ ∀ a ∈ R, M ∉ vanish (gtransl a (H0 Ls hH hc)) := by
  classical
  set V := H0 Ls hH hc
  have hV := isZClosed_H0 hH hc
  obtain ⟨w, T, N, d, e, hwW, hTh, hT, hN, hNh, hTδ⟩ := exists_identity_data_hom hH hc W
  choose T' N' hT' hN' hN'h hTδ' using transport_hom two_ne_zero (discr_g2L Ls) hV
    (vanish_H0_isPrime hH hc) (H0_isSubgroup hH hc).zero_mem w T N hTh hT hN hNh hTδ
  have hpC : ∀ a, (vanish (gtransl a V)).IsPrime := fun a =>
    vanish_gtransl_isPrime two_ne_zero (discr_g2L Ls) hV (vanish_H0_isPrime hH hc) a
  -- multihomogeneous separators
  have hsep : ∀ a b : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls), ∃ (ef : Fin m → ℕ)
      (f : MvPolynomial (Var d₀ d₁ m) ℂ), IsWeightedHomogeneous wV f ef ∧
      (a ∈ R → b ∈ R → a ≠ b → f ∈ vanish (gtransl b V) ∧ f ∉ vanish (gtransl a V)) := by
    intro a b
    by_cases h : a ∈ R ∧ b ∈ R ∧ a ≠ b
    · obtain ⟨ef, f, hfe, hf1, hf2⟩ := exists_hom_sep
        (isZClosed_gtransl two_ne_zero (discr_g2L Ls) hV b)
        (not_gtransl_subset (H0_isSubgroup hH hc) (hdist a h.1 b h.2.1 h.2.2))
      exact ⟨ef, f, hfe, fun _ _ _ => ⟨hf1, hf2⟩⟩
    · exact ⟨0, 0, isWeightedHomogeneous_zero _ _ _, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose ef f hfe hf using hsep
  set β : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) → Fin m → ℕ := fun a => ∑ b ∈ R.erase a, ef a b
  set βm : Fin m → ℕ := ∑ a ∈ R, β a
  set B : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) → MvPolynomial (Var d₀ d₁ m) ℂ :=
    fun a => lpow α (βm - β a) * ∏ b ∈ R.erase a, f a b
  have hBh : ∀ a ∈ R, IsWeightedHomogeneous wV (B a) βm := by
    intro a ha
    have hle : β a ≤ βm := Finset.single_le_sum (f := β) (fun _ _ => zero_le) ha
    have h1 := (isWH_lpow (d₀ := d₀) (d₁ := d₁) α (βm - β a)).mul
      (IsWeightedHomogeneous.prod (R.erase a) (fun b => f a b) (fun b => ef a b)
        fun b _ => hfe a b)
    rwa [tsub_add_cancel_of_le hle] at h1
  have hB : ∀ a ∈ R, B a ∉ vanish (gtransl a V) := by
    intro a ha hmem
    rcases (hpC a).mem_or_mem hmem with h | h
    · exact lpow_notMem (hpC a) α (hℓ a ha) _ h
    · obtain ⟨b, hb, hfb⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpC a)).mp h
      exact (hf a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).2 hfb
  have hBo : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → B a ∈ vanish (gtransl b V) := by
    intro a ha b hb hab
    have hbe : b ∈ R.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
    refine Ideal.mul_mem_left _ _ ?_
    rw [show ∏ x ∈ R.erase a, f a x = f a b * ∏ x ∈ (R.erase a).erase b, f a x from
      (Finset.mul_prod_erase _ _ hbe).symm]
    exact Ideal.mul_mem_right _ _ (hf a b ha hb hab).1
  have hg := glue (K := ℂ) R (fun a => vanish (gtransl a V)) (fun a _ => hpC a)
    (fun a i => Dh (g2L Ls) (g3L Ls) (chartAt a) (w i)) T' N' B (fun a _ => hT' a)
    (fun a _ => hTδ' a) (fun a _ => hN' a) hB hBo
  refine ⟨w, B, fun j => ∑ a ∈ R, B a ^ 2 * T' a j, ∑ a ∈ R, B a ^ 3 * N' a,
    3 • βm + (1 + 2 • e), hwW, fun j => ?_, fun i j => ?_, ?_, fun a ha => (hg a ha).2.2⟩
  · exact (mem_vanish_biUnion R _).mpr fun a ha => (hg a ha).1 j
  · exact (mem_vanish_biUnion R _).mpr fun a ha => (hg a ha).2.1 i j
  · exact IsWeightedHomogeneous.sum _ _ _ fun a ha =>
      ((hBh a ha).pow 3).mul (isWH_of_isHomE (hN'h a))

/-! ### The sliced Wüstholz lemma for cosets -/

/-- **Sliced Wüstholz lemma for `E = ⋃_{a ∈ R} (a + H⁰)`** (STAGE2 §11.3, S4): for `α` with
`ℓ_k ∉ I(a + H⁰)` (`a ∈ R`, all `k`) there is `c₀` such that for every ideal `A` vanishing to order
`> S₀` modulo `I(E)` along `W` (words in all charts) and `ℓ k ≤ S₀`:
`(k+1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_cosets_sl (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) (R : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH hc) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    (α : Fin m → ℂ) (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH hc))) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) * k ≤ S0 →
      A ≤ VOg (Dmix Ls) (Wmix W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) S0 → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) *
          hfun blk D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc)))) t ≤
        hfun blk D ℂ (sl α A) (t + S0 * c0) := by
  classical
  obtain ⟨w, B, Q, M, μ, hwW, hQ, hδ, hMh, hMn⟩ := exists_transversals_sl hH hc W R hdist α hℓ
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' blk hD Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  have hpC : ∀ a ∈ R, (vanish (gtransl a (H0 Ls hH hc))).IsPrime := fun a _ =>
    vanish_gtransl_isPrime two_ne_zero (discr_g2L Ls) (isZClosed_H0 hH hc)
      (vanish_H0_isPrime hH hc) a
  exact wustholz_sl_of_data α D (fun i => ∑ a ∈ R, B a • Dh (g2L Ls) (g3L Ls) (chartAt a) (w i))
    (fun k x hx => Eul_mem_vanish k hx) hQ hδ
    (nzd_sl α R (fun a => gtransl a (H0 Ls hH hc)) hpC hℓ hMh hMn) hQdeg
    (Dw := Dmix Ls) (Ws := Wmix W) (fun k p x => Eul_Dh k p.1 p.2 x)
    (fun i n x hx => glued_mem_VOg (Dv := Dmix Ls) R B (fun a => (chartAt a, w i))
      (fun a _ => hwW i) hx) hk hA t

end LSG.ME
