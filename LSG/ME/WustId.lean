import Mathlib
import StrongSix.M2.Pairing
import LSG.ME.WustTrans
import LSG.ME.SubgroupIrred

/-!
# Wüstholz transversals for cosets of `H⁰` (STAGE2 §5, "Wüstholz transversals"; `K = ℂ`)

For a Zariski-closed subgroup `H ⊆ G(ℂ)` with identity component `H⁰` (`H0`), a subspace
`W ⊆ Lie G` and `ℓ = dim W − dim (W ∩ lieAlg H)`:

* `eval_Dh_one_a0`: at the identity's cone point `a0 = coords 0 1`, the homogenised `V`-chart
  derivation agrees with the chart derivation of `TZ`.
* `exists_hom_lift` (any `K`, any `E ∋ 0`): replacing polynomials of `I(E)` by multihomogeneous ones
  of one common multidegree (components times powers of the `V_k`) without changing the values
  `D̂_w P (0)`.
* **`exists_identity_data`**: `w₁..w_ℓ ∈ W`, homogeneous `T₁..T_ℓ ∈ I(H⁰)` of a common
  multidegree, `N ∉ I(H⁰)` with `D̂_{wᵢ} Tⱼ − δᵢⱼ N ∈ I(H⁰)`. Route: the pairing
  `(w, P) ↦ D̂_w P (0)` on `Lie G × I(H⁰)` has left kernel `TZ H⁰ = lieAlg H` (`mem_TZ_iff`), so
  Gram–Schmidt (`exists_biorth`) gives `D̂_{wᵢ} Pⱼ (0) = δᵢⱼ`; with `A = (D̂_{wᵢ} Pⱼ)`,
  `N = det A` (`= 1` at `0`) and `T = P · adj A`.
* **`exists_transversals`**: for distinct cosets `a + H⁰` (`a ∈ R`), `E = ⋃ (a + H⁰)`: glued
  derivations `Dᵢ = Σ_{a ∈ R} B_a • Dh (chartAt a) wᵢ`, `Qⱼ ∈ I(E)`, `M` a non-zero-divisor
  modulo `I(E)` with `Dᵢ Qⱼ − δᵢⱼ M ∈ I(E)`.
* `DLmix_mem_VO1`, `mem_VOg_mix`: homogeneous polynomials vanishing to order `> n` along `W` (in the
  canonical charts) at every point of `E` vanish to order `> n` modulo `I(E)` for words in all
  charts (`Dmix`), hence (`DL_glued_mem`) for words in the glued derivations.
* **`wustholz_cosets`**: Wüstholz's lemma for `I(E)`:
  `(k+1)^ℓ · H(I(E); t) ≤ H(A; t + S₀ c₀)` for `A ⊆ VOg Dmix (I(E)) S₀`, `ℓ k ≤ S₀`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.W88 (Tan)
open StrongSix.M2 (FLE hfun DL DL_cons)

namespace LSG.ME

/-! ### Homogeneous lifts (any field) -/

section HomLift

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

theorem wk_eq_wE (k : Fin m) : (wk k : Var d₀ d₁ m → ℕ) = wE k := by
  funext v
  cases v <;> simp [wk, wE, wV, Pi.single_apply, eq_comm]

theorem isHomE_of_wV {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hP : IsWeightedHomogeneous wV P d) : IsHomE P d := fun k s hs => by
  rw [wk_eq_wE, weight_wE, hP hs]

theorem eval_coords_zero_e1 (lam : Fin m → Kˣ) (k : Fin m) :
    coords (0 : GPt K d₀ d₁ g₂ g₃) lam (.e k 1) = lam k := by
  simp [coords, rep, O]

/-- **Homogeneous lifts.** -/
theorem exists_hom_lift [Infinite K] {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (h0 : (0 : GPt K d₀ d₁ g₂ g₃) ∈ E) {ℓ : ℕ} (P : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K)
    (hP : ∀ j, P j ∈ vanish E) :
    ∃ (d : Fin m → ℕ) (P' : Fin ℓ → MvPolynomial (Var d₀ d₁ m) K), (∀ j, IsHomE (P' j) d) ∧
      (∀ j, P' j ∈ vanish E) ∧ ∀ (ch : Fin m → Fin 3) (w : LieE K d₀ d₁ m) j,
        eval (coords (0 : GPt K d₀ d₁ g₂ g₃) 1) (Dh g₂ g₃ ch w (P' j)) =
          eval (coords (0 : GPt K d₀ d₁ g₂ g₃) 1) (Dh g₂ g₃ ch w (P j)) := by
  classical
  set a0 := coords (0 : GPt K d₀ d₁ g₂ g₃) 1
  set cp : (Fin m → ℕ) → MvPolynomial (Var d₀ d₁ m) K → MvPolynomial (Var d₀ d₁ m) K :=
    fun e Q => weightedHomogeneousComponent wV e Q
  let Sj : Fin ℓ → Finset (Fin m → ℕ) := fun j =>
    (weightedHomogeneousComponent_finsupp (w := (wV : Var d₀ d₁ m → Fin m → ℕ)) (P j)).toFinset
  let S : Finset (Fin m → ℕ) := Finset.univ.biUnion Sj
  let d : Fin m → ℕ := ∑ e ∈ S, e
  have hle : ∀ e ∈ S, e ≤ d := fun e he => Finset.single_le_sum (f := fun e => e) (fun _ _ => zero_le) he
  have hsumP : ∀ j, P j = ∑ e ∈ S, cp e (P j) := by
    intro j
    conv_lhs => rw [← finsum_weightedHomogeneousComponent wV (P j)]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro e he
    have : e ∈ Sj j := (Set.Finite.mem_toFinset _).mpr he
    exact Finset.mem_coe.mpr (Finset.subset_biUnion_of_mem Sj (Finset.mem_univ j) this)
  have hcpv : ∀ e j, cp e (P j) ∈ vanish E := fun e j => multiComp_mem_vanish e (hP j)
  have ha0 : ∀ Q ∈ vanish E, eval a0 Q = 0 := fun Q hQ => mem_vanish.mp hQ 0 h0 1
  have hVpow : ∀ e, eval a0 (Vpow e : MvPolynomial (Var d₀ d₁ m) K) = 1 := by
    intro e
    simp [Vpow, a0, eval_coords_zero_e1]
  refine ⟨d, fun j => ∑ e ∈ S, Vpow (d - e) * cp e (P j), fun j => ?_, fun j => ?_,
    fun ch w j => ?_⟩
  · rw [← mem_homSub]
    refine Submodule.sum_mem _ fun e he => mem_homSub.mpr ?_
    have := (isHomE_Vpow (K := K) (d₀ := d₀) (d₁ := d₁) (d - e)).mul'
      (isHomE_of_wV (weightedHomogeneousComponent_isWeightedHomogeneous e (P j)))
    rwa [tsub_add_cancel_of_le (hle e he)] at this
  · exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (hcpv e j)
  · conv_rhs => rw [hsumP j]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul, hVpow,
      ha0 _ (hcpv _ j), one_mul, zero_mul, add_zero]

end HomLift

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

/-! ### The pairing at the identity -/

variable (Ls) in
/-- The identity's cone point `coords 0 1`. -/
noncomputable abbrev aId (d₀ d₁ : ℕ) : Var d₀ d₁ m → ℂ :=
  coords (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) 1

/-- `lieAlg H⁰ = lieAlg H` (as in `SubgroupHilb.mem_lieAlg_H0`, which is not imported here because
`LSG.ME.SmoothDeriv` and `LSG.ME.Order` both declare `LSG.ME.derivation_aeval`). -/
theorem wmem_lieAlg_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) {v : Tan d₀ d₁ m} :
    v ∈ lieAlg Ls (H0_isSubgroup hH hc) (isZClosed_H0 hH hc) ↔ v ∈ lieAlg Ls hH hc := by
  rw [mem_lieAlg, mem_lieAlg]
  constructor
  · intro h c; exact mem_Htil.mpr (H0_subset hH hc (mem_Htil.mp (h c)))
  · intro h c
    exact mem_Htil.mpr (expG_mem_H0 hH hc (mem_lieAlg.mpr fun c' => by
      rw [smul_smul]; exact h _))

theorem eval_mult_one_a0 (v : Var d₀ d₁ m) :
    eval (aId Ls d₀ d₁) (mult (K := ℂ) (fun _ => 1) v) = 1 := by
  have hV : ∀ j : Fin m, eval (aId Ls d₀ d₁) (X (.e j 1) : MvPolynomial (Var d₀ d₁ m) ℂ) = 1 :=
    fun j => by simp [eval_coords_zero_e1]
  cases v <;> simp [mult, Lc, Lo, hV]

/-- At `a0`, `D̂_w` (`V`-charts) agrees with the chart derivation used in `TZ`. -/
theorem eval_Dh_one_a0 (w : Tan d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (aId Ls d₀ d₁) (Dh (g2L Ls) (g3L Ls) (fun _ => 1) w P) =
      eval (aId Ls d₀ d₁) (Dw (g2L Ls) (g3L Ls) (chartAt (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) w P) := by
  rw [chartAt_zero, Dh, Dw, mkDerivation_eq_sum, mkDerivation_eq_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [dvalh, map_mul, eval_mult_one_a0, one_mul]

variable (Ls) in
/-- The pairing `(w, P) ↦ D̂_w P (0)` on `Lie G × I(H⁰)`. -/
noncomputable def pairing0 (V : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) :
    Tan d₀ d₁ m →ₗ[ℂ] ↥((vanish V).restrictScalars ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun w P => eval (aId Ls d₀ d₁) (Dh (g2L Ls) (g3L Ls) (fun _ => 1) w P))
    (fun w w' P => by rw [Dh_add_apply, map_add])
    (fun a w P => by rw [Dh_smul_apply, smul_eval, smul_eq_mul])
    (fun w P P' => by rw [Submodule.coe_add, map_add, map_add])
    (fun a w P => by rw [Submodule.coe_smul, Derivation.map_smul, smul_eval, smul_eq_mul])

theorem pairing0_apply (V : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) (w : Tan d₀ d₁ m)
    (P : ↥((vanish V).restrictScalars ℂ)) :
    pairing0 Ls V w P = eval (aId Ls d₀ d₁) (Dh (g2L Ls) (g3L Ls) (fun _ => 1) w P) := rfl

theorem ker_pairing0_le (hH : IsSubgroupG H) (hc : IsZClosed H) :
    LinearMap.ker (pairing0 Ls (H0 Ls hH hc)) ≤ lieAlg Ls hH hc := by
  intro w hw
  rw [← wmem_lieAlg_H0 hH hc, ← mem_TZ_iff (H0_isSubgroup hH hc) (isZClosed_H0 hH hc)]
  refine mem_TZ.mpr fun P hP => ?_
  have := LinearMap.congr_fun (LinearMap.mem_ker.mp hw) ⟨P, hP⟩
  rw [pairing0_apply, eval_Dh_one_a0] at this
  exact this

/-! ### Identity data -/

/-- **Transversal data at the identity.** -/
theorem exists_identity_data (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → Tan d₀ d₁ m)
      (T : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (N : MvPolynomial (Var d₀ d₁ m) ℂ) (d : Fin m → ℕ),
      (∀ i, w i ∈ W) ∧ (∀ j, IsHomE (T j) d) ∧ (∀ j, T j ∈ vanish (H0 Ls hH hc)) ∧
      N ∉ vanish (H0 Ls hH hc) ∧
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
  refine ⟨w, fun j => ∑ k, P k * A.adjugate k j, A.det, d + (ℓ - 1) • (d + 1), hwW,
    fun j => ?_, fun j => Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hPV k),
    fun hmem => ?_, fun i j => ?_⟩
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

/-! ### Transversals for finitely many cosets of `H⁰` -/

/-- **Wüstholz transversals for a finite union of cosets of `H⁰`.** -/
theorem exists_transversals (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) (R : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH hc) :
    ∃ (w : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → Tan d₀ d₁ m)
      (B : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (Q : Fin (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) → MvPolynomial (Var d₀ d₁ m) ℂ)
      (M : MvPolynomial (Var d₀ d₁ m) ℂ),
      (∀ i, w i ∈ W) ∧ (∀ j, Q j ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) ∧
      (∀ i j, (∑ a ∈ R, B a • Dh (g2L Ls) (g3L Ls) (chartAt a) (w i)) (Q j) -
        (if i = j then M else 0) ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) ∧
      ∀ x, M * x ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc)) →
        x ∈ vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc)) := by
  classical
  obtain ⟨w, T, N, d, hwW, hTh, hT, hN, hTδ⟩ := exists_identity_data hH hc W
  obtain ⟨B, Q, M, hQ, hδ, hM⟩ := transversals_of_identity two_ne_zero (discr_g2L Ls)
    (isZClosed_H0 hH hc) (vanish_H0_isPrime hH hc) (H0_isSubgroup hH hc).zero_mem w T N hTh hT hN
    hTδ R fun a ha b hb hab => not_gtransl_subset (H0_isSubgroup hH hc) (hdist a ha b hb hab)
  exact ⟨w, B, Q, M, hwW, hQ, hδ, hM⟩

/-! ### Orders of vanishing in mixed charts -/

variable (Ls) in
/-- All homogenised derivations, indexed by (chart, direction). -/
noncomputable def Dmix (p : (Fin m → Fin 3) × Tan d₀ d₁ m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  Dh (g2L Ls) (g3L Ls) p.1 p.2

/-- The index set of `W`-directions in all charts. -/
def Wmix (W : Submodule ℂ (Tan d₀ d₁ m)) : Set ((Fin m → Fin 3) × Tan d₀ d₁ m) := {p | p.2 ∈ W}

/-- Mixed-chart words lower the canonical order by their length (homogeneous `x`). -/
theorem DLmix_mem_VO1 (W : Submodule ℂ (Tan d₀ d₁ m)) {g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)}
    (l : List ((Fin m → Fin 3) × Tan d₀ d₁ m)) (hlW : ∀ p ∈ l, p ∈ Wmix W) :
    ∀ {b : ℕ} {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}, IsHomE x d →
      x ∈ VO1 (g2L Ls) (g3L Ls) (chartAt g) W (l.length + b) (vanish {g}) →
      DL (Dmix Ls) l x ∈ VO1 (g2L Ls) (g3L Ls) (chartAt g) W b (vanish {g}) := by
  induction l with
  | nil => intro b x d _ hxv; simpa using hxv
  | cons p l ih =>
    intro b x d hx hxv
    rw [DL_cons]
    refine ih (fun q hq => hlW q (List.mem_cons_of_mem _ hq)) (isHomE_Dh hx p.1 p.2) ?_
    refine Dh_mem_VO1_chartAt two_ne_zero W hx ?_ p.1 (hlW p List.mem_cons_self)
    simpa [List.length_cons, add_assoc, add_comm 1] using hxv

/-- **Canonical order at every point of `E` ⇒ order modulo `I(E)` in all charts.** -/
theorem mem_VOg_mix (W : Submodule ℂ (Tan d₀ d₁ m)) {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}
    {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hx : IsHomE x d) {n : ℕ}
    (hv : ∀ g ∈ E, VanCan (g2L Ls) (g3L Ls) W x n g) :
    x ∈ VOg (Dmix Ls) (Wmix W) (vanish E) n := by
  intro l hlW hl
  refine mem_vanish.mpr fun g hg lam => ?_
  have h1 := DLmix_mem_VO1 W l hlW hx (b := 0) (VOg_anti (by omega) (hv g hg))
  exact mem_vanish_singleton.mp (mem_VOg_zero.mp h1) lam

/-! ### Wüstholz's lemma for a finite union of cosets of `H⁰` -/

/-- **Wüstholz's lemma for `I(E)`, `E` a finite union of distinct cosets of `H⁰`**:
`(k+1)^ℓ · H(I(E); t) ≤ H(A; t + S₀ c₀)` for every ideal `A` vanishing to order `> S₀` modulo
`I(E)` along `W` (words in all charts), `ℓ k ≤ S₀`, with `c₀` independent of `A`, `S₀`, `k`, `t`. -/
theorem wustholz_cosets (hH : IsSubgroupG H) (hc : IsZClosed H)
    (W : Submodule ℂ (Tan d₀ d₁ m)) (R : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH hc) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) * k ≤ S0 →
      A ≤ VOg (Dmix Ls) (Wmix W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) S0 → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlg Ls hH hc)) *
          hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) t ≤
        hfun blk D ℂ A (t + S0 * c0) := by
  classical
  obtain ⟨w, B, Q, M, hwW, hQ, hδ, hM⟩ := exists_transversals hH hc W R hdist
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' blk hD Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  set Dv := fun i => ∑ a ∈ R, B a • Dh (g2L Ls) (g3L Ls) (chartAt a) (w i)
  have hD' : ∀ i (n : ℕ) x, x ∈ VOg (Dmix Ls) (Wmix W)
      (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) (n + 1) →
      Dv i x ∈ VOg (Dmix Ls) (Wmix W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH hc))) n :=
    fun i n x hx => glued_mem_VOg (Dv := Dmix Ls) R B (fun a => (chartAt a, w i))
      (fun a _ => hwW i) hx
  exact wustholzM' blk D Dv hQ hδ hM hQdeg hk
    (fun x hx l hl => DL_glued_mem Dv hD' l (hA hx) hl) t

end LSG.ME
