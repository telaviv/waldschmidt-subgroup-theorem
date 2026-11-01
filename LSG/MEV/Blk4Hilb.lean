import Mathlib
import LSG.MEV.Blk4
import LSG.MEV.MainVecAux

/-!
# Hilbert-function layers in the 4-block grading (STAGE5_MEV §10.3)

Copies, with `blk4 ct` in place of `blk`, of: `hfun_le_of_hom` (`Slice`), `hfun_le_transl`
(`TranslHF`), `prod_three_le`, `hfun_sum_cosets_P` (`SliceCoset`), `hfun_P_transl_ge_c`,
`hfun_cosets_ge_c` (`MainVecAux`), `wustholz_sl_of_dataV` (`SliceWustV`), `wustholz_cosets_slV`
(`SliceWustVCoset`). Only the degree bookkeeping changes (`Dcut4`, `comp_mem_FLE4`,
`lsl_mem_FLE4`, `transl_mem_FLE4`, `tpl4_le`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk VOg VOg_succ_le Nsub hfun_eq_finrank_quotient
  finrank_quotient_le_of_ker_le fle_X
  fle_add)
open StrongSix.M2 (FLE hfun hdata HasData finrank_comap_subtype)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} (ct : ℕ)

/-! ### Degree helpers -/

theorem bdeg4_e_eq_weight (s : Var d₀ d₁ m →₀ ℕ) (k : Fin m) :
    StrongSix.M2.bdeg (blk4 ct) s (.e k) = Finsupp.weight wtV s k := by
  rw [← bdeg_e_eq_weight]
  unfold StrongSix.M2.bdeg
  refine Finset.sum_congr rfl fun v _ => ?_
  cases v with
  | x i => simp only [blk4_x, blk_x]; split_ifs <;> simp
  | _ => simp [blk4, blk]

/-- The block degrees with the elliptic ones replaced by `e`. -/
def Dcut4 (t : ℕ) (D : Blk4 m → ℕ) (e : Fin m → ℕ) : Blk4 m → ℕ
  | .xl => t * D .xl
  | .xt => t * D .xt
  | .yz => t * D .yz
  | .e k => e k

theorem comp_mem_FLE4 {t : ℕ} {D : Blk4 m → ℕ} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ FLE ℂ (blk4 ct) (t • D)) (e : Fin m → ℕ) :
    weightedHomogeneousComponent wtV e P ∈ FLE ℂ (blk4 ct) (Dcut4 t D e) := by
  classical
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at hP ⊢
  intro s hs
  rw [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hs
  split_ifs at hs with hw
  · have hS := hP (MvPolynomial.mem_support_iff.mpr hs)
    intro b
    cases b with
    | xl => exact hS .xl
    | xt => exact hS .xt
    | yz => exact hS .yz
    | e k => rw [bdeg4_e_eq_weight, hw]; rfl
  · exact absurd rfl hs

theorem lsl_mem_FLE4 (α : Fin m → ℂ) (k : Fin m) :
    lsl (d₀ := d₀) (d₁ := d₁) α k ∈ FLE ℂ (blk4 ct) (Pi.single (Blk4.e k) 1) :=
  fle4_of_fle ct (fun b => by cases b <;> simp [Pi.single_apply, b4to3]) (lsl_mem_FLE α k)

theorem tpl4_le (D : Blk4 m → ℕ) (t : ℕ) : tpl4 (t • D) ≤ (3 * t) • D := fun b => by
  simp only [tpl4, Pi.smul_apply, smul_eq_mul]
  have := bmul4_le_three b
  calc bmul4 b * (t * D b) ≤ 3 * (t * D b) := Nat.mul_le_mul_right _ this
    _ = 3 * t * D b := by ring

/-! ### The copies -/

/-- **Slicing loses at most `∏ (t D_k + 1)`**, for any ideal `I` whose multihomogeneous elements lie
in `vanish E` (`vanish E` prime, all `ℓ_k ∉ vanish E`):
`H(vanish E; t) ≤ ∏_k (t D_k + 1) · H(I; t)`. -/
theorem hfun_le_of_hom4 (α : Fin m → ℂ) {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    (I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ))
    (hI : ∀ (Q : MvPolynomial (Var d₀ d₁ m) ℂ) (d : Fin m → ℕ), IsWeightedHomogeneous wtV Q d →
      Q ∈ I → Q ∈ vanish E) (D : Blk4 m → ℕ) (t : ℕ) :
    hfun (blk4 ct) D ℂ (vanish E) t ≤ (∏ k, (t * D (.e k) + 1)) * hfun (blk4 ct) D ℂ I t := by
  classical
  set F := FLE ℂ (blk4 ct) (t • D)
  set N : Fin m → ℕ := fun k => t * D (.e k)
  let Ix := (k : Fin m) → Fin (N k + 1)
  let ev : Ix → (Fin m → ℕ) := fun e k => (e k : ℕ)
  let L : Ix → MvPolynomial (Var d₀ d₁ m) ℂ := fun e =>
    ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ^ (N k - ev e k)
  have hLmem : ∀ e (P : MvPolynomial (Var d₀ d₁ m) ℂ), P ∈ F →
      L e * weightedHomogeneousComponent wtV (ev e) P ∈ F := by
    intro e P hP
    have h1 : L e ∈ FLE ℂ (blk4 ct) (∑ k, (N k - ev e k) • Pi.single (Blk4.e k) 1) :=
      StrongSix.M2.prod_mem_FLE' _ _ _ fun k _ => StrongSix.M2.pow_mem_FLE' (lsl_mem_FLE4 ct α k) _
    refine StrongSix.M2.FLE_mono ℂ (blk4 ct) (fun b => ?_)
      (StrongSix.M2.mul_mem_FLE ℂ h1 (comp_mem_FLE4 ct hP (ev e)))
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    cases b with
    | xl => simp [Dcut4]
    | xt => simp [Dcut4]
    | yz => simp [Dcut4]
    | e k =>
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      have := (e k).isLt
      have hN : N k = t * D (.e k) := rfl
      simp only [ite_true, mul_one, Dcut4, ev]
      omega
  let φ : Ix → F →ₗ[ℂ] F := fun e =>
    ((LinearMap.mulLeft ℂ (L e) ∘ₗ (weightedHomogeneousComponent wtV (ev e)).restrictScalars ℂ) ∘ₗ
      F.subtype).codRestrict F fun P => hLmem e P P.2
  let Φ : F →ₗ[ℂ] (Ix → F ⧸ Nsub (K := ℂ) (blk4 ct) D I t) :=
    LinearMap.pi fun e => (Nsub (K := ℂ) (blk4 ct) D I t).mkQ ∘ₗ φ e
  have hker : LinearMap.ker Φ ≤ Nsub (K := ℂ) (blk4 ct) D (vanish E) t := by
    intro P hP
    have hcomp : ∀ e, weightedHomogeneousComponent wtV (ev e) (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
        vanish E := by
      intro e
      have h0 := congrFun (LinearMap.mem_ker.mp hP) e
      simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hs : L e * weightedHomogeneousComponent wtV (ev e) (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈
          I := h0
      have hhom : IsWeightedHomogeneous wtV (L e * weightedHomogeneousComponent wtV (ev e)
          (P : MvPolynomial (Var d₀ d₁ m) ℂ)) (∑ k, (N k - ev e k) • Pi.single k 1 + ev e) :=
        (IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_lsl α k).pow _).mul
          (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      have hv := hI _ _ hhom hs
      have hL : L e ∉ vanish E := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
        exact hℓ k (hp.mem_of_pow_mem _ hk)
      exact (hp.mem_or_mem hv).resolve_left hL
    have hsum : (P : MvPolynomial (Var d₀ d₁ m) ℂ) =
        ∑ e : Ix, weightedHomogeneousComponent wtV (ev e) P := by
      ext s
      rw [coeff_sum]
      simp only [coeff_weightedHomogeneousComponent]
      by_cases hs : (P : MvPolynomial (Var d₀ d₁ m) ℂ).coeff s = 0
      · simp [hs]
      have hsS : s ∈ StrongSix.M2.S (blk4 ct) (t • D) := by
        have h' : (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ FLE ℂ (blk4 ct) (t • D) := P.2
        rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at h'
        exact h' (MvPolynomial.mem_support_iff.mpr hs)
      have hb : ∀ k, Finsupp.weight wtV s k < N k + 1 := fun k => by
        have := hsS (.e k)
        rw [bdeg4_e_eq_weight ct] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact Nat.lt_succ_of_le this
      let e₀ : Ix := fun k => ⟨Finsupp.weight wtV s k, hb k⟩
      rw [Finset.sum_eq_single e₀ (fun e _ he => ite_eq_right_iff.mpr fun hw =>
          absurd (funext fun k => Fin.ext (congrFun hw k).symm) he) (by simp)]
      simp only [↓reduceIte]
    change (P : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ vanish E
    rw [hsum]
    exact Ideal.sum_mem _ fun e _ => hcomp e
  have h := finrank_quotient_le_of_ker_le Φ hker
  rw [← hfun_eq_finrank_quotient, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    ← hfun_eq_finrank_quotient] at h
  have hcard : Fintype.card Ix = ∏ k, (t * D (.e k) + 1) := by
    simp [Ix, Fintype.card_pi, N]
  rw [← hcard]
  calc hfun (blk4 ct) D ℂ (vanish E) t ≤ Fintype.card Ix • hfun (blk4 ct) D ℂ I t := h
    _ = _ := smul_eq_mul _ _

set_option maxSynthPendingDepth 10 in
/-- **Hilbert functions of translates**, with constant loss `8^m` and `t ↦ 3t`. -/
theorem hfun_le_transl4 (D : Blk4 m → ℕ) (E : Set (GPtV d₀ d₁ Ls)) (g : GPtV d₀ d₁ Ls) (t : ℕ) :
    hfun (blk4 ct) D ℂ (vanish E) t ≤
      8 ^ m * hfun (blk4 ct) D ℂ (vanish (gtransl g E)) (3 * t) := by
  set F₁ := FLE ℂ (blk4 ct) (t • D)
  set F₂ := FLE ℂ (blk4 ct) ((3 * t) • D)
  set E' := gtransl g E
  set N : Submodule ℂ F₂ := ((vanish E').restrictScalars ℂ).comap F₂.subtype
  have hτ : ∀ c, ∀ P ∈ F₁, τ Ls (-g) c P ∈ F₂ := fun c P hP =>
    LSG.ME.fle_le (transl_mem_FLE4 ct (-g) c hP) (tpl4_le D t)
  let φ : (Fin m → LC) → (F₁ →ₗ[ℂ] F₂ ⧸ N) := fun c =>
    N.mkQ ∘ₗ ((τ Ls (-g) c).toLinearMap.restrict (hτ c))
  let Ψ : F₁ →ₗ[ℂ] ((Fin m → LC) → F₂ ⧸ N) := LinearMap.pi φ
  have hker : LinearMap.ker Ψ ≤ ((vanish E).restrictScalars ℂ).comap F₁.subtype := by
    intro x hx
    have hc : ∀ c, τ Ls (-g) c (x : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ vanish E' := by
      intro c
      have := congrFun (LinearMap.mem_ker.mp hx) c
      simp only [Ψ, φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    refine mem_vanish.mpr fun e he ν => ?_
    have hh : e + g ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨c, hgood⟩ := exists_good (e + g) (-g)
    obtain ⟨μ, hμ⟩ := eval_transl_good hgood
    obtain ⟨lam, hlam⟩ := exists_cube_mul μ ν
    have := mem_vanish.mp (hc c) (e + g) hh lam
    rw [hμ, hlam, add_neg_cancel_right] at this
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 : finrank ℂ (LinearMap.range Ψ) ≤ finrank ℂ ((Fin m → LC) → F₂ ⧸ N) :=
    Submodule.finrank_le _
  have e3 : finrank ℂ ((Fin m → LC) → F₂ ⧸ N) = 8 ^ m * finrank ℂ (F₂ ⧸ N) := by
    have hfr := Module.finrank_pi_fintype ℂ (ι := Fin m → LC) (M := fun _ => ↥F₂ ⧸ N)
    rw [hfr, Finset.sum_const, Finset.card_univ, card_LC_fun, smul_eq_mul]
  have e4 : finrank ℂ (F₂ ⧸ N) = hfun (blk4 ct) D ℂ (vanish E') (3 * t) := by
    have := Submodule.finrank_quotient_add_finrank N
    rw [finrank_comap_subtype, inf_comm] at this
    change finrank ℂ (F₂ ⧸ N) = finrank ℂ F₂ - finrank ℂ ↥((vanish E').restrictScalars ℂ ⊓ F₂)
    omega
  have e5 : finrank ℂ (LinearMap.ker Ψ) ≤ finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := by
    have := Submodule.finrank_mono hker
    rwa [finrank_comap_subtype, inf_comm] at this
  have e6 : hfun (blk4 ct) D ℂ (vanish E) t =
      finrank ℂ F₁ - finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := rfl
  rw [e6, ← e4]
  omega

theorem prod_three_le4 (D : Blk4 m → ℕ) (t : ℕ) :
    ∏ k : Fin m, (3 * t * D (.e k) + 1) ≤ 3 ^ m * ∏ k : Fin m, (t * D (.e k) + 1) := by
  calc ∏ k : Fin m, (3 * t * D (.e k) + 1) ≤ ∏ k : Fin m, (3 * (t * D (.e k) + 1)) :=
        Finset.prod_le_prod fun k _ => by nlinarith
    _ = 3 ^ m * ∏ k : Fin m, (t * D (.e k) + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The sliced coset sum** (S5). -/
theorem hfun_sum_cosets_P4 (D : Blk4 m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → ℂ)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun (blk4 ct) D ℂ (vanishP Finset.univ α (gtransl a V)) t ≤
      hfun (blk4 ct) D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (t + c) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih (fun x hx k => hα x (Finset.mem_insert_of_mem hx) k)
      fun x hx y hy hxy =>
        hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hα' := hα a (Finset.mem_insert_self a s)
    have hpa := vanish_gtransl_isPrime hV hp a
    obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa hα'
    have hPa := vanishP_isPrime (s := Finset.univ) hpa (fun k _ => hα' k) hg₀ (fun k _ => hs₀ k)
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanishP Finset.univ α (gtransl a V) := by
      intro b hb
      have hns := hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
      obtain ⟨x, hxa, hxb⟩ := Set.not_subset.mp hns
      obtain ⟨Q, hQb, ⟨d, hd⟩, hQx⟩ := exists_homogVanish_ne (isZClosed_gtransl hV b) hxb
      refine ⟨Q, hQb, fun hQa => ?_⟩
      have := hom_mem_vanish_of_mem_vanishP hpa hα' hd hQa
      exact hQx 1 (mem_vanish.mp this x hxa 1)
    choose! f hfb hfa using hsep
    set B := ∏ b ∈ s, f b
    have hBs : B ∈ vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) := by
      rw [mem_vanishP_biUnion]
      intro b hb
      rw [show B = f b * ∏ x ∈ s.erase b, f x from (Finset.mul_prod_erase s f hb).symm]
      exact Ideal.mul_mem_right _ _ (vanish_le_vanishP _ α _ (hfb b hb))
    have hBa : B ∉ vanishP Finset.univ α (gtransl a V) := by
      intro h
      obtain ⟨b, hb, hfb'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPa)).mp h
      exact hfa b hb hfb'
    have hnzd : ∀ x, B * x ∈ vanishP Finset.univ α (gtransl a V) →
        x ∈ vanishP Finset.univ α (gtransl a V) := fun x hx =>
      (hPa.mem_or_mem hx).resolve_left hBa
    have hBdeg := StrongSix.M2.mem_FLE_totalDegree (blk4 ct) D ℂ hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : vanishP Finset.univ α (⋃ x ∈ insert a s, gtransl x V) =
        vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) ⊓ vanishP Finset.univ α (gtransl a V) := by
      ext P
      simp only [Submodule.mem_inf, mem_vanishP_biUnion, Finset.forall_mem_insert]
      exact and_comm
    have h1 := LSG.ME.hfun_inter_ge (blk4 ct) D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, Finset.sum_insert ha]
    have := hc t
    omega

theorem hfun_P_transl_ge_c4 (D : Blk4 m → ℕ) {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (a : GPtV d₀ d₁ Ls) (α : Fin m → ℂ)
    (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a V)) (L : ℕ → ℕ) (c : ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ c * hfun (blk4 ct) D ℂ (vanish V) t)
    (t : ℕ) :
    L t ≤ c * 24 ^ m * hfun (blk4 ct) D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
  have hpa := vanish_gtransl_isPrime hV hp a
  have h2 := hfun_le_transl4 ct D V a t
  have h3 := hfun_le_of_hom4 ct α hpa hℓ _
    (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs)
    D (3 * t)
  set P := ∏ k : Fin m, (t * D (.e k) + 1)
  set hP := hfun (blk4 ct) D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t)
  have hP0 : 0 < P := Finset.prod_pos fun k _ => Nat.succ_pos _
  have h4 := prod_three_le4 D t
  have hchain : L t * P ≤ c * 24 ^ m * hP * P := by
    calc L t * P ≤ c * hfun (blk4 ct) D ℂ (vanish V) t := hL t
      _ ≤ c * (8 ^ m * hfun (blk4 ct) D ℂ (vanish (gtransl a V)) (3 * t)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ c * (8 ^ m * ((∏ k : Fin m, (3 * t * D (.e k) + 1)) * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ ≤ c * (8 ^ m * ((3 ^ m * P) * hP)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4))
      _ = c * 24 ^ m * hP * P := by
          rw [show (24 : ℕ) ^ m = 8 ^ m * 3 ^ m by rw [← mul_pow]; norm_num]; ring
  exact Nat.le_of_mul_le_mul_right hchain hP0

/-- **The sliced coset count** with a constant `c` in the unsliced lower bound. -/
theorem hfun_cosets_ge_c4 (D : Blk4 m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → ℂ)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) (L : ℕ → ℕ) (c : ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ c * hfun (blk4 ct) D ℂ (vanish V) t) :
    ∃ c' : ℕ, ∀ t, R.card * L t ≤
      c * 24 ^ m *
        hfun (blk4 ct) D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (3 * t + c') := by
  obtain ⟨c', hc'⟩ := hfun_sum_cosets_P4 ct D hD α hV hp R hα hdist
  refine ⟨c', fun t => ?_⟩
  calc R.card * L t = ∑ _a ∈ R, L t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ R, c * 24 ^ m * hfun (blk4 ct) D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) :=
        Finset.sum_le_sum fun a ha => hfun_P_transl_ge_c4 ct D hV hp a α (hα a ha) L c hL t
    _ = c * 24 ^ m * ∑ a ∈ R, hfun (blk4 ct) D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
        rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (hc' (3 * t))

/-- **Sliced Wüstholz lemma from glued data** (vector extensions). `J` is stable under the Euler
derivations; `Dᵢ Qⱼ ≡ δᵢⱼ M (mod J)`, `Qⱼ ∈ J`, `M` a non-zero-divisor modulo `sl α J`; the `Dᵢ`
lower the order `VOg Dw Ws J` by one and `[Eul_k, Dw] = 2 Dw`. Then for `A ≤ VOg Dw Ws J S₀` and
`ℓ k ≤ S₀`: `(k+1)^ℓ · H(sl α J; t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_sl_of_dataV4 (α : Fin m → ℂ) (D : Blk4 m → ℕ) {ℓ : ℕ}
    (Dv : Fin ℓ → Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    {J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hJE : ∀ k, ∀ x ∈ J, EulV k x ∈ J)
    {Q : Fin ℓ → MvPolynomial (Var d₀ d₁ m) ℂ} {M : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : ∀ j, Q j ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then M else 0) ∈ J)
    (hM : ∀ x, M * x ∈ sl α J → x ∈ sl α J) {c0 : ℕ} (hQdeg : ∀ j, Q j ∈ FLE ℂ (blk4 ct) (c0 • D))
    {ι' : Type*}
    {Dw : ι' → Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ)}
    {Ws : Set ι'} (hcomm : ∀ k i x, EulV k (Dw i x) = Dw i (EulV k x) + 2 • Dw i x)
    (hDv : ∀ i (n : ℕ) x, x ∈ VOg Dw Ws J (n + 1) → Dv i x ∈ VOg Dw Ws J n)
    {S0 k : ℕ} (hk : ℓ * k ≤ S0) {A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)}
    (hA : A ≤ VOg Dw Ws J S0) (t : ℕ) :
    (k + 1) ^ ℓ * hfun (blk4 ct) D ℂ (sl α J) t ≤ hfun (blk4 ct) D ℂ (sl α A) (t + S0 * c0) := by
  classical
  set D' := fun i => DslV α (Dv i)
  have hEV : ∀ k' (n : ℕ) x, x ∈ VOg Dw Ws J n → EulV k' x ∈ VOg Dw Ws J n :=
    fun k' => eul2_mem_VOg (EulV k') (hJE k') (hcomm k')
  have hD' : ∀ i (n : ℕ) x, x ∈ VOg Dw Ws J (n + 1) → D' i x ∈ VOg Dw Ws J n := by
    intro i n x hx
    simp only [D', DslV_apply]
    refine sub_mem (hDv i n x hx) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ ?_)
    exact VOg_succ_le n (hEV k' (n + 1) x hx)
  have hJsl := le_sl α J
  refine LSG.ME.wustholzM' (blk4 ct) D D' (fun j => hJsl (hQ j)) (fun i j => hJsl ?_) hM hQdeg hk
    ?_ t
  · have e : D' i (Q j) - (if i = j then M else 0) =
        (Dv i (Q j) - (if i = j then M else 0)) - ∑ k', Dv i (lsl α k') * EulV k' (Q j) := by
      simp only [D', DslV_apply]; ring
    rw [e]
    exact sub_mem (hδ i j) (Ideal.sum_mem _ fun k' _ => Ideal.mul_mem_left _ _ (hJE k' _ (hQ j)))
  · intro x hx l hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact add_mem (hJsl (LSG.ME.DL_glued_mem D' hD' l (hA hy) hl))
      (LslV_le_sl α J (DL_DslV_mem_Lsl α Dv l hz))
section Trans

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **Sliced Wüstholz lemma for `E = ⋃_{a ∈ R} (a + H⁰)`** (vector extensions): for `α` with
`ℓ_k ∉ I(a + H⁰)` (`a ∈ R`, all `k`) there is `c₀` such that for every ideal `A` vanishing to order
`> S₀` modulo `I(E)` along `W` in all charts and `ℓ k ≤ S₀`:
`(k+1)^ℓ · H(sl α I(E); t) ≤ H(sl α A; t + S₀ c₀)`. -/
theorem wustholz_cosets_slV4 (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ H0 Ls hH) (D : Blk4 m → ℕ) (hD : ∀ i, 1 ≤ D i)
    (α : Fin m → ℂ) (hℓ : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH))) :
    ∃ c0 : ℕ, ∀ (A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) (S0 k : ℕ),
      (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) * k ≤ S0 →
      A ≤ VOg (DmixV Ls) (WmixV W) (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH))) S0 → ∀ t,
      (k + 1) ^ (finrank ℂ W - finrank ℂ ↥(W ⊓ lieAlgL Ls hH)) *
          hfun (blk4 ct) D ℂ (sl α (vanish (⋃ a ∈ R, gtransl a (H0 Ls hH)))) t ≤
        hfun (blk4 ct) D ℂ (sl α A) (t + S0 * c0) := by
  classical
  obtain ⟨w, B, Q, M, μ, hwW, hQ, hδ, hMh, hMn⟩ := exists_transversals_slV hH hc W R hdist α hℓ
  obtain ⟨c0, hQdeg⟩ := StrongSix.M2.exists_c0' (blk4 ct) hD Q
  refine ⟨c0, fun A S0 k hk hA t => ?_⟩
  have hpC : ∀ a ∈ R, (vanish (gtransl a (H0 Ls hH))).IsPrime := fun a _ =>
    vanish_gtransl_isPrime (isZClosed_H0 hH) (vanish_H0_isPrime hH) a
  exact wustholz_sl_of_dataV4 ct α D (fun i => ∑ a ∈ R, B a • Dhc Ls (chartsV a) (w i))
    (fun k x hx => EulV_mem_vanish k hx) hQ hδ
    (nzd_slV α R (fun a => gtransl a (H0 Ls hH)) hpC hℓ hMh hMn) hQdeg
    (Dw := DmixV Ls) (Ws := WmixV W) (fun k p x => EulV_Dhc k p.1 p.2 x)
    (fun i n x hx => LSG.ME.glued_mem_VOg (Dv := DmixV Ls) R B (fun a => (chartsV a, w i))
      (fun a _ => hwW i) hx) hk hA t

end Trans

end

end LSG.MEV
