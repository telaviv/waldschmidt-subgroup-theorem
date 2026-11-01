import Mathlib
import LSG.ME.Order

/-!
# Translation invariance of the order of vanishing (STAGE2 §3)

* `isHomE_transl`: `τ g c` doubles all elliptic degrees of a homogeneous polynomial.
* `tr_id` (**translation identity**): for charts `ch`, `ch'` with values in `{V, W}` and `Q`
  homogeneous of degrees `d`:
  `τ(Lc ch') · Dh_ch(τ Q) − Lc ch · τ(Dh_{ch'} Q) − Σₖ teₖ · dₖ · τ Q ∈ I_G`
  (analytically: the invariant derivation commutes with translations; the generated identities
  `tr_eq_cab` of `LSG.ME.OrderId` are the elliptic case).
* `transl_good`: for a good law choice `c` at `(h, g)`, `τ g c` maps order `> n` along `W` at
  `h + g` (canonical charts) to order `> n` at `h`.
* `cong_laws` (Nullstellensatz + `law₁_cross_law₂`): for homogeneous `Q`, `τ g c Q` and
  `τ g c' Q` agree modulo `I_G` up to the factors `∏ₖ τ(Lₖ)^{dₖ}`.
* **`transl_van`**: the same for **every** law choice `c` (`K` algebraically closed).
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (DL DL_cons)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Homogeneity of translates -/

section Hom

variable {σ : Type*}

theorem isWH_aeval {w : σ → ℕ} {f : σ → MvPolynomial σ K} {c n : ℕ}
    (hf : ∀ v, (f v).IsWeightedHomogeneous w (c * w v)) {P : MvPolynomial σ K}
    (hP : P.IsWeightedHomogeneous w n) : (aeval f P).IsWeightedHomogeneous w (c * n) := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hw : Finsupp.weight w d = n := hP (mem_support_iff.mp hd)
  rw [aeval_monomial, algebraMap_eq]
  have h := IsWeightedHomogeneous.prod d.support (fun v => f v ^ d v) (fun v => d v • (c * w v))
    (fun v _ => (hf v).pow (d v))
  have e : ∑ v ∈ d.support, d v • (c * w v) = c * n := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by simp only [smul_eq_mul]; ring
  rw [e] at h
  exact h.C_mul _

end Hom

theorem lawc_one_smul {R : Type*} [CommRing R] (c : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (u : R) :
    lawc c g₂ g₃ (u • P) Q = u ^ 2 • lawc c g₂ g₃ P Q := by
  have := lawc_smul c g₂ g₃ P Q u 1
  rwa [one_smul, mul_one] at this

section CharZero

variable [CharZero K]

theorem lawPoly_isWH (c : Fin 2) (k k' : Fin m) (q : Fin 3 → K) (i : Fin 3) :
    (lawPoly g₂ g₃ d₀ d₁ c k' q i).IsWeightedHomogeneous (wk k) (2 * if k' = k then 1 else 0) := by
  apply isWH_of_scale
  set φ : MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Var d₀ d₁ m) K :=
    aeval (fun v : Var d₀ d₁ m => C ((2 : K) ^ wk k v) * X v)
  have hmap : φ (lawc c (C (g₂ k')) (C (g₃ k')) (bvars d₀ d₁ k') (fun i => C (q i)) i) =
      lawc c (φ (C (g₂ k'))) (φ (C (g₃ k'))) (φ ∘ bvars d₀ d₁ k') (φ ∘ fun i => C (q i)) i :=
    lawc_map φ.toRingHom c _ _ _ _ i
  have hC : ∀ a : K, φ (C a) = C a := fun a => by simp [φ]
  have hfc : (φ ∘ fun i => C (q i) : Fin 3 → MvPolynomial (Var d₀ d₁ m) K) = fun i => C (q i) := by
    funext i; simp [hC]
  rw [lawPoly, hmap, hC, hC, hfc]
  by_cases hk : k' = k
  · subst hk
    have hb : φ ∘ bvars d₀ d₁ k' =
        (C (2 : K) : MvPolynomial (Var d₀ d₁ m) K) • bvars (K := K) d₀ d₁ k' := by
      funext i; simp [φ, bvars]
    rw [hb, lawc_one_smul]
    simp [map_ofNat]
  · have hb : φ ∘ bvars d₀ d₁ k' = bvars (K := K) d₀ d₁ k' := by
      funext i; simp [φ, bvars, hk]
    rw [hb]
    simp [hk]

theorem translVar_isWH (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (k : Fin m)
    (v : Var d₀ d₁ m) : (translVar g₂ g₃ g c v).IsWeightedHomogeneous (wk k) (2 * wk k v) := by
  cases v with
  | x i => exact (isWeightedHomogeneous_X _ _ _).add (isWeightedHomogeneous_C _ _)
  | y j => exact isWH_mul' (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_X _ _ _) rfl
  | z j => exact isWH_mul' (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_X _ _ _) rfl
  | e k' i =>
    have := lawPoly_isWH (g₂ := g₂) (g₃ := g₃) (d₀ := d₀) (d₁ := d₁) (c k') k k' (rep (g.2.2 k')) i
    simpa [translVar] using this

/-- **Translations double the elliptic degrees.** -/
theorem isHomE_transl {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsHomE Q d)
    (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) : IsHomE (τ g₂ g₃ g c Q) (2 • d) :=
  fun k => isWH_aeval (translVar_isWH g c k) (hQ k)

end CharZero

/-! ### The translation identity -/

theorem lawc_zero {R : Type*} [CommRing R] : (lawc 0 : R → R → (Fin 3 → R) → (Fin 3 → R) → _) =
    law₁ := by
  funext; simp [lawc]

theorem lawc_one {R : Type*} [CommRing R] : (lawc 1 : R → R → (Fin 3 → R) → (Fin 3 → R) → _) =
    law₂ := by
  funext; simp [lawc]

/-- The generated translation identities, for both laws and charts `a, b ∈ {V, W}`. -/
theorem tr_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra S R] (D : Derivation S R R)
    (c : Fin 2) {a b : Fin 3} (ha : a ≠ 0) (hb : b ≠ 0) (g₂ g₃ s : R) (P Q : Fin 3 → R)
    (hg₂ : D g₂ = 0) (hg₃ : D g₃ = 0) (hQ : ∀ j, D (Q j) = 0)
    (hP : ∀ j, D (P j) = s * c2 a g₂ g₃ P j) (i : Fin 3) : ∃ f₁ f₂ : R,
    lawc c g₂ g₃ P Q b * D (lawc c g₂ g₃ P Q i) - s * (P a * c2 b g₂ g₃ (lawc c g₂ g₃ P Q) i) -
      s * (trE c a b g₂ g₃ P Q * lawc c g₂ g₃ P Q i) = s * (f₁ * Fv g₂ g₃ P + f₂ * Fv g₂ g₃ Q) := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;> simp at ha hb <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, lawc_zero, lawc_one, trE]
  · exact tr_eq_011 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_012 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_021 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_022 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_111 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_112 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_121 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i
  · exact tr_eq_122 D g₂ g₃ s P Q hg₂ hg₃ hQ hP i

theorem c2_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (a : Fin 3) (g₂ g₃ : R)
    (P : Fin 3 → R) (i : Fin 3) : φ (c2 a g₂ g₃ P i) = c2 a (φ g₂) (φ g₃) (φ ∘ P) i := by
  fin_cases a <;> fin_cases i <;> simp [c2, map_ofNat]

theorem chartAt_ne_zero (g : GPt K d₀ d₁ g₂ g₃) (k : Fin m) : chartAt g k ≠ 0 := by
  unfold chartAt; split <;> decide

variable (g₂ g₃) in
/-- The Euler coefficient of the translation identity in block `k`. -/
noncomputable def te (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (ch ch' : Fin m → Fin 3)
    (w : LieE K d₀ d₁ m) (k : Fin m) : MvPolynomial (Var d₀ d₁ m) K :=
  C (w.2.2 k) * Lo d₀ d₁ ch k * τ g₂ g₃ g c (Lo d₀ d₁ ch' k) * C (1 / 2) *
    trE (c k) (ch k) (ch' k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) fun i => C (rep (g.2.2 k) i)

theorem tr_var (h2 : (2 : K) ≠ 0) {ch ch' : Fin m → Fin 3} (hch : ∀ k, ch k ≠ 0)
    (hch' : ∀ k, ch' k ≠ 0) (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (w : LieE K d₀ d₁ m)
    (v : Var d₀ d₁ m) : ∃ G ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃,
      τ g₂ g₃ g c (Lc d₀ d₁ ch') * Dh g₂ g₃ ch w (translVar g₂ g₃ g c v) -
        Lc d₀ d₁ ch * τ g₂ g₃ g c (dvalh g₂ g₃ ch' w v) =
        ∑ k, wk k v • (te g₂ g₃ g c ch ch' w k * translVar g₂ g₃ g c v) + G := by
  cases v with
  | e k i =>
    have hP : ∀ j, Dh g₂ g₃ ch w (bvars d₀ d₁ k j) = (Lo d₀ d₁ ch k * C (w.2.2 k) * C (1 / 2)) *
        c2 (ch k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) j := fun j => by
      simp only [bvars, Dh_X, dvalh, mult, dval, chartPoly_eq_half h2]; ring
    obtain ⟨f₁, f₂, hf⟩ := tr_eq (Dh g₂ g₃ ch w) (c k) (hch k) (hch' k) (C (g₂ k)) (C (g₃ k))
      (Lo d₀ d₁ ch k * C (w.2.2 k) * C (1 / 2)) (bvars d₀ d₁ k) (fun i => C (rep (g.2.2 k) i))
      (Dh_C ch w _) (Dh_C ch w _) (fun j => Dh_C ch w _) hP i
    have hq : Fv (C (g₂ k)) (C (g₃ k)) (fun i => (C (rep (g.2.2 k) i) :
        MvPolynomial (Var d₀ d₁ m) K)) = 0 := by
      have := Fv_map (C : K →+* MvPolynomial (Var d₀ d₁ m) K) (g₂ k) (g₃ k) (rep (g.2.2 k))
      rw [Fv_rep h2, map_zero] at this
      exact this.symm
    rw [hq, Fv_bvars] at hf
    refine ⟨τ g₂ g₃ g c (Lo d₀ d₁ ch' k) * (Lo d₀ d₁ ch k * C (w.2.2 k) * C (1 / 2)) * f₁ *
      Fk g₂ g₃ d₀ d₁ k, Ideal.mul_mem_left _ _ (Fk_mem_IG g₂ g₃ k), ?_⟩
    simp only [wk_e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hτC : ∀ a : K, τ g₂ g₃ g c (C a) = C a := fun a => by simp [τ]
    have hlaw : ∀ j, τ g₂ g₃ g c (X (.e k j)) = lawc (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)
        (fun i => C (rep (g.2.2 k) i)) j := fun j => by simp [τ, translVar, lawPoly]
    have hτc2 : τ g₂ g₃ g c (c2 (ch' k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) i) =
        c2 (ch' k) (C (g₂ k)) (C (g₃ k))
          (lawc (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) fun i => C (rep (g.2.2 k) i)) i := by
      rw [← AlgHom.coe_toRingHom, c2_map]
      simp only [AlgHom.coe_toRingHom, hτC]
      congr 1
      funext j; simp only [Function.comp_apply, bvars, hlaw]
    have hd : τ g₂ g₃ g c (dvalh g₂ g₃ ch' w (.e k i)) = τ g₂ g₃ g c (Lo d₀ d₁ ch' k) *
        (C (w.2.2 k) * (C (1 / 2) * c2 (ch' k) (C (g₂ k)) (C (g₃ k))
          (lawc (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) fun i => C (rep (g.2.2 k) i)) i)) := by
      simp only [dvalh, mult, dval, chartPoly_eq_half h2, map_mul, hτC, hτc2]
    have hT : translVar g₂ g₃ g c (.e k i) = lawc (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)
        (fun i => C (rep (g.2.2 k) i)) i := rfl
    rw [Lc_eq ch' k, Lc_eq ch k, map_mul, hlaw, hd, hT]
    simp only [te]
    simp only [bvars] at hf ⊢
    linear_combination (τ g₂ g₃ g c (Lo d₀ d₁ ch' k)) * hf
  | x i => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval, translVar, τ]; ring⟩
  | y j => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval, translVar, τ]; ring⟩
  | z j => exact ⟨0, Ideal.zero_mem _, by simp [dvalh, mult, dval, translVar, τ]; ring⟩

/-- **The translation identity.** -/
theorem tr_id (h2 : (2 : K) ≠ 0) {ch ch' : Fin m → Fin 3} (hch : ∀ k, ch k ≠ 0)
    (hch' : ∀ k, ch' k ≠ 0) (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (w : LieE K d₀ d₁ m)
    {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsHomE Q d) :
    τ g₂ g₃ g c (Lc d₀ d₁ ch') * Dh g₂ g₃ ch w (τ g₂ g₃ g c Q) -
      Lc d₀ d₁ ch * τ g₂ g₃ g c (Dh g₂ g₃ ch' w Q) -
        ∑ k, te g₂ g₃ g c ch ch' w k * (d k • τ g₂ g₃ g c Q) ∈
      IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  choose G hG hGe using tr_var (g₂ := g₂) (g₃ := g₃) h2 hch hch' g c w
  set f := translVar g₂ g₃ g c
  have e1 : τ g₂ g₃ g c (Lc d₀ d₁ ch') * Dh g₂ g₃ ch w (τ g₂ g₃ g c Q) -
      Lc d₀ d₁ ch * τ g₂ g₃ g c (Dh g₂ g₃ ch' w Q) =
      ∑ v, (τ g₂ g₃ g c (Lc d₀ d₁ ch') * Dh g₂ g₃ ch w (f v) -
        Lc d₀ d₁ ch * τ g₂ g₃ g c (dvalh g₂ g₃ ch' w v)) * τ g₂ g₃ g c (pderiv v Q) := by
    rw [show τ g₂ g₃ g c Q = aeval f Q from rfl, derivation_aeval, Dh_eq_sum, map_sum,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_mul]
    simp only [τ]
    ring
  have e3 : ∑ v, (∑ k, wk k v • (te g₂ g₃ g c ch ch' w k * f v)) * τ g₂ g₃ g c (pderiv v Q) =
      ∑ k, te g₂ g₃ g c ch ch' w k * (d k • τ g₂ g₃ g c Q) := by
    calc ∑ v, (∑ k, wk k v • (te g₂ g₃ g c ch ch' w k * f v)) * τ g₂ g₃ g c (pderiv v Q)
        = ∑ v, ∑ k, te g₂ g₃ g c ch ch' w k *
            τ g₂ g₃ g c (wk k v • (X v * pderiv v Q)) :=
          Finset.sum_congr rfl fun v _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by
              rw [map_nsmul, map_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
              simp [τ, f]
      _ = ∑ k, ∑ v, te g₂ g₃ g c ch ch' w k * τ g₂ g₃ g c (wk k v • (X v * pderiv v Q)) :=
          Finset.sum_comm
      _ = ∑ k, te g₂ g₃ g c ch ch' w k * (d k • τ g₂ g₃ g c Q) :=
          Finset.sum_congr rfl fun k _ => by
            rw [← Finset.mul_sum, ← map_sum, euler hQ k, map_nsmul]
  have e2 : τ g₂ g₃ g c (Lc d₀ d₁ ch') * Dh g₂ g₃ ch w (τ g₂ g₃ g c Q) -
      Lc d₀ d₁ ch * τ g₂ g₃ g c (Dh g₂ g₃ ch' w Q) -
        ∑ k, te g₂ g₃ g c ch ch' w k * (d k • τ g₂ g₃ g c Q) =
      ∑ v, G v * τ g₂ g₃ g c (pderiv v Q) := by
    rw [e1, ← e3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hGe v]; ring
  rw [e2]
  exact Ideal.sum_mem _ fun v _ => Ideal.mul_mem_right _ _ (hG v)

/-! ### Translation invariance -/

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

theorem eval_transl_Lc_ne {h g : GPt K d₀ d₁ g₂ g₃} {c : Fin m → Fin 2} (hc : Good h g c)
    (lam : Fin m → Kˣ) : eval (coords h lam) (τ g₂ g₃ g c (Lc d₀ d₁ (chartAt (h + g)))) ≠ 0 := by
  obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc
  rw [hμ]
  exact eval_Lc_chartAt_ne _ _

section CharZero

variable [CharZero K]

/-- **Translation invariance** (good law choice). -/
theorem transl_good (W : Submodule K (LieE K d₀ d₁ m)) {h g : GPt K d₀ d₁ g₂ g₃}
    {c : Fin m → Fin 2} (hc : Good h g c) :
    ∀ (n : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}, IsHomE Q d →
      Q ∈ VO1 g₂ g₃ (chartAt (h + g)) W n (vanish {h + g}) →
      τ g₂ g₃ g c Q ∈ VO1 g₂ g₃ (chartAt h) W n (vanish {h}) := by
  obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc
  intro n
  induction n with
  | zero =>
    intro Q d _ hQv
    rw [mem_VOg_zero, mem_vanish_singleton] at hQv ⊢
    intro lam
    rw [hμ]; exact hQv _
  | succ n ih =>
    intro Q d hQ hQv
    have hτ : τ g₂ g₃ g c Q ∈ VO1 g₂ g₃ (chartAt h) W n (vanish {h}) :=
      ih hQ (VOg_succ_le n hQv)
    rw [mem_VOg_succ]
    refine ⟨VOg_le n hτ, fun w hw => ?_⟩
    refine sat (chartAt h) W (eval_transl_Lc_ne h2 hΔ hc) n _ ?_
    have hid := IG_le_VO1 h2 (chartAt h) W n {h}
      (tr_id h2 (chartAt_ne_zero h) (chartAt_ne_zero (h + g)) g c w hQ)
    have h1 := Ideal.mul_mem_left _ (Lc d₀ d₁ (chartAt h))
      (ih (isHomE_Dh (g₂ := g₂) (g₃ := g₃) hQ _ w) ((mem_VOg_succ.mp hQv).2 w hw))
    have h3 : ∑ k, te g₂ g₃ g c (chartAt h) (chartAt (h + g)) w k * (d k • τ g₂ g₃ g c Q) ∈
        VO1 g₂ g₃ (chartAt h) W n (vanish {h}) :=
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (by
        rw [nsmul_eq_mul]; exact Ideal.mul_mem_left _ _ hτ)
    have := Ideal.add_mem _ (Ideal.add_mem _ hid h1) h3
    convert this using 1
    ring

end CharZero

/-! ### Arbitrary law choices -/

section Scale

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The block scalars: `a k` on block `k`, `1` elsewhere. -/
def sc (a : Fin m → A) : Var d₀ d₁ m → A
  | .e k _ => a k
  | _ => 1

omit [DecidableEq K] h2 hΔ in
theorem sc_eq (a : Fin m → A) (v : Var d₀ d₁ m) : sc a v = ∏ k, a k ^ wk k v := by
  cases v <;> simp [sc, wk, pow_ite]

omit [DecidableEq K] h2 hΔ in
/-- **Scaling a homogeneous polynomial** block by block. -/
theorem aeval_sc {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsHomE Q d)
    (f : Var d₀ d₁ m → A) (a : Fin m → A) :
    aeval (fun v => f v * sc a v) Q = (∏ k, a k ^ d k) * aeval f Q := by
  rw [Q.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hw : ∀ k, Finsupp.weight (wk k) n = d k := fun k => hQ k (mem_support_iff.mp hn)
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp_rw [mul_pow, Finset.prod_mul_distrib, sc_eq, ← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm (s := n.support)]
  have e : ∀ k, ∏ v ∈ n.support, a k ^ (wk k v * n v) = a k ^ d k := fun k => by
    rw [Finset.prod_pow_eq_pow_sum, ← hw k, Finsupp.weight_apply, Finsupp.sum]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by simp [mul_comm]
  simp_rw [e]
  ring

end Scale

omit [DecidableEq K] in
/-- The two addition laws are proportional on `E × E`, modulo `I_G` (Nullstellensatz). -/
theorem cross_mem [IsAlgClosed K] (c c' : Fin 2) (k : Fin m) (q : Fin 3 → K)
    (hq : Fv (g₂ k) (g₃ k) q = 0) (i b : Fin 3) :
    lawPoly g₂ g₃ d₀ d₁ c k q i * lawPoly g₂ g₃ d₀ d₁ c' k q b -
      lawPoly g₂ g₃ d₀ d₁ c' k q i * lawPoly g₂ g₃ d₀ d₁ c k q b ∈
      IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  rw [← vanish_univ hΔ h2]
  refine mem_vanish.mpr fun h _ lam => ?_
  have hP : Fv (g₂ k) (g₃ k) (fun i => coords h lam (.e k i)) = 0 := by
    have := mem_vanish.mp (IG_le_vanish h2 Set.univ (Fk_mem_IG g₂ g₃ (d₀ := d₀) (d₁ := d₁) k))
      h (Set.mem_univ _) lam
    simpa [Fk, Fv, F] using this
  simp only [map_sub, map_mul, eval_lawPoly]
  fin_cases c <;> fin_cases c' <;> simp only [Fin.zero_eta, Fin.mk_one, lawc_zero, lawc_one,
    sub_self]
  · have := law₁_cross_law₂ hP hq i b
    linear_combination this
  · have := law₁_cross_law₂ hP hq i b
    linear_combination -this

omit [DecidableEq K] in
/-- **Congruence of the translates by different law choices** (homogeneous `Q`). -/
theorem cong_laws [IsAlgClosed K] (g : GPt K d₀ d₁ g₂ g₃) (c c' : Fin m → Fin 2) (b : Fin m → Fin 3)
    {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsHomE Q d) :
    τ g₂ g₃ g c Q * ∏ k, τ g₂ g₃ g c' (X (.e k (b k))) ^ d k -
      τ g₂ g₃ g c' Q * ∏ k, τ g₂ g₃ g c (X (.e k (b k))) ^ d k ∈
      IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  set π := Ideal.Quotient.mkₐ K (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
  rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk K]
  have hf : (fun v => π (translVar g₂ g₃ g c v) * sc (fun k => π (τ g₂ g₃ g c' (X (.e k (b k))))) v)
      = fun v => π (translVar g₂ g₃ g c' v) * sc (fun k => π (τ g₂ g₃ g c (X (.e k (b k))))) v := by
    funext v
    cases v with
    | e k i =>
      simp only [sc, τ, aeval_X, translVar, ← map_mul]
      exact Ideal.Quotient.eq.mpr (cross_mem h2 hΔ (c k) (c' k) k _ (Fv_rep h2 _) i (b k))
    | x i => simp only [sc, mul_one, translVar]
    | y j => simp only [sc, mul_one, translVar]
    | z j => simp only [sc, mul_one, translVar]
  have := congrArg (fun F => aeval F Q) hf
  simp only [aeval_sc hQ] at this
  simp only [map_mul, map_prod, map_pow]
  rw [show (aeval fun v => π (translVar g₂ g₃ g c v)) Q = π (τ g₂ g₃ g c Q) from
      (comp_aeval_apply _ _ _).symm,
    show (aeval fun v => π (translVar g₂ g₃ g c' v)) Q = π (τ g₂ g₃ g c' Q) from
      (comp_aeval_apply _ _ _).symm] at this
  linear_combination this

/-- **Translation invariance of the order of vanishing**, any law choice (homogeneous `Q`). -/
theorem transl_van [CharZero K] [IsAlgClosed K] (W : Submodule K (LieE K d₀ d₁ m))
    {h g : GPt K d₀ d₁ g₂ g₃}
    (c : Fin m → Fin 2) (n : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hQ : IsHomE Q d) (hQv : Q ∈ VO1 g₂ g₃ (chartAt (h + g)) W n (vanish {h + g})) :
    τ g₂ g₃ g c Q ∈ VO1 g₂ g₃ (chartAt h) W n (vanish {h}) := by
  obtain ⟨c', hc'⟩ := exists_good h2 hΔ h g
  have hgood := transl_good h2 hΔ W hc' n hQ hQv
  have hcong := cong_laws h2 hΔ g c c' (chartAt (h + g)) hQ
  obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc'
  refine sat (chartAt h) W (u := ∏ k, τ g₂ g₃ g c' (X (.e k (chartAt (h + g) k))) ^ d k)
    (fun lam => ?_) n _ ?_
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro k _
    rw [map_pow, hμ, eval_X]
    simp only [coords, coordsZ_e]
    rw [rep_chartAt]
    simp
  · have := Ideal.add_mem _ (IG_le_VO1 h2 (chartAt h) W n {h} hcong)
      (Ideal.mul_mem_right (∏ k, τ g₂ g₃ g c (X (.e k (chartAt (h + g) k))) ^ d k) _ hgood)
    convert this using 1
    ring

end LSG.ME
