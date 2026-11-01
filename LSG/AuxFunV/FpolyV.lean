/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunV.FibreId
import LSG.AuxFun.LemmaUBounds

/-!
# Lemma U for the class `𝒞`: the function `F_t` and its identity with `Ψ(t + s v)`

Basic factors (`gfacV`): the abelian ones (`gfac` on the base `π t`, `π v`) and, for each fibre
form `S_i`, the **fibre factor**

  `(cᵢ + vᵢ s) Π_k N_{k,W}(s) + Σ_j M_ij q_j G_j(s) Π_{l≠j} N_{l,W}(s)`,

with `N_{k,W}(s) = law_{κ_k}(X'_k, ξ_k(s))_W`, `G_j(s) = NLaw_{κ_j,λ_j,W}(P̂_j, Q̂_j(s))₃`
(`gT_eq`), `q_j = (2 λ_j(X'_j))⁻¹` and the constants `cᵢ = sᵢ(t) − Σ_j M_ij W_j`,
`W_j = ζ(t_j + z₀) + ζ(z₀) − η(ω₁)`.

**`FpolyV_eq`**: `F_t(s) = Π_k R_k(s)^D · Ψ(t + s v)` (the abelian unit; each fibre form has degree
one in every elliptic block).
-/

open Complex Finset LSG.Weierstrass LSG.Elliptic PeriodPair LSG.W88 LSG.W88.Vec
open LSG.Aux (ellW ellV IsRep zh wpP wpQ xiV lawk lawk_eq_smul_ellV Fct coordF gfac cidx
  ellV_cidx differentiable_ellW contDiff_coordF differentiableAt_lawk_xi)
open scoped ContDiff

noncomputable section

namespace LSG.AuxV

variable {d0 d1 m r D : ℕ}

/-- Index set of the coordinate functions of `exp_G`, `G ∈ 𝒞`. -/
abbrev FctV (d0 d1 m r : ℕ) := Fct d0 d1 m ⊕ Fin r

/-- The exponent vector of a monomial of the class `𝒞`. -/
def MonoV.expo (μ : MonoV d0 d1 m r D) : FctV d0 d1 m r → ℕ
  | .inl (.inl i) => μ.α i
  | .inl (.inr (.inl i)) => μ.β i
  | .inl (.inr (.inr kc)) => μ.γ kc.1 kc.2
  | .inr i => μ.φ i

/-- The coordinate functions. -/
def coordFV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) :
    FctV d0 d1 m r → TanV d0 d1 m r → ℂ
  | .inl f => fun p => coordF Ls f (piT p)
  | .inr i => fun p => fibF Ls M i p.2.2.1 p.2.2.2

lemma MonoV.eval_eq_prod (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (μ : MonoV d0 d1 m r D) (p : TanV d0 d1 m r) :
    μ.eval Ls M p = ∏ f, coordFV Ls M f p ^ μ.expo f := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type,
    Fintype.prod_prod_type, MonoV.eval]
  simp only [coordFV, coordF, MonoV.expo, piT_apply]
  ring

/-- `Ψ = Σ_l p_l M_l`. -/
def PsiV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (x : TanV d0 d1 m r) : ℂ :=
  ∑ l, (p l : ℂ) * (μs l).eval Ls M x

/-- The base-`W` law factor `N_{k,W}(s)`. -/
def NW (L : PeriodPair) (κ : Fin 2) (X : Fin 3 → ℂ) (c s : ℂ) : ℂ :=
  lawk κ L.g₂ L.g₃ X (xiV L c s) 2

/-- The fibre law factor `G(s) = NLaw_{κ,λ,W}(P̂, Q̂(s))₃`. -/
def GT (L : PeriodPair) (κ : Fin 2) (X : Fin 3 → ℂ) (c s : ℂ) : ℂ :=
  NLaw L.g₂ L.g₃ κ (lamIdx X) 1 (Phat X) (Qhat L c s) 3

/-- The fibre basic factor. -/
def fibFac (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (κ : Fin m → Fin 2)
    (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) (v : TanV d0 d1 m r) (i : Fin r) (s : ℂ) : ℂ :=
  (cst i + v.2.2.2 i * s) * ∏ k, NW (Ls k) (κ k) (X' k) (v.2.2.1 k) s +
    ∑ j, M i j * ((2 * mult (lamIdx (X' j)) (X' j))⁻¹ * GT (Ls j) (κ j) (X' j) (v.2.2.1 j) s *
      ∏ l ∈ univ.erase j, NW (Ls l) (κ l) (X' l) (v.2.2.1 l) s)

/-- The basic factors of `F_t`. -/
def gfacV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (t v : TanV d0 d1 m r)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) :
    FctV d0 d1 m r → ℂ → ℂ
  | .inl f => gfac Ls (piT t) (piT v) κ X' f
  | .inr i => fibFac Ls M κ X' cst v i

/-- `F_t`. -/
def FpolyV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (t v : TanV d0 d1 m r)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ) (cst : Fin r → ℂ) {L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (s : ℂ) : ℂ :=
  ∑ l, (p l : ℂ) * ∏ f, gfacV Ls M t v κ X' cst f s ^ (μs l).expo f

/-- The fibre parameter `W_k = ζ(t_k + z₀) + ζ(z₀) − η(ω₁)`. -/
def Wpar (L : PeriodPair) (u : ℂ) : ℂ := zeta L (u + zh L) + zeta L (zh L) - eta L L.ω₁

/-- **`F_t = Π_k R_k^D · Ψ(t + s v)`** for the class `𝒞`. -/
theorem FpolyV_eq (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) (t v : TanV d0 d1 m r)
    (κ : Fin m → Fin 2) (X' : Fin m → Fin 3 → ℂ)
    (hX' : ∀ k, IsRep (Ls k) (t.2.2.1 k + zh (Ls k)) (X' k)) (cst : Fin r → ℂ)
    (hcst : ∀ i, cst i = t.2.2.2 i - ∑ j, M i j * Wpar (Ls j) (t.2.2.1 j))
    {L : ℕ} (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (j : Fin m → Fin 3) {s : ℂ}
    (hs : ∀ k, zh (Ls k) + v.2.2.1 k * s ∉ (Ls k).lattice)
    (hj : ∀ k, ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (j k) ≠ 0) :
    FpolyV Ls M t v κ X' cst μs p s = (∏ k, (lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k)
        (xiV (Ls k) (v.2.2.1 k) s) (j k) / ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (j k)) ^ D) *
      PsiV Ls M μs p (t + s • v) := by
  set R : Fin m → ℂ := fun k => lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k)
    (xiV (Ls k) (v.2.2.1 k) s) (j k) / ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (j k)
  have hlaw : ∀ k, lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2.1 k) s) =
      R k • ellV (Ls k) (t.2.2.1 k + v.2.2.1 k * s) := fun k =>
    lawk_eq_smul_ellV (Ls k) (hX' k) (hs k) (κ k) (hj k)
  have hNW : ∀ k, NW (Ls k) (κ k) (X' k) (v.2.2.1 k) s =
      R k * ellW (Ls k) 0 (t.2.2.1 k + v.2.2.1 k * s) := fun k => by
    have := congrFun (hlaw k) 2
    simpa [NW, ellV] using this
  have hGT : ∀ k, (2 * mult (lamIdx (X' k)) (X' k))⁻¹ * GT (Ls k) (κ k) (X' k) (v.2.2.1 k) s =
      R k * ellN (Ls k) (t.2.2.1 k + v.2.2.1 k * s) (Wpar (Ls k) (t.2.2.1 k)) 3 := by
    intro k
    have hm : mult (lamIdx (X' k)) (X' k) ≠ 0 := mult_lamIdx_ne_zero (Ls k) (hX' k)
    rw [GT, gT_eq (Ls k) (hX' k) (hs k) (κ k) (hj k), Wpar]
    field_simp
    ring
  have hpt : ∀ k, (t + s • v).2.2.1 k = t.2.2.1 k + v.2.2.1 k * s := fun k => by
    simp [mul_comm]
  have hfac : ∀ f : FctV d0 d1 m r, gfacV Ls M t v κ X' cst f s =
      (match f with
        | .inl (.inl _) => 1
        | .inl (.inr (.inl _)) => 1
        | .inl (.inr (.inr kc)) => R kc.1
        | .inr _ => ∏ k, R k) * coordFV Ls M f (t + s • v) := by
    intro f
    rcases f with (i | i | ⟨k, c⟩) | i
    · simp [gfacV, gfac, coordFV, coordF]; ring
    · simp [gfacV, gfac, coordFV, coordF, Complex.exp_add]; ring_nf
    · change lawk (κ k) (Ls k).g₂ (Ls k).g₃ (X' k) (xiV (Ls k) (v.2.2.1 k) s) (cidx c) =
        R k * ellW (Ls k) c ((t + s • v).2.2.1 k)
      have := congrFun (hlaw k) (cidx c)
      rw [this, Pi.smul_apply, smul_eq_mul, ellV_cidx, hpt]
    · simp only [gfacV, coordFV, fibFac]
      rw [fibF_eq_ellN Ls M i _ _ (fun j => Wpar (Ls j) (t.2.2.1 j))]
      simp only [hNW, hGT, hpt]
      have hs2 : (t + s • v).2.2.2 i = t.2.2.2 i + v.2.2.2 i * s := by simp [mul_comm]
      rw [hs2, hcst i, mul_add, mul_sum, prod_mul_distrib]
      congr 1
      · ring
      · refine sum_congr rfl fun jj _ => ?_
        rw [← mul_prod_erase univ R (mem_univ jj), prod_mul_distrib]
        ring
  unfold FpolyV PsiV
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [MonoV.eval_eq_prod]
  simp_rw [hfac, mul_pow, prod_mul_distrib]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  simp only [one_pow, prod_const_one, one_mul, MonoV.expo]
  have hD : ∀ k, (∏ c : Fin 3, R k ^ (μs l).γ k c) * R k ^ (∑ i, (μs l).φ i) = R k ^ D := by
    intro k; rw [prod_pow_eq_pow_sum, ← pow_add, (μs l).hγ k]
  have hF : ∏ i, (∏ k, R k) ^ (μs l).φ i = ∏ k, R k ^ (∑ i, (μs l).φ i) := by
    rw [prod_pow_eq_pow_sum, ← prod_pow]
  rw [hF]
  have : ∏ k, R k ^ D = (∏ k, ∏ c : Fin 3, R k ^ (μs l).γ k c) *
      ∏ k, R k ^ (∑ i, (μs l).φ i) := by
    rw [← prod_mul_distrib]; exact prod_congr rfl fun k _ => (hD k).symm
  rw [this]
  ring

/-! ### Smoothness -/

lemma contDiff_coordFV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ)
    (f : FctV d0 d1 m r) : ContDiff ℂ ∞ (coordFV Ls M f) := by
  rcases f with f | i
  · exact (contDiff_coordF Ls f).comp piT.contDiff
  · change ContDiff ℂ ∞ (fun p : TanV d0 d1 m r => fibF Ls M i p.2.2.1 p.2.2.2)
    have hz : ∀ l, ContDiff ℂ ∞ (fun p : TanV d0 d1 m r => p.2.2.1 l) := fun l =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) l).contDiff.comp
        (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))
    have hsi : ContDiff ℂ ∞ (fun p : TanV d0 d1 m r => p.2.2.2 i) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).contDiff.comp
        (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
    have hW : ∀ l, ContDiff ℂ ∞ (fun p : TanV d0 d1 m r => ellW (Ls l) 0 (p.2.2.1 l)) :=
      fun l => (differentiable_ellW (Ls l) 0).contDiff.comp (hz l)
    unfold fibF
    refine (hsi.mul (contDiff_prod fun l _ => hW l)).sub (ContDiff.sum fun jj _ => ?_)
    exact contDiff_const.mul (((differentiable_zetaS (Ls jj)).contDiff.comp (hz jj)).mul
      (contDiff_prod fun l _ => hW l))

lemma contDiff_PsiV (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) : ContDiff ℂ ∞ (PsiV Ls M μs p) := by
  unfold PsiV
  refine ContDiff.sum fun l _ => contDiff_const.mul ?_
  have : (μs l).eval Ls M = fun x => ∏ f, coordFV Ls M f x ^ (μs l).expo f :=
    funext (MonoV.eval_eq_prod Ls M (μs l))
  rw [this]
  exact contDiff_prod fun f _ => (contDiff_coordFV Ls M f).pow _

lemma analyticAt_PsiV_line (Ls : Fin m → PeriodPair) (M : Matrix (Fin r) (Fin m) ℂ) {L : ℕ}
    (μs : Fin L → MonoV d0 d1 m r D) (p : Fin L → ℤ) (t v : TanV d0 d1 m r) :
    AnalyticAt ℂ (fun s : ℂ => PsiV Ls M μs p (t + s • v)) 0 := by
  have h : Differentiable ℂ (fun s : ℂ => PsiV Ls M μs p (t + s • v)) :=
    ((contDiff_PsiV Ls M μs p).differentiable (by simp)).comp (by fun_prop)
  exact h.analyticAt 0

lemma differentiableAt_zS (L : PeriodPair) (c : ℂ) {s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    DifferentiableAt ℂ (zS L c) s := (hasDerivAt_zS L c hs).differentiableAt

lemma differentiableAt_wpP (L : PeriodPair) (c : ℂ) {s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    DifferentiableAt ℂ (wpP L c) s :=
  (LSG.Weierstrass.hasDerivAt_weierstrassP L hs).differentiableAt.comp s (by fun_prop)

lemma differentiableAt_wpQ (L : PeriodPair) (c : ℂ) {s : ℂ} (hs : zh L + c * s ∉ L.lattice) :
    DifferentiableAt ℂ (wpQ L c) s :=
  (LSG.Weierstrass.differentiableAt_derivWeierstrassP L hs).comp s (by fun_prop)

end LSG.AuxV
