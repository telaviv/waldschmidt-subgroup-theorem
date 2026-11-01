/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.HilbH0Fam

/-!
# The unsliced Hilbert lower bound for `H⁰` (α′; STAGE_A4 §7.3 (6), step 2)

**`h0LowerBound O : H0LowerBound O (cHB B)`** for every obstruction data `O` (ME's `hfun_H0_ge''`), with
`cHB B = ∏_k (g_k+1)^{g_k+1}` depending only on `B`. With `CosetGe.coset_ge_of_lower` this closes the field
`SubgroupData.coset_ge` (**`coset_ge_of_obstr`**, constant `cHB B · nLaw B · 2^m`).

Proof. `I(O.grp) = I(exp T)`, `T = h₀ × U^⊥ × t` (`grp_eq`, `vanish_zcl`), and `P ∈ I(exp T)` iff
`P(liftZ u μ) = 0` for `u ∈ T`, `μ ∈ ℂ^m` (`mem_vanish_expG_iff`). The family `hPoly` of `HilbH0Fam.lean` (built
from coordinates on `h₀`, torus coordinates independent modulo `U`, and the pivot set `J` of `t` from `pivot`)
evaluates on such lifts to the monomials `w^{hExp i}` in target coordinates `w`; **`eventually_lift`** shows that
every `w` near the base point `hBase` is attained (inverse function theorem on the pivot blocks via
`chartRatio_image_mem_nhds`, a continuous section of the pivot projection, `exp` on the torus coordinates, free
scalings `μ`). A polynomial vanishing near a point is `0`, so the family is independent modulo `I(H⁰)`
(`hExp_injective`), and `card_le_hfun_vanish` + `count_le` give the bound.
-/

open MvPolynomial Module Filter Topology Set
open StrongSix.M2 (FLE hfun)

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

variable (B) in
/-- The base point of the target coordinates. -/
noncomputable def hBase (t₀ : ℕ) (κ : Type) (J : Finset (Fin m)) : HCrd B t₀ κ J → ℂ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr ⟨_, none⟩) => 0
  | .inr (.inr ⟨k, some j⟩) => (B k).chartRatio 0 (Fin.castLE (pivG_le J k) j)

/-- **Every target point near `hBase` is attained by a lift of a point of `exp T`.** -/
theorem eventually_lift (O : ObstrDataB d₀ d₁ B) {J : Finset (Fin m)}
    (hsurj : ∀ y : ∀ k, Fin (B k).g → ℂ, ∃ z ∈ O.t, ∀ k ∈ J, z k = y k)
    {κ : Type} [Fintype κ] (jj : κ → Fin d₁)
    (hind : LinearIndependent ℚ fun k => O.U.mkQ (Pi.single (jj k) 1))
    (L : Fin (finrank ℂ O.h0) → (Fin d₀ → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ l l', L l (Module.finBasis ℂ O.h0 l' : Fin d₀ → ℂ) = if l' = l then 1 else 0) :
    ∀ᶠ w in 𝓝 (hBase B (finrank ℂ O.h0) κ J), ∃ u ∈ O.tan, ∃ μ : Fin m → ℂ,
      (∀ l, L l u.1 = w (.inl l)) ∧
      (∀ k, Complex.exp (u.2.1 (jj k)) = w (.inr (.inl k))) ∧
      (∀ k, μ k * (B k).θ (u.2.2 k) (B k).i₀ = w (.inr (.inr ⟨k, none⟩))) ∧
      (∀ k j, μ k * (B k).θ (u.2.2 k) ((B k).is (Fin.castLE (pivG_le J k) j)) =
        w (.inr (.inr ⟨k, none⟩)) * w (.inr (.inr ⟨k, some j⟩))) := by
  classical
  obtain ⟨σ, hσt, hσJ⟩ := exists_pivot_section hsurj
  -- where all the `θ_{k,i₀}` are nonzero
  have hV : ∀ᶠ y in 𝓝 (0 : ∀ k, Fin (B k).g → ℂ), ∀ k, (B k).θ (σ y k) (B k).i₀ ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    have hc : ContinuousAt (fun y : (∀ k, Fin (B k).g → ℂ) => (B k).θ (σ y k) (B k).i₀) 0 :=
      (((B k).continuous_θ_apply (B k).i₀).comp ((continuous_apply k).comp σ.continuous)).continuousAt
    have h0 : (B k).θ (σ 0 k) (B k).i₀ ≠ 0 := by simpa using (B k).θ_i₀
    exact hc.eventually_ne h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hV
  -- the ratio coordinates of a pivot block
  let T : ∀ k, k ∈ J → (HCrd B (finrank ℂ O.h0) κ J → ℂ) → (Fin (B k).g → ℂ) :=
    fun k hk w j' => w (.inr (.inr ⟨k, some ⟨j', by rw [pivG_of_mem hk]; exact j'.2⟩⟩))
  have hT0 : ∀ k (hk : k ∈ J), T k hk (hBase B (finrank ℂ O.h0) κ J) = (B k).chartRatio 0 :=
    fun k hk => funext fun j' => rfl
  have hTc : ∀ k (hk : k ∈ J), Continuous (T k hk) := fun k hk =>
    continuous_pi fun j' => continuous_apply _
  have hG : ∀ᶠ w in 𝓝 (hBase B (finrank ℂ O.h0) κ J), (∀ k, w (.inr (.inl k)) ≠ 0) ∧
      ∀ k (hk : k ∈ J), T k hk w ∈ (B k).chartRatio '' Metric.ball 0 ε := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro k
      exact (continuous_apply _).continuousAt.eventually_ne (by simp [hBase])
    · rw [Filter.eventually_all]
      intro k
      by_cases hk : k ∈ J
      · have := (hTc k hk).continuousAt.preimage_mem_nhds (x := hBase B (finrank ℂ O.h0) κ J)
          (by rw [hT0 k hk]; exact (B k).chartRatio_image_mem_nhds (Metric.ball_mem_nhds 0 hε))
        filter_upwards [this] with w hw
        exact fun _ => hw
      · exact Filter.Eventually.of_forall fun w hk' => absurd hk' hk
  filter_upwards [hG] with w ⟨hw1, hw2⟩
  -- the point on the pivot blocks
  choose yk hyk hyr using hw2
  let y : ∀ k, Fin (B k).g → ℂ := fun k => if hk : k ∈ J then yk k hk else 0
  have hyball : y ∈ Metric.ball 0 ε := by
    rw [ball_pi _ hε]
    intro k _
    by_cases hk : k ∈ J
    · simp only [y, dif_pos hk]; exact hyk k hk
    · simp only [y, dif_neg hk]; exact Metric.mem_ball_self hε
  have hne := hball y hyball
  -- the additive part
  let v0 := Module.finBasis ℂ O.h0
  let x : Fin d₀ → ℂ := ∑ l, w (.inl l) • (v0 l : Fin d₀ → ℂ)
  have hx : x ∈ O.h0 := Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (v0 l).2
  have hLx : ∀ l, L l x = w (.inl l) := by
    intro l
    simp only [x, map_sum, map_smul, v0, hL, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- the torus part
  obtain ⟨v, hv, hvj⟩ := exists_mem_torusLie O.U jj hind fun k => Complex.log (w (.inr (.inl k)))
  refine ⟨(x, v, σ y), ⟨hx, hv, hσt y⟩,
    fun k => w (.inr (.inr ⟨k, none⟩)) / (B k).θ (σ y k) (B k).i₀, hLx, fun k => ?_, fun k => ?_,
    fun k j => ?_⟩
  · change Complex.exp (v (jj k)) = _
    rw [hvj k, Complex.exp_log (hw1 k)]
  · change w (.inr (.inr ⟨k, none⟩)) / (B k).θ (σ y k) (B k).i₀ * (B k).θ (σ y k) (B k).i₀ = _
    rw [div_mul_cancel₀ _ (hne k)]
  · have hk : k ∈ J := by
      by_contra hk
      have := j.2
      have h0 : pivG B J k = 0 := if_neg hk
      omega
    have hzk : σ y k = yk k hk := by rw [hσJ y k hk]; simp [y, dif_pos hk]
    have hr := congrFun (hyr k hk) (Fin.castLE (pivG_le J k) j)
    change (B k).θ (yk k hk) ((B k).is (Fin.castLE (pivG_le J k) j)) / (B k).θ (yk k hk) (B k).i₀ =
      w (.inr (.inr ⟨k, some j⟩)) at hr
    change w (.inr (.inr ⟨k, none⟩)) / (B k).θ (σ y k) (B k).i₀ *
      (B k).θ (σ y k) ((B k).is (Fin.castLE (pivG_le J k) j)) = _
    have hne' := hne k
    rw [hzk] at hne' ⊢
    rw [← hr]
    field_simp

/-- A monomial with exponent vector `e`, evaluated. -/
theorem eval_monomial_fun {S : Type*} [Fintype S] (e : S → ℕ) (w : S → ℂ) :
    eval w (monomial (Finsupp.equivFunOnFinite.symm e) (1 : ℂ)) = ∏ s, w s ^ e s := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
  simp

/-- **The unsliced Hilbert lower bound for `H⁰`** (ME's `hfun_H0_ge''`), constant `cHB B`. -/
theorem h0LowerBound (O : ObstrDataB d₀ d₁ B) : H0LowerBound O (cHB B) := by
  classical
  intro D₀ D₁ D₂ t
  obtain ⟨J, hinj, hsurj⟩ := pivot O.t_rat
  obtain ⟨κ, _, jj, -, hκ, hind⟩ := StrongSix.M2.exists_indep_quot O.U
  set t₀ := finrank ℂ O.h0 with ht₀
  let v0 := Module.finBasis ℂ O.h0
  have hL : ∀ l : Fin t₀, ∃ L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ, L.comp O.h0.subtype = v0.coord l :=
    fun l => LinearMap.exists_extend _
  choose L hLv using hL
  have hLk : ∀ l l', L l (v0 l' : Fin d₀ → ℂ) = if l' = l then 1 else 0 := by
    intro l l'
    have := congrArg (fun f => f (v0 l')) (hLv l)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  set M0 := t * D₀ / t₀ + 1
  set M1 := t * D₁ / (d₁ - finrank ℚ O.U) + 1
  set T := t * D₂
  let P : HIdx B t₀ M0 κ M1 J T → MvPolynomial (Var d₀ d₁ B) ℂ :=
    hPoly (fun l => linPoly (L l)) jj
  have hM0 : t₀ * (M0 - 1) ≤ t * D₀ := by simp only [M0, Nat.add_sub_cancel]; exact Nat.mul_div_le _ _
  have hM1 : Fintype.card κ * (M1 - 1) ≤ t * D₁ := by
    simp only [M1, Nat.add_sub_cancel, hκ]; exact Nat.mul_div_le _ _
  have hind' : ∀ c : HIdx B t₀ M0 κ M1 J T → ℂ, ∑ i, c i • P i ∈ vanish O.grp → ∀ i, c i = 0 := by
    intro c hc
    rw [O.grp_eq, vanish_zcl, mem_vanish_expG_iff] at hc
    let Q : MvPolynomial (HCrd B t₀ κ J) ℂ :=
      ∑ i, c i • monomial (Finsupp.equivFunOnFinite.symm (hExp i)) 1
    have hQ : Q = 0 := by
      refine eq_zero_of_eventually_eval Q (hBase B t₀ κ J) ?_
      filter_upwards [eventually_lift O hsurj jj hind L hLk] with w ⟨u, hu, μ, h1, h2, h3, h4⟩
      have := hc u hu μ
      rw [map_sum] at this
      rw [← this]
      simp only [Q, map_sum, smul_eval, eval_monomial_fun]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      exact (eval_hPoly _ jj u μ w (fun l => by rw [eval_linPoly]; exact h1 l) h2 h3 h4 i).symm
    intro i
    have := congrArg (fun p : MvPolynomial (HCrd B t₀ κ J) ℂ =>
      p.coeff (Finsupp.equivFunOnFinite.symm (hExp i))) hQ
    simp only [Q, coeff_sum, coeff_smul, coeff_monomial, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by
        rw [if_neg]; · simp
        intro h
        exact hi' (hExp_injective (Finsupp.equivFunOnFinite.symm.injective h)))
      (by simp)] at this
    simpa using this
  have hcard := card_le_hfun_vanish (DfunB D₀ D₁ D₂) t O.grp P
    (fun i => hPoly_mem_FLE _ (fun l => linPoly_mem_FLE _) jj hM0 hM1 rfl i) hind'
  rw [card_HIdx, hκ] at hcard
  have hcount := count_le (B := B) (J := J) (T := T) (s := finrank ℂ O.t) (finrank_le_pivot hinj)
  calc M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * (T + 1) ^ (finrank ℂ O.t + m)
      ≤ M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * (cHB B * ∏ k, pivM B J T k ^ (pivG B J k + 1)) :=
        Nat.mul_le_mul_left _ hcount
    _ = cHB B * (M0 ^ t₀ * M1 ^ (d₁ - finrank ℚ O.U) * ∏ k, pivM B J T k ^ (pivG B J k + 1)) := by
        ring
    _ ≤ cHB B * hfun blk (DfunB D₀ D₁ D₂) ℂ (vanish O.grp) t := Nat.mul_le_mul_left _ hcard

/-- **The field `SubgroupData.coset_ge`** for any obstruction data, constant `cHB B · nLaw B · 2^m`. -/
theorem coset_ge_of_obstr (O : ObstrDataB d₀ d₁ B) :
    ∀ (α : Alpha B) (a : GPt d₀ d₁ B), (∀ k, lsl α k ∉ vanish (gtransl a O.grp)) →
    ∀ D₀ D₁ D₂ t : ℕ,
      (t * D₀ / finrank ℂ O.h0 + 1) ^ finrank ℂ O.h0 *
          (t * D₁ / (d₁ - finrank ℚ O.U) + 1) ^ (d₁ - finrank ℚ O.U) *
          (t * D₂ + 1) ^ finrank ℂ O.t ≤
        (cHB B * nLaw B * 2 ^ m) *
          hfun blk (DfunB D₀ D₁ D₂) ℂ (vanishP Finset.univ α (gtransl a O.grp)) (2 * t) :=
  coset_ge_of_lower (h0LowerBound O)

/-- **The uniform form** (the hypothesis of β″'s `mebInputs_of_lower`): one constant `cHB B > 0` for every
obstruction data. -/
theorem h0LowerBound_uniform : ∀ (d₀ d₁ m : ℕ) (B : Fin m → AbBlock), ∃ cH : ℕ, 0 < cH ∧
    ∀ O : ObstrDataB d₀ d₁ B, H0LowerBound O cH :=
  fun _ _ _ B => ⟨cHB B, one_le_cHB, fun O => h0LowerBound O⟩

theorem cHB_nLaw_pos : 0 < cHB B * nLaw B * 2 ^ m := by
  have h1 := one_le_cHB (B := B)
  have h2 : 0 < nLaw B := by
    unfold nLaw
    exact Finset.prod_pos fun k _ => by
      rcases Nat.eq_zero_or_pos (B k).nL with h | h
      · exact absurd h (by
          intro h0
          obtain ⟨i, -⟩ := (B k).law_complete 0 0
          exact (Fin.elim0 (h0 ▸ i)))
      · exact h
  positivity

end LSG.MEB
