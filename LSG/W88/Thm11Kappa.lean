/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.K11Sub

/-!
# `lean_mstar`'s hypothesis `Thm11Kappa` from W88 Thm 4.1 (the §5d deduction)

`thm11Kappa_of_theorem41 : Theorem41Abelian → MStarCopy.Thm11Kappa L d₁`, where
`MStarCopy.Thm11Kappa` (file `LSG/W88/MStarCopy.lean`) is a verbatim copy of
`CM4E.Waldschmidt.Thm11Kappa` (`lean_mstar/CM4E/Waldschmidt.lean`): W88 Thm 1.1 with (1.2)
replaced by (5.4), `m > (d₁ + 2 − κ)(d − 1 − t)`, for `G = G_m^{d₁} × E`.

## The argument (W88 §5, Lemmas 5.1, 5.2 and §5d, specialised to `G_m^{d₁} × E`)

Suppose `V` contains no nonzero `tangentSub ℒ b`. For a connected algebraic subgroup
`G' = T_ℒ × (0 or E)` put `a(G') = rk(Γ ∩ G') + d₁' + 2d₂'` and `e(G') = dim G' − dim (W ∩ T_{G'})`
(`aF`, `eF`). Every `G' ≠ 0` has `e(G') > 0`, and (5.4) says `a(G) > D e(G)`, `D = d₁ + 2 − κ`.
Choose `G' ≠ 0` maximising `a/e` (Lemma 5.1); then `a(G') > D e(G')` and `T_{G'} ⊄ V`, so
`V' = V ∩ T_{G'}` is a hyperplane of `T_{G'}`. Apply Thm 4.1 to `G'`, `V'`, `W ∩ T_{G'}`,
`Y ∩ T_{G'}` (`thm41Sub`; its hypothesis (NR) `2 dim V' ≥ d₁' + κ'` can fail only when
`κ' ≥ d₁' + 2d₂' − 1`, and that corner is handled directly below: it forces a period line
`0 × ℂ ⊂ V`, a rational toric line in `V`, or `V' = 0`). The resulting `G'' ⊂ G'`, together with
Lemma 5.2 (`rk Γ' ≥ rk (Γ ∩ G') − D + D'`) and the maximality of `G'`, gives
`(s − 1)(D − D') < 0` with `s ≥ 1`, `D ≥ D'`: a contradiction.
-/

open Complex Module

namespace LSG.W88

open MStarCopy

namespace K11

variable {d₁ : ℕ}

lemma finrank_tangentSub (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) :
    finrank ℂ (tangentSub ℒ b) = finrank ℚ ℒ + b.toNat := by
  obtain ⟨C, D, hDC, hC⟩ := exists_frame ℒ
  rw [← range_iotaL hDC hC b, LinearMap.finrank_range_of_inj (iotaL_injective hDC b)]
  simp

lemma finrank_T : finrank ℂ (T d₁) = d₁ + 1 := by simp

lemma fg_of_le_addSubgroup {E : Type*} [AddCommGroup E] {P Q : AddSubgroup E} (hP : P.FG)
    (h : Q ≤ P) : Q.FG := by
  have : Module.Finite ℤ P := Module.Finite.iff_addGroup_fg.mpr hP
  have : Module.Finite ℤ Q :=
    Module.Finite.of_injective (AddSubgroup.inclusion h).toIntLinearMap
      (AddSubgroup.inclusion_injective h)
  exact Module.Finite.iff_addGroup_fg.mp this

lemma exists_ne_zero_of_finrank_map_lt {E F : Type*} [AddCommGroup E] [Module ℚ E]
    [AddCommGroup F] [Module ℚ F] (X : Submodule ℚ E) [FiniteDimensional ℚ X] (f : E →ₗ[ℚ] F)
    (h : finrank ℚ (X.map f) < finrank ℚ X) : ∃ x ∈ X, x ≠ 0 ∧ f x = 0 := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective (f.comp X.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    exact hne x x.2 (fun h0 => hx0 (Subtype.ext h0)) hx
  have := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at this
  omega

/-- The final inequality chase of §5d. -/
lemma arith_final {a a'' e e'' s D D' : ℤ} (hmx : a'' * e ≤ a * e'') (hes : e'' = e - s)
    (hX : a - a'' ≤ s * D' + (D - D')) (he : 0 < e) (ha : D * e < a) (hs1 : 1 ≤ s)
    (hDD : D' ≤ D) : False := by
  subst hes
  have hstep : a * s ≤ (s * D' + (D - D')) * e := by
    nlinarith [mul_le_mul_of_nonneg_right hX he.le]
  have hstep2 : D * e * s < a * s := mul_lt_mul_of_pos_right ha (by linarith)
  have h3 : (s - 1) * (D - D') * e < 0 := by nlinarith
  have h4 : 0 ≤ (s - 1) * (D - D') * e :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) he.le
  linarith

/-- **The core of the §5d deduction.** -/
theorem core (h : Theorem41Abelian) (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂)
    (hg₃ : IsAlgebraic ℚ L.g₃) (V W : Submodule ℂ (T d₁)) (Y : AddSubgroup (T d₁)) (hYfg : Y.FG)
    (hY : ∀ y ∈ Y, y ∈ V ∧ GoodPt L y) (hV : finrank ℂ V = d₁) (hWV : W ≤ V) (hWrat : RatSub W)
    (hno : ∀ ℒ b, tangentSub ℒ b ≤ V → tangentSub ℒ b = ⊥)
    (hineq : ((finrank ℚ (Submodule.span ℚ (Y : Set (T d₁))) : ℤ) >
      ((d₁ : ℤ) + 2 - finrank ℚ ↥(Submodule.span ℚ (Y : Set (T d₁)) ⊓ OmegaQ L d₁)) *
        ((d₁ : ℤ) - finrank ℂ W))) : False := by
  classical
  set Yq := Submodule.span ℚ (Y : Set (T d₁)) with hYq
  have : FiniteDimensional ℚ Yq := finiteDimensional_span_of_fg hYfg
  set Ω := OmegaQ L d₁ with hΩ
  set κ := finrank ℚ ↥(Yq ⊓ Ω) with hκ
  have hκle : κ ≤ d₁ + 2 := (Submodule.finrank_mono inf_le_right).trans (finrank_omegaQ L).le
  have hYV : Yq ≤ V.restrictScalars ℚ := Submodule.span_le.mpr fun y hy => (hY y hy).1
  let aF : Submodule ℚ (Fin d₁ → ℚ) × Bool → ℤ := fun p =>
    (finrank ℚ ↥(Yq ⊓ (Tq p.1 p.2 ⊔ Ω)) : ℤ) - κ + nP p.1 p.2
  let eF : Submodule ℚ (Fin d₁ → ℚ) × Bool → ℤ := fun p =>
    (nT p.1 p.2 : ℤ) - finrank ℂ ↥(W ⊓ tangentSub p.1 p.2)
  -- every nonzero `G'` has `e(G') > 0`
  have he : ∀ p : Submodule ℚ (Fin d₁ → ℚ) × Bool, tangentSub p.1 p.2 ≠ ⊥ → 0 < eF p := by
    intro p hp
    have h1 : finrank ℂ ↥(W ⊓ tangentSub p.1 p.2) ≤ finrank ℂ (tangentSub p.1 p.2) :=
      Submodule.finrank_mono inf_le_right
    have h2 : finrank ℂ ↥(W ⊓ tangentSub p.1 p.2) ≠ finrank ℂ (tangentSub p.1 p.2) := by
      intro heq
      have := Submodule.eq_of_le_of_finrank_eq inf_le_right heq
      exact hp (hno p.1 p.2 (this ▸ inf_le_left |>.trans hWV))
    rw [finrank_tangentSub] at h1 h2
    simp only [eF, nT]; omega
  -- the values at `0`
  have hzero : ∀ p : Submodule ℚ (Fin d₁ → ℚ) × Bool, tangentSub p.1 p.2 = ⊥ →
      aF p = 0 ∧ eF p = 0 := by
    intro p hp
    have hf := finrank_tangentSub p.1 p.2
    rw [hp, finrank_bot] at hf
    have hTq : Tq p.1 p.2 = ⊥ := by
      change (tangentSub p.1 p.2).restrictScalars ℚ = ⊥; rw [hp]; rfl
    have hYT : Yq ⊓ (Tq p.1 p.2 ⊔ Ω) = Yq ⊓ Ω := by rw [hTq, bot_sup_eq]
    refine ⟨?_, ?_⟩
    · change (finrank ℚ ↥(Yq ⊓ (Tq p.1 p.2 ⊔ Ω)) : ℤ) - κ + nP p.1 p.2 = 0
      rw [hYT]; simp only [nP]; omega
    · change (nT p.1 p.2 : ℤ) - finrank ℂ ↥(W ⊓ tangentSub p.1 p.2) = 0
      rw [hp, inf_bot_eq, finrank_bot]; simp only [nT]; omega
  -- the value at `G`
  have hTG : tangentSub (⊤ : Submodule ℚ (Fin d₁ → ℚ)) true = ⊤ := by
    rw [tangentSub_eq, cspan_top]; simp
  have hGC : tangentSub (⊤ : Submodule ℚ (Fin d₁ → ℚ)) true ≠ ⊥ := by
    rw [hTG]; exact top_ne_bot
  have haG : aF (⊤, true) = (finrank ℚ Yq : ℤ) - κ + (d₁ + 2) := by
    have : Tq (⊤ : Submodule ℚ (Fin d₁ → ℚ)) true = ⊤ := by
      change (tangentSub ⊤ true).restrictScalars ℚ = ⊤; rw [hTG]; rfl
    change (finrank ℚ ↥(Yq ⊓ (Tq ⊤ true ⊔ Ω)) : ℤ) - κ + nP ⊤ true = _
    rw [this, top_sup_eq, inf_top_eq]
    simp only [nP, finrank_top, finrank_fin_fun, Bool.toNat_true]
    push_cast; ring
  have heG : eF (⊤, true) = (d₁ : ℤ) + 1 - finrank ℂ W := by
    change (nT ⊤ true : ℤ) - finrank ℂ ↥(W ⊓ tangentSub ⊤ true) = _
    rw [hTG, inf_top_eq]
    simp only [nT, finrank_top, finrank_fin_fun, Bool.toNat_true]
    push_cast; ring
  set D : ℤ := (d₁ : ℤ) + 2 - κ with hD
  have hD0 : 0 ≤ D := by omega
  have hGineq : D * eF (⊤, true) < aF (⊤, true) := by
    rw [haG, heG]
    have : D * ((d₁ : ℤ) + 1 - finrank ℂ W) = D * ((d₁ : ℤ) - finrank ℂ W) + D := by ring
    rw [this]; simp only [hD] at hineq ⊢; linarith
  -- Lemma 5.1: a maximiser of `a/e`
  set S : Set (ℤ × ℤ) := (fun p => (aF p, eF p)) ''
    {p : Submodule ℚ (Fin d₁ → ℚ) × Bool | tangentSub p.1 p.2 ≠ ⊥} with hS
  have hSfin : S.Finite := by
    refine ((Set.finite_Icc (-(κ : ℤ)) (finrank ℚ Yq + d₁ + 2)).prod
      (Set.finite_Icc (-(d₁ : ℤ) - 1) (d₁ + 1))).subset ?_
    rintro _ ⟨p, -, rfl⟩
    have h1 : finrank ℚ ↥(Yq ⊓ (Tq p.1 p.2 ⊔ Ω)) ≤ finrank ℚ Yq :=
      Submodule.finrank_mono inf_le_left
    have h2 : finrank ℚ p.1 ≤ d₁ := (Submodule.finrank_le p.1).trans (by simp)
    have h3 : finrank ℂ ↥(W ⊓ tangentSub p.1 p.2) ≤ d₁ + 1 :=
      (Submodule.finrank_le _).trans finrank_T.le
    have h4 : p.2.toNat ≤ 1 := Bool.toNat_le p.2
    simp only [Set.mem_prod, Set.mem_Icc, aF, eF, nP, nT]
    omega
  obtain ⟨_, ⟨⟨ℒ, b⟩, hC', rfl⟩, hmax⟩ := Set.exists_max_image S (fun q : ℤ × ℤ =>
    (q.1 : ℚ) / q.2) hSfin ⟨_, ⟨(⊤, true), hGC, rfl⟩⟩
  have hC : tangentSub ℒ b ≠ ⊥ := hC'
  have he' : 0 < eF (ℒ, b) := he (ℒ, b) hC
  have hmaxAll : ∀ p, aF p * eF (ℒ, b) ≤ aF (ℒ, b) * eF p := by
    intro p
    by_cases hp : tangentSub p.1 p.2 = ⊥
    · obtain ⟨h1, h2⟩ := hzero p hp; rw [h1, h2]; simp
    · have := hmax _ ⟨p, hp, rfl⟩
      simp only at this
      rw [div_le_div_iff₀ (by exact_mod_cast he p hp) (by exact_mod_cast he')] at this
      exact_mod_cast this
  have ha' : D * eF (ℒ, b) < aF (ℒ, b) := by
    have h1 := hmaxAll (⊤, true)
    have heG' := he (⊤, true) hGC
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_right hGineq he', mul_le_mul_of_nonneg_right hcon heG'.le]
  -- the maximiser `G' = (ℒ, b)`
  set T' := tangentSub ℒ b with hT'
  have hT'V : ¬ T' ≤ V := fun hle => hC (hno ℒ b hle)
  set V' := V ⊓ T' with hV'
  have hVdim : finrank ℂ V' + 1 = nT ℒ b := by
    have hlt : V < V ⊔ T' := lt_of_le_of_ne le_sup_left fun heq => hT'V (heq ▸ le_sup_right)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank ℂ ↥(V ⊔ T') ≤ d₁ + 1 := (Submodule.finrank_le _).trans finrank_T.le
    have h3 : finrank ℂ ↥(V ⊔ T') + finrank ℂ V' = finrank ℂ V + (finrank ℚ ℒ + b.toNat) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq V T'
      rwa [hT', finrank_tangentSub] at this
    rw [hV] at h1 h3
    change finrank ℂ V' + 1 = finrank ℚ ℒ + b.toNat
    omega
  set Y' := Y ⊓ T'.toAddSubgroup with hY'
  have hY'fg : Y'.FG := fg_of_le_addSubgroup hYfg inf_le_left
  have hY'mem : ∀ y ∈ Y', y ∈ V' ∧ GoodPt L y := fun y hy =>
    ⟨⟨(hY y hy.1).1, hy.2⟩, (hY y hy.1).2⟩
  have hspan' : Submodule.span ℚ (Y' : Set (T d₁)) = Yq ⊓ Tq ℒ b := by
    rw [hY', span_inf_addSubgroup, span_submodule_coe]
  set κ' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (T d₁)) ⊓ Ω) with hκ'
  set m' := finrank ℚ ↥(Submodule.span ℚ (Y' : Set (T d₁))) with hm'
  have hΩT := finrank_omegaQ_inf_tangent L ℒ b
  have hΩd := finrank_omegaQ L (d₁ := d₁)
  -- Lemma 5.2: `r' ≤ m' + (d₁ + 2) − n'`
  have hL52 : finrank ℚ ↥(Yq ⊓ (Tq ℒ b ⊔ Ω)) + nP ℒ b ≤ m' + (d₁ + 2) := by
    have := finrank_le_of_le_sup (Yq ⊓ (Tq ℒ b ⊔ Ω)) (Tq ℒ b) Ω inf_le_right
    have e : Yq ⊓ (Tq ℒ b ⊔ Ω) ⊓ Tq ℒ b = Yq ⊓ Tq ℒ b := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_left : Tq ℒ b ≤ Tq ℒ b ⊔ Ω)]
    rw [e, hΩT, hΩd, ← hspan'] at this
    simp only [nP]; omega
  -- `κ − κ' ≤ (d₁ + 2) − n'`
  have hLk : κ + nP ℒ b ≤ κ' + (d₁ + 2) := by
    have := finrank_le_of_le_sup (Yq ⊓ Ω) (Tq ℒ b) Ω (inf_le_right.trans le_sup_right)
    have e : Yq ⊓ Ω ⊓ Tq ℒ b = Submodule.span ℚ (Y' : Set (T d₁)) ⊓ Ω := by
      rw [hspan', inf_right_comm]
    rw [e, hΩT, hΩd] at this
    simp only [nP]; omega
  have he'v : eF (ℒ, b) = (nT ℒ b : ℤ) - finrank ℂ ↥(W ⊓ T') := rfl
  have ha'v : aF (ℒ, b) = (finrank ℚ ↥(Yq ⊓ (Tq ℒ b ⊔ Ω)) : ℤ) - κ + nP ℒ b := rfl
  by_cases hNR : finrank ℚ ℒ + κ' ≤ 2 * finrank ℂ V'
  · -- the main case: Theorem 4.1 for `G'`
    obtain ⟨ℒ'', b'', hT''T, hτ, hin⟩ := thm41Sub h L hg₂ hg₃ ℒ b V' (W ⊓ T') Y' inf_le_right
      hVdim (inf_le_inf_right _ hWV) (ratSub_inf_tangent hWrat ℒ b) hY'fg hY'mem hNR
    have hWW : W ⊓ T' ⊓ tangentSub ℒ'' b'' = W ⊓ tangentSub ℒ'' b'' := by
      rw [inf_assoc, inf_eq_right.mpr hT''T]
    rw [hWW] at hτ hin
    -- `rk Γ' ∩ G''` vs `rk Γ ∩ G''`
    have hlam : finrank ℚ ↥(Submodule.span ℚ (Y' : Set (T d₁)) ⊓ (Tq ℒ'' b'' ⊔ Ω)) + κ ≤
        finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ Ω)) + κ' := by
      have hle : Submodule.span ℚ (Y' : Set (T d₁)) ⊓ (Tq ℒ'' b'' ⊔ Ω) ≤
          Yq ⊓ (Tq ℒ'' b'' ⊔ Ω) := inf_le_inf_right _ (Submodule.span_mono inf_le_left)
      have : FiniteDimensional ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ Ω)) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have := finrank_le_of_le _ _ Ω hle
      have e1 : Yq ⊓ (Tq ℒ'' b'' ⊔ Ω) ⊓ Ω = Yq ⊓ Ω := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ Tq ℒ'' b'' ⊔ Ω)]
      have e2 : Submodule.span ℚ (Y' : Set (T d₁)) ⊓ (Tq ℒ'' b'' ⊔ Ω) ⊓ Ω =
          Submodule.span ℚ (Y' : Set (T d₁)) ⊓ Ω := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Ω ≤ Tq ℒ'' b'' ⊔ Ω)]
      rw [e1, e2] at this
      omega
    have hmx := hmaxAll (ℒ'', b'')
    have he''v : eF (ℒ'', b'') = (nT ℒ'' b'' : ℤ) - finrank ℂ ↥(W ⊓ tangentSub ℒ'' b'') := rfl
    have ha''v : aF (ℒ'', b'') =
        (finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ Ω)) : ℤ) - κ + nP ℒ'' b'' := rfl
    -- integer bookkeeping
    set s : ℤ := ((nT ℒ b : ℤ) - nT ℒ'' b'') -
      ((finrank ℂ ↥(W ⊓ T') : ℤ) - finrank ℂ ↥(W ⊓ tangentSub ℒ'' b'')) with hs
    have hs1 : 1 ≤ s := by simp only [hs]; omega
    have hes : eF (ℒ'', b'') = eF (ℒ, b) - s := by rw [he''v, he'v, hs]; ring
    set D' : ℤ := (nP ℒ b : ℤ) - κ' with hD'
    have hDD : D' ≤ D := by simp only [hD, hD']; omega
    have hX : aF (ℒ, b) - aF (ℒ'', b'') ≤ s * D' + (D - D') := by
      rw [ha'v, ha''v]
      have h1 : (finrank ℚ ↥(Yq ⊓ (Tq ℒ b ⊔ Ω)) : ℤ) + nP ℒ b ≤ m' + (d₁ + 2) := by
        exact_mod_cast hL52
      have h2 : (finrank ℚ ↥(Submodule.span ℚ (Y' : Set (T d₁)) ⊓ (Tq ℒ'' b'' ⊔ Ω)) : ℤ) + κ ≤
          finrank ℚ ↥(Yq ⊓ (Tq ℒ'' b'' ⊔ Ω)) + κ' := by exact_mod_cast hlam
      simp only [hD, hD']
      linarith
    exact arith_final hmx hes hX he' ha' hs1 hDD
  · -- the corner `κ' ≥ d₁' + 2d₂' − 1`
    have hspanV : Submodule.span ℚ (Y' : Set (T d₁)) ≤ V.restrictScalars ℚ :=
      Submodule.span_le.mpr fun y hy => (hY'mem y hy).1.1
    set X := Submodule.span ℚ (Y' : Set (T d₁)) ⊓ Ω with hX
    have hXΩT : X ≤ Ω ⊓ Tq ℒ b := by
      rw [hX, hspan']; exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have hfX : finrank ℚ X = κ' := rfl
    have : FiniteDimensional ℚ X := Submodule.finiteDimensional_of_le inf_le_right
    cases b
    · -- `b = false`
      have hk1 : 1 ≤ finrank ℚ ℒ := by
        have h1 : finrank ℂ T' = finrank ℚ ℒ + false.toNat := finrank_tangentSub ℒ false
        have h2 : finrank ℂ T' ≠ 0 := fun h0 => hC (Submodule.finrank_eq_zero.mp h0)
        simp only [Bool.toNat_false, add_zero] at h1
        omega
      simp only [nT, Bool.toNat_false, add_zero] at hVdim
      by_cases hk2 : 2 ≤ finrank ℚ ℒ
      · have hXne : X ≠ ⊥ := by
          intro hX0
          have h0 : finrank ℚ X = 0 := by rw [hX0]; exact finrank_bot ℚ _
          omega
        obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
        have hxΩT := hXΩT hxX
        obtain ⟨q, p₁, p₂, rfl⟩ := (mem_omegaQ L).mp hxΩT.1
        have hxT : PhiL L d₁ (q, p₁, p₂) ∈ tangentSub ℒ false := hxΩT.2
        rw [mem_tangentSub, phiL_apply] at hxT
        obtain ⟨rfl, rfl⟩ := rat_indep L (hxT.2.resolve_left (by simp))
        have hq0 : q ≠ 0 := by rintro rfl; exact hx0 (by simp [phiL_apply])
        have hxV : PhiL L d₁ (q, 0, 0) ∈ V :=
          hspanV ((show X ≤ Submodule.span ℚ (Y' : Set (T d₁)) from inf_le_left) hxX)
        apply hq0
        have hle : tangentSub (Submodule.span ℚ {q}) false ≤ V := by
          intro u hu
          rw [mem_tangentSub, cspan_span, Set.image_singleton, Submodule.mem_span_singleton] at hu
          obtain ⟨⟨c, hc⟩, hu2⟩ := hu
          have hu2' : u.2 = 0 := hu2.resolve_left (by simp)
          have : u = (c / (2 * Real.pi * I)) • PhiL L d₁ (q, 0, 0) := by
            rw [phiL_apply]
            refine Prod.ext ?_ ?_
            · simp only [Prod.smul_fst, smul_smul, div_mul_cancel₀ _ two_pi_I_ne_zero, hc]
            · simp [hu2']
          rw [this]; exact V.smul_mem _ hxV
        have hbot := hno _ _ hle
        have hmem : (castL d₁ q, (0 : ℂ)) ∈ tangentSub (Submodule.span ℚ {q}) false := by
          rw [mem_tangentSub]
          exact ⟨castL_mem_cspan (Submodule.mem_span_singleton_self q), Or.inr rfl⟩
        rw [hbot, Submodule.mem_bot, Prod.mk_eq_zero] at hmem
        exact castL_injective d₁ (by rw [hmem.1, map_zero])
      · -- `dim ℒ = 1`: then `V' = 0`
        have hk : finrank ℚ ℒ = 1 := by omega
        have hV'0 : V' = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
        have hm0 : m' = 0 := by
          have : Submodule.span ℚ (Y' : Set (T d₁)) = ⊥ := by
            rw [Submodule.span_eq_bot]
            intro y hy
            have := (hY'mem y hy).1
            rw [hV'0, Submodule.mem_bot] at this; exact this
          rw [hm', this]; exact finrank_bot ℚ _
        have hA : aF (ℒ, false) ≤ D := by
          rw [ha'v]
          have h1 : (finrank ℚ ↥(Yq ⊓ (Tq ℒ false ⊔ Ω)) : ℤ) + nP ℒ false ≤ m' + (d₁ + 2) := by
            exact_mod_cast hL52
          have h2 : (nP ℒ false : ℤ) = 1 := by simp [nP, hk]
          rw [hm0] at h1
          simp only [hD]; push_cast at h1; linarith
        have h2 : (1 : ℤ) ≤ eF (ℒ, false) := he'
        have h3 : D ≤ D * eF (ℒ, false) := le_mul_of_one_le_right hD0 h2
        linarith
    · -- `b = true`
      simp only [nT, Bool.toNat_true] at hVdim
      have hXfst : finrank ℚ ↥(X.map (LinearMap.fst ℚ (Fin d₁ → ℂ) ℂ)) < finrank ℚ X := by
        have h1 := (Submodule.finrank_mono (Submodule.map_mono hXΩT)).trans
          (finrank_map_fst_le L ℒ true)
        omega
      obtain ⟨x, hxX, hx0, hx1⟩ := exists_ne_zero_of_finrank_map_lt X _ hXfst
      have hxV : x ∈ V :=
        hspanV ((show X ≤ Submodule.span ℚ (Y' : Set (T d₁)) from inf_le_left) hxX)
      have hx1' : x.1 = 0 := hx1
      have hx2 : x.2 ≠ 0 := fun h2 => hx0 (Prod.ext hx1' h2)
      have hle : tangentSub (⊥ : Submodule ℚ (Fin d₁ → ℚ)) true ≤ V := by
        intro u hu
        rw [mem_tangentSub, cspan_bot, Submodule.mem_bot] at hu
        have : u = (u.2 / x.2) • x := by
          refine Prod.ext ?_ ?_
          · simp [hu.1, hx1']
          · simp [div_mul_cancel₀ _ hx2]
        rw [this]; exact V.smul_mem _ hxV
      have hbot := hno _ _ hle
      have hmem : ((0 : Fin d₁ → ℂ), (1 : ℂ)) ∈ tangentSub (⊥ : Submodule ℚ (Fin d₁ → ℚ)) true := by
        rw [mem_tangentSub, cspan_bot]; exact ⟨Submodule.zero_mem _, Or.inl rfl⟩
      rw [hbot, Submodule.mem_bot, Prod.mk_eq_zero] at hmem
      exact one_ne_zero hmem.2

end K11

open K11 in
/-- **W88 §5d: `lean_mstar`'s hypothesis `Thm11Kappa` follows from Theorem 4.1.** -/
theorem thm11Kappa_of_theorem41 (h : Theorem41Abelian) (L : PeriodPair) (d₁ : ℕ) :
    MStarCopy.Thm11Kappa L d₁ := by
  intro hg₂ hg₃ V W m y hV hWV hWrat hy hineq
  by_contra hcon
  have hno : ∀ ℒ b, tangentSub ℒ b ≤ V → tangentSub ℒ b = ⊥ := fun ℒ b hle =>
    by_contra fun hne => hcon ⟨_, ⟨ℒ, b, rfl⟩, hne, hle⟩
  set Y := AddSubgroup.closure (Set.range y) with hY
  have hspanY : Submodule.span ℚ (Y : Set (T d₁)) = Submodule.span ℚ (Set.range y) :=
    span_closure_eq _
  have hYle : Y ≤ V.toAddSubgroup ⊓ goodSub L hg₂ d₁ := by
    rw [hY, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hy i).1, mem_goodSub_of_expAlg L hg₂ (hy i).2⟩
  have hVd : finrank ℂ V = d₁ := by rw [finrank_T] at hV; omega
  refine core h L hg₂ hg₃ V W Y ((AddSubgroup.fg_iff _).mpr ⟨_, rfl, Set.finite_range y⟩)
    (fun z hz => ⟨(hYle hz).1, goodPt_of_mem L hg₂ (hYle hz).2⟩) hVd hWV hWrat hno ?_
  rw [hspanY]
  have := hineq
  simp only [gmE, finrank_T] at this
  push_cast at this
  convert this using 2
  · rfl
  · ring

end LSG.W88
