/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAnV.KChart
import LSG.JacAnV.PD

/-!
# M2.2 (N1): Lemma K♮ by Liouville

For an entire lift `Θ : ℂ² → ℂ⁹` with the chart-0 projective flow, on the model, with a nonzero `Θ₀`, covered by the
charts `{0, 4, 8}` and quasi-periodic with affine-exponential factors on `latt` (`KHyp`; instance for `θ_N` in
`KTheta.lean`), put, for `c ∈ {0, 4, 8}`,

  `G_c := Θ_c ∂_i∂_jΘ_c − ∂_iΘ_c ∂_jΘ_c + Q_{c,ij}(Θ)`   (`kG`; `Q_{0,ij} = 3 Θ_m Θ₀`).

* `KHyp.kG_compat`: `Θ_c² G_{c'} = Θ_{c'}² G_c` (the chart identities `kChart_alg` + the identity theorem);
* `kH := G_c / Θ_c²` for a chart with `Θ_c ≠ 0` is well defined (`kH_eq`), entire, and `latt`-periodic;
* **`KHyp.lemmaK`**: `G_c = K_ij Θ_c²` for constants `K_ij` (Liouville), i.e. in chart 0
  `∂_i∂_j log Θ₀ = −3 ℘_ij + K_ij` (M2.md §2.2 N1).
-/

noncomputable section

open Metric Set Filter Topology Bornology

namespace LSG.JacAnV

open LSG.JacAn

section polyAn

variable {X : P9} {f g : P9 → ℂ}

lemma an_add (hf : AnalyticAt ℂ f X) (hg : AnalyticAt ℂ g X) : AnalyticAt ℂ (fun X => f X + g X) X := hf.add hg
lemma an_sub (hf : AnalyticAt ℂ f X) (hg : AnalyticAt ℂ g X) : AnalyticAt ℂ (fun X => f X - g X) X := hf.sub hg
lemma an_mul (hf : AnalyticAt ℂ f X) (hg : AnalyticAt ℂ g X) : AnalyticAt ℂ (fun X => f X * g X) X := hf.mul hg
lemma an_neg (hf : AnalyticAt ℂ f X) : AnalyticAt ℂ (fun X => -f X) X := hf.neg
lemma an_pow (hf : AnalyticAt ℂ f X) (n : ℕ) : AnalyticAt ℂ (fun X => f X ^ n) X := hf.pow n
lemma an_coord (a : Fin 9) : AnalyticAt ℂ (fun X : P9 => X a) X :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) a).analyticAt X

end polyAn

/-- `z ↦ kQ c i j X` is analytic for the three charts. -/
lemma kQ_analytic {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (i j : Fin 2) (X : P9) :
    AnalyticAt ℂ (fun X => kQ c i j X) X := by
  rcases hc with rfl | rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp only [kQ, mIdx, Matrix.cons_val, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.zero_eta, Fin.mk_one] <;>
    apply_rules [an_add, an_sub, an_mul, an_neg, an_pow, an_coord, analyticAt_const]

/-- The hypotheses of Lemma K♮ on a lift `Θ`. -/
structure KHyp (Θ : (Fin 2 → ℂ) → P9) : Prop where
  an : ∀ z, AnalyticAt ℂ Θ z
  pf : ∀ w, PFAt flowW 1 0 Θ w
  quad : ∀ z r, quadA (Θ z) r = 0
  ne0 : ∃ w, Θ w 0 ≠ 0
  cover : ∀ z, Θ z 0 ≠ 0 ∨ Θ z 4 ≠ 0 ∨ Θ z 8 ≠ 0
  per : ∀ ω ∈ latt, ∃ (a : ℂ) (ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ), ∀ z, Θ (z + ω) = (a * Complex.exp (ℓ z)) • Θ z

/-- `G_c = Θ_c ∂_i∂_jΘ_c − ∂_iΘ_c ∂_jΘ_c + Q_{c,ij}(Θ)`. -/
def kG (Θ : (Fin 2 → ℂ) → P9) (c : Fin 9) (i j : Fin 2) (z : Fin 2 → ℂ) : ℂ :=
  Θ z c * pd i (pd j (cmpV Θ c)) z - pd i (cmpV Θ c) z * pd j (cmpV Θ c) z + kQ c i j (Θ z)

/-- The chart index used to define `kH`. -/
def kc (Θ : (Fin 2 → ℂ) → P9) (z : Fin 2 → ℂ) : Fin 9 :=
  if Θ z 0 ≠ 0 then 0 else if Θ z 4 ≠ 0 then 4 else 8

/-- `kH = G_c / Θ_c²` in the chart `kc`. -/
def kH (Θ : (Fin 2 → ℂ) → P9) (i j : Fin 2) (z : Fin 2 → ℂ) : ℂ := kG Θ (kc Θ z) i j z / Θ z (kc Θ z) ^ 2

lemma kc_mem (Θ : (Fin 2 → ℂ) → P9) (z : Fin 2 → ℂ) : kc Θ z = 0 ∨ kc Θ z = 4 ∨ kc Θ z = 8 := by
  unfold kc; split_ifs <;> simp

namespace KHyp

variable {Θ : (Fin 2 → ℂ) → P9} (h : KHyp Θ)
include h

lemma kc_ne (z : Fin 2 → ℂ) : Θ z (kc Θ z) ≠ 0 := by
  unfold kc
  split_ifs with h0 h4
  · exact h0
  · exact h4
  · rcases h.cover z with h0' | h4' | h8'
    · exact absurd h0' h0
    · exact absurd h4' h4
    · exact h8'

lemma ent_cmp' (c : Fin 9) : Ent (cmpV Θ c) := ent_cmp h.an c

lemma ent_kG {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (i j : Fin 2) : Ent (kG Θ c i j) := by
  have hm := h.ent_cmp' c
  have e : kG Θ c i j = fun z => (cmpV Θ c z * pd i (pd j (cmpV Θ c)) z - pd i (cmpV Θ c) z * pd j (cmpV Θ c) z) +
      kQ c i j (Θ z) := rfl
  rw [e]
  exact ((hm.mul ((hm.pd j).pd i)).sub ((hm.pd i).mul (hm.pd j))).add
    (fun z => (kQ_analytic hc i j _).comp (h.an z))

/-- PF in `pd` form. -/
lemma pf_pd (j : Fin 2) (l : Fin 9) (w : Fin 2 → ℂ) :
    Θ w 0 * pd j (cmpV Θ l) w - Θ w l * pd j (cmpV Θ 0) w = flowW j (Θ w) l := by
  have e := h.pf w (Pi.single j 1) l
  rw [pd_cmp (h.an w).differentiableAt, pd_cmp (h.an w).differentiableAt, e, one_mul]
  fin_cases j <;> simp

/-- **The chart identity** (before the identity theorem). -/
theorem kG_chart0 {k : Fin 9} (hk : k = 4 ∨ k = 8) (i j : Fin 2) (z : Fin 2 → ℂ) :
    Θ z 0 * (Θ z k ^ 2 * kG Θ 0 i j z - Θ z 0 ^ 2 * kG Θ k i j z) = 0 := by
  have hc : ∀ c, Ent (cmpV Θ c) := h.ent_cmp'
  have hfun : (fun w => cmpV Θ 0 w * pd j (cmpV Θ k) w - cmpV Θ k w * pd j (cmpV Θ 0) w) =
      fun w => flowW j (Θ w) k := funext fun w => h.pf_pd j k w
  have hE1 := pd_congr (z := z) hfun i
  rw [pd_sub (((hc 0).mul ((hc k).pd j)) z).differentiableAt (((hc k).mul ((hc 0).pd j)) z).differentiableAt,
    pd_mul ((hc 0).diff z) (((hc k).pd j).diff z), pd_mul ((hc k).diff z) (((hc 0).pd j).diff z),
    pd_flowW (fun c => (hc c).diff z)] at hE1
  exact kChart_alg hk i j (Θ z) (pdv i Θ z) (fun a => pd j (cmpV Θ a) z) (pd i (pd j (cmpV Θ 0)) z)
    (pd i (pd j (cmpV Θ k)) z) (h.quad z) hE1 (h.pf_pd j k z) (fun a => h.pf_pd i a z)

lemma ent_sq (c : Fin 9) : Ent (fun z => Θ z c ^ 2) := fun z => ((h.ent_cmp' c) z).pow 2

theorem kG_compat0 {k : Fin 9} (hk : k = 4 ∨ k = 8) (i j : Fin 2) (z : Fin 2 → ℂ) :
    Θ z k ^ 2 * kG Θ 0 i j z = Θ z 0 ^ 2 * kG Θ k i j z := by
  obtain ⟨w, hw⟩ := h.ne0
  have hk' : k = 0 ∨ k = 4 ∨ k = 8 := Or.inr hk
  have := eq_zero_of_mul_eq_zero_analytic (f := cmpV Θ 0)
    (g := fun z => Θ z k ^ 2 * kG Θ 0 i j z - Θ z 0 ^ 2 * kG Θ k i j z) (h.ent_cmp' 0)
    (((h.ent_sq k).mul (h.ent_kG (Or.inl rfl) i j)).sub ((h.ent_sq 0).mul (h.ent_kG hk' i j)))
    (fun z => h.kG_chart0 hk i j z) hw z
  exact sub_eq_zero.mp this

/-- **Chart compatibility**: `Θ_c² G_{c'} = Θ_{c'}² G_c` for `c, c' ∈ {0, 4, 8}`. -/
theorem kG_compat {c c' : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (hc' : c' = 0 ∨ c' = 4 ∨ c' = 8)
    (i j : Fin 2) (z : Fin 2 → ℂ) : Θ z c ^ 2 * kG Θ c' i j z = Θ z c' ^ 2 * kG Θ c i j z := by
  have h48 : ∀ z, Θ z 8 ^ 2 * kG Θ 4 i j z = Θ z 4 ^ 2 * kG Θ 8 i j z := by
    obtain ⟨w, hw⟩ := h.ne0
    intro z
    have hmul : ∀ z, Θ z 0 ^ 2 * (Θ z 8 ^ 2 * kG Θ 4 i j z - Θ z 4 ^ 2 * kG Θ 8 i j z) = 0 := fun z => by
      have e4 := h.kG_compat0 (k := 4) (Or.inl rfl) i j z
      have e8 := h.kG_compat0 (k := 8) (Or.inr rfl) i j z
      linear_combination Θ z 4 ^ 2 * e8 - Θ z 8 ^ 2 * e4
    have := eq_zero_of_mul_eq_zero_analytic (f := fun z => Θ z 0 ^ 2)
      (g := fun z => Θ z 8 ^ 2 * kG Θ 4 i j z - Θ z 4 ^ 2 * kG Θ 8 i j z) (h.ent_sq 0)
      (((h.ent_sq 8).mul (h.ent_kG (by simp) i j)).sub ((h.ent_sq 4).mul (h.ent_kG (by simp) i j)))
      hmul (pow_ne_zero 2 hw) z
    exact sub_eq_zero.mp this
  rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl
  · rfl
  · exact (h.kG_compat0 (Or.inl rfl) i j z).symm
  · exact (h.kG_compat0 (Or.inr rfl) i j z).symm
  · exact h.kG_compat0 (Or.inl rfl) i j z
  · rfl
  · exact (h48 z).symm
  · exact h.kG_compat0 (Or.inr rfl) i j z
  · exact h48 z
  · rfl

lemma kH_eq {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (i j : Fin 2) {z : Fin 2 → ℂ} (hz : Θ z c ≠ 0) :
    kH Θ i j z = kG Θ c i j z / Θ z c ^ 2 := by
  rw [kH, div_eq_div_iff (pow_ne_zero 2 (h.kc_ne z)) (pow_ne_zero 2 hz)]
  have := h.kG_compat hc (kc_mem Θ z) i j z
  linear_combination this

lemma ent_kH (i j : Fin 2) : Ent (kH Θ i j) := fun z₀ => by
  set c := kc Θ z₀
  have hc := kc_mem Θ z₀
  have hz := h.kc_ne z₀
  have hden : Θ z₀ c ^ 2 ≠ 0 := pow_ne_zero 2 hz
  refine ((h.ent_kG hc i j z₀).div (h.ent_sq c z₀) hden).congr ?_
  filter_upwards [((h.ent_cmp' c) z₀).continuousAt.eventually_ne hz] with z hz'
  exact (h.kH_eq hc i j hz').symm

/-! ### Quasi-periodicity -/

lemma per_ne_zero {ω : Fin 2 → ℂ} {a : ℂ} {ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ}
    (hp : ∀ z, Θ (z + ω) = (a * Complex.exp (ℓ z)) • Θ z) : a ≠ 0 := by
  rintro rfl
  obtain ⟨w, hw⟩ := h.ne0
  have := congrFun (hp (w - ω)) 0
  rw [sub_add_cancel] at this
  simp [this] at hw

omit h in
/-- Derivative of a shifted function. -/
lemma pd_shift {g k : (Fin 2 → ℂ) → ℂ} (hk : Ent k) {ω : Fin 2 → ℂ} {a : ℂ} {ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ}
    (hω : ∀ z, g (z + ω) = a * Complex.exp (ℓ z) * k z) (j : Fin 2) (z : Fin 2 → ℂ) :
    pd j g (z + ω) = a * Complex.exp (ℓ z) * (ℓ (Pi.single j 1) * k z + pd j k z) := by
  rw [← pd_comp_add, pd_congr (funext hω) j]
  have hf : DifferentiableAt ℂ (fun z => a * Complex.exp (ℓ z)) z :=
    ((analyticAt_const (v := a)).mul (ℓ.analyticAt z).cexp).differentiableAt
  rw [pd_mul hf (hk.diff z)]
  rw [pd_expAff]
  ring

theorem kG_add {c : Fin 9} (hc : c = 0 ∨ c = 4 ∨ c = 8) (i j : Fin 2) {ω : Fin 2 → ℂ} {a : ℂ}
    {ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ} (hp : ∀ z, Θ (z + ω) = (a * Complex.exp (ℓ z)) • Θ z) (z : Fin 2 → ℂ) :
    kG Θ c i j (z + ω) = (a * Complex.exp (ℓ z)) ^ 2 * kG Θ c i j z := by
  have hm := h.ent_cmp' c
  have h0 : ∀ z, cmpV Θ c (z + ω) = a * Complex.exp (ℓ z) * cmpV Θ c z := fun z => by
    simp only [cmpV, hp z, Pi.smul_apply, smul_eq_mul]
  have hi := pd_shift hm h0 i z
  have hj : ∀ z, pd j (cmpV Θ c) (z + ω) = a * Complex.exp (ℓ z) *
      (ℓ (Pi.single j 1) * cmpV Θ c z + pd j (cmpV Θ c) z) := pd_shift hm h0 j
  have hk : Ent (fun z => ℓ (Pi.single j 1) * cmpV Θ c z + pd j (cmpV Θ c) z) :=
    (hm.const_mul _).add (hm.pd j)
  have hij := pd_shift hk hj i z
  rw [pd_add ((hm.const_mul _) z).differentiableAt ((hm.pd j).diff z),
    pd_const_mul _ (hm.diff z)] at hij
  simp only [kG]
  rw [hij, hi, hj z, hp z, kQ_smul]
  simp only [cmpV, Pi.smul_apply, smul_eq_mul]
  ring

lemma kH_add (i j : Fin 2) {ω : Fin 2 → ℂ} (hω : ω ∈ latt) (z : Fin 2 → ℂ) : kH Θ i j (z + ω) = kH Θ i j z := by
  obtain ⟨a, ℓ, hp⟩ := h.per ω hω
  have ha := h.per_ne_zero hp
  set c := kc Θ z
  have hc := kc_mem Θ z
  have hz := h.kc_ne z
  have hf : a * Complex.exp (ℓ z) ≠ 0 := mul_ne_zero ha (Complex.exp_ne_zero _)
  have hzω : Θ (z + ω) c ≠ 0 := by
    rw [hp z]; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero hf hz
  rw [h.kH_eq hc i j hzω, h.kH_eq hc i j hz, h.kG_add hc i j hp z, hp z]
  simp only [Pi.smul_apply, smul_eq_mul]
  have ha2 : Complex.exp (ℓ z) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- **`kH` is constant** (Liouville). -/
theorem kH_const (i j : Fin 2) (z w : Fin 2 → ℂ) : kH Θ i j z = kH Θ i j w := by
  have hcont : Continuous (kH Θ i j) :=
    continuous_iff_continuousAt.mpr fun x => (h.ent_kH i j x).continuousAt
  obtain ⟨M, hM⟩ := isCompact_fundDom.exists_bound_of_continuousOn hcont.continuousOn
  have hb : IsBounded (range (kH Θ i j)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨u, rfl⟩
    obtain ⟨f, hf, c, hc, rfl⟩ := exists_fund u
    rw [h.kH_add i j hc]
    exact hM f hf
  have hdiff : Differentiable ℂ (kH Θ i j) := fun x => (h.ent_kH i j x).differentiableAt
  exact hdiff.apply_eq_apply_of_bounded hb z w

/-- **Lemma K♮**: `G_c = K_ij Θ_c²` on all of `ℂ²`, for the three charts, with constants `K_ij`. -/
theorem lemmaK : ∃ K : Fin 2 → Fin 2 → ℂ, ∀ c : Fin 9, (c = 0 ∨ c = 4 ∨ c = 8) → ∀ (i j : Fin 2) z,
    kG Θ c i j z = K i j * Θ z c ^ 2 := by
  refine ⟨fun i j => kH Θ i j 0, fun c hc i j z => ?_⟩
  show kG Θ c i j z = kH Θ i j 0 * Θ z c ^ 2
  by_cases hz : Θ z c = 0
  · have hz' := h.kc_ne z
    have e := h.kG_compat (kc_mem Θ z) hc i j z
    rw [hz, zero_pow two_ne_zero, zero_mul] at e
    have hG : kG Θ c i j z = 0 := (mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 hz')
    rw [hG, hz]; ring
  · have e := h.kH_eq hc i j hz
    rw [← h.kH_const i j z 0, e]
    field_simp

end KHyp

end LSG.JacAnV
