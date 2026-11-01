/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.Model

/-!
# M2.4b: surjectivity of the lift off `{X = 0}` (field `surjV`, M2.1.6)

If `Y = (X; T)` has `X ≠ 0` and all 15 generators vanish at `Y`, then `X = c θ(z)` (the base field `surj`), some
chart `c₀ = fc t` has `X_{c₀} ≠ 0` (`chart_cover`), `w` is chosen so that `c T_t(z, w) = Y_t`, and the two Plücker
generators through `c₀` determine the other two fibre coordinates. No exit words or anchors are needed.
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV

namespace LSG.JacBlockV

open LSG.JacBlock

variable {B₁ B₂ : LocalBranch f₅ 2} {p : ℂ × ℂ} {hp : p ∈ dom2 B₁ B₂} {hx : p.1 ≠ p.2}
  {G : GermRad a1Facts hp hx} (D : ThetaData G)

lemma plkGen_mem_pair : ∀ t t' : Fin 3, t ≠ t' →
    ∃ a b, plkGen a b ∈ gensTV ∧ ((a = t ∧ b = t') ∨ (a = t' ∧ b = t)) := by
  have h01 : plkGen 0 1 ∈ gensTV := by simp [gensTV]
  have h02 : plkGen 0 2 ∈ gensTV := by simp [gensTV]
  have h12 : plkGen 1 2 ∈ gensTV := by simp [gensTV]
  intro t t' hne
  fin_cases t <;> fin_cases t' <;>
    first
    | exact absurd rfl hne
    | exact ⟨0, 1, h01, by decide⟩
    | exact ⟨0, 2, h02, by decide⟩
    | exact ⟨1, 2, h12, by decide⟩

/-- Two points on the fibre generators with the same `X`-part, the same `T_t` and `X_{fc t} ≠ 0` agree. -/
lemma fib_unique {Y L : Idx → ℂ} (hX : ∀ k, Y (Sum.inl k) = L (Sum.inl k))
    (hY : ∀ Q ∈ gensTV, eval Y Q = 0) (hL : ∀ Q ∈ gensTV, eval L Q = 0) {t : Fin 3}
    (ht : Y (Sum.inr t) = L (Sum.inr t)) (hne : Y (Sum.inl (fcV t)) ≠ 0) : Y = L := by
  have key : ∀ a b, plkGen a b ∈ gensTV →
      Y (Sum.inl (fcV a)) * (Y (Sum.inr b) - L (Sum.inr b)) -
        Y (Sum.inl (fcV b)) * (Y (Sum.inr a) - L (Sum.inr a)) = 0 := by
    intro a b hab
    have h1 := hY _ hab
    have h2 := hL _ hab
    rw [eval_plkGen] at h1 h2
    have e : (fun c => L (Sum.inl c)) = fun c => Y (Sum.inl c) := funext fun c => (hX c).symm
    rw [e, ← hX, ← hX] at h2
    linear_combination h1 - h2
  funext i
  rcases i with k | t'
  · exact hX k
  · by_cases htt : t = t'
    · subst htt; exact ht
    obtain ⟨a, b, hab, hc⟩ := plkGen_mem_pair t t' htt
    have h := key a b hab
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ht, sub_self, mul_zero, sub_zero] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)
    · rw [ht, sub_self, mul_zero, zero_sub, neg_eq_zero] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)

/-- **Surjectivity off `{X = 0}`.** -/
theorem surjVV (Y : Idx → ℂ) (hX : (fun c => Y (Sum.inl c)) ≠ 0)
    (hY : ∀ Q ∈ LSG.MEBV.gensOf gensMv gensTV, eval Y Q = 0) :
    ∃ (q : (Fin 2 → ℂ) × ℂ) (c : ℂ), Y = c • LSG.MEBV.liftOf D.thetaN fcV (ΦV D) q := by
  set X : Fin 9 → ℂ := fun c => Y (Sum.inl c) with hXdef
  have hA : ∀ Q ∈ gensMv, eval X Q = 0 := fun Q hQ => by
    have := hY (rename Sum.inl Q) (List.mem_append_left _ (List.mem_map.mpr ⟨Q, hQ, rfl⟩))
    rwa [eval_rename] at this
  have hT : ∀ Q ∈ gensTV, eval Y Q = 0 := fun Q hQ => hY Q (List.mem_append_right _ hQ)
  obtain ⟨z, c, hz⟩ := (aBlockD D).surj X hX hA
  change X = c • D.thetaN z at hz
  obtain ⟨c₀, hc₀, hne⟩ := (aBlockD D).chart_cover X hX hA
  obtain ⟨t, rfl⟩ := fc_charts c₀ hc₀
  have hXt : X (fcV t) = c * D.thetaN z (fcV t) := by rw [hz]; rfl
  have hc : c ≠ 0 := fun h0 => hne (by rw [hXt, h0, zero_mul])
  have hθ : D.thetaN z (fcV t) ≠ 0 := fun h0 => hne (by rw [hXt, h0, mul_zero])
  set w := (Y (Sum.inr t) / c + ΦV D z t) / D.thetaN z (fcV t) with hw
  refine ⟨(z, w), c, fib_unique (t := t) (fun k => ?_) hT (fun Q hQ => ?_) ?_ hne⟩
  · change X k = c * D.thetaN z k
    rw [hz]; rfl
  · rw [eval_smul_of_isHomogeneous (by
      simp only [gensTV, List.mem_cons, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl | rfl <;> exact plkGen_hom _ _), liftT_modelV D (z, w) Q hQ, mul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, LSG.MEBV.liftOf, Sum.elim_inr, LSG.MEBV.fibOf]
    rw [hw]
    field_simp
    ring

end LSG.JacBlockV
