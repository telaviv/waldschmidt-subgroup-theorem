/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Stmt
import LSG.MEB.Sanity

/-!
# Sanity checks for the frozen `VBlock` interface (M2.4a)

* **`pointVBlock : VBlock`**: `G_a` as a vector extension of the point block `LSG.MEB.Sanity.pointBlock`. Model
  `ℙ¹` with coordinates `(X₀ : T₀)`, lift `(z, w) ↦ (1, w)` (`Φ = 0`), no generators, the law
  `(X₀Y₀ : X₀U₀ + T₀Y₀)` of bidegree `(1, 1)`, `η = 0`, Hilbert forms `(X₀, T₀)` with `hilb_deg = 1`, one empty local
  system. It shows the field list is satisfiable and exercises the model, law, surjectivity and certificate fields
  (the flow fields are vacuous, `g = 0`). `G_a` is not anti-affine, which is why anti-affineness is not a field.
* `notMem_IGsem_one`: the statement-side definitions instantiate on `G_a^{d₀} × G_m^{d₁} × G_a^m`.
* `invarKV_example`: on `G̃ = G_a × G_a` (`d₀ = 0`, `r = 1`, `M = (1)`), the polynomial `x·X₀ + T₀` is
  `K_M`-invariant (`InvarKV`), i.e. a polynomial on the push-out `G = G̃ / K_M ≅ G_a`.
-/

open MvPolynomial

namespace LSG.MEBV.Sanity

open LSG.MEB.Sanity (pointBlock)

/-- The only base coordinate. -/
def x0 : Fin pointBlock.N := ⟨0, Nat.zero_lt_one⟩

theorem fin_pt (c d : Fin pointBlock.N) : c = d :=
  Fin.ext (by have h1 := c.isLt; have h2 := d.isLt; change _ < 1 at h1 h2; omega)

@[simp] theorem θ_pt (z : Fin pointBlock.g → ℂ) (c : Fin pointBlock.N) : pointBlock.θ z c = 1 := rfl

theorem fin_g_eq (ω : Fin pointBlock.g → ℂ) : ω = 0 := Subsingleton.elim (α := Fin 0 → ℂ) ω 0

/-- The coordinates `X₀` (`inl x0`) and `T₀` (`inr 0`). -/
abbrev PIdx : Type := Fin pointBlock.N ⊕ Fin 1

/-- The law `(X₀Y₀ : X₀U₀ + T₀Y₀)` of `G_a`. -/
noncomputable def gaLaw : Fin 1 → PIdx → MvPolynomial (PIdx ⊕ PIdx) ℂ
  | _, Sum.inl _ => X (Sum.inl (Sum.inl x0)) * X (Sum.inr (Sum.inl x0))
  | _, Sum.inr _ => X (Sum.inl (Sum.inl x0)) * X (Sum.inr (Sum.inr 0)) +
      X (Sum.inl (Sum.inr 0)) * X (Sum.inr (Sum.inl x0))

theorem gaLaw_hom (i : Fin 1) (k : PIdx) :
    (gaLaw i k).IsWeightedHomogeneous (biWV PIdx) ((1, 1) : ℕ × ℕ) := by
  have hl : ∀ v : PIdx, (X (Sum.inl v) : MvPolynomial (PIdx ⊕ PIdx) ℂ).IsWeightedHomogeneous
      (biWV PIdx) (1, 0) := fun v => isWeightedHomogeneous_X ℂ (biWV PIdx) (Sum.inl v)
  have hr : ∀ v : PIdx, (X (Sum.inr v) : MvPolynomial (PIdx ⊕ PIdx) ℂ).IsWeightedHomogeneous
      (biWV PIdx) (0, 1) := fun v => isWeightedHomogeneous_X ℂ (biWV PIdx) (Sum.inr v)
  rcases k with k | k
  · simpa [gaLaw] using (hl _).mul (hr _)
  · simpa [gaLaw] using ((hl _).mul (hr _)).add ((hl _).mul (hr _))

/-- The index of the `a`-th Hilbert form: `X₀`, then `T₀`. -/
def hIdx (a : Fin (pointBlock.g + 2)) : PIdx := if a.val = 0 then Sum.inl x0 else Sum.inr 0

theorem lformV_single (v : PIdx) :
    lformV (fun c => if c = v then (1 : ℂ) else 0) = (X v : MvPolynomial PIdx ℂ) := by
  simp [lformV]

theorem gens_point : gensOf pointBlock.gens ([] : List (MvPolynomial PIdx ℂ)) = [] := rfl

/-- **`G_a` as a vector-extension block over the point.** -/
noncomputable def pointVBlock : VBlock where
  base := pointBlock
  nT := 1
  fc := fun _ => x0
  fc_charts := fun c _ => ⟨0, fin_pt _ _⟩
  gensT := []
  gensT_hom := by simp
  Φ := fun _ _ => 0
  Φ_analytic := fun _ => analyticAt_const
  liftT_model := by simp
  η := fun _ => 0
  lift_per := fun ω _ p => ⟨1, one_ne_zero, by simp only [fin_g_eq ω, Prod.mk_zero_zero, add_zero, one_smul]⟩
  surjV := fun Y hY _ => by
    have h0 : Y (Sum.inl x0) ≠ 0 := fun h => hY (funext fun c => by rw [fin_pt c x0, h]; rfl)
    refine ⟨(0, Y (Sum.inr 0) / Y (Sum.inl x0)), Y (Sum.inl x0), funext fun v => ?_⟩
    rcases v with c | t
    · rw [fin_pt c x0]
      simp only [liftOf, Pi.smul_apply, Sum.elim_inl, smul_eq_mul, θ_pt, mul_one]
    · rw [Subsingleton.elim t 0]
      simp only [liftOf, fibOf, Pi.smul_apply, Sum.elim_inr, smul_eq_mul, θ_pt, one_mul, sub_zero]
      field_simp
  nLV := 1
  ld := 1
  lawV := gaLaw
  lawV_hom := gaLaw_hom
  lawV_eq := fun _ p q => ⟨1, funext fun k => by
    rcases k with k | k
    · simp only [evalLawV, gaLaw, liftOf, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
        smul_eq_mul, θ_pt, mul_one]
    · simp only [evalLawV, gaLaw, liftOf, fibOf, map_add, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr,
        Pi.smul_apply, smul_eq_mul, Prod.snd_add, θ_pt]
      ring⟩
  lawV_complete := fun _ _ => ⟨0, fun h => by
    have := congrFun h (Sum.inl x0)
    simp only [evalLawV, gaLaw, liftOf, map_mul, eval_X, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      θ_pt, mul_one] at this
    exact one_ne_zero this⟩
  WT := fun _ _ => 0
  WT_hom := fun _ _ => isHomogeneous_zero _ _ _
  T_flow := fun _ _ j => j.elim0
  plk := fun _ _ => 0
  plk_hom := fun _ _ => isHomogeneous_zero _ _ _
  T_plk := fun t t' z w => by
    rw [Subsingleton.elim t 0, Subsingleton.elim t' 0]; simp
  t₀ := 0
  fc_t₀ := fin_pt _ _
  hilb_l := fun a c => if c = hIdx a then 1 else 0
  hilb_deg := 1
  hilb := fun M hM => by
    have hM' : M ∈ Ideal.span ((X : PIdx → MvPolynomial PIdx ℂ) '' Set.univ) := by
      rw [mem_ideal_span_X_image]
      intro d hd
      have h := hM (mem_support_iff.mp hd)
      have hne : d ≠ 0 := by
        rintro rfl
        simp at h
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
      exact ⟨i, Set.mem_univ _, by simpa using hi⟩
    refine Ideal.mem_sup_right (Ideal.span_mono ?_ hM')
    rintro _ ⟨v, -, rfl⟩
    rcases v with c | t
    · refine ⟨⟨0, by omega⟩, ?_⟩
      change lformV (fun c' => if c' = hIdx ⟨0, _⟩ then (1 : ℂ) else 0) = _
      rw [lformV_single, fin_pt c x0]; rfl
    · refine ⟨⟨1, by omega⟩, ?_⟩
      change lformV (fun c' => if c' = hIdx ⟨1, _⟩ then (1 : ℂ) else 0) = _
      rw [lformV_single, Subsingleton.elim t 0]; rfl
  lci_s := 1
  lci_S := fun _ => 1
  lci_F := fun _ => []
  lci_len := fun _ => rfl
  lci_F_le := fun _ => by simp [Ideal.ofList]
  lci_mem := fun _ Q hQ => by
    rw [gens_point] at hQ
    simp at hQ
  lci_cover := fun v => ⟨0, Ideal.mem_sup_right (Ideal.subset_span ⟨0, (pow_zero _).symm⟩)⟩

/-- `1 ∉ IGsem` on `G_a^{d₀} × G_m^{d₁} × G_a^m`. -/
theorem notMem_IGsem_one (d₀ d₁ m : ℕ) :
    (1 : MvPolynomial (Var d₀ d₁ fun _ : Fin m => pointVBlock) ℂ) ∉
      IGsem d₀ d₁ (fun _ : Fin m => pointVBlock) :=
  notMem_IGsem_of_eval_ne (u := 0) (by simp)

/-- **A polynomial on the push-out**: `x·X₀ + T₀` is `K_M`-invariant on `G_a × G_a`, `M = (1)`. -/
theorem invarKV_example :
    InvarKV (d₀ := 0) (r := 1) (d₁ := 0) (B := fun _ : Fin 1 => pointVBlock) !![1]
      (X (.x (Fin.natAdd 0 0)) * X (.e 0 (Sum.inl x0)) + X (.e 0 (Sum.inr (⟨0, Nat.zero_lt_one⟩ :
        Fin pointVBlock.nT)))) := by
  intro u v
  simp only [map_add, map_mul, eval_X, liftV, Tan.blkV]
  change (u.1 (Fin.natAdd 0 0) + Fin.append (0 : Fin 0 → ℂ) (-(!![1] : Matrix (Fin 1) (Fin 1) ℂ).mulVec v)
      (Fin.natAdd 0 0)) * 1 + (1 * (u.2.2.2 0 + v 0) - 0) = u.1 (Fin.natAdd 0 0) * 1 + (1 * u.2.2.2 0 - 0)
  rw [Fin.append_right]
  simp [dotProduct]
  ring

end LSG.MEBV.Sanity
