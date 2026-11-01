/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacAn3.PsiLiouville
import LSG.JacAn3.TaylorFields

/-!
# M2.2 (N0): partial derivatives of entire functions on `ℂ²`

* `pd j f z = Df(z)(e_j)`, and `Ent f`: `f` is analytic everywhere;
* calculus rules: `pd_add`, `pd_sub`, `pd_mul`, `pd_const_mul`, `pd_const`, `pd_comp_add` (translation),
  `pd_expAff` (`a · exp ℓ`), `pd_cmp` (components `cmpV Θ c` of a vector-valued map), `pd_sum`;
* `pd_quadForm` / `pd_flowW`: the derivative of `z ↦ W(Θ z)_l` for a quadratic table `W`, in the polarised form
  `W(X + Y) − W(X) − W(Y)`.
-/

noncomputable section

open Metric Set Filter Topology

namespace LSG.JacAnV

open LSG.JacAn

/-- The `j`-th partial derivative. -/
def pd (j : Fin 2) (f : (Fin 2 → ℂ) → ℂ) (z : Fin 2 → ℂ) : ℂ := fderiv ℂ f z (Pi.single j 1)

/-- `f` is entire. -/
def Ent (f : (Fin 2 → ℂ) → ℂ) : Prop := ∀ z, AnalyticAt ℂ f z

/-- The `c`-th component of a vector-valued map. -/
abbrev cmpV (Θ : (Fin 2 → ℂ) → P9) (c : Fin 9) : (Fin 2 → ℂ) → ℂ := fun z => Θ z c

section calculus

variable {f g : (Fin 2 → ℂ) → ℂ} {z : Fin 2 → ℂ}

lemma Ent.diff (hf : Ent f) (z : Fin 2 → ℂ) : DifferentiableAt ℂ f z := (hf z).differentiableAt

lemma Ent.add (hf : Ent f) (hg : Ent g) : Ent (fun z => f z + g z) := fun z => (hf z).add (hg z)

lemma Ent.sub (hf : Ent f) (hg : Ent g) : Ent (fun z => f z - g z) := fun z => (hf z).sub (hg z)

lemma Ent.mul (hf : Ent f) (hg : Ent g) : Ent (fun z => f z * g z) := fun z => (hf z).mul (hg z)

lemma Ent.const_mul (a : ℂ) (hf : Ent f) : Ent (fun z => a * f z) := fun z => analyticAt_const.mul (hf z)

lemma ent_const (a : ℂ) : Ent (fun _ => a) := fun _ => analyticAt_const

lemma Ent.pd (hf : Ent f) (j : Fin 2) : Ent (pd j f) := fun z => by
  have h := (hf z).fderiv
  exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ))).analyticAt _).comp h

lemma ent_cmp {Θ : (Fin 2 → ℂ) → P9} (hΘ : ∀ z, AnalyticAt ℂ Θ z) (c : Fin 9) : Ent (cmpV Θ c) :=
  fun z => (analyticAt_pi_iff.mp (hΘ z)) c

lemma ent_lin (ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ) : Ent (fun z => ℓ z) := fun z => ℓ.analyticAt z

lemma Ent.comp_add (hf : Ent f) (ω : Fin 2 → ℂ) : Ent (fun z => f (z + ω)) := fun z => by
  have h : AnalyticAt ℂ (fun z : Fin 2 → ℂ => z + ω) z := by fun_prop
  exact AnalyticAt.comp (g := f) (f := fun z : Fin 2 → ℂ => z + ω) (hf (z + ω)) h

lemma pd_add (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (j : Fin 2) :
    pd j (fun z => f z + g z) z = pd j f z + pd j g z := by
  unfold pd; change fderiv ℂ (f + g) z _ = _; rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]; rfl

lemma pd_sub (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (j : Fin 2) :
    pd j (fun z => f z - g z) z = pd j f z - pd j g z := by
  unfold pd; change fderiv ℂ (f - g) z _ = _; rw [(hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]; rfl

lemma pd_mul (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (j : Fin 2) :
    pd j (fun z => f z * g z) z = pd j f z * g z + f z * pd j g z := by
  unfold pd; change fderiv ℂ (f * g) z _ = _; rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma pd_const_mul (a : ℂ) (hf : DifferentiableAt ℂ f z) (j : Fin 2) :
    pd j (fun z => a * f z) z = a * pd j f z := by
  unfold pd; rw [(hf.hasFDerivAt.const_mul a).fderiv]
  simp only [smul_apply, smul_eq_mul]

lemma pd_const (a : ℂ) (j : Fin 2) : pd j (fun _ => a) z = 0 := by
  simp [pd]

lemma pd_lin (ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ) (j : Fin 2) : pd j (fun z => ℓ z) z = ℓ (Pi.single j 1) := by
  unfold pd; rw [ℓ.hasFDerivAt.fderiv]

lemma pd_comp_add (ω : Fin 2 → ℂ) (j : Fin 2) : pd j (fun z => f (z + ω)) z = pd j f (z + ω) := by
  simp only [pd, fderiv_comp_add_right]

lemma pd_expAff (a : ℂ) (ℓ : (Fin 2 → ℂ) →L[ℂ] ℂ) (j : Fin 2) :
    pd j (fun z => a * Complex.exp (ℓ z)) z = ℓ (Pi.single j 1) * (a * Complex.exp (ℓ z)) := by
  have h := (ℓ.hasFDerivAt (x := z)).cexp.const_mul a
  unfold pd; rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma pd_cmp {Θ : (Fin 2 → ℂ) → P9} (hΘ : DifferentiableAt ℂ Θ z) (c : Fin 9) (j : Fin 2) :
    pd j (cmpV Θ c) z = fderiv ℂ Θ z (Pi.single j 1) c := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) c).hasFDerivAt.comp z hΘ.hasFDerivAt
  simp only [pd]
  change fderiv ℂ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 => ℂ) c) ∘ Θ) z _ = _
  rw [h.fderiv]
  rfl

lemma pd_congr {f g : (Fin 2 → ℂ) → ℂ} (h : f = g) (j : Fin 2) : pd j f z = pd j g z := by rw [h]

lemma pd_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin 2 → ℂ) → ℂ} (hF : ∀ a, DifferentiableAt ℂ (F a) z)
    (j : Fin 2) : pd j (fun z => ∑ a ∈ s, F a z) z = ∑ a ∈ s, pd j (F a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pd_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : DifferentiableAt ℂ (fun z => ∑ a ∈ s, F a z) z := by
      simpa using DifferentiableAt.fun_sum (u := s) (fun i _ => hF i)
    rw [pd_add (hF a) hs, ih]

end calculus

/-! ### Quadratic tables -/

section quad

variable {Θ : (Fin 2 → ℂ) → P9} {z : Fin 2 → ℂ}

/-- The vector of partial derivatives `∂_j Θ(z)`. -/
def pdv (j : Fin 2) (Θ : (Fin 2 → ℂ) → P9) (z : Fin 2 → ℂ) : P9 := fun c => pd j (cmpV Θ c) z

lemma pd_quadForm (C : Fin 9 → Fin 9 → ℂ) (hΘ : ∀ c, DifferentiableAt ℂ (cmpV Θ c) z) (j : Fin 2) :
    pd j (fun z => ∑ a, ∑ b, C a b * (Θ z a * Θ z b)) z =
      ∑ a, ∑ b, C a b * (pdv j Θ z a * Θ z b + Θ z a * pdv j Θ z b) := by
  rw [pd_sum (F := fun a z => ∑ b, C a b * (Θ z a * Θ z b)) _ (fun a => by
    simpa using DifferentiableAt.fun_sum (u := Finset.univ)
      (fun b _ => ((hΘ a).mul (hΘ b)).const_mul (C a b)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pd_sum (F := fun b z => C a b * (Θ z a * Θ z b)) _
    (fun b => ((hΘ a).mul (hΘ b)).const_mul (C a b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pd_const_mul (f := fun z => Θ z a * Θ z b) _ ((hΘ a).mul (hΘ b)),
    pd_mul (f := fun z => Θ z a) (g := fun z => Θ z b) (hΘ a) (hΘ b)]
  rfl

/-- The polarisation identity for a quadratic table. -/
lemma quadForm_polar (C : Fin 9 → Fin 9 → ℂ) (X Y : P9) :
    ∑ a, ∑ b, C a b * (Y a * X b + X a * Y b) =
      (∑ a, ∑ b, C a b * ((X + Y) a * (X + Y) b)) - (∑ a, ∑ b, C a b * (X a * X b)) -
        ∑ a, ∑ b, C a b * (Y a * Y b) := by
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.add_apply]; ring

/-- **The derivative of `z ↦ W(Θ z)_l`** for a quadratic table `W`. -/
lemma pd_table (W : Fin 2 → P9 → P9) (Wc : Fin 2 → Fin 9 → Fin 9 → Fin 9 → ℂ)
    (hWc : ∀ j X l, W j X l = ∑ a, ∑ b, Wc j l a b * (X a * X b))
    (hΘ : ∀ c, DifferentiableAt ℂ (cmpV Θ c) z) (i j : Fin 2) (l : Fin 9) :
    pd i (fun z => W j (Θ z) l) z = W j (Θ z + pdv i Θ z) l - W j (Θ z) l - W j (pdv i Θ z) l := by
  simp only [hWc]
  rw [pd_quadForm _ hΘ, quadForm_polar]

lemma pd_flowW (hΘ : ∀ c, DifferentiableAt ℂ (cmpV Θ c) z) (i j : Fin 2) (l : Fin 9) :
    pd i (fun z => flowW j (Θ z) l) z =
      flowW j (Θ z + pdv i Θ z) l - flowW j (Θ z) l - flowW j (pdv i Θ z) l :=
  pd_table flowW flowC flowW_quad hΘ i j l

end quad

end LSG.JacAnV
