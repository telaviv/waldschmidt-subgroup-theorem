/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.Deriv
import LSG.Jac.Model

/-!
# Analyticity and homogeneity glue for the polynomial maps (fields of `A1Facts`)

* `hasFDerivAt_evalSP_left`: the Fréchet derivative of `X ↦ evalSP X Y p` is `Σ_i evalSP X Y (dXsp i p) • proj i`.
* `hasFDerivAt_evalSP_diag`: the Fréchet derivative of `X ↦ evalSP X X p` is
  `Σ_i (evalSP X X (dXsp i p) + evalSP X X (dYsp i p)) • proj i`.
* `analyticAt_evalSP`: `z ↦ evalSP (F z) (G z) p` is analytic for analytic `F`, `G`.
* `evalSP_smul_left/right`: bihomogeneity, from a degree check on the data (`law_deg`).
* `onQ_smul`.
-/

namespace LSG.Jac

open Finset Data

section Frechet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The `i`-th coordinate projection on `𝕜⁹`. -/
abbrev pj (i : Fin 9) : (Fin 9 → 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 9 => 𝕜) i

/-- Fréchet derivative of a monomial. -/
theorem hasFDerivAt_xmono (X₀ : Fin 9 → 𝕜) (c : ℕ) (hc : ∀ i : Fin 9, decOK1 i c = true) :
    HasFDerivAt (fun X : Fin 9 → 𝕜 => xmono X c)
      (∑ i : Fin 9, ((digit c i : 𝕜) * xmono X₀ (lowerCode i c)) • pj i) X₀ := by
  unfold xmono
  have h := HasFDerivAt.finsetProd (u := univ) (g := fun k (X : Fin 9 → 𝕜) => X k ^ digit c k)
    (g' := fun k => (((digit c k : ℕ) : 𝕜) * X₀ k ^ (digit c k - 1)) • pj k)
    (fun k _ => by
      have h1 : HasFDerivAt (fun X : Fin 9 → 𝕜 => X k) (pj k) X₀ :=
        (pj (𝕜 := 𝕜) k).hasFDerivAt (x := X₀)
      simpa using h1.pow (digit c k))
  refine h.congr_fderiv (sum_congr rfl fun i _ => ?_)
  by_cases hd : digit c i = 0
  · ext v; simp [hd]
  · rw [← mul_prod_erase univ (fun k => X₀ k ^ digit (lowerCode i c) k) (mem_univ i),
      decOK1_spec (hc i) hd i.2, if_pos rfl]
    have hrest : ∏ k ∈ univ.erase i, X₀ k ^ digit (lowerCode i c) k =
        ∏ k ∈ univ.erase i, X₀ k ^ digit c k := by
      refine prod_congr rfl fun k hk => ?_
      rw [decOK1_spec (hc i) hd k.2, if_neg (fun h' => (mem_erase.mp hk).1 (Fin.ext h'))]
    rw [hrest, smul_smul]
    congr 1
    ring

lemma hasFDerivAt_lsum {α : Type*} (l : List α) {F : α → (Fin 9 → 𝕜) → 𝕜}
    {F' : α → (Fin 9 → 𝕜) →L[𝕜] 𝕜} {X₀ : Fin 9 → 𝕜} (h : ∀ a ∈ l, HasFDerivAt (F a) (F' a) X₀) :
    HasFDerivAt (fun X => (l.map fun a => F a X).sum) (l.map F').sum X₀ := by
  induction l with
  | nil => simpa using hasFDerivAt_const (0 : 𝕜) X₀
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

lemma decOK_spec {p : SP} (hp : decOK p = true) :
    ∀ r ∈ p.rows, (∀ i : Fin 9, decOK1 i r.1 = true) ∧ ∀ t ∈ r.2, ∀ i : Fin 9, decOK1 i t.1 = true := by
  intro r hr
  unfold decOK at hp
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hp
  exact ⟨fun i => (hp i i.2 r hr).1, fun t ht i => (hp i i.2 r hr).2 t ht⟩

/-- Fréchet derivative of `X ↦ evalSP X Y p`. -/
theorem hasFDerivAt_evalSP_left (X₀ Y : Fin 9 → 𝕜) (p : SP) (hp : decOK p = true) :
    HasFDerivAt (fun X => evalSP X Y p)
      (∑ i : Fin 9, evalSP X₀ Y (dXsp i p) • pj i) X₀ := by
  have hc := decOK_spec hp
  have h := hasFDerivAt_lsum p.rows (F := fun r X => xmono X r.1 * evalRow Y r.2)
    (fun r hr => (hasFDerivAt_xmono X₀ r.1 (hc r hr).1).mul_const (evalRow Y r.2))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have e := map_list_sum (ContinuousLinearMap.apply 𝕜 𝕜 v)
    (p.rows.map fun r => evalRow Y r.2 •
      ∑ i : Fin 9, ((digit r.1 i : 𝕜) * xmono X₀ (lowerCode i r.1)) • pj i)
  simp only [ContinuousLinearMap.apply_apply, List.map_map] at e
  rw [e]
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, pj, ContinuousLinearMap.proj_apply, smul_eq_mul, evalSP_dX,
    Finset.mul_sum]
  rw [lsum_finset_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [lsum_mul_right]
  exact lsum_congr fun r _ => by ring

lemma lsum_clm_apply {α : Type*} (l : List α) (F : α → (Fin 9 → 𝕜) →L[𝕜] 𝕜) (v : Fin 9 → 𝕜) :
    (l.map F).sum v = (l.map fun a => F a v).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Fréchet derivative of a row of monomials. -/
lemma hasFDerivAt_evalRow (X₀ : Fin 9 → 𝕜) (r : List (ℕ × ℕ × Bool))
    (hr : ∀ t ∈ r, ∀ i : Fin 9, decOK1 i t.1 = true) :
    HasFDerivAt (fun X => evalRow X r) ((r.map fun t => (sval t.2.1 t.2.2 : 𝕜) •
      ∑ i : Fin 9, ((digit t.1 i : 𝕜) * xmono X₀ (lowerCode i t.1)) • pj i).sum) X₀ := by
  unfold evalRow
  exact hasFDerivAt_lsum r fun t ht => (hasFDerivAt_xmono X₀ t.1 (hr t ht)).const_mul _ |>.congr_fderiv
    (by ext v; simp)

/-- Fréchet derivative of `X ↦ evalSP X X p` (the diagonal). -/
theorem hasFDerivAt_evalSP_diag (X₀ : Fin 9 → 𝕜) (p : SP) (hp : decOK p = true) :
    HasFDerivAt (fun X => evalSP X X p)
      (∑ i : Fin 9, (evalSP X₀ X₀ (dXsp i p) + evalSP X₀ X₀ (dYsp i p)) • pj i) X₀ := by
  have hc := decOK_spec hp
  have h := hasFDerivAt_lsum p.rows (F := fun r X => xmono X r.1 * evalRow X r.2)
    (fun r hr => (hasFDerivAt_xmono X₀ r.1 (hc r hr).1).mul (hasFDerivAt_evalRow X₀ r.2 (hc r hr).2))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [lsum_clm_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, pj, ContinuousLinearMap.proj_apply, smul_eq_mul,
    evalSP_dX, evalSP_dY, add_mul, Finset.sum_add_distrib, lsum_mul_right]
  rw [← lsum_finset_comm, ← lsum_finset_comm, ← List.sum_map_add]
  refine lsum_congr fun r _ => ?_
  rw [add_comm]
  congr 1
  · rw [mul_sum]; exact sum_congr rfl fun i _ => by unfold evalRow; ring
  · rw [lsum_mul_left]
    simp only [mul_sum]
    rw [lsum_finset_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_comm, lsum_mul_left, lsum_mul_left]
    exact lsum_congr fun t _ => by ring

end Frechet

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma analyticAt_xmono {F : E → Fin 9 → 𝕜} {z : E} (hF : AnalyticAt 𝕜 F z) (c : ℕ) :
    AnalyticAt 𝕜 (fun z => xmono (F z) c) z :=
  Finset.analyticAt_fun_prod _ fun i _ => ((analyticAt_pi_iff (f := fun i x => F x i)).mp hF i).pow _

lemma analyticAt_lsum {α : Type*} (l : List α) {F : α → E → 𝕜} {z : E}
    (h : ∀ a ∈ l, AnalyticAt 𝕜 (F a) z) : AnalyticAt 𝕜 (fun z => (l.map fun a => F a z).sum) z := by
  induction l with
  | nil => simpa using analyticAt_const
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- `z ↦ evalSP (F z) (G z) p` is analytic. -/
theorem analyticAt_evalSP {F G : E → Fin 9 → 𝕜} {z : E} (hF : AnalyticAt 𝕜 F z) (hG : AnalyticAt 𝕜 G z)
    (p : SP) : AnalyticAt 𝕜 (fun z => evalSP (F z) (G z) p) z := by
  unfold evalSP
  refine analyticAt_lsum p.rows fun r _ => (analyticAt_xmono hF r.1).mul ?_
  unfold evalRow
  exact analyticAt_lsum r.2 fun t _ => analyticAt_const.mul (analyticAt_xmono hG t.1)

end Analytic

/-! ## Homogeneity -/

/-- The degree of a monomial code. -/
def degc (c : ℕ) : ℕ := ((List.range 9).map (digit c)).sum

/-- All `X`-codes have degree `dx`, all `Y`-codes degree `dy`. -/
def degOK (p : SP) (dx dy : ℕ) : Bool := p.rows.all fun r => degc r.1 == dx && r.2.all fun t => degc t.1 == dy

lemma degc_eq (c : ℕ) : degc c = ∑ i : Fin 9, digit c i := by
  rw [degc, Fin.sum_univ_eq_sum_range (fun i => digit c i)]
  simp [List.range_succ, Finset.sum_range_succ]; ring

lemma xmono_smul {R : Type*} [CommRing R] (a : R) (x : Fin 9 → R) (c : ℕ) :
    xmono (a • x) c = a ^ degc c * xmono x c := by
  rw [degc_eq]
  simp only [xmono, Pi.smul_apply, smul_eq_mul, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]

lemma evalRow_smul {R : Type*} [CommRing R] (a : R) (x : Fin 9 → R) (r : List (ℕ × ℕ × Bool)) (d : ℕ)
    (h : r.all (fun t => degc t.1 == d) = true) : evalRow (a • x) r = a ^ d * evalRow x r := by
  unfold evalRow
  rw [lsum_mul_left]
  refine lsum_congr fun t ht => ?_
  have := List.all_eq_true.mp h t ht
  simp only [beq_iff_eq] at this
  rw [xmono_smul, this]; ring

lemma evalSP_smul_left {R : Type*} [CommRing R] (a : R) (x y : Fin 9 → R) (p : SP) {dx dy : ℕ}
    (h : degOK p dx dy = true) : evalSP (a • x) y p = a ^ dx * evalSP x y p := by
  unfold evalSP
  rw [lsum_mul_left]
  refine lsum_congr fun r hr => ?_
  have := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  rw [xmono_smul, this.1]; ring

lemma evalSP_smul_right {R : Type*} [CommRing R] (a : R) (x y : Fin 9 → R) (p : SP) {dx dy : ℕ}
    (h : degOK p dx dy = true) : evalSP x (a • y) p = a ^ dy * evalSP x y p := by
  unfold evalSP
  rw [lsum_mul_left]
  refine lsum_congr fun r hr => ?_
  have := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  rw [evalRow_smul a y r.2 dy this.2]; ring

lemma law_deg : ∀ k m : Fin 9, degOK (law k m) 2 2 = true := by decide +kernel

section Laws

variable {R : Type*} [CommRing R]

theorem lawPt_smul_left (m : Fin 9) (a : R) (x y : Fin 9 → R) : lawPt m (a • x) y = a ^ 2 • lawPt m x y := by
  funext k; simp only [lawPt, A32, Pi.smul_apply, smul_eq_mul]; exact evalSP_smul_left a x y _ (law_deg k m)

theorem lawPt_smul_right (m : Fin 9) (a : R) (x y : Fin 9 → R) : lawPt m x (a • y) = a ^ 2 • lawPt m x y := by
  funext k; simp only [lawPt, A32, Pi.smul_apply, smul_eq_mul]; exact evalSP_smul_right a x y _ (law_deg k m)

theorem dup_smul (a : R) (x : Fin 9 → R) : dup (a • x) = a ^ 4 • dup x := by
  simp only [dup]
  rw [lawPt_smul_left, lawPt_smul_right, smul_smul]; ring_nf

theorem onQ_smul (a : R) {x : Fin 9 → R} (hx : OnQ x) : OnQ (a • x) := by
  rw [onQ_iff] at hx ⊢
  intro j
  have h := hx j
  have e : quad (a • x) j = a ^ 2 * quad x j := by
    fin_cases j <;> simp [quad] <;> ring
  rw [e, h, mul_zero]

end Laws

end LSG.Jac
