/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarVPoly

/-!
# M2.6.8b: the degrees of the polynomial fed to `MultEstV`

* **`isHomV_PWV`**: block degree `D + F + 1` in every block `B_k^♮` (`X`- and `T`-coordinates together).
* **`PWV_mem_FLE`**: `G_a`-degree `≤ A₀` (lead and trailing variables together: `Σ α + Σ φ ≤ A₀`), `G_m`-degree
  `≤ A₁`, block degree `≤ D + F + 1`.
* **`trailDeg_PWV`**: degree `≤ F` in the `r` trailing additive variables (only the fibre forms contain them).
-/

open MvPolynomial Module Finset LSG.AuxAV LSG.AuxA
open StrongSix.M2 (FLE FLE_mono mul_mem_FLE prod_mem_FLE' pow_mem_FLE')

noncomputable section

namespace LSG.W88

open LSG.MEB (Blk DfunB)
open LSG.MEBV (VBlock Var liftV blk wk IsHomV TrailDeg)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock}

/-! ### Block homogeneity -/

theorem isWH_Xe {n : ℕ} (k k' : Fin m) (c : (B k').Idx) :
    (X (.e k' c) : MvPolynomial (Var n d₁ B) ℂ).IsWeightedHomogeneous (wk k) (if k' = k then 1 else 0) := by
  have := isWeightedHomogeneous_X ℂ (wk k) (Var.e k' c : Var n d₁ B)
  convert this using 1
  simp [wk]

theorem isWH_prod_XI (k : Fin m) (s : Finset (Fin m)) :
    (∏ l ∈ s, XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) l).IsWeightedHomogeneous (wk k)
      (if k ∈ s then 1 else 0) := by
  have := IsWeightedHomogeneous.prod s (fun l => XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) l)
    (fun l => if l = k then 1 else 0) (fun l _ => isWH_Xe k l _)
  convert this using 1
  rw [Finset.sum_ite_eq']

theorem isWH_fibPolyA (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) (k : Fin m) :
    (fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i).IsWeightedHomogeneous (wk k) 1 := by
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => ?_)
  · rw [mem_weightedHomogeneousSubmodule]
    have h1 := isWeightedHomogeneous_X ℂ (wk k) (Var.x (Fin.natAdd d₀ i) : Var (d₀ + r) d₁ B)
    have h2 := isWH_prod_XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) k univ
    convert h1.mul h2 using 1
    simp [wk]
  · rw [mem_weightedHomogeneousSubmodule]
    have h1 := isWH_Xe (n := d₀ + r) (d₁ := d₁) (B := B) k j (Sum.inr (B j).t₀)
    have h2 := isWH_prod_XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) k (univ.erase j)
    convert (isWeightedHomogeneous_C (wk k) (M i j)).mul (h1.mul h2) using 1
    by_cases hkj : j = k
    · subst hkj; simp
    · simp [hkj, Ne.symm hkj]

theorem isHomV_monoPolyA (M : Matrix (Fin r) (Fin m) ℂ) {D F : ℕ} (ν : MonoAV d₀ d₁ r B D F) :
    IsHomV (monoPolyA M ν) (fun _ => D + F) := by
  intro k
  have hx := IsWeightedHomogeneous.prod univ
    (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ ν.μ.α i)
    (fun _ => 0) (fun i _ => by
      simpa [wk] using (isWeightedHomogeneous_X ℂ (wk k)
        (Var.x (Fin.castAdd r i) : Var (d₀ + r) d₁ B)).pow (ν.μ.α i))
  have hy := IsWeightedHomogeneous.prod univ
    (fun j => (X (.y j) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ ν.μ.β j)
    (fun _ => 0) (fun j _ => by
      simpa [wk] using (isWeightedHomogeneous_X ℂ (wk k) (Var.y j : Var (d₀ + r) d₁ B)).pow (ν.μ.β j))
  have he := IsWeightedHomogeneous.prod univ
    (fun k' => ∏ c, (X (.e k' (Sum.inl (fidx (Bb B k') c))) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^
      ν.μ.γ k' c)
    (fun k' => if k' = k then ∑ c, ν.μ.γ k' c else 0) (fun k' _ => by
      have := IsWeightedHomogeneous.prod univ
        (fun c => (X (.e k' (Sum.inl (fidx (Bb B k') c))) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^
          ν.μ.γ k' c)
        (fun c => ν.μ.γ k' c * if k' = k then 1 else 0)
        (fun c _ => by simpa [mul_comm] using (isWH_Xe (n := d₀ + r) (d₁ := d₁) (B := B) k k'
          (Sum.inl (fidx (Bb B k') c))).pow (ν.μ.γ k' c))
      convert this using 1
      split_ifs <;> simp)
  have hp := (isWH_prod_XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) k univ).pow (F - ∑ i, ν.φ i)
  have hf := IsWeightedHomogeneous.prod univ
    (fun i => fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i ^ ν.φ i) (fun i => ν.φ i)
    (fun i _ => by simpa using (isWH_fibPolyA (d₀ := d₀) (d₁ := d₁) M i k).pow (ν.φ i))
  change IsWeightedHomogeneous _ (monoPolyA M ν) (D + F)
  unfold monoPolyA
  convert (((hx.mul hy).mul he).mul hp).mul hf using 1
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
  rw [ν.μ.hγ k, smul_eq_mul, mul_one]
  have := ν.hφ
  omega

theorem isHomV_PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) : IsHomV (PWV M νs p) (fun _ => D + F + 1) := by
  intro k
  have hP : (PpolyAV M νs p).IsWeightedHomogeneous (wk k) (D + F) := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    simpa using (isWeightedHomogeneous_C (wk k) (p l : ℂ)).mul (isHomV_monoPolyA M (νs l) k)
  have hW : (WprodA (d₀ := d₀) (r := r) (d₁ := d₁) (B := B)).IsWeightedHomogeneous (wk k) 1 := by
    simpa [WprodA] using isWH_prod_XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) k univ
  exact hP.mul hW

/-! ### Block degrees -/

/-- The block degrees of a fibre form: `1` in `x` and in every block. -/
def E1AV (m : ℕ) : Blk m → ℕ := Pi.single Blk.x 1 + ∑ k : Fin m, Pi.single (Blk.e k) 1

theorem prodXI_mem_FLE (s : Finset (Fin m)) :
    (∏ l ∈ s, XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) l) ∈
      FLE ℂ blk (∑ l ∈ s, Pi.single (Blk.e l : Blk m) 1) :=
  prod_mem_FLE' _ _ _ fun l _ => LSG.ME.fle_X (Var.e l (Sum.inl (B l).base.i₀) : Var (d₀ + r) d₁ B)

theorem fibPolyA_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i ∈ FLE ℂ blk (E1AV m) := by
  classical
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => ?_)
  · exact mul_mem_FLE ℂ (LSG.ME.fle_X (Var.x (Fin.natAdd d₀ i) : Var (d₀ + r) d₁ B))
      (prodXI_mem_FLE univ)
  · rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (FLE_mono ℂ blk ?_ (mul_mem_FLE ℂ
      (LSG.ME.fle_X (Var.e j (Sum.inr (B j).t₀) : Var (d₀ + r) d₁ B)) (prodXI_mem_FLE (univ.erase j))))
    intro b
    simp only [E1AV, Pi.add_apply, Finset.sum_apply]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [blk, Pi.single_apply]
    omega

theorem monoPolyA_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) {D F A₀ A₁ : ℕ} (ν : MonoAV d₀ d₁ r B D F)
    (hA : ∑ i, ν.μ.α i + ∑ i, ν.φ i ≤ A₀) (hB : ∑ j, ν.μ.β j ≤ A₁) :
    monoPolyA M ν ∈ FLE ℂ blk (DfunB A₀ A₁ (D + F)) := by
  classical
  have h1 := prod_mem_FLE' (K := ℂ) (β := blk) univ
    (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ ν.μ.α i)
    (fun i => ν.μ.α i • Pi.single (blk (Var.x (Fin.castAdd r i) : Var (d₀ + r) d₁ B)) 1)
    (fun i _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h2 := prod_mem_FLE' (K := ℂ) (β := blk) univ
    (fun j => (X (.y j) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ ν.μ.β j)
    (fun j => ν.μ.β j • Pi.single (blk (Var.y j : Var (d₀ + r) d₁ B)) 1)
    (fun j _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h3 := prod_mem_FLE' (K := ℂ) (β := blk) univ
    (fun k => ∏ c, (X (.e k (Sum.inl (fidx (Bb B k) c))) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ ν.μ.γ k c)
    (fun k => ∑ c, ν.μ.γ k c • Pi.single (blk (Var.e k (Sum.inl (fidx (Bb B k) c)) : Var (d₀ + r) d₁ B)) 1)
    (fun k _ => prod_mem_FLE' _ _ _ fun c _ => pow_mem_FLE' (LSG.ME.fle_X _) _)
  have h4 := pow_mem_FLE' (prodXI_mem_FLE (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) univ) (F - ∑ i, ν.φ i)
  have h5 := prod_mem_FLE' (K := ℂ) (β := blk) univ
    (fun i => fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i ^ ν.φ i) (fun i => ν.φ i • E1AV m)
    (fun i _ => pow_mem_FLE' (fibPolyA_mem_FLE M i) _)
  refine FLE_mono ℂ blk (fun b => ?_)
    (mul_mem_FLE ℂ (mul_mem_FLE ℂ (mul_mem_FLE ℂ (mul_mem_FLE ℂ h1 h2) h3) h4) h5)
  have hφ := ν.hφ
  cases b with
  | x =>
    simp only [DfunB, E1AV, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blk, Pi.single_apply,
      smul_eq_mul, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero, add_zero, ite_true, mul_one]
    simpa using hA
  | yz =>
    simp only [DfunB, E1AV, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blk, Pi.single_apply,
      smul_eq_mul, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero, add_zero, ite_true, mul_one]
    simpa using hB
  | e k =>
    simp only [DfunB, E1AV, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blk, Pi.single_apply,
      smul_eq_mul, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero, zero_add, Blk.e.injEq,
      mul_ite, mul_one, add_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_one]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [ite_true]
    rw [ν.μ.hγ k]
    omega

theorem PWV_mem_FLE (M : Matrix (Fin r) (Fin m) ℂ) {D F L A₀ A₁ : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) (hA : ∀ l, ∑ i, (νs l).μ.α i + ∑ i, (νs l).φ i ≤ A₀)
    (hB : ∀ l, ∑ j, (νs l).μ.β j ≤ A₁) :
    PWV M νs p ∈ FLE ℂ blk (DfunB A₀ A₁ (D + F + 1)) := by
  have hP : PpolyAV M νs p ∈ FLE ℂ blk (DfunB A₀ A₁ (D + F)) := by
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (monoPolyA_mem_FLE M _ (hA l) (hB l))
  refine FLE_mono ℂ blk (fun b => ?_) (mul_mem_FLE ℂ hP (prodXI_mem_FLE (d₀ := d₀) (r := r) (d₁ := d₁)
    (B := B) univ))
  cases b with
  | x => simp [DfunB, Finset.sum_apply]
  | yz => simp [DfunB, Finset.sum_apply]
  | e k => simp [DfunB, Finset.sum_apply, Pi.single_apply]

/-! ### Degree in the trailing additive variables -/

section Trail

variable {P Q : MvPolynomial (Var (d₀ + r) d₁ B) ℂ} {a b : ℕ}

theorem trailDegA_mono (h : a ≤ b) (hP : TrailDeg (d₀ := d₀) a P) : TrailDeg (d₀ := d₀) b P :=
  fun s hs => (hP s hs).trans h

theorem trailDegA_add (hP : TrailDeg (d₀ := d₀) a P) (hQ : TrailDeg (d₀ := d₀) a Q) :
    TrailDeg (d₀ := d₀) a (P + Q) := by
  classical
  intro s hs
  rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with h | h
  · exact hP s h
  · exact hQ s h

theorem trailDegA_mul (hP : TrailDeg (d₀ := d₀) a P) (hQ : TrailDeg (d₀ := d₀) b Q) :
    TrailDeg (d₀ := d₀) (a + b) (P * Q) := by
  classical
  intro s hs
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  exact add_le_add (hP u hu) (hQ v hv)

theorem trailDegA_C_mul (c : ℂ) (hP : TrailDeg (d₀ := d₀) a P) : TrailDeg (d₀ := d₀) a (C c * P) :=
  fun s hs => hP s (MvPolynomial.support_smul (by rwa [smul_eq_C_mul]))

theorem trailDegA_one : TrailDeg (d₀ := d₀) 0 (1 : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) := by
  intro s hs
  rw [show (1 : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) = monomial 0 1 from rfl] at hs
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hs
  simp [hs]

theorem trailDegA_pow (hP : TrailDeg (d₀ := d₀) a P) (n : ℕ) : TrailDeg (d₀ := d₀) (n * a) (P ^ n) := by
  induction n with
  | zero => simpa using trailDegA_one
  | succ n ih => rw [pow_succ, add_mul, one_mul]; exact trailDegA_mul ih hP

theorem trailDegA_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Var (d₀ + r) d₁ B) ℂ)
    (e : ι → ℕ) (h : ∀ i ∈ s, TrailDeg (d₀ := d₀) (e i) (f i)) :
    TrailDeg (d₀ := d₀) (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using trailDegA_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact trailDegA_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem trailDegA_X (v : Var (d₀ + r) d₁ B) :
    TrailDeg (d₀ := d₀) (∑ i : Fin r, Finsupp.single v 1 (.x (Fin.natAdd d₀ i))) (X v) := by
  intro s hs
  rw [X] at hs
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton] at hs
  rw [hs]

theorem trailDegA_X_lead {v : Var (d₀ + r) d₁ B} (hv : ∀ i : Fin r, v ≠ .x (Fin.natAdd d₀ i)) :
    TrailDeg (d₀ := d₀) 0 (X v) := by
  have h := trailDegA_X (d₀ := d₀) v
  have e : ∑ i : Fin r, Finsupp.single v 1 (.x (Fin.natAdd d₀ i)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (hv i).symm
  rwa [e] at h

end Trail

theorem trailDeg_prodXI (s : Finset (Fin m)) :
    TrailDeg (d₀ := d₀) 0 (∏ l ∈ s, XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) l) := by
  simpa using trailDegA_prod (d₀ := d₀) s (fun l => XI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) l)
    (fun _ => 0) fun l _ => trailDegA_X_lead fun i' => by simp

theorem trailDeg_fibPolyA (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin r) :
    TrailDeg (d₀ := d₀) 1 (fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i) := by
  classical
  refine trailDegA_add ?_ ?_
  · have h1 : TrailDeg (d₀ := d₀) 1 (X (.x (Fin.natAdd d₀ i)) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) := by
      have h := trailDegA_X (d₀ := d₀) (.x (Fin.natAdd d₀ i) : Var (d₀ + r) d₁ B)
      refine trailDegA_mono ?_ h
      rw [Finset.sum_eq_single i (fun b _ hb => Finsupp.single_eq_of_ne (by
        intro h'; apply hb; simpa using h')) (by simp)]
      simp
    simpa using trailDegA_mul h1 (trailDeg_prodXI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) univ)
  · have hs : TrailDeg (d₀ := d₀) 0 (∑ j, C (M i j) * (XT (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) j *
        ∏ l ∈ univ.erase j, XI l)) := by
      have hsum : ∀ (s : Finset (Fin m)), TrailDeg (d₀ := d₀) 0 (∑ j ∈ s, C (M i j) *
          (XT (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) j * ∏ l ∈ univ.erase j, XI l)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using trailDegA_C_mul (d₀ := d₀) 0 trailDegA_one
        | insert j s hj ih =>
          rw [Finset.sum_insert hj]
          refine trailDegA_add ?_ ih
          refine trailDegA_C_mul _ ?_
          simpa using trailDegA_mul (trailDegA_X_lead (d₀ := d₀) (v := .e j (Sum.inr (B j).t₀))
            fun i' => by simp) (trailDeg_prodXI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) (univ.erase j))
      exact hsum univ
    exact trailDegA_mono (Nat.zero_le 1) hs

theorem trailDeg_PWV (M : Matrix (Fin r) (Fin m) ℂ) {D F L : ℕ} (νs : Fin L → MonoAV d₀ d₁ r B D F)
    (p : Fin L → ℤ) : TrailDeg (d₀ := d₀) F (PWV M νs p) := by
  have hmono : ∀ l, TrailDeg (d₀ := d₀) F (monoPolyA M (νs l)) := by
    intro l
    have hx := trailDegA_prod (d₀ := d₀) univ
      (fun i => (X (.x (Fin.castAdd r i)) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ (νs l).μ.α i)
      (fun _ => 0) fun i _ => by
        simpa using trailDegA_pow (trailDegA_X_lead (d₀ := d₀) (v := .x (Fin.castAdd r i)) fun i' => by
          simp only [ne_eq, Var.x.injEq, Fin.ext_iff, Fin.coe_castAdd, Fin.coe_natAdd]; omega) _
    have hy := trailDegA_prod (d₀ := d₀) univ
      (fun j => (X (.y j) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^ (νs l).μ.β j)
      (fun _ => 0) fun j _ => by
        simpa using trailDegA_pow (trailDegA_X_lead (d₀ := d₀) (v := .y j) fun i' => by simp) _
    have he := trailDegA_prod (d₀ := d₀) univ
      (fun k => ∏ c, (X (.e k (Sum.inl (fidx (Bb B k) c))) : MvPolynomial (Var (d₀ + r) d₁ B) ℂ) ^
        (νs l).μ.γ k c)
      (fun _ => 0) fun k _ => by
        simpa using trailDegA_prod (d₀ := d₀) univ _ (fun _ => 0) fun c _ => by
          simpa using trailDegA_pow (trailDegA_X_lead (d₀ := d₀) (v := .e k (Sum.inl (fidx (Bb B k) c)))
            fun i' => by simp) _
    have hp := trailDegA_pow (trailDeg_prodXI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) univ)
      (F - ∑ i, (νs l).φ i)
    have hf := trailDegA_prod (d₀ := d₀) univ (fun i => fibPolyA (d₀ := d₀) (d₁ := d₁) (B := B) M i ^ (νs l).φ i)
      (fun i => (νs l).φ i * 1) fun i _ => trailDegA_pow (trailDeg_fibPolyA M i) _
    have h := trailDegA_mul (trailDegA_mul (trailDegA_mul (trailDegA_mul hx hy) he) hp) hf
    simp only [Finset.sum_const_zero, mul_zero, zero_add, mul_one] at h
    exact trailDegA_mono (νs l).hφ h
  have hP : TrailDeg (d₀ := d₀) F (PpolyAV M νs p) := by
    have hsum : ∀ (s : Finset (Fin L)), TrailDeg (d₀ := d₀) F (∑ l ∈ s, C (p l : ℂ) * monoPolyA M (νs l)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using trailDegA_mono (Nat.zero_le F) (trailDegA_C_mul (d₀ := d₀) 0 trailDegA_one)
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact trailDegA_add (trailDegA_C_mul _ (hmono j)) ih
    exact hsum univ
  simpa [PWV, WprodA] using trailDegA_mul hP (trailDeg_prodXI (d₀ := d₀) (r := r) (d₁ := d₁) (B := B) univ)

end LSG.W88
