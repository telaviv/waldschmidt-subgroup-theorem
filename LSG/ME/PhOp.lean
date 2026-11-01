import Mathlib
import LSG.ME.PhOpCurve

/-!
# Philippon's degree-stable operators (Philippon 1986, §4.1; STAGE2 §10)

For `g ∈ G`, `w ∈ Lie G`, law choices `c, c'` and `κ ∈ ℕ`:
`phOp g w c c' κ Q = [z^κ] Q(law_c(X, law_{c'}(rep g, exp(z w))))` (blockwise; `G_a`, `G_m`
blocks translated by `x_g + z ξ`, `y_g exp(z η)`), Philippon's `δ^κ_g Q` along the direction `w`.

* `eval_phOp`: evaluated at a point `x₀`, `phOp g w c c' κ Q` is the `κ`-th Taylor coefficient of
  `Q(x₀ + (g + exp(z w)))`.
* **`phOp_mem_FLE`**: `Q ∈ FLE D ⇒ phOp g w c c' κ Q ∈ FLE (dblE D)` (elliptic degrees at most
  doubled, the others preserved), **for every `κ`**.
* **`phOp_IG`**: `phOp` maps `I_G` into `I_G`.
* `OrdGt W Q n p` (**formal order `> n` along `W` at `p`**): for all `w ∈ W`, the power series
  `Q(p + exp(z w))` (`fexp`, canonical charts at `p`) has no terms of degree `≤ n`. It is an
  ideal condition (`ordIdeal`). Over an infinite field this is the multivariable condition
  "`Q(p + exp(z₁ w₁ + ⋯ + z_t w_t))` has no terms of total degree `≤ n`" (restrict to lines).
* `aeval_lawPt`: independence of the law choices up to units (homogeneous `Q`).
* **`zeros_phOp`** (Philippon, Prop. 4.4): for homogeneous `Q`s,
  `h ∈ zeros(I_G + (phOp g w c c' κ Q : Q ∈ 𝒬, w ∈ W, κ ≤ k, all c, c'))` iff every `Q ∈ 𝒬`
  has formal order `> k` along `W` at `h + g`.
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE S bdeg mul_mem_FLE FLE_mono pow_mem_FLE' prod_mem_FLE')

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

local notation "PS" => PowerSeries (MvPolynomial (Var d₀ d₁ m) K)

/-! ### Low-order vanishing -/

section Low

variable {A : Type*} [CommRing A]

/-- `f` has no terms of degree `≤ n`. -/
def LowZero (n : ℕ) (f : PowerSeries A) : Prop := ∀ i ≤ n, PowerSeries.coeff i f = 0

theorem LowZero.mul_left {n : ℕ} {f : PowerSeries A} (hf : LowZero n f) (g : PowerSeries A) :
    LowZero n (g * f) := by
  intro i hi
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [hf p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega), mul_zero]

theorem LowZero.of_unit {n : ℕ} {f u : PowerSeries A} (hu : IsUnit u) (h : LowZero n (u * f)) :
    LowZero n f := by
  obtain ⟨v, rfl⟩ := hu
  have := h.mul_left (↑v⁻¹ : PowerSeries A)
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

end Low

/-! ### The operators -/

section Op

/-! #### Degrees -/

/-- All coefficients in `FLE D`. -/
def CF (D : Blk m → ℕ) (F : PS) : Prop := ∀ n, PowerSeries.coeff n F ∈ FLE K blk D

theorem CF_add {D : Blk m → ℕ} {F G : PS} (hF : CF D F) (hG : CF D G) : CF D (F + G) :=
  fun n => by rw [map_add]; exact fle_add (hF n) (hG n)

theorem CF_sub {D : Blk m → ℕ} {F G : PS} (hF : CF D F) (hG : CF D G) : CF D (F - G) :=
  fun n => by rw [map_sub]; exact fle_sub (hF n) (hG n)

theorem CF.mono {D D' : Blk m → ℕ} {F : PS} (hF : CF D F) (h : D ≤ D') : CF D' F :=
  fun n => fle_le (hF n) h

theorem CF_mul {D E : Blk m → ℕ} {F G : PS} (hF : CF D F) (hG : CF E G) : CF (D + E) (F * G) :=
  fun n => by
    rw [PowerSeries.coeff_mul]
    exact Submodule.sum_mem _ fun p _ => mul_mem_FLE K (hF p.1) (hG p.2)

theorem CF_C {D : Blk m → ℕ} {p : MvPolynomial (Var d₀ d₁ m) K} (hp : p ∈ FLE K blk D) :
    CF D (PowerSeries.C p) := fun n => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact Submodule.zero_mem _

theorem CF_mapC {D : Blk m → ℕ} (B : PowerSeries K) :
    CF D (PowerSeries.map (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) B) :=
  fun n => by rw [PowerSeries.coeff_map]; exact fle_C _

theorem CF_one {D : Blk m → ℕ} : CF D (1 : PS) := by
  rw [← map_one PowerSeries.C]; exact CF_C (by rw [← C_1]; exact fle_C _)

theorem CF_pow {D : Blk m → ℕ} {F : PS} (hF : CF D F) (n : ℕ) : CF (n • D) (F ^ n) := by
  induction n with
  | zero => simpa using (CF_one (D := 0))
  | succ n ih => rw [pow_succ, succ_nsmul]; exact CF_mul ih hF

theorem CF_prod {ι' : Type*} (s : Finset ι') (f : ι' → PS) (e : ι' → Blk m → ℕ)
    (h : ∀ i ∈ s, CF (e i) (f i)) : CF (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CF_one (D := 0))
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact CF_mul (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable [CharZero K]


variable (g₂ g₃) in
/-- The point `g + exp(z w)`, computed with the laws `c'`. -/
noncomputable def phPt (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c' : Fin m → Fin 2) :
    Var d₀ d₁ m → PowerSeries K :=
  addPt g₂ g₃ c' (fun v => PowerSeries.C (coords g 1 v)) (Exp g₂ g₃ w)

variable (g₂ g₃) in
/-- The substitution `X ↦ law_c(X, g + exp(z w))`, with coefficients in `K[Var]`. -/
noncomputable def phSub (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) :
    Var d₀ d₁ m → PS :=
  addPt g₂ g₃ c (fun v => PowerSeries.C (X v))
    (fun v => PowerSeries.map (MvPolynomial.C) (phPt g₂ g₃ g w c' v))

variable (g₂ g₃) in
/-- **Philippon's operator** `δ^κ_g` along `w` (law choices `c, c'`). -/
noncomputable def phOp (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) K) : MvPolynomial (Var d₀ d₁ m) K :=
  PowerSeries.coeff κ (aeval (phSub g₂ g₃ g w c c') Q)

omit [CharZero K] in
theorem phOp_add (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ)
    (P Q : MvPolynomial (Var d₀ d₁ m) K) :
    phOp g₂ g₃ g w c c' κ (P + Q) = phOp g₂ g₃ g w c c' κ P + phOp g₂ g₃ g w c c' κ Q := by
  simp [phOp]

omit [CharZero K] in
/-- **Evaluation**: `phOp … Q (x₀)` is the `κ`-th Taylor coefficient of `Q(x₀ + (g + exp(z w)))`. -/
theorem eval_phOp (x₀ : Var d₀ d₁ m → K) (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m)
    (c c' : Fin m → Fin 2) (κ : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    eval x₀ (phOp g₂ g₃ g w c c' κ Q) = PowerSeries.coeff κ
      (aeval (addPt g₂ g₃ c (fun v => PowerSeries.C (x₀ v)) (phPt g₂ g₃ g w c')) Q) := by
  rw [phOp, ← PowerSeries.coeff_map, ringHom_aeval (PowerSeries.map (eval x₀))
    (fun a => by simp [PowerSeries.algebraMap_apply])]
  have hid : (eval x₀).comp (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) =
      RingHom.id K := by
    ext; simp
  have e : (fun v => PowerSeries.map (eval x₀) (phSub g₂ g₃ g w c c' v)) =
      addPt g₂ g₃ c (fun v => PowerSeries.C (x₀ v)) (phPt g₂ g₃ g w c') := by
    funext v
    rw [phSub, addPt_map _ (fun a => by simp [PowerSeries.algebraMap_apply])]
    have hmm : ∀ F : PowerSeries K, PowerSeries.map (eval x₀) (PowerSeries.map C F) = F :=
      fun F => by rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hid, PowerSeries.map_id]; rfl
    simp only [PowerSeries.map_C, eval_X, hmm]
  rw [e]

omit [CharZero K] in
theorem CF_lawc (c : Fin 2) (k : Fin m) (B : Fin 3 → PowerSeries K) (i : Fin 3) :
    CF (Pi.single (Blk.e k) 2) (lawc c (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
      (fun i => PowerSeries.C (X (.e k i))) (fun i => PowerSeries.map MvPolynomial.C (B i)) i) := by
  have hL : ∀ q : Fin 3 → K, lawc c (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
      (fun i => PowerSeries.C (X (.e k i))) (fun i => algebraMap K PS (q i)) i =
      PowerSeries.C (lawPoly g₂ g₃ d₀ d₁ c k q i) := fun q => by
    rw [lawPoly, lawc_map (PowerSeries.C : MvPolynomial (Var d₀ d₁ m) K →+* PS)]
    simp only [PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq, Function.comp_def, bvars]
  have hE : ∀ q : Fin 3 → K, CF (Pi.single (Blk.e k) 2)
      (lawc c (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
        (fun i => PowerSeries.C (X (.e k i))) (fun i => algebraMap K PS (q i)) i) := fun q => by
    rw [hL q]; exact CF_C (lawPoly_mem c k _ i)
  have hq : ∀ j l, CF (0 : Blk m → ℕ)
      (PowerSeries.map (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) (B j) *
      PowerSeries.map (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) (B l)) := fun j l => by
    rw [← map_mul]; exact CF_mapC _
  have hq2 : ∀ j, CF (0 : Blk m → ℕ)
      (PowerSeries.map (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K) (B j) ^ 2) :=
    fun j => by rw [sq]; exact hq j j
  have T : ∀ (F : PS), CF (0 : Blk m → ℕ) F → ∀ q : Fin 3 → K, CF (Pi.single (Blk.e k) 2)
      (F * lawc c (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
        (fun i => PowerSeries.C (X (.e k i))) (fun i => algebraMap K PS (q i)) i) :=
    fun F hF q => (CF_mul hF (hE q)).mono (by simp)
  have ev : ∀ x y z : K, (![algebraMap K PS x, algebraMap K PS y, algebraMap K PS z] : Fin 3 → PS) =
      fun i => algebraMap K PS (![x, y, z] i) := fun x y z => by
    funext j; fin_cases j <;> rfl
  have e1 : (1 : PS) = algebraMap K PS 1 := (map_one _).symm
  have e0 : (0 : PS) = algebraMap K PS 0 := (map_zero _).symm
  rw [lawc_quad]
  simp only [mul_sub]
  rw [show (![1, 0, 0] : Fin 3 → PS) = ![algebraMap K PS 1, algebraMap K PS 0, algebraMap K PS 0]
      by rw [← e1, ← e0],
    show (![0, 1, 0] : Fin 3 → PS) = ![algebraMap K PS 0, algebraMap K PS 1, algebraMap K PS 0]
      by rw [← e1, ← e0],
    show (![0, 0, 1] : Fin 3 → PS) = ![algebraMap K PS 0, algebraMap K PS 0, algebraMap K PS 1]
      by rw [← e1, ← e0],
    show (![1, 1, 0] : Fin 3 → PS) = ![algebraMap K PS 1, algebraMap K PS 1, algebraMap K PS 0]
      by rw [← e1, ← e0],
    show (![1, 0, 1] : Fin 3 → PS) = ![algebraMap K PS 1, algebraMap K PS 0, algebraMap K PS 1]
      by rw [← e1, ← e0],
    show (![0, 1, 1] : Fin 3 → PS) = ![algebraMap K PS 0, algebraMap K PS 1, algebraMap K PS 1]
      by rw [← e1, ← e0]]
  simp only [ev]
  refine CF_add (CF_add (CF_add (CF_add (CF_add (T _ (hq2 0) _) (T _ (hq2 1) _)) (T _ (hq2 2) _))
    (CF_sub (CF_sub (T _ (hq 0 1) _) (T _ (hq 0 1) _)) (T _ (hq 0 1) _)))
    (CF_sub (CF_sub (T _ (hq 0 2) _) (T _ (hq 0 2) _)) (T _ (hq 0 2) _)))
    (CF_sub (CF_sub (T _ (hq 1 2) _) (T _ (hq 1 2) _)) (T _ (hq 1 2) _))

omit [CharZero K] in
theorem CF_phSub (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2)
    (v : Var d₀ d₁ m) : CF (Pi.single (blk v) (bmul (blk v))) (phSub g₂ g₃ g w c c' v) := by
  have hX := fun u : Var d₀ d₁ m => fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) u
  cases v with
  | x i =>
    simp only [phSub, addPt]
    exact CF_add (CF_C (by simpa [bmul] using hX (.x i))) (CF_mapC _)
  | y j =>
    simp only [phSub, addPt]
    simpa [bmul] using CF_mul (CF_C (hX (.y j))) (CF_mapC (D := 0) _)
  | z j =>
    simp only [phSub, addPt]
    simpa [bmul] using CF_mul (CF_C (hX (.z j))) (CF_mapC (D := 0) _)
  | e k i =>
    simp only [phSub, addPt]
    simpa [bmul] using CF_lawc (g₂ := g₂) (g₃ := g₃) (c k) k _ i

omit [CharZero K] in
/-- **Degree bound**: `phOp` at most doubles elliptic degrees and preserves the others, for every
order `κ` (Philippon's `c_i ≤ 2`, independent of `κ`). -/
theorem CF_sum {ι' : Type*} (s : Finset ι') (f : ι' → PS) {D : Blk m → ℕ}
    (h : ∀ i ∈ s, CF D (f i)) : CF D (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact Submodule.sum_mem _ fun i hi => h i hi n

omit [CharZero K] in
theorem phOp_mem_FLE (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ)
    {D : Blk m → ℕ} {Q : MvPolynomial (Var d₀ d₁ m) K} (hQ : Q ∈ FLE K blk D) :
    phOp g₂ g₃ g w c c' κ Q ∈ FLE K blk (dblE D) := by
  suffices h : CF (dblE D) (aeval (phSub g₂ g₃ g w c c') Q) by exact h κ
  rw [Q.as_sum, map_sum]
  refine CF_sum _ _ fun s hs => ?_
  have hsS : s ∈ S blk D := by
    rw [FLE, mem_restrictSupport_iff] at hQ; exact hQ hs
  rw [aeval_monomial, Finsupp.prod]
  have h1 : ∀ v, CF (s v • Pi.single (blk v) (bmul (blk v))) (phSub g₂ g₃ g w c c' v ^ s v) :=
    fun v => CF_pow (CF_phSub g w c c' v) (s v)
  have hprod : CF (∑ v ∈ s.support, s v • Pi.single (blk v) (bmul (blk v)))
      (∏ v ∈ s.support, phSub g₂ g₃ g w c c' v ^ s v) := CF_prod _ _ _ fun v _ => h1 v
  have hle : (∑ v ∈ s.support, (s v • Pi.single (blk v) (bmul (blk v)) : Blk m → ℕ)) ≤ dblE D := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ _ => Nat.zero_le _) ?_
    rw [Pi.le_def]
    intro b
    have hb := hsS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, dblE]
    calc ∑ v, s v * (if b = blk v then bmul (blk v) else 0)
        = ∑ v, bmul b * (if blk v = b then s v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmul b * ∑ v, (if blk v = b then s v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmul b * D b := Nat.mul_le_mul_left _ hb
  have hc : ∀ a : K, CF (0 : Blk m → ℕ) (algebraMap K PS a) := fun a => by
    rw [PowerSeries.algebraMap_apply]; exact CF_C (fle_C _)
  exact (CF_mul (hc _) hprod).mono (by simpa using hle)

/-! #### `I_G` -/

/-- Power series all of whose coefficients lie in `I`. -/
def CI (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Ideal PS where
  carrier := {F | ∀ n, PowerSeries.coeff n F ∈ I}
  add_mem' hF hG n := by rw [map_add]; exact I.add_mem (hF n) (hG n)
  zero_mem' n := by rw [map_zero]; exact I.zero_mem
  smul_mem' a F hF n := by
    rw [smul_eq_mul, PowerSeries.coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hF p.2)

omit [CharZero K] in
theorem C_mem_CI {I : Ideal (MvPolynomial (Var d₀ d₁ m) K)} {p : MvPolynomial (Var d₀ d₁ m) K}
    (hp : p ∈ I) : PowerSeries.C p ∈ CI I := fun n => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact I.zero_mem

theorem phPt_YZ (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c' : Fin m → Fin 2) (j : Fin d₁) :
    phPt g₂ g₃ g w c' (.y j) * phPt g₂ g₃ g w c' (.z j) = 1 := by
  have h := fexp_YZ (0 : GPt K d₀ d₁ g₂ g₃) w j
  simp only [YZ, map_sub, map_mul, aeval_X, map_one, sub_eq_zero] at h
  simp only [phPt, addPt, coords, coordsZ_y, coordsZ_z]
  rw [show ∀ a b c d : PowerSeries K, a * b * (c * d) = (a * c) * (b * d) from
      fun _ _ _ _ => by ring,
    ← map_mul, Units.mul_inv, map_one, one_mul]
  exact h

theorem phPt_F (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c' : Fin m → Fin 2) (k : Fin m) :
    Fv (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k))
      (fun i => phPt g₂ g₃ g w c' (.e k i)) = 0 := by
  have hm := Fv_lawc_mem (c' k) (algebraMap K (PowerSeries K) (g₂ k))
    (algebraMap K (PowerSeries K) (g₃ k)) (fun i => PowerSeries.C (coords g 1 (.e k i)))
    (fun i => Exp g₂ g₃ w (.e k i))
  have h1 : Fv (algebraMap K (PowerSeries K) (g₂ k)) (algebraMap K (PowerSeries K) (g₃ k))
      (fun i => PowerSeries.C (coords g 1 (.e k i))) = 0 := by
    have := Fv_map (PowerSeries.C : K →+* PowerSeries K) (g₂ k) (g₃ k) (rep (g.2.2 k))
    rw [Fv_rep (two_ne_zero (α := K)), map_zero] at this
    simpa [coords, Function.comp_def, PowerSeries.algebraMap_apply] using this.symm
  have h2 : Fv (algebraMap K (PowerSeries K) (g₂ k)) (algebraMap K (PowerSeries K) (g₃ k))
      (fun i => Exp g₂ g₃ w (.e k i)) = 0 := by
    rw [← aeval_Fk]; exact fexp_Fk 0 w k
  rw [h1, h2, Set.pair_eq_singleton, Ideal.span_singleton_eq_bot.mpr rfl] at hm
  exact (Submodule.mem_bot _).mp hm

/-- **`phOp` maps `I_G` into `I_G`.** -/
theorem phOp_IG (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) K} (hQ : Q ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) :
    phOp g₂ g₃ g w c c' κ Q ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  suffices h : IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤
      (CI (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)).comap (aeval (phSub g₂ g₃ g w c c')) from h hQ κ
  rw [IG, Ideal.ofList, Ideal.span_le]
  rintro _ hP
  simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hP
  rcases hP with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · have e : aeval (phSub g₂ g₃ g w c c') (YZ K d₀ m j) = PowerSeries.C (YZ K d₀ m j) := by
      simp only [YZ, map_sub, map_mul, aeval_X, map_one, phSub, addPt]
      rw [show ∀ a b c d : PS, a * b * (c * d) = (a * c) * (b * d) from fun _ _ _ _ => by ring,
        ← map_mul (PowerSeries.map MvPolynomial.C), phPt_YZ, map_one, mul_one]
    rw [SetLike.mem_coe, Ideal.mem_comap, e]
    exact C_mem_CI (YZ_mem_IG g₂ g₃ j)
  · rw [SetLike.mem_coe, Ideal.mem_comap, aeval_Fk]
    have hm := Fv_lawc_mem (c k) (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
      (fun i => PowerSeries.C (X (.e k i)))
      (fun i => PowerSeries.map MvPolynomial.C (phPt g₂ g₃ g w c' (.e k i)))
    have h1 : Fv (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
        (fun i => PowerSeries.C (X (.e k i))) = PowerSeries.C (Fk g₂ g₃ d₀ d₁ k) := by
      rw [← Fv_bvars, Fv_map]
      simp [PowerSeries.algebraMap_apply, Function.comp_def, bvars]
    have h2 : Fv (algebraMap K PS (g₂ k)) (algebraMap K PS (g₃ k))
        (fun i => PowerSeries.map MvPolynomial.C (phPt g₂ g₃ g w c' (.e k i))) = 0 := by
      have := Fv_map (PowerSeries.map (MvPolynomial.C : K →+* MvPolynomial (Var d₀ d₁ m) K))
        (algebraMap K _ (g₂ k)) (algebraMap K _ (g₃ k)) (fun i => phPt g₂ g₃ g w c' (.e k i))
      rw [phPt_F, map_zero] at this
      simpa [PowerSeries.algebraMap_apply, Function.comp_def] using this.symm
    rw [h1, h2, Set.pair_comm, Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
      at hm
    refine Ideal.span_le.mpr ?_ hm
    rintro _ rfl
    exact C_mem_CI (Fk_mem_IG g₂ g₃ k)

/-! ### The formal order of vanishing -/

variable (g₂ g₃) in
/-- **Formal order `> n` along `W` at `p`**: for every `w ∈ W` the power series `Q(p + exp(z w))`
has no terms of degree `≤ n`. -/
def OrdGt (W : Submodule K (LieE K d₀ d₁ m)) (Q : MvPolynomial (Var d₀ d₁ m) K) (n : ℕ)
    (p : GPt K d₀ d₁ g₂ g₃) : Prop :=
  ∀ w ∈ W, LowZero n (aeval (fexp g₂ g₃ p w) Q)

variable (g₂ g₃) in
/-- The ideal of polynomials with formal order `> n` along `W` at every point of `E`. -/
def ordIdeal (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) where
  carrier := {Q | ∀ p ∈ E, OrdGt g₂ g₃ W Q n p}
  add_mem' hP hQ p hp w hw i hi := by
    rw [map_add, map_add, hP p hp w hw i hi, hQ p hp w hw i hi, add_zero]
  zero_mem' p _ w _ i _ := by simp
  smul_mem' a Q hQ p hp w hw := by
    rw [smul_eq_mul, map_mul]; exact (hQ p hp w hw).mul_left _

omit [CharZero K] in
theorem mem_ordIdeal {W : Submodule K (LieE K d₀ d₁ m)} {n : ℕ} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    {Q : MvPolynomial (Var d₀ d₁ m) K} : Q ∈ ordIdeal g₂ g₃ W n E ↔ ∀ p ∈ E, OrdGt g₂ g₃ W Q n p :=
  Iff.rfl

omit [CharZero K] in
theorem ordIdeal_anti (W : Submodule K (LieE K d₀ d₁ m)) {n n' : ℕ} (h : n ≤ n')
    (E : Set (GPt K d₀ d₁ g₂ g₃)) : ordIdeal g₂ g₃ W n' E ≤ ordIdeal g₂ g₃ W n E :=
  fun _ hQ p hp w hw i hi => hQ p hp w hw i (hi.trans h)

theorem IG_le_ordIdeal (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ ordIdeal g₂ g₃ W n E := by
  rw [IG, Ideal.ofList, Ideal.span_le]
  rintro _ hP p _ w _ i _
  simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hP
  rcases hP with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [fexp_YZ, map_zero]
  · rw [fexp_Fk, map_zero]

omit [CharZero K] in
/-- Formal order `> 0` is vanishing at the normalized representative. -/
theorem ordGt_zero_iff {W : Submodule K (LieE K d₀ d₁ m)} {Q : MvPolynomial (Var d₀ d₁ m) K}
    {p : GPt K d₀ d₁ g₂ g₃} : OrdGt g₂ g₃ W Q 0 p ↔ eval (coords p 1) Q = 0 := by
  have e : ∀ w, PowerSeries.coeff 0 (aeval (fexp g₂ g₃ p w) Q) = eval (coords p 1) Q := fun w => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_aeval]
    simp only [fexp_const]; rfl
  constructor
  · intro h; rw [← e 0]; exact h 0 W.zero_mem 0 le_rfl
  · intro h w _ i hi; rw [Nat.le_zero.mp hi, e, h]

/-- **Independence of the law choices up to units** (homogeneous `Q`):
`Q(h + (g + exp(z w)))` computed with any laws is `(∏ₖ uₖ^{dₖ}) · Q((h + g) + exp(z w))`, and the
`uₖ` are units for good choices (`lawPt_unit`). -/
theorem aeval_lawPt [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
    {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsHomE Q d)
    (h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (g : GPt K d₀ d₁ g₂ g₃) (w : LieE K d₀ d₁ m)
    (c c' : Fin m → Fin 2) :
    aeval (lawPt g₂ g₃ h lam g w c c') Q =
      (∏ k, lawPt g₂ g₃ h lam g w c c' (.e k (chartAt (h + g) k)) ^ d k) *
        aeval (fexp g₂ g₃ (h + g) w) Q := by
  conv_lhs => rw [lawPt_eq hΔ h lam g w c c']
  exact aeval_scl hQ _ _

omit [CharZero K] in
theorem eval_phOp_coords (h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (g : GPt K d₀ d₁ g₂ g₃)
    (w : LieE K d₀ d₁ m) (c c' : Fin m → Fin 2) (κ : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) K) :
    eval (coords h lam) (phOp g₂ g₃ g w c c' κ Q) =
      PowerSeries.coeff κ (aeval (lawPt g₂ g₃ h lam g w c c') Q) :=
  eval_phOp _ g w c c' κ Q

variable (g₂ g₃) in
/-- The generators `δ^κ_g Q` (`Q ∈ 𝒬`, `w ∈ W`, `κ ≤ k`, all law choices). -/
def phGens (W : Submodule K (LieE K d₀ d₁ m)) (Qs : Set (MvPolynomial (Var d₀ d₁ m) K))
    (g : GPt K d₀ d₁ g₂ g₃) (k : ℕ) : Set (MvPolynomial (Var d₀ d₁ m) K) :=
  {P | ∃ Q ∈ Qs, ∃ w ∈ W, ∃ κ ≤ k, ∃ c c', P = phOp g₂ g₃ g w c c' κ Q}

/-- **Philippon, Prop. 4.4**: `h ∈ Z(δ^k_g I)` iff every `Q ∈ I` vanishes to formal order `> k`
along `W` at `h + g` (for a set `𝒬` of multihomogeneous generators). -/
theorem zeros_phOp [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
    (W : Submodule K (LieE K d₀ d₁ m)) {Qs : Set (MvPolynomial (Var d₀ d₁ m) K)}
    (hQs : ∀ Q ∈ Qs, ∃ d, IsHomE Q d) (g h : GPt K d₀ d₁ g₂ g₃) (k : ℕ) :
    h ∈ zeros ((IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span (phGens g₂ g₃ W Qs g k) :
      Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Set _) ↔
      ∀ Q ∈ Qs, OrdGt g₂ g₃ W Q k (h + g) := by
  rw [mem_zeros_iff_le_vanish]
  constructor
  · intro hz Q hQ w hw
    obtain ⟨d, hd⟩ := hQs Q hQ
    obtain ⟨c, hc⟩ := exists_good two_ne_zero hΔ h g
    obtain ⟨c', hc'⟩ := exists_good two_ne_zero hΔ g 0
    have hu : IsUnit (∏ k, lawPt g₂ g₃ h 1 g w c c' (.e k (chartAt (h + g) k)) ^ d k) :=
      IsUnit.prod_univ_iff.mpr fun k => (lawPt_unit hΔ h 1 g w hc hc' k).pow _
    refine LowZero.of_unit hu ?_
    intro i hi
    rw [← aeval_lawPt hΔ hd, ← eval_phOp_coords]
    exact mem_vanish.mp (hz (Ideal.mem_sup_right (Ideal.subset_span
      ⟨Q, hQ, w, hw, i, hi, c, c', rfl⟩))) h rfl 1
  · intro hord
    refine sup_le (IG_le_vanish two_ne_zero _) (Ideal.span_le.mpr ?_)
    rintro _ ⟨Q, hQ, w, hw, i, hi, c, c', rfl⟩
    obtain ⟨d, hd⟩ := hQs Q hQ
    refine mem_vanish.mpr fun h' hh' lam => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    rw [eval_phOp_coords, aeval_lawPt hΔ hd]
    exact (hord Q hQ w hw).mul_left _ i hi

omit [CharZero K] in
/-- The same for the whole ideal generated by `𝒬`. -/
theorem ordGt_span_iff {W : Submodule K (LieE K d₀ d₁ m)} {Qs : Set (MvPolynomial (Var d₀ d₁ m) K)}
    {k : ℕ} {p : GPt K d₀ d₁ g₂ g₃} :
    (∀ Q ∈ Ideal.span Qs, OrdGt g₂ g₃ W Q k p) ↔ ∀ Q ∈ Qs, OrdGt g₂ g₃ W Q k p := by
  refine ⟨fun h Q hQ => h Q (Ideal.subset_span hQ), fun h Q hQ => ?_⟩
  have : Ideal.span Qs ≤ ordIdeal g₂ g₃ W k {p} :=
    Ideal.span_le.mpr fun Q hQ p' hp' => (Set.mem_singleton_iff.mp hp') ▸ h Q hQ
  exact this hQ p rfl

/-- **Philippon, Prop. 4.4, ideal form**: the operators may be applied to all of `I = (𝒬)`. -/
theorem zeros_phOp_span [DecidableEq K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
    (W : Submodule K (LieE K d₀ d₁ m)) {Qs : Set (MvPolynomial (Var d₀ d₁ m) K)}
    (hQs : ∀ Q ∈ Qs, ∃ d, IsHomE Q d) (g h : GPt K d₀ d₁ g₂ g₃) (k : ℕ) :
    h ∈ zeros ((IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔
      Ideal.span (phGens g₂ g₃ W (Ideal.span Qs : Set _) g k) :
        Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Set _) ↔
      ∀ Q ∈ Ideal.span Qs, OrdGt g₂ g₃ W Q k (h + g) := by
  rw [ordGt_span_iff]
  constructor
  · intro hz
    refine (zeros_phOp hΔ W hQs g h k).mp ?_
    rw [mem_zeros_iff_le_vanish] at hz ⊢
    refine le_trans (sup_le_sup_left (Ideal.span_mono ?_) _) hz
    rintro _ ⟨Q, hQ, w, hw, κ, hκ, c, c', rfl⟩
    exact ⟨Q, Ideal.subset_span hQ, w, hw, κ, hκ, c, c', rfl⟩
  · intro hord
    let J : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
      { carrier := {Q | ∀ w ∈ W, ∀ (c c' : Fin m → Fin 2) (lam : Fin m → Kˣ),
          LowZero k (aeval (lawPt g₂ g₃ h lam g w c c') Q)}
        add_mem' := fun hP hQ w hw c c' lam i hi => by
          rw [map_add, map_add, hP w hw c c' lam i hi, hQ w hw c c' lam i hi, add_zero]
        zero_mem' := fun w _ c c' lam i _ => by simp
        smul_mem' := fun a Q hQ w hw c c' lam => by
          rw [smul_eq_mul, map_mul]; exact (hQ w hw c c' lam).mul_left _ }
    have hJ : Ideal.span Qs ≤ J := Ideal.span_le.mpr fun Q hQ w hw c c' lam => by
      obtain ⟨d, hd⟩ := hQs Q hQ
      show LowZero k _
      rw [aeval_lawPt hΔ hd]
      exact (hord Q hQ w hw).mul_left _
    refine (mem_zeros_iff_le_vanish).mpr
      (sup_le (IG_le_vanish two_ne_zero _) (Ideal.span_le.mpr ?_))
    rintro _ ⟨Q, hQ, w, hw, i, hi, c, c', rfl⟩
    refine mem_vanish.mpr fun h' hh' lam => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    rw [eval_phOp_coords]
    exact hJ hQ w hw c c' lam i hi

end Op

end LSG.ME
