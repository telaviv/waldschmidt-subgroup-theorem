import Mathlib
import LSG.ME.IG

/-!
# Translations on the multi-cone model (STAGE2 §3)

For `g ∈ G` and a choice of addition law `c : Fin m → Fin 2` per elliptic factor, `τ g c` is the
`K`-algebra endomorphism of `K[Var]` with
`X ↦ X + x_g`, `Y ↦ y_g Y`, `Z ↦ y_g⁻¹ Z`, and, in the `k`-th elliptic block,
`(U, V, W) ↦ law_{c k}((U, V, W), rep(g_k))` (bidegree `(2, 2)` addition laws, so this is quadratic
in the block variables).

* `lawc`: the two laws `law₁`, `law₂` indexed by `Fin 2`, with their properties.
* **`transl_mem_FLE`**: `τ g c` preserves the `X`- and `(Y, Z)`-block degrees and doubles the
  elliptic ones (`dblE D`).
* **`transl_IG`**: `τ g c` maps `I_G` into `I_G`.
* **`eval_transl`**: `eval (coords h λ) (τ g c P) = eval (coordsZ (h + g) ν) P` for some `ν`
  (always); **`eval_transl_good`**: if every chosen law is nonzero at `(rep hₖ, rep gₖ)`, then
  `ν = λ² μ` with `μ : Fin m → Kˣ` independent of `λ` and `P`. **`exists_good`**: some `c` is good.
* `translI g J = I_G ⊔ (τ g c P : P ∈ J, all c)`; **`zeros_translI`**:
  `zeros (translI g J) = {h | h + g ∈ zeros J}` (`K` algebraically closed, any `J`).

The Hilbert-function comparison is in `LSG.ME.TranslHF`.
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE S bdeg bdeg_single mul_mem_FLE FLE_mono pow_mem_FLE' prod_mem_FLE')

namespace LSG.ME

/-! ### The two laws, indexed by `Fin 2` -/

section Laws

variable {R : Type*} [CommRing R]

/-- `law₁` for `c = 0`, `law₂` otherwise. -/
def lawc (c : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) : Fin 3 → R :=
  if c = 0 then law₁ g₂ g₃ P Q else law₂ g₂ g₃ P Q

theorem lawc_smul (c : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) (u v : R) :
    lawc c g₂ g₃ (u • P) (v • Q) = (u * v) ^ 2 • lawc c g₂ g₃ P Q := by
  unfold lawc; split_ifs
  · exact law₁_smul g₂ g₃ P Q u v
  · exact law₂_smul g₂ g₃ P Q u v

theorem Fv_lawc_mem (c : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R) :
    Fv g₂ g₃ (lawc c g₂ g₃ P Q) ∈ Ideal.span {Fv g₂ g₃ P, Fv g₂ g₃ Q} := by
  unfold lawc; split_ifs
  · exact Fv_law₁_mem g₂ g₃ P Q
  · exact Fv_law₂_mem g₂ g₃ P Q

theorem lawc_map {S : Type*} [CommRing S] (f : R →+* S) (c : Fin 2) (g₂ g₃ : R) (P Q : Fin 3 → R)
    (i : Fin 3) : f (lawc c g₂ g₃ P Q i) = lawc c (f g₂) (f g₃) (f ∘ P) (f ∘ Q) i := by
  unfold lawc
  split_ifs <;> fin_cases i <;>
    simp [law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W, map_ofNat]

theorem Fv_map {S : Type*} [CommRing S] (f : R →+* S) (g₂ g₃ : R) (P : Fin 3 → R) :
    f (Fv g₂ g₃ P) = Fv (f g₂) (f g₃) (f ∘ P) := by
  simp [Fv, F, map_ofNat]

end Laws

section LawsField

variable {K : Type*} [Field K] [DecidableEq K] {a b : K} (h2 : (2 : K) ≠ 0)
  (hΔ : a ^ 3 - 27 * b ^ 2 ≠ 0)
include h2 hΔ

omit [DecidableEq K] in
/-- **Completeness**: some law is nonzero at a pair of points. -/
theorem exists_lawc_ne (p q : (curve a b).toAffine.Point) :
    ∃ c : Fin 2, lawc c a b (rep p) (rep q) ≠ 0 := by
  rcases law_complete h2 hΔ (Fv_rep h2 p) (Fv_rep h2 q) (rep_ne_zero p) (rep_ne_zero q) with h | h
  · exact ⟨0, by simpa [lawc] using h⟩
  · exact ⟨1, by simpa [lawc] using h⟩

/-- On representatives, a law is a multiple of `rep (p + q)` (nonzero iff the law is). -/
theorem lawc_rep (c : Fin 2) (p q : (curve a b).toAffine.Point) :
    ∃ μ : K, lawc c a b (rep p) (rep q) = μ • rep (p + q) ∧
      (lawc c a b (rep p) (rep q) ≠ 0 → μ ≠ 0) := by
  by_cases h0 : lawc c a b (rep p) (rep q) = 0
  · exact ⟨0, by rw [h0, zero_smul], fun h => absurd h0 h⟩
  · have hF : Fv a b (lawc c a b (rep p) (rep q)) = 0 := by
      have := Fv_lawc_mem c a b (rep p) (rep q)
      rw [Fv_rep h2, Fv_rep h2, Set.pair_eq_singleton, Ideal.span_singleton_eq_bot.mpr rfl] at this
      exact (Submodule.mem_bot K).mp this
    have hpt : toPoint a b (lawc c a b (rep p) (rep q)) = toPoint a b (rep (p + q)) := by
      rw [toPoint_rep h2]
      unfold lawc at h0 ⊢
      split_ifs at h0 ⊢
      · rw [toPoint_law₁ h2 hΔ (Fv_rep h2 p) (Fv_rep h2 q) (rep_ne_zero p) (rep_ne_zero q) h0,
          toPoint_rep h2, toPoint_rep h2]
      · rw [toPoint_law₂ h2 hΔ (Fv_rep h2 p) (Fv_rep h2 q) (rep_ne_zero p) (rep_ne_zero q) h0,
          toPoint_rep h2, toPoint_rep h2]
    obtain ⟨μ, hμ, he⟩ :=
      (toPoint_eq_iff h2 hΔ hF (Fv_rep h2 _) h0 (rep_ne_zero _)).mp hpt
    exact ⟨μ, he, fun _ => hμ⟩

end LawsField

/-! ### Block-degree bookkeeping -/

section FLETac

variable {σ ι : Type*} [Fintype σ] [DecidableEq ι] {K : Type*} [Field K]
  {β : σ → ι}

theorem fle_add {p q : MvPolynomial σ K} {D : ι → ℕ} (hp : p ∈ FLE K β D) (hq : q ∈ FLE K β D) :
    p + q ∈ FLE K β D := Submodule.add_mem _ hp hq

theorem fle_sub {p q : MvPolynomial σ K} {D : ι → ℕ} (hp : p ∈ FLE K β D) (hq : q ∈ FLE K β D) :
    p - q ∈ FLE K β D := Submodule.sub_mem _ hp hq

theorem fle_neg {p : MvPolynomial σ K} {D : ι → ℕ} (hp : p ∈ FLE K β D) : -p ∈ FLE K β D :=
  Submodule.neg_mem _ hp

theorem fle_le {p : MvPolynomial σ K} {D D' : ι → ℕ} (hp : p ∈ FLE K β D) (h : D ≤ D') :
    p ∈ FLE K β D' := by classical exact FLE_mono K β h hp

theorem fle_X (v : σ) : (X v : MvPolynomial σ K) ∈ FLE K β (Pi.single (β v) 1) := by
  classical
  rw [FLE, X, monomial_mem_restrictSupport]
  refine Or.inl fun i => ?_
  rw [bdeg_single]
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

theorem fle_C (a : K) {D : ι → ℕ} : (C a : MvPolynomial σ K) ∈ FLE K β D := by
  classical
  rw [FLE, ← monomial_zero', monomial_mem_restrictSupport]
  exact Or.inl fun i => by simp

theorem fle_ofNat (n : ℕ) [n.AtLeastTwo] {D : ι → ℕ} :
    (OfNat.ofNat n : MvPolynomial σ K) ∈ FLE K β D := by
  rw [← map_ofNat C n]; exact fle_C _

theorem fle_Cpow (a : K) (n : ℕ) {D : ι → ℕ} : ((C a) ^ n : MvPolynomial σ K) ∈ FLE K β D := by
  rw [← map_pow]; exact fle_C _

theorem fle_X' {v : σ} {D : ι → ℕ} (h : Pi.single (β v) 1 ≤ D) :
    (X v : MvPolynomial σ K) ∈ FLE K β D := fle_le (fle_X v) h

theorem fle_Xpow' {v : σ} {n : ℕ} {D : ι → ℕ} (h : n • Pi.single (β v) 1 ≤ D) :
    (X v ^ n : MvPolynomial σ K) ∈ FLE K β D := by
  classical exact fle_le (pow_mem_FLE' (fle_X v) n) h

theorem fle_mul_X {p : MvPolynomial σ K} {v : σ} {D : ι → ℕ}
    (hp : p ∈ FLE K β (D - Pi.single (β v) 1)) (h : Pi.single (β v) 1 ≤ D) :
    p * X v ∈ FLE K β D := by
  classical
  refine fle_le (mul_mem_FLE K hp (fle_X v)) fun i => ?_
  have := h i
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

theorem fle_mul_Xpow {p : MvPolynomial σ K} {v : σ} {n : ℕ} {D : ι → ℕ}
    (hp : p ∈ FLE K β (D - n • Pi.single (β v) 1)) (h : n • Pi.single (β v) 1 ≤ D) :
    p * X v ^ n ∈ FLE K β D := by
  classical
  refine fle_le (mul_mem_FLE K hp (pow_mem_FLE' (fle_X v) n)) fun i => ?_
  have := h i
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

theorem fle_pow_single {p : MvPolynomial σ K} {b : ι} {d : ℕ} (hp : p ∈ FLE K β (Pi.single b d))
    (n : ℕ) : p ^ n ∈ FLE K β (Pi.single b (n * d)) := by
  classical
  refine fle_le (pow_mem_FLE' hp n) ?_
  rw [Pi.le_def]
  intro i
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fle_mul_c {p b : MvPolynomial σ K} {D : ι → ℕ} (hb : b ∈ FLE K β 0) (hp : p ∈ FLE K β D) :
    p * b ∈ FLE K β D := by
  classical
  simpa using mul_mem_FLE K hp hb

end FLETac

/-- Pointwise inequalities between sums/differences of `Pi.single`s. -/
macro "fle_ineq" : tactic => `(tactic|
  (rw [Pi.le_def]
   intro b
   simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, Pi.single_apply,
     smul_eq_mul, blk_e, blk_x, blk_y, blk_z]
   split_ifs <;> omega))

/-- Block degrees of sums of products of variables, constants and numerals, against a concrete
bound (peeling factors from the right). -/
macro "fle_tac" : tactic => `(tactic|
  repeat'
    first
    | with_reducible_and_instances refine fle_add ?_ ?_
    | with_reducible_and_instances refine fle_sub ?_ ?_
    | with_reducible_and_instances refine fle_neg ?_
    | with_reducible_and_instances refine fle_mul_Xpow ?_ ?_
    | with_reducible_and_instances refine fle_mul_X ?_ ?_
    | with_reducible_and_instances refine fle_mul_c ?_ ?_
    | with_reducible_and_instances exact fle_C _
    | with_reducible_and_instances exact fle_Cpow _ _
    | with_reducible_and_instances exact fle_ofNat _
    | with_reducible_and_instances refine fle_Xpow' ?_
    | with_reducible_and_instances refine fle_X' ?_
    | fle_ineq)

/-! ### The translation `τ g c` -/

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- The variables of the `k`-th elliptic block, as a vector. -/
noncomputable def bvars (d₀ d₁ : ℕ) (k : Fin m) : Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  fun i => X (.e k i)

/-- The law `law_c((U_k, V_k, W_k), q)` in `K[Var]`. -/
noncomputable def lawPoly (g₂ g₃ : Fin m → K) (d₀ d₁ : ℕ) (c : Fin 2) (k : Fin m) (q : Fin 3 → K) :
    Fin 3 → MvPolynomial (Var d₀ d₁ m) K :=
  lawc c (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k) fun i => C (q i)

/-- The multiplier of a block: `2` on elliptic blocks, `1` otherwise. -/
def bmul : Blk m → ℕ
  | .e _ => 2
  | _ => 1

/-- Block degrees after translation: elliptic entries doubled. -/
def dblE (D : Blk m → ℕ) : Blk m → ℕ := fun b => bmul b * D b

theorem bmul_le_two (b : Blk m) : bmul b ≤ 2 := by cases b <;> simp [bmul]

theorem dblE_le (D : Blk m → ℕ) (t : ℕ) : dblE (t • D) ≤ (2 * t) • D := fun b => by
  simp only [dblE, Pi.smul_apply, smul_eq_mul]
  have := bmul_le_two b
  calc bmul b * (t * D b) ≤ 2 * (t * D b) := Nat.mul_le_mul_right _ this
    _ = 2 * t * D b := by ring

set_option maxHeartbeats 4000000 in
-- `fle_tac` on the six law components (each a sum of up to twelve monomials) needs more time.
theorem lawPoly_mem (c : Fin 2) (k : Fin m) (q : Fin 3 → K) (i : Fin 3) :
    lawPoly g₂ g₃ d₀ d₁ c k q i ∈ FLE K blk (Pi.single (Blk.e k) 2) := by
  unfold lawPoly lawc bvars
  split_ifs <;> fin_cases i <;>
    simp only [law₁, law₂, law₁U, law₁V, law₁W, law₂U, law₂V, law₂W, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    fle_tac

variable (g₂ g₃)

/-- The images of the variables under translation by `g` with law choice `c`. -/
noncomputable def translVar (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) :
    Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) K
  | .x i => X (.x i) + C (g.1 i)
  | .y j => C (g.ym j : K) * X (.y j)
  | .z j => C (((g.ym j)⁻¹ : Kˣ) : K) * X (.z j)
  | .e k i => lawPoly g₂ g₃ d₀ d₁ (c k) k (rep (g.2.2 k)) i

/-- **Translation by `g`** with law choice `c`. -/
noncomputable def τ (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) :
    MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Var d₀ d₁ m) K :=
  aeval (translVar g₂ g₃ g c)

variable {g₂ g₃}

/-- The degree of a variable's image. -/
theorem translVar_mem (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (v : Var d₀ d₁ m) :
    translVar g₂ g₃ g c v ∈ FLE K blk (Pi.single (blk v) (bmul (blk v))) := by
  cases v with
  | x i =>
    have := fle_add (fle_X (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.x i))
      (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (D := Pi.single Blk.x 1) (g.1 i))
    simpa [bmul, translVar] using this
  | y j =>
    have := mul_mem_FLE K (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0) (g.ym j : K))
      (fle_X (Var.y j : Var d₀ d₁ m))
    simpa [bmul, translVar] using this
  | z j =>
    have := mul_mem_FLE K (fle_C (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0)
      (((g.ym j)⁻¹ : Kˣ) : K)) (fle_X (Var.z j : Var d₀ d₁ m))
    simpa [bmul, translVar] using this
  | e k i =>
    have := lawPoly_mem (g₂ := g₂) (g₃ := g₃) (d₀ := d₀) (d₁ := d₁) (c k) k (rep (g.2.2 k)) i
    simpa [bmul, translVar] using this

/-- **Block degrees under translation**: `X`- and `(Y, Z)`-degrees are preserved, elliptic
degrees at most double. -/
theorem transl_mem_FLE (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) :
    τ g₂ g₃ g c P ∈ FLE K blk (dblE D) := by
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S blk D := by
    rw [FLE, mem_restrictSupport_iff] at hP; exact hP hn
  rw [τ, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  have hprod := prod_mem_FLE' (K := K) (β := (blk : Var d₀ d₁ m → Blk m)) Finset.univ
    (fun v => translVar g₂ g₃ g c v ^ n v)
    (fun v => Pi.single (blk v) (n v * bmul (blk v))) fun v _ =>
      fle_pow_single (translVar_mem g c v) (n v)
  have hle : (∑ v, (Pi.single (blk v) (n v * bmul (blk v)) : Blk m → ℕ)) ≤ dblE D := by
    rw [Pi.le_def]
    intro b
    have hb := hnS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.single_apply, dblE]
    calc ∑ v, (if b = blk v then n v * bmul (blk v) else 0)
        = ∑ v, bmul b * (if blk v = b then n v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmul b * ∑ v, (if blk v = b then n v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmul b * D b := Nat.mul_le_mul_left _ hb
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (FLE_mono K blk hle hprod)

/-! ### `I_G` is preserved -/

theorem transl_IG (h2 : (2 : K) ≠ 0) (g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2)
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) :
    τ g₂ g₃ g c P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
  have hle : (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃).map (τ g₂ g₃ g c) ≤ IG g₂ g₃ := by
    rw [IG, Ideal.ofList, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨Q, hQ, rfl⟩
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hQ
    rcases hQ with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · have : τ g₂ g₃ g c (YZ K d₀ m j) = YZ K d₀ m j := by
        simp only [YZ, τ, map_sub, map_mul, aeval_X, map_one, translVar]
        have h1 : C (g.ym j : K) * C (((g.ym j)⁻¹ : Kˣ) : K) = (1 : MvPolynomial (Var d₀ d₁ m) K)
            := by
          rw [← C_mul, Units.mul_inv, C_1]
        linear_combination (X (.y j) * X (.z j) : MvPolynomial (Var d₀ d₁ m) K) * h1
      rw [SetLike.mem_coe, this]
      exact YZ_mem_IG g₂ g₃ j
    · -- `F(law(U, q)) ∈ (F(U), F(q)) = (F_k)`
      have hmem := Fv_lawc_mem (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)
        (fun i => (C (rep (g.2.2 k) i) : MvPolynomial (Var d₀ d₁ m) K))
      have hq : Fv (C (g₂ k)) (C (g₃ k))
          (fun i => (C (rep (g.2.2 k) i) : MvPolynomial (Var d₀ d₁ m) K)) = 0 := by
        have := Fv_map (C : K →+* MvPolynomial (Var d₀ d₁ m) K) (g₂ k) (g₃ k) (rep (g.2.2 k))
        rw [Fv_rep h2, map_zero] at this
        exact this.symm
      have himg : τ g₂ g₃ g c (Fk g₂ g₃ d₀ d₁ k) =
          Fv (C (g₂ k)) (C (g₃ k)) (lawc (c k) (C (g₂ k)) (C (g₃ k)) (bvars d₀ d₁ k)
            fun i => C (rep (g.2.2 k) i)) := by
        simp only [Fk, F, Fv, τ, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
          algebraMap_eq, map_ofNat, translVar, lawPoly]
      rw [SetLike.mem_coe, himg]
      rw [hq, Set.pair_comm, Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
        at hmem
      refine Ideal.span_le.mpr ?_ hmem
      rintro _ rfl
      exact Fk_mem_IG g₂ g₃ k
  exact hle (Ideal.mem_map_of_mem _ hP)

/-! ### Evaluation -/

theorem eval_aeval' {σ : Type*} (A : MvPolynomial σ K) (h : σ → MvPolynomial σ K) (u : σ → K) :
    eval u (aeval h A) = eval (fun k => eval u (h k)) A := by
  rw [aeval_def, eval_eval₂]
  have : (eval u).comp (algebraMap K (MvPolynomial σ K)) = RingHom.id K := by ext; simp
  rw [this]; rfl

theorem eval_lawPoly (c : Fin 2) (k : Fin m) (q : Fin 3 → K) (i : Fin 3) (x : Var d₀ d₁ m → K) :
    eval x (lawPoly g₂ g₃ d₀ d₁ c k q i) = lawc c (g₂ k) (g₃ k) (fun i => x (.e k i)) q i := by
  rw [lawPoly, lawc_map]
  congr 1 <;> simp [bvars, Function.comp_def]

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Evaluation of a translate** (any law choice). -/
theorem eval_transl (g h : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) (lam : Fin m → Kˣ) :
    ∃ ν : Fin m → K, ∀ P, eval (coords h lam) (τ g₂ g₃ g c P) = eval (coordsZ (h + g) ν) P := by
  choose μ hμ _ using fun k => lawc_rep h2 (hΔ k) (c k) (h.2.2 k) (g.2.2 k)
  refine ⟨fun k => (lam k : K) ^ 2 * μ k, fun P => ?_⟩
  rw [τ, eval_aeval']
  congr 2
  funext v
  cases v with
  | x i => simp [translVar, coords, add_comm]
  | y j => simp [translVar, coords, mul_comm]
  | z j => simp [translVar, coords, mul_comm]
  | e k i =>
    simp only [translVar, eval_lawPoly, coords, coordsZ_e]
    have hs := lawc_smul (c k) (g₂ k) (g₃ k) (rep (h.2.2 k)) (rep (g.2.2 k)) (lam k : K) 1
    rw [one_smul, mul_one, hμ k, smul_smul] at hs
    have : (fun i => (lam k : K) * rep (h.2.2 k) i) = (lam k : K) • rep (h.2.2 k) := by
      funext i; simp
    rw [this, hs]
    simp [mul_assoc]

/-- The law choice `c` is **good** at `(h, g)`: every chosen law is nonzero there. -/
def Good (h g : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) : Prop :=
  ∀ k, lawc (c k) (g₂ k) (g₃ k) (rep (h.2.2 k)) (rep (g.2.2 k)) ≠ 0

omit [DecidableEq K] hΔ in
theorem exists_good (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0) (h g : GPt K d₀ d₁ g₂ g₃) :
    ∃ c, Good h g c := by
  choose c hc using fun k => exists_lawc_ne h2 (hΔ k) (h.2.2 k) (g.2.2 k)
  exact ⟨c, hc⟩

/-- **Evaluation of a translate**, good law choice: `ν = λ² μ` with `μ` independent of `λ`. -/
theorem eval_transl_good {g h : GPt K d₀ d₁ g₂ g₃} {c : Fin m → Fin 2} (hc : Good h g c) :
    ∃ μ : Fin m → Kˣ, ∀ lam P, eval (coords h lam) (τ g₂ g₃ g c P) =
      eval (coords (h + g) fun k => lam k ^ 2 * μ k) P := by
  choose μ hμ hμ0 using fun k => lawc_rep h2 (hΔ k) (c k) (h.2.2 k) (g.2.2 k)
  refine ⟨fun k => Units.mk0 (μ k) (hμ0 k (hc k)), fun lam P => ?_⟩
  rw [τ, eval_aeval']
  congr 2
  funext v
  cases v with
  | x i => simp [translVar, coords, add_comm]
  | y j => simp [translVar, coords, mul_comm]
  | z j => simp [translVar, coords, mul_comm]
  | e k i =>
    simp only [translVar, eval_lawPoly, coords, coordsZ_e]
    have hs := lawc_smul (c k) (g₂ k) (g₃ k) (rep (h.2.2 k)) (rep (g.2.2 k)) (lam k : K) 1
    rw [one_smul, mul_one, hμ k, smul_smul] at hs
    have : (fun i => (lam k : K) * rep (h.2.2 k) i) = (lam k : K) • rep (h.2.2 k) := by
      funext i; simp
    rw [this, hs]
    simp [mul_assoc]

omit [DecidableEq K] h2 hΔ in
/-- Every `ν ∈ (Kˣ)^m` is `λ² μ` for some `λ` (`K` algebraically closed). -/
theorem exists_sq_mul [IsAlgClosed K] (μ ν : Fin m → Kˣ) :
    ∃ lam : Fin m → Kˣ, (fun k => lam k ^ 2 * μ k) = ν := by
  have : ∀ k, ∃ z : Kˣ, z ^ 2 * μ k = ν k := fun k => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((ν k : K) / μ k) (n := 2) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
      exact div_ne_zero (ν k).ne_zero (μ k).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
    field_simp
  choose lam hlam using this
  exact ⟨lam, funext hlam⟩

/-! ### Ideal translates -/

omit h2 hΔ in
variable (g₂ g₃) in
/-- The ideal translate `τ_g J = I_G + (τ g c P : P ∈ J, all c)`; its zeros are `zeros J − g`. -/
noncomputable def translI (g : GPt K d₀ d₁ g₂ g₃) (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span {Q | ∃ P ∈ J, ∃ c, Q = τ g₂ g₃ g c P}

/-- **Zeros of an ideal translate.** -/
theorem zeros_translI [IsAlgClosed K] (g : GPt K d₀ d₁ g₂ g₃)
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    zeros (translI g₂ g₃ g J : Set _) = {h | h + g ∈ zeros (J : Set _)} := by
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hh P hP lam'
    obtain ⟨c, hc⟩ := exists_good h2 hΔ h g
    obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc
    obtain ⟨lam, hlam⟩ := exists_sq_mul μ lam'
    have := hh _ (Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, c, rfl⟩)) lam
    rw [hμ, hlam] at this
    exact this
  · intro hh
    rw [mem_zeros_iff_le_vanish]
    refine sup_le (IG_le_vanish h2 _) (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, hP, c, rfl⟩
    refine mem_vanish.mpr fun h' hh' lam => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    obtain ⟨ν, hν⟩ := eval_transl h2 hΔ g h' c lam
    rw [hν]
    exact eval_coordsZ_eq_zero (hh P hP) ν

end LSG.ME
