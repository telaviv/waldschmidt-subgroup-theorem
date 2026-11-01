import Mathlib
import LSG.MEV.MainVecLe

/-!
# The 4-block grading of `G̃` (STAGE5_MEV §10.3)

`blk4 a` refines `blk`: the additive variables `x i` with `i < a` (*leading*) and `i ≥ a`
(*trailing*) get separate blocks; `yz` and the `E^♮` blocks are as in `blk`.

* `Blk4`, `blk4 a`, `D4f A B C E` (lead, trail, yz, `E^♮`), `b4to3` (forget the split).
* **`fle4_of_fle`**: `FLE blk D ⊆ FLE (blk4 a) D'` when `D ∘ b4to3 ≤ D'`.
* **`hdim4_eq`**: the Hilbert dimension does not depend on the grading
  (`StrongSix.M2.hdim_add_height_eq`).
* `CF4`, **`phOp_mem_FLE4`**, `translVar_mem4`, **`transl_mem_FLE4`**: Philippon's operators and
  translations preserve the 4-block degrees (`E^♮` degrees at most tripled), in particular they
  never
  raise the trailing degree; `transl_gensR2_mem_FLE4` for the generators of Roy's ideal.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE S bdeg mul_mem_FLE FLE_mono hdata)

namespace LSG.MEV

/-- The four blocks: leading `x`, trailing `x`, `(Y, Z)`, one per `E^♮` factor. -/
inductive Blk4 (m : ℕ)
  | xl
  | xt
  | yz
  | e (k : Fin m)
  deriving DecidableEq, Fintype

variable {d₀ d₁ m : ℕ}

/-- The 4-block grading with cutoff `a` (`x i` leading iff `i < a`). -/
def blk4 (a : ℕ) : Var d₀ d₁ m → Blk4 m
  | .x i => if (i : ℕ) < a then .xl else .xt
  | .y _ => .yz
  | .z _ => .yz
  | .e k _ => .e k

@[simp] theorem blk4_y (a : ℕ) (j : Fin d₁) : blk4 a (.y j : Var d₀ d₁ m) = .yz := rfl
@[simp] theorem blk4_z (a : ℕ) (j : Fin d₁) : blk4 a (.z j : Var d₀ d₁ m) = .yz := rfl
@[simp] theorem blk4_e (a : ℕ) (k : Fin m) (c : Fin 5) :
    blk4 a (.e k c : Var d₀ d₁ m) = .e k := rfl
theorem blk4_x (a : ℕ) (i : Fin d₀) :
    blk4 a (.x i : Var d₀ d₁ m) = if (i : ℕ) < a then .xl else .xt := rfl

/-- The block degrees `(A, B, C, E)` (lead, trail, `yz`, `E^♮`). -/
def D4f (A B C E : ℕ) : Blk4 m → ℕ
  | .xl => A
  | .xt => B
  | .yz => C
  | .e _ => E

@[simp] theorem D4f_xl (A B C E : ℕ) : (D4f A B C E : Blk4 m → ℕ) .xl = A := rfl
@[simp] theorem D4f_xt (A B C E : ℕ) : (D4f A B C E : Blk4 m → ℕ) .xt = B := rfl
@[simp] theorem D4f_yz (A B C E : ℕ) : (D4f A B C E : Blk4 m → ℕ) .yz = C := rfl
@[simp] theorem D4f_e (A B C E : ℕ) (k : Fin m) : (D4f A B C E : Blk4 m → ℕ) (.e k) = E := rfl

theorem D4f_pos {A B C E : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hE : 1 ≤ E) :
    ∀ i : Blk4 m, 1 ≤ D4f A B C E i := fun i => by cases i <;> simpa

/-- Forget the lead/trail split. -/
def b4to3 : Blk4 m → Blk m
  | .xl => .x
  | .xt => .x
  | .yz => .yz
  | .e k => .e k

theorem b4to3_blk4 (a : ℕ) (v : Var d₀ d₁ m) : b4to3 (blk4 a v) = blk v := by
  cases v with
  | x i => simp only [blk4_x]; split_ifs <;> rfl
  | _ => rfl

theorem bdeg4_le (a : ℕ) (s : Var d₀ d₁ m →₀ ℕ) (b : Blk4 m) :
    bdeg (blk4 a) s b ≤ bdeg blk s (b4to3 b) := by
  unfold bdeg
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases h : blk4 a v = b
  · have h' : blk v = b4to3 b := by rw [← h, b4to3_blk4]
    simp [h, h']
  · simp [h]

variable {K : Type*} [Field K]

/-- **Transfer from the 3-block grading.** -/
theorem fle4_of_fle (a : ℕ) {D : Blk m → ℕ} {D' : Blk4 m → ℕ} (hD : ∀ b, D (b4to3 b) ≤ D' b)
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ FLE K blk D) : P ∈ FLE K (blk4 a) D' := by
  classical
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at hP ⊢
  intro s hs b
  exact (bdeg4_le a s b).trans ((hP hs (b4to3 b)).trans (hD b))

/-- **The Hilbert dimension does not depend on the grading.** -/
theorem hdim4_eq (a : ℕ) {D' : Blk4 m → ℕ} (hD' : ∀ i, 1 ≤ D' i) {D : Blk m → ℕ}
    (hD : ∀ i, 1 ≤ D i) {L : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (hL : L ≠ ⊤) :
    (hdata (blk4 a) D' K L).1 = (hdata blk D K L).1 := by
  have h1 := StrongSix.M2.hdim_add_height_eq (blk4 a) D' hD' hL
  have h2 := StrongSix.M2.hdim_add_height_eq blk D hD hL
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hL)
  rw [← hn] at h1 h2
  have e1 : (hdata (blk4 a) D' K L).1 + n = Fintype.card (Var d₀ d₁ m) := by exact_mod_cast h1
  have e2 : (hdata blk D K L).1 + n = Fintype.card (Var d₀ d₁ m) := by exact_mod_cast h2
  omega

/-! ### Multiplier and block degrees under `phOp`, `τ` -/

/-- `3` on `E^♮` blocks, `1` elsewhere. -/
def bmul4 : Blk4 m → ℕ
  | .e _ => 3
  | _ => 1

/-- Block degrees after `phOp` / translation. -/
def tpl4 (D : Blk4 m → ℕ) : Blk4 m → ℕ := fun b => bmul4 b * D b

theorem bmul4_le_three (b : Blk4 m) : bmul4 b ≤ 3 := by cases b <;> simp [bmul4]

theorem tpl4_tpl4_le (D : Blk4 m → ℕ) : tpl4 (tpl4 D) ≤ 9 • D := fun b => by
  simp only [tpl4, Pi.smul_apply, smul_eq_mul]
  have := bmul4_le_three b
  calc bmul4 b * (bmul4 b * D b) ≤ 3 * (3 * D b) :=
        Nat.mul_le_mul this (Nat.mul_le_mul_right _ this)
    _ = 9 * D b := by ring

theorem single_b4to3_le (a : ℕ) (v : Var d₀ d₁ m) (hv : ∀ i, v ≠ .x i) (d : ℕ) :
    ∀ b, (Pi.single (blk v) d : Blk m → ℕ) (b4to3 b) ≤ (Pi.single (blk4 a v) d : Blk4 m → ℕ) b := by
  intro b
  cases v with
  | x i => exact absurd rfl (hv i)
  | y j => cases b <;> simp [b4to3]
  | z j => cases b <;> simp [b4to3]
  | e k c => cases b <;> simp [Pi.single_apply, b4to3]

/-- The sum bound shared by `phOp` and `τ`. -/
theorem sum_single_le_tpl4 (a : ℕ) {D : Blk4 m → ℕ} {s : Var d₀ d₁ m →₀ ℕ}
    (hs : s ∈ S (blk4 a) D) :
    (∑ v, (Pi.single (blk4 a v) (s v * bmul4 (blk4 a v)) : Blk4 m → ℕ)) ≤ tpl4 D := by
  rw [Pi.le_def]
  intro b
  have hb := hs b
  simp only [bdeg] at hb
  simp only [Finset.sum_apply, Pi.single_apply, tpl4]
  calc ∑ v, (if b = blk4 a v then s v * bmul4 (blk4 a v) else 0)
      = ∑ v, bmul4 b * (if blk4 a v = b then s v else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : b = blk4 a v
        · subst h; simp [mul_comm]
        · simp [h, Ne.symm h]
    _ = bmul4 b * ∑ v, (if blk4 a v = b then s v else 0) := by rw [Finset.mul_sum]
    _ ≤ bmul4 b * D b := Nat.mul_le_mul_left _ hb

section CF4

variable {Ls : Fin m → PeriodPair}

local notation "PS" => PowerSeries (MvPolynomial (Var d₀ d₁ m) ℂ)

variable (a : ℕ)

/-- All coefficients in `FLE (blk4 a) D`. -/
def CF4 (D : Blk4 m → ℕ) (F : PS) : Prop := ∀ n, PowerSeries.coeff n F ∈ FLE ℂ (blk4 a) D

variable {a}

theorem CF4_add {D : Blk4 m → ℕ} {F G : PS} (hF : CF4 a D F) (hG : CF4 a D G) :
    CF4 a D (F + G) :=
  fun n => by rw [map_add]; exact LSG.ME.fle_add (hF n) (hG n)

theorem CF4_mul {D E : Blk4 m → ℕ} {F G : PS} (hF : CF4 a D F) (hG : CF4 a E G) :
    CF4 a (D + E) (F * G) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact Submodule.sum_mem _ fun p _ => mul_mem_FLE ℂ (hF p.1) (hG p.2)

theorem CF4_C {D : Blk4 m → ℕ} {p : MvPolynomial (Var d₀ d₁ m) ℂ} (hp : p ∈ FLE ℂ (blk4 a) D) :
    CF4 a D (PowerSeries.C p) := fun n => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact Submodule.zero_mem _

theorem CF4_mapC {D : Blk4 m → ℕ} (B : PowerSeries ℂ) :
    CF4 a D (PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ) B) :=
  fun n => by rw [PowerSeries.coeff_map]; exact LSG.ME.fle_C _

theorem CF4_one {D : Blk4 m → ℕ} : CF4 a D (1 : PS) := by
  rw [← map_one PowerSeries.C]; exact CF4_C (by rw [← C_1]; exact LSG.ME.fle_C _)

theorem CF4_pow {D : Blk4 m → ℕ} {F : PS} (hF : CF4 a D F) (n : ℕ) : CF4 a (n • D) (F ^ n) := by
  induction n with
  | zero => simpa using (CF4_one (a := a) (D := 0))
  | succ n ih => rw [pow_succ, succ_nsmul]; exact CF4_mul ih hF

theorem CF4_prod {ι' : Type*} (s : Finset ι') (f : ι' → PS) (e : ι' → Blk4 m → ℕ)
    (h : ∀ i ∈ s, CF4 a (e i) (f i)) : CF4 a (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CF4_one (a := a) (D := 0))
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact CF4_mul (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CF4_sum {ι' : Type*} (s : Finset ι') (f : ι' → PS) {D : Blk4 m → ℕ}
    (h : ∀ i ∈ s, CF4 a D (f i)) : CF4 a D (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact Submodule.sum_mem _ fun i hi => h i hi n

theorem CF4_of_CF {D : Blk m → ℕ} {D' : Blk4 m → ℕ} (hD : ∀ b, D (b4to3 b) ≤ D' b) {F : PS}
    (hF : CF D F) : CF4 a D' F := fun n => fle4_of_fle a hD (hF n)

theorem CF4_phSub (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC)
    (v : Var d₀ d₁ m) :
    CF4 a (Pi.single (blk4 a v) (bmul4 (blk4 a v))) (phSub Ls g w c c' v) := by
  cases v with
  | x i =>
    have hX := LSG.ME.fle_X (K := ℂ) (β := (blk4 a : Var d₀ d₁ m → Blk4 m)) (.x i)
    have hb : bmul4 (blk4 a (.x i : Var d₀ d₁ m)) = 1 := by
      simp only [blk4_x]; split_ifs <;> rfl
    simp only [phSub, hb]
    exact CF4_add (CF4_C hX) (CF4_mapC _)
  | y j =>
    have h := CF_phSub g w c c' (.y j)
    exact CF4_of_CF (single_b4to3_le a _ (fun _ h => by cases h) _) h
  | z j =>
    have h := CF_phSub g w c c' (.z j)
    exact CF4_of_CF (single_b4to3_le a _ (fun _ h => by cases h) _) h
  | e k i =>
    have h := CF_phSub g w c c' (.e k i)
    exact CF4_of_CF (single_b4to3_le a _ (fun _ h => by cases h) _) h

/-- **`phOp` and the 4-block degrees**: `E^♮` degrees at most tripled, leading, trailing and
`yz` degrees preserved, for every `κ`. -/
theorem phOp_mem_FLE4 (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    {D : Blk4 m → ℕ} {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ FLE ℂ (blk4 a) D) :
    phOp Ls g w c c' κ Q ∈ FLE ℂ (blk4 a) (tpl4 D) := by
  suffices h : CF4 a (tpl4 D) (aeval (phSub Ls g w c c') Q) by exact h κ
  rw [Q.as_sum, map_sum]
  refine CF4_sum _ _ fun s hs => ?_
  have hsS : s ∈ S (blk4 a) D := by
    rw [FLE, mem_restrictSupport_iff] at hQ; exact hQ hs
  rw [aeval_monomial, Finsupp.prod]
  have h1 : ∀ v, CF4 a (s v • Pi.single (blk4 a v) (bmul4 (blk4 a v)))
      (phSub Ls g w c c' v ^ s v) := fun v => CF4_pow (CF4_phSub g w c c' v) (s v)
  have hprod : CF4 a (∑ v ∈ s.support, s v • Pi.single (blk4 a v) (bmul4 (blk4 a v)))
      (∏ v ∈ s.support, phSub Ls g w c c' v ^ s v) := CF4_prod _ _ _ fun v _ => h1 v
  have hle : (∑ v ∈ s.support, (s v • Pi.single (blk4 a v) (bmul4 (blk4 a v)) : Blk4 m → ℕ)) ≤
      tpl4 D := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ _ => Nat.zero_le _) (le_trans (le_of_eq ?_) (sum_single_le_tpl4 a hsS))
    refine Finset.sum_congr rfl fun v _ => ?_
    funext b
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hc : ∀ x : ℂ, CF4 a (0 : Blk4 m → ℕ) (algebraMap ℂ PS x) := fun x => by
    rw [PowerSeries.algebraMap_apply]; exact CF4_C (LSG.ME.fle_C _)
  have hm := CF4_mul (hc (Q.coeff s)) hprod
  exact fun n => FLE_mono ℂ (blk4 a) (by simpa using hle) (hm n)

end CF4

/-! ### Translations -/

variable {Ls : Fin m → PeriodPair}

theorem translVar_mem4 (a : ℕ) (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) (v : Var d₀ d₁ m) :
    translVar Ls g c v ∈ FLE ℂ (blk4 a) (Pi.single (blk4 a v) (bmul4 (blk4 a v))) := by
  cases v with
  | x i =>
    have hb : bmul4 (blk4 a (.x i : Var d₀ d₁ m)) = 1 := by
      simp only [blk4_x]; split_ifs <;> rfl
    rw [hb]
    exact LSG.ME.fle_add (LSG.ME.fle_X (K := ℂ) (β := (blk4 a : Var d₀ d₁ m → Blk4 m)) (Var.x i))
      (LSG.ME.fle_C _)
  | y j =>
    exact fle4_of_fle a (single_b4to3_le a _ (fun _ h => by cases h) _) (translVar_mem g c _)
  | z j =>
    exact fle4_of_fle a (single_b4to3_le a _ (fun _ h => by cases h) _) (translVar_mem g c _)
  | e k i =>
    exact fle4_of_fle a (single_b4to3_le a _ (fun _ h => by cases h) _) (translVar_mem g c _)

/-- **Translations and the 4-block degrees.** -/
theorem transl_mem_FLE4 (a : ℕ) (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) {D : Blk4 m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ FLE ℂ (blk4 a) D) :
    τ Ls g c P ∈ FLE ℂ (blk4 a) (tpl4 D) := by
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S (blk4 a) D := by
    rw [FLE, mem_restrictSupport_iff] at hP; exact hP hn
  rw [τ, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  have hprod := StrongSix.M2.prod_mem_FLE' (K := ℂ) (β := (blk4 a : Var d₀ d₁ m → Blk4 m))
    Finset.univ (fun v => translVar Ls g c v ^ n v)
    (fun v => Pi.single (blk4 a v) (n v * bmul4 (blk4 a v))) fun v _ =>
      LSG.ME.fle_pow_single (translVar_mem4 a g c v) (n v)
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (FLE_mono ℂ (blk4 a) (sum_single_le_tpl4 a hnS) hprod)

/-- **Generators of Roy's ideal** in the 4-block grading. -/
theorem transl_gensR2_mem_FLE4 (a : ℕ) {W : Submodule ℂ (LieV ℂ d₀ d₁ m)}
    {S' : Finset (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ} {T : ℕ} {D : Blk4 m → ℕ}
    (hPD : P ∈ FLE ℂ (blk4 a) D) (r : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hQ : Q ∈ gensR2 Ls W S' P T r) (v : GPtV d₀ d₁ Ls) (c : Fin m → LC) :
    τ Ls v c Q ∈ FLE ℂ (blk4 a) (9 • D) := by
  obtain ⟨σ, _, w, _, κ, _, c₁, c₂, rfl⟩ := hQ
  exact LSG.ME.fle_le (transl_mem_FLE4 a v c (phOp_mem_FLE4 σ w c₁ c₂ κ hPD)) (tpl4_tpl4_le D)

end LSG.MEV
