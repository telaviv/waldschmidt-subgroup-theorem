import Mathlib
import LSG.MEV.HomDeriv

/-!
# Homogenised words at every cone representative; mixed charts (`mem_VOg_mixV`)

The input format of the Wüstholz step: Roy's ideal `A` must vanish to order `> T` modulo `I(E)`
for words in the homogenised chart derivations of **all** charts. Here this is derived from the
formal order `OrdGt` of the chain layer.

* `chartIdeal ch = (L_k − 1)_k`: both `Dv ch w` and `Dhc ch w` kill the chart forms of `ch`
  (`dvalB_bi`), so they map `chartIdeal ch` into itself, and they agree modulo it
  (`Dhc_sub_Dv_mem`: the homogenising factors are `≡ 1`). Hence **every word in `Dhc ch` agrees with
  the same word in `Dv ch` modulo `chartIdeal ch`** (`DL_Dhc_sub_DL_Dv`); no homogeneity needed.
* **`vanCan_of_ordGtV`**: for homogeneous `Q` with `OrdGt W Q n g`, all words of length `≤ n` in the
  homogenised canonical-chart derivations `Dhc (chartsV g) w`, `w ∈ W`, vanish at every cone
  representative of `g` (from `words_of_ordGt` at the normalised representative, the comparison
  above, and homogeneity of the words, `isHomV_DLc`).
* `satV`: cancellation of a factor nonvanishing at the cone representatives of `g`.
* **`Dhc_mem_VOV_chart`** (chart change, from `chgV`): derivatives in any chart lower the
  canonical order by one (homogeneous `x`).
* `DmixV`, `WmixV`: all homogenised derivations, indexed by (chart, direction).
* **`mem_VOg_mixV`**: homogeneous `x` with `OrdGt W x n g` at every `g ∈ E` lies in
  `VOg DmixV (WmixV W) (I(E)) n`. `IG_le_VOg_mixV`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk VOg mem_VOg_succ mem_VOg_zero VOg_le VOg_succ_le VOg_anti)
open StrongSix.M2 (DL DL_cons)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### The chart ideal -/

/-- The ideal `(L_k − 1)_k` of the chart forms of `ch`. -/
noncomputable def chartIdeal (d₀ d₁ : ℕ) (ch : Fin m → Fin 2) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  Ideal.span (Set.range fun k => (X (.e k (bi (ch k))) : MvPolynomial (Var d₀ d₁ m) ℂ) - 1)

theorem X_sub_one_mem (ch : Fin m → Fin 2) (k : Fin m) :
    (X (.e k (bi (ch k))) : MvPolynomial (Var d₀ d₁ m) ℂ) - 1 ∈ chartIdeal d₀ d₁ ch :=
  Ideal.subset_span ⟨k, rfl⟩

theorem prod_sub_one_mem {R ι : Type*} [CommRing R] {I : Ideal R} (s : Finset ι) (f : ι → R)
    (h : ∀ k ∈ s, f k - 1 ∈ I) : ∏ k ∈ s, f k - 1 ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : f a * ∏ k ∈ s, f k - 1 = f a * (∏ k ∈ s, f k - 1) + (f a - 1) := by ring
    rw [e]
    exact I.add_mem (I.mul_mem_left _ (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))
      (h a (Finset.mem_insert_self a s))

theorem sq_sub_one_mem (ch : Fin m → Fin 2) (k : Fin m) :
    (X (.e k (bi (ch k))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ 2 - 1 ∈ chartIdeal d₀ d₁ ch := by
  have e : (X (.e k (bi (ch k))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ 2 - 1 =
      (X (.e k (bi (ch k))) + 1) * (X (.e k (bi (ch k))) - 1) := by ring
  rw [e]; exact Ideal.mul_mem_left _ _ (X_sub_one_mem ch k)

theorem facV_sub_one_mem (ch : Fin m → Fin 2) (v : Var d₀ d₁ m) :
    facV ch v - 1 ∈ chartIdeal d₀ d₁ ch := by
  cases v with
  | e k c => exact prod_sub_one_mem _ _ fun k' _ => sq_sub_one_mem ch k'
  | x i => exact prod_sub_one_mem _ _ fun k' _ => sq_sub_one_mem ch k'
  | y j => exact prod_sub_one_mem _ _ fun k' _ => sq_sub_one_mem ch k'
  | z j => exact prod_sub_one_mem _ _ fun k' _ => sq_sub_one_mem ch k'

/-- A derivation killing the chart forms maps `chartIdeal` into itself. -/
theorem map_chartIdeal (ch : Fin m → Fin 2)
    (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    (hD : ∀ k, D (X (.e k (bi (ch k)))) = 0) {x : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hx : x ∈ chartIdeal d₀ d₁ ch) : D x ∈ chartIdeal d₀ d₁ ch := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    rw [map_sub, hD, Derivation.map_one_eq_zero, sub_zero]; exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
  | smul a y hy' hy =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')

theorem Dv_bi (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    Dv Ls ch w (X (.e k (bi (ch k)))) = 0 := by rw [Dv_X, dvV_bi]

theorem Dhc_bi (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    Dhc Ls ch w (X (.e k (bi (ch k)))) = 0 := by rw [Dhc_X, dvh, dvV_bi, mul_zero]

/-- `Dhc` and `Dv` agree modulo `chartIdeal`. -/
theorem Dhc_sub_Dv_mem (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m)
    (y : MvPolynomial (Var d₀ d₁ m) ℂ) : Dhc Ls ch w y - Dv Ls ch w y ∈ chartIdeal d₀ d₁ ch := by
  rw [Dhc_eq_sum, Dv_eq_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun v _ => ?_
  have e : dvh Ls ch w v * pderiv v y - dvV Ls ch w v * pderiv v y =
      (facV ch v - 1) * (dvV Ls ch w v * pderiv v y) := by simp only [dvh]; ring
  rw [e]; exact Ideal.mul_mem_right _ _ (facV_sub_one_mem ch v)

/-- **Words in `Dhc ch` and in `Dv ch` agree modulo `chartIdeal ch`.** -/
theorem DL_Dhc_sub_DL_Dv (ch : Fin m → Fin 2) :
    ∀ (l : List (LieV ℂ d₀ d₁ m)) {y y' : MvPolynomial (Var d₀ d₁ m) ℂ},
      y - y' ∈ chartIdeal d₀ d₁ ch → DL (Dhc Ls ch) l y - DL (Dv Ls ch) l y' ∈ chartIdeal d₀ d₁ ch
  | [], _, _, h => by simpa using h
  | w :: l, y, y', h => by
    rw [DL_cons, DL_cons]
    refine DL_Dhc_sub_DL_Dv ch l ?_
    have e : Dhc Ls ch w y - Dv Ls ch w y' = (Dhc Ls ch w y - Dv Ls ch w y) + Dv Ls ch w (y - y') :=
      by rw [map_sub]; ring
    rw [e]
    exact Ideal.add_mem _ (Dhc_sub_Dv_mem ch w y) (map_chartIdeal ch _ (Dv_bi ch w) h)

theorem eval_chartIdeal (g : GPtV d₀ d₁ Ls) {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ chartIdeal d₀ d₁ (chartsV g)) : eval (coords g 1) P = 0 := by
  have hle : chartIdeal d₀ d₁ (chartsV g) ≤ RingHom.ker (eval (coords g 1)) := by
    rw [chartIdeal, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp [coords, chartsV, repV_chart]
  exact hle hP

/-- At the normalised representative, homogenised canonical words are the plain ones. -/
theorem eval_DL_Dhc_chartsV (g : GPtV d₀ d₁ Ls) (l : List (LieV ℂ d₀ d₁ m))
    (x : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (coords g 1) (DL (Dhc Ls (chartsV g)) l x) =
      eval (coords g 1) (DL (Dv Ls (chartsV g)) l x) := by
  have := eval_chartIdeal g (DL_Dhc_sub_DL_Dv (Ls := Ls) (chartsV g) l (y := x) (y' := x)
    (by rw [sub_self]; exact Ideal.zero_mem _))
  rwa [map_sub, sub_eq_zero] at this

theorem DL_eq_DLV (ch : Fin m → Fin 2) :
    ∀ (l : List (LieV ℂ d₀ d₁ m)) (Q : MvPolynomial (Var d₀ d₁ m) ℂ),
      DL (Dv Ls ch) l Q = DLV Ls ch l.reverse Q
  | [], Q => rfl
  | w :: l, Q => by
    rw [DL_cons, DL_eq_DLV ch l, List.reverse_cons, DLV, DLV, List.foldr_append]
    rfl

theorem mem_vanish_singleton {g : GPtV d₀ d₁ Ls} {P : MvPolynomial (Var d₀ d₁ m) ℂ} :
    P ∈ vanish {g} ↔ ∀ lam, eval (coords g lam) P = 0 := by
  rw [mem_vanish]; simp

/-- **Formal order ⇒ homogenised canonical words vanish at all cone representatives.** -/
theorem vanCan_of_ordGtV {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {n : ℕ} {g : GPtV d₀ d₁ Ls} (h : OrdGt Ls W Q n g) :
    Q ∈ VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) n := by
  intro l hlW hl
  refine mem_vanish_singleton.mpr fun lam => ?_
  rw [eval_coords_isHomV (isHomV_DLc hQ _ l) g lam, eval_DL_Dhc_chartsV, DL_eq_DLV,
    words_of_ordGt hQ h l.reverse (fun x hx => hlW x (List.mem_reverse.mp hx))
      (by simpa using hl), mul_zero]

/-! ### Chart change in the order of vanishing -/

/-- **Saturation**. -/
theorem satV (ch : Fin m → Fin 2) (W : Set (LieV ℂ d₀ d₁ m)) {g : GPtV d₀ d₁ Ls}
    {u : MvPolynomial (Var d₀ d₁ m) ℂ} (hu : ∀ lam, eval (coords g lam) u ≠ 0) :
    ∀ (n : ℕ) (y : MvPolynomial (Var d₀ d₁ m) ℂ), u * y ∈ VOg (Dhc Ls ch) W (vanish {g}) n →
      y ∈ VOg (Dhc Ls ch) W (vanish {g}) n := by
  intro n
  induction n with
  | zero =>
    intro y hy
    rw [mem_VOg_zero, mem_vanish_singleton] at hy ⊢
    intro lam
    have := hy lam
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).resolve_left (hu lam)
  | succ n ih =>
    intro y hy
    have hy' : y ∈ VOg (Dhc Ls ch) W (vanish {g}) n := ih y (VOg_succ_le n hy)
    rw [mem_VOg_succ] at hy ⊢
    refine ⟨VOg_le n hy', fun w hw => ih _ ?_⟩
    have h1 := hy.2 w hw
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := Ideal.mul_mem_left _ (Dhc Ls ch w u) hy'
    have := Ideal.sub_mem _ h1 h2
    rwa [mul_comm y, add_sub_cancel_right] at this

theorem eval_Lcv_chartsV_ne (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) :
    eval (coords g lam) (Lcv d₀ d₁ (chartsV g)) ≠ 0 := by
  simp [Lcv, coords, chartsV, repV_chart, Finset.prod_ne_zero_iff]

theorem IG_le_VOV (ch : Fin m → Fin 2) (W : Set (LieV ℂ d₀ d₁ m)) (n : ℕ)
    (E : Set (GPtV d₀ d₁ Ls)) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ VOg (Dhc Ls ch) W (vanish E) n :=
  fun _ hx l _ _ => IG_le_vanish E (DLc_IG ch l hx)

/-- **Chart change**: derivatives in any chart lower the canonical order by one. -/
theorem Dhc_mem_VOV_chart (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) {g : GPtV d₀ d₁ Ls} {n : ℕ}
    {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hx : IsHomV x d)
    (hxv : x ∈ VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) (n + 1))
    (ch : Fin m → Fin 2) {w : LieV ℂ d₀ d₁ m} (hw : w ∈ W) :
    Dhc Ls ch w x ∈ VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) n := by
  refine satV (chartsV g) W (eval_Lcv_chartsV_ne g) n _ ?_
  have hG := IG_le_VOV (Ls := Ls) (chartsV g) W n {g} (chgV (chartsV g) ch w hx)
  have h1 := Ideal.mul_mem_left _ (Lcv d₀ d₁ ch) ((mem_VOg_succ.mp hxv).2 w hw)
  have h3 : ∑ k, aeV Ls (chartsV g) ch w k * (d k • x) ∈
      VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) n :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (by
      rw [nsmul_eq_mul]; exact Ideal.mul_mem_left _ _ (VOg_succ_le n hxv))
  have := Ideal.add_mem _ (Ideal.add_mem _ hG h1) h3
  convert this using 1
  ring

/-! ### Mixed charts -/

variable (Ls) in
/-- All homogenised derivations, indexed by (chart, direction). -/
noncomputable def DmixV (p : (Fin m → Fin 2) × LieV ℂ d₀ d₁ m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  Dhc Ls p.1 p.2

/-- The index set of `W`-directions in all charts. -/
def WmixV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) : Set ((Fin m → Fin 2) × LieV ℂ d₀ d₁ m) :=
  {p | p.2 ∈ W}

/-- Mixed-chart words lower the canonical order by their length (homogeneous `x`). -/
theorem DLmix_mem_VOV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) {g : GPtV d₀ d₁ Ls}
    (l : List ((Fin m → Fin 2) × LieV ℂ d₀ d₁ m)) (hlW : ∀ p ∈ l, p ∈ WmixV W) :
    ∀ {b : ℕ} {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}, IsHomV x d →
      x ∈ VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) (l.length + b) →
      DL (DmixV Ls) l x ∈ VOg (Dhc Ls (chartsV g)) (W : Set (LieV ℂ d₀ d₁ m)) (vanish {g}) b := by
  induction l with
  | nil => intro b x d _ hxv; simpa using hxv
  | cons p l ih =>
    intro b x d hx hxv
    rw [DL_cons]
    refine ih (fun q hq => hlW q (List.mem_cons_of_mem _ hq)) (isHomV_Dhc hx p.1 p.2) ?_
    refine Dhc_mem_VOV_chart W hx ?_ p.1 (hlW p List.mem_cons_self)
    simpa [List.length_cons, add_assoc, add_comm 1] using hxv

/-- **Formal order at every point of `E` ⇒ order modulo `I(E)` in all charts.** -/
theorem mem_VOg_mixV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) {E : Set (GPtV d₀ d₁ Ls)}
    {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hx : IsHomV x d) {n : ℕ}
    (hv : ∀ g ∈ E, OrdGt Ls W x n g) : x ∈ VOg (DmixV Ls) (WmixV W) (vanish E) n := by
  intro l hlW hl
  refine mem_vanish.mpr fun g hg lam => ?_
  have h1 := DLmix_mem_VOV W l hlW hx (b := 0)
    (VOg_anti (by omega) (vanCan_of_ordGtV hx (hv g hg)))
  exact mem_vanish_singleton.mp (mem_VOg_zero.mp h1) lam

theorem IG_le_VOg_mixV (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ) (E : Set (GPtV d₀ d₁ Ls)) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤ VOg (DmixV Ls) (WmixV W) (vanish E) n := by
  intro x hx l _ _
  have : ∀ (l : List ((Fin m → Fin 2) × LieV ℂ d₀ d₁ m)) {y : MvPolynomial (Var d₀ d₁ m) ℂ},
      y ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) →
      DL (DmixV Ls) l y ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
    intro l
    induction l with
    | nil => intro y hy; simpa using hy
    | cons p l ih => intro y hy; rw [DL_cons]; exact ih (Dhc_IG p.1 p.2 hy)
  exact IG_le_vanish E (this l hx)

end LSG.MEV
