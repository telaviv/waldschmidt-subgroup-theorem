import Mathlib
import LSG.MEV.SliceDim
import LSG.MEV.SliceIG
import LSG.MEV.TranslHF
import LSG.MEV.SubgroupCompV
import LSG.ME.WustCoset
import StrongSix.M2.Component

/-!
# Sliced cosets on `G̃`: good chart forms, dimension of sliced unions, the sliced coset count

Port of the slice parts of `LSG.ME.MainAbSlice` / `LSG.ME.MainAbAux` to the vector-extension model.

* `comp_mem_vanish`, `exists_homog`, `exists_homogVanish_ne`: `vanish E` is multihomogeneous in
  the `E^♮` blocks; points outside a Zariski-closed set are detected by multihomogeneous elements.
* **`exists_good_alpha`**: chart forms `ℓ_k = V_k + α_k W_k` with `ℓ_k ∉ I(a + V)` for finitely many
  translates (only finitely many values `α_k` are bad, one per point of `E_k`).
* `point_of_lsl_notMem`, `mem_vanishP_biUnion`, `vanishP_biUnion_eq_inf`.
* **`hdim_vanishP_cosets_le`**: `hdim (vanishP univ α (⋃_{a ∈ R} (a + V))) + m ≤ hdim I(V)`.
* **`hfun_sum_cosets_P`**:
  `Σ_{a ∈ R} H(vanishP univ α (a + V); t) ≤ H(vanishP univ α (⋃ (a + V)); t + c)`
  for distinct translates (multihomogeneous separators + `hfun_inter_ge`).
* **`hfun_P_transl_ge`** (per-coset sliced lower bound): an *unsliced* lower bound
  `L(t) · ∏_k (t D_k + 1) ≤ H(I(V); t)` (the shape of the subgroup layer's G4 bound, whose `m` extra
  `D₂`-exponents come from the free cone scalings) gives
  `L(t) ≤ 24^m H(vanishP univ α I(a + V); 3t)`;
  **`hfun_cosets_ge`**: summed over distinct translates. `hfun_P_coset_ge_H0`: the case `V = H⁰`.
* `exists_reps_GV`: distinct coset representatives.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)
open LSG.ME (Blk g2L g3L)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Multihomogeneous components of `vanish E` -/

/-- The grading by the `k`-th `E^♮` block. -/
def wEV (k : Fin m) : Var d₀ d₁ m → ℕ := fun v => wtV v k

theorem weight_wEV (k : Fin m) (s : Var d₀ d₁ m →₀ ℕ) :
    Finsupp.weight (wEV k) s = Finsupp.weight wtV s k := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wEV]

theorem isWeightedHomogeneous_wtV {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {n : Fin m → ℕ}
    (h : ∀ k, IsWeightedHomogeneous (wEV k) Q (n k)) : IsWeightedHomogeneous wtV Q n := by
  intro s hs
  funext k
  rw [← weight_wEV]; exact h k hs

/-- **`vanish E` is homogeneous in each `E^♮` block.** -/
theorem comp_mem_vanish {E : Set (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ vanish E) (k : Fin m) (n : ℕ) :
    weightedHomogeneousComponent (wEV k) n P ∈ vanish E := by
  classical
  refine mem_vanish.mpr fun g hg lam => ?_
  set x := coords g lam
  have hfin := weightedHomogeneousComponent_finsupp (w := wEV k) P
  set T := hfin.toFinset
  have hsum : P = ∑ i ∈ T, weightedHomogeneousComponent (wEV k) i P := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (wEV k) P]
    exact finsum_eq_sum _ hfin
  set f : Polynomial ℂ := ∑ i ∈ T,
    Polynomial.C (eval x (weightedHomogeneousComponent (wEV k) i P)) * Polynomial.X ^ i
  have hroot : ∀ t : ℂ, t ≠ 0 → f.eval t = 0 := by
    intro t ht
    have hs := mem_vanish.mp hP g hg (fun k' => (if k' = k then Units.mk0 t ht else 1) * lam k')
    rw [coords_mul, hsum, map_sum] at hs
    rw [← hs, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := wEV k) i P
    have := LSG.ME.eval_scale (κ := Unit) (fun v _ => wEV k v) (fun _ => t) x
      (Q := weightedHomogeneousComponent (wEV k) i P) (d := fun _ => i)
      (fun s hs' => funext fun _ => by
        rw [← hh hs', Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
          Finset.sum_apply]; rfl)
    simp only [Finset.univ_unique, Finset.prod_singleton] at this
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm,
      ← this]
    congr 2
    funext v
    congr 1
    simp only [wEV, apply_ite Units.val, Units.val_mk0, Units.val_one]
    rw [Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hf : f = 0 := Polynomial.eq_zero_of_infinite_isRoot f
    (Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) (fun t ht => hroot t ht)
      (Set.Finite.infinite_compl (Set.finite_singleton 0)))
  by_cases hn : n ∈ T
  · have := congrArg (Polynomial.coeff · n) hf
    simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single n (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd h (Ne.symm hb))
      (fun h => absurd hn h)] at this
    simpa using this
  · have : weightedHomogeneousComponent (wEV k) n P = 0 := by
      by_contra h
      exact hn (hfin.mem_toFinset.mpr h)
    rw [this, map_zero]

/-- **Multihomogeneous replacement.** -/
theorem exists_homog {E : Set (GPtV d₀ d₁ Ls)} {x : Var d₀ d₁ m → ℂ}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ vanish E) (hx : eval x P ≠ 0) :
    ∃ Q ∈ vanish E, eval x Q ≠ 0 ∧ ∃ d, IsWeightedHomogeneous wtV Q d := by
  classical
  suffices h : ∀ s : Finset (Fin m), ∃ Q ∈ vanish E, eval x Q ≠ 0 ∧
      ∀ k ∈ s, ∃ n, IsWeightedHomogeneous (wEV k) Q n by
    obtain ⟨Q, hQ, hxQ, hh⟩ := h Finset.univ
    choose n hn using fun k => hh k (Finset.mem_univ k)
    exact ⟨Q, hQ, hxQ, n, isWeightedHomogeneous_wtV hn⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨P, hP, hx, by simp⟩
  | insert k s _ ih =>
    obtain ⟨Q, hQ, hxQ, hh⟩ := ih
    have hfin := weightedHomogeneousComponent_finsupp (w := wEV k) Q
    have hsum : Q = ∑ i ∈ hfin.toFinset, weightedHomogeneousComponent (wEV k) i Q := by
      conv_lhs => rw [← finsum_weightedHomogeneousComponent (wEV k) Q]
      exact finsum_eq_sum _ hfin
    rw [hsum, map_sum] at hxQ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxQ
    refine ⟨_, comp_mem_vanish hQ k i, hi, fun k' hk' => ?_⟩
    rcases Finset.mem_insert.mp hk' with rfl | hk'
    · exact ⟨i, weightedHomogeneousComponent_isWeightedHomogeneous i Q⟩
    · obtain ⟨n, hn⟩ := hh k' hk'
      exact ⟨n, LSG.ME.isWeightedHomogeneous_comp hn i⟩

/-- A point outside a Zariski-closed set is detected by a multihomogeneous element of its
vanishing ideal, at every cone representative. -/
theorem exists_homogVanish_ne {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    {g : GPtV d₀ d₁ Ls} (hg : g ∉ V) :
    ∃ Q ∈ vanish V, (∃ d, IsWeightedHomogeneous wtV Q d) ∧ ∀ lam, eval (coords g lam) Q ≠ 0 := by
  rw [← zeros_vanish hV] at hg
  simp only [zeros, Set.mem_ofPred_eq, not_forall] at hg
  obtain ⟨P, hP, lam₀, hne⟩ := hg
  obtain ⟨Q, hQ, hxQ, d, hd⟩ := exists_homog hP hne
  exact ⟨Q, hQ, ⟨d, hd⟩, fun lam h => hxQ ((eval_coords_eq_zero_iff hd g _ _).mp h)⟩

/-! ### Choice of the chart forms -/

theorem repV_one_two (L : PeriodPair) (p : EVL L) :
    repV p 1 = rep p.base 1 ∧ repV p 2 = rep p.base 2 :=
  ⟨congrFun (Pe_repV p) 1, congrFun (Pe_repV p) 2⟩

/-- **Good chart forms** for finitely many translates of a nonempty set. -/
theorem exists_good_alpha {V : Set (GPtV d₀ d₁ Ls)} (hV : V.Nonempty)
    (R : Finset (GPtV d₀ d₁ Ls)) :
    ∃ α : Fin m → ℂ, ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V) := by
  classical
  obtain ⟨v, hv⟩ := hV
  let bad : Fin m → Finset ℂ := fun k =>
    R.image fun a => -(repV ((v + a).2.2 k) 1) / repV ((v + a).2.2 k) 2
  choose α hα using fun k => Infinite.exists_notMem_finset (bad k)
  refine ⟨α, fun a ha k hmem => ?_⟩
  have h0 := mem_vanish.mp hmem (v + a) ⟨v, hv, rfl⟩ 1
  rw [eval_coords_lsl] at h0
  simp only [Pi.one_apply, Units.val_one, one_mul, lval] at h0
  apply hα k
  refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
  obtain ⟨h1, h2⟩ := repV_one_two (Ls k) ((v + a).2.2 k)
  rw [h1, h2] at h0 ⊢
  generalize ((v + a).2.2 k).base = q at h0 ⊢
  cases q with
  | zero => simp [rep, O] at h0
  | some x y _ =>
    simp only [rep] at h0 ⊢
    simp at h0 ⊢
    linear_combination -h0

/-- A point with all `ℓ_k(repV) ≠ 0`. -/
theorem point_of_lsl_notMem {α : Fin m → ℂ} {E : Set (GPtV d₀ d₁ Ls)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E) :
    ∃ g ∈ E, ∀ k, lval α g k ≠ 0 := by
  classical
  have hprod := prod_lsl_notMem (s := Finset.univ) hp fun k _ => hℓ k
  by_contra hcon
  push Not at hcon
  apply hprod
  refine mem_vanish.mpr fun g hg lam => ?_
  obtain ⟨k, hk⟩ := hcon g hg
  rw [map_prod, Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_coords_lsl, hk, mul_zero])]

theorem mem_vanishP_biUnion {s : Finset (Fin m)} {α : Fin m → ℂ} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPtV d₀ d₁ Ls)) {P : MvPolynomial (Var d₀ d₁ m) ℂ} :
    P ∈ vanishP s α (⋃ a ∈ R, C a) ↔ ∀ a ∈ R, P ∈ vanishP s α (C a) := by
  simp only [mem_vanishP, Set.mem_iUnion]
  constructor
  · intro h a ha g hg hs lam; exact h g ⟨a, ha, hg⟩ hs lam
  · rintro h g ⟨a, ha, hg⟩ hs lam; exact h a ha g hg hs lam

theorem vanishP_biUnion_eq_inf {s : Finset (Fin m)} {α : Fin m → ℂ} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPtV d₀ d₁ Ls)) :
    vanishP s α (⋃ a ∈ R, C a) = R.inf fun a => vanishP s α (C a) := by
  ext P
  rw [mem_vanishP_biUnion]
  simp only [Finset.inf_eq_iInf, Submodule.mem_iInf]

/-! ### Sliced unions of cosets -/

/-- **Sliced unions of translates drop the dimension by `m`.** -/
theorem hdim_vanishP_cosets_le (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) {α : Fin m → ℂ}
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hne : vanishP Finset.univ α (⋃ a ∈ R, gtransl a V) ≠ ⊤) :
    (hdata blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V))).1 + m ≤
      (hdata blk D ℂ (vanish V)).1 := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top vanish_empty'
  obtain ⟨q, hq, hJq, hqdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  rw [vanishP_biUnion_eq_inf] at hJq hqdim
  obtain ⟨a, ha, haq⟩ := (Ideal.IsPrime.inf_le' (hp := hq)).mp hJq
  have hpa := vanish_gtransl_isPrime hV hp a
  obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa (hα a ha)
  have hdrop := hdim_vanishP_add_le D hD hpa (hα a ha) hg₀ hs₀ Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, hdim_vanish_gtransl D hVne a] at hdrop
  have hle := hdata_le_of_le blk D ℂ haq hq.ne_top
  rw [vanishP_biUnion_eq_inf]
  rcases hle with h | ⟨h, -⟩ <;> omega

/-- **The sliced coset sum** (S5). -/
theorem hfun_sum_cosets_P (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → ℂ)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) t ≤
      hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (t + c) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih (fun x hx k => hα x (Finset.mem_insert_of_mem hx) k)
      fun x hx y hy hxy =>
        hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hα' := hα a (Finset.mem_insert_self a s)
    have hpa := vanish_gtransl_isPrime hV hp a
    obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa hα'
    have hPa := vanishP_isPrime (s := Finset.univ) hpa (fun k _ => hα' k) hg₀ (fun k _ => hs₀ k)
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanishP Finset.univ α (gtransl a V) := by
      intro b hb
      have hns := hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
      obtain ⟨x, hxa, hxb⟩ := Set.not_subset.mp hns
      obtain ⟨Q, hQb, ⟨d, hd⟩, hQx⟩ := exists_homogVanish_ne (isZClosed_gtransl hV b) hxb
      refine ⟨Q, hQb, fun hQa => ?_⟩
      have := hom_mem_vanish_of_mem_vanishP hpa hα' hd hQa
      exact hQx 1 (mem_vanish.mp this x hxa 1)
    choose! f hfb hfa using hsep
    set B := ∏ b ∈ s, f b
    have hBs : B ∈ vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) := by
      rw [mem_vanishP_biUnion]
      intro b hb
      rw [show B = f b * ∏ x ∈ s.erase b, f x from (Finset.mul_prod_erase s f hb).symm]
      exact Ideal.mul_mem_right _ _ (vanish_le_vanishP _ α _ (hfb b hb))
    have hBa : B ∉ vanishP Finset.univ α (gtransl a V) := by
      intro h
      obtain ⟨b, hb, hfb'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPa)).mp h
      exact hfa b hb hfb'
    have hnzd : ∀ x, B * x ∈ vanishP Finset.univ α (gtransl a V) →
        x ∈ vanishP Finset.univ α (gtransl a V) := fun x hx =>
      (hPa.mem_or_mem hx).resolve_left hBa
    have hBdeg := StrongSix.M2.mem_FLE_totalDegree blk D ℂ hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : vanishP Finset.univ α (⋃ x ∈ insert a s, gtransl x V) =
        vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) ⊓ vanishP Finset.univ α (gtransl a V) := by
      ext P
      simp only [Submodule.mem_inf, mem_vanishP_biUnion, Finset.forall_mem_insert]
      exact and_comm
    have h1 := LSG.ME.hfun_inter_ge blk D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, Finset.sum_insert ha]
    have := hc t
    omega

/-! ### The sliced lower bound for a translate, and the sliced coset count -/

theorem prod_three_le (D : Blk m → ℕ) (t : ℕ) :
    ∏ k : Fin m, (3 * t * D (.e k) + 1) ≤ 3 ^ m * ∏ k : Fin m, (t * D (.e k) + 1) := by
  calc ∏ k : Fin m, (3 * t * D (.e k) + 1) ≤ ∏ k : Fin m, (3 * (t * D (.e k) + 1)) :=
        Finset.prod_le_prod fun k _ => by nlinarith
    _ = 3 ^ m * ∏ k : Fin m, (t * D (.e k) + 1) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The sliced lower bound for a translate.** An unsliced lower bound
`L(t) · ∏_k (t D_k + 1) ≤ H(I(V); t)` gives `L(t) ≤ 24^m · H(vanishP univ α I(a + V); 3t)`. -/
theorem hfun_P_transl_ge (D : Blk m → ℕ) {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (a : GPtV d₀ d₁ Ls) (α : Fin m → ℂ)
    (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a V)) (L : ℕ → ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ hfun blk D ℂ (vanish V) t) (t : ℕ) :
    L t ≤ 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
  have hpa := vanish_gtransl_isPrime hV hp a
  have h2 := hfun_le_transl D V a t
  have h3 := hfun_le_of_hom α hpa hℓ _ (fun _ _ hQ hs => hom_mem_vanish_of_mem_vanishP hpa hℓ hQ hs)
    D (3 * t)
  set P := ∏ k : Fin m, (t * D (.e k) + 1)
  set hP := hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t)
  have hP0 : 0 < P := Finset.prod_pos fun k _ => Nat.succ_pos _
  have h4 := prod_three_le D t
  have hchain : L t * P ≤ 24 ^ m * hP * P := by
    calc L t * P ≤ hfun blk D ℂ (vanish V) t := hL t
      _ ≤ 8 ^ m * hfun blk D ℂ (vanish (gtransl a V)) (3 * t) := h2
      _ ≤ 8 ^ m * ((∏ k : Fin m, (3 * t * D (.e k) + 1)) * hP) := Nat.mul_le_mul_left _ h3
      _ ≤ 8 ^ m * ((3 ^ m * P) * hP) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
      _ = 24 ^ m * hP * P := by
          rw [show (24 : ℕ) ^ m = 8 ^ m * 3 ^ m by rw [← mul_pow]; norm_num]; ring
  exact Nat.le_of_mul_le_mul_right hchain hP0

/-- **The sliced coset count**: for distinct translates `a + V` (`a ∈ R`) with good chart forms,
`|R| · L(t) ≤ 24^m · H(vanishP univ α I(⋃_{a ∈ R} (a + V)); 3t + c)`. -/
theorem hfun_cosets_ge (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → ℂ)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) (L : ℕ → ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ hfun blk D ℂ (vanish V) t) :
    ∃ c : ℕ, ∀ t, R.card * L t ≤
      24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (3 * t + c) := by
  obtain ⟨c, hc⟩ := hfun_sum_cosets_P D hD α hV hp R hα hdist
  refine ⟨c, fun t => ?_⟩
  calc R.card * L t = ∑ _a ∈ R, L t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ R, 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) :=
        Finset.sum_le_sum fun a ha => hfun_P_transl_ge D hV hp a α (hα a ha) L hL t
    _ = 24 ^ m * ∑ a ∈ R, hfun blk D ℂ (vanishP Finset.univ α (gtransl a V)) (3 * t) := by
        rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (hc (3 * t))

/-- The case `V = H⁰` of `hfun_P_transl_ge`; the hypothesis `hL` is the subgroup layer's Hilbert
lower bound (gap G4 of STAGE5_MEV §6.4, with `L` of degree `t₀ + t₁ + t₂`). -/
theorem hfun_P_coset_ge_H0 {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (D : Blk m → ℕ)
    (a : GPtV d₀ d₁ Ls) (α : Fin m → ℂ) (hℓ : ∀ k, lsl α k ∉ vanish (gtransl a (H0 Ls hH)))
    (L : ℕ → ℕ)
    (hL : ∀ t, L t * ∏ k : Fin m, (t * D (.e k) + 1) ≤ hfun blk D ℂ (vanish (H0 Ls hH)) t)
    (t : ℕ) :
    L t ≤ 24 ^ m * hfun blk D ℂ (vanishP Finset.univ α (gtransl a (H0 Ls hH))) (3 * t) :=
  hfun_P_transl_ge D (isZClosed_H0 hH) (vanish_H0_isPrime hH) a α hℓ L hL t

/-! ### Distinct coset representatives -/

theorem gtransl_eq_of_sub_memV {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H)
    {a b : GPtV d₀ d₁ Ls} (h : a - b ∈ H) : gtransl a H = gtransl b H := by
  ext x
  rw [mem_gtransl, mem_gtransl]
  constructor
  · intro hx
    have := hH.add_mem _ hx _ h
    rwa [show x - a + (a - b) = x - b by abel] at this
  · intro hx
    have := hH.add_mem _ hx _ (hH.neg_mem _ h)
    rwa [show x - b + -(a - b) = x - a by abel] at this

/-- **Distinct coset representatives.** -/
theorem exists_reps_GV {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H)
    (T' : Finset (GPtV d₀ d₁ Ls)) :
    ∃ Rs ⊆ T', (⋃ a ∈ Rs, gtransl a H) = (⋃ a ∈ T', gtransl a H) ∧
      ∀ a ∈ Rs, ∀ b ∈ Rs, a ≠ b → a - b ∉ H := by
  classical
  induction T' using Finset.induction_on with
  | empty => exact ⟨∅, subset_refl _, by simp, by simp⟩
  | insert t T' ht ih =>
    obtain ⟨Rs, hsub, hU, hd⟩ := ih
    by_cases hc : ∃ a ∈ Rs, t - a ∈ H
    · obtain ⟨a, ha, hat⟩ := hc
      refine ⟨Rs, hsub.trans (Finset.subset_insert _ _), ?_, hd⟩
      rw [Finset.set_biUnion_insert, ← hU, gtransl_eq_of_sub_memV hH hat]
      exact (Set.union_eq_right.mpr
        (Set.subset_iUnion₂ (s := fun a (_ : a ∈ Rs) => gtransl a H) a ha)).symm
    · push Not at hc
      refine ⟨insert t Rs, Finset.insert_subset_insert _ hsub, ?_, ?_⟩
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert, hU]
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · exact absurd rfl hab
          · exact hc b hb'
        · rcases Finset.mem_insert.mp hb with rfl | hb'
          · intro hmem
            apply hc a ha'
            have := hH.neg_mem _ hmem
            rwa [neg_sub] at this
          · exact hd a ha' b hb' hab

/-- Distinct representatives give pairwise non-nested cosets of a subgroup. -/
theorem not_gtransl_subset_of_sub_notMem {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H)
    {a b : GPtV d₀ d₁ Ls} (h : a - b ∉ H) : ¬ gtransl a H ⊆ gtransl b H := by
  intro hsub
  have ha : a ∈ gtransl a H := mem_gtransl.mpr (by simpa using hH.zero_mem)
  exact h (mem_gtransl.mp (hsub ha))

end LSG.MEV
