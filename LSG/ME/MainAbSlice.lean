import Mathlib
import LSG.ME.SliceDim
import LSG.ME.MainAbChain

/-!
# Sliced pieces of the assembly (STAGE2 §11, S5 and parts of S6)

* `ordGt_of_eval_phOp`: Philippon's generators vanishing at **one** cone representative of `h`
  already give formal order `> k` at `h + g` (the `(→)` half of `zeros_phOp`, any scaling).
* **`Zs_subset_transl`**: the normalised zeros of Roy's ideal `A₂` satisfy `h + V ⊆ Z(L_r)`.
* **`exists_good_alpha`**: chart forms `ℓ_k = V_k + α_k W_k` avoiding finitely many translates
  `a + V` (`ℓ_k ∉ I(a + V)`).
* `mem_vanishP_biUnion`, `point_of_lsl_notMem`.
* **`hdim_vanishP_cosets_le`**: `hdim (vanishP univ (⋃_{c ∈ R} (c + V))) + m ≤ hdim I(V)`.
* **`hfun_sum_cosets_P`** (S5):
  `Σ_{a ∈ R} H(vanishP univ (a + V); t) ≤ H(vanishP univ (⋃ (a + V)); t + c)`
  for distinct cosets (multihomogeneous separators, `hfun_inter_ge`).
-/

open MvPolynomial LSG.Elliptic Module
open StrongSix.M2 (FLE hfun hdata hdata_le_of_le)

namespace LSG.ME

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Normalised zeros of Roy's ideal -/

section Roy

variable [DecidableEq K] [CharZero K] (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include hΔ

/-- Generators vanishing at one cone representative give formal order. -/
theorem ordGt_of_eval_phOp (W : Submodule K (LieE K d₀ d₁ m)) {Q : MvPolynomial (Var d₀ d₁ m) K}
    {d : Fin m → ℕ} (hQ : IsHomE Q d) (g h : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (k : ℕ)
    (hz : ∀ w ∈ W, ∀ κ ≤ k, ∀ c c', eval (coords h lam) (phOp g₂ g₃ g w c c' κ Q) = 0) :
    OrdGt g₂ g₃ W Q k (h + g) := by
  intro w hw
  obtain ⟨c, hc⟩ := exists_good two_ne_zero hΔ h g
  obtain ⟨c', hc'⟩ := exists_good two_ne_zero hΔ g 0
  have hu : IsUnit (∏ k, lawPt g₂ g₃ h lam g w c c' (.e k (chartAt (h + g) k)) ^ d k) :=
    IsUnit.prod_univ_iff.mpr fun k => (lawPt_unit hΔ h lam g w hc hc' k).pow _
  refine LowZero.of_unit hu ?_
  intro i hi
  rw [← aeval_lawPt hΔ hQ, ← eval_phOp_coords]
  exact hz w hw i hi c c'

/-- **Normalised zeros of `A₂`.** -/
theorem Zs_subset_transl (α : Fin m → K) (W : Submodule K (LieE K d₀ d₁ m))
    (S : Finset (GPt K d₀ d₁ g₂ g₃)) {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hP : IsHomE P d) (T r : ℕ) (V : Set (GPt K d₀ d₁ g₂ g₃)) :
    Zs (g₂ := g₂) (g₃ := g₃) α (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span {Q' | ∃ Q ∈
      gensR2 g₂ g₃ W S P T r, ∃ v ∈ V, ∃ c, Q' = τ g₂ g₃ v c Q}) ⊆
      {h | gtransl h V ⊆ zeros (Lr2 g₂ g₃ W S P T r : Set _)} := by
  intro h hh
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨c, hc⟩ := exists_good two_ne_zero hΔ h v
  obtain ⟨μ, hμ⟩ := eval_transl_good two_ne_zero hΔ hc
  obtain ⟨lam₀, hn⟩ : ∃ lam₀, nrm α h = coords h lam₀ := ⟨_, rfl⟩
  have hgen : ∀ Q ∈ gensR2 g₂ g₃ W S P T r,
      eval (coords (h + v) fun k => lam₀ k ^ 2 * μ k) Q = 0 := by
    intro Q hQ
    rw [← hμ, ← hn]
    exact hh.2 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨Q, hQ, v, hv, c, rfl⟩))
  change v + h ∈ zeros (Lr2 g₂ g₃ W S P T r : Set _)
  rw [add_comm, mem_zeros_iff_le_vanish]
  refine sup_le (IG_le_vanish two_ne_zero _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c₁, c₂, rfl⟩
  have hord := ordGt_of_eval_phOp hΔ W hP σ (h + v) _ (r * T)
    (fun w hw κ hκ c c' => hgen _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩)
  have hz := (zeros_phOp hΔ W (Qs := {P}) (fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩)
    σ (h + v) (r * T)).mpr (fun Q hQ => by rw [Set.mem_singleton_iff.mp hQ]; exact hord)
  rw [mem_zeros_iff_le_vanish] at hz
  exact hz (Ideal.mem_sup_right (Ideal.subset_span ⟨P, rfl, w, hw, κ, hκ, c₁, c₂, rfl⟩))

end Roy

/-! ### Choice of the chart forms -/

/-- **Good chart forms** for finitely many translates of a nonempty set. -/
theorem exists_good_alpha [DecidableEq K] [Infinite K] {V : Set (GPt K d₀ d₁ g₂ g₃)}
    (hV : V.Nonempty)
    (R : Finset (GPt K d₀ d₁ g₂ g₃)) :
    ∃ α : Fin m → K, ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V) := by
  classical
  obtain ⟨v, hv⟩ := hV
  let bad : Fin m → Finset K := fun k =>
    R.image fun a => -(rep ((v + a).2.2 k) 1) / rep ((v + a).2.2 k) 2
  choose α hα using fun k => Infinite.exists_notMem_finset (bad k)
  refine ⟨α, fun a ha k hmem => ?_⟩
  have h0 := mem_vanish.mp hmem (v + a) ⟨v, hv, rfl⟩ 1
  rw [eval_coords_lsl] at h0
  simp only [Pi.one_apply, Units.val_one, one_mul, lval] at h0
  apply hα k
  refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
  generalize (v + a).2.2 k = q at h0 ⊢
  cases q with
  | zero => simp [rep, O] at h0
  | some x y _ =>
    simp only [rep] at h0 ⊢
    simp at h0 ⊢
    linear_combination -h0

/-- A point with all `ℓ_k(rep) ≠ 0`. -/
theorem point_of_lsl_notMem {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
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

theorem mem_vanishP_biUnion {s : Finset (Fin m)} {α : Fin m → K} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPt K d₀ d₁ g₂ g₃)) {P : MvPolynomial (Var d₀ d₁ m) K} :
    P ∈ vanishP s α (⋃ a ∈ R, C a) ↔ ∀ a ∈ R, P ∈ vanishP s α (C a) := by
  simp only [mem_vanishP, Set.mem_iUnion]
  constructor
  · intro h a ha g hg hs lam; exact h g ⟨a, ha, hg⟩ hs lam
  · rintro h g ⟨a, ha, hg⟩ hs lam; exact h a ha g hg hs lam

theorem vanishP_biUnion_eq_inf {s : Finset (Fin m)} {α : Fin m → K} {ι : Type*} (R : Finset ι)
    (C : ι → Set (GPt K d₀ d₁ g₂ g₃)) :
    vanishP s α (⋃ a ∈ R, C a) = R.inf fun a => vanishP s α (C a) := by
  ext P
  rw [mem_vanishP_biUnion]
  simp only [Finset.inf_eq_iInf, Submodule.mem_iInf]

/-! ### Dimension of sliced unions of cosets -/

section Cosets

variable [DecidableEq K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Sliced unions of translates drop the dimension by `m`.** -/
theorem hdim_vanishP_cosets_le (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) {α : Fin m → K}
    {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt K d₀ d₁ g₂ g₃)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hne : vanishP Finset.univ α (⋃ a ∈ R, gtransl a V) ≠ ⊤) :
    (hdata blk D K (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V))).1 + m ≤
      (hdata blk D K (vanish V)).1 := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top (vanish_empty' (g₂ := g₂) (g₃ := g₃) (d₀ := d₀) (d₁ := d₁))
  obtain ⟨q, hq, hJq, hqdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  rw [vanishP_biUnion_eq_inf] at hJq hqdim
  obtain ⟨a, ha, haq⟩ := (Ideal.IsPrime.inf_le' (hp := hq)).mp hJq
  have hpa := vanish_gtransl_isPrime h2 hΔ hV hp a
  obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa (hα a ha)
  have hdrop := hdim_vanishP_add_le h2 D hD hpa (hα a ha) hg₀ hs₀ Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, hdim_vanish_gtransl h2 hΔ D hVne a] at hdrop
  have hle := hdata_le_of_le blk D K haq hq.ne_top
  rw [vanishP_biUnion_eq_inf]
  rcases hle with h | ⟨h, -⟩ <;> omega

/-- **The sliced coset count** (S5). -/
theorem hfun_sum_cosets_P (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) (α : Fin m → K)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt K d₀ d₁ g₂ g₃)) (hα : ∀ a ∈ R, ∀ k, lsl α k ∉ vanish (gtransl a V))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun blk D K (vanishP Finset.univ α (gtransl a V)) t ≤
      hfun blk D K (vanishP Finset.univ α (⋃ a ∈ R, gtransl a V)) (t + c) := by
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
    have hpa := vanish_gtransl_isPrime h2 hΔ hV hp a
    obtain ⟨g₀, hg₀, hs₀⟩ := point_of_lsl_notMem hpa hα'
    have hPa := vanishP_isPrime (s := Finset.univ) hpa (fun k _ => hα' k) hg₀ (fun k _ => hs₀ k)
    -- multihomogeneous separators
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanishP Finset.univ α (gtransl a V) := by
      intro b hb
      have hns := hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
      obtain ⟨x, hxa, hxb⟩ := Set.not_subset.mp hns
      obtain ⟨Q, ⟨hQb, d, hd⟩, hQx⟩ := exists_homogVanish_ne (isZClosed_gtransl h2 hΔ hV b) hxb
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
    have hBdeg := StrongSix.M2.mem_FLE_totalDegree blk D K hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : vanishP Finset.univ α (⋃ x ∈ insert a s, gtransl x V) =
        vanishP Finset.univ α (⋃ b ∈ s, gtransl b V) ⊓ vanishP Finset.univ α (gtransl a V) := by
      ext P
      simp only [Submodule.mem_inf, mem_vanishP_biUnion, Finset.forall_mem_insert]
      exact and_comm
    have h1 := hfun_inter_ge blk D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, Finset.sum_insert ha]
    have := hc t
    omega

end Cosets

end LSG.ME
