import Mathlib
import LSG.MEV.SubgroupTangentV
import LSG.ME.SmoothPoint
import LSG.ME.DimTrdeg
import LSG.ME.SubgroupTanSp

/-!
# The identity component `H⁰` of a closed subgroup of `G̃` and its dimension (gap G3)

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)` with Lie algebra `T′ = lieAlg H`:
* **`H0 = zcl (exp T′)`**: a Zariski-closed subgroup, `H0 ⊆ H`, `lieAlg H0 = T′` (`lieAlg_H0`).
* **`vanish_H0_isPrime`**: along every complex line in `T′ × ℂ^m` the functions
  `c ↦ P(liftV(t₀ + c t, μ₀ + c μ))` are entire, so `PQ ∈ vanish H0` forces `P` or `Q` to vanish.
* **`finrank_tangentSpace_zero_le`**: at the identity `a₀ = FV 0`, `dim T_{a₀} ≤ dim T′ + m`
  (a tangent vector is `D̂_w(a₀) + Σ s_k·(block k of a₀)` with `w ∈ TZ H⁰ = T′`).
* **`le_finrank_tangentSpace`**: at a cone point `a` of `H⁰` with all `V_k ≠ 0`,
  `dim T′ + m ≤ dim T_a` (the vectors `r · D̂_w(FV p)`, `w ∈ T′`, and the block scalings).
* **`trdeg_H0`**: `trdeg_ℂ (ℂ[Var]/vanish H⁰) = dim T′ + m` (upper bound at `a₀`, lower bound at a
  smooth point with `∏ V_k ≠ 0`), and **`hdim_H0`**: StrongSix's Hilbert dimension of `vanish H⁰`
  is `dim T′ + m` (the cone shift: one scaling per `E^♮` block).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set Module
open LSG.AuxV (ellN)
open LSG.Aux (ellW)
open LSG.ME (tangentSpace)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem differentiable_eval_of {σ : Type*} {Y : ℂ → σ → ℂ} (hY : ∀ v, Differentiable ℂ fun c => Y c v)
    (P : MvPolynomial σ ℂ) : Differentiable ℂ fun c => eval (Y c) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p v hp => simp only [map_mul, eval_X]; exact hp.mul (hY v)

theorem mem_zeroLocus_iff {I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {x : Var d₀ d₁ m → ℂ} :
    x ∈ zeroLocus ℂ I ↔ ∀ f ∈ I, eval x f = 0 := by
  simp [zeroLocus]

theorem line_mem {E : Type*} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E) {a b : E}
    (ha : a ∈ V) (hb : b ∈ V) (c : ℂ) : a + c • (b - a) ∈ V :=
  V.add_mem ha (V.smul_mem c (V.sub_mem hb ha))

/-! ### `H⁰` -/

section H0

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)

variable (Ls) in
/-- **The identity component** `H⁰ = zcl (exp T′)`. -/
def H0 : Set (GPtV d₀ d₁ Ls) := zcl (expGV Ls '' (lieAlg Ls hH : Set (TanG d₀ d₁ m)))

theorem expGV_image_isSubgroup (V : Submodule ℂ (TanG d₀ d₁ m)) :
    IsSubgroupG (expGV Ls '' (V : Set (TanG d₀ d₁ m))) where
  zero_mem := ⟨0, V.zero_mem, expGV_zero Ls⟩
  add_mem := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, V.add_mem ha hb, expGV_add Ls a b⟩
  neg_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, V.neg_mem ha, (expGVHom Ls).map_neg a⟩

theorem H0_isSubgroup : IsSubgroupG (H0 Ls hH) := zcl_isSubgroup (expGV_image_isSubgroup _)

theorem isZClosed_H0 : IsZClosed (H0 Ls hH) := isZClosed_zcl _

theorem expGV_mem_H0 {t : TanG d₀ d₁ m} (ht : t ∈ lieAlg Ls hH) : expGV Ls t ∈ H0 Ls hH :=
  subset_zcl _ ⟨t, ht, rfl⟩

include hc in
theorem H0_subset : H0 Ls hH ⊆ H :=
  zcl_minimal hc fun _ ⟨t, ht, e⟩ => e ▸ lieAlg_le_Htil ht

include hc in
/-- **`lieAlg H⁰ = lieAlg H`.** -/
theorem lieAlg_H0 : lieAlg Ls (H0_isSubgroup hH) = lieAlg Ls hH := by
  ext v
  constructor
  · intro hv c; exact H0_subset hH hc (hv c)
  · intro hv c; exact expGV_mem_H0 hH ((lieAlg Ls hH).smul_mem c hv)

/-- Membership in `vanish H⁰` via the global lift. -/
theorem mem_vanish_H0_iff {P : MvPolynomial (Var d₀ d₁ m) ℂ} :
    P ∈ vanish (H0 Ls hH) ↔ ∀ t ∈ lieAlg Ls hH, ∀ μ : Fin m → ℂ, eval (liftV Ls t μ) P = 0 := by
  rw [H0, vanish_zcl]
  constructor
  · intro hP t ht μ
    obtain ⟨c, hc'⟩ := liftV_eq Ls t
    rw [hc']
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ ⟨t, ht, rfl⟩ lam) _
  · intro h
    refine mem_vanish.mpr ?_
    rintro _ ⟨t, ht, rfl⟩ lam
    obtain ⟨c, hc'⟩ := liftV_eq Ls t
    have := h t ht fun k => lam k / c k
    rw [hc'] at this
    have e : coords (expGV Ls t) lam =
        coordsZ (expGV Ls t) fun k => (lam k : ℂ) / c k * c k := by
      funext v
      cases v with
      | x i => rfl
      | y j => rfl
      | z j => rfl
      | e k i => simp [coords, div_mul_cancel₀ _ (c k).ne_zero]
    rw [e]; exact this

/-- **`vanish H⁰` is prime.** -/
theorem vanish_H0_isPrime : (vanish (H0 Ls hH)).IsPrime := by
  refine ⟨vanish_ne_top ⟨0, subset_zcl _ ⟨0, Submodule.zero_mem _, expGV_zero Ls⟩⟩, ?_⟩
  intro P Q hPQ
  by_contra hcon
  push Not at hcon
  obtain ⟨hP, hQ⟩ := hcon
  rw [mem_vanish_H0_iff] at hP hQ hPQ
  push Not at hP hQ
  obtain ⟨t₀, ht₀, μ₀, h₀⟩ := hP
  obtain ⟨t₁, ht₁, μ₁, h₁⟩ := hQ
  -- the line through `(t₀, μ₀)` and `(t₁, μ₁)`
  let Y : ℂ → Var d₀ d₁ m → ℂ := fun c => liftV Ls (t₀ + c • (t₁ - t₀)) (μ₀ + c • (μ₁ - μ₀))
  have hY : ∀ v, Differentiable ℂ fun c => Y c v := by
    intro v
    cases v with
    | x i => show Differentiable ℂ fun c : ℂ => (t₀ + c • (t₁ - t₀)).1 i; fun_prop
    | y j => show Differentiable ℂ fun c : ℂ => Complex.exp ((t₀ + c • (t₁ - t₀)).2.1 j); fun_prop
    | z j => show Differentiable ℂ fun c : ℂ => Complex.exp (-(t₀ + c • (t₁ - t₀)).2.1 j); fun_prop
    | e k i =>
      show Differentiable ℂ fun c : ℂ => (μ₀ + c • (μ₁ - μ₀)) k *
        ellN (Ls k) ((t₀ + c • (t₁ - t₀)).2.2.1 k) ((t₀ + c • (t₁ - t₀)).2.2.2 k) i
      have h1 : Differentiable ℂ fun c : ℂ =>
          ((t₀ + c • (t₁ - t₀)).2.2.1 k, (t₀ + c • (t₁ - t₀)).2.2.2 k) := by fun_prop
      have h2 := (LSG.AuxV.differentiable_ellN (Ls k) i).comp h1
      simp only [Function.comp_def] at h2
      exact (by fun_prop : Differentiable ℂ fun c : ℂ => (μ₀ + c • (μ₁ - μ₀)) k).mul h2
  have hmem : ∀ c : ℂ, t₀ + c • (t₁ - t₀) ∈ lieAlg Ls hH := fun c => line_mem _ ht₀ ht₁ c
  let fP : ℂ → ℂ := fun c => eval (Y c) P
  let fQ : ℂ → ℂ := fun c => eval (Y c) Q
  have hprod : ∀ c, fP c * fQ c = 0 := fun c => by
    have := hPQ _ (hmem c) (μ₀ + c • (μ₁ - μ₀)); rw [map_mul] at this; exact this
  have hanQ : AnalyticOnNhd ℂ fQ univ := fun c _ => (differentiable_eval_of hY Q).analyticAt c
  have hP0 : fP 0 ≠ 0 := by
    show eval (liftV Ls (t₀ + (0 : ℂ) • (t₁ - t₀)) (μ₀ + (0 : ℂ) • (μ₁ - μ₀))) P ≠ 0
    rw [zero_smul, zero_smul, add_zero, add_zero]; exact h₀
  have hcont : ContinuousAt fP 0 := (differentiable_eval_of hY P).continuous.continuousAt
  have hev : fQ =ᶠ[𝓝 0] 0 := by
    filter_upwards [hcont.eventually_ne hP0] with c hc'
    exact (mul_eq_zero.mp (hprod c)).resolve_left hc'
  have := hanQ.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 0)
    hev (mem_univ 1)
  apply h₁
  have e : eval (liftV Ls (t₀ + (1 : ℂ) • (t₁ - t₀)) (μ₀ + (1 : ℂ) • (μ₁ - μ₀))) Q = 0 := this
  rwa [one_smul, one_smul, add_sub_cancel, add_sub_cancel] at e

end H0

/-! ### The identity point -/

theorem FVb_zero (L : PeriodPair) : FVb L 0 0 = ptO 0 := by
  have h := LSG.AuxV.ellN_at_zero L 0
  have h2 : ellW L 2 0 = -2 := by
    have := congrFun h 1; rw [LSG.AuxV.ellN_one] at this; simpa [ptO] using this
  rw [FVb, h, h2, smul_smul]; norm_num

theorem a0_x (i : Fin d₀) : FV Ls (0 : TanG d₀ d₁ m) (.x i) = 0 := rfl
theorem a0_y (j : Fin d₁) : FV Ls (0 : TanG d₀ d₁ m) (.y j) = 1 := by simp [FV, liftV]
theorem a0_z (j : Fin d₁) : FV Ls (0 : TanG d₀ d₁ m) (.z j) = 1 := by simp [FV, liftV]
theorem a0_e (k : Fin m) (c : Fin 5) : FV Ls (0 : TanG d₀ d₁ m) (.e k c) = ptO 0 c := by
  rw [FV_e]; exact congrFun (FVb_zero (Ls k)) c

/-- The tangent pairing as a derivation. -/
def dirDer (v : Var d₀ d₁ m → ℂ) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  mkDerivation ℂ fun i => C (v i)

theorem eval_dirDer (v a : Var d₀ d₁ m → ℂ) (f : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval a (dirDer v f) = ∑ i, v i * eval a (pderiv i f) := by
  classical
  rw [dirDer, mkDerivation_eq_sum, map_sum]
  simp

section Tan

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)

/-- The coordinates `(w, s)` of a tangent vector at the identity. -/
def tanCoord (v : Var d₀ d₁ m → ℂ) : TanG d₀ d₁ m × (Fin m → ℂ) :=
  ((fun i => v (.x i), fun j => v (.y j), fun k => -2 * v (.e k 0), fun k => v (.e k 4)),
    fun k => v (.e k 1))

theorem tanCoord_linear : IsLinearMap ℂ (tanCoord (d₀ := d₀) (d₁ := d₁) (m := m)) := by
  constructor
  · intro v v'; simp only [tanCoord]; ext <;> simp; ring
  · intro c v; simp only [tanCoord]; ext <;> simp; ring

include hc in
/-- **Upper bound at the identity**: `dim T_{a₀} ≤ dim T′ + m`. -/
theorem finrank_tangentSpace_zero_le :
    finrank ℂ (tangentSpace (vanish (H0 Ls hH)) (FV Ls 0)) ≤ finrank ℂ (lieAlg Ls hH) + m := by
  classical
  set T := tangentSpace (vanish (H0 Ls hH)) (FV Ls (0 : TanG d₀ d₁ m))
  have hH0 := H0_isSubgroup hH
  have hc0 := isZClosed_H0 (Ls := Ls) hH
  obtain ⟨ν, hν⟩ := FV_eq_coords (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
  have h0H : expGV Ls 0 ∈ H0 Ls hH := by rw [expGV_zero]; exact hH0.zero_mem
  -- the tangent conditions from `I_G̃`
  have htan : ∀ v ∈ T, ∀ f ∈ vanish (H0 Ls hH), eval (FV Ls 0) (dirDer v f) = 0 := by
    intro v hv f hf; rw [eval_dirDer]; exact hv f hf
  have hYZ : ∀ j, YZ ℂ d₀ m j ∈ vanish (H0 Ls hH) := fun j =>
    mem_vanish.mpr fun g _ lam => by simp [YZ, coords]
  have hFk : ∀ k, Fk (LSG.ME.g2L Ls) (LSG.ME.g3L Ls) d₀ d₁ k ∈ vanish (H0 Ls hH) := fun k =>
    mem_vanish.mpr fun g _ lam => eval_coords_Fk g _ k
  have hGk : ∀ k, Gk ℂ d₀ d₁ k ∈ vanish (H0 Ls hH) := fun k =>
    mem_vanish.mpr fun g _ lam => eval_coords_Gk g _ k
  -- reconstruction
  have hrec : ∀ v ∈ T, v = fun i => DV Ls (tanCoord v).1 (FV Ls 0) i +
      ∑ k, (tanCoord v).2 k * blockPart k (FV Ls 0) i := by
    intro v hv
    funext i
    rw [DV_of_V Ls (FV_V goodV_zero)]
    cases i with
    | x i => simp [dvalE, tanCoord, blockPart]
    | y j => simp [dvalE, tanCoord, blockPart, a0_y]
    | z j =>
      have := htan v hv _ (hYZ j)
      simp [YZ, dirDer, Derivation.leibniz, a0_y, a0_z] at this
      simp [dvalE, tanCoord, blockPart, a0_z]
      linear_combination this
    | e k c =>
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [blockPart, Ne.symm hb]) (by simp)]
      simp only [blockPart, ite_true, dvalE, a0_e, tanCoord]
      have hF := htan v hv _ (hFk k)
      have hG := htan v hv _ (hGk k)
      simp [Fk, F, Gk, Gfib, dirDer, Derivation.leibniz, Derivation.leibniz_pow, a0_e, ptO]
        at hF hG
      fin_cases c <;> simp [bField, ptO, hF, hG] <;> ring
  -- the image lies in `TZ H⁰ × ℂ^m`
  have himg : ∀ v ∈ T, (tanCoord v).1 ∈ lieAlg Ls hH := by
    intro v hv
    rw [← lieAlg_H0 hH hc, ← TZ_eq_lieAlg hH0 hc0]
    intro Q hQ
    have h := hv Q hQ
    rw [hrec v hv] at h
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    have heul : ∀ k ∈ Finset.univ, ∑ i, (tanCoord v).2 k * blockPart k (FV Ls 0) i *
        eval (FV Ls 0) (pderiv i Q) = 0 := fun k _ => by
      have := euler_eq_zero hQ h0H ν k
      rw [← hν] at this
      simp only [mul_assoc, mul_comm (blockPart k (FV Ls 0) _), ← Finset.mul_sum, this, mul_zero]
    rw [Finset.sum_eq_zero heul, add_zero] at h
    rw [eval_Dh]
    simpa [mul_comm] using h
  -- the injective linear map
  let Φ : T →ₗ[ℂ] lieAlg Ls hH × (Fin m → ℂ) :=
    { toFun := fun v => (⟨(tanCoord v.1).1, himg v.1 v.2⟩, (tanCoord v.1).2)
      map_add' := fun v v' => by
        ext <;> simp [tanCoord_linear.map_add]
      map_smul' := fun c v => by
        ext <;> simp [tanCoord_linear.map_smul] }
  have hinj : Function.Injective Φ := by
    intro v v' h
    have h1 : tanCoord v.1 = tanCoord v'.1 := by
      have e1 := congrArg (fun x => (x.1 : TanG d₀ d₁ m)) h
      have e2 := congrArg Prod.snd h
      exact Prod.ext e1 e2
    exact Subtype.ext (by rw [hrec v.1 v.2, hrec v'.1 v'.2, h1])
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun] at this

omit hH in
theorem Fn_smul (g₂ g₃ c : ℂ) (P : Fin 5 → ℂ) : Fn g₂ g₃ (c • P) = c ^ 3 * Fn g₂ g₃ P := by
  simp [Fn, F]; ring

include hc in
/-- **Lower bound at a cone point of `H⁰` with all `V_k ≠ 0`.** -/
theorem le_finrank_tangentSpace {a : Var d₀ d₁ m → ℂ} (ha : a ∈ zeroLocus ℂ (vanish (H0 Ls hH)))
    (hV : ∀ k, a (.e k 1) ≠ 0) :
    finrank ℂ (lieAlg Ls hH) + m ≤ finrank ℂ (tangentSpace (vanish (H0 Ls hH)) a) := by
  classical
  rw [mem_zeroLocus_iff] at ha
  have hH0 := H0_isSubgroup hH
  have hc0 := isZClosed_H0 (Ls := Ls) hH
  -- `a` is a cone representative of a point of `H⁰`
  have hyz : ∀ j, a (.y j) * a (.z j) = 1 := fun j => by
    have := ha _ (mem_vanish.mpr fun g _ lam => by simp [YZ, coords] : YZ ℂ d₀ m j ∈ _)
    simpa [YZ, sub_eq_zero] using this
  have hb : ∀ k, ∃ (q : EVL (Ls k)) (u : ℂ), u ≠ 0 ∧ (fun c => a (.e k c)) = u • repV q := by
    intro k
    have hF := ha _ (mem_vanish.mpr fun g _ lam => eval_coords_Fk g _ k :
      Fk (LSG.ME.g2L Ls) (LSG.ME.g3L Ls) d₀ d₁ k ∈ _)
    have hG := ha _ (mem_vanish.mpr fun g _ lam => eval_coords_Gk g _ k : Gk ℂ d₀ d₁ k ∈ _)
    have hF' : Fn (Ls k).g₂ (Ls k).g₃ (fun c => a (.e k c)) = 0 := by
      simpa [Fk, Fn, F, LSG.ME.g2L, LSG.ME.g3L] using hF
    have hG' : Gn (fun c => a (.e k c)) = 0 := by simpa [Gk, Gn, Gfib] using hG
    have hP : Pe (fun c => a (.e k c)) ≠ 0 := fun h => hV k (by simpa using congrFun h 1)
    obtain ⟨q, t, u, hu, he⟩ := exists_smul_repB two_ne_zero (discr_ne_zero (Ls k)) hF' hG' hP
    exact ⟨⟨q, t⟩, u, hu, he⟩
  obtain ⟨g, lam, hga⟩ := exists_coords_of_rel hyz hb
  have hgH : g ∈ H0 Ls hH := by
    rw [← zeros_vanish hc0]
    intro Q hQ lam'
    have := ha _ (scl_mem_vanish (fun k => lam' k * (lam k)⁻¹) hQ)
    rw [eval_scl, hga, scaleV_coords] at this
    simpa using this
  obtain ⟨p, rfl⟩ := expGV_surjective Ls g
  have hp : GoodV Ls p := (goodV_iff p).mpr fun k h => hV k (by simp [hga, coords, h])
  obtain ⟨ν, hν⟩ := FV_eq_coords hp
  set ρ : Fin m → ℂˣ := fun k => lam k * (ν k)⁻¹
  have haρ : a = scaleV (fun k => (ρ k : ℂ)) (FV Ls p) := by
    rw [hga, hν, scaleV_coords]; congr 1; funext k; simp [ρ]
  have hρ0 : ∏ k, ((ρ k : ℂ)) ^ 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (ρ k).ne_zero
  -- the map
  let φ : TanG d₀ d₁ m × (Fin m → ℂ) → Var d₀ d₁ m → ℂ := fun ws =>
    scaleV (fun k => (ρ k : ℂ)) (DV Ls ws.1 (FV Ls p)) + ∑ k, ws.2 k • blockPart k a
  have hφadd : ∀ x y, φ (x + y) = φ x + φ y := fun x y => by
    funext i; simp only [φ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Prod.fst_add, Prod.snd_add, scaleV_eq_rr, DV_add, add_mul, Finset.sum_add_distrib, mul_add]
    ring
  have hφsmul : ∀ (c : ℂ) x, φ (c • x) = c • φ x := fun c x => by
    funext i; simp only [φ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Prod.smul_fst, Prod.smul_snd, scaleV_eq_rr, DV_smul, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have hmemT : ∀ ws : lieAlg Ls hH × (Fin m → ℂ),
      φ ((ws.1 : TanG d₀ d₁ m), ws.2) ∈ tangentSpace (vanish (H0 Ls hH)) a := by
    rintro ⟨⟨w, hw⟩, s⟩ Q hQ
    have hwT : w ∈ TZ Ls (H0 Ls hH) := by rw [TZ_eq_lieAlg hH0 hc0, lieAlg_H0 hH hc]; exact hw
    have hD : eval a (Dh Ls w Q) = 0 := by
      rw [hga]; exact mem_vanish.mp (Dh_mem_vanish hH0 hwT hQ) _ hgH lam
    rw [haρ, eval_Dh] at hD
    simp only [DV_scale] at hD
    simp only [φ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    have heul : ∀ k ∈ Finset.univ, ∑ i, s k * blockPart k a i *
        eval a (pderiv i Q) = 0 := fun k _ => by
      have := euler_eq_zero hQ hgH lam k
      rw [← hga] at this
      simp only [mul_assoc, mul_comm (blockPart k a _), ← Finset.mul_sum, this, mul_zero]
    rw [Finset.sum_eq_zero heul, add_zero]
    have : ∑ i, eval (scaleV (fun k => (ρ k : ℂ)) (FV Ls p)) (pderiv i Q) *
        ((∏ k, (ρ k : ℂ) ^ 2) * scaleV (fun k => (ρ k : ℂ)) (DV Ls w (FV Ls p)) i) =
        (∏ k, (ρ k : ℂ) ^ 2) * ∑ i, scaleV (fun k => (ρ k : ℂ)) (DV Ls w (FV Ls p)) i *
          eval a (pderiv i Q) := by
      rw [Finset.mul_sum, ← haρ]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this] at hD
    exact (mul_eq_zero.mp hD).resolve_left hρ0
  let Φ : lieAlg Ls hH × (Fin m → ℂ) →ₗ[ℂ] tangentSpace (vanish (H0 Ls hH)) a :=
    { toFun := fun ws => ⟨φ ((ws.1 : TanG d₀ d₁ m), ws.2), hmemT ws⟩
      map_add' := fun x y => Subtype.ext (by simpa using hφadd (x.1, x.2) (y.1, y.2))
      map_smul' := fun c x => Subtype.ext (by simpa using hφsmul c (x.1, x.2)) }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨w, hw⟩, s⟩ h0
    have h := congrArg Subtype.val h0
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero] at h
    have hcoord : ∀ i, φ (w, s) i = 0 := fun i => congrFun h i
    have hDV : ∀ i, DV Ls w (FV Ls p) i = dvalE Ls w (FV Ls p) i := DV_of_V Ls (FV_V hp) w
    have h1 : w.1 = 0 := funext fun i => by
      have := hcoord (.x i); simpa [φ, blockPart, hDV, dvalE] using this
    have h2 : w.2.1 = 0 := funext fun j => by
      have := hcoord (.y j)
      simp only [φ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, scaleV_y,
        blockPart, mul_zero, Finset.sum_const_zero, add_zero] at this
      rw [hDV] at this
      simp only [dvalE] at this
      exact (mul_eq_zero.mp this).resolve_right (by simp [FV, liftV, Complex.exp_ne_zero])
    have hs : s = 0 := funext fun k => by
      have := hcoord (.e k 1)
      simp only [φ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [blockPart, Ne.symm hb]) (by simp)] at this
      simp [blockPart, hDV, dvalE, bField] at this
      exact this.resolve_right (hV k)
    -- the block components
    have hblk : ∀ k, bField (Ls k).g₂ (Ls k).g₃ (w.2.2.1 k) (w.2.2.2 k)
        (fun i => FV Ls p (.e k i)) = 0 := fun k => funext fun i => by
      have := hcoord (.e k i)
      simp [φ, blockPart, hDV, dvalE, hs, (ρ k).ne_zero] at this
      exact this
    have hFk : ∀ k, FV Ls p (.e k 2) - 4 * FV Ls p (.e k 0) ^ 3 +
        (Ls k).g₂ * FV Ls p (.e k 0) * FV Ls p (.e k 2) ^ 2 +
        (Ls k).g₃ * FV Ls p (.e k 2) ^ 3 = 0 := fun k => by
      have hb' : (fun c => FV Ls p (.e k c)) = (ν k : ℂ) • repV ((expGV Ls p).2.2 k) := by
        rw [hν]; funext c; simp [coords]
      have hFn : Fn (Ls k).g₂ (Ls k).g₃ (fun c => FV Ls p (.e k c)) = 0 := by
        rw [hb', Fn_smul, Fn_repV, mul_zero]
      simp only [Fn, F, FV_V hp k] at hFn
      linear_combination hFn
    have h3 : w.2.2.1 = 0 := funext fun k => by
      have hne := LSG.ME.chartVf_ne_zero (hFk k)
      by_contra ha'
      apply hne
      funext i
      have e0 := congrFun (hblk k) 0
      have e2 := congrFun (hblk k) 2
      simp [bField, FV_V hp k] at e0 e2
      fin_cases i
      · simpa [LSG.ME.chartVf] using e0.resolve_left ha'
      · simp [LSG.ME.chartVf]
      · simpa [LSG.ME.chartVf] using e2.resolve_left ha'
    have h4 : w.2.2.2 = 0 := funext fun k => by
      have e4 := congrFun (hblk k) 4
      simp [bField, FV_V hp k, congrFun h3 k] at e4
      exact e4
    have hw0 : w = 0 := Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
    subst hw0 hs
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun] at this

end Tan

/-! ### Transcendence degree and Hilbert dimension of `H⁰` -/

section Dim

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **`trdeg (ℂ[Var]/vanish H⁰) = dim T′ + m`.** -/
theorem trdeg_H0 :
    (Algebra.trdeg ℂ (MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish (H0 Ls hH))).toNat =
      finrank ℂ (lieAlg Ls hH) + m := by
  classical
  have := vanish_H0_isPrime (Ls := Ls) hH
  have hH0 := H0_isSubgroup hH
  apply le_antisymm
  · have ha0 : FV Ls (0 : TanG d₀ d₁ m) ∈ zeroLocus ℂ (vanish (H0 Ls hH)) := by
      rw [mem_zeroLocus_iff]
      intro f hf
      obtain ⟨ν, hν⟩ := FV_eq_coords (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
      rw [hν]; exact mem_vanish.mp hf _ (by rw [expGV_zero]; exact hH0.zero_mem) ν
    exact (LSG.ME.trdeg_le_finrank_tangentSpace _ _ ha0).trans
      (finrank_tangentSpace_zero_le hH hc)
  · have hh : (∏ k, X (.e k 1) : MvPolynomial (Var d₀ d₁ m) ℂ) ∉ vanish (H0 Ls hH) := by
      intro h
      have := mem_vanish.mp h 0 hH0.zero_mem 1
      simp [coords, repV, ptO] at this
    obtain ⟨a, ha, hne, heq⟩ := LSG.ME.exists_smooth_point _ _ hh
    have hV : ∀ k, a (.e k 1) ≠ 0 := by
      intro k h0
      apply hne
      simp only [map_prod, eval_X]
      exact Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [← heq]
    exact le_finrank_tangentSpace hH hc ha hV

/-- **StrongSix's Hilbert dimension of `vanish H⁰` is `dim T′ + m`** (one cone scaling per `E^♮`
block). -/
theorem hdim_H0 (D : LSG.ME.Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (StrongSix.M2.hdata blk D ℂ (vanish (H0 Ls hH))).1 = finrank ℂ (lieAlg Ls hH) + m := by
  classical
  have := vanish_H0_isPrime (Ls := Ls) hH
  rw [LSG.ME.hdim_eq_trdeg blk D hD, trdeg_H0 hH hc]

end Dim

end

end LSG.MEV

