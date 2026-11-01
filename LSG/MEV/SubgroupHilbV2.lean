import Mathlib
import LSG.MEV.SubgroupHilbV

/-!
# The Hilbert lower bound for `H⁰ ⊆ G̃` (gap G4), part 2: fibres, free scalings, the bound

Block coordinates of an `E^♮` block `k`, for a predicate `act` (here: `t = π_Z(T′)` is not
identically `0` in block `k`, `actB`):
* the **fibre coordinate** `fcI k` = `T₁` (index 3) if `act k`, else `T₃` (index 4);
* its **coefficient** `svI k` = `W` (index 2) if `act k`, else `V` (index 1).
The fibre translation `t ↦ t + w` acts by `T₁ ↦ T₁ + wW`, `T₃ ↦ T₃ + wV` and fixes `U, V, W`
(`repB_add_fib`), so the fibre coordinate moves by `w · (coefficient)` (`coordsZ_fibshift`).

* **`sepA`**: separation of the fibre powers (along `FibV`, the pure fibre directions of `T′`) and of
  the free scalings (blocks outside `ι_z`): if `Σ_q B_q · ∏ T_{ι_w}^{δ} · ∏ S_J^{γ} ∈ vanish H⁰`, where
  the `B_q` see neither fibre shifts nor the scalings of the blocks `J`, then every
  `B_q · ∏ S_{ι_w} · ∏ S_J ∈ vanish H⁰` (polynomial identities in the fibre parameters and the
  scalings, `coeff_sep`).
* `exists_sv_point`: a point of `H⁰` at which all coefficients `S_k` equal `1`.
* **`hfun_H0_ge_genV`**: `H(L0V; tD₀, tD₁) · (⌊tD₂/2⌋ + 1)^{dim t + dim FibV + m} ≤ H(vanish H⁰; tD)`.
  The family: lifts of a basis of `ℂ[L0V]_{≤(tD₀, tD₁)}` × cone monomials (`monoPV`, degree
  `≤ n`) in the `ι_z` blocks × fibre powers `≤ n` in the `ι_w` blocks × coefficient powers `≤ n` in
  the blocks `k ∉ ι_z`, `n = ⌊tD₂/2⌋` (block degree `≤ 2n ≤ tD₂`).
* **`hfun_H0_geV`**: the explicit bound with the projection exponents
  `(t₀, t₁, t₂ + m)`, `t₀ = dim π₀(Γ)`, `t₁ = dim (T′ ∩ torus)`, `t₂ = dim (T′ ∩ ker π₀ ∩ ker π₁)`:
  `(tD₀/t₀ + 1)^{t₀} (tD₁/t₁ + 1)^{t₁} (⌊tD₂/2⌋ + 1)^{t₂ + m} ≤ H(vanish H⁰; tD)`;
  **`hdim_H0_eq_exps`**: `hdim (vanish H⁰) = t₀ + t₁ + t₂ + m`, the same degree.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module Set
open LSG.W88 (IsAbelianTangent torusLie)
open LSG.W88.Vec (vecIncl torIncl g2Incl)
open StrongSix.M2 (FLE hfun)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Fibre coordinates and their coefficients -/

section Coord

variable (act : Fin m → Prop) [DecidablePred act]

/-- The fibre coordinate of block `k`: `T₁` if `act k`, else `T₃`. -/
def fcI (k : Fin m) : Fin 5 := if act k then 3 else 4

/-- Its coefficient under fibre translation: `W` if `act k`, else `V`. -/
def svI (k : Fin m) : Fin 5 := if act k then 2 else 1

theorem fibv_fcI (P : Fin 5 → ℂ) (k : Fin m) : fibv P (fcI act k) = P (svI act k) := by
  unfold fcI svI fibv; split_ifs <;> rfl

theorem fibv_svI (P : Fin 5 → ℂ) (k : Fin m) : fibv P (svI act k) = 0 := by
  unfold svI fibv; split_ifs <;> rfl

end Coord

/-! ### Fibre translations -/

theorem block_fibshift (g : GPtV d₀ d₁ Ls) (φ : Fin m → ℂ) (k : Fin m) :
    (g + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m)).2.2 k =
      ⟨(g.2.2 k).base, (g.2.2 k).fib + φ k⟩ := by
  show g.2.2 k + expV (Ls k) (0, φ k) = _
  exact add_expV_fib _ _

theorem coordsZ_fibshift (g : GPtV d₀ d₁ Ls) (φ : Fin m → ℂ) (ν : Fin m → ℂ) (k : Fin m)
    (i : Fin 5) :
    coordsZ (g + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m)) ν (.e k i) =
      ν k * (repV (g.2.2 k) i + φ k * fibv (repV (g.2.2 k)) i) := by
  rw [coordsZ_e, block_fibshift]
  show ν k * repB (g.2.2 k).base ((g.2.2 k).fib + φ k) i = _
  rw [repB_add_fib]
  rfl

theorem linPtG_fibshift (g : GPtV d₀ d₁ Ls) (φ : Fin m → ℂ) :
    linPtG (g + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m)) = linPtG g := by
  refine Prod.ext ?_ ?_
  · funext i; simp [linPtG, expGV]
  · funext j; apply Units.ext; simp [linPtG, expGV, GPtV.ym, LSG.ME.expU]

/-- Evaluation of a product of a linear polynomial and cone monomials. -/
theorem eval_P0 {r : ℕ} (ι : Fin r → Fin m) (n : ℕ) (A : MvPolynomial (StrongSix.M2.V3 d₀ d₁) ℂ)
    (β : Fin r → Fin (n + 1) × Fin (n + 1)) (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) :
    eval (coordsZ g ν) (rename ιLV A * ∏ l, monoPV n (ι l) (β l)) =
      eval (StrongSix.M2.pt (linPtG g)) A *
        ∏ l, LSG.ME.monoF n (β l) (fun c => ν (ι l) * rep (g.2.2 (ι l)).base c) := by
  simp only [map_mul, map_prod, eval_rename_ιLV, eval_monoPV, coordsZ_e, repV_base]

/-! ### Separation of fibre powers and free scalings -/

section Sep

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (act : Fin m → Prop) [DecidablePred act]

/-- **Separation.** -/
theorem sepA {f : ℕ} {ιw : Fin f → Fin m}
    (hsw : ∀ y : Fin f → ℂ, ∃ φ ∈ FibV Ls hH, ∀ l, φ (ιw l) = y l)
    {J : Type} [Fintype J] [DecidableEq J] (eJ : J → Fin m) (heJ : Function.Injective eJ)
    {N : ℕ} (B : (Fin f → Fin (N + 1)) × (J → Fin (N + 1)) → MvPolynomial (Var d₀ d₁ m) ℂ)
    (hB : ∀ q (g : GPtV d₀ d₁ Ls) (φ : Fin m → ℂ) (ν ν' : Fin m → ℂ),
      (∀ k, k ∉ Set.range eJ → ν k = ν' k) →
      eval (coordsZ (g + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m)) ν) (B q) =
        eval (coordsZ g ν') (B q))
    (hvan : ∑ q, B q * ((∏ l, X (.e (ιw l) (fcI act (ιw l))) ^ (q.1 l : ℕ)) *
      ∏ j, X (.e (eJ j) (svI act (eJ j))) ^ (q.2 j : ℕ)) ∈ vanish (H0 Ls hH))
    (q₀ : (Fin f → Fin (N + 1)) × (J → Fin (N + 1))) :
    B q₀ * ((∏ l, X (.e (ιw l) (svI act (ιw l)))) * ∏ j, X (.e (eJ j) (svI act (eJ j)))) ∈
      vanish (H0 Ls hH) := by
  classical
  obtain ⟨δ₀, γ₀⟩ := q₀
  refine mem_vanish.mpr fun h hh lam => ?_
  set ω : Fin m → ℂ := fun k => repV (h.2.2 k) (svI act k)
  set τ : Fin m → ℂ := fun k => repV (h.2.2 k) (fcI act k)
  have hPi : eval (coords h lam) ((∏ l, X (.e (ιw l) (svI act (ιw l)))) *
      ∏ j, X (.e (eJ j) (svI act (eJ j))) : MvPolynomial (Var d₀ d₁ m) ℂ) =
      (∏ l, (lam (ιw l) : ℂ) * ω (ιw l)) * ∏ j, (lam (eJ j) : ℂ) * ω (eJ j) := by
    simp [coords, ω]
  by_cases h0 : (∃ l, ω (ιw l) = 0) ∨ (∃ j, ω (eJ j) = 0)
  · rw [map_mul, hPi]
    rcases h0 with ⟨l, hl⟩ | ⟨j, hj⟩
    · rw [Finset.prod_eq_zero (Finset.mem_univ l) (by rw [hl, mul_zero]), zero_mul, mul_zero]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, mul_zero]), mul_zero, mul_zero]
  push Not at h0
  obtain ⟨hω1, hω2⟩ := h0
  -- the values at fibre-shifted points
  have hval : ∀ (ν : Fin m → ℂˣ), ∀ φ ∈ FibV Ls hH, ∑ q, eval (coords h ν) (B q) *
      ((∏ l, ((ν (ιw l) : ℂ) * (τ (ιw l) + φ (ιw l) * ω (ιw l))) ^ (q.1 l : ℕ)) *
        ∏ j, ((ν (eJ j) : ℂ) * ω (eJ j)) ^ (q.2 j : ℕ)) = 0 := by
    intro ν φ hφ
    have hmem : h + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), φ) : TanG d₀ d₁ m) ∈ H0 Ls hH :=
      (H0_isSubgroup hH).add_mem _ hh _ (expGV_mem_H0 hH hφ)
    have := mem_vanish.mp hvan _ hmem ν
    rw [map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]
    congr 1
    · exact (hB q h φ _ _ fun _ _ => rfl).symm
    · simp only [coords, map_mul, map_prod, map_pow, eval_X, coordsZ_fibshift, fibv_fcI,
        fibv_svI, mul_zero, add_zero, τ, ω]
  -- step 1: the fibre powers
  have hstep1 : ∀ ν : Fin m → ℂˣ, ∀ δ : Fin f → Fin (N + 1),
      ∑ γ, eval (coords h ν) (B (δ, γ)) * ∏ j, ((ν (eJ j) : ℂ) * ω (eJ j)) ^ (γ j : ℕ) = 0 := by
    intro ν
    have hsep := coeff_sep (J := Fin f) (N := N)
      (fun δ => ∑ γ, eval (coords h ν) (B (δ, γ)) * ∏ j, ((ν (eJ j) : ℂ) * ω (eJ j)) ^ (γ j : ℕ))
      (fun _ => univ) (fun _ => infinite_univ) ?_
    · exact fun δ => congrFun hsep δ
    intro σ _
    obtain ⟨φ, hφ, hφι⟩ := hsw fun l => ((σ l / ν (ιw l)) - τ (ιw l)) / ω (ιw l)
    have hσ : ∀ l, (ν (ιw l) : ℂ) * (τ (ιw l) + φ (ιw l) * ω (ιw l)) = σ l := by
      intro l
      rw [hφι l, div_mul_cancel₀ _ (hω1 l), add_sub_cancel]
      field_simp [(ν (ιw l)).ne_zero]
    have := hval ν φ hφ
    simp only [hσ] at this
    rw [Fintype.sum_prod_type] at this
    rw [← this]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring
  -- step 2: the free scalings
  have key : ∀ x : J → ℂ, (∀ j, x j ∈ ({0}ᶜ : Set ℂ)) →
      ∑ γ, (eval (coords h lam) (B (δ₀, γ)) * ∏ j, ω (eJ j) ^ (γ j : ℕ)) *
        ∏ j, x j ^ (γ j : ℕ) = 0 := by
    intro x hx
    let ν : Fin m → ℂˣ := fun k =>
      if hk : ∃ j, eJ j = k then Units.mk0 (x hk.choose) (hx _) else lam k
    have hνe : ∀ j, (ν (eJ j) : ℂ) = x j := by
      intro j
      have hk : ∃ j', eJ j' = eJ j := ⟨j, rfl⟩
      simp only [ν, hk, ↓reduceDIte]
      rw [heJ hk.choose_spec]
      rfl
    have hνo : ∀ k, k ∉ Set.range eJ → ν k = lam k := by
      intro k hk
      have : ¬ ∃ j, eJ j = k := fun ⟨j, hj⟩ => hk ⟨j, hj⟩
      simp only [ν, this, ↓reduceDIte]
    have e0 : h + expGV Ls (vecIncl ((0 : Fin d₀ → ℂ), (0 : Fin m → ℂ)) : TanG d₀ d₁ m) = h := by
      rw [show ((0 : Fin d₀ → ℂ), (0 : Fin m → ℂ)) = 0 from rfl, map_zero, expGV_zero, add_zero]
    rw [← hstep1 ν δ₀]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hBν : eval (coords h ν) (B (δ₀, γ)) = eval (coords h lam) (B (δ₀, γ)) := by
      have := hB (δ₀, γ) h 0 (fun k => ν k) (fun k => lam k) (fun k hk => by rw [hνo k hk])
      rw [e0] at this
      exact this
    rw [hBν]
    simp only [hνe, mul_pow, Finset.prod_mul_distrib]
    ring
  have hc := coeff_sep (J := J) _ (fun _ => {0}ᶜ) (fun _ => (finite_singleton 0).infinite_compl) key
  have h1 := congrFun hc γ₀
  have hprod : ∏ j, ω (eJ j) ^ (γ₀ j : ℕ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hω2 j)
  have hBq : eval (coords h lam) (B (δ₀, γ₀)) = 0 := (mul_eq_zero.mp h1).resolve_right hprod
  rw [map_mul, hBq, zero_mul]

end Sep

/-! ### A point with all coefficients `1` -/

theorem exists_sv_point {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) [DecidablePred
    (actB ((lieAlg Ls hH).map (piZ (d₀ := d₀) (d₁ := d₁) (m := m))))] :
    ∃ g ∈ H0 Ls hH, ∀ k, coords g 1
      (.e k (svI (actB ((lieAlg Ls hH).map (piZ (d₀ := d₀) (d₁ := d₁) (m := m)))) k)) = 1 := by
  classical
  set t := (lieAlg Ls hH).map (piZ (d₀ := d₀) (d₁ := d₁) (m := m))
  obtain ⟨v, hvt, hv⟩ := exists_avoid t
  let S : Set ℂ := ⋃ k, {c | actB t k ∧ 0 + c * v k ∈ (Ls k).lattice}
  have hS : S.Countable := by
    refine Set.countable_iUnion fun k => ?_
    by_cases hk : actB t k
    · exact (countable_line_lattice (Ls k) 0 (v k) (hv k hk)).mono fun c hc => hc.2
    · exact (Set.countable_empty).mono fun c hc => hk hc.1
  obtain ⟨c, hcS⟩ := (hS.dense_compl ℂ).nonempty
  obtain ⟨u, hu, hpz⟩ := Submodule.mem_map.mp (t.smul_mem c hvt)
  refine ⟨expGV Ls u, expGV_mem_H0 hH hu, fun k => ?_⟩
  rw [coords_expGV_e]
  have hzk : u.2.2.1 k = c * v k := by
    have := congrFun hpz k
    simpa using this
  simp only [Pi.one_apply, Units.val_one, one_mul]
  unfold svI
  split_ifs with hk
  · have hnot : u.2.2.1 k ∉ (Ls k).lattice := fun hm =>
      hcS (Set.mem_iUnion.mpr ⟨k, hk, by rwa [zero_add, ← hzk]⟩)
    rw [expN_of_notMem _ hnot]
    simp [ptAff]
  · have h0 : u.2.2.1 k = 0 := by
      by_contra hne
      exact hk ⟨piZ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, hne⟩
    have hmem : u.2.2.1 k ∈ (Ls k).lattice := by rw [h0]; exact (Ls k).lattice.zero_mem
    simp [expN, hmem, ptO]

/-! ### Block degrees -/

theorem sum_single_e {Ix : Type*} [Fintype Ix] (e : Ix → Fin m) (he : Function.Injective e)
    (n : ℕ) (k : Fin m) :
    (∑ i, (Pi.single (LSG.ME.Blk.e (e i)) n : LSG.ME.Blk m → ℕ)) (LSG.ME.Blk.e k) =
      if ∃ i, e i = k then n else 0 := by
  classical
  rw [Finset.sum_apply]
  split_ifs with h
  · obtain ⟨i, rfl⟩ := h
    rw [Finset.sum_eq_single i (fun b _ hb => by
      simp only [Pi.single_apply, LSG.ME.Blk.e.injEq]
      exact ite_eq_right_iff.mpr fun h' => absurd (he h'.symm) hb) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Pi.single_apply, LSG.ME.Blk.e.injEq]
    exact ite_eq_right_iff.mpr fun h' => absurd ⟨i, h'.symm⟩ h

theorem sum_single_x {Ix : Type*} [Fintype Ix] (e : Ix → Fin m) (n : ℕ) :
    (∑ i, (Pi.single (LSG.ME.Blk.e (e i)) n : LSG.ME.Blk m → ℕ)) LSG.ME.Blk.x = 0 := by
  classical
  rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _ => by simp

theorem sum_single_yz {Ix : Type*} [Fintype Ix] (e : Ix → Fin m) (n : ℕ) :
    (∑ i, (Pi.single (LSG.ME.Blk.e (e i)) n : LSG.ME.Blk m → ℕ)) LSG.ME.Blk.yz = 0 := by
  classical
  rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _ => by simp

theorem pow_X_mem (v : Var d₀ d₁ m) {n a : ℕ} (ha : a ≤ n) :
    (X v : MvPolynomial (Var d₀ d₁ m) ℂ) ^ a ∈ FLE ℂ blk (Pi.single (blk v) n) := by
  classical
  refine StrongSix.M2.FLE_mono ℂ blk (fun b => ?_)
    (StrongSix.M2.pow_mem_FLE' (LSG.ME.fle_X (K := ℂ) (β := (blk : Var d₀ d₁ m → LSG.ME.Blk m)) v) a)
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> omega

end

end LSG.MEV
