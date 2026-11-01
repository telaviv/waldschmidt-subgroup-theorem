import Mathlib
import LSG.MEV.ChainV
import StrongSix.M2.BridgeLow

/-!
# Hilbert dimensions on `G̃` and the pigeonhole of the chain

* `card_Var = d₀ + 2d₁ + 5m`; **`hdim_IG`**: `hdim I_G̃ = d₀ + d₁ + 3m` (each `E^♮` cone has affine
  dimension `3`).
* `q0`: the linear ideal of the cone over `0` (`X = 0`, `Y = Z = 1`, all `E^♮` coordinates but `V`
  zero); **`hdim_ge_of_le_vanish_zero`**: an ideal vanishing at `0` has `hdim ≥ m`.
* `const_ZG`: the constant term of the canonical formal point is `coords p 1`.
* **`hdim_Lr2_zero_lt`**, **`exists_flat2`**: some `r < d₀ + d₁ + 2m` has
  `hdim L_{r+1} = hdim L_r` (the chain has length `d₀ + d₁ + 2m = dim G̃`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE hdata hdata_le_of_le hdim_section_lt hdim_add_height_eq)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem card_Var : Fintype.card (Var d₀ d₁ m) = d₀ + 2 * d₁ + 5 * m := by
  rw [Fintype.card_congr (varEquiv d₀ d₁ m), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin]
  ring

section Dims

variable {K : Type*} [Field K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)

include hD in
/-- **`hdim I_G̃ = d₀ + d₁ + 3m`.** -/
theorem hdim_IG (g₂ g₃ : Fin m → K) (h2 : (2 : K) ≠ 0) :
    (hdata blk D K (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)).1 = d₀ + d₁ + 3 * m := by
  have hne := (IG_isPrime (d₀ := d₀) (d₁ := d₁) g₂ g₃ h2).ne_top
  have h := hdim_add_height_eq blk D hD hne
  rw [IG, height_IG g₂ g₃ h2, lG_length, card_Var] at h
  have h' : (((hdata blk D K (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)).1 + (d₁ + 2 * m) : ℕ) : ℕ∞) =
      ((d₀ + 2 * d₁ + 5 * m : ℕ) : ℕ∞) := by
    push_cast; exact h
  have := ENat.natCast_inj.mp h'
  omega

/-- The point `0` (the `V`-coordinates are free). -/
def pt0 : Var d₀ d₁ m → K
  | .x _ => 0
  | .y _ => 1
  | .z _ => 1
  | .e _ _ => 0

/-- `V`-coordinates. -/
def isV : Var d₀ d₁ m → Prop
  | .e _ c => c = 1
  | _ => False

instance : DecidablePred (isV : Var d₀ d₁ m → Prop) := fun v => by
  cases v <;> unfold isV <;> infer_instance

theorem card_isV : (Finset.univ.filter fun v : Var d₀ d₁ m => isV v).card = m := by
  have : (Finset.univ.filter fun v : Var d₀ d₁ m => isV v) =
      Finset.univ.image fun k : Fin m => (Var.e k 1 : Var d₀ d₁ m) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    cases v with
    | e k c =>
      simp only [isV, Var.e.injEq]
      exact ⟨fun h => ⟨k, by simp [h]⟩, fun ⟨_, _, h⟩ => h.symm⟩
    | _ => simp [isV]
  rw [this, Finset.card_image_of_injective _ (fun a b h => by cases h; rfl)]
  simp

variable (K) in
/-- The linear ideal of the closure of the cone over `0`. -/
noncomputable def q0 (d₀ d₁ m : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  Ideal.span ((fun v => X v - C (pt0 v)) '' {v | ¬ isV v})

variable (K) in
/-- The projection onto the closure of the cone over `0`. -/
noncomputable def φ0 : MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Var d₀ d₁ m) K :=
  aeval fun v => if isV v then X v else C (pt0 v)

theorem sub_φ0_mem (P : MvPolynomial (Var d₀ d₁ m) K) : P - φ0 K P ∈ q0 K d₀ d₁ m := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [φ0]
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    rwa [map_add, add_sub_add_comm]
  | mul_X p v hp =>
    have hv : X v - φ0 K (X v) ∈ q0 K d₀ d₁ m := by
      by_cases h : isV v
      · simp [φ0, h]
      · exact Ideal.subset_span ⟨v, h, by simp [φ0, h]⟩
    have : p * X v - φ0 K (p * X v) = (p - φ0 K p) * X v + φ0 K p * (X v - φ0 K (X v)) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hv)

theorem q0_ne_top : q0 K d₀ d₁ m ≠ ⊤ := by
  intro h
  have hle : q0 K d₀ d₁ m ≤ RingHom.ker (eval (pt0 (d₀ := d₀) (d₁ := d₁) (m := m))) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, -, rfl⟩
    simp
  have := hle (h ▸ Submodule.mem_top : (1 : MvPolynomial (Var d₀ d₁ m) K) ∈ q0 K d₀ d₁ m)
  simp at this

include hD in
theorem hdim_q0 : m ≤ (hdata blk D K (q0 K d₀ d₁ m)).1 := by
  classical
  set s := (Finset.univ.filter fun v : Var d₀ d₁ m => ¬ isV v).image
    fun v => (X v - C (pt0 v) : MvPolynomial (Var d₀ d₁ m) K) with hs
  have hq : q0 K d₀ d₁ m = Ideal.span (s : Set _) := by
    rw [q0, hs, Finset.coe_image, Finset.coe_filter]
    simp
  have h := hdim_add_height_eq blk D hD (q0_ne_top (K := K) (d₀ := d₀) (d₁ := d₁) (m := m))
  have hht := Ideal.height_span_le_card_of_span_ne_top (s := s) (hq ▸ q0_ne_top)
  have hcard : s.card ≤ (Finset.univ.filter fun v : Var d₀ d₁ m => ¬ isV v).card :=
    Finset.card_image_le
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v : Var d₀ d₁ m => isV v)
  rw [card_isV, Finset.card_univ] at hsplit
  rw [← hq] at hht
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top (q0_ne_top (K := K)
    (d₀ := d₀) (d₁ := d₁) (m := m)))
  rw [← hn] at h hht
  have h' : (((hdata blk D K (q0 K d₀ d₁ m)).1 + n : ℕ) : ℕ∞) =
      ((Fintype.card (Var d₀ d₁ m) : ℕ) : ℕ∞) := by
    push_cast; exact h
  have h1 := ENat.natCast_inj.mp h'
  have h2 : n ≤ s.card := ENat.natCast_le_natCast.mp hht
  omega

end Dims

theorem vanish_zero_le_q0 : vanish ({0} : Set (GPtV d₀ d₁ Ls)) ≤ q0 ℂ d₀ d₁ m := by
  intro P hP
  have hφ : φ0 ℂ P = 0 := by
    have hprod : φ0 ℂ P * ∏ k, X (Var.e k 1 : Var d₀ d₁ m) = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_prod, map_zero, φ0, eval_aeval']
      by_cases hy : ∀ k, y (.e k 1) ≠ 0
      · let lam : Fin m → ℂˣ := fun k => Units.mk0 _ (hy k)
        have : (fun v => eval y (if isV v then X v else C (pt0 v))) =
            coords (0 : GPtV d₀ d₁ Ls) lam := by
          funext v
          cases v with
          | x i => simp [isV, pt0, coords]
          | y j => simp [isV, pt0, coords]
          | z j => simp [isV, pt0, coords]
          | e k c => fin_cases c <;> simp [isV, pt0, coords, lam, repV, ptO]
        rw [this, mem_vanish.mp hP 0 rfl lam, zero_mul]
      · push Not at hy
        obtain ⟨k, hk⟩ := hy
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simpa using hk), mul_zero]
    have hne : (∏ k, X (Var.e k 1 : Var d₀ d₁ m) : MvPolynomial (Var d₀ d₁ m) ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => X_ne_zero _
    exact (mul_eq_zero.mp hprod).resolve_right hne
  have := sub_φ0_mem P
  rwa [hφ, sub_zero] at this

/-- **Ideals vanishing at `0` have dimension `≥ m`.** -/
theorem hdim_ge_of_le_vanish_zero (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hL : L ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls))) :
    m ≤ (hdata blk D ℂ L).1 := by
  have h := hdata_le_of_le blk D ℂ (hL.trans vanish_zero_le_q0) q0_ne_top
  have := hdim_q0 (K := ℂ) (d₀ := d₀) (d₁ := d₁) D hD
  rcases h with h | ⟨h, -⟩ <;> omega

/-! ### The pigeonhole -/

theorem const_ZG (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) :
    (fun v => PowerSeries.constantCoeff (ZG Ls p w v)) = coords p 1 := by
  funext v
  cases v with
  | x i => simp [ZG, ExpV, coords]
  | y j => simp [ZG, ExpV, coords, GPtV.ym, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
  | z j => simp [ZG, ExpV, coords, GPtV.ym, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale]
  | e k c => simp [ZG, coords, (ZB_spec _ _ _).2.2.2]

section Flat

variable {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {S : Finset (GPtV d₀ d₁ Ls)}
  {P : MvPolynomial (Var d₀ d₁ m) ℂ} {T : ℕ} (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include hD

/-- `hdim L₀ < d₀ + d₁ + 3m` (`P ∉ I_G̃`, `I_G̃` prime). -/
theorem hdim_Lr2_zero_lt {d : Fin m → ℕ} (hP : IsHomV P d)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) (hL0 : Lr2 Ls W S P T 0 ≠ ⊤) :
    (hdata blk D ℂ (Lr2 Ls W S P T 0)).1 < d₀ + d₁ + 3 * m := by
  have hprime := IG_isPrime (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) (two_ne_zero' ℂ)
  rw [← vanish_univ] at hPI
  obtain ⟨h, -, lam, hh⟩ : ∃ h ∈ (Set.univ : Set (GPtV d₀ d₁ Ls)), ∃ lam,
      eval (coords h lam) P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPI (mem_vanish.mpr hcon)
  obtain ⟨c, hc⟩ := exists_goodLaw h 0
  obtain ⟨c', hc'⟩ := exists_goodLaw (0 : GPtV d₀ d₁ Ls) 0
  set Q₀ := phOp Ls 0 0 c c' 0 P
  have hQ₀ : Q₀ ∈ Lr2 Ls W S P T 0 :=
    Ideal.mem_sup_right (Ideal.subset_span
      ⟨0, ⟨Fin.elim0, fun i => i.elim0, by simp⟩, 0, W.zero_mem, 0, Nat.zero_le _, c, c', rfl⟩)
  have hτ : Q₀ ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
    intro hm
    have h1 := mem_vanish.mp (IG_le_vanish Set.univ hm) h (Set.mem_univ _) lam
    rw [eval_phOp_eq h 0 lam 0 c c' 0 hP, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul, LSG.ME.constantCoeff_aeval (K := ℂ), add_zero, const_ZG] at h1
    have hu := isUnit_prod_pow (lawAt_unit h 0 lam 0 hc hc') d
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, add_zero] at hu
    have hP1 : aeval (coords h 1) P = eval (coords h 1) P := rfl
    rw [hP1] at h1
    have hh1 : eval (coords h 1) P ≠ 0 := by
      intro h0
      apply hh
      have : coords h lam = fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords h 1 v := by
        funext v
        cases v with
        | e k c =>
          simp only [coords, coordsZ_e, wb, blk_e]
          rw [Finset.prod_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
          simp
        | _ => simp [coords, wb]
      rw [this, show eval (fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords h 1 v) P =
        aeval (fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords h 1 v) P from rfl,
        aeval_weightScale _ d _ _ P hP]
      change _ * eval (coords h 1) P = 0
      rw [h0, mul_zero]
    exact (mul_ne_zero hu hh1) h1
  have hlt := hdim_section_lt blk D ℂ hD (J := IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls))
    (P := Q₀) (fun Q hQ => (hprime.mem_or_mem hQ).resolve_left hτ)
    (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hQ₀))) hL0
  rwa [hdim_IG D hD _ _ (two_ne_zero' ℂ)] at hlt

/-- **Pigeonhole**: two consecutive ideals of the chain have the same Hilbert dimension. -/
theorem exists_flat2 {d : Fin m → ℕ} (hP : IsHomV P d) (hS : (0 : GPtV d₀ d₁ Ls) ∈ S)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls))
    (hlast : Lr2 Ls W S P T (d₀ + d₁ + 2 * m) ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls))) :
    ∃ r < d₀ + d₁ + 2 * m,
      (hdata blk D ℂ (Lr2 Ls W S P T (r + 1))).1 = (hdata blk D ℂ (Lr2 Ls W S P T r)).1 := by
  have hlast' : Lr2 Ls W S P T (d₀ + d₁ + 2 * m) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlast
  have hne : ∀ r ≤ d₀ + d₁ + 2 * m, Lr2 Ls W S P T r ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hlast' (Lr2_mono' hS hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d₀ + d₁ + 2 * m, (hdata blk D ℂ (Lr2 Ls W S P T (r + 1))).1 <
      (hdata blk D ℂ (Lr2 Ls W S P T r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D ℂ (Lr2_mono hS r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d₀ + d₁ + 2 * m, (hdata blk D ℂ (Lr2 Ls W S P T r)).1 + r ≤
      (hdata blk D ℂ (Lr2 Ls W S P T 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have h0 := hdim_Lr2_zero_lt D hD hP hPI (hne 0 (Nat.zero_le _))
  have h1 := hdec (d₀ + d₁ + 2 * m) le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlast
  omega

end Flat

end LSG.MEV
