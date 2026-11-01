import Mathlib
import LSG.MEV.Canon
import LSG.MEV.Chain

/-!
# Formal associativity on `G̃` and the characterization of Philippon's operators

* `ZG p w`: the canonical formal point `p + exp(z w)` (blocks `ZB`, normalized in the canonical
  charts); `sclV u Γ`: rescaling of the `E^♮` blocks; `IsHomV Q d`: `Q` is homogeneous of degree
  `d k` in block `k`; **`aeval_sclV`**: `Q(sclV u Γ) = (∏ u_k^{d_k}) Q(Γ)`.
* **`phPt_eq`**: `phPt p w c' = sclV u (ZG p w)` (units for good `c'`).
* **`lawAt_eq`**: `law_c(rep h, phPt g w c') = sclV v (ZG (h + g) w)` (units for good `c, c'`).
* **`transl_phPt_eq`**: `(τ_v^c Q)(phPt y w c') = Q(sclV v (ZG (y + v) w))`.
* **`ordGt_iff`**: for homogeneous `Q`, `OrdGt W Q n p ↔ ∀ w ∈ W, Q(ZG p w)` has no terms of degree
  `≤ n` (law-independence).
* **`zeros_phOp`** (Philippon, Prop. 4.4), **`ordGt_transl`**, **`Lr2_le_vanish_zero`**.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Rescaling and homogeneity -/

section Scale

variable {σ ι : Type*} [Fintype σ] [Fintype ι] {K : Type*} [Field K] {A : Type*} [CommRing A]
  [Algebra K A]

theorem aeval_weightScale (wt : ι → σ → ℕ) (d : ι → ℕ) (u : ι → A) (Γ : σ → A)
    (Q : MvPolynomial σ K) (hQ : ∀ k, Q.IsWeightedHomogeneous (wt k) (d k)) :
    aeval (fun v => (∏ k, u k ^ wt k v) * Γ v) Q = (∏ k, u k ^ d k) * aeval Γ Q := by
  classical
  conv_lhs => rw [Q.as_sum, map_sum]
  conv_rhs => rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hc : Q.coeff s ≠ 0 := mem_support_iff.mp hs
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
    Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib]
  have key : (∏ v, (∏ k, u k ^ wt k v) ^ s v) = ∏ k, u k ^ d k := by
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_pow_eq_pow_sum, ← hQ k hc, Finsupp.weight_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by rw [smul_eq_mul, mul_comm]
  rw [key]; ring

end Scale

/-- `Q` is homogeneous of degree `d k` in the `k`-th `E^♮` block. -/
def IsHomV (Q : MvPolynomial (Var d₀ d₁ m) ℂ) (d : Fin m → ℕ) : Prop :=
  ∀ k, Q.IsWeightedHomogeneous (wb blk (Blk.e k)) (d k)

/-- Rescaling of the `E^♮` blocks. -/
noncomputable def sclV (u : Fin m → PowerSeries ℂ) (Γ : Var d₀ d₁ m → PowerSeries ℂ) :
    Var d₀ d₁ m → PowerSeries ℂ
  | .e k c => u k * Γ (.e k c)
  | v => Γ v

theorem sclV_eq (u : Fin m → PowerSeries ℂ) (Γ : Var d₀ d₁ m → PowerSeries ℂ) :
    sclV u Γ = fun v => (∏ k, u k ^ wb blk (Blk.e k) v) * Γ v := by
  classical
  funext v
  cases v with
  | x i => simp [sclV, wb]
  | y j => simp [sclV, wb]
  | z j => simp [sclV, wb]
  | e k c =>
    simp only [sclV, wb, blk_e]
    rw [Finset.prod_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp

theorem aeval_sclV {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (u : Fin m → PowerSeries ℂ) (Γ : Var d₀ d₁ m → PowerSeries ℂ) :
    aeval (sclV u Γ) Q = (∏ k, u k ^ d k) * aeval Γ Q := by
  rw [sclV_eq]; exact aeval_weightScale _ d u Γ Q hQ

theorem isUnit_prod_pow {u : Fin m → PowerSeries ℂ} (hu : ∀ k, IsUnit (u k)) (d : Fin m → ℕ) :
    IsUnit (∏ k, u k ^ d k) :=
  Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun k _ => (hu k).pow _

theorem LowZero.of_unit' {A : Type*} [CommRing A] {n : ℕ} {f u : PowerSeries A} (hu : IsUnit u)
    (h : LowZero n (u * f)) : LowZero n f := by
  obtain ⟨v, rfl⟩ := hu
  have := h.mul_left (↑v⁻¹ : PowerSeries A)
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

/-! ### The canonical formal point -/

variable (Ls) in
/-- **The canonical formal point** `p + exp(z w)` (canonical charts). -/
noncomputable def ZG (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) : Var d₀ d₁ m → PowerSeries ℂ
  | .x i => PowerSeries.C (p.1 i) + ExpV (g2L Ls) (g3L Ls) w (.x i)
  | .y j => PowerSeries.C (p.ym j : ℂ) * ExpV (g2L Ls) (g3L Ls) w (.y j)
  | .z j => PowerSeries.C (((p.ym j)⁻¹ : ℂˣ) : ℂ) * ExpV (g2L Ls) (g3L Ls) w (.z j)
  | .e k c => ZB (p.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 c

theorem ExpV_e (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    (fun c => ExpV (g2L Ls) (g3L Ls) w (.e k c)) = ZB (0 : EVL (Ls k)) ((w.2.2 k).1 / 2) (w.2.2 k).2 := by
  rw [← ExpBlock_eq]
  funext c
  simp only [ExpV]
  rw [mul_div_cancel₀ _ (two_ne_zero' ℂ)]
  rfl

theorem ZG_norm (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    ZG Ls p w (.e k (bi (chartV (p.2.2 k)))) = 1 :=
  (ZB_spec _ _ _).1.norm

/-- A law choice is good at `(h, g)` in every block. -/
def GoodLaw (h g : GPtV d₀ d₁ Ls) (c : Fin m → LC) : Prop :=
  ∀ k, nlawc (c k) (Ls k).g₂ (Ls k).g₃ (repV (h.2.2 k)) (repV (g.2.2 k)) ≠ 0

theorem exists_goodLaw (h g : GPtV d₀ d₁ Ls) : ∃ c, GoodLaw h g c := by
  choose i j k hc using fun l => exists_NLaw_ne (h.2.2 l) (g.2.2 l)
  exact ⟨fun l => (i l, j l, k l), fun l => hc l⟩

/-- The constant term of a law at a canonical flow. -/
theorem const_law_ZB {L : PeriodPair} (c : LC) (g h : EVL L) (s β : ℂ) (u : ℂ) (l : Fin 5) :
    PowerSeries.constantCoeff (nlawc c (algebraMap ℂ _ L.g₂) (algebraMap ℂ _ L.g₃)
      (fun l => PowerSeries.C (u * repV h l)) (ZB g s β) l) =
      u ^ 3 * nlawc c L.g₂ L.g₃ (repV h) (repV g) l := by
  rw [nlawc, NLaw_map]
  have h1 : (PowerSeries.constantCoeff ∘ fun l => PowerSeries.C (u * repV h l)) = u • repV h := by
    funext l; simp
  have h2 : (PowerSeries.constantCoeff ∘ ZB g s β) = repV g := funext (ZB_spec g s β).2.2.2
  rw [h1, h2]
  simp only [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, Algebra.algebraMap_self, RingHom.id_apply]
  have := nlawc_smul_left c L.g₂ L.g₃ u (repV h) (repV g)
  rw [nlawc] at this
  rw [this]; rfl

/-! ### `phPt` -/

/-- **`phPt` in terms of the canonical point.** -/
theorem phPt_eq (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC) :
    phPt Ls p w c' =
      sclV (fun k : Fin m => phPt Ls p w c' (.e k (bi (chartV (p.2.2 k))))) (ZG Ls p w) := by
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j => rfl
  | e k i =>
    show phPt Ls p w c' (.e k i) = phPt Ls p w c' (.e k (bi (chartV (p.2.2 k)))) *
      ZB (p.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 i
    have hmem : (fun l => phPt Ls p w c' (.e k l)) ∈ lawsAt (algebraMap ℂ _ (Ls k).g₂)
        (algebraMap ℂ _ (Ls k).g₃) (ZB (0 : EVL (Ls k)) ((w.2.2 k).1 / 2) (w.2.2 k).2)
        (fun l => PowerSeries.C (repV (p.2.2 k) l)) := by
      refine ⟨(c' k).1, (c' k).2.1, (c' k).2.2, Or.inr ?_⟩
      funext l
      simp only [phPt, nlawc]
      rw [← ExpV_e]
    have := congrFun (laws_eq (0 : EVL (Ls k)) (p.2.2 k) _ _ hmem) i
    rw [zero_add] at this
    exact this

theorem phPt_unit (p : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) {c' : Fin m → LC}
    (hc' : GoodLaw p 0 c') (k : Fin m) :
    IsUnit (phPt Ls p w c' (.e k (bi (chartV (p.2.2 k))))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have e := const_law_ZB (c' k) (0 : EVL (Ls k)) (p.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 1
    (bi (chartV (p.2.2 k)))
  simp only [one_mul, one_pow] at e
  have hfun : (fun l => phPt Ls p w c' (.e k l)) = nlawc (c' k) (algebraMap ℂ _ (Ls k).g₂)
      (algebraMap ℂ _ (Ls k).g₃) (fun l => PowerSeries.C (repV (p.2.2 k) l))
      (ZB (0 : EVL (Ls k)) ((w.2.2 k).1 / 2) (w.2.2 k).2) := by
    funext l; simp only [phPt]; rw [← ExpV_e]
  have := congrFun hfun (bi (chartV (p.2.2 k)))
  rw [this, e]
  obtain ⟨μ, hμ0, hμ⟩ := NLaw_repV_ne (p.2.2 k) 0 (c' k).1 (c' k).2.1 (c' k).2.2 (hc' k)
  rw [nlawc, hμ, add_zero, Pi.smul_apply, smul_eq_mul, repV_chart, mul_one]
  exact hμ0.isUnit

/-! ### `law(rep h, phPt g)` -/

theorem lawAt_eq (h g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) (w : LieV ℂ d₀ d₁ m)
    (c c' : Fin m → LC) :
    lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c =
      sclV (fun k : Fin m => lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c
        (.e k (bi (chartV ((h + g).2.2 k))))) (ZG Ls (h + g) w) := by
  funext v
  cases v with
  | x i =>
    show PowerSeries.C (h.1 i) + (PowerSeries.C (g.1 i) + _) = PowerSeries.C ((h + g).1 i) + _
    rw [Prod.fst_add, Pi.add_apply, map_add, add_assoc]
  | y j =>
    show PowerSeries.C (h.ym j : ℂ) * (PowerSeries.C (g.ym j : ℂ) * _) =
      PowerSeries.C ((h + g).ym j : ℂ) * _
    rw [GPtV.ym_add, Units.val_mul, map_mul, mul_assoc]
  | z j =>
    show PowerSeries.C (((h.ym j)⁻¹ : ℂˣ) : ℂ) * (PowerSeries.C (((g.ym j)⁻¹ : ℂˣ) : ℂ) * _) =
      PowerSeries.C ((((h + g).ym j)⁻¹ : ℂˣ) : ℂ) * _
    simp only [GPtV.ym_add, mul_inv, Units.val_mul, map_mul]
    ring
  | e k i =>
    set s := (w.2.2 k).1 / 2
    set β := (w.2.2 k).2
    set u' := phPt Ls g w c' (.e k (bi (chartV (g.2.2 k))))
    have hB : (fun l => phPt Ls g w c' (.e k l)) = u' • ZB (g.2.2 k) s β := by
      funext l; exact congrFun (phPt_eq g w c') (.e k l)
    have hA : (fun l => PowerSeries.C (coords h lam (.e k l))) =
        PowerSeries.C (lam k : ℂ) • fun l => PowerSeries.C (repV (h.2.2 k) l) := by
      funext l; simp [coords]
    have hL : (fun l => lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c (.e k l)) =
        (PowerSeries.C (lam k : ℂ) * u') ^ 3 • nlawc (c k) (algebraMap ℂ _ (Ls k).g₂)
          (algebraMap ℂ _ (Ls k).g₃) (fun l => PowerSeries.C (repV (h.2.2 k) l))
          (ZB (g.2.2 k) s β) := by
      funext l
      simp only [lawAt]
      rw [hA, hB, nlawc, NLaw_smul]; rfl
    have hmem : nlawc (c k) (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
        (fun l => PowerSeries.C (repV (h.2.2 k) l)) (ZB (g.2.2 k) s β) ∈
        lawsAt (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃) (ZB (g.2.2 k) s β)
          (fun l => PowerSeries.C (repV (h.2.2 k) l)) :=
      ⟨(c k).1, (c k).2.1, (c k).2.2, Or.inr rfl⟩
    have hlaw := laws_eq (g.2.2 k) (h.2.2 k) s β hmem
    have hgh : (h + g).2.2 k = g.2.2 k + h.2.2 k := by
      show h.2.2 k + g.2.2 k = _; exact add_comm _ _
    have e1 := congrFun hL i
    have e2 := congrFun hL (bi (chartV ((h + g).2.2 k)))
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    show lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c (.e k i) =
      lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c (.e k (bi (chartV ((h + g).2.2 k)))) *
        ZB ((h + g).2.2 k) s β i
    rw [e1, e2, hgh]
    have h3 := congrFun hlaw i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [h3]
    ring

theorem lawAt_unit (h g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) (w : LieV ℂ d₀ d₁ m)
    {c c' : Fin m → LC} (hc : GoodLaw h g c) (hc' : GoodLaw g 0 c') (k : Fin m) :
    IsUnit (lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c
      (.e k (bi (chartV ((h + g).2.2 k))))) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  set b := bi (chartV ((h + g).2.2 k))
  obtain ⟨μ', hμ'0, hμ'⟩ := NLaw_repV_ne (g.2.2 k) 0 (c' k).1 (c' k).2.1 (c' k).2.2 (hc' k)
  obtain ⟨μ, hμ0, hμ⟩ := NLaw_repV_ne (h.2.2 k) (g.2.2 k) (c k).1 (c k).2.1 (c k).2.2 (hc k)
  have hB : ∀ l, PowerSeries.constantCoeff (phPt Ls g w c' (.e k l)) = μ' * repV (g.2.2 k) l := by
    intro l
    have := congrFun (phPt_eq g w c') (.e k l)
    rw [this]
    show PowerSeries.constantCoeff (phPt Ls g w c' (.e k (bi (chartV (g.2.2 k)))) *
      ZB (g.2.2 k) _ _ l) = _
    rw [map_mul, (ZB_spec _ _ _).2.2.2]
    congr 1
    have e := const_law_ZB (c' k) (0 : EVL (Ls k)) (g.2.2 k) ((w.2.2 k).1 / 2) (w.2.2 k).2 1
      (bi (chartV (g.2.2 k)))
    simp only [one_mul, one_pow] at e
    have hfun : phPt Ls g w c' (.e k (bi (chartV (g.2.2 k)))) = nlawc (c' k)
        (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
        (fun l => PowerSeries.C (repV (g.2.2 k) l))
        (ZB (0 : EVL (Ls k)) ((w.2.2 k).1 / 2) (w.2.2 k).2) (bi (chartV (g.2.2 k))) := by
      simp only [phPt]; rw [← ExpV_e]
    rw [hfun, e, nlawc, hμ', add_zero, Pi.smul_apply, smul_eq_mul, repV_chart, mul_one]
  simp only [lawAt]
  rw [nlawc, NLaw_map]
  have h1 : (PowerSeries.constantCoeff ∘ fun l => PowerSeries.C (coords h lam (.e k l))) =
      (lam k : ℂ) • repV (h.2.2 k) := by funext l; simp [coords]
  have h2 : (PowerSeries.constantCoeff ∘ fun l => phPt Ls g w c' (.e k l)) =
      μ' • repV (g.2.2 k) := by funext l; simp [hB]
  rw [h1, h2]
  simp only [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, Algebra.algebraMap_self, RingHom.id_apply]
  rw [NLaw_smul, hμ]
  have hgh : h.2.2 k + g.2.2 k = (h + g).2.2 k := rfl
  rw [hgh]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show repV ((h + g).2.2 k) b = 1 from repV_chart _, mul_one]
  exact (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (lam k).ne_zero hμ'0)) hμ0).isUnit

end LSG.MEV
