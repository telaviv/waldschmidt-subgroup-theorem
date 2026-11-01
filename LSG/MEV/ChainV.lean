import Mathlib
import LSG.MEV.Assoc

/-!
# Philippon's operators and the formal order on `G̃` (zeros, translations, nontriviality)

* **`ordGt_iff`**: for homogeneous `Q`, `OrdGt W Q n p` iff `Q(ZG p w)` has no terms of degree
  `≤ n` for all `w ∈ W` (independence of the law choices).
* **`zeros_phOp`** (Philippon, Prop. 4.4): for homogeneous `Q`s,
  `h ∈ zeros {phOp g w c c' κ Q : Q ∈ 𝒬, w ∈ W, κ ≤ k, all c, c'}` iff every `Q ∈ 𝒬` has
  formal order `> k` along `W` at `h + g`.
* `transl_phPt_eq`, **`ordGt_transl`**: `Q` of order `> n` at `y + v` ⇒ `τ_v^c Q` of order `> n`
  at `y`, for every law choice `c`.
* **`Lr2_le_vanish_zero`**: the last ideal of the chain vanishes at `0`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- **Law-independence of the formal order.** -/
theorem ordGt_iff {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ) (p : GPtV d₀ d₁ Ls) :
    OrdGt Ls W Q n p ↔ ∀ w ∈ W, LowZero n (aeval (ZG Ls p w) Q) := by
  constructor
  · intro h w hw
    obtain ⟨c', hc'⟩ := exists_goodLaw p 0
    have := h w hw c'
    rw [phPt_eq, aeval_sclV hQ] at this
    exact LowZero.of_unit' (isUnit_prod_pow (phPt_unit p w hc') d) this
  · intro h w hw c'
    rw [phPt_eq, aeval_sclV hQ]
    exact (h w hw).mul_left _

variable (Ls) in
/-- The generators of Philippon's ideal: `phOp g w c c' κ Q`, `Q ∈ 𝒬`, `w ∈ W`, `κ ≤ k`. -/
def phGensV (g : GPtV d₀ d₁ Ls) (W : Submodule ℂ (LieV ℂ d₀ d₁ m))
    (Qs : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) (k : ℕ) : Set (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  {P | ∃ Q ∈ Qs, ∃ w ∈ W, ∃ κ ≤ k, ∃ c c' : Fin m → LC, P = phOp Ls g w c c' κ Q}

theorem eval_phOp_eq (h g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) (w : LieV ℂ d₀ d₁ m)
    (c c' : Fin m → LC) (κ : ℕ) {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}
    (hQ : IsHomV Q d) :
    eval (coords h lam) (phOp Ls g w c c' κ Q) = PowerSeries.coeff κ
      ((∏ k, lawAt (Ls := Ls) (coords h lam) (phPt Ls g w c') c
        (.e k (bi (chartV ((h + g).2.2 k)))) ^ d k) * aeval (ZG Ls (h + g) w) Q) := by
  rw [eval_phOp]
  conv_lhs => rw [lawAt_eq]
  rw [aeval_sclV hQ]

/-- **Philippon's Proposition 4.4.** -/
theorem zeros_phOp (g : GPtV d₀ d₁ Ls) (W : Submodule ℂ (LieV ℂ d₀ d₁ m))
    {Qs : Set (MvPolynomial (Var d₀ d₁ m) ℂ)} (hQs : ∀ Q ∈ Qs, ∃ d, IsHomV Q d) (k : ℕ)
    (h : GPtV d₀ d₁ Ls) :
    h ∈ zeros (phGensV Ls g W Qs k) ↔ ∀ Q ∈ Qs, OrdGt Ls W Q k (h + g) := by
  constructor
  · intro hh Q hQ
    obtain ⟨d, hd⟩ := hQs Q hQ
    rw [ordGt_iff hd]
    intro w hw
    obtain ⟨c, hc⟩ := exists_goodLaw h g
    obtain ⟨c', hc'⟩ := exists_goodLaw g 0
    refine LowZero.of_unit' (isUnit_prod_pow (lawAt_unit h g 1 w hc hc') d) fun κ hκ => ?_
    rw [← eval_phOp_eq h g 1 w c c' κ hd]
    exact hh _ ⟨Q, hQ, w, hw, κ, hκ, c, c', rfl⟩ 1
  · rintro hh _ ⟨Q, hQ, w, hw, κ, hκ, c, c', rfl⟩ lam
    obtain ⟨d, hd⟩ := hQs Q hQ
    rw [eval_phOp_eq h g lam w c c' κ hd]
    exact ((ordGt_iff hd W k (h + g)).mp (hh Q hQ) w hw).mul_left _ κ hκ

/-! ### Translations -/

theorem aeval_lawPolyV (Γ : Var d₀ d₁ m → PowerSeries ℂ) (c : LC) (k : Fin m) (q : Fin 5 → ℂ)
    (i : Fin 5) :
    aeval Γ (lawPolyV Ls d₀ d₁ c k q i) = nlawc c (algebraMap ℂ _ (Ls k).g₂)
      (algebraMap ℂ _ (Ls k).g₃) (fun l => Γ (.e k l)) (fun l => PowerSeries.C (q l)) i := by
  rw [lawPolyV, nlawc, ← AlgHom.coe_toRingHom, NLaw_map]
  simp only [AlgHom.coe_toRingHom, aeval_C, nlawc]
  congr 1
  · funext l; simp [bvars]
  · funext l; simp [PowerSeries.algebraMap_apply]

theorem transl_phPt_eq (y v : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) :
    (fun var => aeval (phPt Ls y w c') (translVar Ls v c var)) =
      sclV (fun k : Fin m => aeval (phPt Ls y w c')
        (translVar Ls v c (.e k (bi (chartV ((y + v).2.2 k)))))) (ZG Ls (y + v) w) := by
  funext var
  cases var with
  | x i =>
    simp only [translVar, sclV, ZG, map_add, aeval_X, aeval_C, phPt, Prod.fst_add, Pi.add_apply,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | y j =>
    simp only [translVar, sclV, ZG, map_mul, aeval_X, aeval_C, phPt, GPtV.ym_add, Units.val_mul,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | z j =>
    simp only [translVar, sclV, ZG, map_mul, aeval_X, aeval_C, phPt, GPtV.ym_add, mul_inv,
      Units.val_mul, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | e k i =>
    set s := (w.2.2 k).1 / 2
    set β := (w.2.2 k).2
    set u' := phPt Ls y w c' (.e k (bi (chartV (y.2.2 k))))
    have hB : (fun l => phPt Ls y w c' (.e k l)) = u' • ZB (y.2.2 k) s β := by
      funext l; exact congrFun (phPt_eq y w c') (.e k l)
    have hL : (fun l => aeval (phPt Ls y w c') (translVar Ls v c (.e k l))) =
        u' ^ 3 • nlawc (c k) (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
          (ZB (y.2.2 k) s β) (fun l => PowerSeries.C (repV (v.2.2 k) l)) := by
      funext l
      simp only [translVar, aeval_lawPolyV]
      rw [hB, nlawc_smul_left]
    have hmem : nlawc (c k) (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
        (ZB (y.2.2 k) s β) (fun l => PowerSeries.C (repV (v.2.2 k) l)) ∈
        lawsAt (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃) (ZB (y.2.2 k) s β)
          (fun l => PowerSeries.C (repV (v.2.2 k) l)) :=
      ⟨(c k).1, (c k).2.1, (c k).2.2, Or.inl rfl⟩
    have hlaw := laws_eq (y.2.2 k) (v.2.2 k) s β hmem
    have e1 := congrFun hL i
    have e2 := congrFun hL (bi (chartV ((y + v).2.2 k)))
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    show aeval (phPt Ls y w c') (translVar Ls v c (.e k i)) =
      aeval (phPt Ls y w c') (translVar Ls v c (.e k (bi (chartV ((y + v).2.2 k))))) *
        ZB ((y + v).2.2 k) s β i
    rw [e1, e2]
    have h3 := congrFun hlaw i
    have h4 := congrFun hlaw (bi (chartV (y.2.2 k + v.2.2 k)))
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    rw [(ZB_spec (y.2.2 k + v.2.2 k) s β).1.norm, mul_one] at h4
    have hyv : (y + v).2.2 k = y.2.2 k + v.2.2 k := rfl
    rw [hyv, h3]
    ring

/-- **Translation invariance of the formal order** (every law choice). -/
theorem ordGt_transl {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ) (y v : GPtV d₀ d₁ Ls) (c : Fin m → LC)
    (h : OrdGt Ls W Q n (y + v)) : OrdGt Ls W (τ Ls v c Q) n y := by
  intro w hw c'
  have e : aeval (phPt Ls y w c') (τ Ls v c Q) =
      aeval (fun var => aeval (phPt Ls y w c') (translVar Ls v c var)) Q := by
    rw [τ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [e, transl_phPt_eq, aeval_sclV hQ]
  exact ((ordGt_iff hQ W n (y + v)).mp h w hw).mul_left _

/-! ### Nontriviality of the chain -/

/-- **The last ideal vanishes at `0`** when `P` has formal order `> r T` along `W` on `Σ[r]`. -/
theorem Lr2_le_vanish_zero {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {S : Finset (GPtV d₀ d₁ Ls)}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} {T : ℕ} {d : Fin m → ℕ} (hP : IsHomV P d) {r : ℕ}
    (hvan : ∀ g ∈ sig S r, OrdGt Ls W P (r * T) g) :
    Lr2 Ls W S P T r ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls)) := by
  refine sup_le (IG_le_vanish _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  have h0 : (0 : GPtV d₀ d₁ Ls) ∈ zeros (phGensV Ls σ W {P} (r * T)) := by
    rw [zeros_phOp σ W (fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩)]
    intro Q hQ
    rw [Set.mem_singleton_iff.mp hQ, zero_add]
    exact hvan σ hσ
  refine mem_vanish.mpr fun g hg lam => ?_
  rw [Set.mem_singleton_iff.mp hg]
  exact h0 _ ⟨P, rfl, w, hw, κ, hκ, c, c', rfl⟩ lam

end LSG.MEV
