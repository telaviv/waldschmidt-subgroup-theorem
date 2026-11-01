import Mathlib
import LSG.MEV.RelChain
import LSG.MEV.SubgroupDimV

/-!
# Invariance under vector translations (the push-out reduction, STAGE5_MEV §4, §10)

A *vector translation* of `G̃` is `k = exp(a, 0, 0, φ)`: it shifts the additive coordinates by `a`
and the fibre coordinates by `φ` (`T₁ ↦ T₁ + φ_k W`, `T₃ ↦ T₃ + φ_k V`). On cone representatives
it is the polynomial substitution `vsub a φ` (`coords_add_vtr`), and on the formal points
`phPt` it is the same substitution (`aeval_vsub_phPt`, from `repB_add_fib` and the fibre
equivariance `NLaw_fib_left` of the laws).

* **`aeval_phPt_add_vtr`**: if `P` is invariant under `k` (on all cone representatives), then
  `P(y + k + exp(z w)) = P(y + exp(z w))` as power series; hence **`ordGt_add_vtr`**.
* `zeros_Lr2_add`: the zero sets of the chain are stable under such translations.
* **`le_lieAlg_stabG`**: if `Z(L)` is stable under `exp(Kv)` (`Kv` a subspace) and `V = Z(p)` is a
  relevant prime of maximal dimension over `relI L`, then `Kv ⊆ lieAlg (stabG V)`. Proof: the
  translates `V + exp(c v)` lie in finitely many cosets of `stabG V` (`component_rel`), so
  `{c | exp(c v) ∈ stabG V}` is a subgroup of `ℂ` containing a multiple `j x` (`1 ≤ j ≤ N`) of every
  `x`; hence it contains `N! · ℂ = ℂ`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (hdata)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Vector translations on representatives and formal points -/

/-- The vector `(a, 0, 0, φ)` of `Lie G̃`. -/
def vtr (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) : TanG d₀ d₁ m := (a, 0, 0, φ)

/-- The substitution of the vector translation by `(a, φ)`. -/
def vsub (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .x i => X (.x i) + C (a i)
  | .y j => X (.y j)
  | .z j => X (.z j)
  | .e k i => X (.e k i) + C (φ k) * fibv (fun l => (X (.e k l) : MvPolynomial (Var d₀ d₁ m) ℂ)) i

theorem fibv_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Fin 5 → R)
    (i : Fin 5) : f (fibv P i) = fibv (fun l => f (P l)) i := by
  fin_cases i <;> simp [fibv]

theorem expU_zero : LSG.ME.expU 0 = 1 := Units.ext (by simp [LSG.ME.expU])

theorem expGV_vtr_ym (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) (j : Fin d₁) :
    (expGV Ls (vtr (d₁ := d₁) a φ)).ym j = 1 := by
  show LSG.ME.expU 0 = 1
  exact expU_zero

theorem add_expGV_vtr_e (g : GPtV d₀ d₁ Ls) (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) (k : Fin m) :
    (g + expGV Ls (vtr a φ)).2.2 k = ⟨(g.2.2 k).base, (g.2.2 k).fib + φ k⟩ := by
  show g.2.2 k + expV (Ls k) (0, φ k) = _
  exact add_expV_fib _ _

theorem repV_add_expGV_vtr (g : GPtV d₀ d₁ Ls) (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) (k : Fin m) :
    repV ((g + expGV Ls (vtr a φ)).2.2 k) = repV (g.2.2 k) + φ k • fibv (repV (g.2.2 k)) := by
  rw [add_expGV_vtr_e]
  exact repB_add_fib _ _ _

/-- **Vector translations are polynomial substitutions on representatives.** -/
theorem coords_add_vtr (g : GPtV d₀ d₁ Ls) (a : Fin d₀ → ℂ) (φ : Fin m → ℂ) (lam : Fin m → ℂˣ) :
    coords (g + expGV Ls (vtr a φ)) lam = fun var => eval (coords g lam) (vsub a φ var) := by
  funext var
  cases var with
  | x i => simp [coords, vsub, vtr, expGV]
  | y j => simp [coords, vsub, expGV_vtr_ym]
  | z j => simp [coords, vsub, expGV_vtr_ym]
  | e k i =>
    simp only [coords, coordsZ_e, vsub, repV_add_expGV_vtr, map_add, map_mul, eval_X, eval_C]
    rw [fibv_map]
    fin_cases i <;> simp [fibv] <;> ring

/-- **Vector translations are the same substitution on the formal points.** -/
theorem aeval_vsub_phPt (y : GPtV d₀ d₁ Ls) (a : Fin d₀ → ℂ) (φ : Fin m → ℂ)
    (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC) :
    (fun var => aeval (phPt Ls y w c') (vsub a φ var)) = phPt Ls (y + expGV Ls (vtr a φ)) w c' := by
  funext var
  cases var with
  | x i =>
    simp only [vsub, phPt, map_add, aeval_X, aeval_C, Prod.fst_add, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    simp only [vtr, expGV, Pi.add_apply, map_add]
    ring
  | y j => simp [vsub, phPt, expGV_vtr_ym]
  | z j => simp [vsub, phPt, expGV_vtr_ym]
  | e k i =>
    simp only [phPt]
    have hP : (fun l => PowerSeries.C (repV ((y + expGV Ls (vtr a φ)).2.2 k) l)) =
        (fun l => PowerSeries.C (repV (y.2.2 k) l)) +
          PowerSeries.C (φ k) • fibv (fun l => PowerSeries.C (repV (y.2.2 k) l)) := by
      funext l
      rw [repV_add_expGV_vtr]
      fin_cases l <;> simp [fibv]
    rw [hP, nlawc, NLaw_fib_left]
    simp only [vsub, map_add, map_mul, aeval_X, aeval_C, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← AlgHom.coe_toRingHom, fibv_map]
    simp only [AlgHom.coe_toRingHom, aeval_X, phPt, nlawc, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]

variable (Ls) in
/-- `P` is invariant under translation by `k` (on all cone representatives). -/
def InvTr (k : GPtV d₀ d₁ Ls) (P : MvPolynomial (Var d₀ d₁ m) ℂ) : Prop :=
  ∀ (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ), eval (coords (g + k) lam) P = eval (coords g lam) P

/-- **Invariant polynomials along formal points.** -/
theorem aeval_phPt_add_vtr {a : Fin d₀ → ℂ} {φ : Fin m → ℂ} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : InvTr Ls (expGV Ls (vtr a φ)) P) (y : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m)
    (c' : Fin m → LC) :
    aeval (phPt Ls (y + expGV Ls (vtr a φ)) w c') P = aeval (phPt Ls y w c') P := by
  have hI : aeval (vsub a φ) P - P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
    rw [← vanish_univ]
    refine mem_vanish.mpr fun g _ lam => ?_
    rw [map_sub, eval_aeval', ← coords_add_vtr, hP, sub_self]
  have h0 := aeval_phPt_IG y w c' hI
  rw [map_sub, sub_eq_zero] at h0
  rw [← h0, ← aeval_vsub_phPt, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- **Invariance of the formal order under vector translations.** -/
theorem ordGt_add_vtr {a : Fin d₀ → ℂ} {φ : Fin m → ℂ} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : InvTr Ls (expGV Ls (vtr a φ)) P) (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (n : ℕ)
    (y : GPtV d₀ d₁ Ls) : OrdGt Ls W P n (y + expGV Ls (vtr a φ)) ↔ OrdGt Ls W P n y := by
  simp only [OrdGt, aeval_phPt_add_vtr hP]

/-! ### The chain is stable -/

/-- The zero sets of the chain are stable under translations preserving the formal order of `P`. -/
theorem zeros_Lr2_add {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {S : Finset (GPtV d₀ d₁ Ls)}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} {T : ℕ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {k : GPtV d₀ d₁ Ls} (hk : ∀ y n, OrdGt Ls W P n y → OrdGt Ls W P n (y + k)) (r : ℕ)
    {h : GPtV d₀ d₁ Ls} (hh : h ∈ zeros (Lr2 Ls W S P T r : Set _)) :
    h + k ∈ zeros (Lr2 Ls W S P T r : Set _) := by
  have hQs : ∀ Q ∈ ({P} : Set (MvPolynomial (Var d₀ d₁ m) ℂ)), ∃ d, IsHomV Q d :=
    fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩
  rw [mem_zeros_iff_le_vanish] at hh ⊢
  refine sup_le (IG_le_vanish _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, w, hw, κ, hκ, c, c', rfl⟩
  have hz : h ∈ zeros (phGensV Ls σ W {P} (r * T)) := by
    intro Q hQ lam
    obtain ⟨Q₀, hQ₀, w', hw', κ', hκ', c₁, c₂, rfl⟩ := hQ
    rw [Set.mem_singleton_iff.mp hQ₀]
    exact mem_vanish.mp (hh (Ideal.mem_sup_right (Ideal.subset_span
      ⟨σ, hσ, w', hw', κ', hκ', c₁, c₂, rfl⟩))) h rfl lam
  have hord := (zeros_phOp σ W hQs (r * T) h).mp hz P rfl
  have hz' : h + k ∈ zeros (phGensV Ls σ W {P} (r * T)) := by
    rw [zeros_phOp σ W hQs]
    intro Q hQ
    rw [Set.mem_singleton_iff.mp hQ, show h + k + σ = h + σ + k by abel]
    exact hk _ _ hord
  exact mem_vanish.mpr fun g hg lam => (Set.mem_singleton_iff.mp hg) ▸
    hz' _ ⟨P, rfl, w, hw, κ, hκ, c, c', rfl⟩ lam

/-! ### Stability of a maximal relevant component -/

theorem nsmul_mem_subgroupG {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) {g : GPtV d₀ d₁ Ls}
    (hg : g ∈ H) : ∀ n : ℕ, n • g ∈ H
  | 0 => by rw [zero_smul]; exact hH.zero_mem
  | n + 1 => by rw [succ_nsmul]; exact hH.add_mem _ (nsmul_mem_subgroupG hH hg n) _ hg

theorem expGV_nsmul (n : ℕ) (u : TanG d₀ d₁ m) :
    expGV Ls ((n : ℂ) • u) = n • expGV Ls u := by
  have := map_nsmul (expGVHom Ls) n u
  simp only [expGVHom_apply] at this
  rw [← this, Nat.cast_smul_eq_nsmul]

/-- **A maximal relevant component is stable under a connected group of symmetries of `Z(L)`.** -/
theorem le_lieAlg_stabG (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime)
    (hdim : (hdata blk D ℂ (vanish V)).1 = (hdata blk D ℂ (relI Ls L)).1)
    (hVL : V ⊆ zeros (L : Set _)) (Kv : Submodule ℂ (TanG d₀ d₁ m))
    (hK : ∀ v ∈ Kv, ∀ h ∈ zeros (L : Set (MvPolynomial (Var d₀ d₁ m) ℂ)),
      h + expGV Ls v ∈ zeros (L : Set _)) :
    Kv ≤ lieAlg Ls (stabG_isSubgroup hV) := by
  classical
  obtain ⟨R, hR⟩ := component_rel D hD hV hp hdim
  set GV := stabG V
  have hGV : IsSubgroupG GV := stabG_isSubgroup hV
  -- every `exp(v)`, `v ∈ Kv`, lies in one of the cosets
  have hcov : ∀ v ∈ Kv, ∃ a ∈ R, expGV Ls v - a ∈ GV := by
    intro v hv
    have hmem : expGV Ls v ∈ {h | gtransl h V ⊆ zeros (L : Set _)} := by
      rintro _ ⟨x, hx, rfl⟩
      exact hK v hv x (hVL hx)
    have := hR hmem
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨a, ha, hm⟩ := this
    exact ⟨a, ha, mem_gtransl.mp hm⟩
  intro v hv
  rw [mem_lieAlg]
  intro c
  -- pigeonhole: for every `x`, some `j x` (`1 ≤ j ≤ |R|`) lies in the stabiliser
  have hpig : ∀ x : ℂ, ∃ j : ℕ, 1 ≤ j ∧ j ≤ R.card ∧ expGV Ls (((j : ℂ) * x) • v) ∈ GV := by
    intro x
    choose! f hfR hf using fun i : ℕ => hcov (((i : ℂ) * x) • v) (Kv.smul_mem _ hv)
    have hmaps : ∀ i ∈ Finset.range (R.card + 1), f i ∈ R := fun i _ => hfR i
    obtain ⟨i, hi, i', hi', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by simp) hmaps
    have hd : ∀ {i i' : ℕ}, f i = f i' → i' < i →
        expGV Ls ((((i - i' : ℕ) : ℂ) * x) • v) ∈ GV := by
      intro i i' he hlt
      have h1 := hf i
      have h2 := hf i'
      rw [he] at h1
      have h3 := hGV.add_mem _ h1 _ (hGV.neg_mem _ h2)
      have e : expGV Ls ((((i - i' : ℕ) : ℂ) * x) • v) =
          expGV Ls (((i : ℂ) * x) • v) - f i' + -(expGV Ls (((i' : ℂ) * x) • v) - f i') := by
        have hs := map_sub (expGVHom Ls) (((i : ℂ) * x) • v) (((i' : ℂ) * x) • v)
        simp only [expGVHom_apply] at hs
        rw [Nat.cast_sub hlt.le, sub_mul, sub_smul, hs]; abel
      rw [e]; exact h3
    have hR' : i < R.card + 1 ∧ i' < R.card + 1 := ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hi'⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i' - i, by omega, by omega, hd heq.symm hlt⟩
    · exact ⟨i - i', by omega, by omega, hd heq hlt⟩
  -- the factorial multiple
  have hfac : ∀ x : ℂ, expGV Ls ((((R.card.factorial : ℕ) : ℂ) * x) • v) ∈ GV := by
    intro x
    obtain ⟨j, hj1, hjN, hj⟩ := hpig x
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hj1 hjN
    have := nsmul_mem_subgroupG hGV hj q
    rw [← expGV_nsmul, smul_smul, ← mul_assoc, mul_comm (q : ℂ), ← Nat.cast_mul, ← hq] at this
    exact this
  have hN : ((R.card.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have := hfac (c / (R.card.factorial : ℂ))
  rwa [mul_div_cancel₀ _ hN] at this

end

end LSG.MEV
