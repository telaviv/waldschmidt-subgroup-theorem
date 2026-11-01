import Mathlib
import LSG.MEV.TwoParam

/-!
# Philippon's operators lower the formal order; Roy's vanishing claim on `G̃`

* `aeval_phOp_map`: `phOp` evaluated along a formal point `Γ` is the `z'^κ`-coefficient of the
  two-parameter series `Q(law_c(Γ, σ + exp(z' w')))`.
* `phSub_map_eq`: for `Γ = sclV u (ZG y w)` that two-parameter point is `sclG v (W2 y σ w w')`.
* **`lowZero_phOp`** (core), **`ordGt_phOp`**: if `P` (homogeneous) has formal order `> N` at
  `y + σ` then `phOp σ w' c₁ c₂ κ P` has formal order `> T` at `y` (`w' ∈ W`, `κ + T ≤ N`);
  `ordGt_transl_phOp`: every translate `τ_v^c (phOp …)` has order `> T` at `y` given order `> N`
  at `y + v + σ`.
* **`hAVO2`**: Roy's vanishing claim.
* The bridge to derivations (canonical charts, normalized representative): **`ordGt_iff_dv`**
  (pure powers) and **`words_of_ordGt`** (all words of length `≤ N`, `DLV`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk c2)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

local notation "Rz" => PowerSeries ℂ
local notation "PS" => PowerSeries (MvPolynomial (Var d₀ d₁ m) ℂ)

theorem lowZero_sum {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι) (f : ι → PowerSeries A)
    {n : ℕ} (h : ∀ i ∈ s, LowZero n (f i)) : LowZero n (∑ i ∈ s, f i) := fun j hj => by
  rw [map_sum]; exact Finset.sum_eq_zero fun i hi => h i hi j hj

theorem map_aeval_alg (Γ : Var d₀ d₁ m → Rz) (a : ℂ) :
    PowerSeries.map (aeval Γ).toRingHom (algebraMap ℂ PS a) = algebraMap ℂ (PowerSeries Rz) a := by
  simp [PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem aeval_phOp_map (Γ : Var d₀ d₁ m → Rz) (σ : GPtV d₀ d₁ Ls) (w' : LieV ℂ d₀ d₁ m)
    (c₁ c₂ : Fin m → LC) (κ : ℕ) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    aeval Γ (phOp Ls σ w' c₁ c₂ κ P) = PowerSeries.coeff κ
      (aeval (fun v => PowerSeries.map (aeval Γ).toRingHom (phSub Ls σ w' c₁ c₂ v)) P) := by
  rw [phOp]
  rw [show aeval Γ (PowerSeries.coeff κ (aeval (phSub Ls σ w' c₁ c₂) P)) =
    PowerSeries.coeff κ (PowerSeries.map (aeval Γ).toRingHom (aeval (phSub Ls σ w' c₁ c₂) P)) from
      (PowerSeries.coeff_map _ _ _).symm]
  congr 1
  induction P using MvPolynomial.induction_on with
  | C a => rw [aeval_C, aeval_C, map_aeval_alg]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X]

theorem map_aeval_mapC (Γ : Var d₀ d₁ m → Rz) (B : PowerSeries ℂ) :
    PowerSeries.map (aeval Γ).toRingHom (PowerSeries.map MvPolynomial.C B) =
      PowerSeries.map (algebraMap ℂ Rz) B := by
  ext n; simp [PowerSeries.coeff_map]

/-- The two-parameter point as a rescaling of `W2`. -/
theorem phSub_map_eq (u : Fin m → Rz) (y σ : GPtV d₀ d₁ Ls) (w w' : LieV ℂ d₀ d₁ m)
    (c₁ c₂ : Fin m → LC) :
    (fun v => PowerSeries.map (aeval (sclV u (ZG Ls y w))).toRingHom (phSub Ls σ w' c₁ c₂ v)) =
      sclG (fun k : Fin m => PowerSeries.map (aeval (sclV u (ZG Ls y w))).toRingHom
        (phSub Ls σ w' c₁ c₂ (.e k (bi (chartV ((y + σ).2.2 k)))))) (W2 Ls y σ w w') := by
  set Γ := sclV u (ZG Ls y w)
  funext v
  cases v with
  | x i =>
    simp only [phSub, sclG]
    rw [map_add, PowerSeries.map_C, map_aeval_mapC]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    simp only [W2, Γ, sclV, ZG, phPt, Prod.fst_add, Pi.add_apply, map_add, PowerSeries.map_C,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | y j =>
    simp only [phSub, sclG]
    rw [map_mul, PowerSeries.map_C, map_aeval_mapC]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    simp only [W2, Γ, sclV, ZG, phPt, GPtV.ym_add, Units.val_mul, map_mul, PowerSeries.map_C,
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | z j =>
    simp only [phSub, sclG]
    rw [map_mul, PowerSeries.map_C, map_aeval_mapC]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    simp only [W2, Γ, sclV, ZG, phPt, GPtV.ym_add, mul_inv, Units.val_mul, map_mul,
      PowerSeries.map_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | e k i =>
    set s := (w.2.2 k).1 / 2
    set β := (w.2.2 k).2
    set s' := (w'.2.2 k).1 / 2
    set β' := (w'.2.2 k).2
    set u' := phPt Ls σ w' c₂ (.e k (bi (chartV (σ.2.2 k))))
    have hB : (fun l => phPt Ls σ w' c₂ (.e k l)) = u' • ZB (σ.2.2 k) s' β' := by
      funext l; exact congrFun (phPt_eq σ w' c₂) (.e k l)
    have hE : ∀ l', PowerSeries.map (aeval Γ).toRingHom (phSub Ls σ w' c₁ c₂ (.e k l')) =
        (PowerSeries.C (u k) * PowerSeries.map (algebraMap ℂ Rz) u') ^ 3 *
          NLaw (algebraMap ℂ (PowerSeries Rz) (Ls k).g₂) (algebraMap ℂ (PowerSeries Rz) (Ls k).g₃)
            (c₁ k).1 (c₁ k).2.1 (c₁ k).2.2 (fun l => PowerSeries.C (ZB (y.2.2 k) s β l))
            (fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB (σ.2.2 k) s' β' l)) l' := by
      intro l'
      simp only [phSub, nlawc]
      rw [NLaw_map, map_aeval_alg, map_aeval_alg]
      have h1 : (PowerSeries.map (aeval (R := ℂ) Γ).toRingHom ∘ fun l =>
          PowerSeries.C (X (.e k l) : MvPolynomial (Var d₀ d₁ m) ℂ)) =
          (PowerSeries.C (R := Rz) (u k) : PowerSeries Rz) •
            (fun l => (PowerSeries.C (R := Rz) (ZB (y.2.2 k) s β l) : PowerSeries Rz)) := by
        funext l
        simp only [Function.comp_apply, PowerSeries.map_C, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, aeval_X, Γ, sclV, ZG, Pi.smul_apply, smul_eq_mul, map_mul]
        rfl
      have h2 : (PowerSeries.map (aeval (R := ℂ) Γ).toRingHom ∘ fun l =>
          PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ)
            (phPt Ls σ w' c₂ (.e k l))) =
          PowerSeries.map (algebraMap ℂ Rz) u' •
            fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB (σ.2.2 k) s' β' l) := by
        funext l
        simp only [Function.comp_apply, map_aeval_mapC, Pi.smul_apply, smul_eq_mul]
        rw [show phPt Ls σ w' c₂ (.e k l) = u' * ZB (σ.2.2 k) s' β' l from congrFun hB l, map_mul]
      rw [h1, h2, NLaw_smul]; rfl
    have hmem : NLaw (algebraMap ℂ (PowerSeries Rz) (Ls k).g₂)
        (algebraMap ℂ (PowerSeries Rz) (Ls k).g₃) (c₁ k).1 (c₁ k).2.1 (c₁ k).2.2
        (fun l => PowerSeries.C (ZB (y.2.2 k) s β l))
        (fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB (σ.2.2 k) s' β' l)) ∈
        lawsAt (algebraMap ℂ (PowerSeries Rz) (Ls k).g₂) (algebraMap ℂ (PowerSeries Rz) (Ls k).g₃)
          (fun l => PowerSeries.map (algebraMap ℂ Rz) (ZB (σ.2.2 k) s' β' l))
          (fun l => PowerSeries.C (ZB (y.2.2 k) s β l)) :=
      ⟨(c₁ k).1, (c₁ k).2.1, (c₁ k).2.2, Or.inr rfl⟩
    have hlaw := (W2e_spec y σ w w' k).2.2 _ hmem
    show PowerSeries.map (aeval Γ).toRingHom (phSub Ls σ w' c₁ c₂ (.e k i)) =
      PowerSeries.map (aeval Γ).toRingHom (phSub Ls σ w' c₁ c₂ (.e k (bi (chartV ((y + σ).2.2 k))))) *
        W2e y σ w w' k i
    rw [hE, hE]
    have h3 := congrFun hlaw i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [h3]
    ring

/-- **The core of the two-parameter lemma.** -/
theorem lowZero_phOp {P : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {N : ℕ} {y σ : GPtV d₀ d₁ Ls}
    (h : OrdGt Ls W P N (y + σ)) {w w' : LieV ℂ d₀ d₁ m} (hw : w ∈ W) (hw' : w' ∈ W)
    (c₁ c₂ : Fin m → LC) {κ T : ℕ} (hκT : κ + T ≤ N) (u : Fin m → Rz) :
    LowZero T (aeval (sclV u (ZG Ls y w)) (phOp Ls σ w' c₁ c₂ κ P)) := by
  rw [aeval_phOp_map, phSub_map_eq, aeval_sclG hP, PowerSeries.coeff_mul]
  refine lowZero_sum _ _ fun ab hab => ?_
  have hb : ab.2 ≤ κ := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hab; omega
  refine LowZero.mul_left (fun i hi => ?_) _
  -- Taylor in `z'`, then in `z`
  have ht := taylorV (W2_isVFlow y σ w w') ab.2 P
  rw [W2_const] at ht
  have ht2 := taylorV (ZG_isVFlow (y + σ) w) i ((Dv Ls (chartsV (y + σ)) w')^[ab.2] P)
  have hz : aeval (coords (y + σ) 1) ((Dv Ls (chartsV (y + σ)) w)^[i]
      ((Dv Ls (chartsV (y + σ)) w')^[ab.2] P)) = 0 := dv_words_of_ordGt hP h hw hw' (by omega)
  rw [const_ZG, hz, ← ht] at ht2
  have hf1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hf2 : (ab.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ab.2
  rw [← map_natCast (PowerSeries.C (R := ℂ)), PowerSeries.coeff_C_mul] at ht2
  rcases mul_eq_zero.mp ht2 with h0 | h0
  · exact absurd h0 hf1
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hf2
    · exact h1

/-- **Philippon's operators lower the formal order by `κ`.** -/
theorem ordGt_phOp {P : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {N : ℕ} {y σ : GPtV d₀ d₁ Ls}
    (h : OrdGt Ls W P N (y + σ)) {w' : LieV ℂ d₀ d₁ m} (hw' : w' ∈ W) (c₁ c₂ : Fin m → LC)
    {κ T : ℕ} (hκT : κ + T ≤ N) : OrdGt Ls W (phOp Ls σ w' c₁ c₂ κ P) T y := by
  intro w hw c'
  rw [phPt_eq]
  exact lowZero_phOp hP h hw hw' c₁ c₂ hκT _

/-- Translates of Philippon's operators (every law choice `c`). -/
theorem ordGt_transl_phOp {P : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {N : ℕ} {y v σ : GPtV d₀ d₁ Ls}
    (h : OrdGt Ls W P N (y + v + σ)) {w' : LieV ℂ d₀ d₁ m} (hw' : w' ∈ W) (c c₁ c₂ : Fin m → LC)
    {κ T : ℕ} (hκT : κ + T ≤ N) : OrdGt Ls W (τ Ls v c (phOp Ls σ w' c₁ c₂ κ P)) T y := by
  intro w hw c'
  have e : aeval (phPt Ls y w c') (τ Ls v c (phOp Ls σ w' c₁ c₂ κ P)) =
      aeval (fun var => aeval (phPt Ls y w c') (translVar Ls v c var)) (phOp Ls σ w' c₁ c₂ κ P) := by
    rw [τ, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [e, transl_phPt_eq]
  exact lowZero_phOp hP h hw hw' c₁ c₂ hκT _

theorem add_mem_sig {S : Finset (GPtV d₀ d₁ Ls)} {r : ℕ} {g s : GPtV d₀ d₁ Ls}
    (hg : g ∈ sig S r) (hs : s ∈ S) : g + s ∈ sig S (r + 1) := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  refine ⟨Fin.snoc σ s, fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hs
    · simpa using hσ i
  · simp [Fin.sum_univ_castSucc]

/-- **Roy's vanishing claim** on `G̃`: with `p ⊇ L_{r+1}`, `V = Z(p)` and `GV` stabilizing `V`,
the ideal `A = I_G̃ + (τ_v^c Q : Q ∈ gensR2 r, v ∈ V, all c)` has formal order `> T` along `W` on
`⋃ s ∈ S, s + GV`. Its generators lie in `FLE (9 • D)` (`transl_gensR2_mem_FLE`). -/
theorem hAVO2 (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (S : Finset (GPtV d₀ d₁ Ls))
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hP : IsHomV P d) (T r : ℕ)
    {p : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hLp : Lr2 Ls W S P T (r + 1) ≤ p)
    (GV : Set (GPtV d₀ d₁ Ls))
    (hGV : ∀ u ∈ GV, ∀ v ∈ zeros (Ls := Ls) (p : Set _), u + v ∈ zeros (p : Set _)) :
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span {Q' | ∃ Q ∈ gensR2 Ls W S P T r,
        ∃ v ∈ zeros (Ls := Ls) (p : Set _), ∃ c, Q' = τ Ls v c Q} ≤
      ordIdeal Ls W T (⋃ s ∈ S, gtransl s GV) := by
  refine sup_le (IG_le_ordIdeal W T _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨_, ⟨σ, hσ, w', hw', κ, hκ, c₁, c₂, rfl⟩, v, hv, c, rfl⟩ y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨s, hs, hy⟩ := hy
  have hu : y - s ∈ GV := mem_gtransl.mp hy
  -- 1. `P` has formal order `> (r + 1) T` at `y + v + σ`
  have hz : y - s + v ∈ zeros (phGensV Ls (σ + s) W {P} ((r + 1) * T)) := by
    have h1 := hGV _ hu v hv
    intro Q hQ lam
    refine h1 Q (hLp (Ideal.mem_sup_right (Ideal.subset_span ?_))) lam
    obtain ⟨Q₀, hQ₀, w, hw, κ', hκ', c, c', rfl⟩ := hQ
    rw [Set.mem_singleton_iff.mp hQ₀]
    exact ⟨σ + s, add_mem_sig hσ hs, w, hw, κ', hκ', c, c', rfl⟩
  have hord := (zeros_phOp (σ + s) W (Qs := {P})
    (fun Q hQ => ⟨d, (Set.mem_singleton_iff.mp hQ) ▸ hP⟩) ((r + 1) * T) (y - s + v)).mp hz P rfl
  rw [show y - s + v + (σ + s) = y + v + σ by abel] at hord
  -- 2. the two-parameter lemma and the translation by `v`
  exact ordGt_transl_phOp hP hord hw' c c₁ c₂ (by rw [Nat.succ_mul]; omega)

/-- **The bridge to derivations** (pure powers, canonical charts): for homogeneous `Q`, formal order
`> N` along `W` at `p` iff `(Dv_w^n Q)(p) = 0` for all `w ∈ W`, `n ≤ N`. Mixed words of length two
are `dv_words_of_ordGt`. -/
theorem ordGt_iff_dv {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    (W : Submodule ℂ (LieV ℂ d₀ d₁ m)) (N : ℕ) (p : GPtV d₀ d₁ Ls) :
    OrdGt Ls W Q N p ↔
      ∀ w ∈ W, ∀ n ≤ N, eval (coords p 1) ((Dv Ls (chartsV p) w)^[n] Q) = 0 := by
  rw [ordGt_iff hQ]
  constructor
  · intro h w hw n hn
    have ht := taylorV (ZG_isVFlow p w) n Q
    rw [h w hw n hn, mul_zero, const_ZG] at ht
    exact ht.symm
  · intro h w hw n hn
    have ht := taylorV (ZG_isVFlow p w) n Q
    rw [const_ZG] at ht
    have hz : aeval (coords p 1) ((Dv Ls (chartsV p) w)^[n] Q) = 0 := h w hw n hn
    rw [hz] at ht
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    exact (mul_eq_zero.mp ht).resolve_left hf

variable (Ls) in
/-- A word in the chart derivations: `D_{w₁} ⋯ D_{w_r} Q`. -/
noncomputable def DLV (ch : Fin m → Fin 2) (l : List (LieV ℂ d₀ d₁ m))
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  l.foldr (fun w R => Dv Ls ch w R) Q

/-- **The bridge to derivation words**: formal order `> N` along `W` at `p` (homogeneous `Q`) kills
every word of length `≤ N` in the canonical-chart derivations `Dv_w`, `w ∈ W`, at `p`
(polarization, one letter at a time, using the exact commutation `Dv_comm`). -/
theorem words_of_ordGt {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hQ : IsHomV Q d)
    {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {N : ℕ} {p : GPtV d₀ d₁ Ls} (h : OrdGt Ls W Q N p)
    (l : List (LieV ℂ d₀ d₁ m)) (hl : ∀ x ∈ l, x ∈ W) (hlen : l.length ≤ N) :
    eval (coords p 1) (DLV Ls (chartsV p) l Q) = 0 := by
  set ch := chartsV p
  have hpw : ∀ (D : Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
      (n : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ), (D.toLinearMap ^ n) Q = D^[n] Q := by
    intro D n Q; rw [Module.End.pow_apply]; rfl
  -- `Prop(r)`
  have key : ∀ r, ∀ u : List (LieV ℂ d₀ d₁ m), u.length = r → (∀ x ∈ u, x ∈ W) →
      ∀ w ∈ W, ∀ j, r + j ≤ N → eval (coords p 1) ((Dv Ls ch w)^[j] (DLV Ls ch u Q)) = 0 := by
    intro r
    induction r with
    | zero =>
      intro u hu _ w hw j hj
      rw [List.length_eq_zero_iff.mp hu]
      exact (ordGt_iff_dv hQ W N p).mp h w hw j (by omega)
    | succ r ih =>
      intro u hu huW w hw j hj
      obtain ⟨w', u', rfl⟩ : ∃ w' u', u = w' :: u' := by
        cases u with
        | nil => simp at hu
        | cons a t => exact ⟨a, t, rfl⟩
      have hw' : w' ∈ W := huW w' (List.mem_cons_self ..)
      have hu'W : ∀ x ∈ u', x ∈ W := fun x hx => huW x (List.mem_cons_of_mem _ hx)
      have hu' : u'.length = r := by simpa using hu
      set A := (Dv Ls ch w).toLinearMap
      set B := (Dv Ls ch w').toLinearMap
      have hAB : Commute A B := LinearMap.ext fun Q => Dv_comm ch w w' Q
      have hpol := polarize A B hAB (aeval (coords p 1)).toLinearMap (DLV Ls ch u' Q) (N - r)
        (fun α β n hn => by
          have e : α • A + β • B = (Dv Ls ch (α • w + β • w')).toLinearMap := by
            rw [Dv_add, Dv_smul, Dv_smul]; rfl
          rw [e]
          simp only [hpw, AlgHom.toLinearMap_apply]
          exact ih u' hu' hu'W _ (W.add_mem (W.smul_mem α hw) (W.smul_mem β hw')) n (by omega))
        (i := j) (j := 1) (by omega)
      simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply] at hpol
      change (aeval (coords p 1)) (((Dv Ls ch w).toLinearMap ^ j)
        (((Dv Ls ch w').toLinearMap ^ 1) (DLV Ls ch u' Q))) = 0 at hpol
      rw [hpw, hpw] at hpol
      exact hpol
  have := key l.length l rfl hl 0 W.zero_mem 0 (by omega)
  simpa using this

end LSG.MEV
