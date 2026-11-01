import Mathlib
import LSG.ME.SubgroupTangent
import LSG.ME.SubgroupComp
import LSG.ME.SubgroupGraded

/-!
# The identity component `H⁰` and its irreducibility (STAGE2 §5, item 5; `K = ℂ`)

For a Zariski-closed subgroup `H ⊆ G(ℂ)` with analytic Lie algebra `T′ = lieAlg H`:

* **`H0 = zcl (exp T′)`**: a Zariski-closed subgroup contained in `H` (`H0_isSubgroup`,
  `H0_subset`), containing `exp T′`.
* **`vanish_H0_isPrime`**: `vanish H⁰` is prime. For `P Q` with `PQ ∈ vanish H⁰`, the closed sets
  `A_P = {t ∈ T′ | P vanishes at exp t}` and `A_Q` cover `T′` (each `vanish {g}` is prime); a
  closed `A_P` with nonempty interior is all of `T′` (along complex lines, with local analytic lifts,
  applied to the multihomogeneous components of `P`); so one of them is `T′`.
* `isClosed_expG_preimage`: preimages of Zariski-closed sets under `expG` are closed.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set
open LSG.W88 (Tan)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- **Preimages of Zariski-closed sets under `exp` are closed.** -/
theorem isClosed_expG_preimage {Z : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} (hc : IsZClosed Z) :
    IsClosed {p : Tan d₀ d₁ m | expG Ls p ∈ Z} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p₀ hp₀
  obtain ⟨U, hU, hzU, F, hF, hFe⟩ := exists_lifts (Ls := Ls) p₀.2.2
  have hnot : ¬ ∀ Q ∈ homogVanish Z, eval (liftX F p₀) Q = 0 := fun h =>
    hp₀ ((mem_iff_liftX hc fun k => hFe k _ (hzU k)).mpr h)
  push Not at hnot
  obtain ⟨Q, hQ, hne⟩ := hnot
  have hcont : ContinuousAt (fun p : Tan d₀ d₁ m => eval (liftX F p) Q) p₀ := by
    refine continuousAt_eval (f := fun v p => liftX F p v) (fun v => ?_) Q
    cases v with
    | x i => exact ((continuous_apply i).comp continuous_fst).continuousAt
    | y j => exact (Complex.continuous_exp.comp
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd))).continuousAt
    | z j => exact (Complex.continuous_exp.comp
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).neg).continuousAt
    | e k i =>
      exact ContinuousAt.comp (f := fun p : Tan d₀ d₁ m => p.2.2 k) (g := fun w => F k w i)
        (hF k i _ (hzU k)).continuousAt (by fun_prop)
  have hU' : ∀ᶠ p in 𝓝 p₀, ∀ k, p.2.2 k ∈ U k := by
    refine eventually_all.mpr fun k => ?_
    exact ((continuous_apply k).comp (continuous_snd.comp continuous_snd)).continuousAt.preimage_mem_nhds
      ((hU k).mem_nhds (hzU k))
  filter_upwards [hcont.eventually_ne hne, hU'] with p hp hpU
  intro hmem
  exact hp ((mem_iff_liftX hc fun k => hFe k _ (hpU k)).mp hmem Q hQ)

theorem mem_vanish_singleton_iff {g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)}
    {R : MvPolynomial (Var d₀ d₁ m) ℂ} : R ∈ vanish {g} ↔ g ∈ (zeros {R} : Set _) := by
  rw [mem_vanish]
  constructor
  · intro h P hP lam; rw [Set.mem_singleton_iff] at hP; subst hP; exact h g rfl lam
  · intro h g' hg' lam; rw [Set.mem_singleton_iff] at hg'; subst hg'; exact h R rfl lam

/-! ### Lines -/

/-- For multihomogeneous `Q`, vanishing at `exp(q + c v)` frequently near `c₀` implies vanishing
near `c₀`. -/
theorem line_eventually {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wV Q d) (q v : Tan d₀ d₁ m) (c₀ : ℂ)
    (hfr : ∃ᶠ c in 𝓝[≠] c₀, Q ∈ vanish {expG Ls (q + c • v)}) :
    ∀ᶠ c in 𝓝 c₀, Q ∈ vanish {expG Ls (q + c • v)} := by
  obtain ⟨U, hU, hzU, F, hF, hFe⟩ := exists_lifts (Ls := Ls) (q + c₀ • v).2.2
  set W := {c : ℂ | ∀ k, (q + c • v).2.2 k ∈ U k}
  have hW : IsOpen W := by
    have : W = ⋂ k, (fun c : ℂ => (q + c • v).2.2 k) ⁻¹' U k := by ext c; simp [W]
    rw [this]
    exact isOpen_iInter_of_finite fun k => (hU k).preimage (by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW c₀ hzU
  have hlift : ∀ c ∈ Metric.ball c₀ r, ∃ lam, liftX F (q + c • v) = coords (expG Ls (q + c • v)) lam :=
    fun c hc => liftX_eq Ls fun k => hFe k _ (hball hc k)
  have han : AnalyticOnNhd ℂ (fun c : ℂ => eval (liftX F (q + c • v)) Q) (Metric.ball c₀ r) := by
    intro c hc
    refine analyticAt_eval (f := fun x c => liftX F (q + c • v) x) (fun x => ?_) Q
    cases x with
    | x i => show AnalyticAt ℂ (fun c : ℂ => q.1 i + c * v.1 i) c; fun_prop
    | y j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (q.2.1 j + c * v.2.1 j)) c; fun_prop
    | z j => show AnalyticAt ℂ (fun c : ℂ => Complex.exp (-(q.2.1 j + c * v.2.1 j))) c; fun_prop
    | e k i =>
      show AnalyticAt ℂ (fun c : ℂ => F k (q.2.2 k + c * v.2.2 k) i) c
      exact AnalyticAt.comp (g := fun z => F k z i) (f := fun c : ℂ => q.2.2 k + c * v.2.2 k)
        (hF k i _ (hball hc k)) (by fun_prop)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball c₀ r).isPreconnected (Metric.mem_ball_self hr) (by
      refine (hfr.and_eventually (nhdsWithin_le_nhds (Metric.ball_mem_nhds c₀ hr))).mono
        fun c ⟨hc, hcb⟩ => ?_
      obtain ⟨lam, hlam⟩ := hlift c hcb
      rw [hlam]
      exact mem_vanish.mp hc _ rfl lam)
  filter_upwards [Metric.ball_mem_nhds c₀ hr] with c hcb
  obtain ⟨lam, hlam⟩ := hlift c hcb
  refine mem_vanish.mpr fun g hg lam' => ?_
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have h0 : eval (coords (expG Ls (q + c • v)) lam) Q = 0 := by
    rw [← hlam]; exact hzero hcb
  exact (eval_coords_eq_zero_iff hQ _ lam lam').mp h0

/-- For multihomogeneous `Q`: vanishing near one point of a complex line implies vanishing on the
whole line. -/
theorem line_all {Q : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wV Q d) (q v : Tan d₀ d₁ m) (c₀ : ℂ)
    (hc₀ : ∀ᶠ c in 𝓝 c₀, Q ∈ vanish {expG Ls (q + c • v)}) (c : ℂ) :
    Q ∈ vanish {expG Ls (q + c • v)} := by
  set Z := {c : ℂ | Q ∈ vanish {expG Ls (q + c • v)}}
  set A := {c : ℂ | ∀ᶠ c' in 𝓝 c, c' ∈ Z}
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun c₁ hc₁ => ?_
    by_cases hA : c₁ ∈ A
    · exact hA
    refine line_eventually hQ q v c₁ ?_
    rw [Filter.frequently_iff]
    intro W hW
    obtain ⟨W', hW'o, hc₁W', hsub⟩ := mem_nhdsWithin.mp hW
    obtain ⟨c₂, hc₂W, hc₂A⟩ := mem_closure_iff.mp hc₁ W' hW'o hc₁W'
    exact ⟨c₂, hsub ⟨hc₂W, fun h => hA (h ▸ hc₂A)⟩, hc₂A.self_of_nhds⟩
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨c₀, hc₀⟩
  exact (huniv ▸ mem_univ c : c ∈ A).self_of_nhds

/-! ### `H⁰` -/

variable {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

variable (Ls) in
/-- **The identity component** `H⁰`: the Zariski closure of `exp(lieAlg H)`. -/
noncomputable def H0 (hH : IsSubgroupG H) (hc : IsZClosed H) :
    Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) :=
  zcl (expG Ls '' (lieAlg Ls hH hc : Set (Tan d₀ d₁ m)))

theorem expG_lieAlg_isSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsSubgroupG (expG Ls '' (lieAlg Ls hH hc : Set (Tan d₀ d₁ m))) where
  zero_mem := ⟨0, (lieAlg Ls hH hc).zero_mem, expG_zero Ls⟩
  add_mem := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, (lieAlg Ls hH hc).add_mem ha hb, expG_add Ls a b⟩
  neg_mem := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨-a, (lieAlg Ls hH hc).neg_mem ha, ?_⟩
    exact (expGHom Ls).map_neg a

theorem H0_isSubgroup (hH : IsSubgroupG H) (hc : IsZClosed H) : IsSubgroupG (H0 Ls hH hc) :=
  zcl_isSubgroup two_ne_zero (discr_g2L Ls) (expG_lieAlg_isSubgroup hH hc)

theorem isZClosed_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) : IsZClosed (H0 Ls hH hc) :=
  isZClosed_zcl _

theorem expG_lieAlg_subset (hH : IsSubgroupG H) (hc : IsZClosed H) :
    expG Ls '' (lieAlg Ls hH hc : Set (Tan d₀ d₁ m)) ⊆ H := by
  rintro _ ⟨a, ha, rfl⟩
  exact lieAlg_le_Htil ha

theorem H0_subset (hH : IsSubgroupG H) (hc : IsZClosed H) : H0 Ls hH hc ⊆ H :=
  zcl_minimal hc (expG_lieAlg_subset hH hc)

theorem expG_mem_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) {t : Tan d₀ d₁ m}
    (ht : t ∈ lieAlg Ls hH hc) : expG Ls t ∈ H0 Ls hH hc :=
  subset_zcl _ ⟨t, ht, rfl⟩

/-- `A_P` has nonempty interior ⇒ `A_P = T′`. -/
theorem A_univ (hH : IsSubgroupG H) (hc : IsZClosed H) (P : MvPolynomial (Var d₀ d₁ m) ℂ)
    (h : (interior {t : lieAlg Ls hH hc | P ∈ vanish ({expG Ls t} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))}).Nonempty)
    (t : lieAlg Ls hH hc) : P ∈ vanish ({expG Ls t} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) := by
  obtain ⟨t₀, ht₀⟩ := h
  obtain ⟨s, hs⟩ := sum_multiComp P
  rw [hs]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hQ := weightedHomogeneousComponent_isWeightedHomogeneous (w := wV) d P
  -- the line through `t₀` and `t`
  let ℓ : ℂ → lieAlg Ls hH hc := fun c => t₀ + c • (t - t₀)
  have hℓ : Continuous ℓ := by fun_prop
  have hnear : ∀ᶠ c in 𝓝 (0 : ℂ),
      weightedHomogeneousComponent wV d P ∈ vanish ({expG Ls ((t₀ : Tan d₀ d₁ m) + c • ((t : Tan d₀ d₁ m) - (t₀ : Tan d₀ d₁ m)))} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) := by
    have hmem : ∀ᶠ c in 𝓝 (0 : ℂ), ℓ c ∈ interior {t : lieAlg Ls hH hc | P ∈ vanish ({expG Ls t} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))} := by
      refine hℓ.continuousAt.preimage_mem_nhds ?_
      simpa [ℓ] using isOpen_interior.mem_nhds ht₀
    filter_upwards [hmem] with c hc'
    have h1 := interior_subset hc'
    rw [Set.mem_ofPred_eq] at h1
    have h2 : ((ℓ c : lieAlg Ls hH hc) : Tan d₀ d₁ m) =
        (t₀ : Tan d₀ d₁ m) + c • ((t : Tan d₀ d₁ m) - (t₀ : Tan d₀ d₁ m)) := by
      simp [ℓ]
    rw [h2] at h1
    exact multiComp_mem_vanish d h1
  have := line_all hQ (t₀ : Tan d₀ d₁ m) ((t : Tan d₀ d₁ m) - (t₀ : Tan d₀ d₁ m)) 0 hnear 1
  simpa using this

/-- **`H⁰` is irreducible**: `vanish H⁰` is prime. -/
theorem vanish_H0_isPrime (hH : IsSubgroupG H) (hc : IsZClosed H) : (vanish (H0 Ls hH hc)).IsPrime := by
  rw [H0, vanish_zcl]
  set S := expG Ls '' (lieAlg Ls hH hc : Set (Tan d₀ d₁ m))
  refine ⟨vanish_ne_top ⟨_, ⟨0, (lieAlg Ls hH hc).zero_mem, rfl⟩⟩, fun {P Q} hPQ => ?_⟩
  let A : MvPolynomial (Var d₀ d₁ m) ℂ → Set (lieAlg Ls hH hc) :=
    fun R => {t | R ∈ vanish ({expG Ls t} : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)))}
  have hAc : ∀ R, IsClosed (A R) := by
    intro R
    have h1 := isClosed_expG_preimage (Ls := Ls) (d₀ := d₀) (d₁ := d₁) (isZClosed_zeros {R})
    have : A R = Subtype.val ⁻¹' {p : Tan d₀ d₁ m | expG Ls p ∈ (zeros {R} : Set _)} := by
      ext t
      simp only [A, Set.mem_ofPred_eq, Set.mem_preimage]
      exact mem_vanish_singleton_iff
    rw [this]
    exact h1.preimage continuous_subtype_val
  have hcover : ∀ t : lieAlg Ls hH hc, t ∈ A P ∨ t ∈ A Q := by
    intro t
    have hp := vanish_singleton_isPrime (expG Ls (t : Tan d₀ d₁ m))
    exact hp.mem_or_mem (vanish_antitone (Set.singleton_subset_iff.mpr
      (show expG Ls (t : Tan d₀ d₁ m) ∈ S from ⟨t, t.2, rfl⟩)) hPQ)
  have hall : ∀ R, (A R = univ) → R ∈ vanish S := by
    intro R hR
    refine mem_vanish.mpr ?_
    rintro _ ⟨t, ht, rfl⟩ lam
    have : (⟨t, ht⟩ : lieAlg Ls hH hc) ∈ A R := hR ▸ mem_univ _
    exact mem_vanish.mp this _ rfl lam
  by_cases hint : (interior (A P)).Nonempty
  · exact Or.inl (hall P (eq_univ_of_forall fun t => A_univ hH hc P hint t))
  · right
    refine hall Q (eq_univ_of_forall fun t => ?_)
    have hdense : Dense (A P)ᶜ := by
      rw [← interior_eq_empty_iff_dense_compl]
      exact not_nonempty_iff_eq_empty.mp hint
    have hsub : (A P)ᶜ ⊆ A Q := fun t ht => (hcover t).resolve_left ht
    have := hdense.closure_eq ▸ closure_mono hsub
    rw [(hAc Q).closure_eq] at this
    exact this (mem_univ t)

end LSG.ME
