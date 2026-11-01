import Mathlib
import LSG.ME.SubgroupDhat

/-!
# Zariski closures, irreducible components, translates of irreducible sets (STAGE2 §5, item 5)

Generic part (`K` algebraically closed, `2 ≠ 0`, nonsingular curves).

* `zcl S = zeros (vanish S)`: the Zariski closure (`subset_zcl`, `zcl_minimal`, `vanish_zcl`).
* **`zcl_isSubgroup`**: the Zariski closure of a subgroup is a subgroup.
* **`vanish_singleton_isPrime`**: `vanish {g}` is prime (it is the kernel of `P ↦ P(coords g λ)` as a
  polynomial in `λ`, and a polynomial vanishing on `(Kˣ)^m` is `0`).
* **`exists_components`**: a Zariski-closed `H` has finitely many components: primes `p ⊇ vanish H`
  with `vanish (zeros p) = p`, and every prime containing `vanish H` contains one of them.
* **`vanish_gtransl_isPrime`**: translates of irreducible Zariski-closed sets are irreducible
  (`vanish (V + h)` is the kernel of `P ↦ τ_h P mod vanish V` for a law choice that is good at one
  point of `V`, hence on a dense open subset).
-/

universe u

open MvPolynomial LSG.Elliptic

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Zariski closure -/

/-- The Zariski closure. -/
def zcl (S : Set (GPt K d₀ d₁ g₂ g₃)) : Set (GPt K d₀ d₁ g₂ g₃) :=
  zeros (vanish S : Set (MvPolynomial (Var d₀ d₁ m) K))

theorem subset_zcl (S : Set (GPt K d₀ d₁ g₂ g₃)) : S ⊆ zcl S := subset_zeros_vanish S

theorem isZClosed_zcl (S : Set (GPt K d₀ d₁ g₂ g₃)) : IsZClosed (zcl S) := isZClosed_zeros _

theorem zcl_minimal {S V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (h : S ⊆ V) : zcl S ⊆ V := by
  rw [← zeros_vanish hV]
  intro g hg P hP lam
  exact hg P (vanish_antitone h hP) lam

theorem vanish_zcl (S : Set (GPt K d₀ d₁ g₂ g₃)) : vanish (zcl S) = vanish S :=
  le_antisymm (vanish_antitone (subset_zcl S)) fun _ hP => mem_vanish.mpr fun _ hg lam => hg _ hP lam

theorem zeros_union (S T : Set (MvPolynomial (Var d₀ d₁ m) K)) :
    (zeros (S ∪ T) : Set (GPt K d₀ d₁ g₂ g₃)) = zeros S ∩ zeros T := by
  ext g
  simp only [zeros, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩,
    fun h P hP => hP.elim (h.1 P) (h.2 P)⟩

theorem IsZClosed.inter {V W : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hW : IsZClosed W) :
    IsZClosed (V ∩ W) := by
  obtain ⟨S, rfl⟩ := hV
  obtain ⟨T, rfl⟩ := hW
  exact ⟨S ∪ T, (zeros_union S T).symm⟩

section Group

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

theorem gtransl_subset_iff [IsAlgClosed K] {a : GPt K d₀ d₁ g₂ g₃} {X Y : Set (GPt K d₀ d₁ g₂ g₃)} :
    gtransl a X ⊆ Y ↔ X ⊆ gtransl (-a) Y := by
  constructor
  · intro h x hx; rw [mem_gtransl, sub_neg_eq_add]; exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h hx
    rwa [mem_gtransl, sub_neg_eq_add] at this

/-- **The Zariski closure of a subgroup is a subgroup.** -/
theorem zcl_isSubgroup [IsAlgClosed K] {S : Set (GPt K d₀ d₁ g₂ g₃)} (hS : IsSubgroupG S) :
    IsSubgroupG (zcl S) := by
  have step1 : ∀ a ∈ S, gtransl a (zcl S) ⊆ zcl S := by
    intro a ha
    rw [gtransl_subset_iff h2 hΔ]
    refine zcl_minimal (isZClosed_gtransl h2 hΔ (isZClosed_zcl S) _) fun s hs => ?_
    rw [mem_gtransl, sub_neg_eq_add]
    exact subset_zcl S (hS.add_mem s hs a ha)
  have step2 : ∀ b ∈ zcl S, b ∈ stabG (zcl S) := by
    intro b hb
    rw [mem_stabG_iff, gtransl_subset_iff h2 hΔ]
    refine zcl_minimal (isZClosed_gtransl h2 hΔ (isZClosed_zcl S) _) fun s hs => ?_
    rw [mem_gtransl, sub_neg_eq_add]
    exact step1 s hs ⟨b, hb, add_comm b s⟩
  have hsub := stabG_isSubgroup h2 hΔ (isZClosed_zcl S)
  refine ⟨subset_zcl S hS.zero_mem, fun g hg h hh => step2 g hg h hh, fun g hg => ?_⟩
  have := hsub.neg_mem g (step2 g hg) 0 (subset_zcl S hS.zero_mem)
  rwa [add_zero] at this

end Group

/-! ### `vanish {g}` is prime -/

/-- `P ↦ P(coords g λ)` as a polynomial in `λ`. -/
noncomputable def evPt (g : GPt K d₀ d₁ g₂ g₃) :
    MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Fin m) K :=
  aeval fun v => match v with
    | .x i => C (g.1 i)
    | .y j => C (g.ym j : K)
    | .z j => C (((g.ym j)⁻¹ : Kˣ) : K)
    | .e k c => X k * C (rep (g.2.2 k) c)

theorem eval_evPt (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) (P : MvPolynomial (Var d₀ d₁ m) K) :
    eval (fun k => (lam k : K)) (evPt g P) = eval (coords g lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evPt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, evPt, aeval_X, eval_X]
    congr 1
    cases v <;> simp [coords]

theorem vanish_singleton_isPrime [Infinite K] (g : GPt K d₀ d₁ g₂ g₃) : (vanish {g}).IsPrime := by
  have e : vanish {g} = RingHom.ker (evPt g : MvPolynomial (Var d₀ d₁ m) K →+* MvPolynomial (Fin m) K)
      := by
    ext P
    rw [mem_vanish, RingHom.mem_ker]
    constructor
    · intro h
      refine funext_set (fun _ => ({0}ᶜ : Set K)) (fun _ => Set.Finite.infinite_compl
        (Set.finite_singleton 0)) fun x hx => ?_
      have hx' : ∀ k, x k ≠ 0 := fun k => hx k (Set.mem_univ k)
      have := h g rfl (fun k => Units.mk0 (x k) (hx' k))
      rw [← eval_evPt] at this
      simpa using this
    · intro h g' hg' lam
      rw [Set.mem_singleton_iff] at hg'
      subst hg'
      rw [← eval_evPt, AlgHom.coe_toRingHom] at *
      rw [h, map_zero]
  rw [e]
  exact RingHom.ker_isPrime _

/-! ### Components -/

theorem vanish_radical (E : Set (GPt K d₀ d₁ g₂ g₃)) : (vanish E).radical = vanish E := by
  refine le_antisymm (fun P ⟨n, hn⟩ => mem_vanish.mpr fun g hg lam => ?_) Ideal.le_radical
  have := mem_vanish.mp hn g hg lam
  rw [map_pow] at this
  exact eq_zero_of_pow_eq_zero this

/-- **Components.** -/
theorem exists_components [Infinite K] {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsZClosed H) :
    ∃ ps : Finset (Ideal (MvPolynomial (Var d₀ d₁ m) K)),
      (∀ p ∈ ps, p.IsPrime ∧ vanish H ≤ p ∧
        vanish (zeros (p : Set _) : Set (GPt K d₀ d₁ g₂ g₃)) = p) ∧
      ∀ q : Ideal (MvPolynomial (Var d₀ d₁ m) K), q.IsPrime → vanish H ≤ q → ∃ p ∈ ps, p ≤ q := by
  classical
  set I := vanish H
  have hfin := I.finite_minimalPrimes_of_isNoetherianRing
  refine ⟨hfin.toFinset, fun p hp => ?_, fun q hq hIq => ?_⟩
  · rw [Set.Finite.mem_toFinset] at hp
    have hpr : p.IsPrime := hp.1.1
    refine ⟨hpr, hp.1.2, le_antisymm ?_ ?_⟩
    swap
    · intro P hP
      exact mem_vanish.mpr fun g hg lam => hg P hP lam
    intro P hP
    by_contra hPp
    -- an element of the other minimal primes outside `p`
    have hQ : ¬ (hfin.toFinset.erase p).inf id ≤ p := by
      intro hle
      obtain ⟨p', hp', hp'p⟩ := (Ideal.IsPrime.inf_le' hpr).mp hle
      obtain ⟨hne, hp'm⟩ := Finset.mem_erase.mp hp'
      rw [Set.Finite.mem_toFinset] at hp'm
      exact hne (le_antisymm hp'p (hp.2 hp'm.1 hp'p))
    obtain ⟨Q, hQinf, hQp⟩ := Set.not_subset.mp hQ
    have hPQ : P * Q ∈ I := by
      refine mem_vanish.mpr fun g hg lam => ?_
      have := vanish_singleton_isPrime g
      have hIg : I ≤ vanish {g} := vanish_antitone (Set.singleton_subset_iff.mpr hg)
      obtain ⟨p'', hp'', hle⟩ := Ideal.exists_minimalPrimes_le hIg
      by_cases he : p'' = p
      · subst he
        have hgz : g ∈ zeros (p'' : Set _) := fun R hR lam' => mem_vanish.mp (hle hR) g rfl lam'
        rw [map_mul, mem_vanish.mp hP g hgz lam, zero_mul]
      · have hQ'' : Q ∈ p'' := by
          have : (hfin.toFinset.erase p).inf id ≤ p'' :=
            Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨he, (Set.Finite.mem_toFinset _).mpr hp''⟩)
          exact this hQinf
        rw [map_mul, mem_vanish.mp (hle hQ'') g rfl lam, mul_zero]
    rcases hpr.mem_or_mem (hp.1.2 hPQ) with h | h
    · exact hPp h
    · exact hQp h
  · obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIq
    exact ⟨p, (Set.Finite.mem_toFinset _).mpr hp, hpq⟩

/-! ### Translates of irreducible sets -/

section Transl

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

omit [DecidableEq K] h2 hΔ in
theorem vanish_empty' : vanish (∅ : Set (GPt K d₀ d₁ g₂ g₃)) = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_vanish.mpr fun _ hg => absurd hg (Set.notMem_empty _)

/-- **Translates of irreducible Zariski-closed sets are irreducible.** -/
theorem vanish_gtransl_isPrime [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (h : GPt K d₀ d₁ g₂ g₃) : (vanish (gtransl h V)).IsPrime := by
  classical
  have hne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top vanish_empty'
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨c₀, hc₀⟩ := exists_good h2 hΔ v₀ h
  choose i hi using fun k => Function.ne_iff.mp (hc₀ k)
  let L : MvPolynomial (Var d₀ d₁ m) K := ∏ k, lawPoly g₂ g₃ d₀ d₁ (c₀ k) k (rep (h.2.2 k)) (i k)
  have hL : ∀ (v : GPt K d₀ d₁ g₂ g₃) lam, eval (coords v lam) L =
      ∏ k, (lam k : K) ^ 2 * lawc (c₀ k) (g₂ k) (g₃ k) (rep (v.2.2 k)) (rep (h.2.2 k)) (i k) := by
    intro v lam
    simp only [L, map_prod, eval_lawPoly]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hs := lawc_smul (c₀ k) (g₂ k) (g₃ k) (rep (v.2.2 k)) (rep (h.2.2 k)) (lam k : K) 1
    rw [one_smul, mul_one] at hs
    have : (fun c => coords v lam (.e k c)) = (lam k : K) • rep (v.2.2 k) := by
      funext c; simp [coords]
    rw [this, hs]
    simp
  have hLV : L ∉ vanish V := fun hmem => by
    have := mem_vanish.mp hmem v₀ hv₀ 1
    rw [hL] at this
    simp only [Pi.one_apply, Units.val_one, one_pow, one_mul] at this
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp this
    exact hi k hk
  let φ : MvPolynomial (Var d₀ d₁ m) K →+* MvPolynomial (Var d₀ d₁ m) K ⧸ vanish V :=
    (Ideal.Quotient.mk (vanish V)).comp (τ g₂ g₃ h c₀).toRingHom
  have e : vanish (gtransl h V) = RingHom.ker φ := by
    ext P
    rw [RingHom.mem_ker]
    simp only [φ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hP
      refine mem_vanish.mpr fun v hv lam => ?_
      obtain ⟨ν, hν⟩ := eval_transl h2 hΔ h v c₀ lam
      rw [hν]
      exact eval_coordsZ_eq_zero (mem_vanish.mp hP _ ⟨v, hv, rfl⟩) ν
    · intro hP
      set G := V ∩ {v | v + h ∈ (zeros ({P} : Set _) : Set (GPt K d₀ d₁ g₂ g₃))}
      have hGc : IsZClosed G := by
        refine hV.inter ⟨(translI g₂ g₃ h (Ideal.span {P}) : Set _), ?_⟩
        rw [zeros_translI h2 hΔ]
        ext w
        simp only [Set.mem_ofPred_eq]
        rw [mem_zeros_span]
      have hVG : V ⊆ G := by
        have hvan : vanish G ≤ vanish V := by
          intro Q hQ
          have hQL : Q * L ∈ vanish V := by
            refine mem_vanish.mpr fun v hv lam => ?_
            by_cases hvG : v ∈ G
            · rw [map_mul, mem_vanish.mp hQ v hvG lam, zero_mul]
            · have hLv : eval (coords v 1) L = 0 := by
                by_contra hLv
                apply hvG
                refine ⟨hv, ?_⟩
                have hgood : Good v h c₀ := by
                  intro k hk
                  rw [hL] at hLv
                  exact hLv (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp))
                obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hgood
                intro R hR lam'
                rw [Set.mem_singleton_iff] at hR
                subst hR
                obtain ⟨l, hl⟩ := exists_sq_mul μ lam'
                rw [← hl, ← hμ]
                exact mem_vanish.mp hP v hv l
              have : eval (coords v lam) L = 0 := by
                rw [hL]; rw [hL] at hLv
                simp only [Pi.one_apply, Units.val_one, one_pow, one_mul] at hLv
                obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hLv
                exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, mul_zero])
              rw [map_mul, this, mul_zero]
          exact (hp.mem_or_mem hQL).resolve_right hLV
        intro v hv
        rw [← zeros_vanish hGc]
        exact fun Q hQ lam => mem_vanish.mp (hvan hQ) v hv lam
      refine mem_vanish.mpr ?_
      rintro _ ⟨v, hv, rfl⟩ lam
      exact (hVG hv).2 P rfl lam
  rw [e]
  exact RingHom.ker_isPrime _

end Transl

end LSG.ME
