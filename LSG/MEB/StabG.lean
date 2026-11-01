/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Transl

/-!
# Stabilisers, Zariski closures of subgroups, components, irreducible translates (A4.2, α)

Retyped from `LSG.ME.{StabG, SubgroupComp}` for abstract blocks; the only input on the blocks is
`zeros_translI` (`LSG.MEB.Transl`).

* `isZClosed_gtransl`: translates of Zariski-closed sets are Zariski closed.
* **`gtransl_eq_of_subset`**: `h + V ⊆ V` implies `h + V = V` (Noetherianity).
* `stabG V = {h | h + V ⊆ V}`; **`stabG_isSubgroup`**; **`stabG_eq_zeros`**, **`isZClosed_stabG`**.
* **`zcl_isSubgroup`**: the Zariski closure of a subgroup is a subgroup.
* `vanish_radical`; **`exists_components`**: finitely many components.
* `subset_or_subset_of_closed_cover`: an irreducible closed set inside a union of two closed sets lies in
  one of them; hence **`vanish_gtransl_isPrime`**: translates of irreducible sets are irreducible (no law
  polynomial needed, unlike `ME.vanish_gtransl_isPrime`).
-/

open MvPolynomial

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- **Translates of Zariski-closed sets are Zariski closed.** -/
theorem isZClosed_gtransl {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (a : GPt d₀ d₁ B) :
    IsZClosed (gtransl a V) := by
  refine ⟨(translI d₀ d₁ B (-a) (vanish V) : Set _), ?_⟩
  rw [zeros_translI, zeros_vanish hV]
  ext h
  simp [mem_gtransl, sub_eq_add_neg]

/-- **`h + V ⊆ V` implies `h + V = V`** for a Zariski-closed `V`. -/
theorem gtransl_eq_of_subset {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V)
    {h : GPt d₀ d₁ B} (hsub : gtransl h V ⊆ V) : gtransl h V = V := by
  classical
  let Vn : ℕ → Set (GPt d₀ d₁ B) := fun n => gtransl (n • h) V
  have hVn : ∀ n, IsZClosed (Vn n) := fun n => isZClosed_gtransl hV _
  have hanti : ∀ n, Vn (n + 1) ⊆ Vn n := by
    intro n
    simp only [Vn, succ_nsmul, ← gtransl_gtransl]
    rw [gtransl_gtransl, add_comm, ← gtransl_gtransl]
    exact gtransl_mono _ hsub
  have hmono : Monotone fun n => vanish (Vn n) :=
    monotone_nat_of_le_succ fun n => vanish_antitone (hanti n)
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial (Var d₀ d₁ B) ℂ) (MvPolynomial (Var d₀ d₁ B) ℂ))
    ⟨fun n => vanish (Vn n), hmono⟩
  have heq : Vn n = Vn (n + 1) :=
    vanish_injOn (hVn n) (hVn (n + 1)) (hn (n + 1) (Nat.le_succ n))
  have := congrArg (gtransl (-(n • h))) heq
  simp only [Vn, gtransl_gtransl, add_neg_cancel, gtransl_zero, succ_nsmul,
    add_neg_cancel_comm] at this
  exact this.symm

/-- The **stabiliser** `{h | h + V ⊆ V}`. -/
def stabG (V : Set (GPt d₀ d₁ B)) : Set (GPt d₀ d₁ B) := {h | ∀ v ∈ V, h + v ∈ V}

theorem mem_stabG_iff {V : Set (GPt d₀ d₁ B)} {h : GPt d₀ d₁ B} :
    h ∈ stabG V ↔ gtransl h V ⊆ V := by
  constructor
  · rintro hh _ ⟨v, hv, rfl⟩; show v + h ∈ V; rw [add_comm]; exact hh v hv
  · intro hh v hv; rw [add_comm]; exact hh ⟨v, hv, rfl⟩

/-- **The stabiliser of a Zariski-closed set is a subgroup.** -/
theorem stabG_isSubgroup {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) : IsSubgroupG (stabG V) where
  zero_mem v hv := by rwa [zero_add]
  add_mem g hg h hh v hv := by rw [add_assoc]; exact hg _ (hh v hv)
  neg_mem g hg v hv := by
    have heq := gtransl_eq_of_subset hV (mem_stabG_iff.mp hg)
    rw [← heq] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    show -g + (u + g) ∈ V
    rwa [add_comm u, neg_add_cancel_left]

variable (d₀ d₁ B) in
/-- The ideal cutting out the stabiliser of `zeros J`. -/
noncomputable def stabIdeal (J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  Ideal.span {Q | ∃ v ∈ (zeros (J : Set _) : Set (GPt d₀ d₁ B)), Q ∈ translI d₀ d₁ B v J}

/-- **The stabiliser is Zariski closed**: `stabG (zeros J) = zeros (stabIdeal J)`. -/
theorem stabG_eq_zeros (J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    stabG (zeros (J : Set _) : Set (GPt d₀ d₁ B)) = zeros (stabIdeal d₀ d₁ B J : Set _) := by
  ext h
  rw [stabIdeal, mem_zeros_span]
  constructor
  · rintro hh Q ⟨v, hv, hQ⟩ lam
    have hz : h ∈ zeros (translI d₀ d₁ B v J : Set _) := by
      rw [zeros_translI]; exact hh v hv
    exact hz Q hQ lam
  · intro hh v hv
    have hz : h ∈ zeros (translI d₀ d₁ B v J : Set _) := fun Q hQ lam => hh Q ⟨v, hv, hQ⟩ lam
    rw [zeros_translI] at hz
    exact hz

theorem isZClosed_stabG {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) : IsZClosed (stabG V) := by
  rw [← zeros_vanish hV, stabG_eq_zeros]
  exact isZClosed_zeros _

/-- **The Zariski closure of a subgroup is a subgroup.** -/
theorem zcl_isSubgroup {S : Set (GPt d₀ d₁ B)} (hS : IsSubgroupG S) : IsSubgroupG (zcl S) := by
  have step1 : ∀ a ∈ S, gtransl a (zcl S) ⊆ zcl S := by
    intro a ha
    rw [gtransl_subset_iff]
    refine zcl_minimal (isZClosed_gtransl (isZClosed_zcl S) _) fun s hs => ?_
    rw [mem_gtransl, sub_neg_eq_add]
    exact subset_zcl S (hS.add_mem s hs a ha)
  have step2 : ∀ b ∈ zcl S, b ∈ stabG (zcl S) := by
    intro b hb
    rw [mem_stabG_iff, gtransl_subset_iff]
    refine zcl_minimal (isZClosed_gtransl (isZClosed_zcl S) _) fun s hs => ?_
    rw [mem_gtransl, sub_neg_eq_add]
    exact step1 s hs ⟨b, hb, add_comm b s⟩
  have hsub := stabG_isSubgroup (isZClosed_zcl S)
  refine ⟨subset_zcl S hS.zero_mem, fun g hg h hh => step2 g hg h hh, fun g hg => ?_⟩
  have := hsub.neg_mem g (step2 g hg) 0 (subset_zcl S hS.zero_mem)
  rwa [add_zero] at this

/-! ### Components -/

theorem vanish_radical (E : Set (GPt d₀ d₁ B)) : (vanish E).radical = vanish E := by
  refine le_antisymm (fun P ⟨n, hn⟩ => mem_vanish.mpr fun g hg lam => ?_) Ideal.le_radical
  have := mem_vanish.mp hn g hg lam
  rw [map_pow] at this
  exact eq_zero_of_pow_eq_zero this

/-- **Components.** -/
theorem exists_components {H : Set (GPt d₀ d₁ B)} :
    ∃ ps : Finset (Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)),
      (∀ p ∈ ps, p.IsPrime ∧ vanish H ≤ p ∧
        vanish (zeros (p : Set _) : Set (GPt d₀ d₁ B)) = p) ∧
      ∀ q : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ), q.IsPrime → vanish H ≤ q → ∃ p ∈ ps, p ≤ q := by
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

/-! ### Irreducible translates -/

/-- An irreducible set inside a union of two Zariski-closed sets lies in one of them. -/
theorem subset_or_subset_of_closed_cover {V A A' : Set (GPt d₀ d₁ B)} (hp : (vanish V).IsPrime)
    (hA : IsZClosed A) (hA' : IsZClosed A') (hcov : V ⊆ A ∪ A') : V ⊆ A ∨ V ⊆ A' := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have n1 : ¬ vanish A ≤ vanish V := fun h => h1 ((vanish_le_vanish_iff hA).mp h)
  have n2 : ¬ vanish A' ≤ vanish V := fun h => h2 ((vanish_le_vanish_iff hA').mp h)
  obtain ⟨f, hfA, hfV⟩ := Set.not_subset.mp n1
  obtain ⟨g, hgA, hgV⟩ := Set.not_subset.mp n2
  have hfg : f * g ∈ vanish V := by
    refine mem_vanish.mpr fun v hv lam => ?_
    rw [map_mul]
    rcases hcov hv with h | h
    · rw [mem_vanish.mp hfA v h lam, zero_mul]
    · rw [mem_vanish.mp hgA v h lam, mul_zero]
  rcases hp.mem_or_mem hfg with h | h
  · exact hfV h
  · exact hgV h

theorem nonempty_of_isPrime {V : Set (GPt d₀ d₁ B)} (hp : (vanish V).IsPrime) : V.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  exact hp.ne_top vanish_empty

/-- The points `v` with `v + a` in the zero set of `P`: Zariski closed. -/
theorem isZClosed_transl_zeros (a : GPt d₀ d₁ B) (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    IsZClosed {v : GPt d₀ d₁ B | v + a ∈ (zeros {P} : Set (GPt d₀ d₁ B))} := by
  refine ⟨(translI d₀ d₁ B a (Ideal.span {P}) : Set _), ?_⟩
  rw [zeros_translI]
  ext w
  simp only [Set.mem_setOf_eq]
  rw [mem_zeros_span]

/-- **Translates of irreducible sets are irreducible.** -/
theorem vanish_gtransl_isPrime {V : Set (GPt d₀ d₁ B)} (hp : (vanish V).IsPrime)
    (a : GPt d₀ d₁ B) : (vanish (gtransl a V)).IsPrime := by
  have hne : (gtransl a V).Nonempty := (nonempty_of_isPrime hp).image _
  refine ⟨vanish_ne_top hne, fun {P Q} hPQ => ?_⟩
  have hcov : V ⊆ {v | v + a ∈ (zeros {P} : Set (GPt d₀ d₁ B))} ∪
      {v | v + a ∈ (zeros {Q} : Set (GPt d₀ d₁ B))} := by
    intro v hv
    have hva : P * Q ∈ vanish {v + a} :=
      vanish_antitone (Set.singleton_subset_iff.mpr (show v + a ∈ gtransl a V from ⟨v, hv, rfl⟩))
        hPQ
    rcases (vanish_singleton_isPrime (v + a)).mem_or_mem hva with h | h
    · exact Or.inl (mem_vanish_singleton_iff.mp h)
    · exact Or.inr (mem_vanish_singleton_iff.mp h)
  have key : ∀ R : MvPolynomial (Var d₀ d₁ B) ℂ,
      V ⊆ {v | v + a ∈ (zeros {R} : Set (GPt d₀ d₁ B))} → R ∈ vanish (gtransl a V) := by
    intro R hR
    refine mem_vanish.mpr ?_
    rintro _ ⟨v, hv, rfl⟩ lam
    exact hR hv R rfl lam
  rcases subset_or_subset_of_closed_cover hp (isZClosed_transl_zeros a P)
    (isZClosed_transl_zeros a Q) hcov with h | h
  · exact Or.inl (key P h)
  · exact Or.inr (key Q h)

end LSG.MEB
