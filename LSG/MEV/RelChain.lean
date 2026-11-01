import Mathlib
import LSG.MEV.AVO
import LSG.MEV.TranslHF
import LSG.MEV.SubgroupCompV
import StrongSix.M2.Component

/-!
# Relevant radicals, the relevant pigeonhole and Roy's component step on `G̃`

Port of `LSG.ME.MainAbChain` to the vector-extension model. As in the abelian case the generators
of `L_r` and of Roy's `A` are homogeneous of positive degree in every `E^♮` block, so the affine
zero sets of these ideals contain irrelevant cone loci (here even the whole plane `U = V = W = 0`
of each block); everything is phrased with the **relevant radical** `relI L = I(Z(L))`.

* `relI`, `le_relI`, `relI_mono`, `relI_le_vanish_zero`.
* **`exists_flat_rel`**: some `r < d₀ + d₁ + 2m` has `hdim (relI L_{r+1}) = hdim (relI L_r)`
  (`hdim L₀ < d₀ + d₁ + 3m`, `hdim ≥ m` at the end).
* **`exists_relevant_prime`**: a prime `p ⊇ relI L` with `hdim p = hdim (relI L)` and
  `vanish (zeros p) = p`.
* **`component_rel`** (Roy §8.4.1): for `V` irreducible Zariski-closed with
  `hdim I(V) = hdim (relI L)`, `{h | h + V ⊆ Z(L)}` is covered by finitely many cosets of
  `stabG V`.
* **`zeros_transl_subset`**: the zeros of `A = I_G̃ + (τ_v^c Q : Q ∈ gens, v ∈ V)` satisfy
  `h + V ⊆ Z(I_G̃ + (gens))`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE hdata hdata_le_of_le)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

variable (Ls) in
/-- The **relevant radical** `I(Z(L))`. -/
noncomputable def relI (L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  vanish (zeros (L : Set _) : Set (GPtV d₀ d₁ Ls))

theorem le_relI (L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) : L ≤ relI Ls L :=
  fun P hP => mem_vanish.mpr fun _ hg lam => hg P hP lam

theorem relI_mono {L L' : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (h : L ≤ L') :
    relI Ls L ≤ relI Ls L' :=
  vanish_antitone fun _ hg P hP lam => hg P (h hP) lam

theorem relI_le_vanish_zero {L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)}
    (h : L ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls))) :
    relI Ls L ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls)) :=
  vanish_antitone (Set.singleton_subset_iff.mpr (mem_zeros_iff_le_vanish.mpr h))

/-! ### The relevant pigeonhole -/

section Flat

variable (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
  {W : Submodule ℂ (LieV ℂ d₀ d₁ m)} {S : Finset (GPtV d₀ d₁ Ls)}
  {P : MvPolynomial (Var d₀ d₁ m) ℂ} {T : ℕ}
include hD

/-- **Pigeonhole for the relevant radicals of the chain.** -/
theorem exists_flat_rel {d : Fin m → ℕ} (hP : IsHomV P d) (hS : (0 : GPtV d₀ d₁ Ls) ∈ S)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls))
    (hlast : Lr2 Ls W S P T (d₀ + d₁ + 2 * m) ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls))) :
    ∃ r < d₀ + d₁ + 2 * m,
      (hdata blk D ℂ (relI Ls (Lr2 Ls W S P T (r + 1)))).1 =
        (hdata blk D ℂ (relI Ls (Lr2 Ls W S P T r))).1 := by
  set J : ℕ → Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) := fun r => relI Ls (Lr2 Ls W S P T r)
  have hlastJ : J (d₀ + d₁ + 2 * m) ≤ vanish ({0} : Set (GPtV d₀ d₁ Ls)) :=
    relI_le_vanish_zero hlast
  have hlast' : J (d₀ + d₁ + 2 * m) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlastJ
  have hmono : ∀ r, J r ≤ J (r + 1) := fun r => relI_mono (Lr2_mono hS r)
  have hmono' : ∀ {r r'}, r ≤ r' → J r ≤ J r' := by
    intro r r' h
    induction r', h using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (hmono n)
  have hne : ∀ r ≤ d₀ + d₁ + 2 * m, J r ≠ ⊤ := fun r hr => ne_top_of_le_ne_top hlast' (hmono' hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d₀ + d₁ + 2 * m, (hdata blk D ℂ (J (r + 1))).1 < (hdata blk D ℂ (J r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D ℂ (hmono r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d₀ + d₁ + 2 * m, (hdata blk D ℂ (J r)).1 + r ≤ (hdata blk D ℂ (J 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have hL0 : Lr2 Ls W S P T 0 ≠ ⊤ := ne_top_of_le_ne_top (hne 0 (Nat.zero_le _)) (le_relI _)
  have h0 := hdim_Lr2_zero_lt D hD hP hPI hL0
  have h0' : (hdata blk D ℂ (J 0)).1 ≤ (hdata blk D ℂ (Lr2 Ls W S P T 0)).1 := by
    change (hdata blk D ℂ (relI Ls (Lr2 Ls W S P T 0))).1 ≤ _
    rcases hdata_le_of_le blk D ℂ (le_relI (Ls := Ls) (Lr2 Ls W S P T 0))
      (hne 0 (Nat.zero_le _)) with h | ⟨h, -⟩ <;> omega
  have h1 := hdec (d₀ + d₁ + 2 * m) le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlastJ
  omega

end Flat

/-! ### A relevant prime of maximal dimension -/

/-- **A relevant prime over `relI L` of the same Hilbert dimension.** -/
theorem exists_relevant_prime (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} (hne : relI Ls L ≠ ⊤) :
    ∃ p : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ), p.IsPrime ∧ relI Ls L ≤ p ∧
      (hdata blk D ℂ p).1 = (hdata blk D ℂ (relI Ls L)).1 ∧
      vanish (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) = p := by
  obtain ⟨p, hp, hJp, hdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  have := hp
  have hmin := StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD hJp hdim
  obtain ⟨ps, hps, hcov⟩ := exists_components (H := (zeros (L : Set _) : Set (GPtV d₀ d₁ Ls)))
  obtain ⟨p', hp'ps, hp'p⟩ := hcov p hp hJp
  obtain ⟨hp'pr, hJp', hp'v⟩ := hps p' hp'ps
  have he : p' = p := le_antisymm hp'p (hmin.2 ⟨hp'pr, hJp'⟩ hp'p)
  subst he
  exact ⟨p', hp, hJp, hdim, hp'v⟩

/-! ### Roy's component step -/

/-- **Roy's component step** (relevant form). -/
theorem component_rel (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime)
    (hdim : (hdata blk D ℂ (vanish V)).1 = (hdata blk D ℂ (relI Ls L)).1) :
    ∃ R : Finset (GPtV d₀ d₁ Ls),
      {h | gtransl h V ⊆ zeros (L : Set _)} ⊆ ⋃ a ∈ R, gtransl a (stabG V) := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top (vanish_empty' (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
  set Z := {h | gtransl h V ⊆ zeros (L : Set (MvPolynomial (Var d₀ d₁ m) ℂ))}
  let φ : GPtV d₀ d₁ Ls → Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) := fun h => vanish (gtransl h V)
  have hmin : ∀ h ∈ Z, φ h ∈ (relI Ls L).minimalPrimes := by
    intro h hh
    have := vanish_gtransl_isPrime hV hp h
    refine StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD (vanish_antitone hh) ?_
    rw [hdim_vanish_gtransl D hVne h, hdim]
  have hfinM : (relI Ls L).minimalPrimes.Finite :=
    (relI Ls L).finite_minimalPrimes_of_isNoetherianRing
  have hfin : (φ '' Z).Finite := hfinM.subset (by rintro _ ⟨h, hh, rfl⟩; exact hmin h hh)
  have hrep : ∀ q ∈ φ '' Z, ∃ a ∈ Z, φ a = q := fun q hq => hq
  choose! rep hrepZ hrepφ using hrep
  refine ⟨hfin.toFinset.image rep, fun h hh => ?_⟩
  have hq : φ h ∈ φ '' Z := ⟨h, hh, rfl⟩
  set a := rep (φ h)
  have haφ : φ a = φ h := hrepφ _ hq
  have hV' : gtransl a V = gtransl h V :=
    vanish_injOn (isZClosed_gtransl hV a) (isZClosed_gtransl hV h) haφ
  simp only [Set.mem_iUnion]
  refine ⟨a, Finset.mem_image.mpr ⟨φ h, (Set.Finite.mem_toFinset _).mpr hq, rfl⟩, ?_⟩
  rw [mem_gtransl]
  intro v hv
  have : v + h ∈ gtransl a V := hV' ▸ ⟨v, hv, rfl⟩
  obtain ⟨u, hu, hu'⟩ := this
  have e : h - a + v = u := by
    have := congrArg (· - a) hu'
    simp only [add_sub_cancel_right] at this
    rw [this]; abel
  rw [e]; exact hu

/-- **The zeros of Roy's ideal**: `h ∈ Z(I_G̃ + (τ_v^c Q : Q ∈ gens, v ∈ V))` implies
`h + V ⊆ Z(I_G̃ + (gens))`. -/
theorem zeros_transl_subset (gens : Set (MvPolynomial (Var d₀ d₁ m) ℂ))
    (V : Set (GPtV d₀ d₁ Ls)) :
    zeros ((IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span {Q' | ∃ Q ∈ gens, ∃ v ∈ V,
        ∃ c, Q' = τ Ls v c Q} : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) : Set _) ⊆
      {h | gtransl h V ⊆ zeros ((IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span gens :
        Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) : Set _)} := by
  intro h hh
  rintro _ ⟨v, hv, rfl⟩
  set A : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) := IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔
    Ideal.span {Q' | ∃ Q ∈ gens, ∃ v ∈ V, ∃ c, Q' = τ Ls v c Q}
  set L : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
    IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span gens
  have hle : translI Ls v L ≤ A := by
    refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, hP, c, rfl⟩
    have hL : L ≤ Ideal.comap (τ Ls v c) A := by
      refine sup_le (fun Q hQ => le_sup_left (a := IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls))
        (transl_IG v c hQ)) (Ideal.span_le.mpr fun Q hQ => ?_)
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨Q, hQ, v, hv, c, rfl⟩)
    exact hL hP
  have hz : h ∈ zeros (translI Ls v L : Set _) := fun P hP lam => hh P (hle hP) lam
  rw [zeros_translI] at hz
  change v + h ∈ _
  rw [add_comm]
  exact hz

end LSG.MEV
