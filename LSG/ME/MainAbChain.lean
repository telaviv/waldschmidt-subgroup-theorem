import Mathlib
import LSG.ME.Chain2
import LSG.ME.WustCoset
import StrongSix.M2.Component

/-!
# Relevant radicals, the relevant pigeonhole and Roy's component step (STAGE2 §11)

**Why relevant radicals.** Every generator of `L_r` (chain v2) and of Roy's ideal `A₂` is
homogeneous of positive degree in every elliptic block (`P` is, and `phOp`, `τ` preserve this), so
the affine cone locus `{X_k = 0} × (cone over the other factors)` of dimension
`d₀ + d₁ + 2m − 2` lies in their affine zero sets: the Hilbert dimensions `hdim L_r` are
dominated by these *irrelevant* components, and a prime `p ⊇ L_{r+1}` of maximal `hdim` may have
`zeros p = ∅` (STAGE2 §11). Everything here is therefore phrased with the **relevant radical**
`relI L = I(Z(L))` (the polynomials vanishing at every cone representative of every common zero),
whose minimal primes are relevant (`vanish (zeros p) = p`).

* `relI`, `le_relI`, `relI_mono`, `relI_le_vanish_zero`.
* **`exists_flat_rel`**: some `r < d₀ + d₁ + m` has `hdim (relI L_{r+1}) = hdim (relI L_r)`.
* **`exists_relevant_prime`**: a prime `p ⊇ relI L` with `hdim p = hdim (relI L)` and
  `vanish (zeros p) = p`.
* **`component_rel`** (Roy §8.4.1): for `V` irreducible Zariski-closed with
  `hdim I(V) = hdim (relI L)`, the set `{h | h + V ⊆ Z(L)}` is covered by finitely many cosets of
  `stabG V`.
* **`zeros_transl_subset`**: the zeros of `A = I_G + (τ_v^c Q : Q ∈ gens, v ∈ V)` satisfy
  `h + V ⊆ Z(I_G + (gens))`.
-/

universe u

open MvPolynomial
open StrongSix.M2 (FLE hdata hdata_le_of_le)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

variable (g₂ g₃) in
/-- The **relevant radical** `I(Z(L))`. -/
def relI (L : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  vanish (zeros (L : Set _) : Set (GPt K d₀ d₁ g₂ g₃))

theorem le_relI (L : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : L ≤ relI g₂ g₃ L :=
  fun P hP => mem_vanish.mpr fun _ hg lam => hg P hP lam

theorem relI_mono {L L' : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (h : L ≤ L') :
    relI g₂ g₃ L ≤ relI g₂ g₃ L' :=
  vanish_antitone fun _ hg P hP lam => hg P (h hP) lam

theorem relI_le_vanish_zero {L : Ideal (MvPolynomial (Var d₀ d₁ m) K)}
    (h : L ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃))) :
    relI g₂ g₃ L ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) :=
  vanish_antitone (Set.singleton_subset_iff.mpr (mem_zeros_iff_le_vanish.mpr h))

/-! ### The relevant pigeonhole -/

section Flat

variable [DecidableEq K] [CharZero K] [IsAlgClosed K]
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
  {W : Submodule K (LieE K d₀ d₁ m)} {S : Finset (GPt K d₀ d₁ g₂ g₃)}
  {P : MvPolynomial (Var d₀ d₁ m) K} {T : ℕ}
include hΔ hD

/-- **Pigeonhole for the relevant radicals of the chain.** -/
theorem exists_flat_rel {d : Fin m → ℕ} (hP : IsHomE P d) (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S)
    (hPI : P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
    (hlast : Lr2 g₂ g₃ W S P T (d₀ + d₁ + m) ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃))) :
    ∃ r < d₀ + d₁ + m,
      (hdata blk D K (relI g₂ g₃ (Lr2 g₂ g₃ W S P T (r + 1)))).1 =
        (hdata blk D K (relI g₂ g₃ (Lr2 g₂ g₃ W S P T r))).1 := by
  set J : ℕ → Ideal (MvPolynomial (Var d₀ d₁ m) K) := fun r => relI g₂ g₃ (Lr2 g₂ g₃ W S P T r)
  have hlastJ : J (d₀ + d₁ + m) ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) :=
    relI_le_vanish_zero hlast
  have hlast' : J (d₀ + d₁ + m) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlastJ
  have hmono : ∀ r, J r ≤ J (r + 1) := fun r => relI_mono (Lr2_mono hS r)
  have hmono' : ∀ {r r'}, r ≤ r' → J r ≤ J r' := by
    intro r r' h
    induction r', h using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact ih.trans (hmono n)
  have hne : ∀ r ≤ d₀ + d₁ + m, J r ≠ ⊤ := fun r hr => ne_top_of_le_ne_top hlast' (hmono' hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d₀ + d₁ + m, (hdata blk D K (J (r + 1))).1 < (hdata blk D K (J r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D K (hmono r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d₀ + d₁ + m, (hdata blk D K (J r)).1 + r ≤ (hdata blk D K (J 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have hL0 : Lr2 g₂ g₃ W S P T 0 ≠ ⊤ :=
    ne_top_of_le_ne_top (hne 0 (Nat.zero_le _)) (le_relI _)
  have h0 := hdim_Lr2_zero_lt hΔ D hD hP hPI hL0
  have h0' : (hdata blk D K (J 0)).1 ≤ (hdata blk D K (Lr2 g₂ g₃ W S P T 0)).1 := by
    change (hdata blk D K (relI g₂ g₃ (Lr2 g₂ g₃ W S P T 0))).1 ≤ _
    rcases hdata_le_of_le blk D K (le_relI (g₂ := g₂) (g₃ := g₃) (Lr2 g₂ g₃ W S P T 0))
      (hne 0 (Nat.zero_le _)) with h | ⟨h, -⟩ <;> omega
  have h1 := hdec (d₀ + d₁ + m) le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlastJ
  omega

end Flat

/-! ### A relevant prime of maximal dimension -/

/-- **A relevant prime over `relI L` of the same Hilbert dimension.** -/
theorem exists_relevant_prime [IsAlgClosed K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (hne : relI g₂ g₃ L ≠ ⊤) :
    ∃ p : Ideal (MvPolynomial (Var d₀ d₁ m) K), p.IsPrime ∧ relI g₂ g₃ L ≤ p ∧
      (hdata blk D K p).1 = (hdata blk D K (relI g₂ g₃ L)).1 ∧
      vanish (zeros (p : Set _) : Set (GPt K d₀ d₁ g₂ g₃)) = p := by
  obtain ⟨p, hp, hJp, hdim⟩ := StrongSix.M2.exists_prime_hdim blk D hD hne
  have := hp
  have hmin := StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD hJp hdim
  obtain ⟨ps, hps, hcov⟩ := exists_components (g₂ := g₂) (g₃ := g₃) (d₀ := d₀) (d₁ := d₁)
    (isZClosed_zeros (L : Set (MvPolynomial (Var d₀ d₁ m) K)))
  obtain ⟨p', hp'ps, hp'p⟩ := hcov p hp hJp
  obtain ⟨hp'pr, hJp', hp'v⟩ := hps p' hp'ps
  have he : p' = p := le_antisymm hp'p (hmin.2 ⟨hp'pr, hJp'⟩ hp'p)
  subst he
  exact ⟨p', hp, hJp, hdim, hp'v⟩

/-! ### Roy's component step -/

section Comp

variable [DecidableEq K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Roy's component step** (relevant form): if `V` is irreducible Zariski-closed with
`hdim I(V) = hdim (relI L)`, the translates `h + V ⊆ Z(L)` are finitely many, so
`{h | h + V ⊆ Z(L)}` is covered by finitely many cosets of `stabG V`. -/
theorem component_rel (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) K)} {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime)
    (hdim : (hdata blk D K (vanish V)).1 = (hdata blk D K (relI g₂ g₃ L)).1) :
    ∃ R : Finset (GPt K d₀ d₁ g₂ g₃),
      {h | gtransl h V ⊆ zeros (L : Set _)} ⊆ ⋃ a ∈ R, gtransl a (stabG V) := by
  classical
  have hVne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top (vanish_empty' (g₂ := g₂) (g₃ := g₃) (d₀ := d₀) (d₁ := d₁))
  set Z := {h | gtransl h V ⊆ zeros (L : Set (MvPolynomial (Var d₀ d₁ m) K))}
  let φ : GPt K d₀ d₁ g₂ g₃ → Ideal (MvPolynomial (Var d₀ d₁ m) K) := fun h =>
    vanish (gtransl h V)
  have hmin : ∀ h ∈ Z, φ h ∈ (relI g₂ g₃ L).minimalPrimes := by
    intro h hh
    have := vanish_gtransl_isPrime h2 hΔ hV hp h
    refine StrongSix.M2.mem_minimalPrimes_of_hdim blk D hD (vanish_antitone hh) ?_
    rw [hdim_vanish_gtransl h2 hΔ D hVne h, hdim]
  have hfinM : (relI g₂ g₃ L).minimalPrimes.Finite :=
    (relI g₂ g₃ L).finite_minimalPrimes_of_isNoetherianRing
  have hfin : (φ '' Z).Finite := hfinM.subset (by rintro _ ⟨h, hh, rfl⟩; exact hmin h hh)
  have hrep : ∀ q ∈ φ '' Z, ∃ a ∈ Z, φ a = q := fun q hq => hq
  choose! rep hrepZ hrepφ using hrep
  refine ⟨hfin.toFinset.image rep, fun h hh => ?_⟩
  have hq : φ h ∈ φ '' Z := ⟨h, hh, rfl⟩
  set a := rep (φ h)
  have haφ : φ a = φ h := hrepφ _ hq
  have hV' : gtransl a V = gtransl h V :=
    vanish_injOn (isZClosed_gtransl h2 hΔ hV a) (isZClosed_gtransl h2 hΔ hV h) haφ
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

/-- **The zeros of Roy's ideal**: `h ∈ Z(I_G + (τ_v^c Q : Q ∈ gens, v ∈ V))` implies
`h + V ⊆ Z(I_G + (gens))`. -/
theorem zeros_transl_subset (gens : Set (MvPolynomial (Var d₀ d₁ m) K))
    (V : Set (GPt K d₀ d₁ g₂ g₃)) :
    zeros ((IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span {Q' | ∃ Q ∈ gens, ∃ v ∈ V, ∃ c,
        Q' = τ g₂ g₃ v c Q} : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Set _) ⊆
      {h | gtransl h V ⊆ zeros ((IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span gens :
        Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Set _)} := by
  intro h hh
  rintro _ ⟨v, hv, rfl⟩
  set A : Ideal (MvPolynomial (Var d₀ d₁ m) K) := IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔
    Ideal.span {Q' | ∃ Q ∈ gens, ∃ v ∈ V, ∃ c, Q' = τ g₂ g₃ v c Q}
  set L : Ideal (MvPolynomial (Var d₀ d₁ m) K) := IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span gens
  have hle : translI g₂ g₃ v L ≤ A := by
    refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, hP, c, rfl⟩
    have hL : L ≤ Ideal.comap (τ g₂ g₃ v c) A := by
      refine sup_le (fun Q hQ => le_sup_left (a := IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
        (transl_IG h2 v c hQ)) (Ideal.span_le.mpr fun Q hQ => ?_)
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨Q, hQ, v, hv, c, rfl⟩)
    exact hL hP
  have hz : h ∈ zeros (translI g₂ g₃ v L : Set _) := fun P hP lam => hh P (hle hP) lam
  rw [zeros_translI h2 hΔ] at hz
  change v + h ∈ _
  rw [add_comm]
  exact hz

end Comp

end LSG.ME
