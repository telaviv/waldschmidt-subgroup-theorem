import Mathlib
import LSG.ME.Transl

/-!
# Stabilisers of Zariski-closed sets (STAGE2 §5, item 1)

For a set `V ⊆ G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, `stabG V = {h | h + V ⊆ V}`.

* `IsZClosed V`: `V` is the zero set (in the cone sense of `LSG.ME.zeros`) of some polynomials.
* `zeros_vanish`: for `V` Zariski closed, `zeros (vanish V) = V`.
* `isZClosed_gtransl`: translates of Zariski-closed sets are Zariski closed (via `zeros_translI`).
* **`gtransl_eq_of_subset`**: if `V` is Zariski closed and `h + V ⊆ V`, then `h + V = V`
  (the chain `V ⊇ h + V ⊇ 2h + V ⊇ ⋯` stabilises since `K[Var]` is Noetherian, and translation is
  a bijection of `G`). No primality or dimension argument is needed (unlike StrongSix, where the
  argument went through Hilbert dimensions of primes).
* **`stabG_isSubgroup`**: the stabiliser of a Zariski-closed set is a subgroup.
* **`stabG_eq_zeros`**: `stabG (zeros J) = zeros (stabIdeal J)`, with
  `stabIdeal J = span (⋃_{v ∈ zeros J} translI v J)`; in particular it is Zariski closed.

All of this holds for every ideal `J` (in particular for a prime `p ⊇ I_G`), `K` algebraically
closed with `2 ≠ 0`, nonsingular curves.
-/

universe u

open MvPolynomial

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-- `V` is **Zariski closed**: the (cone) zero set of a set of polynomials. -/
def IsZClosed (V : Set (GPt K d₀ d₁ g₂ g₃)) : Prop :=
  ∃ S : Set (MvPolynomial (Var d₀ d₁ m) K), V = zeros S

theorem isZClosed_zeros (S : Set (MvPolynomial (Var d₀ d₁ m) K)) :
    IsZClosed (zeros S : Set (GPt K d₀ d₁ g₂ g₃)) := ⟨S, rfl⟩

theorem subset_zeros_vanish (V : Set (GPt K d₀ d₁ g₂ g₃)) :
    V ⊆ zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ m) K)) :=
  fun g hg _ hP lam => mem_vanish.mp hP g hg lam

/-- A Zariski-closed set is the zero set of its vanishing ideal. -/
theorem zeros_vanish {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) :
    zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ m) K)) = V := by
  refine le_antisymm ?_ (subset_zeros_vanish V)
  obtain ⟨S, rfl⟩ := hV
  intro g hg P hP lam
  exact hg P (mem_vanish.mpr fun g' hg' lam' => hg' P hP lam') lam

theorem vanish_injOn {V V' : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hV' : IsZClosed V')
    (h : vanish V = vanish V') : V = V' := by
  rw [← zeros_vanish hV, ← zeros_vanish hV', h]

/-- The intersection of Zariski-closed sets is Zariski closed. -/
theorem isZClosed_iInter {ι : Sort*} {V : ι → Set (GPt K d₀ d₁ g₂ g₃)} (hV : ∀ i, IsZClosed (V i)) :
    IsZClosed (⋂ i, V i) := by
  choose S hS using hV
  refine ⟨⋃ i, S i, ?_⟩
  ext g
  simp only [Set.mem_iInter, hS, zeros, Set.mem_ofPred_eq, Set.mem_iUnion, forall_exists_index]
  exact ⟨fun h P i hP lam => h i P hP lam, fun h i P hP lam => h P i hP lam⟩

section Group

variable [DecidableEq K]

theorem gtransl_gtransl (a b : GPt K d₀ d₁ g₂ g₃) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    gtransl a (gtransl b E) = gtransl (b + a) E := by
  ext h; simp only [mem_gtransl, sub_add_eq_sub_sub, sub_right_comm]

theorem gtransl_zero (E : Set (GPt K d₀ d₁ g₂ g₃)) : gtransl 0 E = E := by
  ext h; simp [mem_gtransl]

theorem gtransl_mono (a : GPt K d₀ d₁ g₂ g₃) {E E' : Set (GPt K d₀ d₁ g₂ g₃)} (h : E ⊆ E') :
    gtransl a E ⊆ gtransl a E' := Set.image_mono h

/-- The **stabiliser** `{h | h + V ⊆ V}`. -/
def stabG (V : Set (GPt K d₀ d₁ g₂ g₃)) : Set (GPt K d₀ d₁ g₂ g₃) := {h | ∀ v ∈ V, h + v ∈ V}

theorem mem_stabG_iff {V : Set (GPt K d₀ d₁ g₂ g₃)} {h : GPt K d₀ d₁ g₂ g₃} :
    h ∈ stabG V ↔ gtransl h V ⊆ V := by
  constructor
  · rintro hh _ ⟨v, hv, rfl⟩; show v + h ∈ V; rw [add_comm]; exact hh v hv
  · intro hh v hv; rw [add_comm]; exact hh ⟨v, hv, rfl⟩

variable (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Translates of Zariski-closed sets are Zariski closed.** -/
theorem isZClosed_gtransl [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    (a : GPt K d₀ d₁ g₂ g₃) : IsZClosed (gtransl a V) := by
  refine ⟨(translI g₂ g₃ (-a) (vanish V) : Set _), ?_⟩
  rw [zeros_translI h2 hΔ, zeros_vanish hV]
  ext h
  simp [mem_gtransl, sub_eq_add_neg]

/-- **`h + V ⊆ V` implies `h + V = V`** for a Zariski-closed `V`: the descending chain
`V ⊇ h + V ⊇ 2h + V ⊇ ⋯` of Zariski-closed sets stabilises (Noetherianity of `K[Var]`). -/
theorem gtransl_eq_of_subset [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V)
    {h : GPt K d₀ d₁ g₂ g₃} (hsub : gtransl h V ⊆ V) : gtransl h V = V := by
  classical
  let Vn : ℕ → Set (GPt K d₀ d₁ g₂ g₃) := fun n => gtransl (n • h) V
  have hVn : ∀ n, IsZClosed (Vn n) := fun n => isZClosed_gtransl h2 hΔ hV _
  have hanti : ∀ n, Vn (n + 1) ⊆ Vn n := by
    intro n
    simp only [Vn, succ_nsmul, ← gtransl_gtransl]
    rw [gtransl_gtransl, add_comm, ← gtransl_gtransl]
    exact gtransl_mono _ hsub
  have hmono : Monotone fun n => vanish (Vn n) :=
    monotone_nat_of_le_succ fun n => vanish_antitone (hanti n)
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial (Var d₀ d₁ m) K) (MvPolynomial (Var d₀ d₁ m) K))
    ⟨fun n => vanish (Vn n), hmono⟩
  have heq : Vn n = Vn (n + 1) :=
    vanish_injOn (hVn n) (hVn (n + 1)) (hn (n + 1) (Nat.le_succ n))
  have := congrArg (gtransl (-(n • h))) heq
  simp only [Vn, gtransl_gtransl, add_neg_cancel, gtransl_zero, succ_nsmul,
    add_neg_cancel_comm] at this
  exact this.symm

/-- **The stabiliser of a Zariski-closed set is a subgroup.** -/
theorem stabG_isSubgroup [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) :
    IsSubgroupG (stabG V) where
  zero_mem v hv := by rwa [zero_add]
  add_mem g hg h hh v hv := by rw [add_assoc]; exact hg _ (hh v hv)
  neg_mem g hg v hv := by
    have heq := gtransl_eq_of_subset h2 hΔ hV (mem_stabG_iff.mp hg)
    rw [← heq] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    show -g + (u + g) ∈ V
    rwa [add_comm u, neg_add_cancel_left]

omit h2 hΔ in
variable (g₂ g₃) in
/-- The ideal cutting out the stabiliser of `zeros J`. -/
noncomputable def stabIdeal (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  Ideal.span {Q | ∃ v ∈ (zeros (J : Set _) : Set (GPt K d₀ d₁ g₂ g₃)), Q ∈ translI g₂ g₃ v J}

/-- **The stabiliser is Zariski closed**: `stabG (zeros J) = zeros (stabIdeal J)`. -/
theorem stabG_eq_zeros [IsAlgClosed K] (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    stabG (zeros (J : Set _) : Set (GPt K d₀ d₁ g₂ g₃)) =
      zeros (stabIdeal g₂ g₃ J : Set _) := by
  ext h
  rw [stabIdeal, mem_zeros_span]
  constructor
  · rintro hh Q ⟨v, hv, hQ⟩ lam
    have hz : h ∈ zeros (translI g₂ g₃ v J : Set _) := by
      rw [zeros_translI h2 hΔ]; exact hh v hv
    exact hz Q hQ lam
  · intro hh v hv
    have hz : h ∈ zeros (translI g₂ g₃ v J : Set _) := fun Q hQ lam => hh Q ⟨v, hv, hQ⟩ lam
    rw [zeros_translI h2 hΔ] at hz
    exact hz

theorem isZClosed_stabG [IsAlgClosed K] {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) :
    IsZClosed (stabG V) := by
  rw [← zeros_vanish hV, stabG_eq_zeros h2 hΔ]
  exact isZClosed_zeros _

/-- For a prime `p ⊇ I_G` (or any ideal): the stabiliser of `zeros p` is a Zariski-closed
subgroup. -/
theorem stabG_zeros_isSubgroup [IsAlgClosed K] (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    IsSubgroupG (stabG (zeros (J : Set _) : Set (GPt K d₀ d₁ g₂ g₃))) ∧
      IsZClosed (stabG (zeros (J : Set _) : Set (GPt K d₀ d₁ g₂ g₃))) :=
  ⟨stabG_isSubgroup h2 hΔ (isZClosed_zeros _), isZClosed_stabG h2 hΔ (isZClosed_zeros _)⟩

end Group

end LSG.ME
