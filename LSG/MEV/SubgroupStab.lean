import Mathlib
import LSG.MEV.Transl

/-!
# Stabilisers of Zariski-closed sets in `G̃ = G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮`

Port of `LSG.ME.StabG` to the vector-extension model `LSG.MEV` (points `GPtV`, cone model of
`E^♮` in `ℙ⁴`). For `V ⊆ G̃(ℂ)`, `stabG V = {h | h + V ⊆ V}`.

* `IsZClosed V`: `V` is the (cone) zero set of some polynomials; `zeros_vanish`, `vanish_injOn`,
  `isZClosed_iInter`, `zcl` (Zariski closure).
* `isZClosed_gtransl`: translates of Zariski-closed sets are Zariski closed (`zeros_translI`).
* **`gtransl_eq_of_subset`**: `h + V ⊆ V` implies `h + V = V` (Noetherianity).
* **`stabG_isSubgroup`**, **`stabG_eq_zeros`**, **`isZClosed_stabG`**: the stabiliser of a
  Zariski-closed set is a Zariski-closed subgroup.
* **`zcl_isSubgroup`**: the Zariski closure of a subgroup is a subgroup.
-/

open MvPolynomial

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- `V` is **Zariski closed**: the (cone) zero set of a set of polynomials. -/
def IsZClosed (V : Set (GPtV d₀ d₁ Ls)) : Prop :=
  ∃ S : Set (MvPolynomial (Var d₀ d₁ m) ℂ), V = zeros S

theorem isZClosed_zeros (S : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    IsZClosed (zeros S : Set (GPtV d₀ d₁ Ls)) := ⟨S, rfl⟩

theorem subset_zeros_vanish (V : Set (GPtV d₀ d₁ Ls)) :
    V ⊆ zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) :=
  fun g hg _ hP lam => mem_vanish.mp hP g hg lam

/-- A Zariski-closed set is the zero set of its vanishing ideal. -/
theorem zeros_vanish {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) :
    zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) = V := by
  refine le_antisymm ?_ (subset_zeros_vanish V)
  obtain ⟨S, rfl⟩ := hV
  intro g hg P hP lam
  exact hg P (mem_vanish.mpr fun g' hg' lam' => hg' P hP lam') lam

theorem vanish_injOn {V V' : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hV' : IsZClosed V')
    (h : vanish V = vanish V') : V = V' := by
  rw [← zeros_vanish hV, ← zeros_vanish hV', h]

/-- The intersection of Zariski-closed sets is Zariski closed. -/
theorem isZClosed_iInter {ι : Sort*} {V : ι → Set (GPtV d₀ d₁ Ls)} (hV : ∀ i, IsZClosed (V i)) :
    IsZClosed (⋂ i, V i) := by
  choose S hS using hV
  refine ⟨⋃ i, S i, ?_⟩
  ext g
  simp only [Set.mem_iInter, hS, zeros, Set.mem_ofPred_eq, Set.mem_iUnion, forall_exists_index]
  exact ⟨fun h P i hP lam => h i P hP lam, fun h i P hP lam => h P i hP lam⟩

/-- The Zariski closure. -/
def zcl (S : Set (GPtV d₀ d₁ Ls)) : Set (GPtV d₀ d₁ Ls) :=
  zeros (vanish S : Set (MvPolynomial (Var d₀ d₁ m) ℂ))

theorem subset_zcl (S : Set (GPtV d₀ d₁ Ls)) : S ⊆ zcl S := subset_zeros_vanish S

theorem isZClosed_zcl (S : Set (GPtV d₀ d₁ Ls)) : IsZClosed (zcl S) := isZClosed_zeros _

theorem zcl_minimal {S V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (h : S ⊆ V) : zcl S ⊆ V := by
  rw [← zeros_vanish hV]
  intro g hg P hP lam
  exact hg P (vanish_antitone h hP) lam

theorem vanish_zcl (S : Set (GPtV d₀ d₁ Ls)) : vanish (zcl S) = vanish S :=
  le_antisymm (vanish_antitone (subset_zcl S)) fun _ hP =>
    mem_vanish.mpr fun _ hg lam => hg _ hP lam

/-! ### Translates and stabilisers -/

theorem gtransl_gtransl (a b : GPtV d₀ d₁ Ls) (E : Set (GPtV d₀ d₁ Ls)) :
    gtransl a (gtransl b E) = gtransl (b + a) E := by
  ext h; simp only [mem_gtransl, sub_add_eq_sub_sub, sub_right_comm]

theorem gtransl_zero (E : Set (GPtV d₀ d₁ Ls)) : gtransl 0 E = E := by
  ext h; simp [mem_gtransl]

theorem gtransl_mono (a : GPtV d₀ d₁ Ls) {E E' : Set (GPtV d₀ d₁ Ls)} (h : E ⊆ E') :
    gtransl a E ⊆ gtransl a E' := Set.image_mono h

/-- The **stabiliser** `{h | h + V ⊆ V}`. -/
def stabG (V : Set (GPtV d₀ d₁ Ls)) : Set (GPtV d₀ d₁ Ls) := {h | ∀ v ∈ V, h + v ∈ V}

theorem mem_stabG_iff {V : Set (GPtV d₀ d₁ Ls)} {h : GPtV d₀ d₁ Ls} :
    h ∈ stabG V ↔ gtransl h V ⊆ V := by
  constructor
  · rintro hh _ ⟨v, hv, rfl⟩; show v + h ∈ V; rw [add_comm]; exact hh v hv
  · intro hh v hv; rw [add_comm]; exact hh ⟨v, hv, rfl⟩

/-- **Translates of Zariski-closed sets are Zariski closed.** -/
theorem isZClosed_gtransl {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (a : GPtV d₀ d₁ Ls) :
    IsZClosed (gtransl a V) := by
  refine ⟨(translI Ls (-a) (vanish V) : Set _), ?_⟩
  rw [zeros_translI, zeros_vanish hV]
  ext h
  simp [mem_gtransl, sub_eq_add_neg]

/-- **`h + V ⊆ V` implies `h + V = V`** for a Zariski-closed `V` (the chain
`V ⊇ h + V ⊇ 2h + V ⊇ ⋯` stabilises by Noetherianity of `ℂ[Var]`). -/
theorem gtransl_eq_of_subset {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    {h : GPtV d₀ d₁ Ls} (hsub : gtransl h V ⊆ V) : gtransl h V = V := by
  classical
  let Vn : ℕ → Set (GPtV d₀ d₁ Ls) := fun n => gtransl (n • h) V
  have hVn : ∀ n, IsZClosed (Vn n) := fun n => isZClosed_gtransl hV _
  have hanti : ∀ n, Vn (n + 1) ⊆ Vn n := by
    intro n
    simp only [Vn, succ_nsmul, ← gtransl_gtransl]
    rw [gtransl_gtransl, add_comm, ← gtransl_gtransl]
    exact gtransl_mono _ hsub
  have hmono : Monotone fun n => vanish (Vn n) :=
    monotone_nat_of_le_succ fun n => vanish_antitone (hanti n)
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ))
    ⟨fun n => vanish (Vn n), hmono⟩
  have heq : Vn n = Vn (n + 1) :=
    vanish_injOn (hVn n) (hVn (n + 1)) (hn (n + 1) (Nat.le_succ n))
  have := congrArg (gtransl (-(n • h))) heq
  simp only [Vn, gtransl_gtransl, add_neg_cancel, gtransl_zero, succ_nsmul,
    add_neg_cancel_comm] at this
  exact this.symm

/-- **The stabiliser of a Zariski-closed set is a subgroup.** -/
theorem stabG_isSubgroup {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) :
    IsSubgroupG (stabG V) where
  zero_mem v hv := by rwa [zero_add]
  add_mem g hg h hh v hv := by rw [add_assoc]; exact hg _ (hh v hv)
  neg_mem g hg v hv := by
    have heq := gtransl_eq_of_subset hV (mem_stabG_iff.mp hg)
    rw [← heq] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    show -g + (u + g) ∈ V
    rwa [add_comm u, neg_add_cancel_left]

variable (Ls) in
/-- The ideal cutting out the stabiliser of `zeros J`. -/
noncomputable def stabIdeal (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  Ideal.span {Q | ∃ v ∈ (zeros (J : Set _) : Set (GPtV d₀ d₁ Ls)), Q ∈ translI Ls v J}

/-- **The stabiliser is Zariski closed**: `stabG (zeros J) = zeros (stabIdeal J)`. -/
theorem stabG_eq_zeros (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    stabG (zeros (J : Set _) : Set (GPtV d₀ d₁ Ls)) = zeros (stabIdeal Ls J : Set _) := by
  ext h
  rw [stabIdeal, mem_zeros_span]
  constructor
  · rintro hh Q ⟨v, hv, hQ⟩ lam
    have hz : h ∈ zeros (translI Ls v J : Set _) := by
      rw [zeros_translI]; exact hh v hv
    exact hz Q hQ lam
  · intro hh v hv
    have hz : h ∈ zeros (translI Ls v J : Set _) := fun Q hQ lam => hh Q ⟨v, hv, hQ⟩ lam
    rw [zeros_translI] at hz
    exact hz

theorem isZClosed_stabG {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) : IsZClosed (stabG V) := by
  rw [← zeros_vanish hV, stabG_eq_zeros]
  exact isZClosed_zeros _

/-- For an ideal `J` (e.g. a prime `p ⊇ I_G̃`): the stabiliser of `zeros J` is a Zariski-closed
subgroup. -/
theorem stabG_zeros_isSubgroup (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    IsSubgroupG (stabG (zeros (J : Set _) : Set (GPtV d₀ d₁ Ls))) ∧
      IsZClosed (stabG (zeros (J : Set _) : Set (GPtV d₀ d₁ Ls))) :=
  ⟨stabG_isSubgroup (isZClosed_zeros _), isZClosed_stabG (isZClosed_zeros _)⟩

/-! ### Closures of subgroups -/

/-- Translation by `a` maps `zcl S` onto `zcl (S + a)`. -/
theorem gtransl_zcl (a : GPtV d₀ d₁ Ls) (S : Set (GPtV d₀ d₁ Ls)) :
    gtransl a (zcl S) = zcl (gtransl a S) := by
  apply le_antisymm
  · -- `zcl (S + a) − a` is closed and contains `S`
    have hc : IsZClosed (gtransl (-a) (zcl (gtransl a S))) :=
      isZClosed_gtransl (isZClosed_zcl _) _
    have h1 : zcl S ⊆ gtransl (-a) (zcl (gtransl a S)) := by
      refine zcl_minimal hc fun s hs => ?_
      rw [mem_gtransl, sub_neg_eq_add]
      exact subset_zcl _ ⟨s, hs, rfl⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := h1 hy
    rw [mem_gtransl, sub_neg_eq_add] at this
    exact this
  · exact zcl_minimal (isZClosed_gtransl (isZClosed_zcl S) a) (gtransl_mono a (subset_zcl S))

/-- **The Zariski closure of a subgroup is a subgroup.** -/
theorem zcl_isSubgroup {S : Set (GPtV d₀ d₁ Ls)} (hS : IsSubgroupG S) : IsSubgroupG (zcl S) := by
  -- `S ⊆ stabG (zcl S)` and then `zcl S ⊆ stabG (zcl S)`
  have h1 : S ⊆ stabG (zcl S) := by
    intro s hs
    rw [mem_stabG_iff, gtransl_zcl]
    refine zcl_minimal (isZClosed_zcl S) fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact subset_zcl S (hS.add_mem _ hy _ hs)
  have h2 : zcl S ⊆ stabG (zcl S) := zcl_minimal (isZClosed_stabG (isZClosed_zcl S)) h1
  have hst := stabG_isSubgroup (isZClosed_zcl S)
  refine ⟨subset_zcl S hS.zero_mem, fun g hg h hh => h2 hg h hh, fun g hg => ?_⟩
  have := hst.neg_mem g (h2 hg)
  simpa using this _ (subset_zcl S hS.zero_mem)

end LSG.MEV
