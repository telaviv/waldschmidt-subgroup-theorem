import Mathlib
import LSG.Elliptic.NaturalGroupFull
import LSG.MEV.LawMap

/-!
# All eight laws are proportional (over a field of characteristic `0`, and over domains)

* **`exists_common`**: for vectors `P, Q` on `X = V(F, G)` with nonzero base parts over a field of
  characteristic `0`, there is a vector `S` such that every law `NLaw i j k` at `(P, Q)` **and at
  `(Q, P)`** is a multiple of `S` (the spike's configuration table: `NLaw_ptAff`, `NLaw_dbl`,
  `NLaw_neg`, `NLaw_ptO_left/right`, `NLaw_ptO_ptO`; the sum is symmetric).
* `lawsAt g₂ g₃ P Q`: the sixteen vectors `NLaw i j k P Q`, `NLaw i j k Q P`.
* **`nlaw_cross`**: over a domain of characteristic `0` (via its fraction field), any two members
  `A, B` of `lawsAt` satisfy `A l · B l' = B l · A l'` (they are proportional). This replaces the
  abelian `lawc_cross`; used with the domains `R⟦z⟧`.
-/

open LSG.Elliptic

namespace LSG.MEV

/-! ### Over a field -/

section Field

variable {K : Type*} [Field K] [CharZero K] {g₂ g₃ : K}

theorem slopeA_comm (x₁ y₁ x₂ y₂ : K) : slopeA x₂ y₂ x₁ y₁ = slopeA x₁ y₁ x₂ y₂ := by
  unfold slopeA
  rw [← neg_sub y₁, ← neg_sub x₁, neg_div_neg_eq]

theorem addXA_comm (x₁ y₁ x₂ y₂ : K) : addXA x₂ y₂ x₁ y₁ = addXA x₁ y₁ x₂ y₂ := by
  unfold addXA; rw [slopeA_comm]; ring

theorem addYA_comm {x₁ y₁ x₂ y₂ : K} (hx : x₁ ≠ x₂) :
    addYA x₂ y₂ x₁ y₁ = addYA x₁ y₁ x₂ y₂ := by
  unfold addYA
  rw [addXA_comm, slopeA_comm]
  have := slopeA_mul (y₁ := y₁) (y₂ := y₂) hx
  linear_combination -this

/-- The common vector for normalized shapes. -/
theorem exists_common_shape {P Q : Fin 5 → K}
    (hP : (∃ x y t, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ ∧ P = ptAff x y t) ∨ ∃ w, P = ptO w)
    (hQ : (∃ x y t, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ ∧ Q = ptAff x y t) ∨ ∃ w, Q = ptO w) :
    ∃ S : Fin 5 → K, ∀ i j k : Fin 2, (∃ a : K, NLaw g₂ g₃ i j k P Q = a • S) ∧
      (∃ a : K, NLaw g₂ g₃ i j k Q P = a • S) := by
  rcases hP with ⟨x₁, y₁, t₁, h₁, rfl⟩ | ⟨w₁, rfl⟩ <;> rcases hQ with ⟨x₂, y₂, t₂, h₂, rfl⟩ | ⟨w₂, rfl⟩
  · by_cases hx : x₁ = x₂
    · subst hx
      by_cases hneg : y₂ = -y₁
      · subst hneg
        refine ⟨ptO (t₁ + t₂), fun i j k => ⟨⟨_, NLaw_neg h₁ t₁ t₂ i j k⟩, ?_⟩⟩
        have h₁' : (-y₁) ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃ := by linear_combination h₁
        have := NLaw_neg h₁' t₂ t₁ i j k
        rw [neg_neg, add_comm] at this
        exact ⟨_, this⟩
      · have hy : (y₂ - y₁) * (y₂ + y₁) = 0 := by linear_combination h₂ - h₁
        have hy' : y₂ = y₁ := by
          rcases mul_eq_zero.mp hy with hy | hy
          · exact sub_eq_zero.mp hy
          · exact absurd (by linear_combination hy) hneg
        subst hy'
        have h0 : y₂ ≠ 0 := fun h0 => hneg (by rw [h0, neg_zero])
        refine ⟨ptAff (dblX g₂ x₁ y₂) (dblY g₂ x₁ y₂) (t₁ + t₂ - dblSlope g₂ x₁ y₂ / 2),
          fun i j k => ⟨⟨_, NLaw_dbl h₁ h0 t₁ t₂ i j k⟩, ?_⟩⟩
        have := NLaw_dbl h₁ h0 t₂ t₁ i j k
        rw [add_comm t₂] at this
        exact ⟨_, this⟩
    · refine ⟨ptAff (addXA x₁ y₁ x₂ y₂) (addYA x₁ y₁ x₂ y₂) (t₁ + t₂ - slopeA x₁ y₁ x₂ y₂ / 2),
        fun i j k => ⟨⟨_, NLaw_ptAff h₁ h₂ hx i j k⟩, ?_⟩⟩
      have := NLaw_ptAff h₂ h₁ (Ne.symm hx) i j k (t₁ := t₂) (t₂ := t₁)
      rw [addXA_comm, addYA_comm hx, slopeA_comm, add_comm t₂] at this
      exact ⟨_, this⟩
  · exact ⟨ptAff x₁ y₁ (t₁ + w₂), fun i j k =>
      ⟨⟨_, NLaw_ptO_right h₁ t₁ w₂ i j k⟩, ⟨_, NLaw_ptO_left h₁ w₂ t₁ i j k⟩⟩⟩
  · exact ⟨ptAff x₂ y₂ (t₂ + w₁), fun i j k =>
      ⟨⟨_, NLaw_ptO_left h₂ w₁ t₂ i j k⟩, ⟨_, NLaw_ptO_right h₂ t₂ w₁ i j k⟩⟩⟩
  · refine ⟨ptO (w₁ + w₂), fun i j k => ⟨⟨_, NLaw_ptO_ptO w₁ w₂ i j k⟩, ?_⟩⟩
    have := NLaw_ptO_ptO (g₂ := g₂) (g₃ := g₃) w₂ w₁ i j k
    rw [add_comm w₂] at this
    exact ⟨_, this⟩

theorem shape_of {P : Fin 5 → K} (hF : Fn g₂ g₃ P = 0) (hG : Gn P = 0) (hP : Pe P ≠ 0) :
    ∃ u : K, ∃ P' : Fin 5 → K, P = u • P' ∧
      ((∃ x y t, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ ∧ P' = ptAff x y t) ∨ ∃ w, P' = ptO w) := by
  rcases eq_ptAff_or_ptO two_ne_zero hF hG hP with ⟨-, he, hc⟩ | ⟨-, -, he⟩
  · exact ⟨_, _, he, Or.inl ⟨_, _, _, hc, rfl⟩⟩
  · exact ⟨_, _, he, Or.inr ⟨_, rfl⟩⟩

/-- **All laws in both orders are multiples of one vector.** -/
theorem exists_common {P Q : Fin 5 → K} (hFP : Fn g₂ g₃ P = 0) (hGP : Gn P = 0) (hP : Pe P ≠ 0)
    (hFQ : Fn g₂ g₃ Q = 0) (hGQ : Gn Q = 0) (hQ : Pe Q ≠ 0) :
    ∃ S : Fin 5 → K, ∀ i j k : Fin 2, (∃ a : K, NLaw g₂ g₃ i j k P Q = a • S) ∧
      (∃ a : K, NLaw g₂ g₃ i j k Q P = a • S) := by
  obtain ⟨u, P', rfl, hP'⟩ := shape_of hFP hGP hP
  obtain ⟨v, Q', rfl, hQ'⟩ := shape_of hFQ hGQ hQ
  obtain ⟨S, hS⟩ := exists_common_shape hP' hQ'
  refine ⟨S, fun i j k => ⟨?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := (hS i j k).1
    exact ⟨(u * v) ^ 3 * a, by rw [NLaw_smul, ha, smul_smul]⟩
  · obtain ⟨a, ha⟩ := (hS i j k).2
    exact ⟨(v * u) ^ 3 * a, by rw [NLaw_smul, ha, smul_smul]⟩

end Field

/-! ### Over a domain -/

/-- The sixteen law values at `(P, Q)` and `(Q, P)`. -/
def lawsAt {T : Type*} [CommRing T] (g₂ g₃ : T) (P Q : Fin 5 → T) : Set (Fin 5 → T) :=
  {A | ∃ i j k : Fin 2, A = NLaw g₂ g₃ i j k P Q ∨ A = NLaw g₂ g₃ i j k Q P}

theorem nlaw_cross_field {K : Type*} [Field K] [CharZero K] {g₂ g₃ : K} {P Q : Fin 5 → K}
    (hFP : Fn g₂ g₃ P = 0) (hGP : Gn P = 0) (hP : Pe P ≠ 0)
    (hFQ : Fn g₂ g₃ Q = 0) (hGQ : Gn Q = 0) (hQ : Pe Q ≠ 0) {A B : Fin 5 → K}
    (hA : A ∈ lawsAt g₂ g₃ P Q) (hB : B ∈ lawsAt g₂ g₃ P Q) (l l' : Fin 5) :
    A l * B l' = B l * A l' := by
  obtain ⟨S, hS⟩ := exists_common hFP hGP hP hFQ hGQ hQ
  have key : ∀ C ∈ lawsAt g₂ g₃ P Q, ∃ a : K, C = a • S := by
    rintro C ⟨i, j, k, rfl | rfl⟩
    · exact (hS i j k).1
    · exact (hS i j k).2
  obtain ⟨a, rfl⟩ := key A hA
  obtain ⟨b, rfl⟩ := key B hB
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem map_mem_lawsAt {T T' : Type*} [CommRing T] [CommRing T'] (φ : T →+* T') {g₂ g₃ : T}
    {P Q A : Fin 5 → T} (hA : A ∈ lawsAt g₂ g₃ P Q) :
    (φ ∘ A) ∈ lawsAt (φ g₂) (φ g₃) (φ ∘ P) (φ ∘ Q) := by
  obtain ⟨i, j, k, rfl | rfl⟩ := hA
  · exact ⟨i, j, k, Or.inl (funext fun l => NLaw_map φ g₂ g₃ i j k P Q l)⟩
  · exact ⟨i, j, k, Or.inr (funext fun l => NLaw_map φ g₂ g₃ i j k Q P l)⟩

/-- **Cross identity over a domain of characteristic `0`.** -/
theorem nlaw_cross {T : Type*} [CommRing T] [IsDomain T] [CharZero T] {g₂ g₃ : T}
    {P Q : Fin 5 → T} (hFP : Fn g₂ g₃ P = 0) (hGP : Gn P = 0) (hP : Pe P ≠ 0)
    (hFQ : Fn g₂ g₃ Q = 0) (hGQ : Gn Q = 0) (hQ : Pe Q ≠ 0) {A B : Fin 5 → T}
    (hA : A ∈ lawsAt g₂ g₃ P Q) (hB : B ∈ lawsAt g₂ g₃ P Q) (l l' : Fin 5) :
    A l * B l' = B l * A l' := by
  set φ := algebraMap T (FractionRing T)
  have hinj : Function.Injective φ := IsFractionRing.injective T (FractionRing T)
  have : CharZero (FractionRing T) := charZero_of_injective_ringHom hinj
  have hne : ∀ {V : Fin 5 → T}, Pe V ≠ 0 → Pe (φ ∘ V) ≠ 0 := fun {V} hV h => hV (by
    funext i
    have := congrFun h i
    simp only [Pe_apply, Function.comp_apply, Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff φ hinj).mp this)
  have hF : ∀ {V : Fin 5 → T}, Fn g₂ g₃ V = 0 → Fn (φ g₂) (φ g₃) (φ ∘ V) = 0 := fun {V} h => by
    rw [← Fn_map, h, map_zero]
  have hG : ∀ {V : Fin 5 → T}, Gn V = 0 → Gn (φ ∘ V) = 0 := fun {V} h => by
    rw [← Gn_map, h, map_zero]
  have := nlaw_cross_field (hF hFP) (hG hGP) (hne hP) (hF hFQ) (hG hGQ) (hne hQ)
    (map_mem_lawsAt φ hA) (map_mem_lawsAt φ hB) l l'
  simp only [Function.comp_apply, ← map_mul] at this
  exact hinj this

end LSG.MEV
