/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.Model
import LSG.Jac.B6V

/-!
# M2.4b: B6 and B5 for `A_σ̄^♮` (fields `hilb_l`, `hilb_deg`, `hilb`, `lci_*`; M2.1.1–M2.1.3)

The certificates of `LSG.Jac.B6V` live in `R12 = MvPolynomial (Fin 12) ℂ` (`T₀, T₄, T₈ = 9, 10, 11`). They are
transported to `MvPolynomial (Fin 9 ⊕ Fin 3) ℂ` along `σ12 = finSumFinEquiv.symm`:
* `rename_P04V`, `rename_P08V`, `rename_P48V`: `P₀₄, P₀₈, P₄₈` are `plkGen 0 1, plkGen 0 2, plkGen 1 2`;
* **`hilbVV`** (B6, degree **41**, linear forms `hilbLV a = hilbL a ∘ finSumFinEquiv`, i.e.
  `T₀, T₄, T₈, X₀ + X₄ + X₈`), from `hilbV`;
* **`kappaVV`**: the Wronskian cocycle `X₀P₄₈ − X₄P₀₈ + X₈P₀₄ = κ_A` (`κ_A = −½X₅Q₁ − X₁Q₅ − ¾C₀`), from `kappaV`.

B5 (M2.1.2): 12 systems indexed by `(i, s) : Fin 4 × Fin 3` (through `e12`), `lciFV = lciF i ++ [the two Plückers
through the chart fc s]`, multiplier `lciSV = S_i·X_{fc s}`. `lciV_mem` uses `lciA_mem` and, for the third Plücker,
`kappaVV`; `lciV_cover` (over the `X`-variables only) is `lciA_cover · hilbA` (exponent `7 + 14`).
-/

noncomputable section

open MvPolynomial LSG.JacAn LSG.Jac LSG.JacAnV

namespace LSG.JacBlockV

open LSG.JacBlock

/-! ### The variable change `Fin 12 ≃ Fin 9 ⊕ Fin 3` -/

/-- `Fin 12 → Fin 9 ⊕ Fin 3` (`0..8 ↦ X`, `9, 10, 11 ↦ T₀, T₄, T₈`). -/
def σ12 (i : Fin 12) : Idx := finSumFinEquiv.symm i

/-- `Fin 9 ⊕ Fin 3 → Fin 12`. -/
def τ12 (i : Idx) : Fin 12 := finSumFinEquiv i

lemma σ12_τ12 (i : Idx) : σ12 (τ12 i) = i := finSumFinEquiv.symm_apply_apply i

lemma τ12_σ12 (i : Fin 12) : τ12 (σ12 i) = i := (finSumFinEquiv (m := 9) (n := 3)).apply_symm_apply i

lemma σ12_ι9 : σ12 ∘ ι9 = Sum.inl := by
  funext i; fin_cases i <;> rfl

@[simp] lemma σ12_0 : σ12 0 = Sum.inl 0 := rfl
@[simp] lemma σ12_1 : σ12 1 = Sum.inl 1 := rfl
@[simp] lemma σ12_2 : σ12 2 = Sum.inl 2 := rfl
@[simp] lemma σ12_3 : σ12 3 = Sum.inl 3 := rfl
@[simp] lemma σ12_4 : σ12 4 = Sum.inl 4 := rfl
@[simp] lemma σ12_5 : σ12 5 = Sum.inl 5 := rfl
@[simp] lemma σ12_6 : σ12 6 = Sum.inl 6 := rfl
@[simp] lemma σ12_7 : σ12 7 = Sum.inl 7 := rfl
@[simp] lemma σ12_8 : σ12 8 = Sum.inl 8 := rfl
@[simp] lemma σ12_9 : σ12 9 = Sum.inr 0 := rfl
@[simp] lemma σ12_10 : σ12 10 = Sum.inr 1 := rfl
@[simp] lemma σ12_11 : σ12 11 = Sum.inr 2 := rfl

lemma rename_σ12_ι9 (Q : MvPolynomial (Fin 9) ℂ) : rename σ12 (rename ι9 Q) = rename Sum.inl Q := by
  rw [rename_rename, σ12_ι9]

lemma rename_P04V : rename σ12 P04V = plkGen 0 1 := by
  apply MvPolynomial.funext; intro x
  simp [P04V, plkGen, plkV, Wmv, Wc0, eval_rename]; ring

lemma rename_P08V : rename σ12 P08V = plkGen 0 2 := by
  apply MvPolynomial.funext; intro x
  simp [P08V, plkGen, plkV, Wmv, Wc0, eval_rename]; ring

lemma rename_P48V : rename σ12 P48V = plkGen 1 2 := by
  apply MvPolynomial.funext; intro x
  simp [P48V, plkGen, plkV, Wmv, Wc4, eval_rename]; ring

/-! ### B6 -/

/-- The B6 linear forms `T₀, T₄, T₈, X₀ + X₄ + X₈` on `Idx`. -/
def hilbLV (a : Fin 4) (i : Idx) : ℂ := hilbL a (τ12 i)

lemma rename_lformV (l : Fin 12 → ℂ) :
    rename σ12 (LSG.Jac.lformV l) = LSG.MEBV.lformV (fun i => l (τ12 i)) := by
  simp only [LSG.Jac.lformV, LSG.MEBV.lformV, map_sum, map_mul, rename_C, rename_X]
  rw [← (finSumFinEquiv.symm : Fin (9 + 3) ≃ Idx).sum_comp (fun j => C (l (τ12 j)) * X j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  change C (l i) * X (σ12 i) = C (l (τ12 (σ12 i))) * X (σ12 i)
  rw [τ12_σ12]

lemma rename_gensV {Q : R12} (hQ : Q ∈ gensV) : rename σ12 Q ∈ LSG.MEBV.gensOf gensMv gensTV := by
  simp only [gensV, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with ⟨Q', hQ', rfl⟩ | rfl | rfl | rfl
  · rw [rename_σ12_ι9]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨Q', hQ', rfl⟩)
  · rw [rename_P04V]; exact List.mem_append_right _ (by simp [gensTV])
  · rw [rename_P08V]; exact List.mem_append_right _ (by simp [gensTV])
  · rw [rename_P48V]; exact List.mem_append_right _ (by simp [gensTV])

/-- **B6 for `A_σ̄^♮`** (degree 41). -/
theorem hilbVV (M : MvPolynomial Idx ℂ) (hM : M.IsHomogeneous 41) :
    M ∈ Ideal.span {Q | Q ∈ LSG.MEBV.gensOf gensMv gensTV} ⊔
      Ideal.span (Set.range fun a => LSG.MEBV.lformV (hilbLV a)) := by
  have hM' : (rename τ12 M).IsHomogeneous 41 := hM.rename_isHomogeneous
  have h := Ideal.mem_map_of_mem (rename (R := ℂ) σ12) (hilbV _ hM')
  have e : rename σ12 (rename τ12 M) = M := by
    rw [rename_rename]
    have : σ12 ∘ τ12 = id := funext σ12_τ12
    rw [this, rename_id_apply]
  rw [e, Ideal.map_sup, Ideal.map_span, Ideal.map_span] at h
  refine (sup_le_sup (Ideal.span_mono ?_) (Ideal.span_mono ?_) :
    Ideal.span _ ⊔ Ideal.span _ ≤ Ideal.span _ ⊔ Ideal.span _) h
  · rintro _ ⟨Q, hQ, rfl⟩
    exact rename_gensV hQ
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by simp only [rename_lformV]; rfl⟩

/-! ### The Wronskian cocycle -/

/-- `κ_A = −½X₅Q₁ − X₁Q₅ − ¾C₀ ∈ (gensMv)`. -/
def kappaA : MvPolynomial (Fin 9) ℂ := -(C (1 / 2) * X 5 * gQ1) - X 1 * gQ5 - C (3 / 4) * gC0

/-- **The Wronskian cocycle** on `Idx` (transported from `kappaV`). -/
theorem kappaVV : X (Sum.inl 0) * plkGen 1 2 - X (Sum.inl 4) * plkGen 0 2 + X (Sum.inl 8) * plkGen 0 1 =
    rename Sum.inl kappaA := by
  have h := congrArg (rename σ12) kappaV
  simp only [map_sub, map_add, map_mul, map_neg, rename_X, rename_C, rename_P04V, rename_P08V, rename_P48V,
    rename_σ12_ι9, σ12_0, σ12_1, σ12_4, σ12_5, σ12_8] at h
  rw [h, kappaA]
  simp only [map_sub, map_neg, map_mul, rename_X, rename_C]

lemma kappaA_mem (i : Fin 4) : lciS i * kappaA ∈ Ideal.ofList (lciF i) := by
  have h1 := lciA_mem i gQ1 (by simp [gensMv])
  have h5 := lciA_mem i gQ5 (by simp [gensMv])
  have h9 := lciA_mem i gC0 (by simp [gensMv])
  have e : lciS i * kappaA = -(C (1 / 2) * X 5) * (lciS i * gQ1) - X 1 * (lciS i * gQ5) -
      C (3 / 4) * (lciS i * gC0) := by unfold kappaA; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h5))
    (Ideal.mul_mem_left _ _ h9)

/-! ### B5: the 12 local systems -/

/-- The B5 indices `(i, s)`. -/
def e12 : Fin 4 × Fin 3 ≃ Fin 12 := finProdFinEquiv

/-- The two Plücker generators through the chart `fc s`. -/
def thrV : Fin 3 → List (MvPolynomial Idx ℂ) :=
  ![[plkGen 0 1, plkGen 0 2], [plkGen 0 1, plkGen 1 2], [plkGen 0 2, plkGen 1 2]]

/-- The local system `(i, s)`. -/
def lciF2 (i : Fin 4) (s : Fin 3) : List (MvPolynomial Idx ℂ) := (lciF i).map (rename Sum.inl) ++ thrV s

/-- The multiplier `S_i·X_{fc s}`. -/
def lciS2 (i : Fin 4) (s : Fin 3) : MvPolynomial Idx ℂ := rename Sum.inl (lciS i) * X (Sum.inl (fcV s))

def lciSV (j : Fin 12) : MvPolynomial Idx ℂ := lciS2 (e12.symm j).1 (e12.symm j).2

def lciFV (j : Fin 12) : List (MvPolynomial Idx ℂ) := lciF2 (e12.symm j).1 (e12.symm j).2

lemma lciV_len (j : Fin 12) : (lciFV j).length + (2 + 1) + 1 = 9 + 3 := by
  have h := lciA_len (e12.symm j).1
  have h2 : (thrV (e12.symm j).2).length = 2 := by
    generalize (e12.symm j).2 = s
    fin_cases s <;> rfl
  simp only [lciFV, lciF2, List.length_append, List.length_map, h2]
  omega

lemma rename_mem_span_gens {q : MvPolynomial (Fin 9) ℂ} (hq : q ∈ Ideal.span {Q | Q ∈ gensMv}) :
    rename Sum.inl q ∈ Ideal.span {Q | Q ∈ LSG.MEBV.gensOf gensMv gensTV} := by
  have h := Ideal.mem_map_of_mem (rename (R := ℂ) (Sum.inl : Fin 9 → Idx)) hq
  rw [Ideal.map_span] at h
  refine Ideal.span_mono ?_ h
  rintro _ ⟨Q, hQ, rfl⟩
  exact List.mem_append_left _ (List.mem_map.mpr ⟨Q, hQ, rfl⟩)

lemma rename_mem_ofList {l : List (MvPolynomial (Fin 9) ℂ)} {q : MvPolynomial (Fin 9) ℂ}
    (hq : q ∈ Ideal.ofList l) : rename Sum.inl q ∈ Ideal.ofList (l.map (rename (Sum.inl : Fin 9 → Idx))) := by
  have h := Ideal.mem_map_of_mem (rename (R := ℂ) (Sum.inl : Fin 9 → Idx)) hq
  rw [Ideal.map_span] at h
  refine Ideal.span_mono ?_ h
  rintro _ ⟨Q, hQ, rfl⟩
  exact List.mem_map.mpr ⟨Q, hQ, rfl⟩

lemma thrV_sub (s : Fin 3) : ∀ x ∈ thrV s, x ∈ gensTV := by
  fin_cases s <;> intro x hx <;> simp [thrV] at hx <;> rcases hx with rfl | rfl <;> simp [gensTV]

lemma lciV_F_le (j : Fin 12) :
    Ideal.ofList (lciFV j) ≤ Ideal.span {Q | Q ∈ LSG.MEBV.gensOf gensMv gensTV} := by
  refine Ideal.span_le.mpr fun x hx => ?_
  simp only [lciFV, lciF2, Set.mem_setOf_eq, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨q, hq, rfl⟩ | hx
  · exact rename_mem_span_gens (lciA_F_le _ (Ideal.subset_span hq))
  · exact Ideal.subset_span (List.mem_append_right _ (thrV_sub _ x hx))

lemma mem_lciF2_thr {i : Fin 4} {s : Fin 3} {x : MvPolynomial Idx ℂ} (hx : x ∈ thrV s) :
    x ∈ Ideal.ofList (lciF2 i s) :=
  Ideal.subset_span (List.mem_append_right _ hx)

lemma mem_lciF2_A {i : Fin 4} {s : Fin 3} {q : MvPolynomial (Fin 9) ℂ} (hq : q ∈ Ideal.ofList (lciF i)) :
    rename Sum.inl q ∈ Ideal.ofList (lciF2 i s) :=
  Ideal.span_mono (fun _ hy => List.mem_append_left _ hy) (rename_mem_ofList hq)

theorem lci2_mem (i : Fin 4) (s : Fin 3) :
    ∀ Q ∈ LSG.MEBV.gensOf gensMv gensTV, lciS2 i s * Q ∈ Ideal.ofList (lciF2 i s) := by
  intro Q hQ
  simp only [LSG.MEBV.gensOf, List.mem_append, List.mem_map] at hQ
  rcases hQ with ⟨Q', hQ', rfl⟩ | hQ
  · have h := mem_lciF2_A (s := s) (lciA_mem i Q' hQ')
    rw [map_mul] at h
    have e : lciS2 i s * rename Sum.inl Q' = X (Sum.inl (fcV s)) * (rename Sum.inl (lciS i) * rename Sum.inl Q') := by
      unfold lciS2; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ h
  · have hk := mem_lciF2_A (s := s) (kappaA_mem i)
    rw [map_mul] at hk
    have hκ := kappaVV
    have key : ∀ a b, plkGen a b ∈ thrV s → lciS2 i s * plkGen a b ∈ Ideal.ofList (lciF2 i s) :=
      fun a b h => Ideal.mul_mem_left _ _ (mem_lciF2_thr h)
    have mt : ∀ a b, plkGen a b ∈ thrV s → ∀ y : MvPolynomial Idx ℂ, y * plkGen a b ∈ Ideal.ofList (lciF2 i s) :=
      fun a b h y => Ideal.mul_mem_left _ y (mem_lciF2_thr h)
    simp only [gensTV, List.mem_cons, List.not_mem_nil, or_false] at hQ
    obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by fin_cases s <;> simp
    -- chart 0: the third Plücker is `plkGen 1 2`
    · rcases hQ with rfl | rfl | rfl
      · exact key 0 1 (by simp [thrV])
      · exact key 0 2 (by simp [thrV])
      · have e : lciS2 i 0 * plkGen 1 2 = rename Sum.inl (lciS i) * rename Sum.inl kappaA +
            (rename Sum.inl (lciS i) * X (Sum.inl 4)) * plkGen 0 2 -
            (rename Sum.inl (lciS i) * X (Sum.inl 8)) * plkGen 0 1 := by
          simp only [lciS2, fcV_0]
          linear_combination (rename Sum.inl (lciS i)) * hκ
        rw [e]
        exact Ideal.sub_mem _ (Ideal.add_mem _ hk (mt 0 2 (by simp [thrV]) _)) (mt 0 1 (by simp [thrV]) _)
    -- chart 4: the third Plücker is `plkGen 0 2`
    · rcases hQ with rfl | rfl | rfl
      · exact key 0 1 (by simp [thrV])
      · have e : lciS2 i 1 * plkGen 0 2 = (rename Sum.inl (lciS i) * X (Sum.inl 0)) * plkGen 1 2 +
            (rename Sum.inl (lciS i) * X (Sum.inl 8)) * plkGen 0 1 -
            rename Sum.inl (lciS i) * rename Sum.inl kappaA := by
          simp only [lciS2, fcV_1]
          linear_combination -(rename Sum.inl (lciS i)) * hκ
        rw [e]
        exact Ideal.sub_mem _ (Ideal.add_mem _ (mt 1 2 (by simp [thrV]) _) (mt 0 1 (by simp [thrV]) _)) hk
      · exact key 1 2 (by simp [thrV])
    -- chart 8: the third Plücker is `plkGen 0 1`
    · rcases hQ with rfl | rfl | rfl
      · have e : lciS2 i 2 * plkGen 0 1 = rename Sum.inl (lciS i) * rename Sum.inl kappaA -
            (rename Sum.inl (lciS i) * X (Sum.inl 0)) * plkGen 1 2 +
            (rename Sum.inl (lciS i) * X (Sum.inl 4)) * plkGen 0 2 := by
          simp only [lciS2, fcV_2]
          linear_combination (rename Sum.inl (lciS i)) * hκ
        rw [e]
        exact Ideal.add_mem _ (Ideal.sub_mem _ hk (mt 1 2 (by simp [thrV]) _)) (mt 0 2 (by simp [thrV]) _)
      · exact key 0 2 (by simp [thrV])
      · exact key 1 2 (by simp [thrV])

theorem lciV_mem (j : Fin 12) :
    ∀ Q ∈ LSG.MEBV.gensOf gensMv gensTV, lciSV j * Q ∈ Ideal.ofList (lciFV j) :=
  lci2_mem _ _

/-! ### B5: the `X`-only cover -/

lemma mul_mem_sup_of {R : Type*} [CommRing R] {I J K L : Ideal R} (hJK : J * K ≤ L) {x y : R}
    (hx : x ∈ I ⊔ J) (hy : y ∈ I ⊔ K) : x * y ∈ I ⊔ L := by
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨i', hi', k, hk, rfl⟩ := Submodule.mem_sup.mp hy
  have e : (i + j) * (i' + k) = i * (i' + k) + j * i' + j * k := by ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ hi)
  · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hi')
  · exact Ideal.mem_sup_right (hJK (Ideal.mul_mem_mul hj hk))

lemma rename_mem_sup {x : MvPolynomial (Fin 9) ℂ} {B : Set (MvPolynomial (Fin 9) ℂ)}
    {B' : Set (MvPolynomial Idx ℂ)} (hB : ∀ b ∈ B, rename Sum.inl b ∈ B')
    (h : x ∈ Ideal.span {Q | Q ∈ gensMv} ⊔ Ideal.span B) :
    rename Sum.inl x ∈ Ideal.span {Q | Q ∈ LSG.MEBV.gensOf gensMv gensTV} ⊔ Ideal.span B' := by
  have h' := Ideal.mem_map_of_mem (rename (R := ℂ) (Sum.inl : Fin 9 → Idx)) h
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span] at h'
  refine (sup_le_sup (Ideal.span_mono ?_) (Ideal.span_mono ?_) :
    Ideal.span _ ⊔ Ideal.span _ ≤ Ideal.span _ ⊔ Ideal.span _) h'
  · rintro _ ⟨Q, hQ, rfl⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
  · rintro _ ⟨b, hb, rfl⟩
    exact hB b hb

lemma yA_eq : yA = fcV := by funext a; fin_cases a <;> rfl

/-- **The B5 cover over the `X`-variables.** -/
theorem lciV_cover (v : Fin 9) : ∃ e : ℕ,
    (X (Sum.inl v) : MvPolynomial Idx ℂ) ^ e ∈
      Ideal.span {Q | Q ∈ LSG.MEBV.gensOf gensMv gensTV} ⊔ Ideal.span (Set.range lciSV) := by
  obtain ⟨e₁, h₁⟩ := lciA_cover v
  have h₂ := hilbA ((X v : MvPolynomial (Fin 9) ℂ) ^ 14) (isHomogeneous_X_pow v 14)
  have h₁' := rename_mem_sup (B' := Set.range fun i => rename Sum.inl (lciS i))
    (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩) h₁
  have h₂' := rename_mem_sup (B' := Set.range fun s => (X (Sum.inl (fcV s)) : MvPolynomial Idx ℂ))
    (by rintro _ ⟨a, rfl⟩; exact ⟨a, by rw [rename_X, yA_eq]⟩) h₂
  refine ⟨e₁ + 14, ?_⟩
  have hmul := mul_mem_sup_of (L := Ideal.span (Set.range lciSV)) ?_ h₁' h₂'
  · rwa [map_pow, map_pow, rename_X, ← pow_add] at hmul
  · rw [Ideal.span_mul_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨s, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨e12 (i, s), ?_⟩
    simp [lciSV, lciS2]

end LSG.JacBlockV
