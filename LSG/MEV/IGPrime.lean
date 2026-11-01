import Mathlib
import LSG.ME.IGPrime
import LSG.Elliptic.NaturalModel

/-!
# Primality of the ideal `(F, G)` of the `E^♮` cone, over an arbitrary base domain

VECEXT_SPIKE §2.3 noted the primality of `(F, G)`, `G = W T₃ − V T₁ + 2U²`, as a proof sketch
(unmixedness + generic reducedness). Here is an elementary proof, in the style of
`LSG.ME.IGPrime`.

* `isPrime_span_linear`: over a domain `S`, `a T + e ∈ S[T]` (`a ≠ 0`) generates a prime ideal if
  `a` is a non-zero-divisor modulo `e` in the sense `a ∣ e h → a ∣ h` (evaluation at `−e/a` in
  `Frac S`; pseudo-division; cancellation of `a`).
* `C_dvd_of_C_dvd_linear_mul`: in `B[X]`, if `c` is a non-zero-divisor modulo `b`, then
  `C b ∣ (C d + C c X) h → C b ∣ h` (descending induction on the degree).
* `V_nzd_mod_W_F`: in `R[U, V, W]`, `V y ∈ (W, F) → y ∈ (W, F)` (setting `W = 0`, `F ≡ −4U³`, and
  `U` is prime).
* **`isPrime_span_FG`**: for a domain `R` that is an algebra over a field `K` with `2 ≠ 0`,
  `(F, G)` is a prime ideal of `R[U, V, W, T₁, T₃]`: `R[U,V,W,T₁,T₃] ≅ A[T₁][T₃]`,
  `A = R[U, V, W]`; modulo the prime `(F)` of `A` (`LSG.ME.isPrime_span_F`) the ideal becomes
  `(W̄ T₃ + (2Ū² − V̄ T₁))` over the domain `S = (A/(F))[T₁]`, prime by the two lemmas above.
* `isPrime_span_gensProdS`: the disjoint-blocks principle of `LSG.ME.isPrime_span_gensProd`, for
  blocks with several relations (a set per block).
-/

universe u

open Polynomial

namespace LSG.MEV

/-! ### Linear polynomials over a domain -/

section Linear

variable {S : Type*} [CommRing S]

/-- In `B[X]`, if `c` is a non-zero-divisor modulo `b`, then `C b ∣ (C d + C c X) h → C b ∣ h`. -/
theorem C_dvd_of_C_dvd_linear_mul {b c d : S} (hc : ∀ y, b ∣ c * y → b ∣ y) :
    ∀ N : ℕ, ∀ h : S[X], h.natDegree ≤ N → C b ∣ (C d + C c * X) * h → C b ∣ h := by
  intro N
  induction N with
  | zero =>
    intro h hN hdvd
    rw [Polynomial.eq_C_of_natDegree_le_zero hN] at hdvd ⊢
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
    have e : (C d + C c * X) * C (h.coeff 0) = C (d * h.coeff 0) + C (c * h.coeff 0) * X := by
      simp only [C_mul]; ring
    have := hdvd 1
    rw [e, coeff_add, coeff_C, coeff_C_mul_X] at this
    simp only [one_ne_zero, ite_false, ite_true, zero_add] at this
    exact map_dvd C (hc _ this)
  | succ N ih =>
    intro h hN hdvd
    by_cases hd : h.natDegree ≤ N
    · exact ih h hd hdvd
    have hdeg : h.natDegree = N + 1 := by omega
    -- the top coefficient
    have htop : b ∣ h.leadingCoeff := by
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      have := hdvd (N + 2)
      have h1 : h.coeff (N + 2) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp only [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul, h1, mul_zero,
        zero_add] at this
      apply hc
      rwa [Polynomial.leadingCoeff, hdeg]
    obtain ⟨q, hq⟩ := htop
    have key : h = h.eraseLead + C b * C q * X ^ h.natDegree := by
      have hsplit := Polynomial.eraseLead_add_C_mul_X_pow h
      rw [hq, C_mul] at hsplit
      exact hsplit.symm
    have hdvd' : C b ∣ (C d + C c * X) * h.eraseLead := by
      have : (C d + C c * X) * h.eraseLead =
          (C d + C c * X) * h - C b * ((C d + C c * X) * (C q * X ^ h.natDegree)) := by
        linear_combination (-(C d + C c * X)) * key
      rw [this]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    have hlt : h.eraseLead.natDegree ≤ N := by
      have := Polynomial.eraseLead_natDegree_le h
      omega
    obtain ⟨r, hr⟩ := ih _ hlt hdvd'
    refine ⟨r + C q * X ^ h.natDegree, ?_⟩
    calc h = h.eraseLead + C b * C q * X ^ h.natDegree := key
      _ = C b * (r + C q * X ^ h.natDegree) := by rw [hr]; ring

variable [IsDomain S]

/-- **`a T + e` generates a prime ideal** if `a ≠ 0` and `a ∣ e h → a ∣ h`. -/
theorem isPrime_span_linear {a e : S} (ha : a ≠ 0) (hnzd : ∀ h, a ∣ e * h → a ∣ h) :
    (Ideal.span {C a * X + C e} : Ideal S[X]).IsPrime := by
  set f₀ : S[X] := C a * X + C e
  set L := FractionRing S
  have hinj := IsFractionRing.injective S L
  have haL : algebraMap S L a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  set φ : S[X] →+* L := Polynomial.eval₂RingHom (algebraMap S L) (-(algebraMap S L e) /
    algebraMap S L a)
  have hφ0 : φ f₀ = 0 := by
    show Polynomial.eval₂ (algebraMap S L) (-(algebraMap S L e) / algebraMap S L a)
      (C a * X + C e) = 0
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_C, mul_div_assoc', mul_neg, neg_div,
      mul_div_cancel_left₀ _ haL]
    ring
  -- pseudo-division
  have hpd : ∀ N : ℕ, ∀ f : S[X], f.natDegree ≤ N →
      ∃ n : ℕ, ∃ r : S, C a ^ n * f - C r ∈ Ideal.span {f₀} := by
    intro N
    induction N with
    | zero =>
      intro f hf
      refine ⟨0, f.coeff 0, ?_⟩
      rw [pow_zero, one_mul, ← Polynomial.eq_C_of_natDegree_le_zero hf, sub_self]
      exact Ideal.zero_mem _
    | succ N ih =>
      intro f hf
      set c := f.coeff (N + 1)
      set f' := C a * f - C c * X ^ N * f₀
      have hf' : f'.natDegree ≤ N := by
        have hsplit : f = (f - C c * X ^ (N + 1)) + C c * X ^ (N + 1) := by ring
        have hlow : (f - C c * X ^ (N + 1)).natDegree ≤ N := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro i hi
          simp only [coeff_sub, coeff_C_mul_X_pow]
          rcases Nat.lt_or_ge (N + 1) i with h | h
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
            simp [show i ≠ N + 1 by omega]
          · have : i = N + 1 := by omega
            subst this; simp [c]
        have : f' = C a * (f - C c * X ^ (N + 1)) - C (c * e) * X ^ N := by
          simp only [f', f₀, C_mul]; ring
        rw [this]
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact (Polynomial.natDegree_C_mul_le _ _).trans hlow
        · exact (Polynomial.natDegree_C_mul_X_pow_le _ _)
      obtain ⟨n, r, hr⟩ := ih f' hf'
      refine ⟨n + 1, r, ?_⟩
      have : C a ^ (n + 1) * f - C r = (C a ^ n * f' - C r) + C a ^ n * C c * X ^ N * f₀ := by
        simp only [f']; ring
      rw [this]
      exact Ideal.add_mem _ hr (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  -- cancellation of `a`
  have hcancel : ∀ g : S[X], C a * g ∈ Ideal.span {f₀} → g ∈ Ideal.span {f₀} := by
    intro g hg
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hg
    have hq' : C a ∣ q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      apply hnzd
      have hq2 : C a * (X * q) + C e * q = C a * g := by rw [← hq]; ring
      have hc := congrArg (fun p => p.coeff n) hq2
      simp only [coeff_add, coeff_C_mul] at hc
      rcases n with _ | n
      · rw [coeff_X_mul_zero, mul_zero, zero_add] at hc
        exact ⟨g.coeff 0, hc⟩
      · rw [coeff_X_mul] at hc
        exact ⟨g.coeff (n + 1) - q.coeff n, by linear_combination hc⟩
    obtain ⟨q', rfl⟩ := hq'
    have hCa : (C a : S[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ha
    have : C a * (q' * f₀) = C a * g := by rw [← hq]; ring
    rw [← mul_left_cancel₀ hCa this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hcancel' : ∀ n : ℕ, ∀ g : S[X], C a ^ n * g ∈ Ideal.span {f₀} → g ∈ Ideal.span {f₀} := by
    intro n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih => intro g hg; exact ih g (hcancel _ (by rw [← mul_assoc, ← pow_succ']; exact hg))
  -- the kernel
  have hker : Ideal.span {f₀} = RingHom.ker φ := by
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hφ0
    · intro f hf
      obtain ⟨n, r, hr⟩ := hpd f.natDegree f le_rfl
      have hr0 : φ (C a ^ n * f - C r) = 0 := by
        have : Ideal.span {f₀} ≤ RingHom.ker φ := by
          rw [Ideal.span_le, Set.singleton_subset_iff]; exact hφ0
        exact this hr
      rw [map_sub, map_mul, RingHom.mem_ker.mp hf, mul_zero, zero_sub, neg_eq_zero] at hr0
      have : r = 0 := by
        simp only [φ, coe_eval₂RingHom, eval₂_C] at hr0
        exact (map_eq_zero_iff _ hinj).mp hr0
      rw [this, map_zero, sub_zero] at hr
      exact hcancel' n f hr
  rw [hker]
  exact RingHom.ker_isPrime φ

end Linear

/-! ### The cone `(F, G)` -/

section Cone

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra K R]

local notation "MX" => MvPolynomial.X
local notation "MC" => MvPolynomial.C

/-- Setting `W = 0` in `R[U, V, W]`. -/
noncomputable def setW0 (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval ![MX 0, MX 1, 0]

omit [IsDomain R] in
theorem sub_setW0_mem (x : MvPolynomial (Fin 3) R) : x - setW0 R x ∈ Ideal.span {MX 2} := by
  induction x using MvPolynomial.induction_on with
  | C a => simp [setW0]
  | add p q hp hq => rw [map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    have : p * MX i - setW0 R p * setW0 R (MX i) =
        (p - setW0 R p) * MX i + setW0 R p * (MX i - setW0 R (MX i)) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    fin_cases i <;> simp [setW0]

omit [IsDomain R] in
theorem setW0_Fcone (g₂ g₃ : R) : setW0 R (LSG.ME.Fcone R g₂ g₃) = -4 * MX 0 ^ 3 := by
  simp [setW0, LSG.ME.Fcone, LSG.Elliptic.F, map_ofNat]

/-- **`V` is a non-zero-divisor modulo `(W, F)`** in `R[U, V, W]` (`2 ≠ 0`). -/
theorem V_nzd_mod_W_F (h2 : (2 : K) ≠ 0) (g₂ g₃ : R) {y z t : MvPolynomial (Fin 3) R}
    (h : MX 1 * y = MX 2 * z + LSG.ME.Fcone R g₂ g₃ * t) :
    ∃ α β : MvPolynomial (Fin 3) R, y = MX 2 * α + LSG.ME.Fcone R g₂ g₃ * β := by
  have h0 := congrArg (setW0 R) h
  simp only [map_mul, map_add, setW0_Fcone] at h0
  have hW : setW0 R (MX 2) = 0 := by simp [setW0]
  have hV : setW0 R (MX 1) = MX 1 := by simp [setW0]
  rw [hW, hV, zero_mul, zero_add] at h0
  have hU : Prime (MX 0 : MvPolynomial (Fin 3) R) := MvPolynomial.X_prime
  have hUV : ¬ (MX 0 : MvPolynomial (Fin 3) R) ∣ MX 1 := by
    rintro ⟨q, hq⟩
    have := congrArg (MvPolynomial.eval ![0, 1, 0]) hq
    simp at this
  have hdvd : (MX 0 : MvPolynomial (Fin 3) R) ^ 3 ∣ MX 1 * setW0 R y :=
    ⟨-4 * setW0 R t, by rw [h0]; ring⟩
  obtain ⟨q, hq⟩ := hU.pow_dvd_of_dvd_mul_left 3 hUV hdvd
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (sub_setW0_mem y)
  -- `1/4`
  set q4 : R := algebraMap K R (1 / 4)
  have hq4 : (4 : R) * q4 = 1 := by
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have : (4 : R) = algebraMap K R 4 := (map_ofNat _ 4).symm
    rw [this, ← map_mul, mul_one_div_cancel h4, map_one]
  have hq4' : (4 : MvPolynomial (Fin 3) R) * MC q4 = 1 := by
    have := congrArg (MC : R → MvPolynomial (Fin 3) R) hq4
    rwa [map_mul, map_one, map_ofNat] at this
  refine ⟨s + MC q4 * q * (MX 1 ^ 2 + MC g₂ * MX 0 * MX 2 + MC g₃ * MX 2 ^ 2), -(MC q4 * q), ?_⟩
  have hy : y = s * MX 2 + MX 0 ^ 3 * q := by rw [← hq]; linear_combination -hs
  rw [hy]
  simp only [LSG.ME.Fcone, LSG.Elliptic.F]
  linear_combination (-(MX 0 ^ 3 * q)) * hq4'

/-- `Fin 5 ≃ Fin 5`, `T₃ ↦ 0`, `T₁ ↦ 1`, `U ↦ 2`, `V ↦ 3`, `W ↦ 4`. -/
def perm5 : Fin 5 ≃ Fin 5 where
  toFun := ![2, 3, 4, 1, 0]
  invFun := ![4, 3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- `R[U, V, W, T₁, T₃] ≃ A[T₁][T₃]`, `A = R[U, V, W]`. -/
noncomputable def fgEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 5) R ≃ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin 3) R)) :=
  ((MvPolynomial.renameEquiv R perm5).trans (MvPolynomial.finSuccEquiv R 4)).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R 3))

omit [IsDomain R] in
theorem fgEquiv_T3 : fgEquiv R (MX 4) = X := by
  have h : perm5 4 = 0 := by decide
  simp only [fgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, h, MvPolynomial.finSuccEquiv_X_zero]
  simp [Polynomial.mapAlgEquiv]

omit [IsDomain R] in
theorem fgEquiv_T1 : fgEquiv R (MX 3) = C X := by
  have h : perm5 3 = (0 : Fin 4).succ := by decide
  simp only [fgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, h, MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.mapAlgEquiv, MvPolynomial.finSuccEquiv_X_zero]

omit [IsDomain R] in
theorem fgEquiv_base (i : Fin 3) :
    fgEquiv R (MX (Fin.castSucc (Fin.castSucc i))) = C (C (MX i)) := by
  have h : perm5 (Fin.castSucc (Fin.castSucc i)) = (i.succ).succ := by fin_cases i <;> decide
  simp only [fgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, h, MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.mapAlgEquiv, MvPolynomial.finSuccEquiv_X_succ]

omit [IsDomain R] in
theorem fgEquiv_C (r : R) : fgEquiv R (MC r) = C (C (MC r)) := by
  have := (fgEquiv R).commutes r
  rw [MvPolynomial.algebraMap_eq] at this
  rw [this, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- The cubic `F` in `R[U, V, W, T₁, T₃]`. -/
noncomputable def Fcone5 (R : Type*) [CommRing R] (g₂ g₃ : R) : MvPolynomial (Fin 5) R :=
  LSG.Elliptic.F (MC g₂) (MC g₃) (MX 0) (MX 1) (MX 2)

/-- The fibre relation `G = W T₃ − V T₁ + 2U²` in `R[U, V, W, T₁, T₃]`. -/
noncomputable def Gcone5 (R : Type*) [CommRing R] : MvPolynomial (Fin 5) R :=
  LSG.Elliptic.Gfib (MX 0) (MX 1) (MX 2) (MX 3) (MX 4)

set_option maxSynthPendingDepth 10 in
/-- **The cone over `X = V(F, G)` is integral**, over any domain `K`-algebra (`2 ≠ 0`). -/
theorem isPrime_span_FG (h2 : (2 : K) ≠ 0) (g₂ g₃ : R) :
    (Ideal.span {Fcone5 R g₂ g₃, Gcone5 R}).IsPrime := by
  set A := MvPolynomial (Fin 3) R
  set J : Ideal A := Ideal.span {LSG.ME.Fcone R g₂ g₃} with hJ
  have hJp : J.IsPrime := LSG.ME.isPrime_span_F h2 g₂ g₃
  set B := A ⧸ J
  set mk := Ideal.Quotient.mk J
  set π : Polynomial (Polynomial A) →+* Polynomial (Polynomial B) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom mk)
  have hπ : Function.Surjective π :=
    Polynomial.map_surjective _ (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  have hU : fgEquiv R (MX 0) = C (C (MX 0)) := fgEquiv_base 0
  have hV : fgEquiv R (MX 1) = C (C (MX 1)) := fgEquiv_base 1
  have hW : fgEquiv R (MX 2) = C (C (MX 2)) := fgEquiv_base 2
  have hF : fgEquiv R (Fcone5 R g₂ g₃) = C (C (LSG.ME.Fcone R g₂ g₃)) := by
    simp only [Fcone5, LSG.ME.Fcone, LSG.Elliptic.F, map_add, map_sub, map_mul, map_pow,
      map_ofNat, hU, hV, hW, fgEquiv_C]
  have hG : fgEquiv R (Gcone5 R) =
      C (C (MX 2)) * X - C (C (MX 1)) * C X + 2 * C (C (MX 0)) ^ 2 := by
    simp only [Gcone5, LSG.Elliptic.Gfib, map_add, map_sub, map_mul, map_pow, map_ofNat, hU, hV,
      hW, fgEquiv_T1, fgEquiv_T3]
  set a : Polynomial B := C (mk (MX 2))
  set e : Polynomial B := C (mk (2 * MX 0 ^ 2)) + C (-(mk (MX 1))) * X
  have hπC : ∀ x : A, π (C (C x)) = C (C (mk x)) := fun x => by
    simp only [π, Polynomial.coe_mapRingHom, Polynomial.map_C]
  have hπX : π X = X := by simp only [π, Polynomial.coe_mapRingHom, Polynomial.map_X]
  have hπCX : π (C X) = C X := by
    simp only [π, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
  have hπG : π (fgEquiv R (Gcone5 R)) = C a * X + C e := by
    rw [hG, map_add, map_sub, map_mul, map_mul, map_mul, map_pow, hπC, hπC, hπC, hπX, hπCX,
      map_ofNat]
    simp only [a, e, C_add, C_neg, map_mul, map_pow, map_ofNat]
    ring
  have hπF : π (fgEquiv R (Fcone5 R g₂ g₃)) = 0 := by
    have hmk : mk (LSG.ME.Fcone R g₂ g₃) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _) : LSG.ME.Fcone R g₂ g₃ ∈ J)
    rw [hF, hπC, hmk, map_zero, map_zero]
  apply LSG.ME.isPrime_of_map_equiv (fgEquiv R).toRingEquiv
  rw [Ideal.map_span, Set.image_pair]
  refine LSG.ME.isPrime_of_map_surj π hπ _ ?_ ?_
  · rw [Polynomial.ker_mapRingHom, Polynomial.ker_mapRingHom, Ideal.mk_ker, hJ, Ideal.map_span,
      Ideal.map_span, Set.image_singleton, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    refine Ideal.subset_span (Or.inl ?_)
    change C (C (LSG.ME.Fcone R g₂ g₃)) = fgEquiv R (Fcone5 R g₂ g₃)
    rw [hF]
  · rw [Ideal.map_span, Set.image_pair]
    change (Ideal.span {π (fgEquiv R (Fcone5 R g₂ g₃)), π (fgEquiv R (Gcone5 R))}).IsPrime
    rw [hπF, hπG, Set.pair_comm, Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl,
      sup_bot_eq]
    -- `a ≠ 0`
    have h4 : (4 : R) ≠ 0 := by
      have h4K : (4 : K) ≠ 0 := by
        have : (4 : K) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have : (4 : R) = algebraMap K R 4 := (map_ofNat _ 4).symm
      rw [this]
      intro h0
      have hu : IsUnit (algebraMap K R 4) := (IsUnit.mk0 _ h4K).map _
      rw [h0] at hu
      exact not_isUnit_zero hu
    have ha : a ≠ 0 := by
      simp only [a, ne_eq, Polynomial.C_eq_zero]
      intro h0
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      have h1 := congrArg (setW0 R) hq
      rw [map_mul, setW0_Fcone] at h1
      have hW0 : setW0 R (MX 2) = 0 := by simp [setW0]
      rw [hW0] at h1
      have hq0 : setW0 R q = 0 := by
        have hX : (MX 0 : A) ^ 3 ≠ 0 := pow_ne_zero _ (MvPolynomial.X_ne_zero _)
        have h4' : (-4 : A) ≠ 0 := by
          rw [show (-4 : A) = MC (-4) by simp [map_ofNat], ne_eq, MvPolynomial.C_eq_zero,
            neg_eq_zero]
          exact h4
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h (mul_ne_zero h4' hX)
      obtain ⟨q', hq'⟩ := Ideal.mem_span_singleton'.mp (sub_setW0_mem q)
      rw [hq0, sub_zero] at hq'
      rw [← hq'] at hq
      have h1 : (MX 2 : A) * (q' * LSG.ME.Fcone R g₂ g₃) = MX 2 * 1 := by
        linear_combination hq
      have h1' := mul_left_cancel₀ (MvPolynomial.X_ne_zero _) h1
      apply hJp.ne_top
      rw [Ideal.eq_top_iff_one, ← h1']
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine isPrime_span_linear ha fun h hh => ?_
    refine C_dvd_of_C_dvd_linear_mul (b := mk (MX 2)) ?_ h.natDegree h le_rfl hh
    intro y hy
    obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, hz⟩ := hy
    obtain ⟨z₀, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hmem : -(MX 1 * y₀) - MX 2 * z₀ ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, map_mul, map_mul, ← neg_mul, hz,
        sub_self]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨α, β, hαβ⟩ := V_nzd_mod_W_F h2 g₂ g₃ (y := y₀) (z := -z₀) (t := -t)
      (by linear_combination ht)
    refine ⟨mk α, ?_⟩
    rw [hαβ, map_add, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span rfl : LSG.ME.Fcone R g₂ g₃ ∈ J), zero_mul, add_zero]

end Cone

/-! ### Disjoint blocks with several relations -/

section Ind

variable {K : Type u} [Field K]

/-- The relation sets `r k`, placed in the `k`-th copy `{k} × B` of the variables. -/
noncomputable def gensProdS {B : Type} {n : ℕ} (R : Type u) [CommRing R] [Algebra K R]
    (r : Fin n → Set (MvPolynomial B K)) : Set (MvPolynomial (Fin n × B) R) :=
  ⋃ k, (fun f => MvPolynomial.rename (Prod.mk k) (MvPolynomial.map (algebraMap K R) f)) '' r k

set_option maxSynthPendingDepth 10 in
/-- **Disjoint blocks.** If each relation set generates a prime ideal over every domain
`K`-algebra, the relation sets in disjoint copies of the variables generate a prime ideal. -/
theorem isPrime_span_gensProdS {B : Type} (P : Set (MvPolynomial B K) → Prop)
    (hP : ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] (s : Set (MvPolynomial B K)),
      P s → (Ideal.span (MvPolynomial.map (algebraMap K R) '' s)).IsPrime) :
    ∀ (n : ℕ) (r : Fin n → Set (MvPolynomial B K)), (∀ k, P (r k)) →
      ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra K R],
        (Ideal.span (gensProdS R r)).IsPrime := by
  intro n
  induction n with
  | zero =>
    intro r _ R _ _ _
    have : gensProdS R r = ∅ := by
      simp only [gensProdS, Set.iUnion_eq_empty]
      intro k; exact k.elim0
    rw [this, Ideal.span_empty]
    exact Ideal.isPrime_bot
  | succ n ih =>
    intro r hr R _ _ _
    set J : Ideal (MvPolynomial B R) :=
      Ideal.span (MvPolynomial.map (algebraMap K R) '' r (Fin.last n)) with hJdef
    have hJ : J.IsPrime := hP R _ (hr _)
    set Φ := LSG.ME.splitEquiv n B R
    set ψ : MvPolynomial (Fin n × B) (MvPolynomial B R) →+*
        MvPolynomial (Fin n × B) (MvPolynomial B R ⧸ J) := MvPolynomial.map (Ideal.Quotient.mk J)
    have hψ : Function.Surjective ψ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
    have halg : algebraMap K (MvPolynomial B R ⧸ J) =
        ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp (algebraMap K R) := by
      ext x
      rfl
    have hcs : ∀ (k : Fin n) (f : MvPolynomial B K),
        ψ (Φ (MvPolynomial.rename (Prod.mk k.castSucc) (MvPolynomial.map (algebraMap K R) f))) =
          MvPolynomial.rename (Prod.mk k)
            (MvPolynomial.map (algebraMap K (MvPolynomial B R ⧸ J)) f) := by
      intro k f
      rw [show Φ _ = _ from LSG.ME.splitEquiv_castSucc k _]
      simp only [ψ, MvPolynomial.map_rename, MvPolynomial.map_map, halg]
      rfl
    have hlast : ∀ f ∈ r (Fin.last n), ψ (Φ (MvPolynomial.rename (Prod.mk (Fin.last n))
        (MvPolynomial.map (algebraMap K R) f))) = 0 := by
      intro f hf
      rw [show Φ _ = _ from LSG.ME.splitEquiv_last _]
      simp only [ψ, MvPolynomial.map_C, MvPolynomial.C_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨f, hf, rfl⟩)
    apply LSG.ME.isPrime_of_map_equiv Φ.toRingEquiv
    refine LSG.ME.isPrime_of_map_surj ψ hψ _ ?_ ?_
    · rw [MvPolynomial.ker_map, Ideal.mk_ker, hJdef, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      rw [← show Φ _ = _ from LSG.ME.splitEquiv_last (n := n)
        (MvPolynomial.map (algebraMap K R) f)]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_iUnion.mpr ⟨_, f, hf, rfl⟩))
    · have : ((Ideal.span (gensProdS R r)).map Φ.toRingEquiv).map ψ =
          Ideal.span (gensProdS (MvPolynomial B R ⧸ J) fun k => r k.castSucc) := by
        rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp]
        apply le_antisymm
        · rw [Ideal.span_le]
          rintro _ ⟨_, hx, rfl⟩
          obtain ⟨k, f, hf, rfl⟩ := Set.mem_iUnion.mp hx
          induction k using Fin.lastCases with
          | last =>
            have h0 : (ψ ∘ Φ.toRingEquiv) (MvPolynomial.rename (Prod.mk (Fin.last n))
                (MvPolynomial.map (algebraMap K R) f)) = 0 := hlast f hf
            simp only [h0, SetLike.mem_coe]
            exact Ideal.zero_mem _
          | cast k =>
            refine Ideal.subset_span (Set.mem_iUnion.mpr ⟨k, f, hf, ?_⟩)
            exact (hcs k f).symm
        · rw [Ideal.span_le]
          rintro _ hx
          obtain ⟨k, f, hf, rfl⟩ := Set.mem_iUnion.mp hx
          exact Ideal.subset_span ⟨_, Set.mem_iUnion.mpr ⟨k.castSucc, f, hf, rfl⟩, hcs k f⟩
      rw [this]
      exact ih _ (fun k => hr _) _

end Ind

end LSG.MEV
