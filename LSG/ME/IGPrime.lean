import Mathlib
import LSG.Elliptic.AdditionLaws

/-!
# Primality of the ideals of `G_m` and of the Weierstrass cone, over an arbitrary base domain

Algebraic input for `LSG.ME.IG` (the ideal `I_G` of `G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`).

* `isPrime_span_monic_cubic`: over a domain `S`, a monic cubic without roots in `Frac S`
  generates a prime ideal of `S[X]` (division by a monic polynomial, and `Frac(S)[X]` is a PID).
* `cubic_no_root`: Eisenstein-type descent. Over `S = T[W]` (`T` a domain), the cubic
  `U³ + W² a U + W c` with `W ∤ c` has no root in `Frac S`.
* **`isPrime_span_F`**: for a domain `R` that is an algebra over a field `K` with `2 ≠ 0`, the cone
  form `F = V²W − 4U³ + g₂UW² + g₃W³` generates a prime ideal of `R[U, V, W]` (any `g₂, g₃ ∈ K`;
  no discriminant condition is needed).
* **`isPrime_span_YZ`**: `Y Z − 1` generates a prime ideal of `R[Y, Z]` (`R[Y, Z]/(YZ − 1)` is
  the localization `R[Z][1/Z]`).
* **`isPrime_span_gensProd`**: if each relation `r k ∈ K[B]` generates a prime ideal over every
  domain `K`-algebra, then the relations `r k`, placed in disjoint copies `{k} × B` of the
  variables, generate a prime ideal of `R[Fin n × B]` (induction on `n`, changing the base ring
  to `R[B]/(r_last)`).
-/

universe u

open Polynomial

namespace LSG.ME

/-! ### Two transfer principles for primality -/

theorem isPrime_of_map_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (I : Ideal A)
    (h : (I.map e).IsPrime) : I.IsPrime := by
  rw [← Ideal.comap_map_of_bijective e e.bijective (I := I)]
  exact Ideal.comap_isPrime _ _

theorem isPrime_of_map_surj {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (hker : RingHom.ker f ≤ I) (h : (I.map f).IsPrime) :
    I.IsPrime := by
  have : (I.map f).comap f = I := by
    rw [Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hker]
  rw [← this]
  exact Ideal.comap_isPrime _ _

/-! ### Monic cubics -/

section Cubic

variable {S : Type*} [CommRing S] [IsDomain S]

/-- A monic cubic without roots in the fraction field generates a prime ideal. -/
theorem isPrime_span_monic_cubic {f : S[X]} (hm : f.Monic) (hd : f.natDegree = 3)
    (hr : ∀ x : FractionRing S, ¬ (f.map (algebraMap S (FractionRing S))).IsRoot x) :
    (Ideal.span {f}).IsPrime := by
  set L := FractionRing S
  set φ : S[X] →+* L[X] := Polynomial.mapRingHom (algebraMap S L)
  have hinj : Function.Injective φ := Polynomial.map_injective _ (IsFractionRing.injective S L)
  have hfm : (f.map (algebraMap S L)).Monic := hm.map _
  have hfd : (f.map (algebraMap S L)).natDegree = 3 := by rw [hm.natDegree_map]; exact hd
  have hirr : Irreducible (f.map (algebraMap S L)) := by
    rw [hfm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun x hx => hr x ?_
    exact (Polynomial.mem_roots hfm.ne_zero).mp hx
  have hp : (Ideal.span {f.map (algebraMap S L)}).IsPrime :=
    (Ideal.span_singleton_prime hfm.ne_zero).mpr hirr.prime
  have heq : Ideal.span {f} = (Ideal.span {f.map (algebraMap S L)}).comap φ := by
    ext g
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.map (algebraMap S L), by simp [φ, Polynomial.map_mul]⟩
    · intro h
      rw [← Polynomial.modByMonic_eq_zero_iff_dvd hm]
      apply hinj
      rw [map_zero]
      change (g %ₘ f).map (algebraMap S L) = 0
      rw [Polynomial.map_modByMonic _ hm, Polynomial.modByMonic_eq_zero_iff_dvd hfm]
      exact h
  rw [heq]
  exact Ideal.comap_isPrime _ _

end Cubic

section Descent

variable {T : Type*} [CommRing T] [IsDomain T]

/-- One descent step for `p³ + W² a p q² + W c q³ = 0` (`W = X` in `T[X]`, `W ∤ c`). -/
theorem cubic_descent_step {a c : T[X]} (hc : ¬ (X : T[X]) ∣ c) {p q : T[X]}
    (h : p ^ 3 + X ^ 2 * a * p * q ^ 2 + X * c * q ^ 3 = 0) :
    ∃ p₁ q₁ : T[X], q = X * q₁ ∧ p₁ ^ 3 + X ^ 2 * a * p₁ * q₁ ^ 2 + X * c * q₁ ^ 3 = 0 := by
  have hX : Prime (X : T[X]) := Polynomial.prime_X
  have hX0 : (X : T[X]) ≠ 0 := Polynomial.X_ne_zero
  have hp3 : (X : T[X]) ∣ p ^ 3 := ⟨-(X * a * p * q ^ 2 + c * q ^ 3), by linear_combination h⟩
  obtain ⟨p₁, rfl⟩ := hX.dvd_of_dvd_pow hp3
  have h1 : X ^ 2 * p₁ ^ 3 + X ^ 2 * a * p₁ * q ^ 2 + c * q ^ 3 = 0 := by
    have : (X : T[X]) * (X ^ 2 * p₁ ^ 3 + X ^ 2 * a * p₁ * q ^ 2 + c * q ^ 3) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hX0
  have hq3 : (X : T[X]) ∣ c * q ^ 3 :=
    ⟨-(X * p₁ ^ 3 + X * a * p₁ * q ^ 2), by linear_combination h1⟩
  have hq : (X : T[X]) ∣ q := hX.dvd_of_dvd_pow ((hX.dvd_or_dvd hq3).resolve_left hc)
  obtain ⟨q₁, rfl⟩ := hq
  refine ⟨p₁, q₁, rfl, ?_⟩
  have : (X : T[X]) ^ 2 * (p₁ ^ 3 + X ^ 2 * a * p₁ * q₁ ^ 2 + X * c * q₁ ^ 3) = 0 := by
    linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hX0)

theorem cubic_descent {a c : T[X]} (hc : ¬ (X : T[X]) ∣ c) :
    ∀ n : ℕ, ∀ p q : T[X], p ^ 3 + X ^ 2 * a * p * q ^ 2 + X * c * q ^ 3 = 0 → (X : T[X]) ^ n ∣ q
        := by
  intro n
  induction n with
  | zero => intro p q _; simp
  | succ n ih =>
    intro p q h
    obtain ⟨p₁, q₁, rfl, h₁⟩ := cubic_descent_step hc h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih p₁ q₁ h₁)

/-- **Eisenstein-type criterion**: `U³ + W² a U + W c` (`W ∤ c`) has no root in `Frac T[W]`. -/
theorem cubic_no_root {a c : T[X]} (hc : ¬ (X : T[X]) ∣ c) (x : FractionRing T[X]) :
    ¬ ((X ^ 3 + (C (X ^ 2 * a) * X + C (X * c)) : T[X][X]).map
      (algebraMap T[X] (FractionRing T[X]))).IsRoot x := by
  intro hx
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := T[X]) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hinj := IsFractionRing.injective T[X] (FractionRing T[X])
  have hqL : algebraMap T[X] (FractionRing T[X]) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq0
  have hev : ∀ y : FractionRing T[X], ((X ^ 3 + (C (X ^ 2 * a) * X + C (X * c)) : T[X][X]).map
      (algebraMap T[X] (FractionRing T[X]))).eval y = y ^ 3 +
        (algebraMap T[X] _ (X ^ 2 * a) * y + algebraMap T[X] _ (X * c)) := by
    intro y; simp
  rw [IsRoot, hev] at hx
  have h1 : algebraMap T[X] (FractionRing T[X]) (p ^ 3 + X ^ 2 * a * p * q ^ 2 + X * c * q ^ 3) =
      0 := by
    simp only [map_mul, map_pow] at hx
    simp only [map_add, map_mul, map_pow]
    field_simp at hx
    linear_combination hx
  have h2 : p ^ 3 + X ^ 2 * a * p * q ^ 2 + X * c * q ^ 3 = 0 := (map_eq_zero_iff _ hinj).mp h1
  have hdvd := cubic_descent hc (q.natDegree + 1) p q h2
  have := Polynomial.natDegree_le_of_dvd hdvd hq0
  rw [Polynomial.natDegree_X_pow] at this
  omega

end Descent

/-! ### The Weierstrass cone form over a domain -/

section Cone

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra K R]

local notation "MX" => MvPolynomial.X
local notation "MC" => MvPolynomial.C

/-- The cone form `F(U, V, W)` with `U = X 0`, `V = X 1`, `W = X 2`. -/
noncomputable def Fcone (R : Type*) [CommRing R] (g₂ g₃ : R) : MvPolynomial (Fin 3) R :=
  LSG.Elliptic.F (MC g₂) (MC g₃) (MX 0) (MX 1) (MX 2)

/-- The iso `R[U, V, W] ≃ T[W][U]`, `T = R[V]`, with `U ↦ X`, `W ↦ C X`, `V ↦ C (C (X 0))`. -/
noncomputable def coneEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 3) R ≃ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin 1) R)) :=
  ((MvPolynomial.renameEquiv R (Equiv.swap (1 : Fin 3) 2)).trans (MvPolynomial.finSuccEquiv R
      2)).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R 1))

omit [IsDomain R] in
theorem coneEquiv_X0 : coneEquiv R (MX 0) = X := by
  have h : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  simp only [coneEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    h, MvPolynomial.finSuccEquiv_X_zero]
  simp [Polynomial.mapAlgEquiv]

omit [IsDomain R] in
theorem coneEquiv_X1 : coneEquiv R (MX 1) = C (C (MX 0)) := by
  have h : Equiv.swap (1 : Fin 3) 2 1 = (1 : Fin 2).succ := by decide
  have e1 : MvPolynomial.finSuccEquiv R 1 (MX (1 : Fin 2)) = C (MX 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  simp only [coneEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X, h,
    MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.mapAlgEquiv, e1]

omit [IsDomain R] in
theorem coneEquiv_X2 : coneEquiv R (MX 2) = C X := by
  have h : Equiv.swap (1 : Fin 3) 2 2 = (0 : Fin 2).succ := by decide
  simp only [coneEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_X, h,
    MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.mapAlgEquiv, MvPolynomial.finSuccEquiv_X_zero]

omit [IsDomain R] in
theorem coneEquiv_C (r : R) : coneEquiv R (MC r) = C (C (MC r)) := by
  have := (coneEquiv R).commutes r
  rw [MvPolynomial.algebraMap_eq] at this
  rw [this, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

set_option maxSynthPendingDepth 10 in
/-- **The cone over a Weierstrass cubic is integral**, over any domain `K`-algebra (`2 ≠ 0`). -/
theorem isPrime_span_F (h2 : (2 : K) ≠ 0) (g₂ g₃ : R) :
    (Ideal.span {Fcone R g₂ g₃}).IsPrime := by
  set T := MvPolynomial (Fin 1) R
  set q4 : R := algebraMap K R (1 / 4)
  have hq4 : (4 : R) * q4 = 1 := by
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have : (4 : R) = algebraMap K R 4 := (map_ofNat _ 4).symm
    rw [this, ← map_mul, mul_one_div_cancel h4, map_one]
  have hq4ne : q4 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hq4; exact zero_ne_one hq4
  -- the monic cubic
  set a : T[X] := C (MC (-(q4 * g₂)))
  set c : T[X] := -(C (MC q4) * (C (MX 0) ^ 2 + C (MC g₃) * X ^ 2))
  set f : T[X][X] := X ^ 3 + (C (X ^ 2 * a) * X + C (X * c))
  have hc : ¬ (X : T[X]) ∣ c := by
    rw [Polynomial.X_dvd_iff]
    have : c.coeff 0 = -(MC q4 * MX 0 ^ 2) := by
      simp only [c, coeff_neg, coeff_C_mul, coeff_add, coeff_C_zero, ← C_pow]
      simp
    rw [this, neg_eq_zero]
    intro h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact hq4ne (MvPolynomial.C_eq_zero.mp h0)
    · exact pow_ne_zero 2 (MvPolynomial.X_ne_zero (0 : Fin 1) : (MX 0 : T) ≠ 0) h0
  have hlow : (C (X ^ 2 * a) * X + C (X * c) : T[X][X]).degree < 3 := by
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact (degree_C_mul_X_le _).trans_lt (by norm_num)
    · exact (degree_C_le).trans_lt (by norm_num)
  have hfm : f.Monic := (monic_X_pow 3).add_of_left (by rwa [degree_X_pow])
  have hfd : f.natDegree = 3 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hf : (Ideal.span {f}).IsPrime :=
    isPrime_span_monic_cubic hfm hfd (cubic_no_root hc)
  -- transport
  have hq4' : (4 : T[X][X]) * C (C (MC q4)) = 1 := by
    have := congrArg (fun r => (C (C (MC r)) : T[X][X])) hq4
    simp only [map_mul, map_ofNat, map_one] at this
    exact this
  have himg : coneEquiv R (Fcone R g₂ g₃) = C (C (MC (-4))) * f := by
    simp only [Fcone, LSG.Elliptic.F, map_add, map_sub, map_mul, map_pow, coneEquiv_X0,
      coneEquiv_X1, coneEquiv_X2, coneEquiv_C, map_ofNat, f, a, c, map_neg]
    linear_combination (-(C (C (MC g₂)) * X * (C X) ^ 2 + (C (C (MX 0))) ^ 2 * C X +
      C (C (MC g₃)) * (C X) ^ 3)) * hq4'
  apply isPrime_of_map_equiv (coneEquiv R).toRingEquiv
  rw [Ideal.map_span, Set.image_singleton]
  change (Ideal.span {coneEquiv R (Fcone R g₂ g₃)}).IsPrime
  rw [himg, Ideal.span_singleton_mul_left_unit]
  · exact hf
  · refine (IsUnit.map _ (IsUnit.map _ (IsUnit.map _ ?_)))
    refine IsUnit.of_mul_eq_one (-q4) ?_
    linear_combination hq4

end Cone

/-! ### `Y Z − 1` -/

section Laurent

variable {R : Type*} [CommRing R] [IsDomain R]

local notation "MX" => MvPolynomial.X

/-- **`R[Y, Z]/(YZ − 1)` is a domain** (it is `R[Z][1/Z]`). -/
theorem isPrime_span_YZ : (Ideal.span {(MX 0 * MX 1 - 1 : MvPolynomial (Fin 2) R)}).IsPrime := by
  set T := MvPolynomial (Fin 1) R
  set r : T := MX 0
  have hr : r ≠ 0 := MvPolynomial.X_ne_zero _
  have : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have : IsDomain (AdjoinRoot (C r * X - 1)) := (Localization.awayEquivAdjoin
      r).symm.toMulEquiv.isDomain
  have hprime : (Ideal.span {(C r * X - 1 : T[X])}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (inferInstanceAs (IsDomain (AdjoinRoot (C r * X - 1))))
  apply isPrime_of_map_equiv (MvPolynomial.finSuccEquiv R 1).toRingEquiv
  rw [Ideal.map_span, Set.image_singleton]
  have e1 : MvPolynomial.finSuccEquiv R 1 (MX (1 : Fin 2)) = C (MX 0) :=
    MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have : (MvPolynomial.finSuccEquiv R 1).toRingEquiv (MX 0 * MX 1 - 1) = C r * X - 1 := by
    simp only [AlgEquiv.coe_toRingEquiv, map_sub, map_mul, map_one]
    rw [MvPolynomial.finSuccEquiv_X_zero, e1, mul_comm]
  rw [this]
  exact hprime

end Laurent

/-! ### Disjoint blocks -/

section Ind

variable {K : Type u} [Field K]

/-- The relations `r k`, placed in the `k`-th copy `{k} × B` of the variables. -/
noncomputable def gensProd {B : Type} {n : ℕ} (R : Type u) [CommRing R] [Algebra K R]
    (r : Fin n → MvPolynomial B K) : Set (MvPolynomial (Fin n × B) R) :=
  Set.range fun k => MvPolynomial.rename (Prod.mk k) (MvPolynomial.map (algebraMap K R) (r k))

/-- `Fin (n+1) × B ≃ (Fin n × B) ⊕ B`, splitting off the last copy. -/
def splitLast (n : ℕ) (B : Type) : Fin (n + 1) × B ≃ (Fin n × B) ⊕ B :=
  ((Equiv.prodCongr finSuccEquivLast (Equiv.refl B)).trans optionProdEquiv).trans
    (Equiv.sumComm _ _)

@[simp] theorem splitLast_castSucc (n : ℕ) (B : Type) (k : Fin n) (b : B) :
    splitLast n B (k.castSucc, b) = .inl (k, b) := by
  simp [splitLast, optionProdEquiv]

@[simp] theorem splitLast_last (n : ℕ) (B : Type) (b : B) :
    splitLast n B (Fin.last n, b) = .inr b := by
  simp [splitLast, optionProdEquiv]

/-- `R[Fin (n+1) × B] ≃ (R[B])[Fin n × B]`. -/
noncomputable def splitEquiv (n : ℕ) (B : Type) (R : Type*) [CommRing R] :
    MvPolynomial (Fin (n + 1) × B) R ≃ₐ[R] MvPolynomial (Fin n × B) (MvPolynomial B R) :=
  (MvPolynomial.renameEquiv R (splitLast n B)).trans (MvPolynomial.sumAlgEquiv R (Fin n × B) B)

theorem splitEquiv_castSucc {B : Type} {n : ℕ} {R : Type*} [CommRing R] (k : Fin n)
    (p : MvPolynomial B R) :
    splitEquiv n B R (MvPolynomial.rename (Prod.mk k.castSucc) p) =
      MvPolynomial.rename (Prod.mk k) (MvPolynomial.map MvPolynomial.C p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [splitEquiv, MvPolynomial.sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p b hp =>
    simp only [map_mul, hp, MvPolynomial.rename_X, MvPolynomial.map_X]
    congr 1
    simp [splitEquiv, MvPolynomial.sumAlgEquiv_X_inl]

theorem splitEquiv_last {B : Type} {n : ℕ} {R : Type*} [CommRing R] (p : MvPolynomial B R) :
    splitEquiv n B R (MvPolynomial.rename (Prod.mk (Fin.last n)) p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [splitEquiv, MvPolynomial.sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p b hp =>
    simp only [map_mul, hp, MvPolynomial.rename_X]
    congr 1
    simp [splitEquiv, MvPolynomial.sumAlgEquiv_X_inr]

set_option maxSynthPendingDepth 10 in
/-- **Disjoint blocks.** If each relation generates a prime ideal over every domain `K`-algebra,
the relations in disjoint copies of the variables generate a prime ideal. -/
theorem isPrime_span_gensProd {B : Type} (P : MvPolynomial B K → Prop)
    (hP : ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] (f : MvPolynomial B K), P f →
      (Ideal.span {MvPolynomial.map (algebraMap K R) f}).IsPrime) :
    ∀ (n : ℕ) (r : Fin n → MvPolynomial B K), (∀ k, P (r k)) →
      ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra K R], (Ideal.span (gensProd R r)).IsPrime
          := by
  intro n
  induction n with
  | zero =>
    intro r _ R _ _ _
    have : gensProd R r = ∅ := by
      simp only [gensProd, Set.range_eq_empty_iff]
      infer_instance
    rw [this, Ideal.span_empty]
    exact Ideal.isPrime_bot
  | succ n ih =>
    intro r hr R _ _ _
    set J : Ideal (MvPolynomial B R) :=
      Ideal.span {MvPolynomial.map (algebraMap K R) (r (Fin.last n))} with hJdef
    have hJ : J.IsPrime := hP R _ (hr _)
    set Φ := splitEquiv n B R
    set ψ : MvPolynomial (Fin n × B) (MvPolynomial B R) →+*
        MvPolynomial (Fin n × B) (MvPolynomial B R ⧸ J) := MvPolynomial.map (Ideal.Quotient.mk J)
    have hψ : Function.Surjective ψ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
    have halg : algebraMap K (MvPolynomial B R ⧸ J) =
        ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp (algebraMap K R) := by
      ext x
      rfl
    have hcs : ∀ k : Fin n, ψ (Φ (MvPolynomial.rename (Prod.mk k.castSucc)
        (MvPolynomial.map (algebraMap K R) (r k.castSucc)))) =
          MvPolynomial.rename (Prod.mk k)
            (MvPolynomial.map (algebraMap K (MvPolynomial B R ⧸ J)) (r k.castSucc)) := by
      intro k
      rw [show Φ _ = _ from splitEquiv_castSucc k _]
      simp only [ψ, MvPolynomial.map_rename, MvPolynomial.map_map, halg]
      rfl
    have hlast : ψ (Φ (MvPolynomial.rename (Prod.mk (Fin.last n))
        (MvPolynomial.map (algebraMap K R) (r (Fin.last n))))) = 0 := by
      rw [show Φ _ = _ from splitEquiv_last _]
      simp only [ψ, MvPolynomial.map_C, MvPolynomial.C_eq_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    apply isPrime_of_map_equiv Φ.toRingEquiv
    refine isPrime_of_map_surj ψ hψ _ ?_ ?_
    · rw [MvPolynomial.ker_map, Ideal.mk_ker, hJdef, Ideal.map_span, Set.image_singleton,
        Ideal.span_le, Set.singleton_subset_iff]
      rw [← show Φ _ = _ from splitEquiv_last (n := n)
        (MvPolynomial.map (algebraMap K R) (r (Fin.last n)))]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨_, rfl⟩)
    · have : ((Ideal.span (gensProd R r)).map Φ.toRingEquiv).map ψ =
          Ideal.span (gensProd (MvPolynomial B R ⧸ J) fun k => r k.castSucc) := by
        rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp]
        apply le_antisymm
        · rw [Ideal.span_le]
          rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
          induction k using Fin.lastCases with
          | last =>
            have h0 : (ψ ∘ Φ.toRingEquiv) (MvPolynomial.rename (Prod.mk (Fin.last n))
                (MvPolynomial.map (algebraMap K R) (r (Fin.last n)))) = 0 := hlast
            simp only [h0, SetLike.mem_coe]
            exact Ideal.zero_mem _
          | cast k =>
            refine Ideal.subset_span ⟨k, ?_⟩
            exact (hcs k).symm
        · rw [Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨_, ⟨k.castSucc, rfl⟩, hcs k⟩
      rw [this]
      exact ih _ (fun k => hr _) _

end Ind

end LSG.ME
