/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import StrongSix.M2.BridgeLow

/-!
# Transcendence degree, Krull dimension and StrongSix's Hilbert dimension

For a prime `p` of `K[σ] = MvPolynomial σ K` (`K` any field, `σ` finite):

* `ringKrullDim_quotient_eq_trdeg`: `dim (K[σ]/p) = trdeg_K (K[σ]/p)`, both finite. Proof: Noether
  normalisation (`exists_integral_inj_algHom_of_fg`) gives an integral injective `K[y₁..y_s] → K[σ]/p`;
  integral extensions preserve Krull dimension (incomparability and going up), and the transcendence
  degree is additive in towers with `trdeg = 0` for the algebraic top layer.
* `ringKrullDim_quotient_le_hdim`: `dim (K[σ]/p) ≤ hdim p` (chains of primes strictly decrease `hdim`).
* `card_le_height_add_ringKrullDim_quotient`: `card σ ≤ ht p + dim (K[σ]/p)`, from the Cohen–Macaulay
  property of the localisation `K[σ]_m` at a maximal ideal `m ⊇ p`.
* With StrongSix's `hdim_add_height_eq` these combine to
  **`trdeg_add_height_eq`**: `trdeg_K (K[σ]/p) + ht p = card σ`, and
  **`hdim_eq_trdeg`**: `hdim p = trdeg_K (K[σ]/p)`.
-/

open MvPolynomial

namespace LSG.ME

universe u v w

/-! ### Krull dimension of integral extensions -/

section Integral

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- Incomparability: an integral extension has Krull dimension at most that of the base. -/
theorem ringKrullDim_le_of_isIntegral : ringKrullDim S ≤ ringKrullDim R := by
  let f : PrimeSpectrum S → PrimeSpectrum R := fun P =>
    ⟨P.asIdeal.comap (algebraMap R S), Ideal.comap_isPrime _ _⟩
  refine Order.krullDim_le_of_strictMono f fun P Q h => ?_
  exact Ideal.IsIntegral.under_lt_under (R := R) (show P.asIdeal < Q.asIdeal from h)

/-- Going up: an injective integral extension has Krull dimension at least that of the base. -/
theorem le_ringKrullDim_of_isIntegral [FaithfulSMul R S] : ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := S) l.head.asIdeal
  have : P.IsPrime := hP.1
  have : P.LiesOver l.head.asIdeal := hP.2
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem ringKrullDim_eq_of_isIntegral [FaithfulSMul R S] : ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral le_ringKrullDim_of_isIntegral

end Integral

/-! ### Dimension and transcendence degree via Noether normalisation -/

/-- Noether normalisation: for a finitely generated `K`-domain `B` there is `s` with
`dim B = s = trdeg_K B`. -/
theorem exists_ringKrullDim_eq_trdeg_of_fg {K : Type u} [Field K] (B : Type w) [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] :
    ∃ s : ℕ, ringKrullDim B = s ∧ Algebra.trdeg K B = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  let _ : Algebra (MvPolynomial (Fin s) K) B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) B := ⟨fun x => hint x⟩
  have : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr hinj
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) K) (S := B),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  · have h1 := lift_trdeg_add_eq K (MvPolynomial (Fin s) K) B
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := B),
      MvPolynomial.trdeg_of_isDomain] at h1
    simpa using h1.symm

variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

/-- Noether normalisation for `K[σ]/p`: there is `s` with `dim (K[σ]/p) = s = trdeg_K (K[σ]/p)`. -/
theorem exists_ringKrullDim_eq_trdeg (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ s : ℕ, ringKrullDim (MvPolynomial σ K ⧸ p) = s ∧
      Algebra.trdeg K (MvPolynomial σ K ⧸ p) = s :=
  exists_ringKrullDim_eq_trdeg_of_fg _

theorem trdeg_quotient_lt_aleph0 (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Algebra.trdeg K (MvPolynomial σ K ⧸ p) < Cardinal.aleph0 := by
  obtain ⟨s, -, hs⟩ := exists_ringKrullDim_eq_trdeg p
  rw [hs]
  exact Cardinal.natCast_lt_aleph0

/-- `dim (K[σ]/p) = trdeg_K (K[σ]/p)` for primes `p`. -/
theorem ringKrullDim_quotient_eq_trdeg (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ringKrullDim (MvPolynomial σ K ⧸ p) = ((Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat : ℕ∞) := by
  obtain ⟨s, hd, hs⟩ := exists_ringKrullDim_eq_trdeg p
  rw [hd, hs, Cardinal.toNat_natCast]
  rfl

/-! ### Comparison with the height and the Hilbert dimension -/

local notation "A" => MvPolynomial σ K

/-- `card σ ≤ ht p + dim (K[σ]/p)` (Cohen–Macaulay localisation at a maximal ideal over `p`). -/
theorem card_le_height_add_ringKrullDim_quotient (p : Ideal A) [hp : p.IsPrime] :
    ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  let Rm := Localization.AtPrime m
  have : IsCohenMacaulayLocalRing Rm :=
    (isCohenMacaulayRing_def A).mp inferInstance m hm.isPrime
  have disj : Disjoint (m.primeCompl : Set A) (p : Set A) :=
    Set.disjoint_left.mpr fun a ha hap => ha (hpm hap)
  let P := p.map (algebraMap A Rm)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl Rm p hp disj
  have hform := Ideal.primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim P
  rw [← Ideal.height_eq_primeHeight, IsLocalization.height_map_of_disjoint m.primeCompl p disj,
    IsLocalization.AtPrime.ringKrullDim_eq_height m Rm,
    StrongSix.M2.height_isMaximal K m] at hform
  let φ : A →+* Rm ⧸ P := (Ideal.Quotient.mk P).comp (algebraMap A Rm)
  have hφinj : ∀ Q : Ideal (Rm ⧸ P), Ideal.map φ (Ideal.comap φ Q) = Q := by
    intro Q
    have h1 : Ideal.comap φ Q = Ideal.comap (algebraMap A Rm) (Ideal.comap (Ideal.Quotient.mk P) Q) :=
      by rw [Ideal.comap_comap]
    rw [h1, ← Ideal.map_map, IsLocalization.map_under m.primeCompl Rm,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hker : ∀ a ∈ p, φ a = 0 := by
    intro a ha
    have : algebraMap A Rm a ∈ P := Ideal.mem_map_of_mem _ ha
    simp only [φ, RingHom.coe_comp, Function.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  let ψ : A ⧸ p →+* Rm ⧸ P := Ideal.Quotient.lift p φ hker
  have hψ : ψ.comp (Ideal.Quotient.mk p) = φ := Ideal.Quotient.lift_comp_mk p φ hker
  let f : PrimeSpectrum (Rm ⧸ P) → PrimeSpectrum (A ⧸ p) := fun Q =>
    ⟨Ideal.comap ψ Q.asIdeal, Ideal.comap_isPrime _ _⟩
  have hf : StrictMono f := by
    intro Q Q' hlt
    have hlt' : Q.asIdeal < Q'.asIdeal := hlt
    refine lt_of_le_of_ne (Ideal.comap_mono hlt'.le) fun h => hlt'.ne ?_
    have h2 : Ideal.comap φ Q.asIdeal = Ideal.comap φ Q'.asIdeal := by
      rw [← hψ, ← Ideal.comap_comap, ← Ideal.comap_comap]
      exact congrArg (Ideal.comap (Ideal.Quotient.mk p)) (congrArg PrimeSpectrum.asIdeal h)
    rw [← hφinj Q.asIdeal, ← hφinj Q'.asIdeal, h2]
  have hdim : ringKrullDim (Rm ⧸ P) ≤ ringKrullDim (A ⧸ p) := Order.krullDim_le_of_strictMono f hf
  rw [← hform]
  gcongr

section HDim

variable {ι : Type w} [Fintype ι] [DecidableEq ι] [DecidableEq σ] (β : σ → ι) (D : ι → ℕ)

/-- `dim (K[σ]/p) ≤ hdim p`: a chain of primes above `p` strictly decreases the Hilbert dimension. -/
theorem ringKrullDim_quotient_le_hdim (hD : ∀ i, 1 ≤ D i) (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) ≤ ((StrongSix.M2.hdata β D K p).1 : ℕ∞) := by
  let mk := Ideal.Quotient.mk p
  let g : PrimeSpectrum (A ⧸ p) → ℕ := fun Q => (StrongSix.M2.hdata β D K (Ideal.comap mk Q.asIdeal)).1
  have hg : StrictAnti g := by
    intro Q Q' hlt
    have hlt' : Q.asIdeal < Q'.asIdeal := hlt
    have hne : Ideal.comap mk Q.asIdeal ≠ Ideal.comap mk Q'.asIdeal := fun h =>
      hlt'.ne (Ideal.comap_injective_of_surjective mk Ideal.Quotient.mk_surjective h)
    have : (Ideal.comap mk Q.asIdeal).IsPrime := Ideal.comap_isPrime mk Q.asIdeal
    exact StrongSix.M2.hdim_lt_of_lt β D K hD (Ideal.comap_isPrime mk Q'.asIdeal).ne_top
      (lt_of_le_of_ne (Ideal.comap_mono hlt'.le) hne)
  have hple : ∀ Q : Ideal (A ⧸ p), p ≤ Ideal.comap mk Q :=
    fun Q => le_trans (le_of_eq Ideal.mk_ker.symm) (Ideal.ker_le_comap _)
  have hgle : ∀ Q, g Q ≤ (StrongSix.M2.hdata β D K p).1 := by
    intro Q
    rcases StrongSix.M2.hdata_le_of_le β D K (hple Q.asIdeal)
      (Ideal.comap_isPrime mk Q.asIdeal).ne_top with h | ⟨h, -⟩ <;> simp only [g] <;> omega
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun s => ?_
  have key : ∀ i : ℕ, ∀ hi : i < s.length + 1, g (s ⟨i, hi⟩) + i ≤ g (s 0) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : g (s ⟨i + 1, hi⟩) < g (s ⟨i, by omega⟩) :=
        hg (s.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)))
      omega
  have h1 := key s.length (Nat.lt_succ_self _)
  have h3 := hgle (s 0)
  have : s.length ≤ (StrongSix.M2.hdata β D K p).1 := by omega
  exact_mod_cast this

/-- `dim (K[σ]/p) + ht p = card σ` and `hdim p = dim (K[σ]/p)`. -/
theorem hdim_eq_ringKrullDim_quotient (hD : ∀ i, 1 ≤ D i) (p : Ideal A) [hp : p.IsPrime] :
    ringKrullDim (A ⧸ p) = ((StrongSix.M2.hdata β D K p).1 : ℕ∞) := by
  refine le_antisymm (ringKrullDim_quotient_le_hdim β D hD p) ?_
  have hb := StrongSix.M2.hdim_add_height_eq β D hD hp.ne_top
  have hc := card_le_height_add_ringKrullDim_quotient p
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hp.ne_top)
  rw [← hn] at hb hc
  obtain ⟨s, hs, -⟩ := exists_ringKrullDim_eq_trdeg p
  rw [hs] at hc ⊢
  have hc' : ((Fintype.card σ : ℕ∞)) ≤ (n : ℕ∞) + (s : ℕ∞) := by exact_mod_cast hc
  rw [← hb] at hc'
  have : (StrongSix.M2.hdata β D K p).1 + n ≤ n + s := by exact_mod_cast hc'
  have : (StrongSix.M2.hdata β D K p).1 ≤ s := by omega
  exact_mod_cast this

/-- **Bridge.** StrongSix's Hilbert dimension of a prime equals the transcendence degree. -/
theorem hdim_eq_trdeg (hD : ∀ i, 1 ≤ D i) (p : Ideal A) [hp : p.IsPrime] :
    ((StrongSix.M2.hdata β D K p).1 : ℕ) = (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat := by
  have h := (hdim_eq_ringKrullDim_quotient β D hD p).symm.trans (ringKrullDim_quotient_eq_trdeg p)
  exact_mod_cast h

end HDim

/-- **Dimension formula** for affine domains: `trdeg_K (K[σ]/p) + ht p = card σ`. -/
theorem trdeg_add_height_eq (p : Ideal A) [hp : p.IsPrime] :
    ((Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat : ℕ∞) + p.height = Fintype.card σ := by
  classical
  have h := StrongSix.M2.hdim_add_height_eq (fun _ : σ => ()) (fun _ => 1) (K := K)
    (fun _ => le_rfl) hp.ne_top
  rwa [hdim_eq_trdeg _ _ (fun _ => le_rfl) p] at h

end LSG.ME
