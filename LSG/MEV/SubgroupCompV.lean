import Mathlib
import LSG.MEV.SubgroupDimV

/-!
# Components, translates of irreducible sets, and `H / H⁰` finite (gap G3, rest)

Port of `LSG.ME.SubgroupComp` and `LSG.ME.SubgroupDim.finite_cosets_H0` to the vector-extension
model `G̃ = G_a^{d₀} × G_m^{d₁} × ∏ E_k^♮` (`LSG.MEV`).

* **`vanish_singleton_isPrime`**: `vanish {g}` is prime (kernel of `P ↦ P(coords g λ)` as a
  polynomial in `λ`).
* **`exists_components`**: a Zariski-closed set has finitely many components.
* **`vanish_gtransl_isPrime`**: translates of irreducible Zariski-closed sets are irreducible
  (laws `nlawc` of bidegree `(3, 3)`, good at one point of `V`).
* **`finrank_tangentSpace_zero_le'`**: for a closed subgroup `H`, the Zariski tangent space of
  `vanish H` at the `V`-normalised identity `FV 0` has dimension `≤ dim T′ + m`.
* **`trdeg_le_of_subset`**: every irreducible Zariski-closed `Y ⊆ H` through `0` has
  `trdeg ≤ dim T′ + m`.
* **`finite_cosets_H0`**: `H` is a finite union of cosets `h + H⁰`, `h ∈ H`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Module
open LSG.ME (tangentSpace)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Zariski-closed sets -/

theorem zeros_union (S T : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    (zeros (S ∪ T) : Set (GPtV d₀ d₁ Ls)) = zeros S ∩ zeros T := by
  ext g
  simp only [zeros, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩,
    fun h P hP => hP.elim (h.1 P) (h.2 P)⟩

theorem IsZClosed.inter {V W : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hW : IsZClosed W) :
    IsZClosed (V ∩ W) := by
  obtain ⟨S, rfl⟩ := hV
  obtain ⟨T, rfl⟩ := hW
  exact ⟨S ∪ T, (zeros_union S T).symm⟩

theorem vanish_empty' : vanish (∅ : Set (GPtV d₀ d₁ Ls)) = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_vanish.mpr fun _ hg => absurd hg (Set.notMem_empty _)

/-! ### `vanish {g}` is prime -/

/-- `P ↦ P(coords g λ)` as a polynomial in `λ`. -/
def evPt (g : GPtV d₀ d₁ Ls) : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  aeval fun v => match v with
    | .x i => C (g.1 i)
    | .y j => C (g.ym j : ℂ)
    | .z j => C (((g.ym j)⁻¹ : ℂˣ) : ℂ)
    | .e k c => X k * C (repV (g.2.2 k) c)

theorem eval_evPt (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (fun k => (lam k : ℂ)) (evPt g P) = eval (coords g lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evPt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, evPt, aeval_X, eval_X]
    congr 1
    cases v <;> simp [coords]

theorem vanish_singleton_isPrime (g : GPtV d₀ d₁ Ls) : (vanish {g}).IsPrime := by
  have e : vanish {g} =
      RingHom.ker (evPt g : MvPolynomial (Var d₀ d₁ m) ℂ →+* MvPolynomial (Fin m) ℂ) := by
    ext P
    rw [mem_vanish, RingHom.mem_ker]
    constructor
    · intro h
      refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => Set.Finite.infinite_compl
        (Set.finite_singleton 0)) fun x hx => ?_
      have hx' : ∀ k, x k ≠ 0 := fun k => hx k (Set.mem_univ k)
      have := h g rfl (fun k => Units.mk0 (x k) (hx' k))
      rw [← eval_evPt] at this
      simpa using this
    · intro h g' hg' lam
      rw [Set.mem_singleton_iff] at hg'
      subst hg'
      rw [← eval_evPt, AlgHom.coe_toRingHom] at *
      rw [h, map_zero]
  rw [e]
  exact RingHom.ker_isPrime _

/-! ### Components -/

/-- **Components.** -/
theorem exists_components {H : Set (GPtV d₀ d₁ Ls)} :
    ∃ ps : Finset (Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)),
      (∀ p ∈ ps, p.IsPrime ∧ vanish H ≤ p ∧
        vanish (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) = p) ∧
      ∀ q : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ), q.IsPrime → vanish H ≤ q → ∃ p ∈ ps, p ≤ q := by
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

/-! ### Translates of irreducible sets -/

/-- **Translates of irreducible Zariski-closed sets are irreducible.** -/
theorem vanish_gtransl_isPrime {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (h : GPtV d₀ d₁ Ls) : (vanish (gtransl h V)).IsPrime := by
  classical
  have hne : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hp.ne_top vanish_empty'
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨c₀, hc₀⟩ := exists_good v₀ h
  choose i hi using fun k => Function.ne_iff.mp (hc₀ k)
  let L : MvPolynomial (Var d₀ d₁ m) ℂ := ∏ k, lawPolyV Ls d₀ d₁ (c₀ k) k (repV (h.2.2 k)) (i k)
  have hL : ∀ (v : GPtV d₀ d₁ Ls) lam, eval (coords v lam) L =
      ∏ k, (lam k : ℂ) ^ 3 * nlawc (c₀ k) (Ls k).g₂ (Ls k).g₃ (repV (v.2.2 k))
        (repV (h.2.2 k)) (i k) := by
    intro v lam
    simp only [L, map_prod, eval_lawPolyV]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (fun c => coords v lam (.e k c)) = (lam k : ℂ) • repV (v.2.2 k) := by
      funext c; simp [coords]
    rw [this, nlawc_smul_left]
    simp
  have hLV : L ∉ vanish V := fun hmem => by
    have := mem_vanish.mp hmem v₀ hv₀ 1
    rw [hL] at this
    simp only [Pi.one_apply, Units.val_one, one_pow, one_mul] at this
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp this
    exact hi k hk
  let φ : MvPolynomial (Var d₀ d₁ m) ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish V :=
    (Ideal.Quotient.mk (vanish V)).comp (τ Ls h c₀).toRingHom
  have e : vanish (gtransl h V) = RingHom.ker φ := by
    ext P
    rw [RingHom.mem_ker]
    simp only [φ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hP
      refine mem_vanish.mpr fun v hv lam => ?_
      obtain ⟨ν, hν⟩ := eval_transl h v c₀ lam
      rw [hν]
      exact eval_coordsZ_eq_zero (mem_vanish.mp hP _ ⟨v, hv, rfl⟩) ν
    · intro hP
      set G := V ∩ {v | v + h ∈ (zeros ({P} : Set _) : Set (GPtV d₀ d₁ Ls))}
      have hGc : IsZClosed G := by
        refine hV.inter ⟨(translI Ls h (Ideal.span {P}) : Set _), ?_⟩
        rw [zeros_translI]
        ext w
        simp only [Set.mem_ofPred_eq]
        rw [mem_zeros_span]
      have hVG : V ⊆ G := by
        have hvan : vanish G ≤ vanish V := by
          intro Q hQ
          have hQL : Q * L ∈ vanish V := by
            refine mem_vanish.mpr fun v hv lam => ?_
            by_cases hvG : v ∈ G
            · rw [map_mul, mem_vanish.mp hQ v hvG lam, zero_mul]
            · have hLv : eval (coords v 1) L = 0 := by
                by_contra hLv
                apply hvG
                refine ⟨hv, ?_⟩
                have hgood : Good v h c₀ := by
                  intro k hk
                  rw [hL] at hLv
                  exact hLv (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp))
                obtain ⟨μ, hμ⟩ := eval_transl_good hgood
                intro R hR lam'
                rw [Set.mem_singleton_iff] at hR
                subst hR
                obtain ⟨l, hl⟩ := exists_cube_mul μ lam'
                rw [← hl, ← hμ]
                exact mem_vanish.mp hP v hv l
              have : eval (coords v lam) L = 0 := by
                rw [hL]; rw [hL] at hLv
                simp only [Pi.one_apply, Units.val_one, one_pow, one_mul] at hLv
                obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hLv
                exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, mul_zero])
              rw [map_mul, this, mul_zero]
          exact (hp.mem_or_mem hQL).resolve_right hLV
        intro v hv
        rw [← zeros_vanish hGc]
        exact fun Q hQ lam => mem_vanish.mp (hvan hQ) v hv lam
      refine mem_vanish.mpr ?_
      rintro _ ⟨v, hv, rfl⟩ lam
      exact (hVG hv).2 P rfl lam
  rw [e]
  exact RingHom.ker_isPrime _

/-! ### The tangent space of `vanish H` at the identity -/

section Tan

variable {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H)
include hc

/-- **Upper bound at the identity, for `vanish H`**: `dim T_{a₀}(vanish H) ≤ dim T′ + m`. -/
theorem finrank_tangentSpace_zero_le' :
    finrank ℂ (tangentSpace (vanish H) (FV Ls 0)) ≤ finrank ℂ (lieAlg Ls hH) + m := by
  classical
  set T := tangentSpace (vanish H) (FV Ls (0 : TanG d₀ d₁ m))
  obtain ⟨ν, hν⟩ := FV_eq_coords (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
  have h0H : expGV Ls 0 ∈ H := by rw [expGV_zero]; exact hH.zero_mem
  have htan : ∀ v ∈ T, ∀ f ∈ vanish H, eval (FV Ls 0) (dirDer v f) = 0 := by
    intro v hv f hf; rw [eval_dirDer]; exact hv f hf
  have hYZ : ∀ j, YZ ℂ d₀ m j ∈ vanish H := fun j =>
    mem_vanish.mpr fun g _ lam => by simp [YZ, coords]
  have hFk : ∀ k, Fk (LSG.ME.g2L Ls) (LSG.ME.g3L Ls) d₀ d₁ k ∈ vanish H := fun k =>
    mem_vanish.mpr fun g _ lam => eval_coords_Fk g _ k
  have hGk : ∀ k, Gk ℂ d₀ d₁ k ∈ vanish H := fun k =>
    mem_vanish.mpr fun g _ lam => eval_coords_Gk g _ k
  have hrec : ∀ v ∈ T, v = fun i => DV Ls (tanCoord v).1 (FV Ls 0) i +
      ∑ k, (tanCoord v).2 k * blockPart k (FV Ls 0) i := by
    intro v hv
    funext i
    rw [DV_of_V Ls (FV_V goodV_zero)]
    cases i with
    | x i => simp [dvalE, tanCoord, blockPart]
    | y j => simp [dvalE, tanCoord, blockPart, a0_y]
    | z j =>
      have := htan v hv _ (hYZ j)
      simp [YZ, dirDer, Derivation.leibniz, a0_y, a0_z] at this
      simp [dvalE, tanCoord, blockPart, a0_z]
      linear_combination this
    | e k c =>
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [blockPart, Ne.symm hb]) (by simp)]
      simp only [blockPart, ite_true, dvalE, a0_e, tanCoord]
      have hF := htan v hv _ (hFk k)
      have hG := htan v hv _ (hGk k)
      simp [Fk, F, Gk, Gfib, dirDer, Derivation.leibniz, Derivation.leibniz_pow, a0_e, ptO]
        at hF hG
      fin_cases c <;> simp [bField, ptO, hF, hG] <;> ring
  have himg : ∀ v ∈ T, (tanCoord v).1 ∈ lieAlg Ls hH := by
    intro v hv
    rw [← TZ_eq_lieAlg hH hc]
    intro Q hQ
    have h := hv Q hQ
    rw [hrec v hv] at h
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    have heul : ∀ k ∈ Finset.univ, ∑ i, (tanCoord v).2 k * blockPart k (FV Ls 0) i *
        eval (FV Ls 0) (pderiv i Q) = 0 := fun k _ => by
      have := euler_eq_zero hQ h0H ν k
      rw [← hν] at this
      simp only [mul_assoc, mul_comm (blockPart k (FV Ls 0) _), ← Finset.mul_sum, this, mul_zero]
    rw [Finset.sum_eq_zero heul, add_zero] at h
    rw [eval_Dh]
    simpa [mul_comm] using h
  let Φ : T →ₗ[ℂ] lieAlg Ls hH × (Fin m → ℂ) :=
    { toFun := fun v => (⟨(tanCoord v.1).1, himg v.1 v.2⟩, (tanCoord v.1).2)
      map_add' := fun v v' => by
        ext <;> simp [tanCoord_linear.map_add]
      map_smul' := fun c v => by
        ext <;> simp [tanCoord_linear.map_smul] }
  have hinj : Function.Injective Φ := by
    intro v v' h
    have h1 : tanCoord v.1 = tanCoord v'.1 := by
      have e1 := congrArg (fun x => (x.1 : TanG d₀ d₁ m)) h
      have e2 := congrArg Prod.snd h
      exact Prod.ext e1 e2
    exact Subtype.ext (by rw [hrec v.1 v.2, hrec v'.1 v'.2, h1])
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun] at this

/-- **Upper bound** for irreducible closed subsets of `H` through `0`. -/
theorem trdeg_le_of_subset {Y : Set (GPtV d₀ d₁ Ls)} [(vanish Y).IsPrime] (hYH : Y ⊆ H)
    (h0 : (0 : GPtV d₀ d₁ Ls) ∈ Y) :
    (Algebra.trdeg ℂ (MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish Y)).toNat ≤
      finrank ℂ (lieAlg Ls hH) + m := by
  obtain ⟨ν, hν⟩ := FV_eq_coords (goodV_zero (Ls := Ls) (d₀ := d₀) (d₁ := d₁))
  have ha : FV Ls (0 : TanG d₀ d₁ m) ∈ zeroLocus ℂ (vanish Y) := by
    rw [mem_zeroLocus_iff]
    intro f hf
    rw [hν]
    exact mem_vanish.mp hf _ (by rw [expGV_zero]; exact h0) ν
  have hmono : tangentSpace (vanish Y) (FV Ls (0 : TanG d₀ d₁ m)) ≤
      tangentSpace (vanish H) (FV Ls 0) :=
    fun v hv f hf => hv f (vanish_antitone hYH hf)
  calc _ ≤ finrank ℂ (tangentSpace (vanish Y) (FV Ls (0 : TanG d₀ d₁ m))) :=
        LSG.ME.trdeg_le_finrank_tangentSpace (vanish Y) _ ha
    _ ≤ finrank ℂ (tangentSpace (vanish H) (FV Ls (0 : TanG d₀ d₁ m))) :=
        Submodule.finrank_mono hmono
    _ ≤ _ := finrank_tangentSpace_zero_le' hH hc

end Tan

/-! ### `H / H⁰` is finite -/

/-- **`H` is a finite union of cosets of `H⁰`.** -/
theorem finite_cosets_H0 {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ∃ R : Finset (GPtV d₀ d₁ Ls), (∀ h ∈ R, h ∈ H) ∧ H ⊆ ⋃ h ∈ R, gtransl h (H0 Ls hH) := by
  classical
  have hp0 := vanish_H0_isPrime (Ls := Ls) hH
  have hc0 := isZClosed_H0 (Ls := Ls) hH
  have h0 : (0 : GPtV d₀ d₁ Ls) ∈ H0 Ls hH := (H0_isSubgroup hH).zero_mem
  obtain ⟨ps, hps, hmin⟩ := exists_components (H := H)
  have key : ∀ h ∈ H, ∃ p ∈ ps, (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) =
      gtransl h (H0 Ls hH) := by
    intro h hh
    set C := gtransl h (H0 Ls hH)
    have hCp : (vanish C).IsPrime := vanish_gtransl_isPrime hc0 hp0 h
    have hCH : C ⊆ H := by
      rintro _ ⟨u, hu, rfl⟩
      exact hH.add_mem u (H0_subset hH hc hu) h hh
    obtain ⟨p, hp, hpC⟩ := hmin _ hCp (vanish_antitone hCH)
    obtain ⟨hpr, hpH, hpv⟩ := hps p hp
    set Vp : Set (GPtV d₀ d₁ Ls) := zeros (p : Set _)
    have hVpc : IsZClosed Vp := isZClosed_zeros _
    have hCV : C ⊆ Vp := by
      have hCc : IsZClosed C := isZClosed_gtransl hc0 h
      rw [← zeros_vanish hCc]
      intro g hg P hP lam
      exact hg P (hpC hP) lam
    have hVpH : Vp ⊆ H := by
      rw [← zeros_vanish hc]
      intro g hg P hP lam
      exact hg P (hpH hP) lam
    set Y := gtransl (-h) Vp
    have hYp : (vanish Y).IsPrime := vanish_gtransl_isPrime hVpc (hpv ▸ hpr) (-h)
    have hYH : Y ⊆ H := by
      rintro _ ⟨u, hu, rfl⟩
      exact hH.add_mem u (hVpH hu) (-h) (hH.neg_mem h hh)
    have hH0Y : H0 Ls hH ⊆ Y := by
      intro u hu
      rw [mem_gtransl, sub_neg_eq_add]
      exact hCV ⟨u, hu, rfl⟩
    have hY0 : (0 : GPtV d₀ d₁ Ls) ∈ Y := hH0Y h0
    have hle := trdeg_le_of_subset hH hc hYH hY0
    have heq : vanish Y = vanish (H0 Ls hH) := by
      refine le_antisymm (vanish_antitone hH0Y) (by_contra fun hne => ?_)
      have hlt : vanish Y < vanish (H0 Ls hH) :=
        lt_of_le_of_ne (vanish_antitone hH0Y) fun e => hne e.ge
      have := StrongSix.M2.hdim_lt_of_lt blk (fun _ => 1) ℂ (fun _ => le_rfl)
        (q := vanish Y) (q' := vanish (H0 Ls hH)) hp0.ne_top hlt
      rw [LSG.ME.hdim_eq_trdeg blk _ (fun _ => le_rfl),
        LSG.ME.hdim_eq_trdeg blk _ (fun _ => le_rfl), trdeg_H0 hH hc] at this
      omega
    have hYc : IsZClosed Y := isZClosed_gtransl hVpc (-h)
    have hYeq : Y = H0 Ls hH := vanish_injOn hYc hc0 heq
    refine ⟨p, hp, ?_⟩
    change Vp = gtransl h (H0 Ls hH)
    have hb : Vp = gtransl h Y := by rw [gtransl_gtransl, neg_add_cancel, gtransl_zero]
    rw [hb, hYeq]
  let rp : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) → GPtV d₀ d₁ Ls := fun p =>
    if hp : ∃ h ∈ H, (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) = gtransl h (H0 Ls hH) then
      Classical.choose hp else 0
  refine ⟨ps.image rp, fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hh
    simp only [rp]
    split_ifs with hp
    · exact (Classical.choose_spec hp).1
    · exact hH.zero_mem
  · obtain ⟨p, hp, hpe⟩ := key h hh
    have hex : ∃ h' ∈ H, (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) = gtransl h' (H0 Ls hH) :=
      ⟨h, hh, hpe⟩
    have hmem : h ∈ (zeros (p : Set _) : Set (GPtV d₀ d₁ Ls)) := by
      rw [hpe, mem_gtransl, sub_self]; exact h0
    simp only [Set.mem_iUnion]
    refine ⟨rp p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    have hrp : rp p = Classical.choose hex := by simp only [rp, hex, ↓reduceDIte]
    rw [hrp, ← (Classical.choose_spec hex).2]
    exact hmem

end

end LSG.MEV
