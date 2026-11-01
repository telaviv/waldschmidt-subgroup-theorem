/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dRat

/-!
# The tangent space `T(B^♮) = perTanId t` of the universal vector extension of an abelian subvariety

For an abelian tangent `t ⊂ ℂ^m` and a chart `c` of `t` (coordinates `ι : Fin g → Fin m`, `g = dim
t`):
* `perTanId_bij`: the coordinate projection `P(z, w) = (z ∘ ι, w ∘ ι)` maps `perTanId t` bijectively
  onto `ℂ^g × ℂ^g` (Legendre's relation for each curve gives surjectivity; `perTanId t` is spanned
  by `2g` vectors, which gives injectivity). So `B^♮ → (E^J)^♮` is an isogeny on tangent spaces.
* `perQ`: the inverse `ℂ^g × ℂ^g → perTanId t`, with `perQ (μ, x) = (lift μ, perK μ + perN x)`.
* `algLin_perK`, `algLin_perN`, `algLin_lift`: algebraic, when `perTanId t` is `ℚ̄`-rational
  (`exists_alg_preimage`).
-/

open Complex Module

namespace LSG.W88.V5d

open LSG.W88.Vec

/-! ### Algebraic preimages -/

lemma algPair_add {a b : ℕ} {u v : (Fin a → ℂ) × (Fin b → ℂ)} (hu : AlgPair u) (hv : AlgPair v) :
    AlgPair (u + v) := ⟨algVec_add hu.1 hv.1, algVec_add hu.2 hv.2⟩

lemma algPair_smul {a b : ℕ} {c : ℂ} (hc : IsAlgebraic ℚ c) {u : (Fin a → ℂ) × (Fin b → ℂ)}
    (hu : AlgPair u) : AlgPair (c • u) := ⟨algVec_smul hc hu.1, algVec_smul hc hu.2⟩

lemma algPair_sum {a b : ℕ} {κ : Type*} (s : Finset κ) (u : κ → (Fin a → ℂ) × (Fin b → ℂ))
    (hu : ∀ i ∈ s, AlgPair (u i)) : AlgPair (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using algVec_zero, by simpa using algVec_zero⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact algPair_add (hu a (Finset.mem_insert_self _ _))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- **Algebraic preimages.** If `S` is `ℚ̄`-rational and `P` algebraic, every algebraic vector of
`P(S)` is `P` of an algebraic vector of `S`. -/
lemma exists_alg_preimage {a b : ℕ} {ι : Type*} [Fintype ι]
    {S : Submodule ℂ ((Fin a → ℂ) × (Fin b → ℂ))} (hS : RatPair S)
    (P : ((Fin a → ℂ) × (Fin b → ℂ)) →ₗ[ℂ] (ι → ℂ))
    (hP : ∀ v, AlgPair v → ∀ i, IsAlgebraic ℚ (P v i)) {e : ι → ℂ} (he : e ∈ S.map P)
    (hea : ∀ i, IsAlgebraic ℚ (e i)) : ∃ s ∈ S, AlgPair s ∧ P s = e := by
  classical
  set Sa := {v | v ∈ S ∧ AlgPair v} with hSa
  have hspan : S.map P = Submodule.span ℂ (P '' Sa) := by
    conv_lhs => rw [hS]
    rw [Submodule.map_span]
  obtain ⟨bs, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ (P '' Sa)
  have : Finite bs := hli.finite
  have : Fintype bs := Fintype.ofFinite bs
  set n := Fintype.card bs
  let eqv : Fin n ≃ bs := (Fintype.equivFin bs).symm
  let col : Fin n → ι → ℂ := fun j => (eqv j : ι → ℂ)
  have hcol : ∀ j, ∃ v, v ∈ Sa ∧ P v = col j := fun j => hbS (eqv j).2
  choose pre hpre hPpre using hcol
  have hcolalg : ∀ j i, IsAlgebraic ℚ (col j i) := fun j i => by
    rw [← hPpre j]; exact hP _ (hpre j).2 i
  let R : Matrix ι (Fin n) K11.Kq := Matrix.of fun i j => ⟨col j i, K11.mem_Kq.mpr (hcolalg j i)⟩
  set Rc : Matrix ι (Fin n) ℂ := R.map K11.Kq.subtype with hRc_def
  have hRc : ∀ c : Fin n → ℂ, Rc.mulVec c = ∑ j, c j • col j := by
    intro c; ext i
    simp only [hRc_def, R, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
      Subfield.coe_subtype, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hlic : LinearIndependent ℂ col := hli.comp eqv eqv.injective
  have hinj : LinearMap.ker R.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Matrix.mulVecLin_apply] at hc
    have h1 : Rc.mulVec (fun j => (c j : ℂ)) = 0 := by
      ext i
      have := congrArg (fun v => ((v i : K11.Kq) : ℂ)) hc
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      push_cast at this
      simp only [hRc_def, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
      exact this
    rw [hRc] at h1
    have := Fintype.linearIndependent_iff.mp hlic _ h1
    funext j; exact Subtype.ext (this j)
  obtain ⟨gK, hg⟩ := R.mulVecLin.exists_leftInverse_of_injective hinj
  set Lm := LinearMap.toMatrix' gK with hLm
  have hLR : Lm * R = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  have hLRc : Lm.map K11.Kq.subtype * Rc = 1 := by
    rw [hRc_def, ← Matrix.map_mul, hLR]; simp
  have he' : e ∈ Submodule.span ℂ (Set.range col) := by
    rw [hspan, ← hbspan] at he
    have : Set.range col = (bs : Set (ι → ℂ)) := by
      ext x; constructor
      · rintro ⟨j, rfl⟩; exact (eqv j).2
      · intro hx; exact ⟨eqv.symm ⟨x, hx⟩, by simp [col]⟩
    rwa [this]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp he'
  have hc' : c = (Lm.map K11.Kq.subtype).mulVec e := by
    rw [← hc, ← hRc, Matrix.mulVec_mulVec, hLRc, Matrix.one_mulVec]
  have hcalg : ∀ j, IsAlgebraic ℚ (c j) := by
    intro j
    rw [hc', ← K11.mem_Kq]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subfield.coe_subtype]
    exact K11.Kq.sum_mem fun i _ => K11.Kq.mul_mem (SetLike.coe_mem _) (K11.mem_Kq.mpr (hea i))
  refine ⟨∑ j, c j • pre j, Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpre j).1,
    algPair_sum _ _ fun j _ => algPair_smul (hcalg j) (hpre j).2, ?_⟩
  rw [map_sum]
  simp only [map_smul, hPpre]
  exact hc

/-! ### `η` on lattice vectors -/

section Eta

variable {m : ℕ} (Ls : Fin m → PeriodPair)

/-- Vectors with every coordinate a period. -/
def LatVec (x : Fin m → ℂ) : Prop := ∀ j, x j ∈ (Ls j).lattice

lemma latVec_add {x y : Fin m → ℂ} (hx : LatVec Ls x) (hy : LatVec Ls y) : LatVec Ls (x + y) :=
  fun j => (Ls j).lattice.add_mem (hx j) (hy j)

lemma latVec_zsmul {x : Fin m → ℂ} (hx : LatVec Ls x) (n : ℤ) : LatVec Ls (n • x) :=
  fun j => by simpa using zsmul_mem (hx j) n

lemma latVec_zero : LatVec Ls (0 : Fin m → ℂ) := fun j => (Ls j).lattice.zero_mem

lemma etaV_zero' : etaV Ls (0 : Fin m → ℂ) = 0 := by
  funext j; exact LSG.Weierstrass.eta_zero (Ls j)

lemma etaV_add {x y : Fin m → ℂ} (hx : LatVec Ls x) (hy : LatVec Ls y) :
    etaV Ls (x + y) = etaV Ls x + etaV Ls y := by
  funext j; exact LSG.Weierstrass.eta_add (Ls j) (hx j) (hy j)

lemma etaV_zsmul {x : Fin m → ℂ} (hx : LatVec Ls x) (n : ℤ) :
    etaV Ls (n • x) = n • etaV Ls x := by
  funext j
  simp only [etaV, Pi.smul_apply, zsmul_eq_mul]
  exact LSG.Weierstrass.eta_zsmul (Ls j) (hx j) n

lemma latVec_sum {κ : Type*} (s : Finset κ) (x : κ → Fin m → ℂ) (hx : ∀ i ∈ s, LatVec Ls (x i)) :
    LatVec Ls (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using latVec_zero Ls
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact latVec_add Ls (hx a (Finset.mem_insert_self _ _))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

lemma etaV_sum {κ : Type*} (s : Finset κ) (x : κ → Fin m → ℂ) (hx : ∀ i ∈ s, LatVec Ls (x i)) :
    etaV Ls (∑ i ∈ s, x i) = ∑ i ∈ s, etaV Ls (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using etaV_zero' Ls
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, etaV_add Ls (hx a (Finset.mem_insert_self _ _))
      (latVec_sum Ls s x fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

lemma fst_mem_of_mem_perTanId {t : Submodule ℂ (Fin m → ℂ)} {p : (Fin m → ℂ) × (Fin m → ℂ)}
    (hp : p ∈ perTanId Ls t) : p.1 ∈ t := by
  induction hp using Submodule.span_induction with
  | mem x hx => exact hx.1
  | zero => exact t.zero_mem
  | add x y _ _ hx hy => exact t.add_mem hx hy
  | smul c x _ hx => exact t.smul_mem c hx

end Eta

/-! ### The isogeny `B^♮ → (E^J)^♮` on tangent spaces -/

section Chart

variable {m : ℕ} {Ls : Fin m → PeriodPair} {t : Submodule ℂ (Fin m → ℂ)} (c : LSG.CM.Chart t)

/-- `P(z, w) = (z ∘ ι, w ∘ ι)`. -/
noncomputable def perP : ((Fin m → ℂ) × (Fin m → ℂ)) →ₗ[ℂ]
    ((Fin (finrank ℂ t) → ℂ) × (Fin (finrank ℂ t) → ℂ)) :=
  LinearMap.prodMap (LSG.CM.proj c.ι) (LSG.CM.proj c.ι)

lemma perP_apply (p : (Fin m → ℂ) × (Fin m → ℂ)) :
    perP c p = (LSG.CM.proj c.ι p.1, LSG.CM.proj c.ι p.2) := rfl

/-- The basic periods `ω_a e_k` of `∏ₖ E_{ι k}`. -/
noncomputable def omg (k : Fin (finrank ℂ t)) (a : Fin 2) : ℂ :=
  if a = 0 then (Ls (c.ι k)).ω₁ else (Ls (c.ι k)).ω₂

lemma omg_mem (k : Fin (finrank ℂ t)) (a : Fin 2) :
    omg (Ls := Ls) c k a ∈ (Ls (c.ι k)).lattice := by
  unfold omg; split_ifs
  · exact (Ls (c.ι k)).ω₁_mem_lattice
  · exact (Ls (c.ι k)).ω₂_mem_lattice

lemma single_omg_lat (k : Fin (finrank ℂ t)) (a : Fin 2) (k' : Fin (finrank ℂ t)) :
    (Pi.single k (omg (Ls := Ls) c k a) : Fin (finrank ℂ t) → ℂ) k' ∈ (Ls (c.ι k')).lattice := by
  by_cases h : k' = k
  · subst h; simpa using omg_mem c k' a
  · simp [h, (Ls (c.ι k')).lattice.zero_mem]

lemma exists_uniformN (ht : IsAbelianTangent Ls t) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ k a, LatVec Ls (c.lift (N • Pi.single k (omg (Ls := Ls) c k a))) := by
  classical
  have h := fun p : Fin (finrank ℂ t) × Fin 2 => c.exists_nsmul_lift_mem ht
    (single_omg_lat (Ls := Ls) c p.1 p.2)
  choose n hn hlat using h
  refine ⟨∏ p, n p, Finset.prod_ne_zero_iff.mpr fun p _ => hn p, fun k a j => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (k, a))
  rw [hq, mul_comm, mul_smul, map_nsmul]
  simpa using nsmul_mem (hlat (k, a) j) q

variable (Ls) in
lemma proj_etaV (z : Fin m → ℂ) :
    LSG.CM.proj c.ι (etaV Ls z) = etaV (Ls ∘ c.ι) (LSG.CM.proj c.ι z) := rfl

/-- **`P` is a bijection `perTanId t → ℂ^g × ℂ^g`.** -/
theorem perTanId_bij (ht : IsAbelianTangent Ls t) :
    Function.Bijective ((perP c).domRestrict (perTanId Ls t)) := by
  classical
  set g := finrank ℂ t
  set S := perTanId Ls t with hS
  obtain ⟨N, hN, hNlat⟩ := exists_uniformN c ht
  let lam : Fin g × Fin 2 → Fin m → ℂ := fun p =>
    c.lift (N • Pi.single p.1 (omg (Ls := Ls) c p.1 p.2))
  let gen : Fin g × Fin 2 → (Fin m → ℂ) × (Fin m → ℂ) := fun p => (lam p, etaV Ls (lam p))
  have hgenS : ∀ p, gen p ∈ S := fun p =>
    Submodule.subset_span ⟨c.lift_mem _, hNlat p.1 p.2, rfl⟩
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  -- `P (gen p) = N • (ω_a e_k, η(ω_a) e_k)`
  have hPgen : ∀ p, perP c (gen p) = (N : ℂ) • ((Pi.single p.1 (omg (Ls := Ls) c p.1 p.2) :
      Fin g → ℂ), (Pi.single p.1 (LSG.Weierstrass.eta (Ls (c.ι p.1)) (omg (Ls := Ls) c p.1 p.2)) :
        Fin g → ℂ)) := by
    rintro ⟨k₀, a⟩
    have h1 : LSG.CM.proj c.ι (lam (k₀, a)) = N • Pi.single k₀ (omg (Ls := Ls) c k₀ a) :=
      c.proj_lift _
    rw [perP_apply]
    refine Prod.ext ?_ ?_
    · change LSG.CM.proj c.ι (lam (k₀, a)) = (N : ℂ) • _
      rw [h1, Nat.cast_smul_eq_nsmul]
    · change LSG.CM.proj c.ι (etaV Ls (lam (k₀, a))) = (N : ℂ) • _
      rw [proj_etaV, h1]
      funext k
      simp only [etaV, Function.comp_apply, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      by_cases hk : k = k₀
      · subst hk
        simp only [Pi.single_eq_same]
        have := LSG.Weierstrass.eta_zsmul (Ls (c.ι k)) (omg_mem c k a) (N : ℤ)
        push_cast at this; exact this
      · simp [hk]
  -- surjectivity: the image is everything (Legendre)
  have hmapTop : S.map (perP c) = ⊤ := by
    rw [eq_top_iff]
    have hbasis : ∀ p : Fin g × Fin 2, ((Pi.single p.1 (omg (Ls := Ls) c p.1 p.2) : Fin g → ℂ),
        (Pi.single p.1 (LSG.Weierstrass.eta (Ls (c.ι p.1)) (omg (Ls := Ls) c p.1 p.2)) :
          Fin g → ℂ)) ∈ S.map (perP c) := by
      intro p
      have : (N : ℂ)⁻¹ • perP c (gen p) ∈ S.map (perP c) :=
        Submodule.smul_mem _ _ ⟨gen p, hgenS p, rfl⟩
      rwa [hPgen, smul_smul, inv_mul_cancel₀ hNC, one_smul] at this
    have he : ∀ k, ((Pi.single k 1 : Fin g → ℂ), (0 : Fin g → ℂ)) ∈ S.map (perP c) ∧
        ((0 : Fin g → ℂ), (Pi.single k 1 : Fin g → ℂ)) ∈ S.map (perP c) := by
      intro k
      set L := Ls (c.ι k)
      set η₁ := LSG.Weierstrass.eta L L.ω₁
      set η₂ := LSG.Weierstrass.eta L L.ω₂
      have hΔ : η₁ * L.ω₂ - η₂ * L.ω₁ ≠ 0 := LSG.Weierstrass.legendre_ne_zero L
      have b0 := hbasis (k, 0)
      have b1 := hbasis (k, 1)
      simp only [omg, ite_true, show ((1 : Fin 2) = 0) ↔ False by decide,
        ite_false] at b0 b1
      have hs : ∀ x : ℂ, (Pi.single k x : Fin g → ℂ) = x • Pi.single k 1 := by
        intro x; ext i; by_cases hi : i = k
        · subst hi; simp
        · simp [hi]
      have hΔ' : η₂ * L.ω₁ - η₁ * L.ω₂ ≠ 0 := fun h => hΔ (by linear_combination -h)
      have c1 : η₂ / (η₂ * L.ω₁ - η₁ * L.ω₂) * L.ω₁ + -η₁ / (η₂ * L.ω₁ - η₁ * L.ω₂) * L.ω₂ = 1 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hΔ']; ring
      have c2 : η₂ / (η₂ * L.ω₁ - η₁ * L.ω₂) * η₁ + -η₁ / (η₂ * L.ω₁ - η₁ * L.ω₂) * η₂ = 0 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]; left; ring
      have c3 : -L.ω₂ / (η₂ * L.ω₁ - η₁ * L.ω₂) * L.ω₁ +
          L.ω₁ / (η₂ * L.ω₁ - η₁ * L.ω₂) * L.ω₂ = 0 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]; left; ring
      have c4 : -L.ω₂ / (η₂ * L.ω₁ - η₁ * L.ω₂) * η₁ + L.ω₁ / (η₂ * L.ω₁ - η₁ * L.ω₂) * η₂ = 1 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hΔ']; ring
      constructor
      · have : ((Pi.single k 1 : Fin g → ℂ), (0 : Fin g → ℂ)) =
            (η₂ / (η₂ * L.ω₁ - η₁ * L.ω₂)) • ((Pi.single k L.ω₁ : Fin g → ℂ),
              (Pi.single k η₁ : Fin g → ℂ)) +
            (-η₁ / (η₂ * L.ω₁ - η₁ * L.ω₂)) • ((Pi.single k L.ω₂ : Fin g → ℂ),
              (Pi.single k η₂ : Fin g → ℂ)) := by
          rw [hs L.ω₁, hs η₁, hs L.ω₂, hs η₂]
          refine Prod.ext ?_ ?_
          · simp only [Prod.fst_add, Prod.smul_fst, smul_smul, ← add_smul]
            rw [c1, one_smul]
          · simp only [Prod.snd_add, Prod.smul_snd, smul_smul, ← add_smul]
            rw [c2, zero_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ b0) (Submodule.smul_mem _ _ b1)
      · have : ((0 : Fin g → ℂ), (Pi.single k 1 : Fin g → ℂ)) =
            (-L.ω₂ / (η₂ * L.ω₁ - η₁ * L.ω₂)) • ((Pi.single k L.ω₁ : Fin g → ℂ),
              (Pi.single k η₁ : Fin g → ℂ)) +
            (L.ω₁ / (η₂ * L.ω₁ - η₁ * L.ω₂)) • ((Pi.single k L.ω₂ : Fin g → ℂ),
              (Pi.single k η₂ : Fin g → ℂ)) := by
          rw [hs L.ω₁, hs η₁, hs L.ω₂, hs η₂]
          refine Prod.ext ?_ ?_
          · simp only [Prod.fst_add, Prod.smul_fst, smul_smul, ← add_smul]
            rw [c3, zero_smul]
          · simp only [Prod.snd_add, Prod.smul_snd, smul_smul, ← add_smul]
            rw [c4, one_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ b0) (Submodule.smul_mem _ _ b1)
    rintro ⟨u, v⟩ -
    have : ((u, v) : (Fin g → ℂ) × (Fin g → ℂ)) = ∑ k, (u k • ((Pi.single k 1 : Fin g → ℂ),
        (0 : Fin g → ℂ)) + v k • ((0 : Fin g → ℂ), (Pi.single k 1 : Fin g → ℂ))) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sum, Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      · simp only [Prod.snd_sum, Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
        funext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.add_mem _ (Submodule.smul_mem _ _ (he k).1)
      (Submodule.smul_mem _ _ (he k).2)
  -- `S` is spanned by the `2g` vectors `gen p`
  have hSle : S ≤ Submodule.span ℂ (Set.range gen) := by
    rw [hS, perTanId, Submodule.span_le]
    rintro ⟨z, w⟩ ⟨hzt, hzlat, hw⟩
    simp only at hzt hzlat hw
    subst hw
    have hcoef : ∀ k, ∃ pq : ℤ × ℤ, z (c.ι k) = pq.1 * (Ls (c.ι k)).ω₁ + pq.2 * (Ls (c.ι k)).ω₂ :=
      fun k => by
        obtain ⟨p, q, h⟩ := PeriodPair.mem_lattice.mp (hzlat (c.ι k))
        exact ⟨(p, q), h.symm⟩
    choose pq hpq using hcoef
    let co : Fin g × Fin 2 → ℤ := fun p => if p.2 = 0 then (pq p.1).1 else (pq p.1).2
    have hlatlam : ∀ p, LatVec Ls (lam p) := fun p => hNlat p.1 p.2
    -- `N z = Σ co p • lam p`
    have hNz : (N : ℤ) • z = ∑ p, co p • lam p := by
      have h1 : (N : ℤ) • z ∈ t := t.smul_of_tower_mem _ hzt
      have h2 : ∑ p, co p • lam p ∈ t :=
        Submodule.sum_mem _ fun p _ => t.smul_of_tower_mem _ (c.lift_mem _)
      rw [← c.lift_proj h1, ← c.lift_proj h2]
      congr 1
      have hproj : ∀ p, LSG.CM.proj c.ι (lam p) = N • Pi.single p.1 (omg (Ls := Ls) c p.1 p.2) :=
        fun p => c.proj_lift _
      rw [map_sum]
      simp only [map_zsmul, hproj]
      funext k
      rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single k]
      · simp only [Fin.sum_univ_two, co, omg, Pi.smul_apply, LSG.CM.proj,
          LinearMap.funLeft_apply, hpq k, zsmul_eq_mul, nsmul_eq_mul]
        simp
        ring
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    have hNe : (N : ℤ) • etaV Ls z = ∑ p, co p • etaV Ls (lam p) := by
      rw [← etaV_zsmul Ls hzlat, hNz, etaV_sum Ls _ _ fun p _ => latVec_zsmul Ls (hlatlam p) _]
      exact Finset.sum_congr rfl fun p _ => etaV_zsmul Ls (hlatlam p) _
    have hNgen : (N : ℂ) • ((z, etaV Ls z) : (Fin m → ℂ) × (Fin m → ℂ)) =
        ∑ p, ((co p : ℤ) : ℂ) • gen p := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, Prod.fst_sum, gen]
        have := congrArg (fun x => x) hNz
        rw [← Int.cast_smul_eq_zsmul ℂ] at this
        simp only [Int.cast_natCast] at this
        rw [this]
        exact Finset.sum_congr rfl fun p _ => Int.cast_smul_eq_zsmul ℂ _ _ |>.symm
      · simp only [Prod.smul_snd, Prod.snd_sum, gen]
        rw [← Int.cast_smul_eq_zsmul ℂ] at hNe
        simp only [Int.cast_natCast] at hNe
        rw [hNe]
        exact Finset.sum_congr rfl fun p _ => Int.cast_smul_eq_zsmul ℂ _ _ |>.symm
    have : ((z, etaV Ls z) : (Fin m → ℂ) × (Fin m → ℂ)) =
        (N : ℂ)⁻¹ • ∑ p, ((co p : ℤ) : ℂ) • gen p := by
      rw [← hNgen, smul_smul, inv_mul_cancel₀ hNC, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  -- dimensions
  have hfinS : finrank ℂ S ≤ g + g := by
    refine (Submodule.finrank_mono hSle).trans ((finrank_range_le_card gen).trans ?_)
    simp; omega
  have hsurj : Function.Surjective ((perP c).domRestrict S) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_domRestrict]; exact hmapTop
  have hfin2 : finrank ℂ S = g + g := by
    have h1 := LinearMap.finrank_range_le ((perP c).domRestrict S)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod,
      Module.finrank_fin_fun] at h1
    omega
  refine ⟨?_, hsurj⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [hfin2, Module.finrank_prod, Module.finrank_fin_fun])).mpr hsurj

variable (ht : IsAbelianTangent Ls t)

/-- `perTanId t ≃ ℂ^g × ℂ^g`. -/
noncomputable def perEquiv :
    perTanId Ls t ≃ₗ[ℂ] (Fin (finrank ℂ t) → ℂ) × (Fin (finrank ℂ t) → ℂ) :=
  LinearEquiv.ofBijective _ (perTanId_bij c ht)

/-- The inverse `ℂ^g × ℂ^g → perTanId t ⊂ ℂ^m × ℂ^m`. -/
noncomputable def perQ : ((Fin (finrank ℂ t) → ℂ) × (Fin (finrank ℂ t) → ℂ)) →ₗ[ℂ]
    ((Fin m → ℂ) × (Fin m → ℂ)) :=
  (perTanId Ls t).subtype ∘ₗ (perEquiv c ht).symm.toLinearMap

lemma perQ_mem (e) : perQ c ht e ∈ perTanId Ls t := ((perEquiv c ht).symm e).2

lemma perP_perQ (e) : perP c (perQ c ht e) = e :=
  (perEquiv c ht).apply_symm_apply e

lemma perQ_perP {p : (Fin m → ℂ) × (Fin m → ℂ)} (hp : p ∈ perTanId Ls t) :
    perQ c ht (perP c p) = p := by
  have : (perEquiv c ht).symm (perP c p) = ⟨p, hp⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [perQ, this]

/-- `κ_t`: `perK μ` is the fibre coordinate of the lift of `μ` with `J`-part `0`. -/
noncomputable def perK : (Fin (finrank ℂ t) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  (LinearMap.snd ℂ _ _) ∘ₗ (perQ c ht) ∘ₗ (LinearMap.inl ℂ _ _)

/-- The fibre `fib(B^♮) ≅ ℂ^J`. -/
noncomputable def perN : (Fin (finrank ℂ t) → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  (LinearMap.snd ℂ _ _) ∘ₗ (perQ c ht) ∘ₗ (LinearMap.inr ℂ _ _)

lemma perQ_fst (μ x : Fin (finrank ℂ t) → ℂ) : (perQ c ht (μ, x)).1 = c.lift μ := by
  have h1 := fst_mem_of_mem_perTanId Ls (perQ_mem c ht (μ, x))
  have h2 := congrArg Prod.fst (perP_perQ c ht (μ, x))
  rw [perP_apply] at h2
  simp only at h2
  rw [← c.lift_proj h1, h2]

lemma perQ_apply (μ x : Fin (finrank ℂ t) → ℂ) :
    perQ c ht (μ, x) = (c.lift μ, perK c ht μ + perN c ht x) := by
  refine Prod.ext (perQ_fst c ht μ x) ?_
  have : ((μ, x) : (Fin (finrank ℂ t) → ℂ) × (Fin (finrank ℂ t) → ℂ)) = (μ, 0) + (0, x) := by simp
  rw [this, map_add]; rfl

lemma mem_perTanId_lift (μ x : Fin (finrank ℂ t) → ℂ) :
    (c.lift μ, perK c ht μ + perN c ht x) ∈ perTanId Ls t := by
  rw [← perQ_apply]; exact perQ_mem c ht _

lemma proj_perK (μ : Fin (finrank ℂ t) → ℂ) : LSG.CM.proj c.ι (perK c ht μ) = 0 := by
  have := congrArg Prod.snd (perP_perQ c ht (μ, 0)); exact this

lemma proj_perN (x : Fin (finrank ℂ t) → ℂ) : LSG.CM.proj c.ι (perN c ht x) = x := by
  have := congrArg Prod.snd (perP_perQ c ht (0, x)); exact this

lemma perTanId_eq {p : (Fin m → ℂ) × (Fin m → ℂ)} (hp : p ∈ perTanId Ls t) :
    p = (c.lift (LSG.CM.proj c.ι p.1),
      perK c ht (LSG.CM.proj c.ι p.1) + perN c ht (LSG.CM.proj c.ι p.2)) := by
  conv_lhs => rw [← perQ_perP c ht hp]
  rw [perP_apply, perQ_apply]

/-- For a period `λ ∈ t ∩ Λ`: `η(λ) = κ_t(λ_J) + N(η_J(λ_J))`. -/
lemma etaV_eq_of_mem {l : Fin m → ℂ} (hlt : l ∈ t) (hl : LatVec Ls l) :
    etaV Ls l =
      perK c ht (LSG.CM.proj c.ι l) + perN c ht (etaV (Ls ∘ c.ι) (LSG.CM.proj c.ι l)) := by
  have hp : ((l, etaV Ls l) : (Fin m → ℂ) × (Fin m → ℂ)) ∈ perTanId Ls t :=
    Submodule.subset_span ⟨hlt, hl, rfl⟩
  have := congrArg Prod.snd (perTanId_eq c ht hp)
  exact this

/-! ### Algebraicity -/

/-- `(z, w) ↦ (z ∘ ι) ⊔ (w ∘ ι)` on `Fin g ⊕ Fin g`. -/
noncomputable def perPs :
    ((Fin m → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] (Fin (finrank ℂ t) ⊕ Fin (finrank ℂ t) → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm.toLinearMap ∘ₗ perP c

lemma perQ_alg (hrat : RatPair (perTanId Ls t))
    {e : (Fin (finrank ℂ t) → ℂ) × (Fin (finrank ℂ t) → ℂ)}
    (he : AlgPair e) : AlgPair (perQ c ht e) := by
  classical
  have hmem : (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm e ∈
      (perTanId Ls t).map (perPs c) :=
    ⟨perQ c ht e, perQ_mem c ht e, by simp only [perPs, LinearMap.comp_apply, perP_perQ]; rfl⟩
  have hea : ∀ i, IsAlgebraic ℚ ((LinearEquiv.sumArrowLequivProdArrow (Fin (finrank ℂ t))
      (Fin (finrank ℂ t)) ℂ ℂ).symm e i) := by
    rintro (i | i)
    · exact he.1 i
    · exact he.2 i
  have hP : ∀ v, AlgPair v → ∀ i, IsAlgebraic ℚ (perPs c v i) := by
    rintro v hv (i | i)
    · exact hv.1 (c.ι i)
    · exact hv.2 (c.ι i)
  obtain ⟨s, hs, hsalg, hPs⟩ := exists_alg_preimage hrat (perPs c) hP hmem hea
  have hPs' : perP c s = e := by
    have := congrArg (LinearEquiv.sumArrowLequivProdArrow (Fin (finrank ℂ t))
      (Fin (finrank ℂ t)) ℂ ℂ) hPs
    simpa [perPs] using this
  rw [← hPs', perQ_perP c ht hs]; exact hsalg

lemma algLin_perK (hrat : RatPair (perTanId Ls t)) : AlgLin (perK c ht) := fun μ hμ =>
  (perQ_alg c ht hrat (e := (μ, 0)) ⟨hμ, algVec_zero⟩).2

lemma algLin_perN (hrat : RatPair (perTanId Ls t)) : AlgLin (perN c ht) := fun x hx =>
  (perQ_alg c ht hrat (e := (0, x)) ⟨algVec_zero, hx⟩).2

omit ht in
lemma algLin_lift (ht : IsAbelianTangent Ls t) (hrat : RatPair (perTanId Ls t)) :
    AlgLin c.lift := fun μ hμ => by
  have := (perQ_alg c ht hrat (e := (μ, 0)) ⟨hμ, algVec_zero⟩).1
  rwa [perQ_fst] at this

end Chart

end LSG.W88.V5d
