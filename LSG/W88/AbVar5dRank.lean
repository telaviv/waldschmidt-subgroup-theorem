/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarSec7Defs
import LSG.W88.K5dModel

/-!
# A5.9a: period ranks for the §5d engine on `G_a^{d₀} × G_m^{d₁} × ∏ B_k` (`STAGE_A5.md` §6.5)

`Ω = span_ℚ Per` (`Per = 0 × 2πiℤ^{d₁} × ∏ per_k`, the full period group; it equals `span_ℚ PerL` by `span_perL`).

* **`finrank_span_Per_le`** (W88's `rk Ω(G) ≤ d₁ + 2G`): a discrete subgroup of `ℂ^g` spanning over `ℝ` lies in the
  `ℚ`-span of `2g` vectors (`exists_span_rat_of_discrete`, through `isNsmulIn_closure_basis`).
* **`finrank_Per_inf_tan_ge`** (W88's `rk (Ω ∩ T_H) ≥ d₁′ + 2d₂′`): the torus part from `annQ U`, the abelian part
  from `IsRatSub (perAb B) t`.
* **`kappa_le_of_torInj`**: under `TorInjB V`, a finite-dimensional `S ⊆ V ∩ Ω` whose toric parts lie in
  `torusLie U` has `dim_ℚ S ≤ dim_ℂ torusLie U` (REVIEW_TORINJ §3d). This replaces the elliptic `corner_false`.
* `finrank_tanB`, `topSubB` (the whole group as `SubgroupDataB`).
-/

open Complex Module Submodule LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.MEB (AbBlock perAb IsRatSub tanOf)

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Upper bound -/

/-- **A discrete subgroup of `ℂ^g` spanning over `ℝ` lies in the `ℚ`-span of `2g` vectors.** -/
theorem exists_span_rat_of_discrete {g : ℕ} (P : AddSubgroup (Fin g → ℂ)) [DiscreteTopology P]
    (hP : span ℝ (P : Set (Fin g → ℂ)) = ⊤) :
    ∃ v : Fin (2 * g) → (Fin g → ℂ), (P : Set (Fin g → ℂ)) ⊆ span ℚ (Set.range v) := by
  classical
  obtain ⟨s, hsP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set (Fin g → ℂ))
  have : Finite s := hli.finite
  have := Fintype.ofFinite s
  let b : Basis s ℝ (Fin g → ℂ) := Basis.mk hli (by rw [Subtype.range_coe, hspan, hP])
  have hb : ∀ i, b i ∈ P := fun i => by rw [Basis.mk_apply]; exact hsP i.2
  have hN := isNsmulIn_closure_basis b P hb
  have hcard : Fintype.card s = 2 * g := by
    rw [← finrank_eq_card_basis b]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  let e : Fin (2 * g) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => b (e i), fun ω hω => ?_⟩
  obtain ⟨N, hN0, hNω⟩ := hN ω hω
  refine mem_span_rat_of_nsmul hN0 ?_
  have hcl : AddSubgroup.closure (Set.range b) ≤
      (span ℚ (Set.range fun i => b (e i))).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact subset_span ⟨e.symm i, by simp⟩
  exact hcl hNω

lemma span_real_per (b : AbBlock) : span ℝ (b.per : Set (Fin b.g → ℂ)) = ⊤ := b.per_span

/-- **`rk (∏ per_k) ≤ 2G`.** -/
theorem finrank_span_perAb_le :
    FiniteDimensional ℚ (span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))) ∧
      finrank ℚ (span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))) ≤ 2 * ∑ k, (B k).g := by
  classical
  choose v hv using fun k => by
    have := (B k).per_discrete
    exact exists_span_rat_of_discrete (B k).per (B k).per_span
  let w : (Σ k, Fin (2 * (B k).g)) → (∀ k, Fin (B k).g → ℂ) := fun σ => Pi.single σ.1 (v σ.1 σ.2)
  have hle : span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) ≤ span ℚ (Set.range w) := by
    rw [span_le]
    intro z hz
    have hz' : z = ∑ k, Pi.single k (z k) := (Finset.univ_sum_single z).symm
    rw [hz']
    refine sum_mem fun k _ => ?_
    have hzk : z k ∈ span ℚ (Set.range (v k)) := hv k (hz k (Set.mem_univ k))
    have hmap : (span ℚ (Set.range (v k))).map (LinearMap.single ℚ (fun k => Fin (B k).g → ℂ) k) ≤
        span ℚ (Set.range w) := by
      rw [map_span, span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact subset_span ⟨⟨k, j⟩, rfl⟩
    exact hmap ⟨z k, hzk, rfl⟩
  have hfd : FiniteDimensional ℚ (span ℚ (Set.range w)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  refine ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans
    ((finrank_range_le_card _).trans ?_)⟩
  simp [Finset.mul_sum]

/-- The toric inclusion `q ↦ (0, 2πi q, 0)`. -/
def inTB (d₀ d₁ : ℕ) (B : Fin m → AbBlock) : (Fin d₁ → ℚ) →ₗ[ℚ] MEB.Tan d₀ d₁ B where
  toFun q := (0, (2 * Real.pi * I : ℂ) • K11.castL d₁ q, 0)
  map_add' a b := by
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    simp [smul_add]
  map_smul' r a := by
    refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
    simp only [map_smul, RingHom.id_apply, Prod.smul_snd, Prod.smul_fst]
    rw [smul_comm]

lemma inTB_apply (q : Fin d₁ → ℚ) :
    inTB d₀ d₁ B q = (0, (2 * Real.pi * I : ℂ) • K11.castL d₁ q, 0) := rfl

lemma inTB_injective : Function.Injective (inTB d₀ d₁ B) := fun a b h => by
  have h2 := congrArg (fun p : MEB.Tan d₀ d₁ B => p.2.1) h
  simp only [inTB_apply] at h2
  have h3 := smul_right_injective _ K11.two_pi_I_ne_zero h2
  funext j
  have := congrFun h3 j
  simpa [K11.castL] using this

lemma inTB_mem_span_Per (q : Fin d₁ → ℚ) :
    inTB d₀ d₁ B q ∈ span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) := by
  classical
  rw [show q = ∑ i, q i • (Pi.single i 1 : Fin d₁ → ℚ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply], map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul]
  refine smul_mem _ _ (subset_span ⟨rfl, fun j => ?_, fun k => (B k).per.zero_mem⟩)
  by_cases h : j = i
  · subst h; exact ⟨1, by simp [inTB_apply, K11.castL]⟩
  · exact ⟨0, by simp [inTB_apply, K11.castL, Pi.single_apply, h]⟩

/-- The abelian inclusion `z ↦ (0, 0, z)`. -/
def inAb (d₀ d₁ : ℕ) (B : Fin m → AbBlock) : (∀ k, Fin (B k).g → ℂ) →ₗ[ℚ] MEB.Tan d₀ d₁ B :=
  (LinearMap.inr ℚ _ _).comp (LinearMap.inr ℚ _ _)

lemma inAb_apply (z : ∀ k, Fin (B k).g → ℂ) : inAb d₀ d₁ B z = (0, 0, z) := rfl

lemma inAb_injective : Function.Injective (inAb d₀ d₁ B) := fun a b h => by
  have := congrArg (fun p : MEB.Tan d₀ d₁ B => p.2.2) h
  simpa [inAb_apply] using this

/-- **`rk Ω(G) ≤ d₁ + 2G`.** -/
theorem finrank_span_Per_le :
    FiniteDimensional ℚ (span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B))) ∧
      finrank ℚ (span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B))) ≤ d₁ + 2 * ∑ k, (B k).g := by
  classical
  obtain ⟨hfdA, hA⟩ := finrank_span_perAb_le (B := B)
  set T := LinearMap.range (inTB d₀ d₁ B) with hT
  set A := (span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))).map (inAb d₀ d₁ B) with hAdef
  have hle : span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) ≤ T ⊔ A := by
    rw [span_le]
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    choose n hn using hp2
    have e : p = inTB d₀ d₁ B (fun i => (n i : ℚ)) + inAb d₀ d₁ B p.2.2 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [inTB_apply, inAb_apply, hp1]
      · funext j
        simp [inTB_apply, inAb_apply, K11.castL, hn j]
      · simp [inTB_apply, inAb_apply]
    rw [e]
    exact add_mem (mem_sup_left ⟨_, rfl⟩)
      (mem_sup_right ⟨p.2.2, subset_span fun k _ => hp3 k, rfl⟩)
  have hfT' : finrank ℚ T ≤ d₁ := (LinearMap.finrank_range_le _).trans (by simp)
  have hfA' : finrank ℚ A ≤ finrank ℚ (span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))) :=
    Submodule.finrank_map_le _ _
  have : FiniteDimensional ℚ A := Module.Finite.map _ _
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq T A
  refine ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans ?_⟩
  omega

instance (d₀ d₁ : ℕ) (B : Fin m → AbBlock) :
    FiniteDimensional ℚ (span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B))) :=
  (finrank_span_Per_le (d₀ := d₀) (d₁ := d₁) (B := B)).1

/-! ### Lower bound -/

lemma finrank_tanOf (h0 : Submodule ℂ (Fin d₀ → ℂ)) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    finrank ℂ (tanOf h0 U t) = finrank ℂ h0 + finrank ℂ (torusLie U) + finrank ℂ t := by
  rw [tanOf, K5d.finrank_prodSub, K5d.finrank_prodSub, add_assoc]

lemma finrank_tanB (H : SubgroupDataB d₀ d₁ B) :
    finrank ℂ H.tan = finrank ℂ H.h0 + finrank ℂ (torusLie H.U) + finrank ℂ H.t :=
  finrank_tanOf _ _ _

/-- The lattice points of `t`, `ℚ`-spanned. -/
def latTB (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : Submodule ℚ (∀ k, Fin (B k).g → ℂ) :=
  span ℚ {z | z ∈ t ∧ z ∈ perAb B}

lemma latTB_le_span (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) :
    latTB t ≤ span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ)) := span_mono fun _ hz => hz.2

lemma latTB_le (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) : latTB t ≤ t.restrictScalars ℚ :=
  span_le.mpr fun _ hz => hz.1

lemma two_mul_le_finrank_latTB {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)} (ht : IsRatSub (perAb B) t) :
    2 * finrank ℂ t ≤ finrank ℚ (latTB t) := by
  classical
  have := (finrank_span_perAb_le (B := B)).1
  have : FiniteDimensional ℚ (latTB t) := Submodule.finiteDimensional_of_le (latTB_le_span t)
  let b := Module.finBasis ℚ (latTB t)
  have hspan : span ℝ {z | z ∈ t ∧ z ∈ perAb B} ≤
      span ℝ (Set.range fun i => (b i : ∀ k, Fin (B k).g → ℂ)) := by
    rw [span_le]
    intro z hz
    have hz' : z ∈ latTB t := subset_span hz
    have h1 : z ∈ span ℚ (Set.range fun i => (b i : ∀ k, Fin (B k).g → ℂ)) := by
      have := congrArg Subtype.val (b.sum_repr ⟨z, hz'⟩)
      rw [Submodule.coe_sum] at this
      change _ = z at this
      rw [← this]
      exact sum_mem fun i _ => by
        rw [Submodule.coe_smul]; exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
    exact span_le_restrictScalars ℚ ℝ _ h1
  have hr : finrank ℝ (t.restrictScalars ℝ) = 2 * finrank ℂ t := finrank_real_of_complex ↥t
  rw [← hr, ht]
  refine (Submodule.finrank_mono hspan).trans ((finrank_range_le_card _).trans ?_)
  simp

/-- **`rk (Ω ∩ T_H) ≥ d₁′ + 2d₂′`.** -/
theorem finrank_Per_inf_tan_ge (h0 : Submodule ℂ (Fin d₀ → ℂ)) (U : Submodule ℚ (Fin d₁ → ℚ))
    (t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) (ht : IsRatSub (perAb B) t) :
    finrank ℂ (torusLie U) + 2 * finrank ℂ t ≤
      finrank ℚ ↥(span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) ⊓ (tanOf h0 U t).restrictScalars ℚ) := by
  classical
  set A := (K11.annQ U).map (inTB d₀ d₁ B) with hA
  set Bb := (latTB t).map (inAb d₀ d₁ B) with hBb
  have hAle : A ≤ span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) ⊓ (tanOf h0 U t).restrictScalars ℚ := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨inTB_mem_span_Per q, ?_⟩
    change inTB d₀ d₁ B q ∈ tanOf h0 U t
    rw [inTB_apply, tanOf, mem_prod, mem_prod]
    exact ⟨h0.zero_mem, K5d.castL_mem_torusLie_iff.mpr hq, t.zero_mem⟩
  have hBle : Bb ≤ span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) ⊓ (tanOf h0 U t).restrictScalars ℚ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · have hz2 := latTB_le_span t hz
      have hmap : (span ℚ (perAb B : Set (∀ k, Fin (B k).g → ℂ))).map (inAb d₀ d₁ B) ≤
          span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) := by
        rw [map_span, span_le]
        rintro _ ⟨y, hy, rfl⟩
        exact subset_span ⟨rfl, fun j => ⟨0, by simp [inAb_apply]⟩, fun k => hy k (Set.mem_univ k)⟩
      exact hmap ⟨z, hz2, rfl⟩
    · change inAb d₀ d₁ B z ∈ tanOf h0 U t
      rw [inAb_apply, tanOf, mem_prod, mem_prod]
      exact ⟨h0.zero_mem, (torusLie U).zero_mem, latTB_le t hz⟩
  have hAB : A ⊓ Bb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨q, -, rfl⟩, ⟨z, -, hz⟩⟩
    have h2 : (inAb d₀ d₁ B z).2.1 = (inTB d₀ d₁ B q).2.1 := congrArg (fun p => p.2.1) hz
    have h2' : (2 * Real.pi * I : ℂ) • K11.castL d₁ q = 0 := by
      simpa [inTB_apply, inAb_apply] using h2.symm
    rw [mem_bot, inTB_apply, h2']; rfl
  have := (finrank_span_perAb_le (B := B)).1
  have : FiniteDimensional ℚ (latTB t) := Submodule.finiteDimensional_of_le (latTB_le_span t)
  have hfA : finrank ℚ A = finrank ℂ (torusLie U) := by
    rw [hA, K5d.finrank_map_inj inTB_injective]
    have h1 := K11.finrank_annQ U
    have h2 := K5d.finrank_torusLie U
    omega
  have hfB : 2 * finrank ℂ t ≤ finrank ℚ Bb := by
    rw [hBb, K5d.finrank_map_inj inAb_injective]; exact two_mul_le_finrank_latTB ht
  have e := Submodule.finrank_sup_add_finrank_inf_eq A Bb
  rw [hAB, finrank_bot] at e
  have : FiniteDimensional ℚ ↥(span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)) ⊓
      (tanOf h0 U t).restrictScalars ℚ) := Submodule.finiteDimensional_of_le inf_le_left
  have hle := Submodule.finrank_mono (sup_le hAle hBle)
  omega

/-! ### Toric injectivity bounds `κ` -/

lemma exists_toric_rat {v : MEB.Tan d₀ d₁ B} (hv : v ∈ span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B))) :
    ∃ q : Fin d₁ → ℚ, v.2.1 = (2 * Real.pi * I : ℂ) • K11.castL d₁ q := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    choose n hn using hx.2.1
    refine ⟨fun i => (n i : ℚ), funext fun i => ?_⟩
    simp [hn i, K11.castL]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Prod.snd_add, Prod.fst_add, ha, hb, map_add, smul_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r • a, ?_⟩
    rw [Prod.smul_snd, Prod.smul_fst, ha, map_smul, smul_comm]

/-- **Toric injectivity bounds the period rank by the toric dimension** (REVIEW_TORINJ §3d). -/
theorem kappa_le_of_torInj {V : Submodule ℂ (MEB.Tan d₀ d₁ B)} (hV : TorInjB V)
    (U : Submodule ℚ (Fin d₁ → ℚ)) (S : Submodule ℚ (MEB.Tan d₀ d₁ B)) [FiniteDimensional ℚ S]
    (hSV : ∀ v ∈ S, v ∈ V) (hSP : S ≤ span ℚ (MEB.Per d₀ d₁ B : Set (MEB.Tan d₀ d₁ B)))
    (hST : ∀ v ∈ S, v.2.1 ∈ torusLie U) : finrank ℚ S ≤ finrank ℂ (torusLie U) := by
  classical
  let b := Module.finBasis ℚ S
  set k := finrank ℚ S
  choose q hq using fun i => exists_toric_rat (hSP (b i).2)
  have hqli : LinearIndependent ℚ q := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set v : MEB.Tan d₀ d₁ B := ∑ i, c i • (b i : MEB.Tan d₀ d₁ B)
    have hvS : v ∈ S := sum_mem fun i _ => smul_mem _ _ (b i).2
    have hv1 : v.2.1 = 0 := by
      have e : v.2.1 = ∑ i, c i • (b i : MEB.Tan d₀ d₁ B).2.1 := by
        simp only [v, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst]
      rw [e]
      simp only [hq, smul_comm (c _) (2 * Real.pi * I : ℂ), ← Finset.smul_sum, ← map_smul, ← map_sum, hc,
        map_zero, smul_zero]
    have hv0 := hV v (hSV v hvS) (hSP hvS) hv1
    have : (∑ i, c i • b i : S) = 0 := Subtype.ext (by simpa [v] using hv0)
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c this
  have hcC := K5d.linIndep_cast (F := ℂ) q hqli
  let f : Fin k → torusLie U := fun i => ⟨(b i : MEB.Tan d₀ d₁ B).2.1, hST _ (b i).2⟩
  have hf : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    refine Fintype.linearIndependent_iff.mp hcC a ?_
    have h1 : ∑ i, a i • (b i : MEB.Tan d₀ d₁ B).2.1 = 0 := by
      have := congrArg Subtype.val ha
      simpa [f] using this
    simp only [hq, K11.castL] at h1
    funext j
    have h2 := congrFun h1 j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply] at h2
    have h3 : (2 * Real.pi * I : ℂ) * ∑ i, a i * ((q i j : ℚ) : ℂ) = 0 := by
      rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have := (mul_eq_zero.mp h3).resolve_left K11.two_pi_I_ne_zero
    simpa [Finset.sum_apply, smul_eq_mul] using this
  simpa using hf.fintype_card_le_finrank

/-! ### The whole group -/

lemma isRatSub_top : IsRatSub (perAb B) (⊤ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) := by
  unfold IsRatSub
  rw [restrictScalars_top, eq_comm, eq_top_iff]
  intro z _
  have hz : z = ∑ k, Pi.single k (z k) := (Finset.univ_sum_single z).symm
  rw [hz]
  refine sum_mem fun k _ => ?_
  have hzk : z k ∈ span ℝ ((B k).per : Set (Fin (B k).g → ℂ)) := by rw [(B k).per_span]; trivial
  have hmap : (span ℝ ((B k).per : Set (Fin (B k).g → ℂ))).map
      (LinearMap.single ℝ (fun k => Fin (B k).g → ℂ) k) ≤
      span ℝ {z | z ∈ (⊤ : Submodule ℂ (∀ k, Fin (B k).g → ℂ)) ∧ z ∈ perAb B} := by
    rw [map_span, span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine subset_span ⟨trivial, fun k' _ => ?_⟩
    by_cases h : k' = k
    · subst h; simpa using hy
    · simp [Pi.single_apply, h, (B k').per.zero_mem]
  exact hmap ⟨z k, hzk, rfl⟩

lemma rationalOverQbar_top {n : ℕ} : RationalOverQbar (⊤ : Submodule ℂ (Fin n → ℂ)) := by
  apply le_antisymm _ le_top
  intro v _
  have : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℂ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine sum_mem fun i _ => smul_mem _ _ (subset_span ⟨mem_top, fun j => ?_⟩)
  by_cases h : j = i
  · subst h; simpa using isAlgebraic_one
  · simpa [h] using isAlgebraic_zero

variable (d₀ d₁ B) in
/-- The whole group as a `SubgroupDataB`. -/
def topSubB : SubgroupDataB d₀ d₁ B where
  h0 := ⊤
  U := ⊥
  t := ⊤
  h0_rat := rationalOverQbar_top
  t_rat := isRatSub_top

lemma topSubB_tan : (topSubB d₀ d₁ B).tan = ⊤ := by
  have h : torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ)) = ⊤ := by
    rw [eq_top_iff]; intro v _ φ hφ
    rw [mem_bot] at hφ; subst hφ; simp
  simp only [topSubB, SubgroupDataB.tan, tanOf, h, prod_top]

end LSG.W88
