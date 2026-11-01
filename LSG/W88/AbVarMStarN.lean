/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dFinal
import LSG.W88.AbVarMStarK
import LSG.W88.MStarCopyAbVarNOn

/-!
# M2.8: lean_mstar's `Thm11KappaAn`, `Thm11KappaAnK` at `y⁵ = x(1 − x)` from `HyperplaneKappaAbVarV`

The bridge from lean_lsg's W88 §5d for the vector-extension class (`hyperplaneKappaAbVarV_aBlockV`, M2.7, at
`d₀ = 0`, `B = fun _ : Fin r => aBlockV`, `M = bᵀ`) to the TorInj-narrowed hypotheses of Theorem MG♮-A
(`MStarCopy.Thm11KappaAn`, `MStarCopy.Thm11KappaAnK`, M2.md §1.6), by one call of `hkOn_transport` each.

* **`iotaN5 r`**: `TanAV 0 (2|ι|) 1 B ≃ TF ι ((Fin 2 × Fin r → ℂ) × ℂ)`, `ι = Fin r × Fin φ(5)`:
  `(a, t, z, s) ↦ (torA t, (abA z, (5/3) s₀))`. The toric part is M1's reindexing, the `A`-part M1's scaling
  `q (s, j) = 5(−1)^s z_j s` (`perA5_scale`), and the fibre is scaled by `5/3`: lean_mstar's period generator `(j, e)`
  has fibre `b_j ζ^{4e} P̄`, lean_lsg's period `[ζ^e]γ` in copy `j` has fibre `b_j η̄(perVec e) = b_j (3/5) ζ^{4e} P̄`
  (`ThetaData.etaB_perVec_nat'`), so `iotaN5 (pvN5 b j e) = qv (genN5 b j e)` (**`iotaN5_pvN5`**).
* `hsub`: a member `H.tan` maps to `torSub (annQ U) × H.tan.map qN5` (`map_tan_eq`); the `Q″`-part is `0` or contains a
  vector with nonzero fibre coordinate: by `FibOK` when `t ≠ 0` (the fibre `(0,0,0,1) ↦ (0, 5/3)`), and directly when
  `t = 0` (then `T_H` has zero abelian part, `perTanA_bot'`).
* `hgood`: **`torInjAV_of`** — `ι` maps `span_ℚ PerAVf` into lean_mstar's `span_ℚ perGen` (`iotaN5_perAV`, via
  `perAVf_nsmul`), and preserves "toric part = 0".
* **`thm11KappaAn5 : Thm11KappaAn 5 2 (·+1) perA5 perB5`** and **`thm11KappaAnK5 : Thm11KappaAnK 5 2 (·+1) perA5
  perB5 ∅`**, unconditional.
-/

open Complex Module LSG.AuxAV

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.JacAn LSG.JacAn.Beta LSG.JacBlock

/-! ### The data -/

/-- The block family `(A_σ̄^♮)^r`. -/
abbrev BN5 (r : ℕ) : Fin r → LSG.MEBV.VBlock := fun _ => LSG.JacBlockV.aBlockV

/-- Its analytic packages. -/
abbrev AnN5 (r : ℕ) : ∀ k, VBlockAn (BN5 r k) := fun _ => LSG.JacBlockV.aBlockVAn

/-- The push-out `M = bᵀ`. -/
abbrev MN5 {r : ℕ} (b : Fin r → ℂ) : Matrix (Fin 1) (Fin r) ℂ := Matrix.of fun (_ : Fin 1) j => b j

/-- lean_lsg's tangent space at `d₀ = 0`, `d₁ = 2|ι|`. -/
abbrev TanN5 (r : ℕ) : Type := TanAV 0 (d1A r) 1 (BN5 r)

/-- lean_mstar's `Q″`. -/
abbrev QN5 (r : ℕ) : Type := (Fin 2 × Fin r → ℂ) × ℂ

/-- lean_mstar's tangent space. -/
abbrev TFN5 (r : ℕ) : Type := MStarCopy.TF (ιA r) (QN5 r)

/-- `κ = (1, 2)`. -/
abbrev κN5 : Fin 2 → ℕ := fun s => (s : ℕ) + 1

variable {r : ℕ}

/-! ### The isomorphism -/

/-- **The isomorphism** `(a, t, z, s) ↦ (torA t, (abA z, (5/3) s₀))`. -/
def iotaN5 (r : ℕ) : TanN5 r ≃ₗ[ℂ] TFN5 r where
  toFun p := (torA r p.2.1, (abA r p.2.2.1, 5 / 3 * p.2.2.2 0))
  invFun v := (0, fun k => Sum.elim v.1.1 v.1.2 (tEA r k), fun j s => (cA s)⁻¹ * v.2.1 (s, j),
    fun _ => 3 / 5 * v.2.2)
  map_add' p q := by
    refine Prod.ext (map_add _ _ _) (Prod.ext (map_add (abA r) p.2.2.1 q.2.2.1) ?_)
    change 5 / 3 * (p.2.2.2 0 + q.2.2.2 0) = 5 / 3 * p.2.2.2 0 + 5 / 3 * q.2.2.2 0
    ring
  map_smul' c p := by
    refine Prod.ext (map_smul _ _ _) (Prod.ext (map_smul (abA r) c p.2.2.1) ?_)
    change 5 / 3 * (c * p.2.2.2 0) = c * (5 / 3 * p.2.2.2 0)
    ring
  left_inv p := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext k
      change Sum.elim _ _ (tEA r k) = p.2.1 k
      rcases h : tEA r k with i | i
      · change p.2.1 ((tEA r).symm (Sum.inl i)) = p.2.1 k
        rw [← h, Equiv.symm_apply_apply]
      · change p.2.1 ((tEA r).symm (Sum.inr i)) = p.2.1 k
        rw [← h, Equiv.symm_apply_apply]
    · funext j s
      change (cA s)⁻¹ * (cA s * p.2.2.1 j s) = p.2.2.1 j s
      rw [← mul_assoc, inv_mul_cancel₀ (cA_ne_zero s), one_mul]
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change 3 / 5 * (5 / 3 * p.2.2.2 0) = p.2.2.2 0
      ring
  right_inv v := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · funext i; simp [torA]
    · funext i; simp [torA]
    · funext sj
      change cA sj.1 * ((cA sj.1)⁻¹ * v.2.1 (sj.1, sj.2)) = v.2.1 sj
      rw [← mul_assoc, mul_inv_cancel₀ (cA_ne_zero _), one_mul]
    · change 5 / 3 * (3 / 5 * v.2.2) = v.2.2
      ring

lemma iotaN5_apply (p : TanN5 r) : iotaN5 r p = (torA r p.2.1, (abA r p.2.2.1, 5 / 3 * p.2.2.2 0)) := rfl

lemma iotaN5_symm_apply (v : TFN5 r) : (iotaN5 r).symm v =
    (0, fun k => Sum.elim v.1.1 v.1.2 (tEA r k), fun j s => (cA s)⁻¹ * v.2.1 (s, j), fun _ => 3 / 5 * v.2.2) :=
  rfl

/-- The `Q″`-part. -/
def qN5 (r : ℕ) : TanN5 r →ₗ[ℂ] QN5 r := LinearMap.snd ℂ _ _ ∘ₗ (iotaN5 r).toLinearMap

lemma qN5_apply (p : TanN5 r) : qN5 r p = (abA r p.2.2.1, 5 / 3 * p.2.2.2 0) := rfl

lemma iotaN5_torIncl (w : Fin (d1A r) → ℂ) :
    iotaN5 r (torInclA (B := BN5 r) (d₀ := 0) (r := 1) w) = (torA r w, 0) := by
  refine Prod.ext rfl (Prod.ext (map_zero (abA r)) ?_)
  change 5 / 3 * (0 : ℂ) = 0
  ring

/-- `ι⁻¹` of a vector with zero `Q″`-part. -/
lemma symmN5_toric (v : TFN5 r) (hv : v.2 = 0) (P : ℂ → Prop) (h1 : ∀ i, P (v.1.1 i)) (h2 : ∀ i, P (v.1.2 i)) :
    (∀ k, P (((iotaN5 r).symm v).2.1 k)) ∧ ((iotaN5 r).symm v).2.2.1 = 0 ∧ ((iotaN5 r).symm v).2.2.2 = 0 := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · change P (Sum.elim v.1.1 v.1.2 (tEA r k))
    rcases tEA r k with i | i
    · exact h1 i
    · exact h2 i
  · funext j s
    change (cA s)⁻¹ * v.2.1 (s, j) = 0
    rw [hv]; simp
  · funext i
    change 3 / 5 * v.2.2 = 0
    rw [hv]; simp

/-! ### Period generators -/

/-- lean_mstar's period generator `(j, e)` of `Q″`. -/
def genN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : QN5 r :=
  ((fun p => if p.2 = j then MStarCopy.zetaN 5 ^ (κN5 p.1 * e) * MStarCopy.perA5 p.1 else 0),
    b j * MStarCopy.zetaN 5 ^ ((5 - 1) * e) * MStarCopy.perB5)

lemma genN5_mem (b : Fin r → ℂ) (j : Fin r) (e : ℕ) :
    genN5 b j e ∈ MStarCopy.perAngen 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b := ⟨(j, e), rfl⟩

/-- lean_lsg's period `[ζ^e]γ` in copy `j`. -/
def pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : TanN5 r :=
  (0, 0, (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ),
    (MN5 b).mulVec (etaB (BN5 r) (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ)))

/-- **The fibre period**: `η̄(perVec e) = (3/5) ζ^{4e} P̄`. -/
lemma etaN5_perVec (e : ℕ) :
    LSG.JacBlockV.aBlockV.η (perVec e) = 3 / 5 * MStarCopy.zetaN 5 ^ (4 * e) * MStarCopy.perB5 :=
  stdPkg.D.etaB_perVec_nat' surjFacts e

lemma fib_pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) :
    (MN5 b).mulVec (etaB (BN5 r) (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ)) 0 =
      b j * (3 / 5 * MStarCopy.zetaN 5 ^ (4 * e) * MStarCopy.perB5) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, etaB]
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, etaN5_perVec]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    exact mul_eq_zero_of_right _ (BN5 r k).η_zero
  · simp

/-- **`ι([ζ^e]γ in copy j) = (j, e)`-th generator.** -/
theorem iotaN5_pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) :
    iotaN5 r (pvN5 b j e) = MStarCopy.qv (genN5 b j e) := by
  refine Prod.ext (map_zero (torA r)) (Prod.ext ?_ ?_)
  · exact abA_single j e
  · change 5 / 3 * (MN5 b).mulVec (etaB (BN5 r) (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ)) 0 =
      b j * MStarCopy.zetaN 5 ^ ((5 - 1) * e) * MStarCopy.perB5
    rw [fib_pvN5]
    norm_num
    ring

lemma symm_qv_genN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) :
    (iotaN5 r).symm (MStarCopy.qv (genN5 b j e)) = pvN5 b j e :=
  (iotaN5 r).symm_apply_eq.mpr (iotaN5_pvN5 b j e).symm

lemma sPart_pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : sPart (MN5 b) (pvN5 b j e) = 0 := sub_self _

lemma pvN5_mem (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : pvN5 b j e ∈ PerAV 0 (d1A r) (AnN5 r) (MN5 b) :=
  ⟨Subsingleton.elim _ _, fun _ => ⟨0, by simp [pvN5]⟩, single_perVec_mem j e, rfl⟩

lemma pvN5_lam (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : pvN5 b j e ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b) := by
  refine ⟨fun i => i.elim0, fun _ => by simpa [pvN5] using isAlgebraic_one, single_perVec_mem j e, ?_⟩
  rw [sPart_pvN5]; exact fun _ => isAlgebraic_zero

/-- A toric vector of lean_lsg's tangent space. -/
lemma sPart_toric (b : Fin r → ℂ) (p : TanN5 r) (hz : p.2.2.1 = 0) (hs : p.2.2.2 = 0) :
    sPart (MN5 b) p = 0 := by
  have he : etaB (BN5 r) p.2.2.1 = 0 := by
    rw [hz]; funext k; exact (BN5 r k).η_zero
  unfold sPart
  rw [he, hs, Matrix.mulVec_zero, sub_zero]

/-! ### Periods -/

lemma tor_decompN5 (f1 f2 : ιA r → ℂ) :
    (((f1, f2), (0 : QN5 r)) : TFN5 r) = ∑ i, MStarCopy.tor1 i (f1 i) + ∑ i, MStarCopy.tor2 i (f2 i) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i; simp [MStarCopy.tor1, MStarCopy.tor2, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext i; simp [MStarCopy.tor1, MStarCopy.tor2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
      Pi.single_apply]
  · simp [MStarCopy.tor1, MStarCopy.tor2, Prod.snd_sum]

lemma tor1_intN5 (i : ιA r) (n : ℤ) :
    (MStarCopy.tor1 i (2 * Real.pi * I * n) : TFN5 r) = n • MStarCopy.tor1 i (2 * Real.pi * I) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext k; by_cases hk : k = i
    · subst hk; simp [MStarCopy.tor1]; ring
    · simp [MStarCopy.tor1, hk]
  · simp [MStarCopy.tor1]
  · simp [MStarCopy.tor1]

lemma tor2_intN5 (i : ιA r) (n : ℤ) :
    (MStarCopy.tor2 i (2 * Real.pi * I * n) : TFN5 r) = n • MStarCopy.tor2 i (2 * Real.pi * I) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp [MStarCopy.tor2]
  · funext k; by_cases hk : k = i
    · subst hk; simp [MStarCopy.tor2]; ring
    · simp [MStarCopy.tor2, hk]
  · simp [MStarCopy.tor2]

/-- lean_mstar's periods. -/
abbrev perN5 (b : Fin r → ℂ) : Submodule ℚ (TFN5 r) :=
  Submodule.span ℚ (MStarCopy.perGen (ι := ιA r) (MStarCopy.perAngen 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b))

/-- The toric projection. -/
def tPrN5 (r : ℕ) : TanN5 r →ₗ[ℂ] (Fin (d1A r) → ℂ) := LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _

/-- The abelian projection. -/
def zPrN5 (r : ℕ) : TanN5 r →ₗ[ℂ] (∀ k, Fin (BN5 r k).g → ℂ) :=
  LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _

lemma zPrN5_torIncl (w : Fin (d1A r) → ℂ) : zPrN5 r (torInclA (B := BN5 r) (d₀ := 0) (r := 1) w) = 0 := rfl

lemma zPrN5_pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) :
    zPrN5 r (pvN5 b j e) = (Pi.single j (perVec e) : Fin r → Fin 2 → ℂ) := rfl

lemma tPrN5_torIncl (w : Fin (d1A r) → ℂ) : tPrN5 r (torInclA (B := BN5 r) (d₀ := 0) (r := 1) w) = w := rfl

lemma tPrN5_pvN5 (b : Fin r → ℂ) (j : Fin r) (e : ℕ) : tPrN5 r (pvN5 b j e) = 0 := rfl

/-- **`ι` maps the counted periods into lean_mstar's periods.** -/
theorem iotaN5_perAV (b : Fin r → ℂ) {p : TanN5 r} (hp : p ∈ PerAV 0 (d1A r) (AnN5 r) (MN5 b)) :
    iotaN5 r p ∈ perN5 b := by
  obtain ⟨-, hp1, hp2, hp3⟩ := hp
  choose n hn using hp1
  choose m hm using fun j => latt_repr' (hp2 j)
  set q : TanN5 r := torInclA (B := BN5 r) (d₀ := 0) (r := 1) p.2.1 +
    ∑ j, ∑ e : Fin 4, m j e • pvN5 b j e with hq
  have hqmem : q ∈ PerAV 0 (d1A r) (AnN5 r) (MN5 b) := by
    refine AddSubgroup.add_mem _ ⟨rfl, fun i => ⟨n i, hn i⟩, fun k => latt.zero_mem, ?_⟩
      (AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun e _ =>
        AddSubgroup.zsmul_mem _ (pvN5_mem b j (e : ℕ)) _)
    have he : etaB (BN5 r) (0 : ∀ k, Fin (BN5 r k).g → ℂ) = 0 := funext fun k => (BN5 r k).η_zero
    change (0 : Fin 1 → ℂ) = (MN5 b).mulVec (etaB (BN5 r) 0)
    rw [he, Matrix.mulVec_zero]
  have hz : p.2.2.1 = ∑ j, ∑ e : Fin 4, m j e • (Pi.single j (perVec (e : ℕ)) : Fin r → Fin 2 → ℂ) := by
    funext j' s
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single j']
    · rw [hm j']; simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hqz : q.2.2.1 = p.2.2.1 := by
    change zPrN5 r q = p.2.2.1
    rw [hq, map_add, map_sum]
    simp only [map_sum, map_zsmul, zPrN5_torIncl, zPrN5_pvN5, zero_add]
    exact hz.symm
  have hqt : q.2.1 = p.2.1 := by
    change tPrN5 r q = p.2.1
    rw [hq, map_add, map_sum]
    simp only [map_sum, map_zsmul, tPrN5_torIncl, tPrN5_pvN5, smul_zero, Finset.sum_const_zero, add_zero]
  have hpq : p = q := by
    have hs : q.2.2.2 = (MN5 b).mulVec (etaB (BN5 r) q.2.2.1) := hqmem.2.2.2
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext hqt.symm (Prod.ext hqz.symm ?_))
    rw [hs, hqz]; exact hp3
  rw [hpq, hq, map_add, iotaN5_torIncl, map_sum]
  refine add_mem ?_ (Submodule.sum_mem _ fun j _ => ?_)
  · rw [show ((torA r p.2.1, (0 : QN5 r)) : TFN5 r) = (((torA r p.2.1).1, (torA r p.2.1).2), 0) from rfl,
      tor_decompN5]
    refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
    · change MStarCopy.tor1 i (p.2.1 ((tEA r).symm (Sum.inl i))) ∈ _
      rw [hn, tor1_intN5]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    · change MStarCopy.tor2 i (p.2.1 ((tEA r).symm (Sum.inr i))) ∈ _
      rw [hn, tor2_intN5]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
  · rw [map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [map_zsmul, iotaN5_pvN5]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span (Or.inr ⟨_, genN5_mem b j e, rfl⟩))

/-- **`ι` maps the full periods into lean_mstar's periods** (`perAVf_nsmul`). -/
theorem iotaN5_spanPerAVf (b : Fin r → ℂ) {v : TanN5 r}
    (hv : v ∈ Submodule.span ℚ (PerAVf 0 (d1A r) (BN5 r) (MN5 b) : Set (TanN5 r))) : iotaN5 r v ∈ perN5 b := by
  have hle : Submodule.span ℚ (PerAVf 0 (d1A r) (BN5 r) (MN5 b) : Set (TanN5 r)) ≤
      (perN5 b).comap ((iotaN5 r).toLinearMap.restrictScalars ℚ) := by
    rw [Submodule.span_le]
    intro p hp
    obtain ⟨N, hN, hNp⟩ := perAVf_nsmul (AnN5 r) hp
    change iotaN5 r p ∈ perN5 b
    refine mem_span_rat_of_nsmul hN ?_
    rw [← map_nsmul]
    exact iotaN5_perAV b hNp
  exact hle hv

/-- **`hgood`**: lean_mstar's toric injectivity (for the periods `perN5 b`) pulls back to `TorInjAV`. -/
theorem torInjAV_of (b : Fin r → ℂ) (V : Submodule ℂ (TFN5 r))
    (hV : ∀ v ∈ V, v ∈ perN5 b → v.1 = 0 → v = 0) : TorInjAV (MN5 b) (V.comap (iotaN5 r).toLinearMap) := by
  intro v hvV hvper htor
  have h0 := hV (iotaN5 r v) hvV (iotaN5_spanPerAVf b hvper) (by rw [iotaN5_apply, htor, map_zero])
  exact (iotaN5 r).injective (by rw [h0, map_zero])

/-! ### Algebraic vectors, logarithms, periods back in lean_lsg -/

lemma isAlgebraic_three_fifths : IsAlgebraic ℚ ((3 : ℂ) / 5) := by
  have h := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (3 / 5 : ℚ)
  simpa using h

lemma isAlgebraic_five_thirds : IsAlgebraic ℚ ((5 : ℂ) / 3) := by
  have h := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (5 / 3 : ℚ)
  simpa using h

/-- **`halg`.** -/
lemma algN5 (v : TFN5 r) (hv : MStarCopy.algF (MStarCopy.algAn 2) v) : AlgTanAV ((iotaN5 r).symm v) := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  refine ⟨fun i => i.elim0, fun k => ?_, fun j s => ?_, fun _ => ?_⟩
  · change IsAlgebraic ℚ (Sum.elim v.1.1 v.1.2 (tEA r k))
    rcases tEA r k with i | i
    · exact h1 i
    · exact h2 i
  · exact (isAlgebraic_cA_inv s).mul (h3 _)
  · exact isAlgebraic_three_fifths.mul h4

lemma etaB_zeroN5 : etaB (BN5 r) (0 : ∀ k, Fin (BN5 r k).g → ℂ) = 0 := funext fun k => (BN5 r k).η_zero

lemma symm_toric_per (b : Fin r → ℂ) (v : TFN5 r) (hv : v.2 = 0)
    (h1 : ∀ i, ∃ k : ℤ, v.1.1 i = 2 * Real.pi * I * k) (h2 : ∀ i, ∃ k : ℤ, v.1.2 i = 2 * Real.pi * I * k) :
    (iotaN5 r).symm v ∈ PerAV 0 (d1A r) (AnN5 r) (MN5 b) := by
  obtain ⟨hk, hz, hs⟩ := symmN5_toric v hv (fun t => ∃ k : ℤ, t = 2 * Real.pi * I * k) h1 h2
  refine ⟨Subsingleton.elim _ _, hk, fun k => by rw [hz]; exact latt.zero_mem, ?_⟩
  rw [hs, hz, etaB_zeroN5, Matrix.mulVec_zero]

lemma symm_toric_lam (b : Fin r → ℂ) (v : TFN5 r) (hv : v.2 = 0)
    (h1 : ∀ i, IsAlgebraic ℚ (Complex.exp (v.1.1 i))) (h2 : ∀ i, IsAlgebraic ℚ (Complex.exp (v.1.2 i))) :
    (iotaN5 r).symm v ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b) := by
  obtain ⟨hk, hz, hs⟩ := symmN5_toric v hv (fun t => IsAlgebraic ℚ (Complex.exp t)) h1 h2
  refine ⟨fun i => i.elim0, hk, fun k => by rw [hz]; exact latt.zero_mem, ?_⟩
  rw [sPart_toric b _ hz hs]; exact fun _ => isAlgebraic_zero

lemma symm_tor1_lam (b : Fin r → ℂ) (j : ιA r) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x)) :
    (iotaN5 r).symm (MStarCopy.tor1 j x) ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b) :=
  symm_toric_lam b _ rfl
    (fun i => by
      by_cases hi : i = j
      · subst hi; simpa [MStarCopy.tor1] using hx
      · simpa [MStarCopy.tor1, Pi.single_apply, hi] using isAlgebraic_one)
    (fun i => by simpa [MStarCopy.tor1] using isAlgebraic_one)

lemma symm_tor2_lam (b : Fin r → ℂ) (j : ιA r) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x)) :
    (iotaN5 r).symm (MStarCopy.tor2 j x) ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b) :=
  symm_toric_lam b _ rfl
    (fun i => by simpa [MStarCopy.tor2] using isAlgebraic_one)
    (fun i => by
      by_cases hi : i = j
      · subst hi; simpa [MStarCopy.tor2] using hx
      · simpa [MStarCopy.tor2, Pi.single_apply, hi] using isAlgebraic_one)

/-- **`hper`.** -/
theorem perN5_symm (b : Fin r → ℂ) {v : TFN5 r} (hv : v ∈ perN5 b) :
    (iotaN5 r).symm v ∈
      Submodule.span ℚ ((PerAV 0 (d1A r) (AnN5 r) (MN5 b) : AddSubgroup (TanN5 r)) : Set (TanN5 r)) := by
  have key : perN5 b ≤ (Submodule.span ℚ ((PerAV 0 (d1A r) (AnN5 r) (MN5 b) : AddSubgroup (TanN5 r)) :
      Set (TanN5 r))).comap ((iotaN5 r).symm.toLinearMap.restrictScalars ℚ) := by
    rw [Submodule.span_le]
    intro w hw
    refine Submodule.subset_span ?_
    change (iotaN5 r).symm w ∈ PerAV 0 (d1A r) (AnN5 r) (MN5 b)
    rcases hw with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, ⟨⟨j, e⟩, rfl⟩, rfl⟩
    · refine symm_toric_per b _ rfl (fun i => ?_) (fun i => ⟨0, by simp [MStarCopy.tor1]⟩)
      by_cases hi : i = j
      · subst hi; exact ⟨1, by simp [MStarCopy.tor1]⟩
      · exact ⟨0, by simp [MStarCopy.tor1, hi]⟩
    · refine symm_toric_per b _ rfl (fun i => ⟨0, by simp [MStarCopy.tor2]⟩) (fun i => ?_)
      by_cases hi : i = j
      · subst hi; exact ⟨1, by simp [MStarCopy.tor2]⟩
      · exact ⟨0, by simp [MStarCopy.tor2, hi]⟩
    · change (iotaN5 r).symm (MStarCopy.qv (genN5 b j e)) ∈ _
      rw [symm_qv_genN5]
      exact pvN5_mem b j e
  exact key hv

/-- **`hd2`**: `dim Q″ = 2r + 1 = Σ g_k + 1`. -/
lemma d2N5 : finrank ℂ (QN5 r) = ∑ k : Fin r, (BN5 r k).g + 1 := by
  change finrank ℂ ((Fin 2 × Fin r → ℂ) × ℂ) = ∑ _k : Fin r, 2 + 1
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  ring

/-! ### Members of the subgroup family -/

section Sub

variable {b : Fin r → ℂ}

lemma tor_mem_tan (H : SubgroupDataAV 0 (d1A r) (BN5 r) (MN5 b)) {p : TanN5 r} (hp : p ∈ H.tan) :
    p.2.1 ∈ torusLie H.U := by
  have hle : H.tan ≤ (torusLie H.U).comap (tPrN5 r) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.map_le_iff_le_comap]
    · intro x _; exact (torusLie H.U).zero_mem
    · intro u hu; exact hu
    · intro x _; exact (torusLie H.U).zero_mem
  exact hle hp

lemma z_zero_of_bot (H : SubgroupDataAV 0 (d1A r) (BN5 r) (MN5 b)) (ht : H.t = ⊥) {p : TanN5 r}
    (hp : p ∈ H.tan) : p.2.2.1 = 0 := by
  have hle : H.tan ≤ (⊥ : Submodule ℂ (∀ k, Fin (BN5 r k).g → ℂ)).comap (zPrN5 r) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.map_le_iff_le_comap]
    · intro x _; exact (Submodule.mem_bot ℂ).mpr rfl
    · intro u _; exact (Submodule.mem_bot ℂ).mpr rfl
    · rw [ht, perTanA_bot']; exact bot_le
  exact (Submodule.mem_bot ℂ).mp (hle hp)

/-- **The image of a member**: `ι(T_H) = torSub (annQ U) × qN5(T_H)`. -/
lemma map_tan_eq (H : SubgroupDataAV 0 (d1A r) (BN5 r) (MN5 b)) :
    H.tan.map (iotaN5 r).toLinearMap =
      (MStarCopy.torSub ((K11.annQ H.U).map (torAQ r))).prod (H.tan.map (qN5 r)) := by
  rw [← torusA_eq]
  ext ⟨x, q⟩
  constructor
  · rintro ⟨p, hp, hpx⟩
    change (torA r p.2.1, qN5 r p) = (x, q) at hpx
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hpx
    exact ⟨⟨_, tor_mem_tan H hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  · rintro ⟨⟨u, hu, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hti : ∀ w ∈ torusLie H.U, torInclA (B := BN5 r) (d₀ := 0) (r := 1) w ∈ H.tan := fun w hw =>
      Submodule.mem_sup_left (Submodule.mem_sup_right ⟨w, hw, rfl⟩)
    refine ⟨p - torInclA p.2.1 + torInclA u, add_mem (sub_mem hp (hti _ (tor_mem_tan H hp))) (hti u hu), ?_⟩
    change iotaN5 r _ = _
    rw [map_add, map_sub, iotaN5_torIncl, iotaN5_torIncl, iotaN5_apply, Prod.mk_sub_mk, Prod.mk_add_mk,
      sub_self, zero_add, sub_zero, add_zero]
    rfl

/-- **`hsub` for `gmAn`.** -/
theorem subN5 (S : Submodule ℂ (TanN5 r)) (hS : (gmLsgAV 0 (d1A r) (AnN5 r) (MN5 b)).sub S) :
    (MStarCopy.gmAn 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b).sub (S.map (iotaN5 r).toLinearMap) := by
  obtain ⟨H, rfl, hF⟩ := hS
  refine ⟨(K11.annQ H.U).map (torAQ r), H.tan.map (qN5 r), ?_, map_tan_eq H⟩
  by_cases ht : H.t = ⊥
  · by_cases hex : ∃ p ∈ H.tan, p.2.2.2 0 ≠ 0
    · obtain ⟨p, hp, hp0⟩ := hex
      right
      exact ⟨qN5 r p, ⟨p, hp, rfl⟩, by
        change 5 / 3 * p.2.2.2 0 ≠ 0
        exact mul_ne_zero (by norm_num) hp0⟩
    · left
      rw [eq_bot_iff]
      rintro _ ⟨p, hp, rfl⟩
      have hs : p.2.2.2 0 = 0 := by
        by_contra h
        exact hex ⟨p, hp, h⟩
      refine (Submodule.mem_bot ℂ).mpr (Prod.ext ?_ ?_)
      · change abA r p.2.2.1 = 0
        rw [z_zero_of_bot H ht hp]
        exact map_zero (abA r)
      · change 5 / 3 * p.2.2.2 0 = 0
        rw [hs, mul_zero]
  · right
    have hf : ((0, 0, 0, fun _ => 1) : TanN5 r) ∈ H.tan := hF ht ⟨fun _ => 1, rfl⟩
    exact ⟨qN5 r (0, 0, 0, fun _ => 1), ⟨_, hf, rfl⟩, by
      change 5 / 3 * (1 : ℂ) ≠ 0
      norm_num⟩

end Sub

/-! ### The main theorem -/

/-- **lean_mstar's `Thm11KappaAn` for `A^♮`, `A = Jac(y⁵ = x(1 − x))`**, unconditionally: W88 §5d on the
toric-injective hyperplanes of `G_m^{2n} × Q″` (M2.md §1.6), from `hyperplaneKappaAbVarV_aBlockV` at `d₀ = 0`. -/
theorem thm11KappaAn5 :
    MStarCopy.Thm11KappaAn 5 2 (fun s => (s : ℕ) + 1) MStarCopy.perA5 MStarCopy.perB5 := by
  intro r b hb
  set G := MStarCopy.gmAn 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b with hG
  refine hkOn_transport (gmLsgAV 0 (d1A r) (AnN5 r) (MN5 b)) (TorInjAV (MN5 b))
    (hyperplaneKappaAbVarV_aBlockV b hb 0 (d1A r)) G (MStarCopy.TorInj G) (iotaN5 r) (fun v hv => algN5 v hv)
    (LamAV 0 (d1A r) (AnN5 r) (MN5 b)) rfl ?_ (fun v hv => perN5_symm b hv) rfl d2N5
    (fun S hS _ => subN5 S hS) (fun V hV => torInjAV_of b V hV)
  intro y hy
  have key : Submodule.span ℚ (MStarCopy.lamGen (ι := ιA r)
      (MStarCopy.perAngen 5 2 κN5 MStarCopy.perA5 MStarCopy.perB5 b)) ≤
      (Submodule.span ℚ ((LamAV 0 (d1A r) (AnN5 r) (MN5 b) : AddSubgroup (TanN5 r)) : Set (TanN5 r))).comap
        ((iotaN5 r).symm.toLinearMap.restrictScalars ℚ) := by
    rw [Submodule.span_le]
    intro v hv
    refine Submodule.subset_span ?_
    change (iotaN5 r).symm v ∈ LamAV 0 (d1A r) (AnN5 r) (MN5 b)
    rcases hv with (⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨q, ⟨⟨j, e⟩, rfl⟩, rfl⟩
    · exact symm_tor1_lam b j x hx
    · exact symm_tor2_lam b j x hx
    · change (iotaN5 r).symm (MStarCopy.qv (genN5 b j e)) ∈ _
      rw [symm_qv_genN5]
      exact pvN5_lam b j e
  exact key hy

end LSG.W88
