/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dHyp
import LSG.W88.AbVarQbarB
import LSG.JacBlockV.An
import LSG.JacBlockV.EtaPer

/-!
# M2.7 for `B = fun _ => aBlockV`: `RatTangentsV` and `PerTanFib`

`A = Jac(y⁵ = x(1 − x))`, CM by `ℚ(ζ)`, `ζ = ζ₅`; `aBlockV = A_σ̄^♮` (`Inst.lean`).

* **`ratTangentsV_aBlockV`**: rational base tangents are `ℚ̄`-rational (`LSG.W88.ratTangents_aBlock`).
* Infrastructure (also used by `PerTanFib2.lean`): a rational `t` is an abelian tangent (`isAbTan_of_ratSub`), stable
  under `[ζ] = diag(ζ, ζ²)` copywise (`Dz_mem`; `Dz = ζ P₀ + ζ²(1 − P₀)`, `abTan_P₀`); the lattice vectors
  `lv n s = Σ_e n_e perVec(e + s)` (`[ζ] (lv n s) = lv n (s + 1)`, `Dz_lv`) and **`eta_lv`**:
  `η(lv n s) = cη ζ^{4s} Σ_e n_e ζ^{4e}` with `cη = η(perVec 0) ≠ 0` (`ThetaData.etaB_perVec_nat'`).
* **`perTanFib_aBlockV`**: for `b` with `θ(j, e) = ζ^e b_j` `ℚ`-independent and `M = bᵀ`, `PerTanFib B M`. For a nonzero
  lattice point `w ∈ t`, `(w, ηw)`, `([ζ]w, ζ⁴ηw)`, `([ζ]²w, ζ⁸ηw) ∈ perTanId t`, and
  `ζ³·(1st) − (ζ + ζ²)·(2nd) + (3rd) = (0, κ ηw)`, `κ = ζ³ − (ζ + ζ²)ζ⁴ + ζ⁸ = 2ζ³ − 1 − ζ ≠ 0` (the polynomial
  `(X − ζ)(X − ζ²)` at `ζ⁴`). `M(ηw) = cη Σ_j b_j Σ_e n_{je} ζ^{4e} ≠ 0` by the independence of `θ`.
-/

noncomputable section

open Module LSG.JacAn LSG.JacAn.Beta LSG.JacBlock

namespace LSG.JacBlockV


open LSG.MEB (IsRatSub)
open LSG.MEBV (VBlock perBase perTanId)

local notation "ζ" => LSG.JacAn.Beta.zetaN 5

variable {m : ℕ}

/-! ### (1) `RatTangentsV` -/

/-- **Rational base tangents of `aBlockV^m` are `ℚ̄`-rational.** -/
theorem ratTangentsV_aBlockV : LSG.W88.RatTangentsV (fun _ : Fin m => aBlockV) :=
  fun _ ht => LSG.W88.ratTangents_aBlock ht

/-! ### Infrastructure -/

/-- A rational tangent (for `kerE^m`) is an abelian tangent (for `latt^m`). -/
theorem isAbTan_of_ratSub {t : Submodule ℂ (∀ k : Fin m, Fin ((fun _ : Fin m => aBlockV) k).g → ℂ)}
    (ht : IsRatSub (perBase (fun _ : Fin m => aBlockV)) t) : LSG.W88.IsAbelianTangentA (r := m) t := by
  have hΛle : ∀ k, LSG.AuxA.latF (aBlockAnF m) k ≤ ((fun _ : Fin m => aBlock) k).per :=
    fun k => (aBlockAnF m k).lat_le
  have hΛ : ∀ k, LSG.W88.IsNsmulIn (LSG.AuxA.latF (aBlockAnF m) k) ((fun _ : Fin m => aBlock) k).per :=
    fun k => (aBlockAnF m k).lat_nsmul
  exact (LSG.W88.isAbelianTangentA_iff_isRatSub t).mpr ((LSG.MEB.isRatSub_perAb_iff hΛle hΛ t).mpr ht)

/-- `[ζ] = diag(ζ, ζ²)` copywise. -/
abbrev Dz : (Fin m → Fin 2 → ℂ) → Fin m → Fin 2 → ℂ := LSG.W88.Dm ζ (ζ ^ 2)

lemma Dz_eq (z : Fin m → Fin 2 → ℂ) : Dz z = ζ • LSG.W88.P₀ z + ζ ^ 2 • (z - LSG.W88.P₀ z) := by
  funext k j; fin_cases j <;> simp [LSG.W88.Dm, LSG.W88.P₀, Matrix.vecHead, Matrix.vecTail]

/-- **An abelian tangent is `[ζ]`-stable.** -/
lemma Dz_mem {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (ht : LSG.W88.IsAbelianTangentA t)
    {z : Fin m → Fin 2 → ℂ} (hz : z ∈ t) : Dz z ∈ t := by
  rw [Dz_eq]
  exact t.add_mem (t.smul_mem _ (LSG.W88.abTan_P₀ ht hz))
    (t.smul_mem _ (t.sub_mem hz (LSG.W88.abTan_P₀ ht hz)))

/-- `Σ_e n_e • perVec (e + s)`. -/
def lv (n : Fin 4 → ℤ) (s : ℕ) : Fin 2 → ℂ := ∑ e : Fin 4, n e • perVec ((e : ℕ) + s)

lemma lv_mem (n : Fin 4 → ℤ) (s : ℕ) : lv n s ∈ latt :=
  sum_mem fun e _ => zsmul_mem (LSG.W88.perVec_mem_latt _) _

lemma lv_zero (n : Fin 4 → ℤ) : lv n 0 = ∑ e : Fin 4, n e • perVec (e : ℕ) := by simp [lv]

lemma Dz_lv (n : Fin m → Fin 4 → ℤ) (s : ℕ) : Dz (fun k => lv (n k) s) = fun k => lv (n k) (s + 1) := by
  funext k j
  fin_cases j
  · simp only [LSG.W88.Dm, lv, Finset.sum_apply, Pi.smul_apply]
    simp only [perVec_eq, zsmul_eq_mul, Finset.mul_sum]
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Fin.isValue, Fin.val_zero]
    refine Finset.sum_congr rfl fun e _ => by ring
  · simp only [LSG.W88.Dm, lv, Finset.sum_apply, Pi.smul_apply]
    simp only [perVec_eq, zsmul_eq_mul, Finset.mul_sum]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.isValue, Fin.val_one]
    refine Finset.sum_congr rfl fun e _ => by ring

/-- `cη = η(perVec 0)`. -/
def cη : ℂ := stdPkg.D.etaB (perVec 0)

lemma eta_perVec (e : ℕ) : stdPkg.D.etaB (perVec e) = cη * ζ ^ (4 * e) := by
  rw [cη, stdPkg.D.etaB_perVec_nat' surjFacts, stdPkg.D.etaB_perVec_nat' surjFacts]; ring

lemma cη_ne : cη ≠ 0 := by
  have h := stdPkg.D.etaB_perVec_cJ surjFacts 0
  simp only [Fin.val_zero, pow_zero, mul_one] at h
  rw [cη, h]
  exact mul_ne_zero (by norm_num) (cJ_ne_zero (by norm_num))

lemma eta_zero' : stdPkg.D.etaB 0 = 0 := stdPkg.D.etaHom.map_zero

lemma eta_sum {ι : Type*} (s : Finset ι) (f : ι → Fin 2 → ℂ) (hf : ∀ i, f i ∈ latt) :
    stdPkg.D.etaB (∑ i ∈ s, f i) = ∑ i ∈ s, stdPkg.D.etaB (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eta_zero'
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, stdPkg.D.etaB_add (hf a) (sum_mem fun i _ => hf i), ih]

lemma eta_zsmul (n : ℤ) {v : Fin 2 → ℂ} (hv : v ∈ latt) :
    stdPkg.D.etaB (n • v) = n * stdPkg.D.etaB v := by
  have h : stdPkg.D.etaHom (n • (⟨v, hv⟩ : latt)) = n • stdPkg.D.etaHom ⟨v, hv⟩ := map_zsmul _ _ _
  rw [zsmul_eq_mul] at h
  exact h

lemma eta_nsmul (N : ℕ) {v : Fin 2 → ℂ} (hv : v ∈ latt) :
    stdPkg.D.etaB (N • v) = N * stdPkg.D.etaB v := by
  have h : stdPkg.D.etaHom (N • (⟨v, hv⟩ : latt)) = N • stdPkg.D.etaHom ⟨v, hv⟩ := map_nsmul _ _ _
  rw [nsmul_eq_mul] at h
  exact h

/-- **The fibre period of a lattice vector.** -/
lemma eta_lv (n : Fin 4 → ℤ) (s : ℕ) :
    stdPkg.D.etaB (lv n s) = cη * ζ ^ (4 * s) * ∑ e : Fin 4, (n e : ℂ) * ζ ^ (4 * (e : ℕ)) := by
  rw [lv, eta_sum _ _ (fun e => zsmul_mem (LSG.W88.perVec_mem_latt _) _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [eta_zsmul _ (LSG.W88.perVec_mem_latt _), eta_perVec, show 4 * ((e : ℕ) + s) = 4 * e + 4 * s by ring,
    pow_add]
  ring

/-- A nonzero abelian tangent contains a nonzero lattice point. -/
lemma exists_latt_ne {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (ht : LSG.W88.IsAbelianTangentA t) (hne : t ≠ ⊥) :
    ∃ w ∈ t, w ≠ 0 ∧ ∀ k, w k ∈ latt := by
  by_contra hcon
  push_neg at hcon
  apply hne
  have hb : Submodule.span ℝ {z : Fin m → Fin 2 → ℂ | z ∈ t ∧ ∀ j, z j ∈ latt} = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro z ⟨hz, hl⟩
    by_contra h
    obtain ⟨k, hk⟩ := hcon z hz h
    exact hk (hl k)
  rw [eq_bot_iff]
  intro z hz
  have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin m → Fin 2 → ℂ)) := hz
  rw [ht, hb] at hz'
  exact hz'

/-! ### `ζ` relations -/

lemma z5 : ζ ^ 5 = 1 := LSG.W88.zeta_pow_five

lemma zsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have hs := LSG.W88.zeta_prim.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  linear_combination hs

/-- `κ = ζ³ − (ζ + ζ²)ζ⁴ + ζ⁸ ≠ 0`. -/
lemma kappa_ne : ζ ^ 3 - (ζ + ζ ^ 2) * ζ ^ 4 + ζ ^ 8 ≠ 0 := by
  intro h
  have h' : ((-1 : ℚ) : ℂ) + ((-1 : ℚ) : ℂ) * ζ + ((0 : ℚ) : ℂ) * ζ ^ 2 + ((2 : ℚ) : ℂ) * ζ ^ 3 = 0 := by
    push_cast
    linear_combination h + (1 + ζ - ζ ^ 3) * z5
  have := LSG.W88.zeta_indep _ _ _ _ h'
  norm_num at this

/-- The coefficients of `Σ_e a_e ζ^{4e}` in the basis `1, ζ, ζ², ζ³`. -/
def gco (a : Fin 4 → ℤ) : Fin 4 → ℚ
  | 0 => a 0 - a 1
  | 1 => -a 1
  | 2 => a 3 - a 1
  | 3 => a 2 - a 1

lemma gco_0 (a : Fin 4 → ℤ) : gco a 0 = a 0 - a 1 := rfl
lemma gco_1 (a : Fin 4 → ℤ) : gco a 1 = -a 1 := rfl
lemma gco_2 (a : Fin 4 → ℤ) : gco a 2 = a 3 - a 1 := rfl
lemma gco_3 (a : Fin 4 → ℤ) : gco a 3 = a 2 - a 1 := rfl

/-- **`ℚ`-independence of `θ(j, e) = ζ^e b_j` makes `Σ_j b_j σ̄(α_j)` nonzero** (`α_j = Σ_e n_{je} ζ^e ≠ 0`). -/
lemma sum_ne_zero_of_indep {b : Fin m → ℂ}
    (hb : LinearIndependent ℚ (LSG.W88.MStarCopy.thetaD (LSG.W88.MStarCopy.zetaN 5) 4 b))
    (n : Fin m → Fin 4 → ℤ) (hn : n ≠ 0) :
    ∑ k, b k * ∑ e : Fin 4, (n k e : ℂ) * ζ ^ (4 * (e : ℕ)) ≠ 0 := by
  intro h0
  rw [Fintype.linearIndependent_iff] at hb
  set g : Fin m × Fin 4 → ℚ := fun p => gco (n p.1) p.2 with hg_def
  have hg : ∑ p, g p • LSG.W88.MStarCopy.thetaD (LSG.W88.MStarCopy.zetaN 5) 4 b p = 0 := by
    rw [Fintype.sum_prod_type, ← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hz5 : LSG.W88.MStarCopy.zetaN 5 = ζ := rfl
    simp only [Fin.sum_univ_four, hg_def, LSG.W88.MStarCopy.thetaD, Rat.smul_def, hz5]
    simp only [gco_0, gco_1, gco_2, gco_3, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [e3]
    push_cast
    linear_combination (b k) * (-(n k 1 : ℂ) * zsum - (n k 2 : ℂ) * ζ ^ 3 * z5 -
      (n k 3 : ℂ) * ζ ^ 2 * (ζ ^ 5 + 1) * z5)
  have hz : ∀ k e, g (k, e) = 0 := fun k e => hb g hg (k, e)
  apply hn
  funext k e
  have h0 := hz k 0
  have h1 := hz k 1
  have h2 := hz k 2
  have h3 := hz k 3
  simp only [hg_def, gco_0, gco_1, gco_2, gco_3] at h0 h1 h2 h3
  have q1' : (n k 1 : ℚ) = 0 := neg_eq_zero.mp h1
  have q1 : n k 1 = 0 := by exact_mod_cast q1'
  have q0 : n k 0 = 0 := by
    have : (n k 0 : ℚ) = 0 := by linarith
    exact_mod_cast this
  have q3 : n k 3 = 0 := by
    have : (n k 3 : ℚ) = 0 := by linarith
    exact_mod_cast this
  have q2 : n k 2 = 0 := by
    have : (n k 2 : ℚ) = 0 := by linarith
    exact_mod_cast this
  fin_cases e <;> simp [q0, q1, q2, q3]

/-! ### (3) `PerTanFib` -/

/-- A lattice period `(lv n s, η(lv n s))` with base part in `t` lies in `perTanId t`. -/
lemma mem_perTanId_lv {t : Submodule ℂ (∀ k : Fin m, Fin ((fun _ : Fin m => aBlockV) k).g → ℂ)}
    (n : Fin m → Fin 4 → ℤ) (s : ℕ) (h : (fun k => lv (n k) s) ∈ t) :
    ((fun k => lv (n k) s : Fin m → Fin 2 → ℂ),
      fun k => cη * ζ ^ (4 * s) * ∑ e : Fin 4, (n k e : ℂ) * ζ ^ (4 * (e : ℕ))) ∈
      perTanId (fun _ : Fin m => aBlockV) t :=
  Submodule.subset_span ⟨h, fun k => ⟨LSG.W88.latt_le_kerE stdPkg.G (lv_mem _ _), (eta_lv _ _).symm⟩⟩

/-- The combination `ζ³·(w, ηw) − (ζ + ζ²)·([ζ]w, ζ⁴ηw) + ([ζ]²w, ζ⁸ηw) = (0, κ ηw)`. -/
lemma combo (w : Fin m → Fin 2 → ℂ) (a : Fin m → ℂ) :
    (ζ ^ 3 • (w, fun k => cη * ζ ^ (4 * 0) * a k) - (ζ + ζ ^ 2) • (Dz w, fun k => cη * ζ ^ (4 * 1) * a k) +
      (Dz (Dz w), fun k => cη * ζ ^ (4 * 2) * a k) : (Fin m → Fin 2 → ℂ) × (Fin m → ℂ)) =
      (0, fun k => (ζ ^ 3 - (ζ + ζ ^ 2) * ζ ^ 4 + ζ ^ 8) * cη * a k) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst]
    funext k j
    fin_cases j <;> simp [LSG.W88.Dm, Matrix.vecHead, Matrix.vecTail] <;> ring
  · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The fibre property of `aBlockV^m` along `M = bᵀ`** (`θ(j, e) = ζ^e b_j` `ℚ`-independent). -/
theorem perTanFib_aBlockV (b : Fin m → ℂ)
    (hb : LinearIndependent ℚ (LSG.W88.MStarCopy.thetaD (LSG.W88.MStarCopy.zetaN 5) 4 b)) :
    LSG.W88.PerTanFib (fun _ : Fin m => aBlockV) (Matrix.of fun (_ : Fin 1) j => b j) := by
  intro t ht hne x
  have hab := isAbTan_of_ratSub ht
  obtain ⟨w, hwt, hw0, hwl⟩ := exists_latt_ne hab hne
  choose n hn using fun k => LSG.W88.latt_repr' (hwl k)
  have hw : w = fun k => lv (n k) 0 := funext fun k => by rw [lv_zero]; exact hn k
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hw0
    rw [hw]
    funext k
    simp [lv]
  have hw1 : Dz w = fun k => lv (n k) 1 := by rw [hw, Dz_lv]
  have hw2 : Dz (Dz w) = fun k => lv (n k) 2 := by rw [hw1, Dz_lv]
  have ht0 : (fun k => lv (n k) 0) ∈ t := hw ▸ hwt
  have ht1 : (fun k => lv (n k) 1) ∈ t := hw1 ▸ Dz_mem hab hwt
  have ht2 : (fun k => lv (n k) 2) ∈ t := hw2 ▸ Dz_mem hab (Dz_mem hab hwt)
  set a : Fin m → ℂ := fun k => ∑ e : Fin 4, (n k e : ℂ) * ζ ^ (4 * (e : ℕ)) with ha
  set κ : ℂ := ζ ^ 3 - (ζ + ζ ^ 2) * ζ ^ 4 + ζ ^ 8 with hκ
  set T := perTanId (fun _ : Fin m => aBlockV) t
  have hmem : ((0 : Fin m → Fin 2 → ℂ), fun k => κ * cη * a k) ∈ T := by
    have h := T.add_mem (T.sub_mem (T.smul_mem (ζ ^ 3) (mem_perTanId_lv n 0 ht0))
      (T.smul_mem (ζ + ζ ^ 2) (mem_perTanId_lv n 1 ht1))) (mem_perTanId_lv n 2 ht2)
    rw [← hw, ← hw1, ← hw2] at h
    exact Eq.subst (motive := fun p => p ∈ T) (combo w a) h
  set M : Matrix (Fin 1) (Fin m) ℂ := Matrix.of fun (_ : Fin 1) j => b j
  have himg := Submodule.mem_map_of_mem (f := LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M)) hmem
  set S : ℂ := ∑ k, b k * a k with hS
  have hS0 : S ≠ 0 := sum_ne_zero_of_indep hb n hn0
  have hMv : M.mulVec (fun k => κ * cη * a k) 0 = κ * cη * S := by
    simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hκ0 : κ * cη * S ≠ 0 := mul_ne_zero (mul_ne_zero kappa_ne cη_ne) hS0
  have hx : (((0 : Fin m → Fin 2 → ℂ)), x) = (x 0 / (κ * cη * S)) •
      (LinearMap.prodMap LinearMap.id (Matrix.mulVecLin M)) ((0 : Fin m → Fin 2 → ℂ), fun k => κ * cη * a k) := by
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      obtain rfl := Subsingleton.elim i 0
      simp only [LinearMap.prodMap_apply, Matrix.mulVecLin_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [hMv]
      have hk1 : κ ≠ 0 := kappa_ne
      have hc1 : cη ≠ 0 := cη_ne
      field_simp
  unfold LSG.W88.perTanA
  convert Submodule.smul_mem _ (x 0 / (κ * cη * S)) himg using 1
  exact hx

/-- The same from lean_mstar's adapted-basis hypothesis. -/
theorem perTanFib_aBlockV_of_adapted (b : Fin m → ℂ)
    (hb : LSG.W88.MStarCopy.IsAdaptedBasisD (LSG.W88.MStarCopy.zetaN 5) (Nat.totient 5) b) :
    LSG.W88.PerTanFib (fun _ : Fin m => aBlockV) (Matrix.of fun (_ : Fin 1) j => b j) := by
  have h5 : Nat.totient 5 = 4 := by decide
  rw [h5] at hb
  exact perTanFib_aBlockV b hb.indep

end LSG.JacBlockV
