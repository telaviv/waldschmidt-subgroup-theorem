import Mathlib
import LSG.MEV.AVO

/-!
# Homogenised chart derivations of `G̃` in arbitrary charts; the chart change

The chain layer (`LSG.MEV.DerivV`) uses the chart derivations `Dv ch w` (charts `ch : Fin m → Fin 2`,
`0 = V`, `1 = W`), which raise the `E^♮` block degrees by `2` on block variables and do not raise
them on the linear variables. For the Wüstholz layer we homogenise them with the **squared** chart
forms `L_k = X_{e k (bi (ch k))}`:

  `Dhc ch w = (∏ₖ L_k²) · D_lin + Σₖ (∏_{k' ≠ k} L_{k'}²) · δ_k`

(`D_lin` the linear part, `δ_k` the block-`k` part of `Dv ch w`).

* `Dhc_add`, `Dhc_smul`: linear in `w`.
* **`isHomV_Dhc`**: `Dhc` raises every `E^♮` degree by exactly `2` (`IsHomV`).
* **`Dhc_IG`**: `Dhc` maps `I_G̃` into itself (the chart derivations are exactly tangent to `F`
  and `G`: `dvalB_F`, `dvalB_G`).
* **`cc_blk`** (block chart change, any commutative ring): with `ψ_{VW} = s V W (g₂W² − 12U²)`,
  `L_b² dvalB_a − L_a² dvalB_b − ψ_{ab} · P ∈ (F(P), G(P))` (explicit cofactors).
* **`chgV`** (chart change identity): for `x` homogeneous of degree `d`,
  `Lcv ch₀ · Dhc ch w x − Lcv ch · Dhc ch₀ w x − Σₖ aeV ch₀ ch w k · (d k • x) ∈ I_G̃`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk c2)
open StrongSix.M2 (DL DL_cons)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Chart forms and the derivation -/

/-- The product of the squared chart forms. -/
noncomputable def Lcv (d₀ d₁ : ℕ) (ch : Fin m → Fin 2) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  ∏ k, X (.e k (bi (ch k))) ^ 2

/-- The product of the squared chart forms other than the `k`-th. -/
noncomputable def Lov (d₀ d₁ : ℕ) (ch : Fin m → Fin 2) (k : Fin m) :
    MvPolynomial (Var d₀ d₁ m) ℂ :=
  ∏ k' ∈ Finset.univ.erase k, X (.e k' (bi (ch k'))) ^ 2

theorem Lcv_eq (ch : Fin m → Fin 2) (k : Fin m) :
    Lcv d₀ d₁ ch = X (.e k (bi (ch k))) ^ 2 * Lov d₀ d₁ ch k :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm

/-- The homogenising factor of a variable: `Lov k` on block `k`, `Lcv` on linear variables. -/
noncomputable def facV (ch : Fin m → Fin 2) : Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .e k _ => Lov d₀ d₁ ch k
  | _ => Lcv d₀ d₁ ch

variable (Ls) in
/-- The values of `Dhc` on the variables. -/
noncomputable def dvh (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    MvPolynomial (Var d₀ d₁ m) ℂ :=
  facV ch v * dvV Ls ch w v

variable (Ls) in
/-- **The homogenised chart derivation** of direction `w` in the charts `ch`. -/
noncomputable def Dhc (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) :
    Derivation ℂ (MvPolynomial (Var d₀ d₁ m) ℂ) (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  mkDerivation ℂ (dvh Ls ch w)

@[simp] theorem Dhc_X (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    Dhc Ls ch w (X v) = dvh Ls ch w v := mkDerivation_X _ _ _

@[simp] theorem Dhc_C (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (a : ℂ) :
    Dhc Ls ch w (C a) = 0 := by
  rw [← algebraMap_eq]; exact Derivation.map_algebraMap _ _

theorem Dhc_eq_sum (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    Dhc Ls ch w P = ∑ v, dvh Ls ch w v * pderiv v P := LSG.ME.mkDerivation_eq_sum _ _

theorem Dv_eq_sum (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    Dv Ls ch w P = ∑ v, dvV Ls ch w v * pderiv v P := LSG.ME.mkDerivation_eq_sum _ _

theorem dvV_add (ch : Fin m → Fin 2) (w w' : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    dvV Ls ch (w + w') v = dvV Ls ch w v + dvV Ls ch w' v := by
  rw [← Dv_X, ← Dv_X, ← Dv_X, Dv_add, Derivation.add_apply]

theorem dvV_smul (ch : Fin m → Fin 2) (a : ℂ) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    dvV Ls ch (a • w) v = C a * dvV Ls ch w v := by
  rw [← Dv_X, ← Dv_X, Dv_smul, Derivation.smul_apply, smul_eq_C_mul]

theorem Dhc_add (ch : Fin m → Fin 2) (w w' : LieV ℂ d₀ d₁ m) :
    Dhc Ls ch (w + w') = Dhc Ls ch w + Dhc Ls ch w' :=
  MvPolynomial.derivation_ext fun v => by
    simp only [Derivation.add_apply, Dhc_X, dvh, dvV_add, mul_add]

theorem Dhc_smul (ch : Fin m → Fin 2) (a : ℂ) (w : LieV ℂ d₀ d₁ m) :
    Dhc Ls ch (a • w) = a • Dhc Ls ch w :=
  MvPolynomial.derivation_ext fun v => by
    simp only [Derivation.smul_apply, Dhc_X, dvh, dvV_smul, smul_eq_C_mul]; ring

theorem Dhc_add_apply (ch : Fin m → Fin 2) (w w' : LieV ℂ d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    Dhc Ls ch (w + w') P = Dhc Ls ch w P + Dhc Ls ch w' P := by
  rw [Dhc_add, Derivation.add_apply]

theorem Dhc_smul_apply (ch : Fin m → Fin 2) (a : ℂ) (w : LieV ℂ d₀ d₁ m)
    (P : MvPolynomial (Var d₀ d₁ m) ℂ) : Dhc Ls ch (a • w) P = a • Dhc Ls ch w P := by
  rw [Dhc_smul, Derivation.smul_apply]

/-! ### Homogeneity -/

theorem dvalB_smul_P {T : Type*} [CommRing T] (a : Fin 2) (g₂ g₃ s β u : T) (P : Fin 5 → T)
    (l : Fin 5) : dvalB a g₂ g₃ s β (u • P) l = u ^ 3 * dvalB a g₂ g₃ s β P l := by
  fin_cases a <;> fin_cases l <;> simp [dvalB, c2, rhoh, Pe] <;> ring

theorem wb_e (k k' : Fin m) (c : Fin 5) :
    wb blk (Blk.e k) (.e k' c : Var d₀ d₁ m) = if k' = k then 1 else 0 := by
  simp [wb]

theorem scw_dvV_e (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k k' : Fin m) (l : Fin 5) :
    scw (wb blk (Blk.e k)) (dvV Ls ch w (.e k' l)) =
      C ((2 : ℂ) ^ (3 * wb blk (Blk.e k) (.e k' l : Var d₀ d₁ m))) * dvV Ls ch w (.e k' l) := by
  simp only [dvV]
  rw [← AlgHom.coe_toRingHom, dvalB_map]
  simp only [AlgHom.coe_toRingHom, scw_C]
  have hb : ((scw (wb blk (Blk.e k)) : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] _) ∘ bvars d₀ d₁ k') =
      (C ((2 : ℂ) ^ wb blk (Blk.e k) (.e k' l : Var d₀ d₁ m)) : MvPolynomial (Var d₀ d₁ m) ℂ) •
        bvars d₀ d₁ k' := by
    funext i
    simp [bvars, scw_X, wb]
  rw [hb, dvalB_smul_P, ← map_pow, ← pow_mul, mul_comm (wb _ _ _) 3]

theorem Lcv_isWH (ch : Fin m → Fin 2) (k : Fin m) :
    (Lcv d₀ d₁ ch).IsWeightedHomogeneous (wb blk (Blk.e k)) 2 := by
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wb blk (Blk.e k)) Finset.univ
    (fun j => (X (.e j (bi (ch j))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ 2)
    (fun j => 2 * wb blk (Blk.e k) (.e j (bi (ch j)) : Var d₀ d₁ m))
    fun j _ => by
      have := (isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (.e j (bi (ch j)) : Var d₀ d₁ m)).pow 2
      simpa [mul_comm] using this
  rw [Lcv]; simpa [wb_e, Finset.sum_ite_eq', ← Finset.mul_sum] using this

theorem Lov_isWH (ch : Fin m → Fin 2) (k k' : Fin m) :
    (Lov d₀ d₁ ch k').IsWeightedHomogeneous (wb blk (Blk.e k)) (if k' = k then 0 else 2) := by
  have := IsWeightedHomogeneous.prod (R := ℂ) (w := wb blk (Blk.e k)) (Finset.univ.erase k')
    (fun j => (X (.e j (bi (ch j))) : MvPolynomial (Var d₀ d₁ m) ℂ) ^ 2)
    (fun j => 2 * wb blk (Blk.e k) (.e j (bi (ch j)) : Var d₀ d₁ m))
    fun j _ => by
      have := (isWeightedHomogeneous_X ℂ (wb blk (Blk.e k)) (.e j (bi (ch j)) : Var d₀ d₁ m)).pow 2
      simpa [mul_comm] using this
  rw [Lov]
  convert this using 1
  simp only [wb_e, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_erase, ne_eq,
    Finset.mem_univ, and_true]
  rcases eq_or_ne k' k with rfl | h
  · simp
  · simp [h, Ne.symm h]

theorem dvh_isWH (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) (v : Var d₀ d₁ m) :
    (dvh Ls ch w v).IsWeightedHomogeneous (wb blk (Blk.e k)) (wb blk (Blk.e k) v + 2) := by
  cases v with
  | x i =>
    refine LSG.ME.isWH_mul' (Lcv_isWH ch k) (isWeightedHomogeneous_C _ _) (by simp [wb])
  | y j =>
    refine LSG.ME.isWH_mul' (Lcv_isWH ch k) (LSG.ME.isWH_mul' (isWeightedHomogeneous_C _ _)
      (isWeightedHomogeneous_X _ _ _) rfl) (by simp [wb])
  | z j =>
    refine LSG.ME.isWH_mul' (Lcv_isWH ch k) (LSG.ME.isWH_mul' (N := 0)
      (isWeightedHomogeneous_C _ _).neg (isWeightedHomogeneous_X _ _ _) (by simp [wb])) (by simp [wb])
  | e k' c =>
    have h3 : (dvV Ls ch w (.e k' c)).IsWeightedHomogeneous (wb blk (Blk.e k))
        (3 * wb blk (Blk.e k) (.e k' c : Var d₀ d₁ m)) :=
      isWH_of_scw (scw_dvV_e ch w k k' c)
    refine LSG.ME.isWH_mul' (Lov_isWH ch k k') h3 ?_
    rw [wb_e]
    by_cases h : k' = k <;> simp [h]

/-- **`Dhc` raises every `E^♮` degree by `2`.** -/
theorem isHomV_Dhc {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hx : IsHomV x d)
    (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) : IsHomV (Dhc Ls ch w x) (fun k => d k + 2) :=
  fun k => LSG.ME.isWH_mkDerivation (fun v => dvh_isWH ch w k v) (hx k)

theorem isHomV_DLc {x : MvPolynomial (Var d₀ d₁ m) ℂ} {d : Fin m → ℕ} (hx : IsHomV x d)
    (ch : Fin m → Fin 2) (l : List (LieV ℂ d₀ d₁ m)) :
    IsHomV (DL (Dhc Ls ch) l x) (fun k => d k + 2 * l.length) := by
  induction l generalizing x d with
  | nil => simpa using hx
  | cons w l ih =>
    rw [DL_cons]
    have := ih (isHomV_Dhc (Ls := Ls) hx ch w)
    convert this using 2
    simp only [List.length_cons]; ring

/-- Evaluation of a homogeneous polynomial at a rescaled cone representative. -/
theorem eval_coords_isHomV {P : MvPolynomial (Var d₀ d₁ m) ℂ} {e : Fin m → ℕ} (hP : IsHomV P e)
    (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) :
    eval (coords g lam) P = (∏ k, (lam k : ℂ) ^ e k) * eval (coords g 1) P := by
  classical
  have : coords g lam = fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords g 1 v := by
    funext v
    cases v with
    | e k c =>
      simp only [coords, coordsZ_e, wb, blk_e]
      rw [Finset.prod_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    | _ => simp [coords, wb]
  rw [this, show eval (fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords g 1 v) P =
    aeval (fun v => (∏ k, ((lam k : ℂ)) ^ wb blk (Blk.e k) v) * coords g 1 v) P from rfl,
    aeval_weightScale _ e _ _ P hP]
  rfl

/-! ### `I_G̃` -/

theorem dvalB_bi {T : Type*} [CommRing T] (a : Fin 2) (g₂ g₃ s β : T) (P : Fin 5 → T) :
    dvalB a g₂ g₃ s β P (bi a) = 0 := by
  fin_cases a <;> simp [dvalB, bi, c2, Pe]

theorem dvV_bi (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    dvV Ls ch w (.e k (bi (ch k))) = 0 := by
  simp only [dvV]; exact dvalB_bi _ _ _ _ _ _

theorem Dhc_YZ (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (j : Fin d₁) :
    Dhc Ls ch w (YZ ℂ d₀ m j) = 0 := by
  simp only [YZ, map_sub, Derivation.leibniz, Dhc_X, dvh, facV, dvV, smul_eq_mul,
    Derivation.map_one_eq_zero]
  ring

theorem Dhc_Fk (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    Dhc Ls ch w (Fk (g2L Ls) (g3L Ls) d₀ d₁ k) = 0 := by
  have hF := dvalB_F (ch k) (C (g2L Ls k)) (C (g3L Ls k)) (C ((w.2.2 k).1 / 2))
    (C (w.2.2 k).2) (bvars d₀ d₁ k)
  simp only [bvars] at hF
  simp only [Fk, F, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, Dhc_X, Dhc_C,
    LSG.ME.D_ofNat, smul_eq_mul, nsmul_eq_mul, dvh, facV, dvV]
  linear_combination (Lov d₀ d₁ ch k) * hF

theorem Dhc_Gk (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    Dhc Ls ch w (Gk ℂ d₀ d₁ k) = 0 := by
  have hG := dvalB_G (ch k) (C (g2L Ls k)) (C (g3L Ls k)) (C ((w.2.2 k).1 / 2))
    (C (w.2.2 k).2) (bvars d₀ d₁ k)
  simp only [bvars] at hG
  simp only [Gk, Gfib, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, Dhc_X,
    LSG.ME.D_ofNat, smul_eq_mul, nsmul_eq_mul, dvh, facV, dvV]
  linear_combination (Lov d₀ d₁ ch k) * hG

/-- **`Dhc` maps `I_G̃` into `I_G̃`.** -/
theorem Dhc_IG (ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    Dhc Ls ch w P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  rw [IG, Ideal.ofList] at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hx
    rcases hx with (⟨j, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · rw [Dhc_YZ]; exact Ideal.zero_mem _
    · rw [Dhc_Fk]; exact Ideal.zero_mem _
    · rw [Dhc_Gk]; exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul a x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx')

theorem DLc_IG (ch : Fin m → Fin 2) (l : List (LieV ℂ d₀ d₁ m))
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    DL (Dhc Ls ch) l P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  induction l generalizing P with
  | nil => simpa using hP
  | cons w l ih => rw [DL_cons]; exact ih (Dhc_IG ch w hP)

/-! ### The chart change -/

/-- The Euler coefficient of the chart change in one block: `ψ_{VW} = s V W (g₂ W² − 12 U²)`. -/
def psiB {T : Type*} [CommRing T] (a b : Fin 2) (g₂ s : T) (P : Fin 5 → T) : T :=
  ![![0, s * P 1 * P 2 * (g₂ * P 2 ^ 2 - 12 * P 0 ^ 2)],
    ![-(s * P 1 * P 2 * (g₂ * P 2 ^ 2 - 12 * P 0 ^ 2)), 0]] a b

/-- The sign of a chart pair. -/
def sgnB {T : Type*} [CommRing T] (a b : Fin 2) : T := ![![0, 1], ![-1, 0]] a b

/-- The `F`-cofactor of the `V → W` chart change. -/
def cfF {T : Type*} [CommRing T] (s : T) (P : Fin 5 → T) (c : Fin 5) : T :=
  ![-3 * P 1 * P 2 * s, 0, 0, -6 * P 0 * P 2 * s, 6 * P 0 * P 1 * s] c

/-- The `G`-cofactor of the `V → W` chart change. -/
def cfG {T : Type*} [CommRing T] (g₂ s : T) (P : Fin 5 → T) (c : Fin 5) : T :=
  ![0, 0, 0, s * (g₂ * P 2 ^ 3 - 12 * P 0 ^ 2 * P 2), s * (12 * P 0 ^ 2 * P 1 - g₂ * P 1 * P 2 ^ 2)] c

/-- **Block chart change**: `L_b² dvalB_a − L_a² dvalB_b − ψ_{ab} P ∈ (F(P), G(P))`. -/
theorem cc_blk {T : Type*} [CommRing T] (a b : Fin 2) (c : Fin 5) (g₂ g₃ s β : T)
    (P : Fin 5 → T) :
    P (bi b) ^ 2 * dvalB a g₂ g₃ s β P c - P (bi a) ^ 2 * dvalB b g₂ g₃ s β P c -
      psiB a b g₂ s P * P c =
      (sgnB a b * cfF s P c) * Fn g₂ g₃ P + (sgnB a b * cfG g₂ s P c) * Gn P := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [dvalB, c2, rhoh, Pe, psiB, sgnB, cfF, cfG, bi, Fn, F, Gn, Gfib] <;> ring

variable (Ls) in
/-- The Euler coefficient of the chart change `ch₀ → ch` in block `k`. -/
noncomputable def aeV (ch₀ ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (k : Fin m) :
    MvPolynomial (Var d₀ d₁ m) ℂ :=
  Lov d₀ d₁ ch k * Lov d₀ d₁ ch₀ k *
    psiB (ch k) (ch₀ k) (C (g2L Ls k)) (C ((w.2.2 k).1 / 2)) (bvars d₀ d₁ k)

theorem chg_varV (ch₀ ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) (v : Var d₀ d₁ m) :
    ∃ G ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls),
      Lcv d₀ d₁ ch₀ * dvh Ls ch w v - Lcv d₀ d₁ ch * dvh Ls ch₀ w v =
        ∑ k, wb blk (Blk.e k) v • (aeV Ls ch₀ ch w k * X v) + G := by
  classical
  cases v with
  | e k c =>
    have hfg := cc_blk (ch k) (ch₀ k) c (C (g2L Ls k)) (C (g3L Ls k)) (C ((w.2.2 k).1 / 2))
      (C (w.2.2 k).2) (bvars d₀ d₁ k)
    have hF : Fn (C (g2L Ls k)) (C (g3L Ls k)) (bvars d₀ d₁ k) =
        (Fk (g2L Ls) (g3L Ls) d₀ d₁ k : MvPolynomial (Var d₀ d₁ m) ℂ) := by
      simp [Fn, Fk, bvars]
    have hG : Gn (bvars d₀ d₁ k) = (Gk ℂ d₀ d₁ k : MvPolynomial (Var d₀ d₁ m) ℂ) := by
      simp [Gn, Gk, bvars]
    rw [hF, hG] at hfg
    refine ⟨Lov d₀ d₁ ch k * Lov d₀ d₁ ch₀ k *
      ((sgnB (ch k) (ch₀ k) * cfF (C ((w.2.2 k).1 / 2)) (bvars d₀ d₁ k) c) *
          Fk (g2L Ls) (g3L Ls) d₀ d₁ k +
        (sgnB (ch k) (ch₀ k) * cfG (C (g2L Ls k)) (C ((w.2.2 k).1 / 2)) (bvars d₀ d₁ k) c) *
          Gk ℂ d₀ d₁ k),
      Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Fk_mem_IG _ _ k))
        (Ideal.mul_mem_left _ _ (Gk_mem_IG _ _ k))), ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [wb_e, Ne.symm hb]) (by simp)]
    simp only [wb_e, ite_true, one_smul]
    rw [Lcv_eq ch₀ k, Lcv_eq ch k]
    simp only [dvh, facV, dvV, aeV]
    simp only [bvars] at hfg ⊢
    linear_combination (Lov d₀ d₁ ch k * Lov d₀ d₁ ch₀ k) * hfg
  | x i => exact ⟨0, Ideal.zero_mem _, by simp [dvh, facV, wb, dvV]; ring⟩
  | y j => exact ⟨0, Ideal.zero_mem _, by simp [dvh, facV, wb, dvV]; ring⟩
  | z j => exact ⟨0, Ideal.zero_mem _, by simp [dvh, facV, wb, dvV]; ring⟩

/-- **Chart change identity**: `Lcv₀ · Dhc_ch − Lcv · Dhc_{ch₀} = Σₖ aeₖ · Eulerₖ` modulo `I_G̃`. -/
theorem chgV (ch₀ ch : Fin m → Fin 2) (w : LieV ℂ d₀ d₁ m) {x : MvPolynomial (Var d₀ d₁ m) ℂ}
    {d : Fin m → ℕ} (hx : IsHomV x d) :
    Lcv d₀ d₁ ch₀ * Dhc Ls ch w x - Lcv d₀ d₁ ch * Dhc Ls ch₀ w x -
      ∑ k, aeV Ls ch₀ ch w k * (d k • x) ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  classical
  choose G hG hGe using chg_varV (Ls := Ls) ch₀ ch w
  have e1 : Lcv d₀ d₁ ch₀ * Dhc Ls ch w x - Lcv d₀ d₁ ch * Dhc Ls ch₀ w x =
      ∑ v, (Lcv d₀ d₁ ch₀ * dvh Ls ch w v - Lcv d₀ d₁ ch * dvh Ls ch₀ w v) * pderiv v x := by
    rw [Dhc_eq_sum, Dhc_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have e3 : ∑ v, (∑ k, wb blk (Blk.e k) v • (aeV Ls ch₀ ch w k * X v)) * pderiv v x =
      ∑ k, aeV Ls ch₀ ch w k * (d k • x) := by
    calc ∑ v, (∑ k, wb blk (Blk.e k) v • (aeV Ls ch₀ ch w k * X v)) * pderiv v x
        = ∑ v, ∑ k, aeV Ls ch₀ ch w k * (wb blk (Blk.e k) v • (X v * pderiv v x)) :=
          Finset.sum_congr rfl fun v _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by
              rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = ∑ k, ∑ v, aeV Ls ch₀ ch w k * (wb blk (Blk.e k) v • (X v * pderiv v x)) :=
          Finset.sum_comm
      _ = ∑ k, aeV Ls ch₀ ch w k * (d k • x) :=
          Finset.sum_congr rfl fun k _ => by
            rw [← Finset.mul_sum, (hx k).sum_weight_X_mul_pderiv]
  have e2 : Lcv d₀ d₁ ch₀ * Dhc Ls ch w x - Lcv d₀ d₁ ch * Dhc Ls ch₀ w x -
      ∑ k, aeV Ls ch₀ ch w k * (d k • x) = ∑ v, G v * pderiv v x := by
    rw [e1, ← e3, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hGe v]; ring
  rw [e2]
  exact Ideal.sum_mem _ fun v _ => Ideal.mul_mem_right _ _ (hG v)

end LSG.MEV
