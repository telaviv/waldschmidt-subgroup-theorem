import Mathlib
import LSG.MEV.FormalExp

/-!
# Philippon's operators for `E^♮` blocks (Philippon 1986, §4.1; VECEXT_SPIKE §7.1)

For `g ∈ G̃`, `w ∈ Lie G̃`, law choices `c, c' : Fin m → LC` and `κ ∈ ℕ`:
`phOp g w c c' κ Q = [z^κ] Q(law_c(X, law_{c'}(rep g, exp(z w))))` (blockwise with the eight
bidegree-`(3, 3)` laws on `E^♮` blocks; `G_a`, `G_m` blocks translated by `x_g + z ξ`,
`y_g e^{η z}`), with the formal exponential `ExpV` of `LSG.MEV.FormalExp`.

* `phPt g w c'`: the formal point `g + exp(z w)`; it lies on `G̃` (`phPt_YZ`, `phPt_F`, `phPt_G`).
* **`phOp_mem_FLE`**: `Q ∈ FLE D ⇒ phOp g w c c' κ Q ∈ FLE (tplE D)` (`E^♮` degrees at most
  tripled, the others preserved), **for every `κ`** (Philippon's `c₁ = 3` for `E^♮` blocks).
  The `E^♮` case (`CF_nlaw`) is proved by homogeneity: rescaling block `k` by `2` multiplies every
  coefficient of the law by `2³` and rescaling the other blocks fixes it.
* **`phOp_IG`**: `phOp` maps `I_G̃` into `I_G̃` (law preservation `NLaw_mem` over `ℂ⟦z⟧` and over
  `ℂ[Var]⟦z⟧`).
* `eval_phOp`: at a point `x₀`, `phOp … Q` is the `κ`-th coefficient of `Q(law_c(x₀, phPt))`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE S bdeg mul_mem_FLE FLE_mono)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

local notation "PS" => PowerSeries (MvPolynomial (Var d₀ d₁ m) ℂ)

/-! ### Coefficientwise block degrees -/

section CF

/-- All coefficients in `FLE D`. -/
def CF (D : Blk m → ℕ) (F : PS) : Prop := ∀ n, PowerSeries.coeff n F ∈ FLE ℂ blk D

theorem CF_add {D : Blk m → ℕ} {F G : PS} (hF : CF D F) (hG : CF D G) : CF D (F + G) :=
  fun n => by rw [map_add]; exact LSG.ME.fle_add (hF n) (hG n)

theorem CF.mono {D D' : Blk m → ℕ} {F : PS} (hF : CF D F) (h : D ≤ D') : CF D' F :=
  fun n => LSG.ME.fle_le (hF n) h

theorem CF_mul {D E : Blk m → ℕ} {F G : PS} (hF : CF D F) (hG : CF E G) : CF (D + E) (F * G) :=
  fun n => by
    rw [PowerSeries.coeff_mul]
    exact Submodule.sum_mem _ fun p _ => mul_mem_FLE ℂ (hF p.1) (hG p.2)

theorem CF_C {D : Blk m → ℕ} {p : MvPolynomial (Var d₀ d₁ m) ℂ} (hp : p ∈ FLE ℂ blk D) :
    CF D (PowerSeries.C p) := fun n => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact Submodule.zero_mem _

theorem CF_mapC {D : Blk m → ℕ} (B : PowerSeries ℂ) :
    CF D (PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ) B) :=
  fun n => by rw [PowerSeries.coeff_map]; exact LSG.ME.fle_C _

theorem CF_one {D : Blk m → ℕ} : CF D (1 : PS) := by
  rw [← map_one PowerSeries.C]; exact CF_C (by rw [← C_1]; exact LSG.ME.fle_C _)

theorem CF_pow {D : Blk m → ℕ} {F : PS} (hF : CF D F) (n : ℕ) : CF (n • D) (F ^ n) := by
  induction n with
  | zero => simpa using (CF_one (D := 0))
  | succ n ih => rw [pow_succ, succ_nsmul]; exact CF_mul ih hF

theorem CF_prod {ι' : Type*} (s : Finset ι') (f : ι' → PS) (e : ι' → Blk m → ℕ)
    (h : ∀ i ∈ s, CF (e i) (f i)) : CF (∑ i ∈ s, e i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CF_one (D := 0))
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact CF_mul (h x (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CF_sum {ι' : Type*} (s : Finset ι') (f : ι' → PS) {D : Blk m → ℕ}
    (h : ∀ i ∈ s, CF D (f i)) : CF D (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact Submodule.sum_mem _ fun i hi => h i hi n

/-- `PowerSeries.map` of a `ℂ`-algebra endomorphism fixes `algebraMap`. -/
theorem map_alg_algebraMap (φ : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ)
    (a : ℂ) : PowerSeries.map φ.toRingHom (algebraMap ℂ PS a) = algebraMap ℂ PS a := by
  simp only [PowerSeries.algebraMap_apply]
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_C]
  split_ifs
  · simp [MvPolynomial.algebraMap_eq, MvPolynomial.algHom_C]
  · simp

theorem map_alg_mapC (φ : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ)
    (B : PowerSeries ℂ) :
    PowerSeries.map φ.toRingHom (PowerSeries.map (MvPolynomial.C) B) = PowerSeries.map C B := by
  ext n; simp [PowerSeries.coeff_map, MvPolynomial.algHom_C]

/-- **Block degrees of an `E^♮` law** with power-series second argument: every coefficient has
degree `3` in block `k` and `0` elsewhere. -/
theorem CF_nlaw (c : LC) (k : Fin m) (a b : ℂ) (B : Fin 5 → PowerSeries ℂ) (i : Fin 5) :
    CF (Pi.single (Blk.e k) 3) (nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
      (fun i => PowerSeries.C (X (.e k i))) (fun i => PowerSeries.map C (B i)) i) := by
  intro n
  set L := nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
      (fun i => PowerSeries.C (X (.e k i))) (fun i => PowerSeries.map C (B i)) i
  have key : ∀ (w : Var d₀ d₁ m → ℕ) (u : MvPolynomial (Var d₀ d₁ m) ℂ),
      (∀ l, scw w (X (.e k l) : MvPolynomial (Var d₀ d₁ m) ℂ) = u * X (.e k l)) →
      scw w (PowerSeries.coeff n L) = u ^ 3 * PowerSeries.coeff n L := by
    intro w u hu
    have h1 : PowerSeries.map (scw w).toRingHom L =
        nlawc c (algebraMap ℂ PS a) (algebraMap ℂ PS b)
          ((PowerSeries.C u) • fun i => PowerSeries.C (X (.e k i)))
          (fun i => PowerSeries.map C (B i)) i := by
      rw [show L = NLaw (algebraMap ℂ PS a) (algebraMap ℂ PS b) c.1 c.2.1 c.2.2
        (fun i => PowerSeries.C (X (.e k i))) (fun i => PowerSeries.map C (B i)) i from rfl,
        NLaw_map, map_alg_algebraMap, map_alg_algebraMap]
      congr 1
      · funext l; simp [PowerSeries.map_C, hu]
      · funext l; exact map_alg_mapC _ _
    rw [nlawc_smul_left] at h1
    have h2 := congrArg (PowerSeries.coeff n) h1
    rw [PowerSeries.coeff_map] at h2
    simp only [AlgHom.coe_toRingHom, Pi.smul_apply, smul_eq_mul, ← map_pow,
      PowerSeries.coeff_C_mul] at h2
    exact h2
  refine mem_FLE_of_isWH (isWH_of_scw ?_) (isWH_of_scw ?_)
  · rw [key (wb blk (Blk.e k)) (C 2) (fun l => by simp [scw_X, wb]), map_pow]
  · rw [key (wo blk (Blk.e k)) 1 (fun l => by simp [scw_X, wo])]
    simp

end CF

/-! ### The operators -/

variable (Ls) in
/-- The formal point `g + exp(z w)`, computed with the laws `c'`. -/
noncomputable def phPt (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC) :
    Var d₀ d₁ m → PowerSeries ℂ
  | .x i => PowerSeries.C (g.1 i) + ExpV (g2L Ls) (g3L Ls) w (.x i)
  | .y j => PowerSeries.C (g.ym j : ℂ) * ExpV (g2L Ls) (g3L Ls) w (.y j)
  | .z j => PowerSeries.C (((g.ym j)⁻¹ : ℂˣ) : ℂ) * ExpV (g2L Ls) (g3L Ls) w (.z j)
  | .e k i => nlawc (c' k) (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
      (fun l => PowerSeries.C (repV (g.2.2 k) l)) (fun l => ExpV (g2L Ls) (g3L Ls) w (.e k l)) i

variable (Ls) in
/-- The substitution `X ↦ law_c(X, g + exp(z w))`, with coefficients in `ℂ[Var]`. -/
noncomputable def phSub (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) :
    Var d₀ d₁ m → PS
  | .x i => PowerSeries.C (X (.x i)) + PowerSeries.map C (phPt Ls g w c' (.x i))
  | .y j => PowerSeries.C (X (.y j)) * PowerSeries.map C (phPt Ls g w c' (.y j))
  | .z j => PowerSeries.C (X (.z j)) * PowerSeries.map C (phPt Ls g w c' (.z j))
  | .e k i => nlawc (c k) (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
      (fun l => PowerSeries.C (X (.e k l))) (fun l => PowerSeries.map C (phPt Ls g w c' (.e k l))) i

variable (Ls) in
/-- **Philippon's operator** `δ^κ_g` along `w` (law choices `c, c'`). -/
noncomputable def phOp (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    (Q : MvPolynomial (Var d₀ d₁ m) ℂ) : MvPolynomial (Var d₀ d₁ m) ℂ :=
  PowerSeries.coeff κ (aeval (phSub Ls g w c c') Q)

theorem phOp_add (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    (P Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    phOp Ls g w c c' κ (P + Q) = phOp Ls g w c c' κ P + phOp Ls g w c c' κ Q := by
  simp [phOp]

/-! ### Degrees (independent of `κ`) -/

theorem CF_phSub (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (v : Var d₀ d₁ m) :
    CF (Pi.single (blk v) (bmulV (blk v))) (phSub Ls g w c c' v) := by
  have hX := fun u : Var d₀ d₁ m => LSG.ME.fle_X (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) u
  cases v with
  | x i =>
    simp only [phSub]
    exact CF_add (CF_C (by simpa [bmulV] using hX (.x i))) (CF_mapC _)
  | y j =>
    simp only [phSub]
    simpa [bmulV] using CF_mul (CF_C (hX (.y j))) (CF_mapC (D := 0) _)
  | z j =>
    simp only [phSub]
    simpa [bmulV] using CF_mul (CF_C (hX (.z j))) (CF_mapC (D := 0) _)
  | e k i =>
    simp only [phSub]
    simpa [bmulV] using CF_nlaw (d₀ := d₀) (d₁ := d₁) (c k) k _ _ _ i

/-- **Degree bound**: `phOp` at most triples `E^♮` degrees and preserves the others, for every
order `κ` (Philippon's `c₁ = 3`, independent of `κ`). -/
theorem phOp_mem_FLE (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    {D : Blk m → ℕ} {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ FLE ℂ blk D) :
    phOp Ls g w c c' κ Q ∈ FLE ℂ blk (tplE D) := by
  suffices h : CF (tplE D) (aeval (phSub Ls g w c c') Q) by exact h κ
  rw [Q.as_sum, map_sum]
  refine CF_sum _ _ fun s hs => ?_
  have hsS : s ∈ S blk D := by
    rw [FLE, mem_restrictSupport_iff] at hQ; exact hQ hs
  rw [aeval_monomial, Finsupp.prod]
  have h1 : ∀ v, CF (s v • Pi.single (blk v) (bmulV (blk v))) (phSub Ls g w c c' v ^ s v) :=
    fun v => CF_pow (CF_phSub g w c c' v) (s v)
  have hprod : CF (∑ v ∈ s.support, s v • Pi.single (blk v) (bmulV (blk v)))
      (∏ v ∈ s.support, phSub Ls g w c c' v ^ s v) := CF_prod _ _ _ fun v _ => h1 v
  have hle : (∑ v ∈ s.support, (s v • Pi.single (blk v) (bmulV (blk v)) : Blk m → ℕ)) ≤
      tplE D := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ _ => Nat.zero_le _) ?_
    rw [Pi.le_def]
    intro b
    have hb := hsS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, tplE]
    calc ∑ v, s v * (if b = blk v then bmulV (blk v) else 0)
        = ∑ v, bmulV b * (if blk v = b then s v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmulV b * ∑ v, (if blk v = b then s v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmulV b * D b := Nat.mul_le_mul_left _ hb
  have hc : ∀ a : ℂ, CF (0 : Blk m → ℕ) (algebraMap ℂ PS a) := fun a => by
    rw [PowerSeries.algebraMap_apply]; exact CF_C (LSG.ME.fle_C _)
  exact (CF_mul (hc _) hprod).mono (by simpa using hle)

/-! ### `I_G̃` -/

/-- Power series all of whose coefficients lie in `I`. -/
def CI (I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) : Ideal PS where
  carrier := {F | ∀ n, PowerSeries.coeff n F ∈ I}
  add_mem' hF hG n := by rw [map_add]; exact I.add_mem (hF n) (hG n)
  zero_mem' n := by rw [map_zero]; exact I.zero_mem
  smul_mem' a F hF n := by
    rw [smul_eq_mul, PowerSeries.coeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hF p.2)

theorem C_mem_CI {I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {p : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hp : p ∈ I) : PowerSeries.C p ∈ CI I := fun n => by
  rw [PowerSeries.coeff_C]; split_ifs
  · exact hp
  · exact I.zero_mem

theorem phPt_YZ (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC) (j : Fin d₁) :
    phPt Ls g w c' (.y j) * phPt Ls g w c' (.z j) = 1 := by
  simp only [phPt]
  rw [show ∀ a b c d : PowerSeries ℂ, a * b * (c * d) = (a * c) * (b * d) from
      fun _ _ _ _ => by ring, ← map_mul, Units.mul_inv, map_one, one_mul]
  exact ExpV_YZ _ _ w j

/-- The `E^♮` part of `g + exp(z w)` lies on `X`. -/
theorem phPt_FG (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c' : Fin m → LC) (k : Fin m) :
    Fn (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₂) (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₃)
      (fun i => phPt Ls g w c' (.e k i)) = 0 ∧ Gn (fun i => phPt Ls g w c' (.e k i)) = 0 := by
  have hF1 : Fn (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₂) (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₃)
      (fun l => PowerSeries.C (repV (g.2.2 k) l)) = 0 := by
    have := Fn_map (PowerSeries.C : ℂ →+* PowerSeries ℂ) (Ls k).g₂ (Ls k).g₃ (repV (g.2.2 k))
    rw [Fn_repV, map_zero] at this
    simpa [Function.comp_def, PowerSeries.algebraMap_apply] using this.symm
  have hG1 : Gn (fun l => (PowerSeries.C (repV (g.2.2 k) l) : PowerSeries ℂ)) = 0 := by
    have := Gn_map (PowerSeries.C : ℂ →+* PowerSeries ℂ) (repV (g.2.2 k))
    rw [Gn_repV, map_zero] at this
    simpa [Function.comp_def] using this.symm
  have hF2 := ExpV_F (g2L Ls) (g3L Ls) w k
  have hG2 := ExpV_G (g2L Ls) (g3L Ls) w k
  simp only [g2L, g3L] at hF2
  have hI : Inat (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₂) (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₃)
      (fun l => PowerSeries.C (repV (g.2.2 k) l)) (fun l => ExpV (g2L Ls) (g3L Ls) w (.e k l)) =
      ⊥ := by
    rw [Inat, hF1, hG1, hF2, hG2]
    simp
  obtain ⟨h1, h2⟩ := NLaw_mem (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₂)
    (algebraMap ℂ (PowerSeries ℂ) (Ls k).g₃) (c' k).1 (c' k).2.1 (c' k).2.2
    (fun l => PowerSeries.C (repV (g.2.2 k) l)) (fun l => ExpV (g2L Ls) (g3L Ls) w (.e k l))
  rw [hI, Submodule.mem_bot] at h1 h2
  exact ⟨h1, h2⟩

/-- **`phOp` maps `I_G̃` into `I_G̃`.** -/
theorem phOp_IG (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m) (c c' : Fin m → LC) (κ : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) ℂ} (hQ : Q ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    phOp Ls g w c c' κ Q ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  suffices h : IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ≤
      (CI (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls))).comap (aeval (phSub Ls g w c c')) from
    h hQ κ
  -- law preservation in block `k`
  have hblk : ∀ k, Fn (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
      (fun i => phSub Ls g w c c' (.e k i)) ∈ CI (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) ∧
      Gn (fun i => phSub Ls g w c c' (.e k i)) ∈
        CI (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) := fun k => by
    have hFX : Fn (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
        (fun l => PowerSeries.C (X (.e k l))) = PowerSeries.C (Fk (g2L Ls) (g3L Ls) d₀ d₁ k) := by
      simp [Fn, F, Fk, PowerSeries.algebraMap_apply, g2L, g3L, map_ofNat]
    have hGX : Gn (fun l => (PowerSeries.C (X (.e k l)) : PS)) = PowerSeries.C (Gk ℂ d₀ d₁ k) := by
      simp [Gn, Gfib, Gk, map_ofNat]
    obtain ⟨hF2, hG2⟩ := phPt_FG g w c' k
    have hFm : Fn (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
        (fun l => PowerSeries.map C (phPt Ls g w c' (.e k l))) = 0 := by
      have := Fn_map (PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ))
        (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃) (fun i => phPt Ls g w c' (.e k i))
      rw [hF2, map_zero] at this
      simpa [PowerSeries.algebraMap_apply, Function.comp_def] using this.symm
    have hGm : Gn (fun l => PowerSeries.map C (phPt Ls g w c' (.e k l)) : Fin 5 → PS) = 0 := by
      have := Gn_map (PowerSeries.map (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ))
        (fun i => phPt Ls g w c' (.e k i))
      rw [hG2, map_zero] at this
      simpa [Function.comp_def] using this.symm
    have hI : Inat (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
        (fun l => PowerSeries.C (X (.e k l))) (fun l => PowerSeries.map C (phPt Ls g w c' (.e k l)))
        ≤ CI (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) := by
      rw [Inat, hFX, hGX, hFm, hGm, Ideal.span_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact C_mem_CI (Fk_mem_IG _ _ k)
      · exact C_mem_CI (Gk_mem_IG _ _ k)
      · exact Ideal.zero_mem _
      · exact Ideal.zero_mem _
    obtain ⟨h1, h2⟩ := NLaw_mem (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃) (c k).1
      (c k).2.1 (c k).2.2 (fun l => PowerSeries.C (X (.e k l)))
      (fun l => PowerSeries.map C (phPt Ls g w c' (.e k l)))
    exact ⟨hI h1, hI h2⟩
  rw [IG, Ideal.ofList, Ideal.span_le]
  rintro _ hP
  simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hP
  rcases hP with (⟨j, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · have e : aeval (phSub Ls g w c c') (YZ ℂ d₀ m j) = PowerSeries.C (YZ ℂ d₀ m j) := by
      simp only [YZ, map_sub, map_mul, aeval_X, map_one, phSub]
      rw [show ∀ a b c d : PS, a * b * (c * d) = (a * c) * (b * d) from fun _ _ _ _ => by ring,
        ← map_mul (PowerSeries.map MvPolynomial.C), phPt_YZ, map_one, mul_one]
    rw [SetLike.mem_coe, Ideal.mem_comap, e]
    exact C_mem_CI (YZ_mem_IG _ _ j)
  · rw [SetLike.mem_coe, Ideal.mem_comap]
    have e : aeval (phSub Ls g w c c') (Fk (g2L Ls) (g3L Ls) d₀ d₁ k) =
        Fn (algebraMap ℂ PS (Ls k).g₂) (algebraMap ℂ PS (Ls k).g₃)
          (fun i => phSub Ls g w c c' (.e k i)) := by
      simp [Fk, F, Fn, g2L, g3L, PowerSeries.algebraMap_apply, map_ofNat]
    rw [e]; exact (hblk k).1
  · rw [SetLike.mem_coe, Ideal.mem_comap]
    have e : aeval (phSub Ls g w c c') (Gk ℂ d₀ d₁ k) = Gn (fun i => phSub Ls g w c c' (.e k i)) :=
      by simp [Gk, Gfib, Gn, map_ofNat]
    rw [e]; exact (hblk k).2

/-! ### Evaluation -/

/-- The point `x₀ + (g + exp(z w))` computed with the laws `c` (`x₀` any cone vector). -/
noncomputable def lawAt (x₀ : Var d₀ d₁ m → ℂ) (B : Var d₀ d₁ m → PowerSeries ℂ) (c : Fin m → LC) :
    Var d₀ d₁ m → PowerSeries ℂ
  | .x i => PowerSeries.C (x₀ (.x i)) + B (.x i)
  | .y j => PowerSeries.C (x₀ (.y j)) * B (.y j)
  | .z j => PowerSeries.C (x₀ (.z j)) * B (.z j)
  | .e k i => nlawc (c k) (algebraMap ℂ _ (Ls k).g₂) (algebraMap ℂ _ (Ls k).g₃)
      (fun l => PowerSeries.C (x₀ (.e k l))) (fun l => B (.e k l)) i

/-- **Evaluation**: `phOp … Q (x₀)` is the `κ`-th Taylor coefficient of `Q(x₀ + (g + exp(z w)))`. -/
theorem eval_phOp (x₀ : Var d₀ d₁ m → ℂ) (g : GPtV d₀ d₁ Ls) (w : LieV ℂ d₀ d₁ m)
    (c c' : Fin m → LC) (κ : ℕ) (Q : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval x₀ (phOp Ls g w c c' κ Q) =
      PowerSeries.coeff κ (aeval (lawAt (Ls := Ls) x₀ (phPt Ls g w c') c) Q) := by
  rw [phOp, ← PowerSeries.coeff_map, LSG.ME.ringHom_aeval (PowerSeries.map (eval x₀))
    (fun a => by simp [PowerSeries.algebraMap_apply])]
  have hid : (eval x₀).comp (MvPolynomial.C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ) =
      RingHom.id ℂ := by
    ext; simp
  have hmm : ∀ F : PowerSeries ℂ, PowerSeries.map (eval x₀) (PowerSeries.map C F) = F :=
    fun F => by rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hid, PowerSeries.map_id]; rfl
  have halg : ∀ a : ℂ, PowerSeries.map (eval x₀) (algebraMap ℂ PS a) =
      algebraMap ℂ (PowerSeries ℂ) a := fun a => by
    simp [PowerSeries.algebraMap_apply]
  have e : (fun v => PowerSeries.map (eval x₀) (phSub Ls g w c c' v)) =
      lawAt (Ls := Ls) x₀ (phPt Ls g w c') c := by
    funext v
    cases v with
    | x i => simp [phSub, lawAt, hmm]
    | y j => simp [phSub, lawAt, hmm]
    | z j => simp [phSub, lawAt, hmm]
    | e k i =>
      simp only [phSub, lawAt, nlawc]
      rw [NLaw_map, halg, halg]
      congr 1
      · funext l; simp
      · funext l; simp [hmm]
  rw [e]

end LSG.MEV
