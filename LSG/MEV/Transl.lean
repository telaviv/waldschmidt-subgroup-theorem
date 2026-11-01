import Mathlib
import LSG.MEV.IGNull
import LSG.MEV.LawMap

/-!
# Translations on the `E^♮` multi-cone model (VECEXT_SPIKE §7.1–7.2)

For `g ∈ G̃` and a law choice `c : Fin m → LC` per `E^♮` factor (`LC = Fin 2 × Fin 2 × Fin 2`: the
`E`-law and the multipliers `λ, μ ∈ {V, W}`), `τ g c` is the `ℂ`-algebra endomorphism of `ℂ[Var]`
with `X ↦ X + x_g`, `Y ↦ y_g Y`, `Z ↦ y_g⁻¹ Z`, and, in the `k`-th block,
`(U, V, W, T₁, T₃) ↦ NLaw_{c k}((U, V, W, T₁, T₃), repV(g_k))` (bidegree `(3, 3)`).

* `lawPolyV_mem`: each component lies in `FLE (single (e k) 3)` (homogeneity by scaling).
* **Block multiplier** `bmulV` (`3` on `E^♮` blocks, `1` otherwise; the abelian `dblE` with
  multiplier `2` becomes `tplE`), **`transl_mem_FLE`**.
* **`transl_IG`**: `τ g c` maps `I_G̃` into `I_G̃` (law preservation `NLaw_mem`).
* **`eval_transl`**, `Good`, `exists_good`, **`eval_transl_good`** (`ν = λ³ μ`), `exists_cube_mul`.
* `translI g J = I_G̃ ⊔ (τ g c P : P ∈ J, all c)`; **`zeros_translI`**:
  `zeros (translI g J) = {h | h + g ∈ zeros J}`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE S bdeg mul_mem_FLE FLE_mono pow_mem_FLE' prod_mem_FLE')

namespace LSG.MEV

/-- A law choice for one `E^♮` factor: the `E`-law and the two multipliers. -/
abbrev LC : Type := Fin 2 × Fin 2 × Fin 2

/-- The law `c` on vectors. -/
def nlawc {R : Type*} [CommRing R] (c : LC) (g₂ g₃ : R) (P Q : Fin 5 → R) : Fin 5 → R :=
  NLaw g₂ g₃ c.1 c.2.1 c.2.2 P Q

theorem nlawc_smul_left (c : LC) {R : Type*} [CommRing R] (g₂ g₃ u : R) (P Q : Fin 5 → R) :
    nlawc c g₂ g₃ (u • P) Q = u ^ 3 • nlawc c g₂ g₃ P Q := by
  have := NLaw_smul g₂ g₃ c.1 c.2.1 c.2.2 P Q u 1
  rwa [one_smul, mul_one] at this

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- The variables of the `k`-th block, as a vector. -/
noncomputable def bvars (d₀ d₁ : ℕ) (k : Fin m) : Fin 5 → MvPolynomial (Var d₀ d₁ m) ℂ :=
  fun i => X (.e k i)

variable (Ls) in
/-- The law `c((U, V, W, T₁, T₃)_k, q)` in `ℂ[Var]`. -/
noncomputable def lawPolyV (d₀ d₁ : ℕ) (c : LC) (k : Fin m) (q : Fin 5 → ℂ) :
    Fin 5 → MvPolynomial (Var d₀ d₁ m) ℂ :=
  nlawc c (C (g2L Ls k)) (C (g3L Ls k)) (bvars d₀ d₁ k) fun i => C (q i)

/-! ### Block degrees of the laws -/

theorem scw_C {σ : Type*} [Fintype σ] (w : σ → ℕ) (a : ℂ) : scw w (C a : MvPolynomial σ ℂ) = C a :=
  by simp [scw]

theorem scw_X {σ : Type*} [Fintype σ] (w : σ → ℕ) (v : σ) :
    scw w (X v : MvPolynomial σ ℂ) = C ((2 : ℂ) ^ w v) * X v := by simp [scw]

/-- An algebra endomorphism applied to a law: substitute in the block variables. -/
theorem alg_lawPolyV (φ : MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ)
    (c : LC) (k : Fin m) (q : Fin 5 → ℂ) (i : Fin 5) :
    φ (lawPolyV Ls d₀ d₁ c k q i) =
      nlawc c (C (g2L Ls k)) (C (g3L Ls k)) (fun l => φ (X (.e k l))) (fun l => C (q l)) i := by
  rw [lawPolyV, nlawc, ← AlgHom.coe_toRingHom, NLaw_map]
  simp only [AlgHom.coe_toRingHom, nlawc]
  congr 1
  · exact MvPolynomial.algHom_C φ _
  · exact MvPolynomial.algHom_C φ _
  · funext l; simp [Function.comp, MvPolynomial.algHom_C]

theorem lawPolyV_isWH (c : LC) (k : Fin m) (q : Fin 5 → ℂ) (i : Fin 5) :
    (lawPolyV Ls d₀ d₁ c k q i).IsWeightedHomogeneous (wb blk (Blk.e k)) 3 := by
  apply isWH_of_scw
  rw [alg_lawPolyV]
  have hb : (fun l => scw (wb blk (Blk.e k)) (X (.e k l) : MvPolynomial (Var d₀ d₁ m) ℂ)) =
      (C (2 : ℂ) : MvPolynomial (Var d₀ d₁ m) ℂ) • bvars d₀ d₁ k := by
    funext l; simp [bvars, scw_X, wb]
  rw [hb, nlawc_smul_left]
  simp only [Pi.smul_apply, smul_eq_mul, map_pow]
  rfl

theorem lawPolyV_isWH_wo (c : LC) (k : Fin m) (q : Fin 5 → ℂ) (i : Fin 5) :
    (lawPolyV Ls d₀ d₁ c k q i).IsWeightedHomogeneous (wo blk (Blk.e k)) 0 := by
  apply isWH_of_scw
  rw [alg_lawPolyV]
  have hb : (fun l => scw (wo blk (Blk.e k)) (X (.e k l) : MvPolynomial (Var d₀ d₁ m) ℂ)) =
      bvars d₀ d₁ k := by
    funext l; simp [bvars, scw_X, wo]
  rw [hb]
  simp [lawPolyV]

theorem lawPolyV_mem (c : LC) (k : Fin m) (q : Fin 5 → ℂ) (i : Fin 5) :
    lawPolyV Ls d₀ d₁ c k q i ∈ FLE ℂ blk (Pi.single (Blk.e k) 3) :=
  mem_FLE_of_isWH (lawPolyV_isWH c k q i) (lawPolyV_isWH_wo c k q i)

/-! ### The translation `τ g c` -/

/-- The multiplier of a block: `3` on `E^♮` blocks, `1` otherwise. -/
def bmulV : Blk m → ℕ
  | .e _ => 3
  | _ => 1

/-- Block degrees after translation: `E^♮` entries tripled. -/
def tplE (D : Blk m → ℕ) : Blk m → ℕ := fun b => bmulV b * D b

theorem bmulV_le_three (b : Blk m) : bmulV b ≤ 3 := by cases b <;> simp [bmulV]

theorem tplE_le (D : Blk m → ℕ) (t : ℕ) : tplE (t • D) ≤ (3 * t) • D := fun b => by
  simp only [tplE, Pi.smul_apply, smul_eq_mul]
  have := bmulV_le_three b
  calc bmulV b * (t * D b) ≤ 3 * (t * D b) := Nat.mul_le_mul_right _ this
    _ = 3 * t * D b := by ring

variable (Ls) in
/-- The images of the variables under translation by `g` with law choice `c`. -/
noncomputable def translVar (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) :
    Var d₀ d₁ m → MvPolynomial (Var d₀ d₁ m) ℂ
  | .x i => X (.x i) + C (g.1 i)
  | .y j => C (g.ym j : ℂ) * X (.y j)
  | .z j => C (((g.ym j)⁻¹ : ℂˣ) : ℂ) * X (.z j)
  | .e k i => lawPolyV Ls d₀ d₁ (c k) k (repV (g.2.2 k)) i

variable (Ls) in
/-- **Translation by `g`** with law choice `c`. -/
noncomputable def τ (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) :
    MvPolynomial (Var d₀ d₁ m) ℂ →ₐ[ℂ] MvPolynomial (Var d₀ d₁ m) ℂ :=
  aeval (translVar Ls g c)

theorem translVar_mem (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) (v : Var d₀ d₁ m) :
    translVar Ls g c v ∈ FLE ℂ blk (Pi.single (blk v) (bmulV (blk v))) := by
  cases v with
  | x i =>
    have := LSG.ME.fle_add (LSG.ME.fle_X (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (Var.x i))
      (LSG.ME.fle_C (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (D := Pi.single Blk.x 1) (g.1 i))
    simpa [bmulV, translVar] using this
  | y j =>
    have := mul_mem_FLE ℂ (LSG.ME.fle_C (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0)
      (g.ym j : ℂ)) (LSG.ME.fle_X (Var.y j : Var d₀ d₁ m))
    simpa [bmulV, translVar] using this
  | z j =>
    have := mul_mem_FLE ℂ (LSG.ME.fle_C (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) (D := 0)
      (((g.ym j)⁻¹ : ℂˣ) : ℂ)) (LSG.ME.fle_X (Var.z j : Var d₀ d₁ m))
    simpa [bmulV, translVar] using this
  | e k i =>
    have := lawPolyV_mem (Ls := Ls) (d₀ := d₀) (d₁ := d₁) (c k) k (repV (g.2.2 k)) i
    simpa [bmulV, translVar] using this

/-- **Block degrees under translation**: `X`- and `(Y, Z)`-degrees are preserved, `E^♮` degrees
at most triple. -/
theorem transl_mem_FLE (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) {D : Blk m → ℕ}
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} (hP : P ∈ FLE ℂ blk D) :
    τ Ls g c P ∈ FLE ℂ blk (tplE D) := by
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  have hnS : n ∈ S blk D := by
    rw [FLE, mem_restrictSupport_iff] at hP; exact hP hn
  rw [τ, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  have hprod := prod_mem_FLE' (K := ℂ) (β := (blk : Var d₀ d₁ m → Blk m)) Finset.univ
    (fun v => translVar Ls g c v ^ n v)
    (fun v => Pi.single (blk v) (n v * bmulV (blk v))) fun v _ =>
      LSG.ME.fle_pow_single (translVar_mem g c v) (n v)
  have hle : (∑ v, (Pi.single (blk v) (n v * bmulV (blk v)) : Blk m → ℕ)) ≤ tplE D := by
    rw [Pi.le_def]
    intro b
    have hb := hnS b
    simp only [bdeg] at hb
    simp only [Finset.sum_apply, Pi.single_apply, tplE]
    calc ∑ v, (if b = blk v then n v * bmulV (blk v) else 0)
        = ∑ v, bmulV b * (if blk v = b then n v else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : b = blk v
          · subst h; simp [mul_comm]
          · simp [h, Ne.symm h]
      _ = bmulV b * ∑ v, (if blk v = b then n v else 0) := by rw [Finset.mul_sum]
      _ ≤ bmulV b * D b := Nat.mul_le_mul_left _ hb
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (FLE_mono ℂ blk hle hprod)

/-! ### `I_G̃` is preserved -/

theorem eval_lawPolyV (c : LC) (k : Fin m) (q : Fin 5 → ℂ) (i : Fin 5) (x : Var d₀ d₁ m → ℂ) :
    eval x (lawPolyV Ls d₀ d₁ c k q i) =
      nlawc c (Ls k).g₂ (Ls k).g₃ (fun i => x (.e k i)) q i := by
  rw [lawPolyV, nlawc, NLaw_map (eval x)]
  simp only [nlawc, eval_C, g2L, g3L]
  congr 1
  · funext l; simp [bvars]
  · funext l; simp

theorem transl_IG (g : GPtV d₀ d₁ Ls) (c : Fin m → LC) {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)) :
    τ Ls g c P ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
  have hle : (IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls)).map (τ Ls g c) ≤ IG (g2L Ls) (g3L Ls) := by
    rw [IG, Ideal.ofList, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨Q, hQ, rfl⟩
    simp only [lG, List.mem_append, List.mem_ofFn, Set.mem_ofPred_eq] at hQ
    -- law preservation in block `k`
    have hblock : ∀ k, Ideal.span {Fn (C (g2L Ls k)) (C (g3L Ls k)) (bvars d₀ d₁ k),
        Gn (bvars d₀ d₁ k)} ≤ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := fun k => by
      rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact Fk_mem_IG (g2L Ls) (g3L Ls) k
      · exact Gk_mem_IG (g2L Ls) (g3L Ls) k
    have hmem : ∀ k, Fn (C (g2L Ls k)) (C (g3L Ls k)) (lawPolyV Ls d₀ d₁ (c k) k (repV (g.2.2 k)))
        ∈ IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ∧
        Gn (lawPolyV Ls d₀ d₁ (c k) k (repV (g.2.2 k))) ∈
          IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := fun k => by
      have hFq : Fn (C (g2L Ls k)) (C (g3L Ls k))
          (fun i => (C (repV (g.2.2 k) i) : MvPolynomial (Var d₀ d₁ m) ℂ)) = 0 := by
        have := Fn_map (C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ) (Ls k).g₂ (Ls k).g₃ (repV (g.2.2 k))
        rw [Fn_repV, map_zero] at this
        exact this.symm
      have hGq : Gn (fun i => (C (repV (g.2.2 k) i) : MvPolynomial (Var d₀ d₁ m) ℂ)) = 0 := by
        have := Gn_map (C : ℂ →+* MvPolynomial (Var d₀ d₁ m) ℂ) (repV (g.2.2 k))
        rw [Gn_repV, map_zero] at this
        exact this.symm
      have hI : Inat (C (g2L Ls k)) (C (g3L Ls k)) (bvars d₀ d₁ k)
          (fun i => (C (repV (g.2.2 k) i) : MvPolynomial (Var d₀ d₁ m) ℂ)) ≤
          IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) := by
        rw [Inat, hFq, hGq]
        refine le_trans (Ideal.span_le.mpr ?_) (hblock k)
        rintro _ (rfl | rfl | rfl | rfl)
        · exact Ideal.subset_span (Or.inl rfl)
        · exact Ideal.subset_span (Or.inr rfl)
        · exact Ideal.zero_mem _
        · exact Ideal.zero_mem _
      obtain ⟨h1, h2⟩ := NLaw_mem (C (g2L Ls k)) (C (g3L Ls k)) (c k).1 (c k).2.1 (c k).2.2
        (bvars d₀ d₁ k) fun i => C (repV (g.2.2 k) i)
      exact ⟨hI h1, hI h2⟩
    rcases hQ with (⟨j, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · have : τ Ls g c (YZ ℂ d₀ m j) = YZ ℂ d₀ m j := by
        simp only [YZ, τ, map_sub, map_mul, aeval_X, map_one, translVar]
        have h1 : C (g.ym j : ℂ) * C (((g.ym j)⁻¹ : ℂˣ) : ℂ) = (1 : MvPolynomial (Var d₀ d₁ m) ℂ) := by
          rw [← C_mul, Units.mul_inv, C_1]
        linear_combination (X (.y j) * X (.z j) : MvPolynomial (Var d₀ d₁ m) ℂ) * h1
      rw [SetLike.mem_coe, this]
      exact YZ_mem_IG _ _ j
    · have himg : τ Ls g c (Fk (g2L Ls) (g3L Ls) d₀ d₁ k) =
          Fn (C (g2L Ls k)) (C (g3L Ls k)) (lawPolyV Ls d₀ d₁ (c k) k (repV (g.2.2 k))) := by
        simp only [Fk, F, Fn, τ, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
          algebraMap_eq, map_ofNat, translVar]
      rw [SetLike.mem_coe, himg]
      exact (hmem k).1
    · have himg : τ Ls g c (Gk ℂ d₀ d₁ k) = Gn (lawPolyV Ls d₀ d₁ (c k) k (repV (g.2.2 k))) := by
        simp only [Gk, Gfib, Gn, τ, map_add, map_sub, map_mul, map_pow, aeval_X, map_ofNat,
          translVar]
      rw [SetLike.mem_coe, himg]
      exact (hmem k).2
  exact hle (Ideal.mem_map_of_mem _ hP)

/-! ### Evaluation -/

theorem eval_aeval' {σ : Type*} (A : MvPolynomial σ ℂ) (h : σ → MvPolynomial σ ℂ) (u : σ → ℂ) :
    eval u (aeval h A) = eval (fun k => eval u (h k)) A := by
  rw [aeval_def, eval_eval₂]
  have : (eval u).comp (algebraMap ℂ (MvPolynomial σ ℂ)) = RingHom.id ℂ := by ext; simp
  rw [this]; rfl

theorem nlawc_repV (c : LC) {L : PeriodPair} (a b : EVL L) :
    ∃ μ : ℂ, nlawc c L.g₂ L.g₃ (repV a) (repV b) = μ • repV (a + b) :=
  NLaw_repV a b c.1 c.2.1 c.2.2

/-- **Evaluation of a translate** (any law choice). -/
theorem eval_transl (g h : GPtV d₀ d₁ Ls) (c : Fin m → LC) (lam : Fin m → ℂˣ) :
    ∃ ν : Fin m → ℂ, ∀ P, eval (coords h lam) (τ Ls g c P) = eval (coordsZ (h + g) ν) P := by
  choose μ hμ using fun k => nlawc_repV (c k) (h.2.2 k) (g.2.2 k)
  refine ⟨fun k => (lam k : ℂ) ^ 3 * μ k, fun P => ?_⟩
  rw [τ, eval_aeval']
  congr 2
  funext v
  cases v with
  | x i => simp [translVar, coords, add_comm]
  | y j => simp [translVar, coords, mul_comm]
  | z j => simp [translVar, coords, mul_comm]
  | e k i =>
    simp only [translVar, eval_lawPolyV, coords, coordsZ_e]
    have : (fun i => (lam k : ℂ) * repV (h.2.2 k) i) = (lam k : ℂ) • repV (h.2.2 k) := by
      funext i; simp
    rw [this, nlawc_smul_left, hμ k]
    simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_add, Pi.add_apply]
    ring

/-- The law choice `c` is **good** at `(h, g)`: every chosen law is nonzero there. -/
def Good (h g : GPtV d₀ d₁ Ls) (c : Fin m → LC) : Prop :=
  ∀ k, nlawc (c k) (Ls k).g₂ (Ls k).g₃ (repV (h.2.2 k)) (repV (g.2.2 k)) ≠ 0

theorem exists_good (h g : GPtV d₀ d₁ Ls) : ∃ c, Good h g c := by
  choose i j k hc using fun k => exists_NLaw_ne (h.2.2 k) (g.2.2 k)
  exact ⟨fun l => (i l, j l, k l), fun l => hc l⟩

/-- **Evaluation of a translate**, good law choice: `ν = λ³ μ` with `μ` independent of `λ`. -/
theorem eval_transl_good {g h : GPtV d₀ d₁ Ls} {c : Fin m → LC} (hc : Good h g c) :
    ∃ μ : Fin m → ℂˣ, ∀ lam P, eval (coords h lam) (τ Ls g c P) =
      eval (coords (h + g) fun k => lam k ^ 3 * μ k) P := by
  choose μ hμ0 hμ using fun k => NLaw_repV_ne (h.2.2 k) (g.2.2 k) (c k).1 (c k).2.1 (c k).2.2
    (hc k)
  refine ⟨fun k => Units.mk0 (μ k) (hμ0 k), fun lam P => ?_⟩
  rw [τ, eval_aeval']
  congr 2
  funext v
  cases v with
  | x i => simp [translVar, coords, add_comm]
  | y j => simp [translVar, coords, mul_comm]
  | z j => simp [translVar, coords, mul_comm]
  | e k i =>
    simp only [translVar, eval_lawPolyV, coords, coordsZ_e]
    have : (fun i => (lam k : ℂ) * repV (h.2.2 k) i) = (lam k : ℂ) • repV (h.2.2 k) := by
      funext i; simp
    rw [this, nlawc_smul_left]
    simp only [nlawc] at hμ ⊢
    rw [hμ k]
    simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_add, Pi.add_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    ring

/-- Every `ν ∈ (ℂˣ)^m` is `λ³ μ` for some `λ`. -/
theorem exists_cube_mul (μ ν : Fin m → ℂˣ) :
    ∃ lam : Fin m → ℂˣ, (fun k => lam k ^ 3 * μ k) = ν := by
  have : ∀ k, ∃ z : ℂˣ, z ^ 3 * μ k = ν k := fun k => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((ν k : ℂ) / μ k) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
      exact div_ne_zero (ν k).ne_zero (μ k).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
    field_simp
  choose lam hlam using this
  exact ⟨lam, funext hlam⟩

/-! ### Ideal translates -/

variable (Ls) in
/-- The ideal translate `τ_g J = I_G̃ + (τ g c P : P ∈ J, all c)`; its zeros are `zeros J − g`. -/
noncomputable def translI (g : GPtV d₀ d₁ Ls) (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  IG (d₀ := d₀) (d₁ := d₁) (g2L Ls) (g3L Ls) ⊔ Ideal.span {Q | ∃ P ∈ J, ∃ c, Q = τ Ls g c P}

/-- **Zeros of an ideal translate.** -/
theorem zeros_translI (g : GPtV d₀ d₁ Ls) (J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)) :
    zeros (translI Ls g J : Set _) = {h | h + g ∈ zeros (J : Set _)} := by
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hh P hP lam'
    obtain ⟨c, hc⟩ := exists_good h g
    obtain ⟨μ, hμ⟩ := eval_transl_good hc
    obtain ⟨lam, hlam⟩ := exists_cube_mul μ lam'
    have := hh _ (Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, c, rfl⟩)) lam
    rw [hμ, hlam] at this
    exact this
  · intro hh
    rw [mem_zeros_iff_le_vanish]
    refine sup_le (IG_le_vanish _) (Ideal.span_le.mpr ?_)
    rintro _ ⟨P, hP, c, rfl⟩
    refine mem_vanish.mpr fun h' hh' lam => ?_
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    obtain ⟨ν, hν⟩ := eval_transl g h' c lam
    rw [hν]
    exact eval_coordsZ_eq_zero (hh P hP) ν

end LSG.MEV
