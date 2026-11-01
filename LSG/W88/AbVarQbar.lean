/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarMStar
import LSG.JacBlock.Simple

/-!
# Abelian subvarieties of `A^r` are defined over `ℚ̄` (tangent form)

`A = Jac(y² = 4x⁵ + 1)`, eigen-coordinates `(z₀, z₁)`, periods `latt = ⟨perVec e⟩`, `perVec e s = cJ s ζ^{(s+1)e}`.

**`abTan_qbar`**: if `t ⊂ (ℂ²)^r` is an abelian tangent (`IsAbelianTangentA`: `t ∩ latt^r` spans `t` over `ℝ`), then `t`
is spanned over `ℂ` by its vectors with algebraic coordinates. **`exists_alg_lam_ne`**: a nonzero `t` contains an algebraic
`z` with `Σ_j b_j z_j(0) ≠ 0` (for `θ(j, e) = ζ^e b_j` `ℚ`-independent).

Proof.
* `D₁ = diag(ζ − ζ⁴, ζ² − ζ³)`, `D₂ = diag(ζ² − ζ³, ζ⁴ − ζ)` (copywise) map `latt` into `latt` (multiplication by
  `ζ − ζ⁴`, `ζ² − ζ³ ∈ ℤ[ζ]`), and `i = c D₁ + d D₂` with real `c, d` that are `ℚ`-linearly independent
  (`cd_indep`: a relation would be a rational relation between `1, ζ, ζ², ζ³`).
* For a lattice point `w ∈ t`: `c D₁w + d D₂w = i w ∈ t = span_ℝ (lattice points of t)`, and `D₁w, D₂w` have rational
  coordinates in the period basis; a `ℚ`-linear functional `λ : ℝ → ℚ` with `λ c = 1`, `λ d = 0` (resp. swapped), applied
  to coordinates, gives `D₁w, D₂w ∈ t` (`mem_of_split`). So `t` is `D₁`- and `D₂`-stable, hence stable under the
  projection `P₀` onto the `z₀`-coordinates (a `ℂ`-combination of `D₁, D₂`).
* A lattice point is `w = cJ₀ a₀ + cJ₁ a₁` with `a_s = cJ_s⁻¹ P_s w ∈ t` algebraic (`a₀(j) = (Σ_e n_{je} ζ^e, 0)`).
-/

open Complex Module Polynomial

namespace LSG.W88

open LSG.JacAn LSG.JacAn.Beta

local notation "ζ" => LSG.JacAn.Beta.zetaN 5

variable {r : ℕ}

/-! ### The real numbers `P, Q, c, d` -/

lemma zeta_prim : IsPrimitiveRoot ζ 5 := zetaN_prim 5 (by norm_num)

lemma zeta_pow_five : ζ ^ 5 = 1 := zeta_prim.pow_eq_one

lemma zeta_ne_zero : ζ ≠ 0 := zeta_prim.ne_zero (by norm_num)

lemma conj_zeta : (starRingEnd ℂ) ζ = ζ ^ 4 := conj_zetaN5

lemma conj_zeta2 : (starRingEnd ℂ) (ζ ^ 2) = ζ ^ 3 := by
  rw [map_pow, conj_zeta, ← pow_mul]
  calc ζ ^ (4 * 2) = ζ ^ 5 * ζ ^ 3 := by rw [← pow_add]
    _ = ζ ^ 3 := by rw [zeta_pow_five, one_mul]

/-- `P = 2 Im ζ`. -/
noncomputable def Pz : ℝ := 2 * Complex.im ζ
/-- `Q = 2 Im ζ²`. -/
noncomputable def Qz : ℝ := 2 * (ζ ^ 2).im

lemma hPz : ζ - ζ ^ 4 = I * Pz := by
  rw [← conj_zeta, Complex.sub_conj, Pz]; push_cast; ring

lemma hQz : ζ ^ 2 - ζ ^ 3 = I * Qz := by
  rw [← conj_zeta2, Complex.sub_conj, Qz]; push_cast; ring

lemma Pz_ne : Pz ≠ 0 := by
  intro h
  have h1 : ζ - ζ ^ 4 = 0 := by rw [hPz, h]; simp
  have h3 : ζ ^ 3 = 1 := by
    have : ζ * (ζ ^ 3 - 1) = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left zeta_ne_zero)
  exact zeta_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h3

lemma PQ_ne : Pz ^ 2 + Qz ^ 2 ≠ 0 := by
  have := Pz_ne; positivity

/-- The real coefficients `c, d` with `i = c D₁ + d D₂`. -/
noncomputable def cR : ℝ := (Pz + Qz) / (Pz ^ 2 + Qz ^ 2)
noncomputable def dR : ℝ := (Qz - Pz) / (Pz ^ 2 + Qz ^ 2)

lemma hI0 : (cR : ℂ) * (ζ - ζ ^ 4) + dR * (ζ ^ 2 - ζ ^ 3) = I := by
  rw [hPz, hQz, cR, dR]
  have h := PQ_ne
  have h' : ((Pz : ℂ) ^ 2 + (Qz : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h
  push_cast
  field_simp
  ring

lemma hI1 : (cR : ℂ) * (ζ ^ 2 - ζ ^ 3) + dR * (ζ ^ 4 - ζ) = I := by
  have e : ζ ^ 4 - ζ = -(ζ - ζ ^ 4) := by ring
  rw [e, hPz, hQz, cR, dR]
  have h := PQ_ne
  have h' : ((Pz : ℂ) ^ 2 + (Qz : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h
  push_cast
  field_simp
  ring

/-- `1, ζ, ζ², ζ³` are `ℚ`-linearly independent. -/
lemma zeta_indep (a₀ a₁ a₂ a₃ : ℚ) (h : (a₀ : ℂ) + a₁ * ζ + a₂ * ζ ^ 2 + a₃ * ζ ^ 3 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  set R : ℚ[X] := C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3
  have hR : aeval ζ R = 0 := by simpa [R] using h
  have hdeg : R.natDegree < 4 := by
    have : R.natDegree ≤ 3 := by simp only [R]; compute_degree
    omega
  by_contra hne
  have hR0 : R ≠ 0 := by
    intro h0
    apply hne
    have c0 := congrArg (fun p => coeff p 0) h0
    have c1 := congrArg (fun p => coeff p 1) h0
    have c2 := congrArg (fun p => coeff p 2) h0
    have c3 := congrArg (fun p => coeff p 3) h0
    simp [R, coeff_X, coeff_X_pow] at c0 c1 c2 c3
    exact ⟨c0, c1, c2, c3⟩
  exact LSG.JacBlock.aeval_ne_zero hR0 hdeg (by simpa using zeta_prim) hR

/-- **`c, d` are `ℚ`-linearly independent.** -/
lemma cd_indep (a b : ℚ) (h : (a : ℝ) * cR + b * dR = 0) : a = 0 ∧ b = 0 := by
  have hPQ := PQ_ne
  have h1 : ((a : ℝ) - b) * Pz + ((a : ℝ) + b) * Qz = 0 := by
    rw [cR, dR] at h
    field_simp at h
    linear_combination h
  have h2 : ((a - b : ℚ) : ℂ) * (ζ - ζ ^ 4) + ((a + b : ℚ) : ℂ) * (ζ ^ 2 - ζ ^ 3) = 0 := by
    rw [hPz, hQz]
    have : (((a : ℝ) - b) * Pz + ((a : ℝ) + b) * Qz : ℂ) = 0 := by exact_mod_cast h1
    push_cast
    linear_combination I * this
  have h4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
    have hs := zeta_prim.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
    linear_combination hs
  rw [h4] at h2
  have := zeta_indep (a - b) (2 * (a - b)) (2 * a) (-2 * b) (by push_cast at h2 ⊢; linear_combination h2)
  obtain ⟨h0, -, h2', h3'⟩ := this
  constructor <;> linarith

/-- A `ℚ`-linear functional `λ : ℝ → ℚ` with `λ x = 1`, `λ y = 0`, for `ℚ`-independent `x, y`. -/
lemma exists_functional {x y : ℝ} (hxy : ∀ a b : ℚ, (a : ℝ) * x + b * y = 0 → a = 0 ∧ b = 0) :
    ∃ lf : ℝ →ₗ[ℚ] ℚ, lf x = 1 ∧ lf y = 0 := by
  have hli : LinearIndependent ℚ ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    exact hxy a b (by simpa [Rat.smul_def] using hab)
  set B := Basis.span hli
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.coord 0)
  refine ⟨g, ?_, ?_⟩
  · have hx : x ∈ Submodule.span ℚ (Set.range ![x, y]) := Submodule.subset_span ⟨0, rfl⟩
    have := congrArg (fun f => f ⟨x, hx⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have hb : B 0 = ⟨x, hx⟩ := by ext; simp [B, Basis.span_apply]
    rw [← hb, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  · have hy : y ∈ Submodule.span ℚ (Set.range ![x, y]) := Submodule.subset_span ⟨1, rfl⟩
    have := congrArg (fun f => f ⟨y, hy⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have hb : B 1 = ⟨y, hy⟩ := by ext; simp [B, Basis.span_apply]
    rw [← hb, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (by decide)]

/-! ### Rational coordinates and the splitting lemma -/

/-- Coordinates in the period basis. -/
noncomputable def crd (x : Fin r → Fin 2 → ℂ) (j : Fin r) (e : Fin 4) : ℝ := latBasis.repr (x j) e

/-- Rational coordinates. -/
def RatC (x : Fin r → Fin 2 → ℂ) : Prop := ∀ j e, ∃ q : ℚ, crd x j e = q

lemma crd_add (x y : Fin r → Fin 2 → ℂ) (j e) : crd (x + y) j e = crd x j e + crd y j e := by
  simp [crd]

lemma crd_smul (c : ℝ) (x : Fin r → Fin 2 → ℂ) (j e) : crd (c • x) j e = c * crd x j e := by
  simp [crd]

lemma crd_ext {x y : Fin r → Fin 2 → ℂ} (h : ∀ j e, crd x j e = crd y j e) : x = y := by
  funext j
  exact latBasis.ext_elem fun e => h j e

lemma crd_finsupp_sum (c : (Fin r → Fin 2 → ℂ) →₀ ℝ) (g : ℝ → ℝ) (j e) :
    crd (c.sum fun m s => g s • m) j e = c.sum fun m s => g s * crd m j e := by
  unfold Finsupp.sum
  induction c.support using Finset.induction_on with
  | empty => simp [crd]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, crd_add, crd_smul, ih]

/-- **The splitting lemma.** -/
theorem mem_of_split {S : Set (Fin r → Fin 2 → ℂ)} (hS : ∀ s ∈ S, RatC s) {u₁ u₂ : Fin r → Fin 2 → ℂ}
    (h₁ : RatC u₁) (h₂ : RatC u₂) {x y : ℝ}
    (hxy : ∀ a b : ℚ, (a : ℝ) * x + b * y = 0 → a = 0 ∧ b = 0)
    (h : x • u₁ + y • u₂ ∈ Submodule.span ℝ S) : u₁ ∈ Submodule.span ℝ S := by
  obtain ⟨lf, hlx, hly⟩ := exists_functional hxy
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.mp h
  set u : Fin r → Fin 2 → ℂ := c.sum fun m s => ((lf s : ℚ) : ℝ) • m
  have hu : u ∈ Submodule.span ℝ S := by
    refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span (hc hm))
  convert hu using 1
  refine crd_ext fun j e => ?_
  obtain ⟨q₁, hq₁⟩ := h₁ j e
  obtain ⟨q₂, hq₂⟩ := h₂ j e
  have heq := congrArg (fun z => crd z j e) hsum
  have hcs := crd_finsupp_sum c id j e
  simp only [id] at hcs
  rw [hcs] at heq
  simp only [crd_add, crd_smul, hq₁, hq₂] at heq
  -- apply `lf` to `x q₁ + y q₂ = Σ c_m crd m`
  choose qm hqm using fun m (hm : m ∈ c.support) => hS m (hc hm) j e
  have hR : (c.sum fun m s => s * crd m j e) = ∑ m ∈ c.support.attach, c m * (qm m.1 m.2 : ℝ) := by
    unfold Finsupp.sum
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only []
    rw [hqm]
  rw [hR] at heq
  have hl := congrArg lf heq
  have e1 : lf (x * q₁ + y * q₂) = q₁ := by
    rw [show x * (q₁ : ℝ) + y * q₂ = q₁ • x + q₂ • y by simp [Rat.smul_def]; ring, map_add,
      map_smul, map_smul, hlx, hly]
    simp
  have e2 : lf (∑ m ∈ c.support.attach, c m * (qm m.1 m.2 : ℝ)) =
      ∑ m ∈ c.support.attach, qm m.1 m.2 * lf (c m) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show c m * (qm m.1 m.2 : ℝ) = qm m.1 m.2 • c m by simp [Rat.smul_def]; ring, map_smul, smul_eq_mul]
  rw [e1, e2] at hl
  have hu_crd : crd u j e = ∑ m ∈ c.support.attach, ((lf (c m) : ℚ) : ℝ) * (qm m.1 m.2 : ℝ) := by
    simp only [u]
    rw [crd_finsupp_sum c (fun s => ((lf s : ℚ) : ℝ))]
    unfold Finsupp.sum
    rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only []
    rw [hqm]
  rw [hq₁, ← hl, hu_crd]
  push_cast
  refine Finset.sum_congr rfl fun m _ => by ring

/-! ### Lattice points -/

lemma crd_perVec (e e' : Fin 4) : latBasis.repr (perVec (e : ℕ)) e' = if e = e' then 1 else 0 := by
  rw [← latBasis_apply, Basis.repr_self, Finsupp.single_apply]

lemma ratC_of_latt {w : Fin r → Fin 2 → ℂ} (hw : ∀ j, w j ∈ latt) : RatC w := by
  intro j e
  obtain ⟨n, hn⟩ := latt_repr' (hw j)
  refine ⟨n e, ?_⟩
  rw [crd, hn, map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, map_zsmul, Finsupp.smul_apply, crd_perVec]
  simp

/-- `D(μ₀, μ₁)` copywise. -/
noncomputable def Dm (μ₀ μ₁ : ℂ) (z : Fin r → Fin 2 → ℂ) : Fin r → Fin 2 → ℂ :=
  fun j => ![μ₀ * z j 0, μ₁ * z j 1]

lemma Dm_add (μ₀ μ₁ : ℂ) (x y : Fin r → Fin 2 → ℂ) : Dm μ₀ μ₁ (x + y) = Dm μ₀ μ₁ x + Dm μ₀ μ₁ y := by
  funext j s; fin_cases s <;> simp [Dm, mul_add]

lemma Dm_smul (μ₀ μ₁ c : ℂ) (x : Fin r → Fin 2 → ℂ) : Dm μ₀ μ₁ (c • x) = c • Dm μ₀ μ₁ x := by
  funext j s; fin_cases s <;> simp [Dm] <;> ring

/-- `D₁ = diag(ζ − ζ⁴, ζ² − ζ³)`. -/
noncomputable abbrev D₁ : (Fin r → Fin 2 → ℂ) → Fin r → Fin 2 → ℂ := Dm (ζ - ζ ^ 4) (ζ ^ 2 - ζ ^ 3)
/-- `D₂ = diag(ζ² − ζ³, ζ⁴ − ζ)`. -/
noncomputable abbrev D₂ : (Fin r → Fin 2 → ℂ) → Fin r → Fin 2 → ℂ := Dm (ζ ^ 2 - ζ ^ 3) (ζ ^ 4 - ζ)

/-- The single-copy maps preserve `latt`. -/
lemma dm_latt (μ₀ μ₁ : ℂ) (k₁ k₂ : ℕ)
    (h0 : ∀ e : ℕ, μ₀ * (ζ ^ 1) ^ e = (ζ ^ 1) ^ (e + k₁) - (ζ ^ 1) ^ (e + k₂))
    (h1 : ∀ e : ℕ, μ₁ * (ζ ^ 2) ^ e = (ζ ^ 2) ^ (e + k₁) - (ζ ^ 2) ^ (e + k₂))
    {v : Fin 2 → ℂ} (hv : v ∈ latt) : ![μ₀ * v 0, μ₁ * v 1] ∈ latt := by
  unfold latt at hv
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    have : ![μ₀ * perVec (e : ℕ) 0, μ₁ * perVec (e : ℕ) 1] = perVec ((e : ℕ) + k₁) - perVec ((e : ℕ) + k₂) := by
      funext s; fin_cases s
      · simp only [Pi.sub_apply, perVec_eq]; simp; linear_combination cJ 0 * h0 e
      · simp only [Pi.sub_apply, perVec_eq]; simp; linear_combination cJ 1 * h1 e
    rw [this]; exact sub_mem (perVec_mem_latt _) (perVec_mem_latt _)
  | zero =>
    have : ![μ₀ * (0 : Fin 2 → ℂ) 0, μ₁ * (0 : Fin 2 → ℂ) 1] = 0 := by funext s; fin_cases s <;> simp
    rw [this]; exact latt.zero_mem
  | add x y _ _ hx hy =>
    have : ![μ₀ * (x + y) 0, μ₁ * (x + y) 1] = ![μ₀ * x 0, μ₁ * x 1] + ![μ₀ * y 0, μ₁ * y 1] := by
      funext s; fin_cases s <;> simp [mul_add]
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : ![μ₀ * (-x) 0, μ₁ * (-x) 1] = -![μ₀ * x 0, μ₁ * x 1] := by
      funext s; fin_cases s <;> simp
    rw [this]; exact neg_mem hx

lemma D₁_latt {w : Fin r → Fin 2 → ℂ} (hw : ∀ j, w j ∈ latt) : ∀ j, D₁ w j ∈ latt := fun j =>
  dm_latt _ _ 1 4 (fun e => by ring) (fun e => by
    have h5 := zeta_pow_five
    rw [show (ζ ^ 2) ^ (e + 4) = (ζ ^ 2) ^ e * ζ ^ 3 * (ζ ^ 5) by ring, h5]; ring) (hw j)

lemma D₂_latt {w : Fin r → Fin 2 → ℂ} (hw : ∀ j, w j ∈ latt) : ∀ j, D₂ w j ∈ latt := fun j =>
  dm_latt _ _ 2 3 (fun e => by ring) (fun e => by
    have h5 := zeta_pow_five
    rw [show (ζ ^ 2) ^ (e + 2) = (ζ ^ 2) ^ e * ζ ^ 4 by ring,
      show (ζ ^ 2) ^ (e + 3) = (ζ ^ 2) ^ e * ζ * ζ ^ 5 by ring, h5]; ring) (hw j)

lemma I_eq (w : Fin r → Fin 2 → ℂ) : I • w = (cR : ℝ) • D₁ w + (dR : ℝ) • D₂ w := by
  funext j s
  fin_cases s
  · simp [Dm, Complex.real_smul]; linear_combination (-w j 0) * hI0
  · simp [Dm, Complex.real_smul]; linear_combination (-w j 1) * hI1

/-! ### Stability -/

variable {t : Submodule ℂ (Fin r → Fin 2 → ℂ)}

/-- **An abelian tangent is `D₁`- and `D₂`-stable.** -/
theorem abTan_D (ht : IsAbelianTangentA t) {z : Fin r → Fin 2 → ℂ} (hz : z ∈ t) : D₁ z ∈ t ∧ D₂ z ∈ t := by
  set S := {z : Fin r → Fin 2 → ℂ | z ∈ t ∧ ∀ j, z j ∈ latt}
  have hS : ∀ s ∈ S, RatC s := fun s hs => ratC_of_latt hs.2
  have hspan : ∀ x, x ∈ t ↔ x ∈ Submodule.span ℝ S := fun x => by
    rw [← ht]; rfl
  have hlat : ∀ w ∈ S, D₁ w ∈ t ∧ D₂ w ∈ t := by
    intro w hw
    have hIw : (cR : ℝ) • D₁ w + (dR : ℝ) • D₂ w ∈ Submodule.span ℝ S := by
      rw [← I_eq, ← hspan]; exact t.smul_mem _ hw.1
    refine ⟨(hspan _).mpr (mem_of_split hS (ratC_of_latt (D₁_latt hw.2)) (ratC_of_latt (D₂_latt hw.2))
      cd_indep hIw), (hspan _).mpr (mem_of_split hS (ratC_of_latt (D₂_latt hw.2))
      (ratC_of_latt (D₁_latt hw.2)) (x := dR) (y := cR) (fun a b hab => (cd_indep b a (by linarith)).symm) (by
        rw [add_comm]; exact hIw))⟩
  have hz' := (hspan z).mp hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx => exact hlat x hx
  | zero => simp only [show D₁ (0 : Fin r → Fin 2 → ℂ) = 0 by funext j s; fin_cases s <;> simp [Dm],
      show D₂ (0 : Fin r → Fin 2 → ℂ) = 0 by funext j s; fin_cases s <;> simp [Dm]]; exact ⟨t.zero_mem, t.zero_mem⟩
  | add x y _ _ hx hy =>
    have e1 : D₁ (x + y) = D₁ x + D₁ y := Dm_add _ _ x y
    have e2 : D₂ (x + y) = D₂ x + D₂ y := Dm_add _ _ x y
    rw [e1, e2]; exact ⟨t.add_mem hx.1 hy.1, t.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    have e0 : (a • x : Fin r → Fin 2 → ℂ) = (a : ℂ) • x := (Complex.coe_smul a x).symm
    have e1 : D₁ ((a : ℂ) • x) = (a : ℂ) • D₁ x := Dm_smul _ _ _ x
    have e2 : D₂ ((a : ℂ) • x) = (a : ℂ) • D₂ x := Dm_smul _ _ _ x
    rw [e0, e1, e2]
    exact ⟨t.smul_mem _ hx.1, t.smul_mem _ hx.2⟩

/-- The projection onto the `z₀`-coordinates. -/
def P₀ (z : Fin r → Fin 2 → ℂ) : Fin r → Fin 2 → ℂ := fun j => ![z j 0, 0]

lemma P₀_eq (z : Fin r → Fin 2 → ℂ) :
    P₀ z = ((Pz : ℂ) / (I * (Pz ^ 2 + Qz ^ 2))) • D₁ z + ((Qz : ℂ) / (I * (Pz ^ 2 + Qz ^ 2))) • D₂ z := by
  have h' : ((Pz : ℂ) ^ 2 + (Qz : ℂ) ^ 2) ≠ 0 := by exact_mod_cast PQ_ne
  have e : ζ ^ 4 - ζ = -(ζ - ζ ^ 4) := by ring
  funext j s
  fin_cases s
  · simp only [P₀, Dm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_zero, Fin.zero_eta]
    rw [hPz, hQz]
    field_simp
    try ring
  · simp only [P₀, Dm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_zero]
    rw [e, hPz, hQz]
    field_simp
    ring

theorem abTan_P₀ (ht : IsAbelianTangentA t) {z : Fin r → Fin 2 → ℂ} (hz : z ∈ t) : P₀ z ∈ t := by
  rw [P₀_eq]
  exact t.add_mem (t.smul_mem _ (abTan_D ht hz).1) (t.smul_mem _ (abTan_D ht hz).2)

/-! ### `ℚ̄`-rationality -/

/-- **Abelian subvarieties of `A^r` are defined over `ℚ̄`** (tangent form). -/
theorem abTan_qbar (ht : IsAbelianTangentA t) : t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z} := by
  apply le_antisymm
  · intro z hz
    have hz' : z ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin r → Fin 2 → ℂ)) := hz
    rw [ht] at hz'
    have key : Submodule.span ℝ {z | z ∈ t ∧ ∀ j, z j ∈ latt} ≤
        (Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z}).restrictScalars ℝ := by
      rw [Submodule.span_le]
      rintro w ⟨hwt, hwl⟩
      choose n hn using fun j => latt_repr' (hwl j)
      have hc0 : cJ 0 ≠ 0 := cJ_ne_zero (by norm_num)
      have hc1 : cJ 1 ≠ 0 := cJ_ne_zero (by norm_num)
      have hw0 : ∀ j, w j 0 = cJ 0 * ∑ e : Fin 4, (n j e : ℂ) * ζ ^ (e : ℕ) := fun j => by
        rw [hn j, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Pi.smul_apply, zsmul_eq_mul, perVec_eq]; simp; ring
      have hw1 : ∀ j, w j 1 = cJ 1 * ∑ e : Fin 4, (n j e : ℂ) * (ζ ^ 2) ^ (e : ℕ) := fun j => by
        rw [hn j, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Pi.smul_apply, zsmul_eq_mul, perVec_eq]; simp; ring
      set a₀ : Fin r → Fin 2 → ℂ := (cJ 0)⁻¹ • P₀ w
      set a₁ : Fin r → Fin 2 → ℂ := (cJ 1)⁻¹ • (w - P₀ w)
      have ha₀ : a₀ ∈ t := t.smul_mem _ (abTan_P₀ ht hwt)
      have ha₁ : a₁ ∈ t := t.smul_mem _ (t.sub_mem hwt (abTan_P₀ ht hwt))
      have halg : ∀ (m : Fin 4 → ℤ) (x : ℂ), IsAlgebraic ℚ x →
          IsAlgebraic ℚ (∑ e : Fin 4, (m e : ℂ) * x ^ (e : ℕ)) := fun m x hx => by
        rw [← mem_algebraicClosure_iff]
        refine sum_mem fun e _ => mul_mem ?_ ?_
        · exact mem_algebraicClosure_iff.mpr (isAlgebraic_int (m e))
        · exact pow_mem (mem_algebraicClosure_iff.mpr hx) _
      have hz5 : IsAlgebraic ℚ ζ := ⟨X ^ 5 - 1, X_pow_sub_C_ne_zero (by norm_num) 1, by simp [zeta_pow_five]⟩
      have ha₀alg : AlgVecA a₀ := fun j s => by
        fin_cases s
        · simp only [a₀, Pi.smul_apply, P₀, smul_eq_mul]
          simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [hw0, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]; exact halg _ _ hz5
        · simp [a₀, P₀, isAlgebraic_zero]
      have ha₁alg : AlgVecA a₁ := fun j s => by
        fin_cases s
        · show IsAlgebraic ℚ ((cJ 1)⁻¹ * (w j 0 - w j 0)); simp [isAlgebraic_zero]
        · simp only [a₁, Pi.smul_apply, Pi.sub_apply, P₀, smul_eq_mul]
          simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
          rw [hw1, ← mul_assoc, inv_mul_cancel₀ hc1, one_mul]; exact halg _ _ (hz5.pow 2)
      have hw : w = cJ 0 • a₀ + cJ 1 • a₁ := by
        simp only [a₀, a₁, smul_smul, mul_inv_cancel₀ hc0, mul_inv_cancel₀ hc1, one_smul]; abel
      rw [hw]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (show a₀ ∈ {z | z ∈ t ∧ AlgVecA z} from ⟨ha₀, ha₀alg⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (show a₁ ∈ {z | z ∈ t ∧ AlgVecA z} from ⟨ha₁, ha₁alg⟩)))
    exact key hz'
  · rw [Submodule.span_le]; exact fun z hz => hz.1

/-- **A nonzero abelian tangent contains an algebraic vector with `Σ_j b_j z_j(0) ≠ 0`.** -/
theorem exists_alg_lam_ne (ht : IsAbelianTangentA t) (hne : t ≠ ⊥) {b : Fin r → ℂ}
    (hb : LinearIndependent ℚ (fun p : Fin r × Fin 4 => ζ ^ (p.2 : ℕ) * b p.1)) :
    ∃ z ∈ t, AlgVecA z ∧ ∑ j, b j * z j 0 ≠ 0 := by
  obtain ⟨z, hz, hzne⟩ := lam_ne_zero_of_abelian ht hne hb
  by_contra hcon
  push Not at hcon
  set ℓ : (Fin r → Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun z => ∑ j, b j * z j 0
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring }
  have hle : t ≤ LinearMap.ker ℓ := by
    rw [abTan_qbar ht, Submodule.span_le]
    rintro w ⟨hwt, hwa⟩
    exact hcon w hwt hwa
  exact hzne (hle hz)

/-! ### The statement forms consumed downstream -/

/-- **`RatTangentsA`** (STAGE_A5 §6.7): every abelian tangent of `A^r` is spanned by vectors with algebraic
coordinates. -/
def RatTangentsA : Prop :=
  ∀ (r : ℕ) (t : Submodule ℂ (Fin r → Fin 2 → ℂ)), IsAbelianTangentA t →
    t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z}

/-- **Abelian subvarieties of `A^r` are defined over `ℚ̄`.** -/
theorem ratTangentsA : RatTangentsA := fun _ _ ht => abTan_qbar ht

/-- `IsRatSub` for the product lattice `latt^r` is `IsAbelianTangentA`. -/
lemma isAbelianTangentA_iff_isRatSub (t : Submodule ℂ (Fin r → Fin 2 → ℂ)) :
    IsAbelianTangentA t ↔ LSG.MEB.IsRatSub (AddSubgroup.pi Set.univ (fun _ : Fin r => latt)) t := by
  unfold IsAbelianTangentA LSG.MEB.IsRatSub
  have : {z : Fin r → Fin 2 → ℂ | z ∈ t ∧ ∀ j, z j ∈ latt} =
      {z | z ∈ t ∧ z ∈ AddSubgroup.pi Set.univ (fun _ : Fin r => latt)} := by
    ext z; simp [AddSubgroup.mem_pi]
  rw [this]

/-- `RatTangentsA` in the `IsRatSub (latt^r)` form. -/
theorem ratTangentsA_isRatSub {t : Submodule ℂ (Fin r → Fin 2 → ℂ)}
    (ht : LSG.MEB.IsRatSub (AddSubgroup.pi Set.univ (fun _ : Fin r => latt)) t) :
    t = Submodule.span ℂ {z | z ∈ t ∧ AlgVecA z} :=
  abTan_qbar ((isAbelianTangentA_iff_isRatSub t).mpr ht)

end LSG.W88
