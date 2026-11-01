/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFun.Prop21Gen

/-!
# Lemma L for a product lattice (non-vacuity check of Tier 3)

For the product basis `e_{(j,0)} = α_j δ_j`, `e_{(j,1)} = β_j δ_j` (`Im(ᾱ_j β_j) ≠ 0`), i.e. the
lattice `Π_j (ℤα_j + ℤβ_j) ⊂ ℂⁿ` of Tier 2, Lemma L (`LSG.Aux.LemmaLInterp`) is **proved** here,
with exponent `c = 1`: it is Lagrange interpolation in each coordinate on the `(2A+1)²` lattice
nodes (`grid_interp2` with the constants of `lat_coord`). So the hypothesis of
`prop21Gen_of_interp` is satisfiable, and the conditional Tier-3 theorem specialises to the
unconditional Tier-2 theorem `prop21Lat` (`LSG.Aux.prop21Lat_of_gen`).

* `LSG.Aux.prodBasis`, `LSG.Aux.vecL_prodBasis`, `LSG.Aux.gptL_prodBasis`.
* `LSG.Aux.lemmaLInterp_prodBasis`, `LSG.Aux.prop21Lat_of_gen`.
-/

open Complex Finset

namespace LSG.Aux

variable {n : ℕ}

/-- The product basis: `(j, 0) ↦ α_j δ_j`, `(j, 1) ↦ β_j δ_j`. -/
noncomputable def prodBasis (α β : Fin n → ℂ) : Idx n → (Fin n → ℂ) :=
  fun c => Pi.single c.1 (if c.2 = 0 then α c.1 else β c.1)

lemma vecL_prodBasis (α β : Fin n → ℂ) (x : Idx n → ℤ) :
    vecL (prodBasis α β) x = perVec α β x := by
  funext j
  simp [vecL, prodBasis, perVec, Finset.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Pi.single_apply]

lemma gptL_prodBasis (α β : Fin n → ℂ) (K : ℕ) (v : Idx n → ℤ) :
    gptL (prodBasis α β) K v = gpt α β K v := by
  rw [gptL, vecL_prodBasis, gpt_eq_div]

/-- **Lemma L for a product lattice** (proved; exponent `c = 1`). -/
theorem lemmaLInterp_prodBasis (α β : Fin n → ℂ)
    (hD : ∀ j, ((starRingEnd ℂ) (α j) * β j).im ≠ 0) : LemmaLInterp (prodBasis α β) := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ j, (‖α j‖ + ‖β j‖) := ⟨_, rfl⟩
  have hSj : ∀ j, ‖α j‖ + ‖β j‖ ≤ S := fun j => by
    have := single_le_sum (f := fun j => ‖α j‖ + ‖β j‖) (fun j _ => by positivity) (mem_univ j)
    rw [hSdef]; linarith
  have hS1 : 1 ≤ S := by
    have := sum_nonneg fun j (_ : j ∈ univ) => (by positivity : 0 ≤ ‖α j‖ + ‖β j‖)
    rw [hSdef]; linarith
  obtain ⟨ci, hcidef⟩ : ∃ ci : ℝ,
      ci = 1 + ∑ j, (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im| := ⟨_, rfl⟩
  have hcij : ∀ j, (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im| ≤ ci := fun j => by
    have := single_le_sum (f := fun j => (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im|)
      (fun j _ => by positivity) (mem_univ j)
    rw [hcidef]; linarith
  have hci1 : 1 ≤ ci := by
    have := sum_nonneg fun j (_ : j ∈ univ) =>
      (by positivity : 0 ≤ (‖α j‖ + ‖β j‖) / |((starRingEnd ℂ) (α j) * β j).im|)
    rw [hcidef]; linarith
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = 3 * S * ci * Real.exp 2 := ⟨_, rfl⟩
  have hG1 : 1 ≤ G := by
    have h1 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ S * ci := one_le_mul_of_one_le_of_one_le hS1 hci1
    have : 1 ≤ S * ci * Real.exp 2 := one_le_mul_of_one_le_of_one_le h2 h1
    rw [hGdef]; nlinarith
  have hBs1 : 1 ≤ 16 * G := by linarith
  obtain ⟨CL, hCLdef⟩ : ∃ CL : ℝ, CL = max ((16 * G) ^ (9 * n) * 2 ^ n) (4 * S) := ⟨_, rfl⟩
  have hCL4 : 4 * S ≤ CL := hCLdef ▸ le_max_right _ _
  have hCLG : (16 * G) ^ (9 * n) * 2 ^ n ≤ CL := hCLdef ▸ le_max_left _ _
  refine ⟨1, CL, 1, one_pos, by linarith, ?_⟩
  intro F A K r R ε M hF _ hA hK hr hArK hrK2 hCLR hε hM hgridL hMR z hz
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hS0 : (0 : ℝ) ≤ S := by linarith
  set r' : ℝ := S * r with hr'
  have hr'0 : 0 < r' := by positivity
  have hrr' : r ≤ r' := le_mul_of_one_le_left hr.le hS1
  have hR4 : 4 * r' ≤ R := by
    have : 4 * S * r ≤ CL * r := mul_le_mul_of_nonneg_right hCL4 hr.le
    rw [hr']; linarith
  have hSAK : S * A / K ≤ r' := by
    rw [div_le_iff₀ hKpos, hr']
    have := mul_le_mul_of_nonneg_left hArK hS0
    linarith
  have hrK : r' * K ≤ 2 * S * A := by
    have := mul_le_mul_of_nonneg_left hrK2 hS0
    rw [hr']; linarith
  have hcoord := fun j => lat_coord (hD j) hA hK hr'0 hR4 (hSj j) (hcij j) hS1 hci1 hSAK hrK
  rw [← hGdef] at hcoord
  -- grid values
  have hgrid : ∀ g : Fin n → ℂ, (∀ j, g j ∈ latNodes (α j) (β j) A K) → ‖F g‖ ≤ ε := by
    intro g hg
    choose pj hpj hpjg using fun j => mem_image.mp (hg j)
    set v : Idx n → ℤ := fun c => ((if c.2 = 0 then (pj c.1).1 else (pj c.1).2 : ℕ) : ℤ) - A
    have hgv : g = gpt α β K v := by
      rw [gpt_eq_lnode]; funext j; exact (hpjg j).symm
    have hv : ∀ c, |v c| ≤ A := by
      intro c
      have hb := hpj c.1
      simp only [latBox, mem_product, mem_range] at hb
      simp only [v]
      split_ifs <;> rw [abs_le] <;> constructor <;> omega
    rw [hgv, ← gptL_prodBasis]
    exact hgridL v hv
  -- interpolation
  have hR0 : 0 < R := by linarith
  have hRr0 : 0 < R / r' := by positivity
  have hq0 : 0 ≤ 2 * r' / (R - r') := div_nonneg (by linarith) (by linarith)
  have hRq : R / r' * (2 * r' / (R - r')) ≤ 4 := by
    rw [show R / r' * (2 * r' / (R - r')) = 2 * R / (R - r') by field_simp]
    rw [div_le_iff₀ (by linarith)]; linarith
  have hC := lag_C_le (M := (2 * A + 1) ^ 2) hG1 hRr0.le hq0 hRq
  have hC1 : (1 : ℝ) ≤ (16 * G) ^ ((2 * A + 1) ^ 2) := one_le_pow₀ hBs1
  have hint := grid_interp2 F hF (fun j => latNodes (α j) (β j) A K) ((2 * A + 1) ^ 2)
    (fun j => card_latNodes (hD j) hK) hr'0.le (by linarith) (fun j => (hcoord j).1)
    (fun j => (hcoord j).2.1) (fun j => (hcoord j).2.2) hC hC1 hε hM hgrid hMR (hz.trans hrr')
  -- comparison of constants
  set N : ℕ := (2 * A + 1) ^ 2
  set q : ℝ := 2 * r' / (R - r')
  set Y : ℝ := CL * r / R
  have hY0 : 0 ≤ Y := div_nonneg (mul_nonneg (by linarith) hr.le) hR0.le
  have hY1 : Y ≤ 1 := by rw [div_le_one hR0]; exact hCLR
  have hqY : q ≤ Y := by
    have h1 : q ≤ 4 * r' / R := by
      rw [div_le_div_iff₀ (by linarith) hR0]; nlinarith
    have h2 : 4 * r' / R ≤ Y := by
      rw [hr']
      exact div_le_div_of_nonneg_right (by nlinarith) hR0.le
    linarith
  have hNA : A ^ 2 ≤ N := Nat.pow_le_pow_left (by omega) 2
  have hqN : q ^ N ≤ Y ^ (A ^ 2) :=
    (pow_le_pow_left₀ hq0 hqY N).trans (pow_le_pow_of_le_one hY0 hY1 hNA)
  have hYr : Y ^ ((1 : ℝ) * (A : ℝ) ^ 2) = Y ^ (A ^ 2) := by
    rw [one_mul]; exact_mod_cast Real.rpow_natCast Y (A ^ 2)
  rw [hYr]
  have hn2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h2n1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hA2 : A ^ 2 ≠ 0 := by positivity
  have hpre1 : ((16 * G) ^ N) ^ n ≤ ((16 * G) ^ (9 * n)) ^ (A ^ 2) := by
    rw [← pow_mul, ← pow_mul]
    refine pow_le_pow_right₀ hBs1 ?_
    have : N ≤ 9 * A ^ 2 := by simp only [N]; nlinarith
    calc N * n ≤ 9 * A ^ 2 * n := Nat.mul_le_mul_right n this
      _ = 9 * n * A ^ 2 := by ring
  have hpre2 : (2 : ℝ) ^ n ≤ (2 ^ n) ^ (A ^ 2) := le_self_pow₀ h2n1 hA2
  have hpre : ((16 * G) ^ N) ^ n * 2 ^ n ≤ CL ^ (A ^ 2) := by
    calc ((16 * G) ^ N) ^ n * 2 ^ n ≤ ((16 * G) ^ (9 * n)) ^ (A ^ 2) * (2 ^ n) ^ (A ^ 2) := by
          gcongr
      _ = ((16 * G) ^ (9 * n) * 2 ^ n) ^ (A ^ 2) := (mul_pow _ _ _).symm
      _ ≤ CL ^ (A ^ 2) := by gcongr
  have hin : ε + n * q ^ N * M ≤ 2 ^ n * (ε + Y ^ (A ^ 2) * M) := by
    have h1 : (n : ℝ) * q ^ N * M ≤ 2 ^ n * (Y ^ (A ^ 2) * M) := by
      have := mul_le_mul hn2 hqN (by positivity) (by positivity)
      calc (n : ℝ) * q ^ N * M = (n * q ^ N) * M := rfl
        _ ≤ (2 ^ n * Y ^ (A ^ 2)) * M := by gcongr
        _ = 2 ^ n * (Y ^ (A ^ 2) * M) := by ring
    have h2 : ε ≤ 2 ^ n * ε := le_mul_of_one_le_left hε h2n1
    rw [mul_add]; linarith
  calc ‖F z‖ ≤ ((16 * G) ^ N) ^ n * (ε + n * q ^ N * M) := hint
    _ ≤ ((16 * G) ^ N) ^ n * (2 ^ n * (ε + Y ^ (A ^ 2) * M)) := by gcongr
    _ = (((16 * G) ^ N) ^ n * 2 ^ n) * (ε + Y ^ (A ^ 2) * M) := by ring
    _ ≤ CL ^ (A ^ 2) * (ε + Y ^ (A ^ 2) * M) := by gcongr

/-- **Tier 2 from Tier 3.** `prop21Gen_of_interp` for the product basis, with Lemma L discharged
by `lemmaLInterp_prodBasis`, gives the statement of `LSG.Aux.prop21Lat` (independently of its
proof). -/
theorem prop21Lat_of_gen (n κ : ℕ) (a : ℝ) (ha : 0 ≤ a) (α β : Fin n → ℂ)
    (hD : ∀ j, ((starRingEnd ℂ) (α j) * β j).im ≠ 0) (P : Fin κ → Idx n → ℤ)
    (I : Fin κ → Idx n) (hI : Function.Injective I) (hd : (minorMat P I).det ≠ 0) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (L : ℕ) (b Δ U R r : ℝ) (ψ : Fin L → (Fin n → ℂ) → ℂ),
      1 ≤ L → 0 < Δ → Δ ≤ U → c₁ ≤ R / r → c₁ ≤ r → r ^ 2 * Real.log (R / r) ≤ U →
      0 ≤ b → b * r ^ 2 ≤ a * U →
      (∀ l, Differentiable ℂ (ψ l)) → (∀ z, ‖z‖ ≤ R → ∑ l, ‖ψ l z‖ ≤ Real.exp U) →
      (∀ k : Fin κ → ℤ, ∀ z : Fin n → ℂ, ∃ m : ℂ,
        ‖m‖ ≤ Real.exp (b * (‖z‖ + ‖∑ i, (k i : ℂ) • perVec α β (P i)‖) ^ 2) ∧
        ∀ l, ψ l (z + ∑ i, (k i : ℂ) • perVec α β (P i)) = m * ψ l z) →
      c₂ * U ^ (n + 1) ≤ L * Δ * r ^ κ * Real.log (R / r) ^ n →
      ∃ p : Fin L → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp Δ) ∧
        ∀ z, ‖z‖ ≤ r → ‖∑ l, (p l : ℂ) * ψ l z‖ ≤ Real.exp (-U) := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := prop21Gen_of_interp n κ a ha (prodBasis α β)
    (lemmaLInterp_prodBasis α β hD) P I hI hd
  refine ⟨c₁, c₂, h1, h2, fun L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR hQP hc =>
    h L b Δ U R r ψ hL hΔ hΔU hRr hr hU hb0 hbU hψd hψR ?_ hc⟩
  have hv : ∀ i, ∑ c, (P i c : ℂ) • prodBasis α β c = perVec α β (P i) :=
    fun i => vecL_prodBasis α β (P i)
  simp only [hv]
  exact hQP

end LSG.Aux
