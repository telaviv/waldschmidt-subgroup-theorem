import Mathlib
import LSG.MEV.Blk4H0
import LSG.MEV.Blk4Hilb
import LSG.MEV.Blk4SliceIG

/-!
# Pieces of the 4-block assembly on `G̃_r` (STAGE5_MEV §10.3)

* `ex0L`, `ex2L`: W88's exponents of `G′ = G̃′/K_M` (`t₀ = dim prLead T′`,
  `t₂ = dim (T′ ∩ ker prLead ∩ ker prB)`).
* **`exps4`**: `dim leadL(h₀) = ex0L`, `ex2L = ex2 + j`, `ex0 = ex0L + j` with
  `j = dim (h₀ ∩ ker leadL)`.
* **`fle4_of_trail`**: `P ∈ FLE blk (D₀, D₁, D₂)` with trailing degree `≤ D₂` lies in
  `FLE (blk4 d₀) (D₀, D₂, D₁, D₂)`.
* `prod_blk4_x`: `∏ᵢ D(blk4 d₀ (x i)) = D_lead^{d₀} D_trail^r`.
* `CstV4`, **`final_arith4`**: the final arithmetic with right side `D₀^{d₀} D₁^{d₁} D₂^{2m+r}`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair Module
open LSG.ME (g2L g3L Blk Dfun)
open LSG.W88.Vec (vecIncl torIncl)
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.MEV

noncomputable section

variable {d₀ r d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-- `t₀ = dim prLead T′`. -/
def ex0L (T : Submodule ℂ (TanG (d₀ + r) d₁ m)) : ℕ :=
  finrank ℂ (T.map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)))

/-- `t₂ = dim (T′ ∩ ker prLead ∩ ker prB)`. -/
def ex2L (T : Submodule ℂ (TanG (d₀ + r) d₁ m)) : ℕ :=
  finrank ℂ ↥(T ⊓ (LinearMap.ker (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) ⊓
    LinearMap.ker (prB (d₀ := d₀ + r) (d₁ := d₁) (m := m) (r := m))))

/-- **The exponents of the 4-block bound.** -/
theorem exps4 {H : Set (GPtV (d₀ + r) d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    finrank ℂ ((h0V hH).map (leadL (d₀ := d₀) (r := r))) = ex0L (lieAlg Ls hH) ∧
      ex2L (lieAlg Ls hH) =
        ex2 (lieAlg Ls hH) + finrank ℂ ↥(h0V hH ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) ∧
      ex0 (lieAlg Ls hH) =
        ex0L (lieAlg Ls hH) + finrank ℂ ↥(h0V hH ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) := by
  classical
  obtain ⟨S, hS, -, -, hgam⟩ := exists_subgroupV hH hc
  have hA := S.map_prA_tan
  rw [hS, hgam] at hA
  have hmap : (h0V hH).map (leadL (d₀ := d₀) (r := r)) =
      (lieAlg Ls hH).map (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m)) := by
    rw [h0V, ← hA, ← Submodule.map_comp]; rfl
  -- rank-nullity for `leadL` on `h₀`
  have hrn : finrank ℂ (h0V hH) = finrank ℂ ((h0V hH).map (leadL (d₀ := d₀) (r := r))) +
      finrank ℂ ↥(h0V hH ⊓ LinearMap.ker (leadL (d₀ := d₀) (r := r))) := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((leadL (d₀ := d₀) (r := r)).domRestrict (h0V hH))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
    exact h.symm
  obtain ⟨j, -, hj0, hj2⟩ := exists_jV S
  rw [hS] at hj0 hj2
  rw [hA] at hj0
  have h1 : finrank ℂ ((h0V hH).map (leadL (d₀ := d₀) (r := r))) = ex0L (lieAlg Ls hH) := by
    rw [hmap]; rfl
  have hX : finrank ℂ (h0V hH) = finrank ℂ ((lieAlg Ls hH).map
      (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m))) + j := hj0
  have hY : ex0L (lieAlg Ls hH) = finrank ℂ ((lieAlg Ls hH).map
      (prLead (d₀ := d₀) (r := r) (d₁ := d₁) (m := m))) := rfl
  have hZ : ex2L (lieAlg Ls hH) = ex2 (lieAlg Ls hH) + j := hj2
  rw [h1] at hrn
  refine ⟨h1, ?_, hrn⟩
  omega

/-- **Trailing degree and the 4-block grading.** -/
theorem fle4_of_trail {D₀ D₁ D₂ : ℕ} {P : MvPolynomial (Var (d₀ + r) d₁ m) ℂ}
    (hP : P ∈ FLE ℂ blk (Dfun D₀ D₁ D₂)) (hT : TrailDeg (d₀ := d₀) D₂ P) :
    P ∈ FLE ℂ (blk4 d₀) (D4f D₀ D₂ D₁ D₂) := by
  classical
  rw [StrongSix.M2.FLE, mem_restrictSupport_iff] at hP ⊢
  intro s hs b
  have h3 := fun b' => (bdeg4_le d₀ s b').trans (hP hs (b4to3 b'))
  cases b with
  | xl => simpa [b4to3, Dfun] using h3 .xl
  | yz => simpa [b4to3, Dfun] using h3 .yz
  | e k => simpa [b4to3, Dfun] using h3 (.e k)
  | xt =>
    refine le_trans ?_ (hT s hs)
    unfold StrongSix.M2.bdeg
    rw [← Finset.sum_filter]
    have himg : Finset.univ.filter (fun v : Var (d₀ + r) d₁ m => blk4 d₀ v = Blk4.xt) ⊆
        Finset.univ.image (fun i : Fin r => (Var.x (Fin.natAdd d₀ i) : Var (d₀ + r) d₁ m)) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      cases v with
      | x i =>
        rw [blk4_x] at hv
        have hi : d₀ ≤ (i : ℕ) := by
          by_contra h
          have h' : (i : ℕ) < d₀ := by omega
          simp [h'] at hv
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨(i : ℕ) - d₀, by omega⟩, by congr 1; ext; simp; omega⟩
      | y j => simp at hv
      | z j => simp at hv
      | e k c => simp at hv
    refine (Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => Nat.zero_le _).trans
      (le_of_eq ?_)
    rw [Finset.sum_image fun i _ i' _ h => by
      have := congrArg (fun v => match v with | Var.x a => (a : ℕ) | _ => 0) h
      exact Fin.ext (by simpa using this)]

/-- `∏ᵢ D(blk4 d₀ (x i)) = D_lead^{d₀} D_trail^r`. -/
theorem prod_blk4_x (D : Blk4 m → ℕ) :
    ∏ i : Fin (d₀ + r), D (blk4 d₀ (.x i : Var (d₀ + r) d₁ m)) = D .xl ^ d₀ * D .xt ^ r := by
  rw [Fin.prod_univ_add]
  congr 1
  · simp [blk4_x]
  · simp [blk4_x]

/-! ### The final arithmetic -/

/-- The constant of the 4-block estimate (`n = d₀ + r + d₁ + 2m`). -/
def CstV4 (d₀ r d₁ m : ℕ) : ℕ :=
  (d₀ + r + d₁ + 2 * m) ^ (d₀ + r + d₁ + 2 * m) * (d₀ ^ d₀ * (d₀ + r) ^ (d₀ + r) * d₁ ^ d₁) *
    2 ^ (d₀ + r + d₁ + 2 * m) * 48 ^ m * 3 ^ (d₀ + r + d₁ + 2 * m) *
    (d₀ + r + d₁ + 2 * m).factorial * 9 ^ (d₀ + r) * 18 ^ d₁ * 486 ^ m

theorem final_arith4 {ℓ e t₀ t₁ t₂ x₂ T nF nR k D₀ D₁ D₂ κ : ℕ} {deg0 degA degIG : ℤ}
    (hℓ : ℓ ≤ d₀ + r + d₁ + 2 * m) (he : e ≤ d₀ + r + d₁ + 2 * m)
    (hx₂ : x₂ ≤ d₀ + r + d₁ + 2 * m) (hκ : κ ≤ d₀ ^ d₀ * (d₀ + r) ^ (d₀ + r) * d₁ ^ d₁)
    (hT : T ^ ℓ ≤ ℓ ^ ℓ * (k + 1) ^ ℓ) (hF : nF ≤ nR) (_h0 : 0 ≤ deg0)
    (A1 : ((nR * (9 * D₀) ^ t₀ * (9 * D₁) ^ t₁ * (9 * D₂) ^ t₂ * e.factorial : ℕ) : ℤ) ≤
      ((κ * 2 ^ x₂ * 48 ^ m : ℕ) : ℤ) * (3 ^ e * deg0))
    (A2 : (((k + 1) ^ ℓ : ℕ) : ℤ) * deg0 ≤ degA) (A3 : degA ≤ degIG)
    (A4 : degIG ≤ (((d₀ + r + d₁ + 2 * m).factorial * ((9 * D₀) ^ d₀ * (9 * D₂) ^ r) *
      (2 * (9 * D₁)) ^ d₁ * ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 : ℕ) : ℤ)) :
    T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤
      CstV4 d₀ r d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) := by
  set n := d₀ + r + d₁ + 2 * m
  set X := (9 * D₀) ^ t₀ * (9 * D₁) ^ t₁ * (9 * D₂) ^ t₂
  set L := ℓ ^ ℓ
  set P := (k + 1) ^ ℓ
  have hDX : D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ X := by
    simp only [X]
    gcongr <;> omega
  have hfac : 1 ≤ e.factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)
  have s1 : T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ ≤ L * P * (nR * X * e.factorial) := by
    calc T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ = T ^ ℓ * nF * (D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂) := by
          ring
      _ ≤ (L * P) * nR * (X * e.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul hT hF) (hDX.trans (Nat.le_mul_of_pos_right _ hfac))
      _ = L * P * (nR * X * e.factorial) := by ring
  set κ' := κ * 2 ^ x₂ * 48 ^ m
  have s2 : ((L * P * (nR * X * e.factorial) : ℕ) : ℤ) ≤ (L : ℤ) * κ' * 3 ^ e * degIG := by
    have hA1 : ((nR * X * e.factorial : ℕ) : ℤ) ≤ (κ' : ℤ) * (3 ^ e * deg0) := by
      simpa [X, κ', mul_assoc] using A1
    calc ((L * P * (nR * X * e.factorial) : ℕ) : ℤ)
        = (L : ℤ) * P * ((nR * X * e.factorial : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (L : ℤ) * P * ((κ' : ℤ) * (3 ^ e * deg0)) := by gcongr
      _ = (L : ℤ) * κ' * 3 ^ e * ((P : ℤ) * deg0) := by ring
      _ ≤ (L : ℤ) * κ' * 3 ^ e * degA :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast A2) (by positivity)
      _ ≤ (L : ℤ) * κ' * 3 ^ e * degIG := by gcongr
  have s3 : (L : ℤ) * κ' * 3 ^ e * degIG ≤
      ((CstV4 d₀ r d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) : ℕ) : ℤ) := by
    have hL : L ≤ n ^ n := LSG.ME.pow_self_mono hℓ
    have h3e : 3 ^ e ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) he
    have h2t : 2 ^ x₂ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hx₂
    have hprod : ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 = 486 ^ m * D₂ ^ (2 * m) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul, ← mul_pow]
      congr 1; ring
    calc (L : ℤ) * κ' * 3 ^ e * degIG
        ≤ (L : ℤ) * κ' * 3 ^ e * (((d₀ + r + d₁ + 2 * m).factorial * ((9 * D₀) ^ d₀ *
            (9 * D₂) ^ r) * (2 * (9 * D₁)) ^ d₁ * ∏ _k : Fin m, 6 * (9 * D₂) ^ 2 : ℕ) : ℤ) := by
          gcongr
      _ = (((L * κ' * 3 ^ e) * ((d₀ + r + d₁ + 2 * m).factorial * ((9 * D₀) ^ d₀ *
            (9 * D₂) ^ r) * (2 * (9 * D₁)) ^ d₁ * ∏ _k : Fin m, 6 * (9 * D₂) ^ 2) : ℕ) : ℤ) := by
          push_cast; ring
      _ ≤ ((CstV4 d₀ r d₁ m * D₀ ^ d₀ * D₁ ^ d₁ * D₂ ^ (2 * m + r) : ℕ) : ℤ) := by
          apply Nat.cast_le.mpr
          have e1 : (2 * (9 * D₁)) ^ d₁ = 18 ^ d₁ * D₁ ^ d₁ := by
            rw [← mul_assoc, mul_pow]; norm_num
          rw [hprod, mul_pow, mul_pow, e1, CstV4]
          calc L * (κ * 2 ^ x₂ * 48 ^ m) * 3 ^ e * ((d₀ + r + d₁ + 2 * m).factorial *
                (9 ^ d₀ * D₀ ^ d₀ * (9 ^ r * D₂ ^ r)) * (18 ^ d₁ * D₁ ^ d₁) *
                (486 ^ m * D₂ ^ (2 * m)))
              = (L * κ * 2 ^ x₂ * 3 ^ e) * (48 ^ m * (d₀ + r + d₁ + 2 * m).factorial *
                  (9 ^ d₀ * 9 ^ r) * 18 ^ d₁ * 486 ^ m * D₀ ^ d₀ * D₁ ^ d₁ *
                  (D₂ ^ (2 * m) * D₂ ^ r)) := by ring
            _ ≤ (n ^ n * (d₀ ^ d₀ * (d₀ + r) ^ (d₀ + r) * d₁ ^ d₁) * 2 ^ n * 3 ^ n) *
                  (48 ^ m * (d₀ + r + d₁ + 2 * m).factorial * (9 ^ d₀ * 9 ^ r) * 18 ^ d₁ *
                    486 ^ m * D₀ ^ d₀ * D₁ ^ d₁ * (D₂ ^ (2 * m) * D₂ ^ r)) := by gcongr
            _ = _ := by rw [← pow_add, ← pow_add]; ring
  exact_mod_cast (show ((T ^ ℓ * nF * D₀ ^ t₀ * D₁ ^ t₁ * D₂ ^ t₂ : ℕ) : ℤ) ≤ _ from
    (Nat.cast_le.mpr s1).trans (s2.trans s3))

end

end LSG.MEV
