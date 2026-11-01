/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.AuxFunA.Package
import LSG.AuxFun.LemmaUId

/-!
# A5.5a: Lemma U, the factorisation on a line through a lattice point (`STAGE_A5.md` D2)

At a point `t` whose block parts are periods in `lat` (all points of `Y(S)` are such), quasi-periodicity gives
`θ_k(t_k + s v_k) = κ_k e^{λ_k s} θ_k(s v_k)`, so on `θ_{i₀}(s v_k) ≠ 0`

  `Ψ(t + s v) = u(s) · F(s)`, `u(s) = Π_k (κ_k e^{λ_k s} θ_{k,i₀}(s v_k))^D`, `F(s) = Σ_l p_l Π_f g_f(s)^{n_{l,f}}`

with the basic factors `g_f` (`gA`): `t_i + v_i s` (`G_a`), `e^{t_j} e^{v_j s}` (`G_m`) and the ratios
`θ_{is j}(s v_k)/θ_{i₀}(s v_k)` (blocks), and `n_l = (μs l).rexp` (`PsiA_line_eq`).

The Taylor coefficients of the ratios at `0` along algebraic directions are algebraic of controlled size: this is the
block's **Taylor package** `AbBlockTay b ι` (for the `A`-block: `ks_chart4F` at `z₀ = 0`). With it, `F` has
`KS`-controlled Taylor coefficients (`ks_FA`, through `LSG.Aux.KS.poly`).
-/

open Complex Finset Module LSG.W88

noncomputable section

namespace LSG.AuxA

open LSG.MEB LSG.Aux

variable {K : Type*} [Field K] [NumberField K]

/-- **The Taylor package of a block** over a number field `K ⊂ ℂ` (via `ι`): along any direction with coordinates
of size `(H_c, d_c)`, the ratios `s ↦ θ_{is j}(s v)/θ_{i₀}(s v)` have Taylor coefficients of size
`(A B^j, e δ^j j!)` with `B = c_B H_c` and `δ = d_c δ₀`. -/
structure AbBlockTay (b : AbBlock) (ι : K →+* ℂ) where
  A : ℝ
  one_le_A : 1 ≤ A
  cB : ℝ
  one_le_cB : 1 ≤ cB
  E : ℕ
  one_le_E : 1 ≤ E
  δ : ℕ
  one_le_δ : 1 ≤ δ
  ks : ∀ (v : Fin b.g → ℂ) (Hc : ℝ) (dc : ℕ), 1 ≤ Hc → (∀ j, Sz ι Hc dc (v j)) →
    ∀ j, KS ι A (cB * Hc) E (dc * δ) (fun s => ratioMap b (s • v) j)

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock} {D : ℕ}

/-- **The basic factors** on the line `s ↦ t + s v`. -/
def gA (t v : Tan d₀ d₁ B) : RVarA d₀ d₁ B → ℂ → ℂ
  | .inl i => fun s => t.1 i + v.1 i * s
  | .inr (.inl j) => fun s => Complex.exp (t.2.1 j) * Complex.exp (v.2.1 j * s)
  | .inr (.inr ⟨k, j⟩) => fun s => ratioMap (B k) (s • v.2.2 k) j

/-- **The normalised function** `F(s) = Σ_l p_l Π_f g_f(s)^{n_{l,f}}`. -/
def FA {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (t v : Tan d₀ d₁ B) (s : ℂ) : ℂ :=
  ∑ l, (p l : ℂ) * ∏ f, gA t v f s ^ (μs l).rexp f

/-- **The unit** `u(s) = Π_k (κ_k e^{λ_k s} θ_{k,i₀}(s v_k))^D`. -/
def uA (D : ℕ) (κ lam : Fin m → ℂ) (v : Tan d₀ d₁ B) (s : ℂ) : ℂ :=
  ∏ k, (κ k * Complex.exp (lam k * s) * (B k).θ (s • v.2.2 k) (B k).i₀) ^ D

lemma line_x (t v : Tan d₀ d₁ B) (s : ℂ) (i : Fin d₀) : (t + s • v).1 i = t.1 i + v.1 i * s := by
  simp [mul_comm]

lemma line_b (t v : Tan d₀ d₁ B) (s : ℂ) (j : Fin d₁) :
    Complex.exp ((t + s • v).2.1 j) = Complex.exp (t.2.1 j) * Complex.exp (v.2.1 j * s) := by
  rw [← Complex.exp_add]; congr 1; simp [mul_comm]

lemma line_z (t v : Tan d₀ d₁ B) (s : ℂ) (k : Fin m) : (t + s • v).2.2 k = t.2.2 k + s • v.2.2 k := rfl

/-- **The factorisation** `Ψ(t + s v) = u(s) F(s)`. -/
theorem PsiA_line_eq {L : ℕ} (μs : Fin L → MonoA d₀ d₁ B D) (p : Fin L → ℤ) (t v : Tan d₀ d₁ B)
    (κ lam : Fin m → ℂ)
    (hθ : ∀ k s, (B k).θ (t.2.2 k + s • v.2.2 k) = (κ k * Complex.exp (lam k * s)) • (B k).θ (s • v.2.2 k))
    (s : ℂ) (hs : ∀ k, (B k).θ (s • v.2.2 k) (B k).i₀ ≠ 0) :
    PsiA μs p (t + s • v) = uA D κ lam v s * FA μs p t v s := by
  unfold PsiA FA
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  have hblk : ∀ k, ∏ c, (B k).θ ((t + s • v).2.2 k) (fidx (B k) c) ^ (μs l).γ k c =
      (κ k * Complex.exp (lam k * s) * (B k).θ (s • v.2.2 k) (B k).i₀) ^ D *
        ∏ j, ratioMap (B k) (s • v.2.2 k) j ^ (μs l).γ k j.succ := by
    intro k
    rw [line_z, hθ k s]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, (μs l).hγ k]
    rw [(μs l).block_eq k _ (hs k)]
    ring
  unfold MonoA.eval
  simp only [line_x, line_b, hblk]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [gA, MonoA.rexp, uA, prod_mul_distrib]
  ring

/-! ### Sizes of the Taylor coefficients of `F` -/

/-- The size of the basic factors. -/
def AfA (Ht He : ℝ) (Tay : ∀ k, AbBlockTay (B k) (ι : K →+* ℂ)) : RVarA d₀ d₁ B → ℝ
  | .inl _ => max 1 Ht
  | .inr (.inl _) => max 1 He
  | .inr (.inr ⟨k, _⟩) => (Tay k).A

/-- The denominators of the basic factors. -/
def efA (dt dv de : ℕ) (Tay : ∀ k, AbBlockTay (B k) (ι : K →+* ℂ)) : RVarA d₀ d₁ B → ℕ
  | .inl _ => dt * dv
  | .inr (.inl _) => de
  | .inr (.inr ⟨k, _⟩) => (Tay k).E

/-- The degree bounds of the basic factors. -/
def NfA (A₀ A₁ D : ℕ) : RVarA d₀ d₁ B → ℕ
  | .inl _ => A₀
  | .inr (.inl _) => A₁
  | .inr (.inr _) => D

/-- The common `B`. -/
def cBm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) : ℝ := 1 + ∑ k, (Tay k).cB

/-- The common `δ` factor. -/
def δm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) : ℕ := ∏ k, (Tay k).δ

lemma one_le_cBm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) : 1 ≤ cBm Tay := by
  have := sum_nonneg fun k (_ : k ∈ univ) => (zero_le_one.trans (Tay k).one_le_cB)
  unfold cBm; linarith

lemma cB_le_cBm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) (k : Fin m) : (Tay k).cB ≤ cBm Tay := by
  have := single_le_sum (f := fun k => (Tay k).cB) (fun k _ => zero_le_one.trans (Tay k).one_le_cB)
    (mem_univ k)
  unfold cBm; linarith

lemma one_le_δm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) : 1 ≤ δm Tay :=
  Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun k _ => by have := (Tay k).one_le_δ; omega)

lemma δ_dvd_δm {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) (k : Fin m) : (Tay k).δ ∣ δm Tay :=
  dvd_prod_of_mem _ (mem_univ k)

/-- **Sizes of the Taylor coefficients of `F`.** -/
theorem ks_FA {ι : K →+* ℂ} (Tay : ∀ k, AbBlockTay (B k) ι) {L A₀ A₁ : ℕ} (μs : Fin L → MonoA d₀ d₁ B D)
    (p : Fin L → ℤ) (hα : ∀ l i, (μs l).α i ≤ A₀) (hβ : ∀ l j, (μs l).β j ≤ A₁)
    (t v : Tan d₀ d₁ B) {Ht He Hv : ℝ} {dt de dv : ℕ} (hHv : 1 ≤ Hv)
    (ht : ∀ i, Sz ι Ht dt (t.1 i)) (he : ∀ j, Sz ι He de (Complex.exp (t.2.1 j)))
    (hv0 : ∀ i, Sz ι Hv dv (v.1 i)) (hv1 : ∀ j, Sz ι Hv dv (v.2.1 j))
    (hv2 : ∀ k j, Sz ι Hv dv (v.2.2 k j)) :
    KS ι ((∑ l, |(p l : ℝ)|) * (2 ^ (∑ f, NfA (d₀ := d₀) (d₁ := d₁) (B := B) A₀ A₁ D f) *
        ∏ f, AfA (d₀ := d₀) (d₁ := d₁) Ht He Tay f ^ NfA (d₀ := d₀) (d₁ := d₁) (B := B) A₀ A₁ D f))
      (2 * (cBm Tay * Hv)) (∏ f, efA (d₀ := d₀) (d₁ := d₁) dt dv de Tay f ^ NfA (d₀ := d₀) (d₁ := d₁) (B := B) A₀ A₁ D f)
      (dv * δm Tay) (FA μs p t v) := by
  have hB0 : 0 ≤ cBm Tay * Hv := by have := one_le_cBm Tay; positivity
  have hHvB : Hv ≤ cBm Tay * Hv := le_mul_of_one_le_left (by linarith) (one_le_cBm Tay)
  have hg : ∀ f, KS ι (AfA Ht He Tay f) (cBm Tay * Hv) (efA dt dv de Tay f) (dv * δm Tay) (gA t v f) := by
    intro f
    rcases f with i | j | ⟨k, j⟩
    · refine ks_lin ((ht i).mono (le_max_right _ _) (Dvd.intro dv rfl)) ?_ hB0
      refine (hv0 i).mono ?_ (Dvd.intro_left dt rfl)
      exact hHvB.trans (le_mul_of_one_le_left hB0 (le_max_left _ _))
    · refine (ks_expm ((he j).mono_le (le_max_right _ _)) (hv1 j)).mono le_rfl
        (zero_le_one.trans hHv) hHvB dvd_rfl (Dvd.intro _ rfl)
    · have h := (Tay k).ks (v.2.2 k) Hv dv hHv (hv2 k) j
      refine h.mono le_rfl (by have := (Tay k).one_le_cB; positivity)
        (mul_le_mul_of_nonneg_right (cB_le_cBm Tay k) (zero_le_one.trans hHv)) dvd_rfl
        (mul_dvd_mul_left dv (δ_dvd_δm Tay k))
  have hA : ∀ f, 1 ≤ AfA (d₀ := d₀) (d₁ := d₁) Ht He Tay f := by
    intro f
    rcases f with i | j | ⟨k, j⟩
    · exact le_max_left _ _
    · exact le_max_left _ _
    · exact (Tay k).one_le_A
  exact KS.poly hB0 hg hA p (fun l => (μs l).rexp) (NfA A₀ A₁ D) fun l f => by
    rcases f with i | j | ⟨k, j⟩
    · exact hα l i
    · exact hβ l j
    · have := (μs l).hγ k
      rw [Fin.sum_univ_succ] at this
      have hle := single_le_sum (f := fun j : Fin (B k).g => (μs l).γ k j.succ) (fun _ _ => Nat.zero_le _)
        (mem_univ j)
      simp only [MonoA.rexp, NfA]; omega

end LSG.AuxA
