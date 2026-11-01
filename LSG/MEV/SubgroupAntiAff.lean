import Mathlib
import LSG.W88.StatementVec
import LSG.Weierstrass.Legendre

/-!
# Anti-affineness of `B^♮`: `dim_ℂ perTanId(t) = 2 dim_ℂ t`

For an abelian tangent `t ⊆ ℂ^m` (`IsAbelianTangent`: `t ∩ Λ` spans `t` over `ℝ`), the
`ℂ`-span of the periods `{(λ, η(λ)) : λ ∈ t ∩ Λ}` of `B^♮` has dimension exactly `2 dim t`
(**`finrank_perTanId`**): the periods of the universal vector extension span its whole Lie algebra.
This is the analytic form of `Hom(B^♮, G_a) = 0`: a proper subspace of `T(B^♮)` containing all
periods does not exist, so `B^♮` has no nontrivial vector-group quotient.

Proof.
* `ηR L : ℂ →ₗ[ℝ] ℂ`, the `ℝ`-linear extension of `η` from `Λ` (`ηR_of_mem`).
* **Legendre in bilinear form** (`pair_eq`): `z ηR(z′) − z′ ηR(z) = −i c_L Im(z̄ z′)` with
  `c_L = 2π s / Im(ω̄₁ ω₂) > 0` (`legC_pos`, `s = ±1` the sign in `legendre`).
* Upper bound: `perTanId t` is the `ℂ`-span of the `ℝ`-linear image `{(z, ηR z) : z ∈ t}`, whose real
  dimension is `2 dim t`.
* Lower bound: for an `ℝ`-basis `b ⊆ t ∩ Λ` of `t`, the vectors `(λ, η(λ))`, `λ ∈ b`, are
  `ℂ`-independent: pairing a relation `Σ cλ (λ, ηλ) = 0` against `(μ, ημ)` with
  `ω((z,w),(z′,w′)) = Σ z_k w′_k − z′_k w_k` gives `Σ cλ E(λ, μ) = 0`, `E(z, z′) = Σ c_k Im(z̄_k z′_k)`,
  and `E(x, i x) = Σ c_k |x_k|² > 0` for `x ≠ 0` in the complex space `t`.
-/

open Complex Module
open LSG.Weierstrass
open LSG.W88 (IsAbelianTangent)
open LSG.W88.Vec (perTanId etaV)

namespace LSG.MEV

noncomputable section

/-! ### One curve -/

section One

variable (L : PeriodPair)

/-- The `ℝ`-linear extension of `η` from the lattice. -/
def ηR : ℂ →ₗ[ℝ] ℂ := L.basis.constr ℝ ![eta L L.ω₁, eta L L.ω₂]

theorem ηR_apply (a b : ℝ) : ηR L ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
    a * eta L L.ω₁ + b * eta L L.ω₂ := by
  have h1 : ηR L L.ω₁ = eta L L.ω₁ := by
    conv_lhs => rw [← L.basis_zero]
    rw [ηR, Basis.constr_basis]; rfl
  have h2 : ηR L L.ω₂ = eta L L.ω₂ := by
    conv_lhs => rw [← L.basis_one]
    rw [ηR, Basis.constr_basis]; rfl
  rw [← Complex.real_smul, ← Complex.real_smul, map_add, map_smul, map_smul, h1, h2,
    Complex.real_smul, Complex.real_smul]

theorem ηR_of_mem {l : ℂ} (hl : l ∈ L.lattice) : ηR L l = eta L l := by
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have hp : (p : ℂ) * L.ω₁ ∈ L.lattice := by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem p L.ω₁_mem_lattice
  have hq : (q : ℂ) * L.ω₂ ∈ L.lattice := by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem q L.ω₂_mem_lattice
  have := ηR_apply L p q
  push_cast at this
  rw [this, eta_add L hp hq, eta_zsmul L L.ω₁_mem_lattice, eta_zsmul L L.ω₂_mem_lattice]

/-- The sign in Legendre's relation. -/
def legS : ℝ := if 0 < (L.ω₂ / L.ω₁).im then 1 else -1

/-- `Im(ω̄₁ ω₂)` (`≠ 0`, the signed covolume). -/
def legJ : ℝ := (starRingEnd ℂ L.ω₁ * L.ω₂).im

/-- The positive constant `c_L = 2π s / Im(ω̄₁ ω₂)`. -/
def legC : ℝ := 2 * Real.pi * legS L / legJ L

theorem im_div_eq : (L.ω₂ / L.ω₁).im = legJ L / Complex.normSq L.ω₁ := by
  rw [Complex.div_im, legJ, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem legJ_mul_legS_pos : 0 < legJ L * legS L := by
  have hω : L.ω₁ ≠ 0 := fun h => by
    have := L.indep.ne_zero 0
    simp [h] at this
  have hn : 0 < Complex.normSq L.ω₁ := Complex.normSq_pos.mpr hω
  have hJ : legJ L = (L.ω₂ / L.ω₁).im * Complex.normSq L.ω₁ := by
    rw [im_div_eq]; field_simp
  rw [legS, hJ]
  split_ifs with h
  · rw [mul_one]; positivity
  · have h' : (L.ω₂ / L.ω₁).im < 0 := lt_of_le_of_ne (not_lt.mp h) (im_div_ne_zero L)
    nlinarith

theorem legJ_ne_zero : legJ L ≠ 0 := fun h => by
  have := legJ_mul_legS_pos L
  rw [h, zero_mul] at this
  exact lt_irrefl 0 this

theorem legC_pos : 0 < legC L := by
  have h := legJ_mul_legS_pos L
  have hs : legS L * legS L = 1 := by unfold legS; split_ifs <;> norm_num
  have : legC L = 2 * Real.pi * (legS L * legS L) / (legJ L * legS L) := by
    rw [legC]; field_simp [legJ_ne_zero L]
  rw [this, hs]
  positivity

/-- **Legendre's relation in bilinear form.** -/
theorem pair_eq (z z' : ℂ) :
    z * ηR L z' - z' * ηR L z = -I * (legC L : ℂ) * ((starRingEnd ℂ z * z').im : ℂ) := by
  have hz := L.basis.sum_repr z
  have hz' := L.basis.sum_repr z'
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hz hz'
  set a := L.basis.repr z 0
  set b := L.basis.repr z 1
  set c := L.basis.repr z' 0
  set d := L.basis.repr z' 1
  rw [Complex.real_smul, Complex.real_smul] at hz hz'
  have hleg : eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = 2 * Real.pi * I * legS L := by
    rw [legendre, legS]; split_ifs <;> push_cast <;> ring
  have him : (starRingEnd ℂ z * z').im = (a * d - b * c) * legJ L := by
    rw [← hz, ← hz', legJ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.add_im,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [him, ← hz, ← hz', ηR_apply, ηR_apply]
  have hJ : legJ L ≠ 0 := legJ_ne_zero L
  have hC : (legC L : ℂ) * (legJ L : ℂ) = 2 * Real.pi * legS L := by
    rw [legC]; push_cast
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hJ)
  push_cast
  linear_combination (I * ((a : ℂ) * d - b * c)) * hC - ((a : ℂ) * d - b * c) * hleg

end One

/-! ### Several curves -/

variable {m : ℕ} (Ls : Fin m → PeriodPair)

/-- `ηR` coordinatewise. -/
def ηRV : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ) := LinearMap.pi fun k => (ηR (Ls k)).comp (LinearMap.proj k)

theorem ηRV_apply (z : Fin m → ℂ) (k : Fin m) : ηRV Ls z k = ηR (Ls k) (z k) := rfl

theorem ηRV_of_mem {z : Fin m → ℂ} (hz : ∀ k, z k ∈ (Ls k).lattice) : ηRV Ls z = etaV Ls z :=
  funext fun k => ηR_of_mem _ (hz k)

/-- The real form `E(z, z′) = Σ c_k Im(z̄_k z′_k)`. -/
def EV : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z z' => ∑ k, legC (Ls k) * (starRingEnd ℂ (z k) * z' k).im)
    (fun z₁ z₂ z' => by
      simp only [Pi.add_apply, map_add, add_mul, Complex.add_im, mul_add, Finset.sum_add_distrib])
    (fun r z z' => by
      simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, Complex.im_ofReal_mul]; ring)
    (fun z z₁ z₂ => by
      simp only [Pi.add_apply, mul_add, Complex.add_im, Finset.sum_add_distrib])
    (fun r z z' => by
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, Complex.im_ofReal_mul]; ring)

theorem EV_apply (z z' : Fin m → ℂ) :
    EV Ls z z' = ∑ k, legC (Ls k) * (starRingEnd ℂ (z k) * z' k).im := rfl

theorem EV_I_self (x : Fin m → ℂ) : EV Ls x (I • x) = ∑ k, legC (Ls k) * Complex.normSq (x k) := by
  rw [EV_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

theorem eq_zero_of_EV_I_self {x : Fin m → ℂ} (h : EV Ls x (I • x) = 0) : x = 0 := by
  rw [EV_I_self] at h
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ legC (Ls k) * Complex.normSq (x k) := fun k _ =>
    mul_nonneg (legC_pos _).le (Complex.normSq_nonneg _)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  funext k
  have hk := this k (Finset.mem_univ k)
  rcases mul_eq_zero.mp hk with h0 | h0
  · exact absurd h0 (legC_pos _).ne'
  · exact Complex.normSq_eq_zero.mp h0

/-- The pairing `ω(p, q) = Σ p₁ₖ q₂ₖ − q₁ₖ p₂ₖ`, linear in `p`. -/
def omegaV (q : (Fin m → ℂ) × (Fin m → ℂ)) : ((Fin m → ℂ) × (Fin m → ℂ)) →ₗ[ℂ] ℂ where
  toFun p := ∑ k, (p.1 k * q.2 k - q.1 k * p.2 k)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem omegaV_graph (z z' : Fin m → ℂ) :
    omegaV (z', ηRV Ls z') (z, ηRV Ls z) = -I * (EV Ls z z' : ℂ) := by
  simp only [omegaV, LinearMap.coe_mk, AddHom.coe_mk, ηRV_apply, pair_eq, EV_apply]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The dimension count -/

/-- `z ↦ (z, ηR z)`. -/
def graphR : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ) × (Fin m → ℂ) := LinearMap.prod LinearMap.id (ηRV Ls)

/-- **Anti-affineness of `B^♮`**: `dim_ℂ perTanId(t) = 2 dim_ℂ t` for an abelian tangent `t`. -/
theorem finrank_perTanId {t : Submodule ℂ (Fin m → ℂ)} (ht : IsAbelianTangent Ls t) :
    finrank ℂ (perTanId Ls t) = 2 * finrank ℂ t := by
  classical
  set S := {z : Fin m → ℂ | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice}
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  have hbt : Submodule.span ℝ b = t.restrictScalars ℝ := by rw [hbspan, ht]
  have hfin : b.Finite := hbli.setFinite
  let _ : Fintype b := hfin.fintype
  set P : b → (Fin m → ℂ) × (Fin m → ℂ) := fun l => graphR Ls l
  have hP : ∀ l : b, P l = ((l : Fin m → ℂ), etaV Ls l) := fun l => by
    change ((l : Fin m → ℂ), ηRV Ls (l : Fin m → ℂ)) = _
    rw [ηRV_of_mem Ls (hbS l.2).2]
  -- `card b = 2 dim t`
  have hcard : Fintype.card b = 2 * finrank ℂ t := by
    have h1 := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbt] at h1
    rw [← h1, ← finrank_real_of_complex]
    rfl
  -- upper bound
  have hup : perTanId Ls t ≤ Submodule.span ℂ (Set.range P) := by
    rw [perTanId, Submodule.span_le]
    rintro ⟨l, s⟩ ⟨hl, hΛ, hs⟩
    simp only at hs
    have hlb : l ∈ Submodule.span ℝ b := by rw [hbt]; exact hl
    have : graphR Ls l ∈ Submodule.span ℝ (Set.range P) := by
      have := Submodule.mem_map_of_mem (f := graphR Ls) hlb
      have hR : Set.range P = graphR Ls '' b := by ext y; simp [P]
      rwa [Submodule.map_span, ← hR] at this
    have hgl : graphR Ls l = (l, s) := by
      change (l, ηRV Ls l) = (l, s)
      rw [hs, ηRV_of_mem Ls hΛ]
    rw [← hgl]
    exact Submodule.span_le_restrictScalars ℝ ℂ _ this
  -- lower bound: `P` is `ℂ`-independent
  have hli : LinearIndependent ℂ P := by
    rw [linearIndependent_iff']
    intro s g hg
    have hE : ∀ μ : b, ∑ i ∈ s, g i * (EV Ls (i : Fin m → ℂ) μ : ℂ) = 0 := by
      intro μ
      have := congrArg (omegaV (P μ)) hg
      rw [map_sum, map_zero] at this
      have h2 : ∀ i ∈ s, omegaV (P μ) (g i • P i) = -I * (g i * (EV Ls (i : Fin m → ℂ) μ : ℂ)) :=
        fun i _ => by
          rw [map_smul, smul_eq_mul]
          change g i * omegaV ((μ : Fin m → ℂ), ηRV Ls μ) ((i : Fin m → ℂ), ηRV Ls i) = _
          rw [omegaV_graph]; ring
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at this
      exact (mul_eq_zero.mp this).resolve_left (by simp [Complex.I_ne_zero])
    have hpart : ∀ f : ℂ → ℝ, (∀ i ∈ s, ∀ μ : b, True) →
        (∀ μ : b, ∑ i ∈ s, f (g i) * EV Ls (i : Fin m → ℂ) μ = 0) → ∀ i ∈ s, f (g i) = 0 := by
      intro f _ hf
      set x : Fin m → ℂ := ∑ i ∈ s, f (g i) • (i : Fin m → ℂ)
      have hx0 : ∀ y ∈ Submodule.span ℝ b, EV Ls x y = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          have := hf ⟨y, hy⟩
          rw [show x = ∑ i ∈ s, f (g i) • (i : Fin m → ℂ) from rfl, map_sum]
          simpa [LinearMap.smul_apply] using this
        | zero => simp
        | add y z _ _ py pz => rw [map_add, py, pz, add_zero]
        | smul a y _ py => rw [map_smul, py, smul_zero]
      have hxt : x ∈ t := by
        refine t.sum_mem fun i _ => ?_
        rw [← Complex.coe_smul]
        exact t.smul_mem _ (hbS i.2).1
      have hIx : I • x ∈ Submodule.span ℝ b := by rw [hbt]; exact t.smul_mem I hxt
      have hx : x = 0 := eq_zero_of_EV_I_self Ls (hx0 _ hIx)
      exact linearIndependent_iff'.mp hbli s (fun i => f (g i)) hx
    have hre := hpart Complex.re (fun _ _ _ => trivial) fun μ => by
      have := congrArg Complex.re (hE μ)
      simpa [Complex.mul_re] using this
    have him := hpart Complex.im (fun _ _ _ => trivial) fun μ => by
      have := congrArg Complex.im (hE μ)
      simpa [Complex.mul_im] using this
    intro i hi
    exact Complex.ext (hre i hi) (him i hi)
  have hlow : Submodule.span ℂ (Set.range P) ≤ perTanId Ls t := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [hP]
    exact Submodule.subset_span ⟨(hbS l.2).1, (hbS l.2).2, rfl⟩
  have heq : perTanId Ls t = Submodule.span ℂ (Set.range P) := le_antisymm hup hlow
  rw [heq, finrank_span_eq_card hli, hcard]

end

end LSG.MEV
