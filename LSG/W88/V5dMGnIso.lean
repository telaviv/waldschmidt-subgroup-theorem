/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dIso
import LSG.W88.MStarCopyMGn
import LSG.CM.Kappa
import LSG.CM.Block

/-!
# The isogeny `G_m^{2n} × (E^r)^♮_{bᵀ} → G_m^{2n} × Q''` behind `gmMGn`, `gmMGnK`

For a CM lattice `L = ω ℤ[α]` (lean_mstar's `CMLattice`, copied) and an adapted basis `θ = (b_k, α
b_k)` of `K ⊇ ℚ(α)` (`n = 2r`), lean_mstar's `Q'' = (E^♮)^n / U` has tangent space `Qn = ℂ^n / Wphi
× ℂ`. We show (`Wphi_eq_ker`) that `Wphi = ℂ·ker φ` is the kernel of `π(v)_k = v_{(k,0)} + ᾱ
v_{(k,1)}` (the vectors `ᾱ e_{(k,0)} − e_{(k,1)}` lie in `ker φ`, and on `k^n ∩ ker π` the form `φ`
is `Σ_k b_k (π v)‾_k`, injective by `ℚ`-independence of `θ`). So `ℂ^n / Wphi ≅ ℂ^r` and `Q''` is
isogenous to the class-`𝒞` group `(E^r)^♮` pushed out along `bᵀ` (`M = mgM b`, curves `mgLs L`);
`mgIota : TanV 0 (2n) r 1 ≃ Qn-model`.

Also: the CM data of `L` under `KappaOneZero` (`CMLat.cmD`, `CMLat.eta_one_eq`) and
`d₂ = finrank Qn = r + 1` (`finrank_Qn`). Generators and subgroups: `LSG.W88.V5dMGnGen`.
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy

/-! ### CM facts for a `CMLattice` -/

namespace CMLat

variable (L : CMLattice)

lemma conj_α : starRingEnd ℂ L.α = L.q - L.α := by
  have h1 := L.hquad
  have h2 : (starRingEnd ℂ L.α) ^ 2 = L.p + L.q * starRingEnd ℂ L.α := by
    have := congrArg (starRingEnd ℂ) h1
    simpa [map_pow, map_add, map_mul, Complex.conj_ofReal] using this
  have hne : L.α - starRingEnd ℂ L.α ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith [L.him]
  have : (L.α - starRingEnd ℂ L.α) * (L.α + starRingEnd ℂ L.α - L.q) = 0 := by
    linear_combination h1 - h2
  have h3 := (mul_eq_zero.mp this).resolve_left hne
  linear_combination h3

lemma isAlgebraic_α : IsAlgebraic ℚ L.α := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C L.q * Polynomial.X - Polynomial.C L.p, ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp at this
  · simp [L.hquad]

lemma conj_mem_kSet {z : ℂ} (hz : z ∈ kSet L.α) : starRingEnd ℂ z ∈ kSet L.α := by
  obtain ⟨u, v, rfl⟩ := hz
  refine ⟨u + v * L.q, -v, ?_⟩
  simp only [map_add, map_mul, map_ratCast, conj_α]; push_cast; ring

lemma conj_mul_mem_kSet {z : ℂ} (hz : z ∈ kSet L.α) : starRingEnd ℂ L.α * z ∈ kSet L.α := by
  obtain ⟨u, v, rfl⟩ := hz
  refine ⟨L.q * u - v * L.p, -u, ?_⟩
  rw [conj_α]; push_cast
  linear_combination (-(v : ℂ)) * L.hquad

lemma add_mem_kSet {z w : ℂ} (hz : z ∈ kSet L.α) (hw : w ∈ kSet L.α) : z + w ∈ kSet L.α := by
  obtain ⟨u, v, rfl⟩ := hz
  obtain ⟨u', v', rfl⟩ := hw
  exact ⟨u + u', v + v', by push_cast; ring⟩

/-- `κ₁ = 0` gives CM data (`αΛ = Λ`, `ᾱ = α⁻¹`). -/
lemma cmD (hκ : KappaOneZero L) : CMData L.pp L.α :=
  cmData_of_zeta L.pp (by rw [L.hω₂, L.hω₁]) L.him (isAlgebraic_α L) fun z => hκ z

/-- `η(ω) = η₀` (Legendre twice). -/
lemma eta_one_eq (hκ : KappaOneZero L) : eta L.pp L.pp.ω₁ = L.η₀ := by
  have hd := cmD L hκ
  have h1 := hd.eta_one_mul
  have h2 := L.legendre
  rw [← hd.conj_eq] at h1
  have hne : L.ω * (L.α - starRingEnd ℂ L.α) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [← L.hω₁]; exact ω₁_ne_zero _
    · rw [hd.conj_eq]; exact hd.ne_inv
  rw [← L.hω₁] at h2 hne
  apply mul_right_cancel₀ hne
  linear_combination h1 - h2

end CMLat

/-! ### The base projection `π` and `Wphi = ker π` -/

variable {r : ℕ}

/-- `π(v)_k = v_{(k,0)} + ᾱ v_{(k,1)}`. -/
noncomputable def piB (α : ℂ) : (Fin r × Fin 2 → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun v k := v (k, 0) + starRingEnd ℂ α * v (k, 1)
  map_add' u v := by funext k; simp; ring
  map_smul' c v := by funext k; simp; ring

lemma piB_apply (α : ℂ) (v : Fin r × Fin 2 → ℂ) (k : Fin r) :
    piB α v k = v (k, 0) + starRingEnd ℂ α * v (k, 1) := rfl

/-- `z ↦ Σ z_k e_{(k,0)}`. -/
noncomputable def inclB : (Fin r → ℂ) →ₗ[ℂ] (Fin r × Fin 2 → ℂ) where
  toFun z j := if j.2 = 0 then z j.1 else 0
  map_add' u v := by funext j; split_ifs <;> simp [*]
  map_smul' c v := by funext j; split_ifs <;> simp [*]

lemma piB_inclB (α : ℂ) (z : Fin r → ℂ) : piB α (inclB z) = z := by
  funext k; simp [piB_apply, inclB]

lemma piB_single (α : ℂ) (j : Fin r × Fin 2) (c : ℂ) :
    piB α (Pi.single j c) = Pi.single j.1 ((if j.2 = 0 then 1 else starRingEnd ℂ α) * c) := by
  funext k
  obtain ⟨k₀, i₀⟩ := j
  rw [piB_apply]
  by_cases hk : k = k₀
  · subst hk
    fin_cases i₀ <;> simp
  · simp [hk]

variable (L : CMLattice) (b : Fin r → ℂ)

/-- `θ_{(k,i)} = b_k · conj(γ_i)`, `γ = (1, ᾱ)`. -/
lemma theta_eq (j : Fin r × Fin 2) :
    theta L.α b j = b j.1 * starRingEnd ℂ (if j.2 = 0 then 1 else starRingEnd ℂ L.α) := by
  unfold theta
  split_ifs <;> simp [mul_comm]

/-- `φ(v) = Σ_k b_k conj(π v)_k`. -/
lemma phi_eq (v : Fin r × Fin 2 → ℂ) :
    ∑ j, theta L.α b j * starRingEnd ℂ (v j) = ∑ k, b k * starRingEnd ℂ (piB L.α v k) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.sum_univ_two, theta, piB_apply, map_add, map_mul, Complex.conj_conj]
  simp; ring

/-- The vectors `ᾱ e_{(k,0)} − e_{(k,1)}` lie in `ker φ`. -/
lemma u_mem (k : Fin r) :
    (Pi.single (k, 0) (starRingEnd ℂ L.α) - Pi.single (k, 1) 1 : Fin r × Fin 2 → ℂ) ∈ Wphi L b := by
  refine Submodule.subset_span ⟨fun j => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.single_apply]
    rw [CMLat.conj_α]
    by_cases h1 : j = (k, 0)
    · subst h1; exact ⟨L.q, -1, by simp; ring⟩
    · by_cases h2 : j = (k, 1)
      · subst h2; exact ⟨-1, 0, by simp⟩
      · exact ⟨0, 0, by simp [h1, h2]⟩
  · rw [phi_eq]
    refine Finset.sum_eq_zero fun k' _ => ?_
    have : piB L.α (Pi.single (k, 0) (starRingEnd ℂ L.α) - Pi.single (k, 1) 1) k' = 0 := by
      rw [map_sub, piB_single, piB_single]
      simp
    rw [this, map_zero, mul_zero]

/-- **`Wphi = ker π`.** -/
theorem Wphi_eq_ker (hb : IsAdaptedFieldBasis L.α b) :
    Wphi L b = LinearMap.ker (piB (r := r) L.α) := by
  apply le_antisymm
  · rw [Wphi, Submodule.span_le]
    rintro v ⟨hk, hφ⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    set c := piB L.α v
    have hc : ∀ k, starRingEnd ℂ (c k) ∈ kSet L.α := fun k =>
      CMLat.conj_mem_kSet L (CMLat.add_mem_kSet L (hk _) (CMLat.conj_mul_mem_kSet L (hk _)))
    choose x y hxy using hc
    rw [phi_eq] at hφ
    let co : Fin r × Fin 2 → ℚ := fun j => if j.2 = 0 then x j.1 else y j.1
    have hsum : ∑ j, co j • theta L.α b j = 0 := by
      rw [← hφ, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e := hxy k
      simp only [c] at e
      rw [e]
      simp only [Fin.sum_univ_two, co, theta, Rat.smul_def]
      simp; ring
    have h0 := Fintype.linearIndependent_iff.mp hb.indep co hsum
    funext k
    have hx : x k = 0 := by simpa [co] using h0 (k, 0)
    have hy : y k = 0 := by simpa [co] using h0 (k, 1)
    have := hxy k
    rw [hx, hy] at this
    simpa using this
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv' : ∀ k, v (k, 0) = -(starRingEnd ℂ L.α * v (k, 1)) := fun k => by
      have := congrFun hv k
      rw [piB_apply, Pi.zero_apply] at this
      linear_combination this
    have : v = ∑ k, (-v (k, 1)) •
        (Pi.single (k, 0) (starRingEnd ℂ L.α) - Pi.single (k, 1) 1 : Fin r × Fin 2 → ℂ) := by
      funext j
      obtain ⟨k, i⟩ := j
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · fin_cases i
        · simp [hv' k, mul_comm]
        · simp
      · intro k' _ hk'
        simp [Ne.symm hk']
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (u_mem L b k)

/-! ### `ℂ^n / Wphi ≅ ℂ^r` -/

variable (hb : IsAdaptedFieldBasis L.α b)

/-- `[v] ↦ π(v)`. -/
noncomputable def qPi : ((Fin r × Fin 2 → ℂ) ⧸ Wphi L b) →ₗ[ℂ] (Fin r → ℂ) :=
  (Wphi L b).liftQ (piB L.α) (Wphi_eq_ker L b hb).le

lemma qPi_mk (v : Fin r × Fin 2 → ℂ) : qPi L b hb (Submodule.Quotient.mk v) = piB L.α v := rfl

lemma mk_inclB_qPi (q : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b) :
    Submodule.Quotient.mk (inclB (qPi L b hb q)) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    rw [qPi_mk, Submodule.Quotient.eq, Wphi_eq_ker L b hb, LinearMap.mem_ker, map_sub,
      piB_inclB, sub_self]

/-- `ℂ^n / Wphi ≃ ℂ^r`. -/
noncomputable def qE : ((Fin r × Fin 2 → ℂ) ⧸ Wphi L b) ≃ₗ[ℂ] (Fin r → ℂ) where
  toFun := qPi L b hb
  invFun z := Submodule.Quotient.mk (inclB z)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := mk_inclB_qPi L b hb
  right_inv z := by rw [qPi_mk, piB_inclB]

include hb in
lemma finrank_Qn : finrank ℂ (Qn L b) = r + 1 := by
  rw [Module.finrank_prod, (qE L b hb).finrank_eq]; simp

/-! ### The toric coordinates -/

/-- `n = |Fin r × Fin 2|`. -/
abbrev nI (r : ℕ) : ℕ := Fintype.card (Fin r × Fin 2)

/-- `Fin (2n) ≃ ι ⊕ ι`. -/
noncomputable def tE (r : ℕ) : Fin (2 * nI r) ≃ (Fin r × Fin 2) ⊕ (Fin r × Fin 2) :=
  (finCongr (two_mul _)).trans (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm))

/-- `ℂ^{2n} ≃ ℂ^ι × ℂ^ι`. -/
noncomputable def torL (r : ℕ) :
    (Fin (2 * nI r) → ℂ) ≃ₗ[ℂ] (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) where
  toFun x := (fun j => x ((tE r).symm (Sum.inl j)), fun j => x ((tE r).symm (Sum.inr j)))
  invFun p i := Sum.elim p.1 p.2 (tE r i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    change Sum.elim _ _ (tE r i) = x i
    rcases h : tE r i with j | j
    · change x ((tE r).symm (Sum.inl j)) = x i
      rw [← h, Equiv.symm_apply_apply]
    · change x ((tE r).symm (Sum.inr j)) = x i
      rw [← h, Equiv.symm_apply_apply]
  right_inv p := by ext j <;> simp

lemma torL_symm_apply (p : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ)) (i : Fin (2 * nI r)) :
    (torL r).symm p i = Sum.elim p.1 p.2 (tE r i) := rfl

/-- The `ℚ`-version of `torL`. -/
noncomputable def torLQ (r : ℕ) :
    (Fin (2 * nI r) → ℚ) →ₗ[ℚ] (Fin r × Fin 2 → ℚ) × (Fin r × Fin 2 → ℚ) where
  toFun x := (fun j => x ((tE r).symm (Sum.inl j)), fun j => x ((tE r).symm (Sum.inr j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### The class-`𝒞` group and `ι` -/

/-- The curves `E^r`. -/
abbrev mgLs (L : CMLattice) (r : ℕ) : Fin r → PeriodPair := fun _ => L.pp

/-- `M = bᵀ`. -/
def mgM (b : Fin r → ℂ) : Matrix (Fin 1) (Fin r) ℂ := fun _ k => b k

lemma mgM_mulVec (x : Fin r → ℂ) : (mgM b).mulVec x 0 = ∑ k, b k * x k := rfl

/-- **`ι : TanV 0 (2n) r 1 ≃ T(G_m^{2n} × Q'')`**, `(a, x, z, s) ↦ (x, ([incl z], s))`. -/
noncomputable def mgIota : TanV 0 (2 * nI r) r 1 ≃ₗ[ℂ] TF (Fin r × Fin 2) (Qn L b) where
  toFun v := (torL r v.2.1, (Submodule.Quotient.mk (inclB v.2.2.1), v.2.2.2 0))
  invFun w := (0, (torL r).symm w.1, qPi L b hb w.2.1, fun _ => w.2.2)
  map_add' v w := by
    refine Prod.ext (map_add _ _ _) (Prod.ext ?_ rfl)
    simp only [Prod.snd_add, Prod.fst_add, map_add, Submodule.Quotient.mk_add]
  map_smul' c v := by
    refine Prod.ext (map_smul _ _ _) (Prod.ext ?_ rfl)
    change Submodule.Quotient.mk (inclB (c • v.2.2.1)) = c • Submodule.Quotient.mk (inclB v.2.2.1)
    rw [map_smul, Submodule.Quotient.mk_smul]
  left_inv v := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Prod.ext ?_ ?_))
    · exact (torL r).symm_apply_apply _
    · change qPi L b hb (Submodule.Quotient.mk _) = _
      rw [qPi_mk, piB_inclB]
    · funext i; fin_cases i; rfl
  right_inv w := by
    refine Prod.ext ((torL r).apply_symm_apply _) (Prod.ext ?_ rfl)
    exact mk_inclB_qPi L b hb _

lemma mgIota_symm_apply (w : TF (Fin r × Fin 2) (Qn L b)) :
    (mgIota L b hb).symm w = (0, (torL r).symm w.1, qPi L b hb w.2.1, fun _ => w.2.2) := rfl

lemma mgIota_apply (v : TanV 0 (2 * nI r) r 1) :
    mgIota L b hb v = (torL r v.2.1, (Submodule.Quotient.mk (inclB v.2.2.1), v.2.2.2 0)) := rfl

end LSG.W88.V5d
