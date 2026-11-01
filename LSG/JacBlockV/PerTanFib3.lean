/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.JacBlockV.PerTanFib2

/-!
# M2.7 for `B = fun _ => aBlockV`: `PerTanPiv`, part 2

`t` rational, `e` a pivot (`z ↦ z ∘ e` bijective on `t`). Then `dim_ℂ t = 2n` (`finrank_t`), and the restriction
`reW : W → ℚ^{4n}`, `x ↦ x ∘ e`, of the rational subspace `W = Wsub t` is injective (pivot injectivity and
`Φ1_eq_zero`) between spaces of dimensions `≥ 4n` (`finrank_t_le`) and `4n`, hence a `ℚ`-linear isomorphism
(`reW_bij`). With `v_i = reW⁻¹(δ_{i,0})` and `A_{ki} = Ψq(v_{i,k})` (algebraic): `reW⁻¹(δ_{i,j}) = Tq^j v_i`
(`W` is `Tq`-stable), and `L x = Ψq(x_k) − Σ_i A_{ki} Ψq(x_{e i})` satisfies `L(Tq x) = ζ⁴ L x`, `L(v_i) = 0`; so
`L ∘ reW⁻¹` vanishes on a basis and **`Ψq(x_k) = Σ_i A_{ki} Ψq(x_{e i})` on `W`** (`exists_A`).

**`perTanPiv_aBlockV`**: for `z ∈ t ∩ kerE^m`, `N z ∈ latt^m` (finite index), `N z = Φq x` with `x ∈ W` integral,
`N η(z_k) = cη Ψq(x_k)` (`eta_lv`), and the relation above gives `η(z_k) = Σ_i A_{ki} η(z_{e i})`.
-/

noncomputable section

open Module LSG.JacAn LSG.JacAn.Beta LSG.JacBlock

namespace LSG.JacBlockV

local notation "ζ" => LSG.JacAn.Beta.zetaN 5

variable {m n : ℕ}

/-- Restriction of `W` to the pivot copies. -/
def reW (t : Submodule ℂ (Fin m → Fin 2 → ℂ)) (e : Fin n → Fin m) : Wsub t →ₗ[ℚ] (Fin n → Fin 4 → ℚ) :=
  (LinearMap.funLeft ℚ (Fin 4 → ℚ) e).comp (Wsub t).subtype

lemma reW_apply (t : Submodule ℂ (Fin m → Fin 2 → ℂ)) (e : Fin n → Fin m) (x : Wsub t) :
    reW t e x = fun i => (x : Fin m → Fin 4 → ℚ) (e i) := rfl

section Pivot

variable {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (e : Fin n → Fin m)
  (hinj : ∀ z ∈ t, (∀ i, z (e i) = 0) → z = 0)
  (hsurj : ∀ w : Fin n → Fin 2 → ℂ, ∃ z ∈ t, ∀ i, z (e i) = w i)

include hinj in
lemma reW_inj : Function.Injective (reW t e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hx0 : ∀ i, (x : Fin m → Fin 4 → ℚ) (e i) = 0 := fun i => congrFun hx i
  have hz := hinj (Φq x) x.2 (fun i => by change Φ1 _ = 0; rw [hx0 i, Φ1_zero])
  exact Subtype.ext (funext fun k => Φ1_eq_zero (congrFun hz k))

include hinj hsurj in
lemma finrank_t : finrank ℂ t = n * 2 := by
  set g : t →ₗ[ℂ] (Fin n → Fin 2 → ℂ) := (LinearMap.funLeft ℂ (Fin 2 → ℂ) e).comp t.subtype
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      exact Subtype.ext (hinj z z.2 (fun i => congrFun hz i))
    · intro w
      obtain ⟨z, hz, hzw⟩ := hsurj w
      exact ⟨⟨z, hz⟩, funext hzw⟩
  rw [(LinearEquiv.ofBijective g hg).finrank_eq]
  simp [Module.finrank_pi_fintype]

include hinj hsurj in
lemma reW_bij (ht : LSG.W88.IsAbelianTangentA t) : Function.Bijective (reW t e) := by
  have hi := reW_inj e hinj
  have hle := finrank_t_le ht
  rw [finrank_t e hinj hsurj] at hle
  have hup := LinearMap.finrank_le_finrank_of_injective hi
  have hdim : finrank ℚ (Fin n → Fin 4 → ℚ) = n * 4 := by simp [Module.finrank_pi_fintype]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).mp hi⟩

end Pivot

/-- `L x = Ψq(x_k) − Σ_i A_{ki} Ψq(x_{e i})`. -/
def L1 (A : Matrix (Fin m) (Fin n) ℂ) (e : Fin n → Fin m) (k : Fin m) : (Fin m → Fin 4 → ℚ) →ₗ[ℚ] ℂ where
  toFun x := Ψq (x k) - ∑ i, A k i * Ψq (x (e i))
  map_add' x y := by
    simp only [Pi.add_apply, Ψq_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' q x := by
    simp only [Pi.smul_apply, Ψq_smul, RingHom.id_apply]
    rw [Rat.smul_def, mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

lemma L1_apply (A : Matrix (Fin m) (Fin n) ℂ) (e : Fin n → Fin m) (k : Fin m) (x : Fin m → Fin 4 → ℚ) :
    L1 A e k x = Ψq (x k) - ∑ i, A k i * Ψq (x (e i)) := rfl

lemma L1_TmI_iter (A : Matrix (Fin m) (Fin n) ℂ) (e : Fin n → Fin m) (k : Fin m) (j : ℕ)
    (x : Fin m → Fin 4 → ℚ) : L1 A e k (TmI^[j] x) = ζ ^ (4 * j) * L1 A e k x := by
  simp only [L1_apply, TmI_iter, Ψq_Tq_iter]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The pivot relation on the rational subspace.** -/
theorem exists_A {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (e : Fin n → Fin m) (ht : LSG.W88.IsAbelianTangentA t)
    (hinj : ∀ z ∈ t, (∀ i, z (e i) = 0) → z = 0)
    (hsurj : ∀ w : Fin n → Fin 2 → ℂ, ∃ z ∈ t, ∀ i, z (e i) = w i) :
    ∃ A : Matrix (Fin m) (Fin n) ℂ, (∀ k i, IsAlgebraic ℚ (A k i)) ∧
      ∀ x ∈ Wsub t, ∀ k, Ψq (x k) = ∑ i, A k i * Ψq (x (e i)) := by
  set f := LinearEquiv.ofBijective (reW t e) (reW_bij e hinj hsurj ht)
  set v : Fin n → Fin m → Fin 4 → ℚ := fun i => (f.symm (Pi.single i (Pi.single 0 1)) : Fin m → Fin 4 → ℚ)
    with hv
  set A : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun k i => Ψq (v i k) with hA
  refine ⟨A, fun k i => Ψq_alg _, ?_⟩
  have hve : ∀ i i', v i (e i') = (Pi.single i (Pi.single (0 : Fin 4) (1 : ℚ)) : Fin n → Fin 4 → ℚ) i' :=
    fun i i' => congrFun (f.apply_symm_apply (Pi.single i (Pi.single 0 1))) i'
  have hsymm : ∀ i (j : Fin 4), f.symm (Pi.single i (Pi.single j 1)) =
      ⟨TmI^[(j : ℕ)] (v i), Wsub_TmI_iter ht _ (f.symm _).2⟩ := by
    intro i j
    rw [f.symm_apply_eq]
    funext i'
    change (Pi.single i (Pi.single j (1 : ℚ)) : Fin n → Fin 4 → ℚ) i' = (TmI^[(j : ℕ)] (v i)) (e i')
    rw [TmI_iter, hve]
    by_cases h : i' = i
    · subst h; simp [Tq_iter_single]
    · simp [h, Tq_iter_zero]
  intro x hx k
  have hLv : ∀ i, L1 A e k (v i) = 0 := fun i => by
    rw [L1_apply, Finset.sum_eq_single i]
    · rw [hve, Pi.single_eq_same, Ψq_single0, mul_one, hA, Matrix.of_apply, sub_self]
    · intro i' _ hi'
      rw [hve, Pi.single_eq_of_ne hi', Ψq_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hg : (L1 A e k).comp ((Wsub t).subtype.comp f.symm.toLinearMap) = 0 := by
    refine (Pi.basis fun _ : Fin n => Pi.basisFun ℚ (Fin 4)).ext fun ij => ?_
    obtain ⟨i, j⟩ := ij
    rw [Pi.basis_apply, Pi.basisFun_apply, LinearMap.zero_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change L1 A e k ((f.symm (Pi.single i (Pi.single j 1)) : Wsub t) : Fin m → Fin 4 → ℚ) = 0
    rw [hsymm]
    change L1 A e k (TmI^[(j : ℕ)] (v i)) = 0
    rw [L1_TmI_iter, hLv, mul_zero]
  have h := congrArg (fun φ : (Fin n → Fin 4 → ℚ) →ₗ[ℚ] ℂ => φ (f ⟨x, hx⟩)) hg
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.zero_apply, Submodule.subtype_apply] at h
  exact sub_eq_zero.mp h

/-- `η(N ω) = N η(ω)` on `kerE`. -/
lemma eta_nsmul_per (N : ℕ) {ω : Fin 2 → ℂ} (hω : ω ∈ kerE stdPkg.G) :
    stdPkg.D.etaB (N • ω) = N * stdPkg.D.etaB ω := by
  induction N with
  | zero =>
    rw [zero_smul, Nat.cast_zero, zero_mul]
    exact aBlockV.η_zero
  | succ N ih =>
    rw [succ_nsmul]
    have h := aBlockV.η_add (ω := N • ω) (ω' := ω) (nsmul_mem hω N) hω
    change stdPkg.D.etaB (N • ω + ω) = stdPkg.D.etaB (N • ω) + stdPkg.D.etaB ω at h
    rw [h, ih]
    push_cast
    ring

/-- The pivot relation for the fibre periods of `z ∈ t ∩ kerE^m`. -/
lemma piv_main {t : Submodule ℂ (Fin m → Fin 2 → ℂ)} (e : Fin n → Fin m) (A : Matrix (Fin m) (Fin n) ℂ)
    (hkey : ∀ x ∈ Wsub t, ∀ k, Ψq (x k) = ∑ i, A k i * Ψq (x (e i)))
    {z : Fin m → Fin 2 → ℂ} (hz : z ∈ t) (hper : ∀ k, z k ∈ kerE stdPkg.G) (k : Fin m) :
    stdPkg.D.etaB (z k) = ∑ i, A k i * stdPkg.D.etaB (z (e i)) := by
  choose Nk hNk using fun k => LSG.W88.isNsmulIn_latt_kerE stdPkg.G (z k) (hper k)
  have hN : 0 < ∏ k, Nk k := Finset.prod_pos fun k _ => (hNk k).1
  have hNz : ∀ k, (∏ k, Nk k) • z k ∈ latt := fun k => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nk (Finset.mem_univ k)
    rw [hc, mul_nsmul]
    exact nsmul_mem (hNk k).2 c
  set N := ∏ k, Nk k
  choose nn hnn using fun k => LSG.W88.latt_repr' (hNz k)
  set x : Fin m → Fin 4 → ℚ := fun k e => (nn k e : ℚ) with hx
  have hxW : x ∈ Wsub t := by
    rw [mem_Wsub]
    have h1 : Φq x = N • z := funext fun k => by
      change Φ1 _ = _
      rw [Φ1_int, ← hnn k]
      rfl
    rw [h1]
    exact t.nsmul_mem hz N
  have heta : ∀ k, (N : ℂ) * stdPkg.D.etaB (z k) = cη * Ψq (x k) := fun k => by
    rw [← eta_nsmul_per N (hper k), hnn k, ← lv_zero, eta_lv]
    simp [Ψq, hx]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  apply mul_left_cancel₀ hN0
  rw [heta, hkey x hxW k, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm (N : ℂ), heta]
  ring

/-- **The pivot property of `aBlockV^m`.** -/
theorem perTanPiv_aBlockV : LSG.W88.PerTanPiv (fun _ : Fin m => aBlockV) := by
  intro t ht n e _he hinj hsurj
  obtain ⟨A, hA, hkey⟩ := exists_A (t := t) e (isAbTan_of_ratSub ht) hinj hsurj
  refine ⟨A, hA, fun z hz hper => funext fun k => ?_⟩
  simp only [Matrix.mulVec, dotProduct]
  exact piv_main e A hkey hz hper k

end LSG.JacBlockV
