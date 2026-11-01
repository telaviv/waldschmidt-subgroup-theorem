/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.V5dMGn
import LSG.W88.MStarCopyNat
import LSG.CM.Inst

/-!
# Theorem 1(a)'s hypothesis `Thm11KappaNat` from `Theorem41VecLA`

lean_mstar's `gmQ` is `G_m⁸ × Q''`, `Q'' = (E_i^♮)⁴ / U`, with coordinates `(ℓ_{τ₁}(z), ℓ_{τ₂}(z),
θᵀw)` on `T(Q'')`, `θ = (1, i, √2, i√2)`. With `π(v) = (v₀ − i v₁, v₂ − i v₃)` (`Wphi = ker π`,
`LSG.W88.V5dMGnIso`) one has `ℓ_{τ₁} = z₀ + √2 z₁`, `ℓ_{τ₂} = z₀ − √2 z₁` for `z = π(v)`, so `Q''`
is the push-out of `(E_i²)^♮` along `(1, √2)` and `natIota : TanV 0 8 2 1 ≃ ℂ⁸ × ℂ³`, `(a, x, z, s)
↦ (x, (z₀ + √2 z₁, z₀ − √2 z₁, s))`.
* `perImg_mem`: `ι⁻¹(0, perImg m n)` is the period `((λ₀ − iλ₁, λ₂ − iλ₃), η(…))`;
* `iota_tanN`: `ι(T_H) = U^⊥ × h`, `U^⊥ = cspan (annQ U)`; a nonzero `h` contains the fibre `e₂`
  (`(0, 0, s)` from the vector part, or `(0, 0, ā₀ + √2 ā₁)` with `ā₀ + √2 ā₁ ≠ 0` for `0 ≠ a ∈
  ℤ[i]²`, since `√2 ∉ ℚ`).

**`thm11KappaNat_of : Theorem41VecLA → MStarCopy.Nat.Thm11KappaNat`**.
-/

open Complex Module LSG.Weierstrass PeriodPair LSG.AuxV LSG.CM

namespace LSG.W88.V5d

open LSG.W88.Vec LSG.W88.MStarCopy LSG.W88.MStarCopy.Nat

/-- The curves `E_i²`. -/
noncomputable abbrev nLs : Fin 2 → PeriodPair := fun _ => lemniscatic

/-- `M = (1, √2)`. -/
noncomputable def nM : Matrix (Fin 1) (Fin 2) ℂ := fun _ k => ![1, r2] k

lemma r2_ne : r2 ≠ 0 := by
  simp only [r2, ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr (by norm_num)).ne'

lemma r2_sq : r2 ^ 2 = 2 := by
  simp [r2, ← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

lemma isAlgebraic_r2 : IsAlgebraic ℚ r2 := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2,
    (Polynomial.monic_X_pow_sub_C 2 two_ne_zero).ne_zero, ?_⟩
  simp [r2_sq]

lemma nM_mulVec (x : Fin 2 → ℂ) : nM.mulVec x 0 = x 0 + r2 * x 1 := by
  simp [Matrix.mulVec, dotProduct, nM, Fin.sum_univ_two]

/-- **`ι : TanV 0 8 2 1 ≃ ℂ⁸ × ℂ³`.** -/
noncomputable def natIota : TanV 0 8 2 1 ≃ₗ[ℂ] TN where
  toFun v := (v.2.1, ![v.2.2.1 0 + r2 * v.2.2.1 1, v.2.2.1 0 - r2 * v.2.2.1 1, v.2.2.2 0])
  invFun w := (0, w.1, ![(w.2 0 + w.2 1) / 2, (w.2 0 - w.2 1) / (2 * r2)], fun _ => w.2 2)
  map_add' v w := by
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp <;> ring
  left_inv v := by
    have := r2_ne
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl (Prod.ext (funext fun i => ?_) ?_))
    · fin_cases i
      · simp
      · simp; field_simp; ring
    · funext i; fin_cases i; rfl
  right_inv w := by
    have := r2_ne
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp <;> field_simp <;> ring

lemma natIota_symm_apply (w : TN) : natIota.symm w =
    (0, w.1, ![(w.2 0 + w.2 1) / 2, (w.2 0 - w.2 1) / (2 * r2)], fun _ => w.2 2) := rfl

/-- `ι⁻¹(0, perImg m n)` is a period. -/
lemma perImg_mem (m n : Fin 4 → ℤ) :
    natIota.symm ((0 : Fin 8 → ℂ), perImg m n) ∈ PerV (d0 := 0) (d1 := 8) nLs nM := by
  have hr := r2_ne
  have hv : (varpi : ℂ) ≠ 0 := varpi_ne_zero'
  -- the two base coordinates
  have hz0 : (perImg m n 0 + perImg m n 1) / 2 =
      ((m 0 + n 1 : ℤ) : ℂ) * lemniscatic.ω₁ + ((n 0 - m 1 : ℤ) : ℂ) * lemniscatic.ω₂ := by
    simp [perImg, θ₁, θ₂, Fin.sum_univ_four, lemniscatic]
    linear_combination (-(n 1 : ℂ) * varpi) * I_sq
  have hz1 : (perImg m n 0 - perImg m n 1) / (2 * r2) =
      ((m 2 + n 3 : ℤ) : ℂ) * lemniscatic.ω₁ + ((n 2 - m 3 : ℤ) : ℂ) * lemniscatic.ω₂ := by
    rw [div_eq_iff (mul_ne_zero two_ne_zero hr)]
    simp [perImg, θ₁, θ₂, Fin.sum_univ_four, lemniscatic]
    linear_combination (-2 * (n 3 : ℂ) * varpi * r2) * I_sq
  rw [natIota_symm_apply]
  refine ⟨rfl, fun i => ⟨0, by simp⟩, fun k => ?_, funext fun i => ?_⟩
  · fin_cases k
    · change (perImg m n 0 + perImg m n 1) / 2 ∈ _; rw [hz0]
      exact PeriodPair.mem_lattice.mpr ⟨_, _, rfl⟩
    · change (perImg m n 0 - perImg m n 1) / (2 * r2) ∈ _; rw [hz1]
      exact PeriodPair.mem_lattice.mpr ⟨_, _, rfl⟩
  · rw [Subsingleton.elim i 0, nM_mulVec]
    simp only [etaV, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hz0, hz1, eta_lem, eta_lem]
    simp [perImg, θ, Fin.sum_univ_four, etaLem]
    linear_combination (-((n 1 : ℂ) + r2 * n 3) * (Real.pi / varpi)) * I_sq

/-- A toric vector with algebraic exponentials pulls back into `Λ(G)`. -/
lemma natTor_lam {y : Fin 8 → ℂ} (hy : ∀ j, IsAlgebraic ℚ (Complex.exp (y j))) :
    natIota.symm (y, (0 : Fin 3 → ℂ)) ∈ LamV (d0 := 0) (d1 := 8) nLs nM := by
  rw [natIota_symm_apply]
  refine ⟨fun i => i.elim0, hy, fun k => ?_, fun _ => ?_⟩
  · fin_cases k <;> simp [zero_mem]
  · have : zetaV nLs ![((0 : Fin 3 → ℂ) 0 + (0 : Fin 3 → ℂ) 1) / 2,
        ((0 : Fin 3 → ℂ) 0 - (0 : Fin 3 → ℂ) 1) / (2 * r2)] = 0 := by
      funext k; fin_cases k <;> simp [zetaV, zeta_zero]
    rw [this, Matrix.mulVec_zero, sub_zero]
    exact isAlgebraic_zero

lemma natTor_per (j : Fin 8) :
    natIota.symm ((Pi.single j (2 * Real.pi * I) : Fin 8 → ℂ), (0 : Fin 3 → ℂ)) ∈
      PerV (d0 := 0) (d1 := 8) nLs nM := by
  rw [natIota_symm_apply]
  refine ⟨rfl, fun i => ?_, fun k => ?_, funext fun _ => ?_⟩
  · by_cases h : i = j
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  · fin_cases k <;> simp [zero_mem]
  · have : etaV nLs ![((0 : Fin 3 → ℂ) 0 + (0 : Fin 3 → ℂ) 1) / 2,
        ((0 : Fin 3 → ℂ) 0 - (0 : Fin 3 → ℂ) 1) / (2 * r2)] = 0 := by
      funext k; fin_cases k <;> simp [etaV]
    rw [this, Matrix.mulVec_zero]; rfl

/-! ### Subgroups -/

/-- `(a, s) ↦ (0, 0, s)`. -/
noncomputable def gN : (Fin 0 → ℂ) × (Fin 1 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun x := ![0, 0, x.2 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

/-- `(z, s) ↦ (z₀ + √2 z₁, z₀ − √2 z₁, s)`. -/
noncomputable def aN : (Fin 2 → ℂ) × (Fin 1 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun x := ![x.1 0 + r2 * x.1 1, x.1 0 - r2 * x.1 1, x.2 0]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring

theorem iota_tanN (H : SubgroupDataV (d0 := 0) (d1 := 8) nLs nM) :
    H.tan.map natIota.toLinearMap = (K11.cspan (K11.annQ H.U)).prod
      (H.gam.map gN ⊔ (perTan nLs nM H.t).map aN) := by
  have e1 : natIota.toLinearMap ∘ₗ vecIncl = LinearMap.inr ℂ _ _ ∘ₗ gN := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp [natIota, vecIncl, gN]
  have e2 : natIota.toLinearMap ∘ₗ torIncl = LinearMap.inl ℂ _ _ := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp [natIota, torIncl]
  have e3 : natIota.toLinearMap ∘ₗ g2Incl = LinearMap.inr ℂ _ _ ∘ₗ aN := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp [natIota, g2Incl, aN]
  have h1 : torusLie H.U = K11.annC H.U := rfl
  rw [SubgroupDataV.tan, Submodule.map_sup, Submodule.map_sup, ← Submodule.map_comp,
    ← Submodule.map_comp, ← Submodule.map_comp, e1, e2, e3, Submodule.map_comp, Submodule.map_comp,
    Submodule.map_inl, Submodule.map_inr, Submodule.map_inr, Submodule.prod_sup_prod,
    Submodule.prod_sup_prod, h1, K11.annC_eq_cspan]
  simp only [bot_sup_eq, sup_bot_eq]

lemma sqrt2_int {p q : ℤ} (h : (p : ℝ) + Real.sqrt 2 * q = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    apply Nat.prime_two.irrational_sqrt
    refine ⟨((-p : ℚ) / q), ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp
    linear_combination -h
  subst hq
  simp only [Int.cast_zero, mul_zero, add_zero] at h
  exact ⟨by exact_mod_cast h, rfl⟩

/-- A nonzero abelian part gives `(0, 0, c)`, `c ≠ 0`. -/
lemma abel_neN (H : SubgroupDataV (d0 := 0) (d1 := 8) nLs nM) (ht : H.t ≠ ⊥) :
    ∃ c : ℂ, c ≠ 0 ∧ ![0, 0, c] ∈ (perTan nLs nM H.t).map aN := by
  have hd := cmLem
  obtain ⟨l, ⟨hlt, hl⟩, hl0⟩ : ∃ l ∈ {z | z ∈ H.t ∧ ∀ j, z j ∈ (nLs j).lattice}, l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ht
    rw [← span_lat_eq H.t_ab, Submodule.span_eq_bot]
    exact hcon
  set ac : Fin 2 → ℂ := fun k => starRingEnd ℂ (l k / lemniscatic.ω₁)
  have hη := hd.eta_one_ne
  have hac : ((0 : Fin 2 → ℂ), ac) ∈ perTanId nLs H.t := by
    have h := Submodule.smul_mem _ (eta lemniscatic lemniscatic.ω₁)⁻¹ (snd_mem hd hlt hl)
    have e : ac = (eta lemniscatic lemniscatic.ω₁)⁻¹ • etaV (fun _ => lemniscatic) l :=
      funext fun k => by
        simp only [ac, Pi.smul_apply, smul_eq_mul, etaV_eq hd hl k]
        field_simp
    rw [e]; simpa using h
  have hmem : ((0 : Fin 2 → ℂ), nM.mulVec ac) ∈ perTan nLs nM H.t := ⟨_, hac, by simp⟩
  refine ⟨ac 0 + r2 * ac 1, ?_, ⟨_, hmem, ?_⟩⟩
  · intro h0
    choose m n hmn using fun k => hd.div_eq (hl k)
    simp only [ac, hmn, map_add, map_mul, map_intCast, Complex.conj_I] at h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp [r2] at hre him
    obtain ⟨hm0, hm1⟩ := sqrt2_int (p := m 0) (q := m 1) (by linarith)
    obtain ⟨hn0, hn1⟩ := sqrt2_int (p := n 0) (q := n 1) (by linarith)
    apply hl0
    funext k
    have : l k / lemniscatic.ω₁ = 0 := by
      rw [hmn k]; fin_cases k <;> simp [hm0, hm1, hn0, hn1]
    rwa [div_eq_zero_iff, or_iff_left (ω₁_ne_zero _)] at this
  · funext i; fin_cases i <;> simp [aN, nM_mulVec]

/-- **Theorem 1(a)'s hypothesis from `Theorem41VecLA`.** -/
theorem thm11KappaNat_of (h : Theorem41VecLA) : MStarCopy.Nat.Thm11KappaNat := by
  intro hg₂ hg₃
  have hLs : ∀ j, IsAlgebraic ℚ (nLs j).g₂ ∧ IsAlgebraic ℚ (nLs j).g₃ := fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat nM := by
    intro i k; fin_cases k
    · simpa [nM] using isAlgebraic_one
    · simpa [nM] using isAlgebraic_r2
  set Λs := lamVSub (d0 := 0) (d1 := 8) nLs nM hLs hM
  refine hyperplaneKappa_of_iso (hyperplaneKappaVec_of h) hLs hM le_rfl
    (liftAlg_block hg₂ hg₃ cmLem) (perTanRat_block cmLem) gmQ natIota ?_ Λs (fun _ hx => hx) ?_ ?_
    rfl rfl ?_
  · -- algebraic vectors
    intro v hv
    rw [natIota_symm_apply]
    have hr := isAlgebraic_r2
    have h2 : IsAlgebraic ℚ (2 : ℂ) := mem_Qbar.mp (ofNat_mem Qbar 2)
    refine ⟨fun i => i.elim0, hv.1, fun k => ?_, fun _ => hv.2 2⟩
    fin_cases k
    · exact ((hv.2 0).add (hv.2 1)).mul h2.inv
    · exact ((hv.2 0).sub (hv.2 1)).mul (h2.mul hr).inv
  · -- logarithms
    rintro y ⟨hy1, ⟨⟨m, n⟩, hmn⟩⟩
    refine ⟨1, one_pos, ?_⟩
    rw [one_smul]
    have : y = (y.1, (0 : Fin 3 → ℂ)) + ((0 : Fin 8 → ℂ), perImg m n) := by
      simp only at hmn
      rw [hmn]; simp
    rw [this, map_add]
    exact Λs.add_mem (natTor_lam hy1) (perV_le_lamV (perImg_mem m n))
  · -- periods
    have key : ∀ x, natIota.symm x ∈ PerV (d0 := 0) (d1 := 8) nLs nM →
        x ∈ (OmV 0 8 nLs nM).map (natIota.toLinearMap.restrictScalars ℚ) := by
      intro x hx
      refine ⟨natIota.symm x, Submodule.subset_span hx, ?_⟩
      simp
    change Submodule.span ℚ _ ≤ _
    rw [Submodule.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨q, ⟨⟨m, n⟩, rfl⟩, rfl⟩) <;> apply key
    · exact natTor_per j
    · exact perImg_mem m n
  · -- subgroups
    intro H _
    refine ⟨K11.annQ H.U, H.gam.map gN ⊔ (perTan nLs nM H.t).map aN, ?_, iota_tanN H⟩
    have hfib : ∀ c : ℂ, c ≠ 0 → ![0, 0, c] ∈ H.gam.map gN ⊔ (perTan nLs nM H.t).map aN →
        Pi.single 2 1 ∈ H.gam.map gN ⊔ (perTan nLs nM H.t).map aN := by
      intro c hc hmem
      have : (Pi.single 2 1 : Fin 3 → ℂ) = c⁻¹ • ![0, 0, c] := by
        funext i; fin_cases i <;> simp [hc]
      rw [this]; exact Submodule.smul_mem _ _ hmem
    by_cases hΓ : H.gam = ⊥
    · by_cases ht : H.t = ⊥
      · left; rw [hΓ, ht, perTan_bot]; simp
      · right
        obtain ⟨c, hc, hmem⟩ := abel_neN H ht
        exact hfib c hc (Submodule.mem_sup_right hmem)
    · right
      obtain ⟨w, hwΓ, -, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hΓ
        rw [H.gam_rat, Submodule.span_eq_bot]
        exact fun w hw => hcon w hw.1 hw.2
      refine hfib (w.2 0) (fun h0 => hw0 (Prod.ext (funext fun i => i.elim0) (funext fun i => ?_)))
        (Submodule.mem_sup_left ⟨w, hwΓ, rfl⟩)
      rw [Subsingleton.elim i 0, h0]; rfl

end LSG.W88.V5d
