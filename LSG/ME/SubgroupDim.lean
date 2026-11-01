import Mathlib
import LSG.ME.SubgroupTanSp
import LSG.ME.DimTrdeg

/-!
# Dimension of `H⁰` and finiteness of `H / H⁰` (STAGE2 §5, item 5; `K = ℂ`)

For a Zariski-closed subgroup `H ⊆ G(ℂ)` with analytic Lie algebra `T′ = lieAlg H` and identity
component `H⁰ = zcl (exp T′)`:

* **`trdeg_le_of_subset`**: every irreducible Zariski-closed `Y ⊆ H` through `0` has
  `trdeg (ℂ[Var]/vanish Y) ≤ dim T′ + m` (tangent space at the identity).
* **`trdeg_H0`**: `trdeg (ℂ[Var]/vanish H⁰) = dim T′ + m` (`≥` at a smooth point of `H⁰` with all
  `V_k ≠ 0`, transported to a `V`-normalised point).
* **`hdim_H0`**: StrongSix's Hilbert dimension: `(hdata blk D ℂ (vanish H⁰)).1 = dim_ℂ T′ + m` for
  every `D ≥ 1` (the `m` is the uniform shift from the cone scalings: affine cone dimensions are
  projective dimensions plus `m`).
* **`finite_cosets_H0`**: `H` is a finite union of cosets `h + H⁰`, `h ∈ H` (each coset is an
  irreducible component of `H`, by the dimension bound and translation of components).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Filter Topology Set Module
open LSG.W88 (Tan)

namespace LSG.ME

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

theorem mem_zeroLocus_iff_eval {I : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {x : Var d₀ d₁ m → ℂ} :
    x ∈ zeroLocus ℂ I ↔ ∀ P ∈ I, eval x P = 0 := by
  rw [mem_zeroLocus_iff]; rfl

/-- A zero of `vanish E` with all `V_k ≠ 0` is a cone representative of a point of `E`. -/
theorem exists_coords_of_zeroLocus {E : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} (hE : IsZClosed E)
    {a : Var d₀ d₁ m → ℂ} (ha : ∀ P ∈ vanish E, eval a P = 0) (hV : ∀ k, a (.e k 1) ≠ 0) :
    ∃ g ∈ E, ∃ ν : Fin m → ℂˣ, a = coords g ν := by
  classical
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hyz : ∀ j, a (.y j) * a (.z j) = 1 := fun j => by
    have := ha _ (IG_le_vanish h2 E (YZ_mem_IG (g2L Ls) (g3L Ls) j))
    simpa [YZ, sub_eq_zero] using this
  set cv : Fin m → Fin 3 → ℂ := fun k c => a (.e k c)
  have hF : ∀ k, Fv (g2L Ls k) (g3L Ls k) (cv k) = 0 := fun k => by
    have := ha _ (IG_le_vanish h2 E (Fk_mem_IG (g2L Ls) (g3L Ls) k))
    simpa [Fk, LSG.Elliptic.F, Fv, cv] using this
  have hcv : ∀ k, cv k ≠ 0 := fun k h => hV k (congrFun h 1)
  choose u hu0 hu using fun k => exists_smul_rep h2 (discr_g2L Ls k) (hF k) (hcv k)
  let g : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) := (fun i => a (.x i),
    Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j),
    fun k => toPoint (g2L Ls k) (g3L Ls k) (cv k))
  let ν : Fin m → ℂˣ := fun k => Units.mk0 (u k) (hu0 k)
  have hag : a = coords g ν := by
    funext v
    cases v with
    | x i => rfl
    | y j => rfl
    | z j =>
      show a (.z j) = (((Units.mkOfMulEqOne _ _ (hyz j))⁻¹ : ℂˣ) : ℂ)
      rw [Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
      exact eq_inv_of_mul_eq_one_right (hyz j)
    | e k c => exact congrFun (hu k) c
  refine ⟨g, ?_, ν, hag⟩
  rw [← zeros_homogVanish hE]
  intro Q hQ lam
  obtain ⟨d, hd⟩ := hQ.2
  have := ha Q hQ.1
  rw [hag] at this
  exact (eval_coords_eq_zero_iff hd g ν lam).mp this

/-- **Upper bound** for irreducible closed subsets of `H` through `0`. -/
theorem trdeg_le_of_subset (hH : IsSubgroupG H) (hc : IsZClosed H)
    {Y : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))} [hY : (vanish Y).IsPrime] (hYH : Y ⊆ H)
    (h0 : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ Y) :
    (Algebra.trdeg ℂ (MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish Y)).toNat ≤
      finrank ℂ (lieAlg Ls hH hc) + m := by
  have ha : a0 Ls d₀ d₁ ∈ zeroLocus ℂ (vanish Y) :=
    mem_zeroLocus_iff_eval.mpr fun P hP => mem_vanish.mp hP 0 h0 1
  have hmono : tangentSpace (vanish Y) (a0 Ls d₀ d₁) ≤ tangentSpace (vanish H) (a0 Ls d₀ d₁) :=
    fun v hv f hf => hv f (vanish_antitone hYH hf)
  calc _ ≤ finrank ℂ (tangentSpace (vanish Y) (a0 Ls d₀ d₁)) :=
        trdeg_le_finrank_tangentSpace (vanish Y) _ ha
    _ ≤ finrank ℂ (tangentSpace (vanish H) (a0 Ls d₀ d₁)) := Submodule.finrank_mono hmono
    _ ≤ _ := finrank_tangentSpace_zero_le hH hc

/-- **`dim H⁰ = dim T′ + m`** (transcendence degree of the cone). -/
theorem trdeg_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) :
    haveI := vanish_H0_isPrime (Ls := Ls) hH hc
    (Algebra.trdeg ℂ (MvPolynomial (Var d₀ d₁ m) ℂ ⧸ vanish (H0 Ls hH hc))).toNat =
      finrank ℂ (lieAlg Ls hH hc) + m := by
  haveI := vanish_H0_isPrime (Ls := Ls) hH hc
  have h0 : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ H0 Ls hH hc := (H0_isSubgroup hH hc).zero_mem
  refine le_antisymm (trdeg_le_of_subset hH hc (H0_subset hH hc) h0) ?_
  -- a smooth point with all `V_k ≠ 0`
  have hVp : (Vprod : MvPolynomial (Var d₀ d₁ m) ℂ) ∉ vanish (H0 Ls hH hc) := by
    intro h
    have := mem_vanish.mp h 0 h0 1
    simp [Vprod, coords, rep, O] at this
  obtain ⟨a, ha, haV, hsm⟩ := exists_smooth_point (vanish (H0 Ls hH hc)) Vprod hVp
  have ha' := mem_zeroLocus_iff_eval.mp ha
  have hVk : ∀ k, a (.e k 1) ≠ 0 := by
    intro k hk
    apply haV
    simp only [Vprod, map_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  obtain ⟨g, hg, ν, rfl⟩ := exists_coords_of_zeroLocus (isZClosed_H0 hH hc) ha' hVk
  obtain ⟨p, rfl⟩ := expG_surjective Ls g
  have hrepV : ∀ k, rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) (p.2.2 k)) 1 ≠ 0 := by
    intro k h
    apply hVk k
    simp only [coords, coordsZ_e]
    rw [show (expG Ls p).2.2 k = expE (Ls k) (p.2.2 k) from rfl, h, mul_zero]
  have hpV : ∀ k, p.2.2 k ∈ (Ls k).lattice ∨ (Ls k).derivWeierstrassP (p.2.2 k) ≠ 0 := by
    intro k
    by_cases hk : p.2.2 k ∈ (Ls k).lattice
    · exact Or.inl hk
    · right
      have := hrepV k
      have hr : rep (g₂ := g2L Ls k) (g₃ := g3L Ls k) (expE (Ls k) (p.2.2 k)) =
          ![(Ls k).weierstrassP (p.2.2 k), (Ls k).derivWeierstrassP (p.2.2 k), 1] :=
        rep_expE_of_notMem (Ls k) hk
      rw [hr] at this
      simpa using this
  obtain ⟨U, F, hF, hpU⟩ := exists_VLifts Ls p.2.2 hpV
  obtain ⟨lam', hlam'⟩ := hF.liftX_eq hpU
  have hscale : coords (expG Ls p) ν = scaleV (fun k => ν k * (lam' k)⁻¹) (liftX F p) := by
    have e : scaleV (fun k => ν k * (lam' k)⁻¹) (coords (expG Ls p) lam') =
        coords (expG Ls p) (fun k => (ν k * (lam' k)⁻¹) * lam' k) := (coords_mul _ _ _).symm
    rw [hlam', e]
    congr 1
    funext k
    rw [inv_mul_cancel_right]
  have hlow := le_finrank_tangentSpace hH hc hg hF hpU
  rw [← finrank_tangentSpace_scale (fun k => ν k * (lam' k)⁻¹), ← hscale, hsm] at hlow
  exact hlow

/-- **Hilbert dimension of `H⁰`**: `dim_ℂ T′ + m` (cone dimension). -/
theorem hdim_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (StrongSix.M2.hdata blk D ℂ (vanish (H0 Ls hH hc))).1 = finrank ℂ (lieAlg Ls hH hc) + m := by
  haveI := vanish_H0_isPrime (Ls := Ls) hH hc
  rw [hdim_eq_trdeg blk D hD, trdeg_H0 hH hc]

/-- **`H` is a finite union of cosets of `H⁰`.** -/
theorem finite_cosets_H0 (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ∃ R : Finset (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)), (∀ h ∈ R, h ∈ H) ∧
      H ⊆ ⋃ h ∈ R, gtransl h (H0 Ls hH hc) := by
  classical
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hΔ := discr_g2L Ls
  have hp0 := vanish_H0_isPrime (Ls := Ls) hH hc
  have hc0 := isZClosed_H0 (Ls := Ls) hH hc
  have h0 : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ H0 Ls hH hc := (H0_isSubgroup hH hc).zero_mem
  obtain ⟨ps, hps, hmin⟩ := exists_components hc
  -- every coset is a component
  have key : ∀ h ∈ H, ∃ p ∈ ps, (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) =
      gtransl h (H0 Ls hH hc) := by
    intro h hh
    set C := gtransl h (H0 Ls hH hc)
    have hCp : (vanish C).IsPrime := vanish_gtransl_isPrime h2 hΔ hc0 hp0 h
    have hCH : C ⊆ H := by
      rintro _ ⟨u, hu, rfl⟩
      exact hH.add_mem u (H0_subset hH hc hu) h hh
    obtain ⟨p, hp, hpC⟩ := hmin _ hCp (vanish_antitone hCH)
    obtain ⟨hpr, hpH, hpv⟩ := hps p hp
    set Vp : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) := zeros (p : Set _)
    have hVpc : IsZClosed Vp := isZClosed_zeros _
    have hCV : C ⊆ Vp := by
      have hCc : IsZClosed C := isZClosed_gtransl h2 hΔ hc0 h
      rw [← zeros_vanish hCc]
      intro g hg P hP lam
      exact hg P (hpC hP) lam
    have hVpH : Vp ⊆ H := by
      rw [← zeros_vanish hc]
      intro g hg P hP lam
      exact hg P (hpH hP) lam
    -- translate back to the identity
    set Y := gtransl (-h) Vp
    have hYp : (vanish Y).IsPrime := vanish_gtransl_isPrime h2 hΔ hVpc (hpv ▸ hpr) (-h)
    have hYH : Y ⊆ H := by
      rintro _ ⟨u, hu, rfl⟩
      exact hH.add_mem u (hVpH hu) (-h) (hH.neg_mem h hh)
    have hH0Y : H0 Ls hH hc ⊆ Y := by
      intro u hu
      rw [mem_gtransl, sub_neg_eq_add]
      exact hCV ⟨u, hu, rfl⟩
    have hY0 : (0 : GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) ∈ Y := hH0Y h0
    have hle := trdeg_le_of_subset hH hc hYH hY0
    have heq : vanish Y = vanish (H0 Ls hH hc) := by
      refine le_antisymm (vanish_antitone hH0Y) (by_contra fun hne => ?_)
      have hlt : vanish Y < vanish (H0 Ls hH hc) :=
        lt_of_le_of_ne (vanish_antitone hH0Y) fun e => hne e.ge
      have := StrongSix.M2.hdim_lt_of_lt blk (fun _ => 1) ℂ (fun _ => le_rfl)
        (q := vanish Y) (q' := vanish (H0 Ls hH hc)) hp0.ne_top hlt
      rw [hdim_eq_trdeg blk _ (fun _ => le_rfl), hdim_eq_trdeg blk _ (fun _ => le_rfl),
        trdeg_H0 hH hc] at this
      omega
    have hYc : IsZClosed Y := isZClosed_gtransl h2 hΔ hVpc (-h)
    have hYeq : Y = H0 Ls hH hc := vanish_injOn hYc hc0 heq
    refine ⟨p, hp, ?_⟩
    change Vp = gtransl h (H0 Ls hH hc)
    have hb : Vp = gtransl h Y := by rw [gtransl_gtransl, neg_add_cancel, gtransl_zero]
    rw [hb, hYeq]
  -- choose representatives
  have hrep : ∀ p ∈ ps, (∃ h ∈ H, (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) =
      gtransl h (H0 Ls hH hc)) → ∃ h ∈ H, (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) =
      gtransl h (H0 Ls hH hc) := fun _ _ h => h
  let rp : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) → GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls) := fun p =>
    if hp : ∃ h ∈ H, (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) =
      gtransl h (H0 Ls hH hc) then Classical.choose hp else 0
  refine ⟨ps.image rp, fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hh
    simp only [rp]
    split_ifs with hp
    · exact (Classical.choose_spec hp).1
    · exact hH.zero_mem
  · obtain ⟨p, hp, hpe⟩ := key h hh
    have hex : ∃ h' ∈ H, (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) =
        gtransl h' (H0 Ls hH hc) := ⟨h, hh, hpe⟩
    have hmem : h ∈ (zeros (p : Set _) : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))) := by
      rw [hpe, mem_gtransl, sub_self]; exact h0
    simp only [Set.mem_iUnion]
    refine ⟨rp p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    have hrp : rp p = Classical.choose hex := by simp only [rp, dif_pos hex]
    rw [hrp, ← (Classical.choose_spec hex).2]
    exact hmem

end LSG.ME
