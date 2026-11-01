import Mathlib
import LSG.ME.SubgroupDim
import LSG.ME.SubgroupHilbAux

/-!
# Product decomposition, step 1: `π_A(T′)` is an abelian tangent space (`K = ℂ`)

For a Zariski-closed subgroup `H ⊆ G(ℂ)` with Lie algebra `T′ = lieAlg H` and `π_A : Tan → ℂ^m`
the projection to the abelian coordinates, **`isAbelianTangent_map_piA`**: `π_A(T′)` is
`Λ`-rational (`IsAbelianTangent`).

Proof (transcendence-degree count). Let `P = π_A(T′)` and `B = zcl (exp (0 × 0 × P))`, a
Zariski-closed subgroup with `0 × 0 × P ⊆ lieAlg B`.
* `B⁰` has a transcendence basis of coordinate functions (`exists_coord_transcendenceBasis`) of size
  `dim lieAlg B + m` (`trdeg_H0`); these are elliptic cone coordinates (linear coordinates are
  constant on `B`).
* `T′_L = T′ ∩ ker π_A` projects onto `r = dim T′_L` of the linear coordinates
  (`exists_coord_surj`).
* The two families together are algebraically independent modulo `vanish H⁰`
  (`eq_zero_of_eval_elim`): at `exp(u + w)`, `u ∈ T′`, `w ∈ T′_L`, the elliptic coordinates only
  depend on `π_A u`, while the chosen linear coordinates sweep out `ℂ^a × (ℂ^×)^b`.
* Hence `r + dim lieAlg B + m ≤ trdeg H⁰ = dim T′ + m = r + dim P + m`, so `0 × 0 × P = lieAlg B`,
  whose abelian part is an abelian tangent space (`exists_abelianTangent_Htil`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Set Module
open LSG.W88 (Tan IsAbelianTangent)

namespace LSG.ME

/-! ### Generic lemmas -/

section Generic

theorem eval_map_sumAlgEquiv {K : Type*} [CommRing K] {S₁ S₂ : Type*}
    (R : MvPolynomial (S₁ ⊕ S₂) K) (x : S₁ → K) (y : S₂ → K) :
    eval x (map (eval y) (sumAlgEquiv K S₁ S₂ R)) = eval (Sum.elim x y) R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    cases v with
    | inl i => simp [hp]
    | inr j => simp [hp]

/-- **Independence on products.** A polynomial in `S₁ ⊕ S₂` vanishing on `X × Y`, where only
`0` vanishes on `X` resp. `Y`, is `0`. -/
theorem eq_zero_of_eval_elim {K : Type*} [CommRing K] {S₁ S₂ : Type*} {X₁ : Set (S₁ → K)}
    {Y : Set (S₂ → K)}
    (hX : ∀ P : MvPolynomial S₁ K, (∀ x ∈ X₁, eval x P = 0) → P = 0)
    (hY : ∀ Q : MvPolynomial S₂ K, (∀ y ∈ Y, eval y Q = 0) → Q = 0)
    {R : MvPolynomial (S₁ ⊕ S₂) K} (hR : ∀ x ∈ X₁, ∀ y ∈ Y, eval (Sum.elim x y) R = 0) :
    R = 0 := by
  set R' := sumAlgEquiv K S₁ S₂ R
  have h1 : ∀ y ∈ Y, map (eval y) R' = 0 := fun y hy =>
    hX _ fun x hx => by rw [eval_map_sumAlgEquiv]; exact hR x hx y hy
  have h2 : R' = 0 := by
    refine MvPolynomial.ext _ _ fun α => ?_
    change R'.coeff α = 0
    refine hY _ fun y hy => ?_
    have := congrArg (fun p => p.coeff α) (h1 y hy)
    simp only [coeff_map] at this
    exact this
  exact (sumAlgEquiv K S₁ S₂).injective (by rw [map_zero]; exact h2)

/-- Coordinate functions independent modulo a prime bound the transcendence degree. -/
theorem card_le_trdeg_of_indep {K : Type} [Field K] {σ ι : Type} [Fintype σ] [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (e : ι → σ)
    (h : ∀ R : MvPolynomial ι K, rename e R ∈ p → R = 0) :
    Fintype.card ι ≤ (Algebra.trdeg K (MvPolynomial σ K ⧸ p)).toNat := by
  set A := MvPolynomial σ K ⧸ p
  have hmk : aeval (fun j => Ideal.Quotient.mk p (X j) : σ → A) = Ideal.Quotient.mkₐ K p := by
    ext i; rw [aeval_X]; rfl
  have hind : AlgebraicIndependent K (fun i => Ideal.Quotient.mk p (X (e i)) : ι → A) := by
    rw [algebraicIndependent_iff]
    intro R hR
    refine h R (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    have : aeval (fun i => Ideal.Quotient.mk p (X (e i)) : ι → A) R =
        aeval (fun j => Ideal.Quotient.mk p (X j) : σ → A) (rename e R) := by
      rw [aeval_rename]; rfl
    rw [this, hmk, Ideal.Quotient.mkₐ_eq_mk] at hR
    exact hR
  have hc := hind.cardinalMk_le_trdeg
  rw [Cardinal.mk_fintype] at hc
  have := Cardinal.toNat_le_toNat hc (trdeg_quotient_lt_aleph0 p)
  rwa [Cardinal.toNat_natCast] at this

end Generic

/-! ### Linear maps on the tangent space -/

variable {d₀ d₁ m : ℕ}

/-- The projection `π_A : Tan → ℂ^m`. -/
def piA : Tan d₀ d₁ m →ₗ[ℂ] (Fin m → ℂ) := (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)

@[simp] theorem piA_apply (u : Tan d₀ d₁ m) : piA u = u.2.2 := rfl

/-- `z ↦ (0, 0, z)` as a linear map. -/
def inAbL : (Fin m → ℂ) →ₗ[ℂ] Tan d₀ d₁ m := (LinearMap.inr ℂ _ _).comp (LinearMap.inr ℂ _ _)

theorem inAbL_apply (z : Fin m → ℂ) : (inAbL z : Tan d₀ d₁ m) = inAb z := rfl

theorem inAbL_injective : Function.Injective (inAbL : (Fin m → ℂ) →ₗ[ℂ] Tan d₀ d₁ m) :=
  fun _ _ h => congrArg (fun u : Tan d₀ d₁ m => u.2.2) h

/-- The linear coordinates `(x, y)` as one vector of `ℂ^{d₀ + d₁}`. -/
def rhoL : Tan d₀ d₁ m →ₗ[ℂ] (Fin (d₀ + d₁) → ℂ) where
  toFun u i := Sum.elim u.1 u.2.1 (finSumFinEquiv.symm i)
  map_add' u v := by
    funext i; simp only [Pi.add_apply]; cases (finSumFinEquiv.symm i) <;> rfl
  map_smul' c u := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply]; cases (finSumFinEquiv.symm i) <;> rfl

theorem rhoL_apply (u : Tan d₀ d₁ m) (i : Fin (d₀ + d₁)) :
    rhoL u i = Sum.elim u.1 u.2.1 (finSumFinEquiv.symm i) := rfl

/-- The linear variables `x i`, `y j`. -/
def varL : Fin d₀ ⊕ Fin d₁ → Var d₀ d₁ m := Sum.elim Var.x Var.y

/-! ### Step 1 -/

variable {Ls : Fin m → PeriodPair} {H : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls))}

theorem expG_submodule_isSubgroup (V : Submodule ℂ (Tan d₀ d₁ m)) :
    IsSubgroupG (expG Ls '' (V : Set (Tan d₀ d₁ m))) where
  zero_mem := ⟨0, V.zero_mem, expG_zero Ls⟩
  add_mem := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, V.add_mem ha hb, expG_add Ls a b⟩
  neg_mem := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, V.neg_mem ha, (expGHom Ls).map_neg a⟩

/-- **Step 1: `π_A(T′)` is an abelian tangent space.** -/
theorem isAbelianTangent_map_piA (hH : IsSubgroupG H) (hc : IsZClosed H) :
    IsAbelianTangent Ls ((lieAlg Ls hH hc).map piA) := by
  classical
  set T := lieAlg Ls hH hc with hTdef
  set P := T.map (piA (d₀ := d₀) (d₁ := d₁) (m := m)) with hPdef
  set PA := P.map (inAbL (d₀ := d₀) (d₁ := d₁) (m := m))
  -- the subgroup `B`
  set S : Set (GPt ℂ d₀ d₁ (g2L Ls) (g3L Ls)) := expG Ls '' (PA : Set (Tan d₀ d₁ m))
  have hB : IsSubgroupG (zcl S) :=
    zcl_isSubgroup two_ne_zero (discr_g2L Ls) (expG_submodule_isSubgroup PA)
  have hBc : IsZClosed (zcl S) := isZClosed_zcl S
  have hPB : PA ≤ lieAlg Ls hB hBc := by
    intro v hv
    rw [mem_lieAlg]
    intro c
    rw [mem_Htil]
    exact subset_zcl S ⟨c • v, PA.smul_mem c hv, rfl⟩
  have hSB : vanish S ≤ vanish (H0 Ls hB hBc) := by
    rw [← vanish_zcl S]; exact vanish_antitone (H0_subset hB hBc)
  -- a transcendence basis of coordinates on `B⁰`
  have := vanish_H0_isPrime (Ls := Ls) hB hBc
  obtain ⟨ι, _, g, -, hb, hcard⟩ := exists_coord_transcendenceBasis (vanish (H0 Ls hB hBc))
  have hindB : ∀ Q : MvPolynomial ι ℂ, rename g Q ∈ vanish (H0 Ls hB hBc) → Q = 0 := by
    intro Q hQ
    refine (algebraicIndependent_iff.mp hb.1) Q ?_
    rw [← aeval_rename]
    exact (aeval_genPt_eq_zero_iff _).mpr hQ
  have hSpt : ∀ g' ∈ S, g'.1 = 0 ∧ ∀ j, g'.ym j = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨rfl, fun j => Units.ext (by simp [expG, GPt.ym, expU, inAbL])⟩
  have hgE : ∀ i, ∃ k c, g i = Var.e k c := by
    intro i
    rcases hgi : g i with j | j | j | ⟨k, c⟩
    · exfalso
      have hm : rename g (X i) ∈ vanish (H0 Ls hB hBc) := hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [rename_X, hgi, eval_X]; exact congrFun (hSpt g' hg').1 j)
      have := congrArg (eval fun _ => (1 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ vanish (H0 Ls hB hBc) :=
        hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, coords, coordsZ_y,
          (hSpt g' hg').2 j]
        simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ vanish (H0 Ls hB hBc) :=
        hSB (mem_vanish.mpr fun g' hg' lam => by
        rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, coords, coordsZ_z,
          (hSpt g' hg').2 j]
        simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exact ⟨k, c, rfl⟩
  -- `T′_L` and its coordinates
  set f := (piA (d₀ := d₀) (d₁ := d₁) (m := m)).comp T.subtype
  have hrange : LinearMap.range f = P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  set K0 := LinearMap.ker f
  set f0 := (rhoL (d₀ := d₀) (d₁ := d₁) (m := m)).comp (T.subtype.comp K0.subtype)
  have hf0 : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hA : ((w : T) : Tan d₀ d₁ m).2.2 = 0 := LinearMap.mem_ker.mp w.2
    have hx : ∀ i, ((w : T) : Tan d₀ d₁ m).1 i = 0 := fun i => by
      have := congrFun hw (finSumFinEquiv (Sum.inl i))
      simpa [f0, rhoL_apply] using this
    have hy : ∀ j, ((w : T) : Tan d₀ d₁ m).2.1 j = 0 := fun j => by
      have := congrFun hw (finSumFinEquiv (Sum.inr j))
      simpa [f0, rhoL_apply] using this
    have : ((w : T) : Tan d₀ d₁ m) = 0 := Prod.ext (funext hx) (Prod.ext (funext hy) hA)
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ιL, -, hsurjL⟩ := exists_coord_surj (LinearMap.range f0)
  have hr : finrank ℂ (LinearMap.range f0) = finrank ℂ K0 := LinearMap.finrank_range_of_inj hf0
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  -- the combined family of coordinates
  set σL := fun l => finSumFinEquiv.symm (ιL l)
  set e := Sum.elim (fun l => varL (m := m) (σL l)) g
  set s : Fin (finrank ℂ (LinearMap.range f0)) → Set ℂ :=
    fun l => Sum.elim (fun _ => univ) (fun _ => {0}ᶜ) (σL l)
  have hX : ∀ Q : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0))) ℂ,
      (∀ x ∈ Set.pi univ s, eval x Q = 0) → Q = 0 := by
    intro Q hQ
    refine funext_set s (fun l => ?_) fun x hx => by rw [hQ x hx, map_zero]
    change (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ) (σL l) : Set ℂ).Infinite
    cases σL l
    · exact Set.infinite_univ
    · exact (Set.finite_singleton 0).infinite_compl
  set Y : Set (ι → ℂ) := {y | ∃ v ∈ PA, ∃ lam : Fin m → ℂˣ, y = coords (expG Ls v) lam ∘ g}
  have hY : ∀ Q : MvPolynomial ι ℂ, (∀ y ∈ Y, eval y Q = 0) → Q = 0 := by
    intro Q hQ
    refine hindB Q (hSB (mem_vanish.mpr fun g' hg' lam => ?_))
    obtain ⟨v, hv, rfl⟩ := hg'
    rw [eval_rename]
    exact hQ _ ⟨v, hv, lam, rfl⟩
  have := vanish_H0_isPrime (Ls := Ls) hH hc
  have hind : ∀ R : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0)) ⊕ ι) ℂ,
      rename e R ∈ vanish (H0 Ls hH hc) → R = 0 := by
    intro R hRm
    refine eq_zero_of_eval_elim hX hY fun x hx y hy => ?_
    obtain ⟨v, hv, lam, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
    set y' : Fin (finrank ℂ (LinearMap.range f0)) → ℂ := fun l =>
      Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j) (σL l)
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hsurjL y'
    have hwA : ((w : T) : Tan d₀ d₁ m).2.2 = 0 := LinearMap.mem_ker.mp w.2
    have hpt : Sum.elim x (coords (expG Ls (inAbL (piA u))) lam ∘ g) =
        coords (expG Ls (u + ((w : T) : Tan d₀ d₁ m))) lam ∘ e := by
      funext t
      cases t with
      | inl l =>
        have hl : Sum.elim ((w : T) : Tan d₀ d₁ m).1 ((w : T) : Tan d₀ d₁ m).2.1 (σL l) =
            Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j) (σL l) :=
          hw l
        have hxl : x l ∈ s l := hx l (Set.mem_univ l)
        change x l = coords (expG Ls (u + ((w : T) : Tan d₀ d₁ m))) lam (varL (σL l))
        simp only [s] at hxl
        generalize σL l = q at hl hxl ⊢
        cases q with
        | inl i =>
          change ((w : T) : Tan d₀ d₁ m).1 i = x l - u.1 i at hl
          change x l = u.1 i + ((w : T) : Tan d₀ d₁ m).1 i
          rw [hl]; ring
        | inr j =>
          change ((w : T) : Tan d₀ d₁ m).2.1 j = Complex.log (x l) - u.2.1 j at hl
          change x l ≠ 0 at hxl
          change x l = Complex.exp (u.2.1 j + ((w : T) : Tan d₀ d₁ m).2.1 j)
          rw [hl, add_sub_cancel, Complex.exp_log hxl]
      | inr i =>
        obtain ⟨k, c, hkc⟩ := hgE i
        simp only [Sum.elim_inr, Function.comp_apply, e, hkc, coords, coordsZ_e]
        have : (u + ((w : T) : Tan d₀ d₁ m)).2.2 k = u.2.2 k := by
          simp [hwA]
        change (lam k : ℂ) * rep (expE (Ls k) (u.2.2 k)) c =
          (lam k : ℂ) * rep (expE (Ls k) ((u + ((w : T) : Tan d₀ d₁ m)).2.2 k)) c
        rw [this]
    rw [hpt, ← eval_rename]
    exact mem_vanish.mp hRm _ (expG_mem_H0 hH hc (T.add_mem hu (w : T).2)) lam
  -- the count
  have hcount := card_le_trdeg_of_indep (vanish (H0 Ls hH hc)) e hind
  rw [trdeg_H0 hH hc, Fintype.card_sum, Fintype.card_fin] at hcount
  have hι : Fintype.card ι = finrank ℂ (lieAlg Ls hB hBc) + m := by
    have := congrArg Cardinal.toNat hcard
    rwa [Cardinal.toNat_natCast, trdeg_H0 hB hBc] at this
  have hPA : finrank ℂ PA = finrank ℂ P :=
    (Submodule.equivMapOfInjective _ inAbL_injective P).finrank_eq.symm
  have hTT : finrank ℂ T = finrank ℂ (lieAlg Ls hH hc) := rfl
  have hle : finrank ℂ (lieAlg Ls hB hBc) ≤ finrank ℂ PA := by
    have hK : finrank ℂ (LinearMap.ker f) = finrank ℂ K0 := rfl
    omega
  have heq : PA = lieAlg Ls hB hBc := Submodule.eq_of_le_of_finrank_le hPB hle
  obtain ⟨t, hab, ht, -⟩ := exists_abelianTangent_Htil hB hBc
  have htP : t = P := by
    ext z
    rw [ht z, ← heq, Submodule.mem_map]
    constructor
    · rintro ⟨z', hz', h⟩
      rwa [← inAbL_injective h]
    · intro h; exact ⟨z, h, rfl⟩
  rw [← htP]
  exact hab

end LSG.ME
