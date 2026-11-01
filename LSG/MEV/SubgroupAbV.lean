import Mathlib
import LSG.MEV.SubgroupCompV
import LSG.MEV.SubgroupClass
import LSG.ME.ProductRat

/-!
# Gap G1: `π_Z(T′)` is an abelian tangent space, and the unconditional classification

For a Zariski-closed subgroup `H ⊆ G̃(ℂ)` with Lie algebra `T′ = lieAlg H` and base projection
`π_Z : T_G̃ → ℂ^m`, **`isAbelianTangent_map_piZ`**: `P = π_Z(T′)` is `Λ`-rational.

Proof (transcendence-degree count, as `LSG.ME.isAbelianTangent_map_piA`, plan of STAGE5_MEV §6.5).
* `B = zcl (exp_G (0 × 0 × P))` in the abelian group `G` (`LSG.ME`), with `0 × 0 × P ⊆ lieAlg B`.
  `B⁰` has a transcendence basis of coordinate functions, all elliptic cone coordinates
  `e k c` (`c : Fin 3`), of size `dim lieAlg B + m` (`LSG.ME.trdeg_H0`).
* `K₀ = T′ ∩ ker π_Z` projects onto `r = dim K₀` of the coordinates `x_i`, `b_j`, `w_k` (linear and
  fibre), `LSG.ME.exists_coord_surj`.
* The corresponding functions on `G̃` — `X_i`, `Y_j`, and the fibre coordinate `T₁` (blocks on
  which `P` is not identically `0`, where the base of a *generic* point is affine) or `T₃` (blocks
  with `P_k = 0`, where the base is `O`) — together with the base coordinates `U_k, V_k, W_k`
  chosen on `B⁰` are algebraically independent modulo `vanish H⁰`: at `exp(u + w)`, `u ∈ T′`
  generic, `w ∈ K₀`, the base coordinates only depend on `π_Z u`, while the chosen linear and fibre
  coordinates sweep out `ℂ^a × (ℂˣ)^b × ℂ^c`. The generic points are dense enough by **`dens_ME`**
  (the entire lift `ellN`, a vector `v ∈ P` with `v_k ≠ 0` on the active blocks, and a countable
  bad set on the line `z + t v`).
* Hence `r + dim lieAlg B + m ≤ trdeg H⁰ = dim T′ + m = r + dim P + m`, so `0 × 0 × P = lieAlg B`,
  whose abelian part is an abelian tangent space (`LSG.ME.exists_abelianTangent_Htil`).

Then **`exists_subgroupV`**: `exists_subgroupPreV` without the hypothesis `hab`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass Set Module
open LSG.W88 (IsAbelianTangent)
open LSG.AuxV (ellN)
open LSG.W88.Vec (vecIncl torIncl g2Incl)

namespace LSG.MEV

noncomputable section

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

/-! ### Coordinates of `exp` -/

theorem coords_expGV_e (p : TanG d₀ d₁ m) (lam : Fin m → ℂˣ) (k : Fin m) (i : Fin 5) :
    coords (expGV Ls p) lam (.e k i) = lam k * expN (Ls k) (p.2.2.1 k) (p.2.2.2 k) i := by
  simp only [coords, coordsZ_e]
  rw [show (expGV Ls p).2.2 k = expV (Ls k) (p.2.2.1 k, p.2.2.2 k) from rfl, repV_expV]

theorem coords_expGV_y (p : TanG d₀ d₁ m) (lam : Fin m → ℂˣ) (j : Fin d₁) :
    coords (expGV Ls p) lam (.y j) = Complex.exp (p.2.1 j) := by
  simp [coords, expGV, GPtV.ym, LSG.ME.expU]

theorem expN_base (L : PeriodPair) (z w : ℂ) (i : Fin 3) :
    expN L z w i.castSucc.castSucc = rep (expE L z) i := by
  have h := Pe_repV (expV L (z, w))
  rw [repV_expV] at h
  have := congrFun h i
  rwa [Pe_apply] at this

theorem ellN_base (L : PeriodPair) (z : ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ i : Fin 3, ellN L z 0 i.castSucc.castSucc = c * rep (expE L z) i := by
  obtain ⟨c, hc0, hc⟩ := LSG.AuxV.ellN_eq_smul_expN L z 0
  exact ⟨c, hc0, fun i => by rw [hc, Pi.smul_apply, smul_eq_mul, expN_base]⟩

/-! ### Density of generic points -/

/-- Block `k` is **active** for `P`: the `k`-th coordinate is not identically `0` on `P`. -/
def actB (P : Submodule ℂ (Fin m → ℂ)) (k : Fin m) : Prop := ∃ z ∈ P, z k ≠ 0

/-- A vector of `P` that is nonzero on every active block. -/
theorem exists_avoid (P : Submodule ℂ (Fin m → ℂ)) : ∃ v ∈ P, ∀ k, actB P k → v k ≠ 0 := by
  classical
  let p : {k // actB P k} → Submodule ℂ P := fun k =>
    LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) k.1).comp P.subtype)
  have h₁ : ∀ k, p k ≠ ⊤ := by
    rintro ⟨k, z, hz, hzk⟩ htop
    have : (⟨z, hz⟩ : P) ∈ p ⟨k, z, hz, hzk⟩ := htop ▸ Submodule.mem_top
    exact hzk (by simpa [p] using this)
  have h₂ : (Finset.univ : Finset {k // actB P k}).card < ENat.card ℂ := by
    rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h₁ h₂
  obtain ⟨v, -, hv⟩ := Set.exists_of_ssubset hss
  refine ⟨v.1, v.2, fun k hk hvk => hv ?_⟩
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨k, hk⟩, by simpa [p] using hvk⟩

theorem countable_line_lattice (L : PeriodPair) (a b : ℂ) (hb : b ≠ 0) :
    {t : ℂ | a + t * b ∈ L.lattice}.Countable := by
  refine ((countable_lattice L).image fun l => (l - a) / b).mono fun t ht => ?_
  exact ⟨a + t * b, ht, by field_simp; ring⟩

/-- **Density** (on the abelian side): a polynomial vanishing at the cone points of `exp(0 × 0 × z)`
for all generic `z ∈ P` (lattice-free on the active blocks) vanishes for all `z ∈ P`. -/
theorem dens_ME (P : Submodule ℂ (Fin m → ℂ)) (Q : MvPolynomial (LSG.ME.Var d₀ d₁ m) ℂ)
    (h : ∀ z ∈ P, (∀ k, actB P k → z k ∉ (Ls k).lattice) → ∀ lam : Fin m → ℂˣ,
      eval (LSG.ME.coords (LSG.ME.expG Ls (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) z)) lam) Q = 0)
    {z : Fin m → ℂ} (hz : z ∈ P) (lam : Fin m → ℂˣ) :
    eval (LSG.ME.coords (LSG.ME.expG Ls (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) z)) lam) Q = 0 := by
  classical
  obtain ⟨v, hvP, hv⟩ := exists_avoid P
  choose c hc0 hc using fun k => ellN_base (Ls k) (z k)
  let μ : Fin m → ℂ := fun k => lam k / c k
  have hμ0 : ∀ k, μ k ≠ 0 := fun k => div_ne_zero (lam k).ne_zero (hc0 k)
  let Y : ℂ → LSG.ME.Var d₀ d₁ m → ℂ := fun t v' => match v' with
    | .x _ => 0
    | .y _ => 1
    | .z _ => 1
    | .e k i => μ k * ellN (Ls k) (z k + t * v k) 0 i.castSucc.castSucc
  have hY : ∀ v', Differentiable ℂ fun t => Y t v' := by
    intro v'
    cases v' with
    | x i => exact differentiable_const _
    | y j => exact differentiable_const _
    | z j => exact differentiable_const _
    | e k i =>
      show Differentiable ℂ fun t : ℂ => μ k * ellN (Ls k) (z k + t * v k) 0 i.castSucc.castSucc
      have h1 : Differentiable ℂ fun t : ℂ => (z k + t * v k, (0 : ℂ)) := by fun_prop
      have h2 := (LSG.AuxV.differentiable_ellN (Ls k) i.castSucc.castSucc).comp h1
      simp only [Function.comp_def] at h2
      exact h2.const_mul _
  have hF : Continuous fun t => eval (Y t) Q := (differentiable_eval_of hY Q).continuous
  let S : Set ℂ := ⋃ k, {t | actB P k ∧ z k + t * v k ∈ (Ls k).lattice}
  have hS : S.Countable := by
    refine Set.countable_iUnion fun k => ?_
    by_cases hk : actB P k
    · exact (countable_line_lattice (Ls k) (z k) (v k) (hv k hk)).mono fun t ht => ht.2
    · exact (Set.countable_empty).mono fun t ht => hk ht.1
  have hzero : EqOn (fun t => eval (Y t) Q) (fun _ => 0) Sᶜ := by
    intro t ht
    have hgen : ∀ k, actB P k → (z + t • v) k ∉ (Ls k).lattice := by
      intro k hk hmem
      apply ht
      exact Set.mem_iUnion.mpr ⟨k, hk, by simpa [mul_comm] using hmem⟩
    choose c' hc'0 hc' using fun k => ellN_base (Ls k) ((z + t • v) k)
    let lam' : Fin m → ℂˣ := fun k => Units.mk0 (μ k * c' k) (mul_ne_zero (hμ0 k) (hc'0 k))
    have hYt : Y t = LSG.ME.coords (LSG.ME.expG Ls (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) (z + t • v)))
        lam' := by
      funext v'
      cases v' with
      | x i => rfl
      | y j => simp [Y, LSG.ME.coords, LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU, LSG.ME.inAb]
      | z j => simp [Y, LSG.ME.coords, LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU, LSG.ME.inAb]
      | e k i =>
        have := hc' k i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
        show μ k * ellN (Ls k) (z k + t * v k) 0 i.castSucc.castSucc =
          (μ k * c' k) * rep (expE (Ls k) (z k + t * v k)) i
        rw [this, mul_assoc]
    show eval (Y t) Q = 0
    rw [hYt]
    exact h _ (P.add_mem hz (P.smul_mem t hvP)) hgen lam'
  have hall := hF.ext_on (hS.dense_compl ℂ) continuous_const hzero
  have h0 : eval (Y 0) Q = 0 := congrFun hall 0
  rw [← h0]
  congr 2
  funext v'
  cases v' with
  | x i => rfl
  | y j => simp [Y, LSG.ME.coords, LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU, LSG.ME.inAb]
  | z j => simp [Y, LSG.ME.coords, LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU, LSG.ME.inAb]
  | e k i =>
    simp only [Y, zero_mul, add_zero, hc k i, LSG.ME.coords, LSG.ME.coordsZ_e, μ]
    rw [← mul_assoc, div_mul_cancel₀ _ (hc0 k)]; rfl

/-! ### Coordinates on `T′ ∩ ker π_Z` -/

/-- Decoding `Fin (d₀ + d₁ + m)` as `(Fin d₀ ⊕ Fin d₁) ⊕ Fin m`. -/
def decV (i : Fin (d₀ + d₁ + m)) : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m :=
  (finSumFinEquiv.symm i).map finSumFinEquiv.symm id

/-- The linear and fibre coordinates `(a, b, w)` of a tangent vector. -/
def rhoV : TanG d₀ d₁ m →ₗ[ℂ] (Fin (d₀ + d₁ + m) → ℂ) where
  toFun u i := Sum.elim (Sum.elim u.1 u.2.1) u.2.2.2 (decV i)
  map_add' u v := by
    funext i; simp only [Pi.add_apply]; rcases decV i with (_ | _) | _ <;> rfl
  map_smul' c u := by
    funext i; simp only [Pi.smul_apply, RingHom.id_apply]; rcases decV i with (_ | _) | _ <;> rfl

theorem decV_surj (q : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m) : ∃ i, decV (d₀ := d₀) (d₁ := d₁) (m := m) i = q := by
  rcases q with (i | j) | k
  · exact ⟨finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))), by simp [decV]⟩
  · exact ⟨finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr j))), by simp [decV]⟩
  · exact ⟨finSumFinEquiv (Sum.inr k), by simp [decV]⟩

/-- The abelian variables inside `Var`. -/
def mvV : LSG.ME.Var d₀ d₁ m → Var d₀ d₁ m
  | .x i => .x i
  | .y j => .y j
  | .z j => .z j
  | .e k c => .e k c.castSucc.castSucc

/-! ### Step G1 -/

/-- **G1: `π_Z(T′)` is an abelian tangent space.** -/
theorem isAbelianTangent_map_piZ {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H)
    (hc : IsZClosed H) : IsAbelianTangent Ls ((lieAlg Ls hH).map piZ) := by
  classical
  set T := lieAlg Ls hH with hTdef
  set P := T.map (piZ (d₀ := d₀) (d₁ := d₁) (m := m)) with hPdef
  set PA := P.map (LSG.ME.inAbL (d₀ := d₀) (d₁ := d₁) (m := m))
  -- the abelian subgroup `B`
  set S : Set (LSG.ME.GPt ℂ d₀ d₁ (LSG.ME.g2L Ls) (LSG.ME.g3L Ls)) :=
    LSG.ME.expG Ls '' (PA : Set (LSG.W88.Tan d₀ d₁ m))
  have hB : LSG.ME.IsSubgroupG (LSG.ME.zcl S) :=
    LSG.ME.zcl_isSubgroup two_ne_zero (LSG.ME.discr_g2L Ls) (LSG.ME.expG_submodule_isSubgroup PA)
  have hBc : LSG.ME.IsZClosed (LSG.ME.zcl S) := LSG.ME.isZClosed_zcl S
  have hPB : PA ≤ LSG.ME.lieAlg Ls hB hBc := by
    intro v hv
    rw [LSG.ME.mem_lieAlg]
    intro c
    rw [LSG.ME.mem_Htil]
    exact LSG.ME.subset_zcl S ⟨c • v, PA.smul_mem c hv, rfl⟩
  have hSB : LSG.ME.vanish S ≤ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) := by
    rw [← LSG.ME.vanish_zcl S]; exact LSG.ME.vanish_antitone (LSG.ME.H0_subset hB hBc)
  have := LSG.ME.vanish_H0_isPrime (Ls := Ls) hB hBc
  obtain ⟨ι, _, g, -, hb, hcard⟩ :=
    LSG.ME.exists_coord_transcendenceBasis (LSG.ME.vanish (LSG.ME.H0 Ls hB hBc))
  have hindB : ∀ Q : MvPolynomial ι ℂ, rename g Q ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) →
      Q = 0 := by
    intro Q hQ
    refine (algebraicIndependent_iff.mp hb.1) Q ?_
    rw [← aeval_rename]
    exact (LSG.ME.aeval_genPt_eq_zero_iff _).mpr hQ
  have hSpt : ∀ g' ∈ S, g'.1 = 0 ∧ ∀ j, g'.ym j = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨rfl, fun j => Units.ext (by simp [LSG.ME.expG, LSG.ME.GPt.ym, LSG.ME.expU,
      LSG.ME.inAbL])⟩
  have hgE : ∀ i, ∃ k c, g i = LSG.ME.Var.e k c := by
    intro i
    rcases hgi : g i with j | j | j | ⟨k, c⟩
    · exfalso
      have hm : rename g (X i) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [rename_X, hgi, eval_X]; exact congrFun (hSpt g' hg').1 j)
      have := congrArg (eval fun _ => (1 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.ME.coords,
            LSG.ME.coordsZ_y, (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exfalso
      have hm : rename g (X i - 1) ∈ LSG.ME.vanish (LSG.ME.H0 Ls hB hBc) :=
        hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => by
          rw [map_sub, rename_X, hgi, map_one, map_sub, eval_X, map_one, LSG.ME.coords,
            LSG.ME.coordsZ_z, (hSpt g' hg').2 j]
          simp)
      have := congrArg (eval fun _ => (0 : ℂ)) (hindB _ hm)
      simp at this
    · exact ⟨k, c, rfl⟩
  -- `K₀ = T′ ∩ ker π_Z` and its coordinates
  set f := (piZ (d₀ := d₀) (d₁ := d₁) (m := m)).comp T.subtype
  have hrange : LinearMap.range f = P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  set K0 := LinearMap.ker f
  set f0 := (rhoV (d₀ := d₀) (d₁ := d₁) (m := m)).comp (T.subtype.comp K0.subtype)
  have hf0 : Function.Injective f0 := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hZ : ((w : T) : TanG d₀ d₁ m).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hco : ∀ q, Sum.elim (Sum.elim ((w : T) : TanG d₀ d₁ m).1 ((w : T) : TanG d₀ d₁ m).2.1)
        ((w : T) : TanG d₀ d₁ m).2.2.2 q = 0 := fun q => by
      obtain ⟨i, rfl⟩ := decV_surj q
      exact congrFun hw i
    have : ((w : T) : TanG d₀ d₁ m) = 0 :=
      Prod.ext (funext fun i => hco (.inl (.inl i)))
        (Prod.ext (funext fun j => hco (.inl (.inr j)))
          (Prod.ext hZ (funext fun k => hco (.inr k))))
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨ιL, -, hsurjL⟩ := LSG.ME.exists_coord_surj (LinearMap.range f0)
  have hr : finrank ℂ (LinearMap.range f0) = finrank ℂ K0 := LinearMap.finrank_range_of_inj hf0
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  -- the combined family of coordinates
  have hPk : ∀ k, ¬ actB P k → ∀ u ∈ T, u.2.2.1 k = 0 := by
    intro k hk u hu
    by_contra hne
    exact hk ⟨piZ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, hne⟩
  let fcV : Fin m → Var d₀ d₁ m := fun k => if actB P k then .e k 3 else .e k 4
  let varV : (Fin d₀ ⊕ Fin d₁) ⊕ Fin m → Var d₀ d₁ m :=
    Sum.elim (Sum.elim Var.x Var.y) fcV
  set e := Sum.elim (fun l => varV (decV (ιL l))) (fun i => mvV (g i))
  set s : Fin (finrank ℂ (LinearMap.range f0)) → Set ℂ :=
    fun l => Sum.elim (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ)) (fun _ => univ) (decV (ιL l))
  have hX : ∀ Q : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0))) ℂ,
      (∀ x ∈ Set.pi univ s, eval x Q = 0) → Q = 0 := by
    intro Q hQ
    refine funext_set s (fun l => ?_) fun x hx => by rw [hQ x hx, map_zero]
    change (Sum.elim (Sum.elim (fun _ => univ) (fun _ => {0}ᶜ)) (fun _ => univ)
      (decV (ιL l)) : Set ℂ).Infinite
    rcases decV (ιL l) with (_ | _) | _
    · exact Set.infinite_univ
    · exact (Set.finite_singleton 0).infinite_compl
    · exact Set.infinite_univ
  set Y : Set (ι → ℂ) := {y | ∃ u ∈ T, (∀ k, actB P k → u.2.2.1 k ∉ (Ls k).lattice) ∧
    ∃ lam : Fin m → ℂˣ, y = LSG.ME.coords (LSG.ME.expG Ls
      (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) (piZ u))) lam ∘ g}
  have hY : ∀ Q : MvPolynomial ι ℂ, (∀ y ∈ Y, eval y Q = 0) → Q = 0 := by
    intro Q hQ
    refine hindB Q (hSB (LSG.ME.mem_vanish.mpr fun g' hg' lam => ?_))
    obtain ⟨v, hv, rfl⟩ := hg'
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    refine dens_ME P (rename g Q) (fun z' hz' hgen lam' => ?_) hz lam
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz'
    rw [eval_rename]
    exact hQ _ ⟨u, hu, hgen, lam', rfl⟩
  have := vanish_H0_isPrime (Ls := Ls) hH
  have hind : ∀ R : MvPolynomial (Fin (finrank ℂ (LinearMap.range f0)) ⊕ ι) ℂ,
      rename e R ∈ vanish (H0 Ls hH) → R = 0 := by
    intro R hRm
    refine LSG.ME.eq_zero_of_eval_elim hX hY fun x hx y hy => ?_
    obtain ⟨u, hu, hgen, lam, rfl⟩ := hy
    set y' : Fin (finrank ℂ (LinearMap.range f0)) → ℂ := fun l =>
      Sum.elim (Sum.elim (fun i => x l - u.1 i) (fun j => Complex.log (x l) - u.2.1 j))
        (fun k => x l / lam k - u.2.2.2 k + zeta (Ls k) (u.2.2.1 k)) (decV (ιL l))
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ := hsurjL y'
    have hwZ : ((w : T) : TanG d₀ d₁ m).2.2.1 = 0 := LinearMap.mem_ker.mp w.2
    have hpt : Sum.elim x (LSG.ME.coords (LSG.ME.expG Ls
        (LSG.ME.inAb (d₀ := d₀) (d₁ := d₁) (piZ u))) lam ∘ g) =
        coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam ∘ e := by
      funext t
      cases t with
      | inl l =>
        have hl := hw l
        have hxl : x l ∈ s l := hx l (Set.mem_univ l)
        change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (varV (decV (ιL l)))
        simp only [s] at hxl
        change Sum.elim (Sum.elim ((w : T) : TanG d₀ d₁ m).1 ((w : T) : TanG d₀ d₁ m).2.1)
          ((w : T) : TanG d₀ d₁ m).2.2.2 (decV (ιL l)) = y' l at hl
        simp only [y'] at hl
        generalize decV (ιL l) = q at hl hxl ⊢
        rcases q with (i | j) | k
        · change ((w : T) : TanG d₀ d₁ m).1 i = x l - u.1 i at hl
          change x l = u.1 i + ((w : T) : TanG d₀ d₁ m).1 i
          rw [hl]; ring
        · change ((w : T) : TanG d₀ d₁ m).2.1 j = Complex.log (x l) - u.2.1 j at hl
          change x l ≠ 0 at hxl
          change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (.y j)
          rw [coords_expGV_y]
          show x l = Complex.exp (u.2.1 j + ((w : T) : TanG d₀ d₁ m).2.1 j)
          rw [hl, add_sub_cancel, Complex.exp_log hxl]
        · change ((w : T) : TanG d₀ d₁ m).2.2.2 k =
            x l / lam k - u.2.2.2 k + zeta (Ls k) (u.2.2.1 k) at hl
          have hz : (u + ((w : T) : TanG d₀ d₁ m)).2.2.1 k = u.2.2.1 k := by
            simp [hwZ]
          have hw' : (u + ((w : T) : TanG d₀ d₁ m)).2.2.2 k - zeta (Ls k) (u.2.2.1 k) =
              x l / lam k := by
            simp only [Prod.snd_add, Pi.add_apply, hl]; ring
          change x l = coords (expGV Ls (u + ((w : T) : TanG d₀ d₁ m))) lam (fcV k)
          simp only [fcV]
          split_ifs with hk
          · rw [coords_expGV_e, hz, expN_of_notMem _ (hgen k hk)]
            simp only [ptAff, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
            rw [hw', mul_div_cancel₀ _ (lam k).ne_zero]
          · have h0 := hPk k hk u hu
            rw [coords_expGV_e, hz]
            have hmem : u.2.2.1 k ∈ (Ls k).lattice := by rw [h0]; exact (Ls k).lattice.zero_mem
            simp only [expN, hmem, ↓reduceIte, ptO, Matrix.cons_val_four, Matrix.tail_cons,
              Matrix.head_cons]
            rw [hw', mul_div_cancel₀ _ (lam k).ne_zero]
      | inr i =>
        obtain ⟨k, c, hkc⟩ := hgE i
        simp only [Sum.elim_inr, Function.comp_apply, e, hkc, mvV]
        rw [coords_expGV_e, expN_base]
        simp [hwZ, LSG.ME.coords, LSG.ME.expG, LSG.ME.inAb]
        rfl
    rw [hpt, ← eval_rename]
    exact mem_vanish.mp hRm _ (expGV_mem_H0 hH (T.add_mem hu (w : T).2)) lam
  -- the count
  have hcount := LSG.ME.card_le_trdeg_of_indep (vanish (H0 Ls hH)) e hind
  rw [trdeg_H0 hH hc, Fintype.card_sum, Fintype.card_fin] at hcount
  have hι : Fintype.card ι = finrank ℂ (LSG.ME.lieAlg Ls hB hBc) + m := by
    have := congrArg Cardinal.toNat hcard
    rwa [Cardinal.toNat_natCast, LSG.ME.trdeg_H0 hB hBc] at this
  have hPA : finrank ℂ PA = finrank ℂ P :=
    (Submodule.equivMapOfInjective _ LSG.ME.inAbL_injective P).finrank_eq.symm
  have hle : finrank ℂ (LSG.ME.lieAlg Ls hB hBc) ≤ finrank ℂ PA := by
    have hK : finrank ℂ (LinearMap.ker f) = finrank ℂ K0 := rfl
    have hTT : finrank ℂ T = finrank ℂ (lieAlg Ls hH) := rfl
    omega
  have heq : PA = LSG.ME.lieAlg Ls hB hBc := Submodule.eq_of_le_of_finrank_le hPB hle
  obtain ⟨t, hab, ht, -⟩ := LSG.ME.exists_abelianTangent_Htil hB hBc
  have htP : t = P := by
    ext z
    rw [ht z, ← heq, Submodule.mem_map]
    constructor
    · rintro ⟨z', hz', h⟩
      rwa [← LSG.ME.inAbL_injective h]
    · intro h; exact ⟨z, h, rfl⟩
  rw [← htP]
  exact hab

/-! ### The unconditional classification -/

/-- **The classification of closed subgroups of `G̃`**: `T′ = lieAlg H` is the tangent space of a
member of the VECEXT family (without `ℚ̄`-rationality of `Γ`), with no further hypothesis. -/
theorem exists_subgroupV {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    ∃ S : SubgroupPreV (d₀ := d₀) (d₁ := d₁) Ls 1, S.tan = lieAlg Ls hH ∧
      S.U = StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H)) ∧
      S.t = (lieAlg Ls hH).map piZ ∧ S.gam = (lieAlg Ls hH).comap vecIncl :=
  exists_subgroupPreV hH hc (isAbelianTangent_map_piZ hH hc)

/-- The decomposition `T′ = Γ ⊕ U^⊥ ⊕ perTanId(π_Z T′)`, unconditionally. -/
theorem lieAlg_eq_tanV {H : Set (GPtV d₀ d₁ Ls)} (hH : IsSubgroupG H) (hc : IsZClosed H) :
    lieAlg Ls hH =
      ((lieAlg Ls hH).comap vecIncl).map vecIncl ⊔
        (LSG.W88.torusLie (StrongSix.M2.qspan (StrongSix.M2.latt (HL Ls H)))).map torIncl ⊔
        (LSG.W88.Vec.perTan Ls 1 ((lieAlg Ls hH).map piZ)).map g2Incl :=
  lieAlg_eq_tan hH hc (isAbelianTangent_map_piZ hH hc)

end

end LSG.MEV
