import Mathlib
import LSG.ME.StabG
import LSG.ME.Elimination
import StrongSix.M2.Classify

/-!
# The linear projection of a Zariski-closed subgroup (STAGE2 §5, item 2)

For a Zariski-closed `H ⊆ G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, its image under the projection
`π_L : G → G_a^{d₀} × G_m^{d₁}` (StrongSix's `GPt K d₀ d₁`) is Zariski closed (`projL_closed`),
and if `H` is a subgroup then `π_L(H) = V × T_Λ` (`projL_eq_prodSet`, via StrongSix's `classify`).

* `wV`: the multigrading by elliptic blocks (`e k c ↦ Pi.single k 1`, other variables `0`);
  `wE k` its `k`-th entry.
* `eval_scale`: evaluation of a weighted-homogeneous polynomial at a rescaled point.
* **`comp_mem_vanish`**: `vanish E` is homogeneous in each elliptic block (`K` infinite).
* **`exists_homog`**: a polynomial of `vanish E` nonzero at `x` can be replaced by a
  multihomogeneous one, still nonzero at `x`.
* **`homogVanish`**: the multihomogeneous elements of `vanish H`; for `H` Zariski closed,
  `g ∉ H` iff some element of `homogVanish H` is nonzero at **every** cone representative of `g`.
* **`projL_closed`**: elimination along the cone blocks (`isClosed_proj_sigma`).
* **`projL_eq_prodSet`**: `π_L(H) = prodSet V Λ` (`CharZero K`).
-/

universe u

open MvPolynomial LSG.Elliptic

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Multigrading by elliptic blocks -/

/-- The multigrading by elliptic blocks. -/
def wV : Var d₀ d₁ m → Fin m → ℕ
  | .e k _ => Pi.single k 1
  | _ => 0

/-- The grading by the `k`-th elliptic block. -/
def wE (k : Fin m) : Var d₀ d₁ m → ℕ := fun v => wV v k

theorem weight_wE (k : Fin m) (s : Var d₀ d₁ m →₀ ℕ) :
    Finsupp.weight (wE k) s = Finsupp.weight wV s k := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wE]

theorem isWeightedHomogeneous_wV {Q : MvPolynomial (Var d₀ d₁ m) K} {n : Fin m → ℕ}
    (h : ∀ k, IsWeightedHomogeneous (wE k) Q (n k)) : IsWeightedHomogeneous wV Q n := by
  intro s hs
  funext k
  rw [← weight_wE]; exact h k hs

theorem homog_of_eq {σ M : Type*} [AddCommMonoid M] {w : σ → M}
    {φ : MvPolynomial σ K} {n n' : M} (h : IsWeightedHomogeneous w φ n) (e : n = n') :
    IsWeightedHomogeneous w φ n' := e ▸ h

/-- Components for one grading stay homogeneous for another. -/
theorem isWeightedHomogeneous_comp {σ M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    {w : σ → M} {w' : σ → N} {φ : MvPolynomial σ K} {n' : N}
    (h : IsWeightedHomogeneous w' φ n') (n : M) :
    IsWeightedHomogeneous w' (weightedHomogeneousComponent w n φ) n' := by
  classical
  intro s hs
  rw [coeff_weightedHomogeneousComponent] at hs
  split_ifs at hs
  · exact h hs
  · exact absurd rfl hs

/-- **Evaluation at a rescaled point.** -/
theorem eval_scale {σ κ : Type*} [Fintype σ] [Fintype κ] (W : σ → κ → ℕ) (μ : κ → K) (x : σ → K)
    {Q : MvPolynomial σ K} {d : κ → ℕ} (hQ : IsWeightedHomogeneous W Q d) :
    eval (fun v => (∏ k, μ k ^ W v k) * x v) Q = (∏ k, μ k ^ d k) * eval x Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hQ (mem_support_iff.mp hs)
  simp only [mul_pow, Finset.prod_mul_distrib]
  have : (∏ v, (∏ k, μ k ^ W v k) ^ s v) = ∏ k, μ k ^ d k := by
    simp_rw [← Finset.prod_pow, ← pow_mul, Finset.prod_comm (s := (Finset.univ : Finset σ)),
      Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
    exact Finset.sum_congr rfl fun v _ => by simp [mul_comm]
  rw [this]; ring

/-- Rescaling the cone coordinates. -/
theorem coords_mul (g : GPt K d₀ d₁ g₂ g₃) (μ lam : Fin m → Kˣ) :
    coords g (fun k => μ k * lam k) =
      fun v => (∏ k, ((μ k : Kˣ) : K) ^ wV v k) * coords g lam v := by
  funext v
  cases v with
  | x i => simp [coords, wV]
  | y j => simp [coords, wV]
  | z j => simp [coords, wV]
  | e k c =>
    simp only [coords, coordsZ_e, wV, Units.val_mul, Pi.single_apply, pow_ite, pow_one,
      pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring

/-! ### Homogeneous components of `vanish E` -/

/-- **`vanish E` is homogeneous in each elliptic block.** -/
theorem comp_mem_vanish [Infinite K] {E : Set (GPt K d₀ d₁ g₂ g₃)}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ vanish E) (k : Fin m) (n : ℕ) :
    weightedHomogeneousComponent (wE k) n P ∈ vanish E := by
  classical
  refine mem_vanish.mpr fun g hg lam => ?_
  set x := coords g lam
  have hfin := weightedHomogeneousComponent_finsupp (w := wE k) P
  set T := hfin.toFinset
  have hsum : P = ∑ i ∈ T, weightedHomogeneousComponent (wE k) i P := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (wE k) P]
    exact finsum_eq_sum _ hfin
  -- the univariate polynomial `Σ_i c_i t^i`
  set f : Polynomial K := ∑ i ∈ T, Polynomial.C (eval x (weightedHomogeneousComponent (wE k) i P)) *
    Polynomial.X ^ i
  have hroot : ∀ t : K, t ≠ 0 → f.eval t = 0 := by
    intro t ht
    have hs := mem_vanish.mp hP g hg (fun k' => (if k' = k then Units.mk0 t ht else 1) * lam k')
    rw [coords_mul, hsum, map_sum] at hs
    rw [← hs, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := wE k) i P
    have := eval_scale (κ := Unit) (fun v _ => wE k v) (fun _ => t) x
      (Q := weightedHomogeneousComponent (wE k) i P) (d := fun _ => i)
      (fun s hs' => funext fun _ => by
        rw [← hh hs', Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
          Finset.sum_apply]; rfl)
    simp only [Finset.univ_unique, Finset.prod_singleton] at this
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm,
      ← this]
    congr 2
    funext v
    congr 1
    simp only [wE, apply_ite Units.val, Units.val_mk0, Units.val_one]
    rw [Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hf : f = 0 := Polynomial.eq_zero_of_infinite_isRoot f
    (Set.Infinite.mono (s := ({0}ᶜ : Set K)) (fun t ht => hroot t ht)
      (Set.Finite.infinite_compl (Set.finite_singleton 0)))
  by_cases hn : n ∈ T
  · have := congrArg (Polynomial.coeff · n) hf
    simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single n (fun b _ hb => ite_eq_right_iff.mpr fun h => absurd h (Ne.symm hb))
      (fun h => absurd hn h)] at this
    simpa using this
  · have : weightedHomogeneousComponent (wE k) n P = 0 := by
      by_contra h
      exact hn (hfin.mem_toFinset.mpr h)
    rw [this, map_zero]

/-- **Multihomogeneous replacement.** -/
theorem exists_homog [Infinite K] {E : Set (GPt K d₀ d₁ g₂ g₃)} {x : Var d₀ d₁ m → K}
    {P : MvPolynomial (Var d₀ d₁ m) K} (hP : P ∈ vanish E) (hx : eval x P ≠ 0) :
    ∃ Q ∈ vanish E, eval x Q ≠ 0 ∧ ∃ d, IsWeightedHomogeneous wV Q d := by
  classical
  suffices h : ∀ s : Finset (Fin m), ∃ Q ∈ vanish E, eval x Q ≠ 0 ∧
      ∀ k ∈ s, ∃ n, IsWeightedHomogeneous (wE k) Q n by
    obtain ⟨Q, hQ, hxQ, hh⟩ := h Finset.univ
    choose n hn using fun k => hh k (Finset.mem_univ k)
    exact ⟨Q, hQ, hxQ, n, isWeightedHomogeneous_wV hn⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨P, hP, hx, by simp⟩
  | insert k s _ ih =>
    obtain ⟨Q, hQ, hxQ, hh⟩ := ih
    have hfin := weightedHomogeneousComponent_finsupp (w := wE k) Q
    have hsum : Q = ∑ i ∈ hfin.toFinset, weightedHomogeneousComponent (wE k) i Q := by
      conv_lhs => rw [← finsum_weightedHomogeneousComponent (wE k) Q]
      exact finsum_eq_sum _ hfin
    rw [hsum, map_sum] at hxQ
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxQ
    refine ⟨_, comp_mem_vanish hQ k i, hi, fun k' hk' => ?_⟩
    rcases Finset.mem_insert.mp hk' with rfl | hk'
    · exact ⟨i, weightedHomogeneousComponent_isWeightedHomogeneous i Q⟩
    · obtain ⟨n, hn⟩ := hh k' hk'
      exact ⟨n, isWeightedHomogeneous_comp hn i⟩

/-- The multihomogeneous elements of `vanish H`. -/
def homogVanish (H : Set (GPt K d₀ d₁ g₂ g₃)) : Set (MvPolynomial (Var d₀ d₁ m) K) :=
  {Q | Q ∈ vanish H ∧ ∃ d, IsWeightedHomogeneous wV Q d}

/-- Multihomogeneous polynomials vanish at all or none of the cone representatives of `g`. -/
theorem eval_coords_eq_zero_iff {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wV Q d) (g : GPt K d₀ d₁ g₂ g₃) (lam lam' : Fin m → Kˣ) :
    eval (coords g lam) Q = 0 ↔ eval (coords g lam') Q = 0 := by
  have e : lam' = fun k => (lam' k * (lam k)⁻¹) * lam k := by
    funext k; rw [inv_mul_cancel_right]
  rw [e, coords_mul, eval_scale wV _ _ hQ, mul_eq_zero, or_iff_right]
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Units.ne_zero _))

/-- For `H` Zariski closed, a point outside `H` is detected by a multihomogeneous element of
`vanish H` at every cone representative. -/
theorem exists_homogVanish_ne [Infinite K] {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsZClosed H)
    {g : GPt K d₀ d₁ g₂ g₃} (hg : g ∉ H) :
    ∃ Q ∈ homogVanish H, ∀ lam, eval (coords g lam) Q ≠ 0 := by
  rw [← zeros_vanish hH] at hg
  simp only [zeros, Set.mem_ofPred_eq, not_forall] at hg
  obtain ⟨P, hP, lam₀, hne⟩ := hg
  obtain ⟨Q, hQ, hxQ, d, hd⟩ := exists_homog hP hne
  exact ⟨Q, ⟨hQ, d, hd⟩, fun lam h => hxQ ((eval_coords_eq_zero_iff hd g _ _).mp h)⟩

/-- **`H` is cut out by multihomogeneous polynomials.** -/
theorem zeros_homogVanish [Infinite K] {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsZClosed H) :
    zeros (homogVanish H) = H := by
  refine le_antisymm (fun g hg => by_contra fun h => ?_)
    (fun g hg Q hQ lam => mem_vanish.mp hQ.1 g hg lam)
  obtain ⟨Q, hQ, hne⟩ := exists_homogVanish_ne hH h
  exact hne 1 (hg Q hQ 1)

/-! ### The projection -/

/-- The point of `G_a^{d₀} × G_m^{d₁}` (StrongSix's `GPt`) under a point of `G`. -/
def linPt (g : GPt K d₀ d₁ g₂ g₃) : StrongSix.Thm1.GPt K d₀ d₁ := (g.1, Additive.toMul g.2.1)

/-- The projection `π_L(H)`. -/
def projL (H : Set (GPt K d₀ d₁ g₂ g₃)) : Set (StrongSix.Thm1.GPt K d₀ d₁) := linPt '' H

/-- The variables as linear variables plus cone variables (`Fin (2 + 1) = Fin 3` per block). -/
def splitVar : Var d₀ d₁ m → StrongSix.M2.V3 d₀ d₁ ⊕ (Σ _ : Fin m, Fin (2 + 1))
  | .x i => .inl (.inl i)
  | .y j => .inl (.inr (.inl j))
  | .z j => .inl (.inr (.inr j))
  | .e k c => .inr ⟨k, c⟩

theorem splitVar_injective : Function.Injective (splitVar : Var d₀ d₁ m → _) := by
  intro a b h
  cases a <;> cases b <;> simp_all [splitVar]

theorem weight_comp_splitVar :
    (Sum.elim (0 : StrongSix.M2.V3 d₀ d₁ → Fin m → ℕ) (blockWeight (Sigma.fst : (Σ _ : Fin m, Fin (2 + 1)) → Fin m))) ∘
      (splitVar : Var d₀ d₁ m → _) = wV := by
  funext v
  cases v <;> rfl

theorem isWeightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M] {e : σ → τ}
    (he : Function.Injective e) {W : τ → M} {Q : MvPolynomial σ K} {d : M}
    (hQ : IsWeightedHomogeneous (W ∘ e) Q d) : IsWeightedHomogeneous W (rename e Q) d := by
  classical
  intro s hs
  have hs' : s ∈ (rename e Q).support := mem_support_iff.mpr hs
  rw [support_rename_of_injective he, Finset.mem_image] at hs'
  obtain ⟨t, ht, rfl⟩ := hs'
  rw [← hQ (mem_support_iff.mp ht), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • W i) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)]
  rfl

omit [Field K] in
theorem isWeightedHomogeneous_Fk [Field K] (k : Fin m) :
    IsWeightedHomogeneous wV (Fk g₂ g₃ d₀ d₁ k : MvPolynomial (Var d₀ d₁ m) K)
      (3 • Pi.single k 1) := by
  have hX : ∀ c, IsWeightedHomogeneous wV (X (Var.e k c) : MvPolynomial (Var d₀ d₁ m) K)
      (Pi.single k 1) := fun c => isWeightedHomogeneous_X K wV _
  have hC : ∀ a : K, IsWeightedHomogeneous wV (C a : MvPolynomial (Var d₀ d₁ m) K) 0 :=
    fun a => isWeightedHomogeneous_C _ _
  have h4 : (4 : MvPolynomial (Var d₀ d₁ m) K) = C 4 := (map_ofNat C 4).symm
  simp only [Fk, F, h4]
  refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.add (IsWeightedHomogeneous.sub ?_ ?_) ?_) ?_
  · exact homog_of_eq (((hX 1).pow 2).mul (hX 2)) (by rw [← succ_nsmul])
  · exact homog_of_eq ((hC 4).mul ((hX 0).pow 3)) (by rw [zero_add])
  · exact homog_of_eq (((hC _).mul (hX 0)).mul ((hX 2).pow 2)) (by rw [zero_add, ← succ_nsmul'])
  · exact homog_of_eq ((hC _).mul ((hX 2).pow 3)) (by rw [zero_add])

theorem eval_splitVar (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) :
    (Sum.elim (StrongSix.M2.pt (linPt g))
      (fun p : Σ _ : Fin m, Fin (2 + 1) => (lam p.1 : K) * rep (g.2.2 p.1) p.2)) ∘ splitVar =
      coords g lam := by
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j => rfl
  | e k c => rfl

variable [DecidableEq K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

omit [DecidableEq K] in
/-- **The linear projection of a Zariski-closed set is Zariski closed** (projective elimination
along the cone blocks). -/
theorem projL_closed [IsAlgClosed K] {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsZClosed H) :
    ∃ Ps : Set (MvPolynomial (StrongSix.M2.V3 d₀ d₁) K), projL H = StrongSix.M2.zeros Ps := by
  classical
  set J := rename (splitVar (d₀ := d₀) (d₁ := d₁) (m := m)) '' homogVanish H with hJdef
  obtain ⟨J', hJ'⟩ := isClosed_proj_sigma (K := K) (N := fun _ : Fin m => 2) J (by
    rintro _ ⟨Q, ⟨-, d, hd⟩, rfl⟩
    refine ⟨d, isWeightedHomogeneous_rename splitVar_injective ?_⟩
    rwa [weight_comp_splitVar])
  refine ⟨J', Set.ext fun g' => ?_⟩
  have key : g' ∈ projL H ↔ StrongSix.M2.pt g' ∈ {x : StrongSix.M2.V3 d₀ d₁ → K |
      ∃ y : (Σ _ : Fin m, Fin (2 + 1)) → K, (∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) ∧
        ∀ f ∈ J, eval (Sum.elim x y) f = 0} := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨fun p => (1 : K) * rep (g.2.2 p.1) p.2, fun k => ?_, ?_⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp (rep_ne_zero (g.2.2 k))
        exact ⟨j, by simpa using hj⟩
      · rintro _ ⟨Q, hQ, rfl⟩
        rw [eval_rename]
        have := eval_splitVar g (fun _ => 1)
        simp only [Units.val_one] at this
        rw [this]
        exact mem_vanish.mp hQ.1 g hg _
    · rintro ⟨y, hy, hJy⟩
      set cv : Fin m → Fin 3 → K := fun k c => y ⟨k, c⟩
      have hcv0 : ∀ k, cv k ≠ 0 := fun k h => by
        obtain ⟨j, hj⟩ := hy k; exact hj (congrFun h j)
      have hF : ∀ k, Fv (g₂ k) (g₃ k) (cv k) = 0 := by
        intro k
        have hFk : Fk g₂ g₃ d₀ d₁ k ∈ homogVanish H :=
          ⟨IG_le_vanish h2 H (Fk_mem_IG g₂ g₃ k), _, isWeightedHomogeneous_Fk k⟩
        have := hJy _ ⟨_, hFk, rfl⟩
        rw [eval_rename] at this
        simpa [Fk, F, Fv, cv, splitVar] using this
      choose u hu0 hu using fun k => exists_smul_rep h2 (hΔ k) (hF k) (hcv0 k)
      let g : GPt K d₀ d₁ g₂ g₃ := (g'.1, Additive.ofMul g'.2,
        fun k => toPoint (g₂ k) (g₃ k) (cv k))
      let lam : Fin m → Kˣ := fun k => Units.mk0 (u k) (hu0 k)
      have hco : (Sum.elim (StrongSix.M2.pt g') y) ∘ splitVar = coords g lam := by
        rw [← eval_splitVar g lam]
        funext v
        cases v with
        | x i => rfl
        | y j => rfl
        | z j => rfl
        | e k c =>
          show y ⟨k, c⟩ = (u k) * rep (g.2.2 k) c
          exact congrFun (hu k) c
      refine ⟨g, ?_, rfl⟩
      rw [← zeros_homogVanish hH]
      intro Q hQ lam'
      have := hJy _ ⟨Q, hQ, rfl⟩
      rw [eval_rename, hco] at this
      obtain ⟨d, hd⟩ := hQ.2
      exact (eval_coords_eq_zero_iff hd g lam lam').mp this
  rw [key, hJ']
  rfl

omit h2 hΔ in
/-- The projection of a subgroup is a subgroup. -/
theorem projL_isSubgroup [CharZero K] {H : Set (GPt K d₀ d₁ g₂ g₃)} (hH : IsSubgroupG H) :
    StrongSix.M2.IsSubgroupG (projL H) where
  one_mem := ⟨0, hH.zero_mem, rfl⟩
  mul_mem := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g + h, hH.add_mem g hg h hh, rfl⟩
  inv_mem := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨-g, hH.neg_mem g hg, rfl⟩

/-- **The linear projection of a Zariski-closed subgroup is `V × T_Λ`** (StrongSix's
`classify`): `π_L(H) = prodSet (linV π_L(H)) (latt π_L(H))`. -/
theorem projL_eq_prodSet [IsAlgClosed K] [CharZero K] {H : Set (GPt K d₀ d₁ g₂ g₃)}
    (hH : IsSubgroupG H) (hc : IsZClosed H) :
    projL H = StrongSix.M2.prodSet (StrongSix.M2.linV (projL H)) (StrongSix.M2.latt (projL H)) := by
  obtain ⟨Ps, hPs⟩ := projL_closed h2 hΔ hc
  exact StrongSix.M2.classify (projL_isSubgroup hH) hPs

end LSG.ME
