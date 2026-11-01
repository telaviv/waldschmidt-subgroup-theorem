/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Stmt

/-!
# The multi-cone model: grading, Zariski topology, homogeneous components (A4.2, α)

Generic facts about the cone model of `G = G_a^{d₀} × G_m^{d₁} × ∏_k B_k` (`LSG.MEB.Geom`), retyped
from `LSG.ME.{Geom, StabG, SubgroupProj, SubgroupGraded, SubgroupComp}` for abstract blocks. Nothing
here uses the analytic fields of `AbBlock`.

* **Grading.** `wV v = e_k` on the `k`-th block, `wE k`; `wk_eq_wE` (the `wk` of `Stmt`);
  `eval_scale`, `coords_mul`; **`eval_coords_eq_zero_iff`**: a multihomogeneous `Q` vanishes at
  all or none of the cone representatives of a point.
* **Zero scalars.** `coordsZ g ν` (scalars may vanish), `coords_eq_coordsZ`,
  **`eval_coordsZ_eq_zero`** (density in `ν`).
* **Zariski topology.** `zeros_vanish`, `vanish_injOn`, `isZClosed_iInter`, `IsZClosed.inter`,
  `zcl_minimal`, `vanish_zcl`, `mem_zeros_iff_le_vanish`, `mem_zeros_span`, `vanish_ne_top`, ….
* **Homogeneous components.** `comp_mem_vanish`, **`multiComp_mem_vanish`**, `sum_multiComp`,
  `exists_homog`, `homogVanish`, `zeros_homogVanish`.
* **`vanish_singleton_isPrime`**: `I({g})` is prime.
* Translates: `gtransl_gtransl`, `gtransl_zero`, `gtransl_mono`, `gtransl_gtransl_neg`.
-/

open MvPolynomial

namespace LSG.MEB

variable {m d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-! ### Simp lemmas for the frozen definitions -/

@[simp] theorem blk_x (i : Fin d₀) : blk (.x i : Var d₀ d₁ B) = .x := rfl
@[simp] theorem blk_y (j : Fin d₁) : blk (.y j : Var d₀ d₁ B) = .yz := rfl
@[simp] theorem blk_z (j : Fin d₁) : blk (.z j : Var d₀ d₁ B) = .yz := rfl
@[simp] theorem blk_e (k : Fin m) (c : Fin (B k).N) : blk (.e k c : Var d₀ d₁ B) = .e k := rfl

@[simp] theorem coords_x (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (i : Fin d₀) :
    coords g lam (.x i) = g.1 i := rfl
@[simp] theorem coords_y (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (j : Fin d₁) :
    coords g lam (.y j) = (g.ym j : ℂ) := rfl
@[simp] theorem coords_z (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (j : Fin d₁) :
    coords g lam (.z j) = (((g.ym j)⁻¹ : ℂˣ) : ℂ) := rfl
@[simp] theorem coords_e (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (k : Fin m) (c : Fin (B k).N) :
    coords g lam (.e k c) = (lam k : ℂ) * (B k).rep (g.2.2 k) c := rfl

@[simp] theorem GPt.ym_add (g h : GPt d₀ d₁ B) (j : Fin d₁) : (g + h).ym j = g.ym j * h.ym j :=
  rfl
@[simp] theorem GPt.ym_neg (g : GPt d₀ d₁ B) (j : Fin d₁) : (-g).ym j = (g.ym j)⁻¹ := rfl
@[simp] theorem GPt.ym_zero (j : Fin d₁) : (0 : GPt d₀ d₁ B).ym j = 1 := rfl
@[simp] theorem GPt.ym_sub (g h : GPt d₀ d₁ B) (j : Fin d₁) : (g - h).ym j = g.ym j / h.ym j :=
  rfl

/-! ### The multigrading by blocks -/

/-- The multigrading by abelian blocks. -/
def wV : Var d₀ d₁ B → Fin m → ℕ
  | .e k _ => Pi.single k 1
  | _ => 0

/-- The grading by the `k`-th block. -/
def wE (k : Fin m) : Var d₀ d₁ B → ℕ := fun v => wV v k

theorem wk_eq_wE (k : Fin m) : (wk k : Var d₀ d₁ B → ℕ) = wE k := by
  funext v
  cases v <;> simp [wk, wE, wV, Pi.single_apply, eq_comm]

theorem weight_wE (k : Fin m) (s : Var d₀ d₁ B →₀ ℕ) :
    Finsupp.weight (wE k) s = Finsupp.weight wV s k := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wE]

theorem isWeightedHomogeneous_wV {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {n : Fin m → ℕ}
    (h : ∀ k, IsWeightedHomogeneous (wE k) Q (n k)) : IsWeightedHomogeneous wV Q n := by
  intro s hs
  funext k
  rw [← weight_wE]; exact h k hs

theorem isHomB_iff_wV {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {n : Fin m → ℕ} :
    IsHomB Q n ↔ IsWeightedHomogeneous wV Q n := by
  constructor
  · intro h; exact isWeightedHomogeneous_wV fun k => by rw [← wk_eq_wE]; exact h k
  · intro h k s hs; rw [wk_eq_wE, weight_wE, h hs]

/-- Components for one grading stay homogeneous for another. -/
theorem isWeightedHomogeneous_comp {σ M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    {w : σ → M} {w' : σ → N} {φ : MvPolynomial σ ℂ} {n' : N}
    (h : IsWeightedHomogeneous w' φ n') (n : M) :
    IsWeightedHomogeneous w' (weightedHomogeneousComponent w n φ) n' := by
  classical
  intro s hs
  rw [coeff_weightedHomogeneousComponent] at hs
  split_ifs at hs
  · exact h hs
  · exact absurd rfl hs

/-- **Evaluation at a rescaled point.** -/
theorem eval_scale {σ κ : Type*} [Fintype σ] [Fintype κ] (W : σ → κ → ℕ) (μ : κ → ℂ) (x : σ → ℂ)
    {Q : MvPolynomial σ ℂ} {d : κ → ℕ} (hQ : IsWeightedHomogeneous W Q d) :
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
theorem coords_mul (g : GPt d₀ d₁ B) (μ lam : Fin m → ℂˣ) :
    coords g (fun k => μ k * lam k) =
      fun v => (∏ k, ((μ k : ℂˣ) : ℂ) ^ wV v k) * coords g lam v := by
  funext v
  cases v with
  | x i => simp [coords, wV]
  | y j => simp [coords, wV]
  | z j => simp [coords, wV]
  | e k c =>
    simp only [coords, wV, Units.val_mul, Pi.single_apply, pow_ite, pow_one,
      pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- Multihomogeneous polynomials vanish at all or none of the cone representatives of `g`. -/
theorem eval_coords_eq_zero_iff {Q : MvPolynomial (Var d₀ d₁ B) ℂ} {d : Fin m → ℕ}
    (hQ : IsWeightedHomogeneous wV Q d) (g : GPt d₀ d₁ B) (lam lam' : Fin m → ℂˣ) :
    eval (coords g lam) Q = 0 ↔ eval (coords g lam') Q = 0 := by
  have e : lam' = fun k => (lam' k * (lam k)⁻¹) * lam k := by
    funext k; rw [inv_mul_cancel_right]
  rw [e, coords_mul, eval_scale wV _ _ hQ, mul_eq_zero, or_iff_right]
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Units.ne_zero _))

/-! ### Zero scalars -/

/-- The cone coordinates of `g` with scalars `ν : Fin m → ℂ` (which may vanish). -/
noncomputable def coordsZ (g : GPt d₀ d₁ B) (ν : Fin m → ℂ) : Var d₀ d₁ B → ℂ
  | .x i => g.1 i
  | .y j => (g.ym j : ℂ)
  | .z j => (((g.ym j)⁻¹ : ℂˣ) : ℂ)
  | .e k c => ν k * (B k).rep (g.2.2 k) c

theorem coords_eq_coordsZ (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) :
    coords g lam = coordsZ g fun k => (lam k : ℂ) := by
  funext v; cases v <;> rfl

/-- **Density.** A polynomial vanishing at `coords g λ` for all `λ` vanishes at `coordsZ g ν` for
all `ν`: along the line `t ↦ (ν, zero entries replaced by t)`. -/
theorem eval_coordsZ_eq_zero {g : GPt d₀ d₁ B} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : ∀ lam, eval (coords g lam) P = 0) (ν : Fin m → ℂ) : eval (coordsZ g ν) P = 0 := by
  classical
  let φ : Var d₀ d₁ B → Polynomial ℂ := fun v => match v with
    | .x i => Polynomial.C (g.1 i)
    | .y j => Polynomial.C (g.ym j : ℂ)
    | .z j => Polynomial.C (((g.ym j)⁻¹ : ℂˣ) : ℂ)
    | .e k c => (if ν k = 0 then Polynomial.X else Polynomial.C (ν k)) *
        Polynomial.C ((B k).rep (g.2.2 k) c)
  set Q := MvPolynomial.aeval φ P
  have hev : ∀ t : ℂ, Q.eval t = eval (fun v => (φ v).eval t) P := by
    intro t
    rw [show Q = MvPolynomial.aeval φ P from rfl, MvPolynomial.aeval_def,
      MvPolynomial.polynomial_eval_eval₂]
    have : (Polynomial.evalRingHom t).comp (algebraMap ℂ (Polynomial ℂ)) = RingHom.id ℂ := by
      ext; simp
    rw [this]; rfl
  have hroot : ∀ t : ℂ, t ≠ 0 → Q.IsRoot t := by
    intro t ht
    rw [Polynomial.IsRoot, hev]
    let lam : Fin m → ℂˣ := fun k => if h : ν k = 0 then Units.mk0 t ht else Units.mk0 (ν k) h
    have : (fun v => (φ v).eval t) = coords g lam := by
      funext v
      cases v with
      | x i => simp [φ, coords]
      | y j => simp [φ, coords]
      | z j => simp [φ, coords]
      | e k c =>
        by_cases h : ν k = 0
        · simp only [φ, coords, lam, h, dite_true, ite_true, Units.val_mk0, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_C]
        · simp [φ, coords, lam, h]
    rw [this]; exact hP lam
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) (fun t ht => hroot t ht) ?_
    exact Set.Finite.infinite_compl (Set.finite_singleton 0)
  have := hev 0
  rw [hQ, Polynomial.eval_zero] at this
  rw [this]
  congr 2
  funext v
  cases v with
  | x i => simp [φ, coordsZ]
  | y j => simp [φ, coordsZ]
  | z j => simp [φ, coordsZ]
  | e k c => by_cases h : ν k = 0 <;> simp [φ, coordsZ, h]

/-! ### Zariski topology -/

theorem one_notMem_vanish {E : Set (GPt d₀ d₁ B)} (hE : E.Nonempty) :
    (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∉ vanish E := by
  obtain ⟨g, hg⟩ := hE
  intro h
  simpa using mem_vanish.mp h g hg 1

theorem vanish_ne_top {E : Set (GPt d₀ d₁ B)} (hE : E.Nonempty) : vanish E ≠ ⊤ :=
  fun h => one_notMem_vanish hE (h ▸ Submodule.mem_top)

theorem vanish_empty : vanish (∅ : Set (GPt d₀ d₁ B)) = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_vanish.mpr fun _ hg => absurd hg (Set.notMem_empty _)

theorem mem_zeros_iff_le_vanish {J : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ)} {g : GPt d₀ d₁ B} :
    g ∈ zeros (J : Set _) ↔ J ≤ vanish {g} := by
  simp only [zeros, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam

theorem mem_zeros_span {s : Set (MvPolynomial (Var d₀ d₁ B) ℂ)} {g : GPt d₀ d₁ B} :
    g ∈ zeros (Ideal.span s : Set _) ↔ g ∈ zeros s := by
  rw [mem_zeros_iff_le_vanish, Ideal.span_le]
  simp only [zeros, Set.mem_setOf_eq]
  constructor
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam

theorem mem_vanish_singleton_iff {g : GPt d₀ d₁ B} {R : MvPolynomial (Var d₀ d₁ B) ℂ} :
    R ∈ vanish {g} ↔ g ∈ (zeros {R} : Set _) := by
  rw [mem_vanish]
  constructor
  · intro h P hP lam; rw [Set.mem_singleton_iff] at hP; subst hP; exact h g rfl lam
  · intro h g' hg' lam; rw [Set.mem_singleton_iff] at hg'; subst hg'; exact h R rfl lam

theorem zeros_antitone {S T : Set (MvPolynomial (Var d₀ d₁ B) ℂ)} (h : S ⊆ T) :
    (zeros T : Set (GPt d₀ d₁ B)) ⊆ zeros S := fun _ hg P hP => hg P (h hP)

theorem isZClosed_zeros (S : Set (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    IsZClosed (zeros S : Set (GPt d₀ d₁ B)) := ⟨S, rfl⟩

theorem subset_zeros_vanish (V : Set (GPt d₀ d₁ B)) :
    V ⊆ zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ B) ℂ)) :=
  fun g hg _ hP lam => mem_vanish.mp hP g hg lam

/-- A Zariski-closed set is the zero set of its vanishing ideal. -/
theorem zeros_vanish {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) :
    zeros (vanish V : Set (MvPolynomial (Var d₀ d₁ B) ℂ)) = V := by
  refine le_antisymm ?_ (subset_zeros_vanish V)
  obtain ⟨S, rfl⟩ := hV
  intro g hg P hP lam
  exact hg P (mem_vanish.mpr fun g' hg' lam' => hg' P hP lam') lam

theorem vanish_injOn {V V' : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (hV' : IsZClosed V')
    (h : vanish V = vanish V') : V = V' := by
  rw [← zeros_vanish hV, ← zeros_vanish hV', h]

theorem vanish_le_vanish_iff {V V' : Set (GPt d₀ d₁ B)} (hV' : IsZClosed V') :
    vanish V' ≤ vanish V ↔ V ⊆ V' := by
  refine ⟨fun h => ?_, vanish_antitone⟩
  rw [← zeros_vanish hV']
  exact (subset_zeros_vanish V).trans (zeros_antitone h)

/-- The intersection of Zariski-closed sets is Zariski closed. -/
theorem isZClosed_iInter {ι : Sort*} {V : ι → Set (GPt d₀ d₁ B)} (hV : ∀ i, IsZClosed (V i)) :
    IsZClosed (⋂ i, V i) := by
  choose S hS using hV
  refine ⟨⋃ i, S i, ?_⟩
  ext g
  simp only [Set.mem_iInter, hS, zeros, Set.mem_setOf_eq, Set.mem_iUnion, forall_exists_index]
  exact ⟨fun h P i hP lam => h i P hP lam, fun h i P hP lam => h P i hP lam⟩

theorem zeros_union (S T : Set (MvPolynomial (Var d₀ d₁ B) ℂ)) :
    (zeros (S ∪ T) : Set (GPt d₀ d₁ B)) = zeros S ∩ zeros T := by
  ext g
  simp only [zeros, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩,
    fun h P hP => hP.elim (h.1 P) (h.2 P)⟩

theorem IsZClosed.inter {V W : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (hW : IsZClosed W) :
    IsZClosed (V ∩ W) := by
  obtain ⟨S, rfl⟩ := hV
  obtain ⟨T, rfl⟩ := hW
  exact ⟨S ∪ T, (zeros_union S T).symm⟩

theorem zcl_minimal {S V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) (h : S ⊆ V) : zcl S ⊆ V := by
  rw [← zeros_vanish hV]
  intro g hg P hP lam
  exact hg P (vanish_antitone h hP) lam

theorem vanish_zcl (S : Set (GPt d₀ d₁ B)) : vanish (zcl S) = vanish S :=
  le_antisymm (vanish_antitone (subset_zcl S)) fun _ hP => mem_vanish.mpr fun _ hg lam => hg _ hP lam

theorem zcl_mono {S T : Set (GPt d₀ d₁ B)} (h : S ⊆ T) : zcl S ⊆ zcl T :=
  zeros_antitone (vanish_antitone h)

theorem zcl_eq_self {V : Set (GPt d₀ d₁ B)} (hV : IsZClosed V) : zcl V = V := zeros_vanish hV

/-! ### Homogeneous components of `vanish E` -/

/-- **`vanish E` is homogeneous in each block.** -/
theorem comp_mem_vanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ}
    (hP : P ∈ vanish E) (k : Fin m) (n : ℕ) :
    weightedHomogeneousComponent (wE k) n P ∈ vanish E := by
  classical
  refine mem_vanish.mpr fun g hg lam => ?_
  set x := coords g lam
  have hfin := weightedHomogeneousComponent_finsupp (w := wE k) P
  set T := hfin.toFinset
  have hsum : P = ∑ i ∈ T, weightedHomogeneousComponent (wE k) i P := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (wE k) P]
    exact finsum_eq_sum _ hfin
  set f : Polynomial ℂ := ∑ i ∈ T,
    Polynomial.C (eval x (weightedHomogeneousComponent (wE k) i P)) * Polynomial.X ^ i
  have hroot : ∀ t : ℂ, t ≠ 0 → f.eval t = 0 := by
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
    (Set.Infinite.mono (s := ({0}ᶜ : Set ℂ)) (fun t ht => hroot t ht)
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

/-- Iterated block components along a list of blocks. -/
noncomputable def compL (d : Fin m → ℕ) : List (Fin m) → MvPolynomial (Var d₀ d₁ B) ℂ →
    MvPolynomial (Var d₀ d₁ B) ℂ
  | [] => id
  | k :: l => fun P => weightedHomogeneousComponent (wE k) (d k) (compL d l P)

open Classical in
theorem coeff_compL (d : Fin m → ℕ) (l : List (Fin m)) (P : MvPolynomial (Var d₀ d₁ B) ℂ)
    (t : Var d₀ d₁ B →₀ ℕ) :
    (compL d l P).coeff t =
      if ∀ k ∈ l, Finsupp.weight (wE k) t = d k then P.coeff t else 0 := by
  induction l with
  | nil => simp [compL]
  | cons k l ih =>
    simp only [compL, coeff_weightedHomogeneousComponent]
    rw [ih]
    by_cases h1 : Finsupp.weight (wE k) t = d k <;>
      by_cases h2 : ∀ k ∈ l, Finsupp.weight (wE k) t = d k <;> simp [h1, h2]

theorem compL_mem_vanish {E : Set (GPt d₀ d₁ B)} (d : Fin m → ℕ)
    (l : List (Fin m)) {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ vanish E) :
    compL d l P ∈ vanish E := by
  induction l with
  | nil => exact hP
  | cons k l ih => exact comp_mem_vanish ih k (d k)

theorem compL_univ (d : Fin m → ℕ) (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    compL d (List.finRange m) P = weightedHomogeneousComponent wV d P := by
  classical
  ext t
  rw [coeff_compL, coeff_weightedHomogeneousComponent]
  congr 1
  apply propext
  constructor
  · intro h; funext k; rw [← weight_wE]; exact h k (List.mem_finRange k)
  · intro h k _; rw [weight_wE, h]

/-- **`vanish E` is closed under multihomogeneous components.** -/
theorem multiComp_mem_vanish {E : Set (GPt d₀ d₁ B)} (d : Fin m → ℕ)
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ vanish E) :
    weightedHomogeneousComponent wV d P ∈ vanish E := by
  rw [← compL_univ]; exact compL_mem_vanish d _ hP

theorem sum_multiComp (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    ∃ s : Finset (Fin m → ℕ), P = ∑ d ∈ s, weightedHomogeneousComponent wV d P := by
  have hfin := weightedHomogeneousComponent_finsupp (w := (wV : Var d₀ d₁ B → Fin m → ℕ)) P
  refine ⟨hfin.toFinset, ?_⟩
  conv_lhs => rw [← finsum_weightedHomogeneousComponent wV P]
  exact finsum_eq_sum _ hfin

/-- **Multihomogeneous replacement.** -/
theorem exists_homog {E : Set (GPt d₀ d₁ B)} {x : Var d₀ d₁ B → ℂ}
    {P : MvPolynomial (Var d₀ d₁ B) ℂ} (hP : P ∈ vanish E) (hx : eval x P ≠ 0) :
    ∃ Q ∈ vanish E, eval x Q ≠ 0 ∧ ∃ d, IsWeightedHomogeneous wV Q d := by
  classical
  obtain ⟨s, hs⟩ := sum_multiComp P
  rw [hs, map_sum] at hx
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact ⟨_, multiComp_mem_vanish d hP, hd, d,
    weightedHomogeneousComponent_isWeightedHomogeneous d P⟩

/-- The multihomogeneous elements of `vanish H`. -/
def homogVanish (H : Set (GPt d₀ d₁ B)) : Set (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  {Q | Q ∈ vanish H ∧ ∃ d, IsWeightedHomogeneous wV Q d}

/-- For `H` Zariski closed, a point outside `H` is detected by a multihomogeneous element of
`vanish H` at every cone representative. -/
theorem exists_homogVanish_ne {H : Set (GPt d₀ d₁ B)} (hH : IsZClosed H)
    {g : GPt d₀ d₁ B} (hg : g ∉ H) :
    ∃ Q ∈ homogVanish H, ∀ lam, eval (coords g lam) Q ≠ 0 := by
  rw [← zeros_vanish hH] at hg
  simp only [zeros, Set.mem_setOf_eq, not_forall] at hg
  obtain ⟨P, hP, lam₀, hne⟩ := hg
  obtain ⟨Q, hQ, hxQ, d, hd⟩ := exists_homog hP hne
  exact ⟨Q, ⟨hQ, d, hd⟩, fun lam h => hxQ ((eval_coords_eq_zero_iff hd g _ _).mp h)⟩

/-- **`H` is cut out by multihomogeneous polynomials.** -/
theorem zeros_homogVanish {H : Set (GPt d₀ d₁ B)} (hH : IsZClosed H) :
    zeros (homogVanish H) = H := by
  refine le_antisymm (fun g hg => by_contra fun h => ?_)
    (fun g hg Q hQ lam => mem_vanish.mp hQ.1 g hg lam)
  obtain ⟨Q, hQ, hne⟩ := exists_homogVanish_ne hH h
  exact hne 1 (hg Q hQ 1)

/-! ### `vanish {g}` is prime -/

/-- `P ↦ P(coords g λ)` as a polynomial in `λ`. -/
noncomputable def evPt (g : GPt d₀ d₁ B) :
    MvPolynomial (Var d₀ d₁ B) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
  aeval fun v => match v with
    | .x i => C (g.1 i)
    | .y j => C (g.ym j : ℂ)
    | .z j => C ((((g.ym j)⁻¹ : ℂˣ)) : ℂ)
    | .e k c => X k * C ((B k).rep (g.2.2 k) c)

theorem eval_evPt (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) (P : MvPolynomial (Var d₀ d₁ B) ℂ) :
    eval (fun k => (lam k : ℂ)) (evPt g P) = eval (coords g lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evPt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, evPt, aeval_X, eval_X]
    congr 1
    cases v <;> simp [coords]

/-- A polynomial in `λ` vanishing on `(ℂˣ)^m` is zero. -/
theorem eq_zero_of_eval_units {f : MvPolynomial (Fin m) ℂ}
    (h : ∀ lam : Fin m → ℂˣ, eval (fun k => (lam k : ℂ)) f = 0) : f = 0 := by
  classical
  -- `f · ∏ X_k` vanishes everywhere
  have hprod : f * ∏ k, X k = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_prod, map_zero]
    by_cases hx : ∀ k, x k ≠ 0
    · have := h fun k => Units.mk0 (x k) (hx k)
      simp only [Units.val_mk0] at this
      rw [this, zero_mul]
    · push_neg at hx
      obtain ⟨k, hk⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), mul_zero]
  have hne : (∏ k, X k : MvPolynomial (Fin m) ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => X_ne_zero k
  exact (mul_eq_zero.mp hprod).resolve_right hne

theorem mem_vanish_singleton_iff_evPt {g : GPt d₀ d₁ B} {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanish {g} ↔ evPt g P = 0 := by
  rw [mem_vanish]
  constructor
  · intro h
    exact eq_zero_of_eval_units fun lam => by rw [eval_evPt]; exact h g rfl lam
  · intro h g' hg' lam
    rw [Set.mem_singleton_iff.mp hg', ← eval_evPt, h, map_zero]

/-- **`I({g})` is prime.** -/
theorem vanish_singleton_isPrime (g : GPt d₀ d₁ B) : (vanish {g}).IsPrime := by
  have : vanish {g} = RingHom.ker (evPt g).toRingHom := by
    ext P; rw [mem_vanish_singleton_iff_evPt, RingHom.mem_ker]; rfl
  rw [this]
  exact RingHom.ker_isPrime _

/-! ### Translates -/

theorem gtransl_gtransl (a b : GPt d₀ d₁ B) (E : Set (GPt d₀ d₁ B)) :
    gtransl a (gtransl b E) = gtransl (b + a) E := by
  ext h; simp only [mem_gtransl, sub_add_eq_sub_sub, sub_right_comm]

theorem gtransl_zero (E : Set (GPt d₀ d₁ B)) : gtransl 0 E = E := by
  ext h; simp [mem_gtransl]

theorem gtransl_mono (a : GPt d₀ d₁ B) {E E' : Set (GPt d₀ d₁ B)} (h : E ⊆ E') :
    gtransl a E ⊆ gtransl a E' := Set.image_mono h

theorem gtransl_gtransl_neg (g : GPt d₀ d₁ B) (E : Set (GPt d₀ d₁ B)) :
    gtransl (-g) (gtransl g E) = E := by
  ext h; simp [mem_gtransl, sub_eq_add_neg]

theorem gtransl_subset_iff {a : GPt d₀ d₁ B} {X Y : Set (GPt d₀ d₁ B)} :
    gtransl a X ⊆ Y ↔ X ⊆ gtransl (-a) Y := by
  constructor
  · intro h x hx; rw [mem_gtransl, sub_neg_eq_add]; exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    have := h hx
    rwa [mem_gtransl, sub_neg_eq_add] at this

end LSG.MEB
