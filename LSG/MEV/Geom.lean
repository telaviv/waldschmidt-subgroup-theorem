import Mathlib
import LSG.MEV.Group
import LSG.ME.Transl

/-!
# The multi-cone model of `G̃ = G_a^{d₀} × G_m^{d₁} × E₁^♮ × ⋯ × E_m^♮` (VECEXT §3.2)

Each `E^♮` factor is modelled by the affine cone over `X = V(F, G) ⊂ ℙ⁴`
(coordinates `(U, V, W, T₁, T₃)`, `F = V²W − 4U³ + g₂UW² + g₃W³`, `G = W T₃ − V T₁ + 2U²`).

* `Var d₀ d₁ m`: the variables `X i` (`G_a`), `Y j`, `Z j` (`G_m`, with `Y Z = 1`), and the five cone
  coordinates `e k c` (`c : Fin 5`) of each `E^♮` factor. The blocks are those of the abelian model
  (`LSG.ME.Blk`): `X`, `(Y, Z)`, one per `E^♮` factor; `blk`.
* `GPtV d₀ d₁ Ls`: the points of `G̃` over `ℂ` (an additive group; `E^♮` points from
  `LSG.MEV.Group`, the curves given by period pairs `Ls`).
* `coordsZ g ν`, `coords g λ`: cone representatives (`(k, c) ↦ νₖ · repV(gₖ) c`).
* `vanish E`, `zeros 𝒫`, `IsSubgroupG`, `gtransl`.
* `eval_coordsZ_eq_zero`: a polynomial vanishing at `coords g λ` for all `λ` vanishes at
  `coordsZ g ν` for all `ν` (zero scalars included).
* **Relevance**: a cone vector is *relevant* if the base part `(U_k, V_k, W_k)` of every block is
  nonzero (`IsRelevant`); an ideal is relevant if it contains no block irrelevant ideal
  `(U_k, V_k, W_k)` (`IdealRelevant`). The cone of `X` contains the irrelevant plane
  `U = V = W = 0` (boundary of `E^♮`), which is killed by every law (`NLaw_zero_of_base`).
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass PeriodPair

namespace LSG.MEV

open LSG.ME (Blk)

/-- The variables: `x i` (`G_a`), `y j`, `z j` (`G_m`), and the cone coordinates `e k c` of the
`E^♮` factors (`c = 0, …, 4` for `U, V, W, T₁, T₃`). -/
inductive Var (d₀ d₁ m : ℕ)
  | x (i : Fin d₀)
  | y (j : Fin d₁)
  | z (j : Fin d₁)
  | e (k : Fin m) (c : Fin 5)
  deriving DecidableEq, Fintype

variable {d₀ d₁ m : ℕ}

/-- The block of a variable. -/
def blk : Var d₀ d₁ m → Blk m
  | .x _ => .x
  | .y _ => .yz
  | .z _ => .yz
  | .e k _ => .e k

@[simp] theorem blk_x (i : Fin d₀) : blk (.x i : Var d₀ d₁ m) = .x := rfl
@[simp] theorem blk_y (j : Fin d₁) : blk (.y j : Var d₀ d₁ m) = .yz := rfl
@[simp] theorem blk_z (j : Fin d₁) : blk (.z j : Var d₀ d₁ m) = .yz := rfl
@[simp] theorem blk_e (k : Fin m) (c : Fin 5) : blk (.e k c : Var d₀ d₁ m) = .e k := rfl

/-- The base coordinate `c ∈ {U, V, W}` of block `k`. -/
abbrev eb (k : Fin m) (c : Fin 3) : Var d₀ d₁ m := .e k c.castSucc.castSucc

/-! ### Points over `ℂ` -/

/-- The points of `G̃ = G_a^{d₀} × G_m^{d₁} × ∏ₖ E_k^♮`. -/
abbrev GPtV (d₀ d₁ : ℕ) {m : ℕ} (Ls : Fin m → PeriodPair) : Type :=
  (Fin d₀ → ℂ) × Additive (Fin d₁ → ℂˣ) × (∀ k, EVL (Ls k))

variable {Ls : Fin m → PeriodPair}

/-- The `G_m` coordinates of a point. -/
def GPtV.ym (g : GPtV d₀ d₁ Ls) (j : Fin d₁) : ℂˣ := Additive.toMul g.2.1 j

@[simp] theorem GPtV.ym_add (g h : GPtV d₀ d₁ Ls) (j : Fin d₁) : (g + h).ym j = g.ym j * h.ym j :=
  rfl
@[simp] theorem GPtV.ym_neg (g : GPtV d₀ d₁ Ls) (j : Fin d₁) : (-g).ym j = (g.ym j)⁻¹ := rfl
@[simp] theorem GPtV.ym_zero (j : Fin d₁) : (0 : GPtV d₀ d₁ Ls).ym j = 1 := rfl

/-- A subgroup of `G̃`. -/
structure IsSubgroupG (E : Set (GPtV d₀ d₁ Ls)) : Prop where
  zero_mem : 0 ∈ E
  add_mem : ∀ g ∈ E, ∀ h ∈ E, g + h ∈ E
  neg_mem : ∀ g ∈ E, -g ∈ E

/-- The translate `E + g`. -/
def gtransl (g : GPtV d₀ d₁ Ls) (E : Set (GPtV d₀ d₁ Ls)) : Set (GPtV d₀ d₁ Ls) := (· + g) '' E

theorem mem_gtransl {g h : GPtV d₀ d₁ Ls} {E : Set (GPtV d₀ d₁ Ls)} :
    h ∈ gtransl g E ↔ h - g ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩; simpa using he
  · intro h'; exact ⟨h - g, h', by simp⟩

theorem gtransl_gtransl_neg (g : GPtV d₀ d₁ Ls) (E : Set (GPtV d₀ d₁ Ls)) :
    gtransl (-g) (gtransl g E) = E := by
  ext h; simp [mem_gtransl, sub_eq_add_neg]

/-- The cone coordinates of `g` with scalars `ν` (which may vanish). -/
noncomputable def coordsZ (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) : Var d₀ d₁ m → ℂ
  | .x i => g.1 i
  | .y j => (g.ym j : ℂ)
  | .z j => ((g.ym j)⁻¹ : ℂˣ)
  | .e k c => ν k * repV (g.2.2 k) c

/-- The cone representative of `g` with scalings `λ`. -/
noncomputable def coords (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) : Var d₀ d₁ m → ℂ :=
  coordsZ g fun k => (lam k : ℂ)

@[simp] theorem coordsZ_x (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (i : Fin d₀) :
    coordsZ g ν (.x i) = g.1 i := rfl
@[simp] theorem coordsZ_y (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (j : Fin d₁) :
    coordsZ g ν (.y j) = (g.ym j : ℂ) := rfl
@[simp] theorem coordsZ_z (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (j : Fin d₁) :
    coordsZ g ν (.z j) = ((g.ym j)⁻¹ : ℂˣ) := rfl
@[simp] theorem coordsZ_e (g : GPtV d₀ d₁ Ls) (ν : Fin m → ℂ) (k : Fin m) (c : Fin 5) :
    coordsZ g ν (.e k c) = ν k * repV (g.2.2 k) c := rfl

/-- The ideal of polynomials vanishing at every cone representative of every point of `E`. -/
noncomputable def vanish (E : Set (GPtV d₀ d₁ Ls)) : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ) :=
  StrongSix.M2.vanish' (fun p : GPtV d₀ d₁ Ls × (Fin m → ℂˣ) => coords p.1 p.2) (E ×ˢ Set.univ)

theorem mem_vanish {E : Set (GPtV d₀ d₁ Ls)} {P : MvPolynomial (Var d₀ d₁ m) ℂ} :
    P ∈ vanish E ↔ ∀ g ∈ E, ∀ lam, eval (coords g lam) P = 0 := by
  rw [vanish, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg lam; exact h (g, lam) ⟨hg, Set.mem_univ _⟩
  · rintro h ⟨g, lam⟩ ⟨hg, -⟩; exact h g hg lam

theorem vanish_antitone {E E' : Set (GPtV d₀ d₁ Ls)} (h : E ⊆ E') : vanish E' ≤ vanish E :=
  fun _ hP => mem_vanish.mpr fun g hg lam => mem_vanish.mp hP g (h hg) lam

theorem one_notMem_vanish {E : Set (GPtV d₀ d₁ Ls)} (hE : E.Nonempty) :
    (1 : MvPolynomial (Var d₀ d₁ m) ℂ) ∉ vanish E := by
  obtain ⟨g, hg⟩ := hE
  intro h
  simpa using mem_vanish.mp h g hg 1

theorem vanish_ne_top {E : Set (GPtV d₀ d₁ Ls)} (hE : E.Nonempty) : vanish E ≠ ⊤ :=
  fun h => one_notMem_vanish hE (h ▸ Submodule.mem_top)

/-- The points of `G̃` at all of whose cone representatives every polynomial of `𝒫` vanishes. -/
def zeros (Ps : Set (MvPolynomial (Var d₀ d₁ m) ℂ)) : Set (GPtV d₀ d₁ Ls) :=
  {g | ∀ P ∈ Ps, ∀ lam, eval (coords g lam) P = 0}

theorem mem_zeros_iff_le_vanish {J : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {g : GPtV d₀ d₁ Ls} :
    g ∈ zeros (J : Set _) ↔ J ≤ vanish {g} := by
  simp only [zeros, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam

theorem mem_zeros_span {s : Set (MvPolynomial (Var d₀ d₁ m) ℂ)} {g : GPtV d₀ d₁ Ls} :
    g ∈ zeros (Ideal.span s : Set _) ↔ g ∈ zeros s := by
  rw [mem_zeros_iff_le_vanish, Ideal.span_le]
  simp only [zeros, Set.mem_ofPred_eq]
  constructor
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam

/-! ### Zero scalars: a density argument -/

/-- **Density.** A polynomial vanishing at `coords g λ` for all `λ` vanishes at `coordsZ g ν` for
all `ν` (along the line `t ↦ (ν, zero entries replaced by t)`). -/
theorem eval_coordsZ_eq_zero {g : GPtV d₀ d₁ Ls} {P : MvPolynomial (Var d₀ d₁ m) ℂ}
    (hP : ∀ lam, eval (coords g lam) P = 0) (ν : Fin m → ℂ) : eval (coordsZ g ν) P = 0 := by
  classical
  let φ : Var d₀ d₁ m → Polynomial ℂ := fun v => match v with
    | .x i => Polynomial.C (g.1 i)
    | .y j => Polynomial.C (g.ym j : ℂ)
    | .z j => Polynomial.C (((g.ym j)⁻¹ : ℂˣ) : ℂ)
    | .e k c => (if ν k = 0 then Polynomial.X else Polynomial.C (ν k)) *
        Polynomial.C (repV (g.2.2 k) c)
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
        · simp only [φ, coords, coordsZ_e, lam, h, dite_eq_left, ite_true, Units.val_mk0,
            Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
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
  | x i => simp [φ]
  | y j => simp [φ]
  | z j => simp [φ]
  | e k c => by_cases h : ν k = 0 <;> simp [φ, h]

/-! ### Relevance -/

/-- A cone vector is **relevant** if the base part of every `E^♮` block is nonzero. -/
def IsRelevant (x : Var d₀ d₁ m → ℂ) : Prop := ∀ k, ∃ c : Fin 3, x (eb k c) ≠ 0

/-- The irrelevant ideal `(U_k, V_k, W_k)` of block `k`. -/
noncomputable def irrel (K : Type*) [Field K] (d₀ d₁ : ℕ) (k : Fin m) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  Ideal.span (Set.range fun c : Fin 3 => X (eb k c))

/-- An ideal is **relevant** if it contains no block irrelevant ideal. -/
def IdealRelevant {K : Type*} [Field K] (p : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Prop :=
  ∀ k, ¬ irrel K d₀ d₁ k ≤ p

/-- Cone representatives with nonzero scalars are relevant. -/
theorem coords_isRelevant (g : GPtV d₀ d₁ Ls) (lam : Fin m → ℂˣ) : IsRelevant (coords g lam) := by
  intro k
  have hne : Pe (repV (g.2.2 k)) ≠ 0 := by rw [Pe_repV]; exact rep_ne_zero _
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
  refine ⟨c, ?_⟩
  simp only [coords, coordsZ_e, eb]
  rw [Pe_apply] at hc
  exact mul_ne_zero (lam k).ne_zero hc

/-- If an ideal vanishes at a relevant vector, it is relevant. -/
theorem idealRelevant_of_eval {p : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {x : Var d₀ d₁ m → ℂ}
    (hx : IsRelevant x) (hp : ∀ P ∈ p, eval x P = 0) : IdealRelevant p := by
  intro k hk
  obtain ⟨c, hc⟩ := hx k
  exact hc (by simpa using hp _ (hk (Ideal.subset_span ⟨c, rfl⟩)))

/-- The zeros of an ideal containing `irrel k` are empty. -/
theorem zeros_eq_empty_of_irrel {p : Ideal (MvPolynomial (Var d₀ d₁ m) ℂ)} {k : Fin m}
    (hk : irrel ℂ d₀ d₁ k ≤ p) : zeros (p : Set _) = (∅ : Set (GPtV d₀ d₁ Ls)) := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  exact idealRelevant_of_eval (coords_isRelevant g 1) (fun P hP => hg P hP 1) k hk

end LSG.MEV
