import Mathlib
import LSG.Elliptic.AdditionLawsGroup
import StrongSix.M2.SeparateGen

/-!
# The multi-cone model of `G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (STAGE2 §2)

Each elliptic factor `E_k : V²W = 4U³ − g₂ₖ U W² − g₃ₖ W³` is modelled by its affine cone in `K³`.

* `Var d₀ d₁ m`: the variables `X i` (`G_a`), `Y j`, `Z j` (`G_m`, with `Y Z = 1`), and the cone
  coordinates `e k c` (`c : Fin 3`, `U, V, W`) of each elliptic factor.
* `Blk m`, `blk`: the blocks `X`, `(Y, Z)`, and one block per elliptic factor.
* `GPt K d₀ d₁ g₂ g₃`: the points of `G` (an additive group: the `G_m` part is written additively).
  The elliptic points are Mathlib's `WeierstrassCurve.Affine.Point` on `LSG.Elliptic.curve`.
* `coords g λ`: the cone representative of `g` with scalings `λ : Fin m → Kˣ`
  (`(k, c) ↦ λₖ · rep(gₖ) c`), and `coordsZ g ν` with `ν : Fin m → K` (scalars may vanish).
* `vanish E`: polynomials vanishing at every cone representative of every point of `E` (the
  generic `StrongSix.M2.vanish'` on pairs `(g, λ)`); `zeros 𝒫`; `IsSubgroupG`; `gtransl`.
* `eval_coordsZ_eq_zero`: (`K` infinite) a polynomial vanishing at `coords g λ` for all `λ`
  vanishes at `coordsZ g ν` for all `ν` (zero scalars included).
* `exists_smul_rep`: a nonzero cone vector on `E` is a nonzero multiple of `rep` of its point.
-/

open MvPolynomial LSG.Elliptic

namespace LSG.ME

/-- The variables: `x i` (`G_a`), `y j`, `z j` (`G_m`), and the cone coordinates `e k c`. -/
inductive Var (d₀ d₁ m : ℕ)
  | x (i : Fin d₀)
  | y (j : Fin d₁)
  | z (j : Fin d₁)
  | e (k : Fin m) (c : Fin 3)
  deriving DecidableEq, Fintype

/-- The blocks: `X`, `(Y, Z)`, and one block per elliptic factor. -/
inductive Blk (m : ℕ)
  | x
  | yz
  | e (k : Fin m)
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
@[simp] theorem blk_e (k : Fin m) (c : Fin 3) : blk (.e k c : Var d₀ d₁ m) = .e k := rfl

variable {K : Type*} [Field K]

/-- The points of the `k`-th elliptic factor. -/
abbrev EPt (g₂ g₃ : Fin m → K) (k : Fin m) : Type _ := (curve (g₂ k) (g₃ k)).toAffine.Point

/-- The points of `G = G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`. -/
abbrev GPt (K : Type*) [Field K] (d₀ d₁ : ℕ) {m : ℕ} (g₂ g₃ : Fin m → K) : Type _ :=
  (Fin d₀ → K) × Additive (Fin d₁ → Kˣ) × (∀ k, EPt g₂ g₃ k)

variable {g₂ g₃ : Fin m → K}

/-- The `G_m` coordinates of a point. -/
def GPt.ym (g : GPt K d₀ d₁ g₂ g₃) (j : Fin d₁) : Kˣ := Additive.toMul g.2.1 j

section Group

variable [DecidableEq K]

@[simp] theorem GPt.ym_add (g h : GPt K d₀ d₁ g₂ g₃) (j : Fin d₁) :
    (g + h).ym j = g.ym j * h.ym j := rfl

omit [DecidableEq K] in
@[simp] theorem GPt.ym_neg (g : GPt K d₀ d₁ g₂ g₃) (j : Fin d₁) : (-g).ym j = (g.ym j)⁻¹ := rfl

omit [DecidableEq K] in
@[simp] theorem GPt.ym_zero (j : Fin d₁) : (0 : GPt K d₀ d₁ g₂ g₃).ym j = 1 := rfl

/-- A subgroup of `G`. -/
structure IsSubgroupG (E : Set (GPt K d₀ d₁ g₂ g₃)) : Prop where
  zero_mem : 0 ∈ E
  add_mem : ∀ g ∈ E, ∀ h ∈ E, g + h ∈ E
  neg_mem : ∀ g ∈ E, -g ∈ E

/-- The translate `E + g`. -/
def gtransl (g : GPt K d₀ d₁ g₂ g₃) (E : Set (GPt K d₀ d₁ g₂ g₃)) : Set (GPt K d₀ d₁ g₂ g₃) :=
  (· + g) '' E

theorem mem_gtransl {g h : GPt K d₀ d₁ g₂ g₃} {E : Set (GPt K d₀ d₁ g₂ g₃)} :
    h ∈ gtransl g E ↔ h - g ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩; simpa using he
  · intro h'; exact ⟨h - g, h', by simp⟩

theorem gtransl_gtransl_neg (g : GPt K d₀ d₁ g₂ g₃) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    gtransl (-g) (gtransl g E) = E := by
  ext h; simp [mem_gtransl, sub_eq_add_neg]

end Group

/-- The cone coordinates of `g` with scalars `ν : Fin m → K` (which may vanish). -/
def coordsZ (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → K) : Var d₀ d₁ m → K
  | .x i => g.1 i
  | .y j => (g.ym j : K)
  | .z j => ((g.ym j)⁻¹ : Kˣ)
  | .e k c => ν k * rep (g.2.2 k) c

/-- The cone representative of `g` with scalings `λ : Fin m → Kˣ`. -/
def coords (g : GPt K d₀ d₁ g₂ g₃) (lam : Fin m → Kˣ) : Var d₀ d₁ m → K :=
  coordsZ g fun k => (lam k : K)

@[simp] theorem coordsZ_x (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → K) (i : Fin d₀) :
    coordsZ g ν (.x i) = g.1 i := rfl
@[simp] theorem coordsZ_y (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → K) (j : Fin d₁) :
    coordsZ g ν (.y j) = (g.ym j : K) := rfl
@[simp] theorem coordsZ_z (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → K) (j : Fin d₁) :
    coordsZ g ν (.z j) = ((g.ym j)⁻¹ : Kˣ) := rfl
@[simp] theorem coordsZ_e (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → K) (k : Fin m) (c : Fin 3) :
    coordsZ g ν (.e k c) = ν k * rep (g.2.2 k) c := rfl

/-- The ideal of polynomials vanishing at every cone representative of every point of `E`. -/
def vanish (E : Set (GPt K d₀ d₁ g₂ g₃)) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  StrongSix.M2.vanish' (fun p : GPt K d₀ d₁ g₂ g₃ × (Fin m → Kˣ) => coords p.1 p.2)
    (E ×ˢ Set.univ)

theorem mem_vanish {E : Set (GPt K d₀ d₁ g₂ g₃)} {P : MvPolynomial (Var d₀ d₁ m) K} :
    P ∈ vanish E ↔ ∀ g ∈ E, ∀ lam, eval (coords g lam) P = 0 := by
  rw [vanish, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg lam; exact h (g, lam) ⟨hg, Set.mem_univ _⟩
  · rintro h ⟨g, lam⟩ ⟨hg, -⟩; exact h g hg lam

theorem vanish_antitone {E E' : Set (GPt K d₀ d₁ g₂ g₃)} (h : E ⊆ E') : vanish E' ≤ vanish E :=
  fun _ hP => mem_vanish.mpr fun g hg lam => mem_vanish.mp hP g (h hg) lam

theorem one_notMem_vanish {E : Set (GPt K d₀ d₁ g₂ g₃)} (hE : E.Nonempty) :
    (1 : MvPolynomial (Var d₀ d₁ m) K) ∉ vanish E := by
  obtain ⟨g, hg⟩ := hE
  intro h
  simpa using mem_vanish.mp h g hg 1

theorem vanish_ne_top {E : Set (GPt K d₀ d₁ g₂ g₃)} (hE : E.Nonempty) : vanish E ≠ ⊤ :=
  fun h => one_notMem_vanish hE (h ▸ Submodule.mem_top)

/-- The points of `G` at all of whose cone representatives every polynomial of `𝒫` vanishes. -/
def zeros (Ps : Set (MvPolynomial (Var d₀ d₁ m) K)) : Set (GPt K d₀ d₁ g₂ g₃) :=
  {g | ∀ P ∈ Ps, ∀ lam, eval (coords g lam) P = 0}

theorem mem_zeros_iff_le_vanish {J : Ideal (MvPolynomial (Var d₀ d₁ m) K)}
    {g : GPt K d₀ d₁ g₂ g₃} : g ∈ zeros (J : Set _) ↔ J ≤ vanish {g} := by
  simp only [zeros, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam

theorem mem_zeros_span {s : Set (MvPolynomial (Var d₀ d₁ m) K)} {g : GPt K d₀ d₁ g₂ g₃} :
    g ∈ zeros (Ideal.span s : Set _) ↔ g ∈ zeros s := by
  rw [mem_zeros_iff_le_vanish, Ideal.span_le]
  simp only [zeros, Set.mem_ofPred_eq]
  constructor
  · intro h P hP lam; exact mem_vanish.mp (h hP) g rfl lam
  · intro h P hP; exact mem_vanish.mpr fun g' hg' lam => (Set.mem_singleton_iff.mp hg') ▸ h P hP lam

/-! ### Zero scalars: a density argument -/

/-- **Density.** A polynomial vanishing at `coords g λ` for all `λ` vanishes at `coordsZ g ν` for
all `ν : Fin m → K` (`K` infinite): along the line `t ↦ (ν, zero entries replaced by t)`. -/
theorem eval_coordsZ_eq_zero [Infinite K] {g : GPt K d₀ d₁ g₂ g₃} {P : MvPolynomial (Var d₀ d₁ m) K}
    (hP : ∀ lam, eval (coords g lam) P = 0) (ν : Fin m → K) : eval (coordsZ g ν) P = 0 := by
  classical
  let φ : Var d₀ d₁ m → Polynomial K := fun v => match v with
    | .x i => Polynomial.C (g.1 i)
    | .y j => Polynomial.C (g.ym j : K)
    | .z j => Polynomial.C (((g.ym j)⁻¹ : Kˣ) : K)
    | .e k c => (if ν k = 0 then Polynomial.X else Polynomial.C (ν k)) *
        Polynomial.C (rep (g.2.2 k) c)
  set Q := MvPolynomial.aeval φ P
  have hev : ∀ t : K, Q.eval t = eval (fun v => (φ v).eval t) P := by
    intro t
    rw [show Q = MvPolynomial.aeval φ P from rfl, MvPolynomial.aeval_def,
      MvPolynomial.polynomial_eval_eval₂]
    have : (Polynomial.evalRingHom t).comp (algebraMap K (Polynomial K)) = RingHom.id K := by
      ext; simp
    rw [this]; rfl
  have hroot : ∀ t : K, t ≠ 0 → Q.IsRoot t := by
    intro t ht
    rw [Polynomial.IsRoot, hev]
    let lam : Fin m → Kˣ := fun k => if h : ν k = 0 then Units.mk0 t ht else
      Units.mk0 (ν k) h
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
    refine Set.Infinite.mono (s := ({0}ᶜ : Set K)) (fun t ht => hroot t ht) ?_
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

/-! ### Cone vectors and points -/

section Cone

variable {a b : K} (h2 : (2 : K) ≠ 0) (hΔ : a ^ 3 - 27 * b ^ 2 ≠ 0)
include h2 hΔ

/-- A nonzero cone vector on `E` is a nonzero multiple of the representative of its point. -/
theorem exists_smul_rep {P : Fin 3 → K} (hP : Fv a b P = 0) (hP0 : P ≠ 0) :
    ∃ u : K, u ≠ 0 ∧ P = u • rep (toPoint a b P) :=
  (toPoint_eq_iff h2 hΔ hP (Fv_rep h2 _) hP0 (rep_ne_zero _)).mp (toPoint_rep h2 _).symm

end Cone

end LSG.ME
