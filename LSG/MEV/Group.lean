import Mathlib
import LSG.Elliptic.NaturalGroupFull
import LSG.ME.SubgroupExpSurj

/-!
# Points of `E^♮` and the group law (VECEXT_SPIKE §2.2, §4.2)

**Representatives (any field).** A point of `E^♮` is a pair `(P, t)` of a point `P` of `E`
(Mathlib's `WeierstrassCurve.Affine.Point` on `LSG.Elliptic.curve`) and a fibre coordinate `t`:
the affine fibre coordinate `t = w − ζ(z)` over an affine point, the regular coordinate
`w' = T₃/V` over `O` (the "`O`-fibre chart"). Its cone representative in the model
`X = V(F, G) ⊂ ℙ⁴` (coordinates `(U, V, W, T₁, T₃)`) is `repB P t`:
`(x : 2y : 1 : t : 2y t − 2x²)` over `P = (x, y)` (Mathlib's `y = ℘'/2`) and `(0 : 1 : 0 : 0 : t)` over
`O`.
* `Fn_repB`, `Gn_repB`, `Pe_repB` (the base part is `LSG.Elliptic.rep P`), `Pe_repB_ne_zero`;
* **`exists_smul_repB`**: every vector on `X` with nonzero base part is a nonzero multiple of a
  representative (so `X ∖ {U = V = W = 0}` is `E^♮`).

**The group over `ℂ`.** For a period pair `L`, `EVL L` (base point + fibre coordinate) carries the
group law `(P, s) + (Q, t) = (P + Q, s + t − c(P, Q))`, `c(expE u, expE v) = ζ(u+v) − ζ(u) − ζ(v)`
(`cc`, independent of the choice of `u, v` by quasi-periodicity, `cc_expE`), transported from
`ℂ²` along the surjective map `expV (z, w) = (expE z, w − ζ(z))` (`expV_add`, `expV_surjective`).
* `repV_expV`: `repV (expV (z, w)) = expN z w` (the spike's analytic exponential);
* **`NLaw_repV`**: every one of the eight laws maps `(repV a, repV b)` to a multiple of
  `repV (a + b)`; **`exists_NLaw_ne`**: some law is nonzero there (completeness).
-/

open LSG.Elliptic LSG.Weierstrass PeriodPair

namespace LSG.MEV

/-! ### Representatives over a field -/

section Rep

variable {K : Type*} [Field K] {g₂ g₃ : K}

/-- The cone representative of `(P, t)`: `(x : 2y : 1 : t : 2yt − 2x²)`, resp. `(0 : 1 : 0 : 0 : t)`. -/
def repB : (curve g₂ g₃).toAffine.Point → K → Fin 5 → K
  | 0, t => ptO t
  | .some x y _, t => ptAff x (2 * y) t

@[simp] theorem repB_zero (t : K) : repB (0 : (curve g₂ g₃).toAffine.Point) t = ptO t := rfl

theorem Pe_repB (P : (curve g₂ g₃).toAffine.Point) (t : K) : Pe (repB P t) = rep P := by
  cases P with
  | zero => funext i; fin_cases i <;> rfl
  | some x y h => funext i; fin_cases i <;> rfl

theorem Pe_repB_ne_zero (P : (curve g₂ g₃).toAffine.Point) (t : K) : Pe (repB P t) ≠ 0 := by
  rw [Pe_repB]; exact rep_ne_zero P

theorem Fn_repB (h2 : (2 : K) ≠ 0) (P : (curve g₂ g₃).toAffine.Point) (t : K) :
    Fn g₂ g₃ (repB P t) = 0 := by
  rw [Fn_eq_Fv, Pe_repB]; exact Fv_rep h2 P

theorem Gn_repB (P : (curve g₂ g₃).toAffine.Point) (t : K) : Gn (repB P t) = 0 := by
  cases P with
  | zero => exact Gn_ptO t
  | some x y h => exact Gn_ptAff _ _ _

theorem repB_ne_zero (P : (curve g₂ g₃).toAffine.Point) (t : K) : repB P t ≠ 0 := fun h =>
  Pe_repB_ne_zero P t (by rw [h]; funext i; fin_cases i <;> rfl)

/-- The fibre translation `(P, t) ↦ (P, t + v)` is linear on representatives:
`T₁ ↦ T₁ + v W`, `T₃ ↦ T₃ + v V`. -/
theorem repB_add_fib (P : (curve g₂ g₃).toAffine.Point) (t v : K) :
    repB P (t + v) = repB P t + v • fibv (repB P t) := by
  cases P with
  | zero => funext i; fin_cases i <;> simp [repB, ptO, fibv]
  | some x y h => funext i; fin_cases i <;> simp [repB, ptAff, fibv]; ring

/-- **Every vector of `X` with nonzero base part is a nonzero multiple of a representative.** -/
theorem exists_smul_repB (h2 : (2 : K) ≠ 0) (hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0) {P : Fin 5 → K}
    (hF : Fn g₂ g₃ P = 0) (hG : Gn P = 0) (hP : Pe P ≠ 0) :
    ∃ (b : (curve g₂ g₃).toAffine.Point) (t u : K), u ≠ 0 ∧ P = u • repB b t := by
  rw [Fn_eq_Fv] at hF
  obtain ⟨u, hu, he⟩ := LSG.ME.exists_smul_rep h2 hΔ hF hP
  generalize toPoint g₂ g₃ (Pe P) = b at he
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  have e2 := congrFun he 2
  simp only [Pe, Pi.smul_apply, smul_eq_mul] at e0 e1 e2
  simp only [Gn, Gfib] at hG
  cases b with
  | zero =>
    simp only [rep, LSG.Elliptic.O, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero, mul_one] at e0 e1 e2
    have hT : P 3 = 0 := by
      rw [e0, e1, e2] at hG
      have : u * P 3 = 0 := by linear_combination -hG
      exact (mul_eq_zero.mp this).resolve_left hu
    refine ⟨0, P 4 / u, u, hu, ?_⟩
    funext i
    fin_cases i <;> simp [ptO, e0, e1, e2, hT, mul_div_cancel₀ _ hu]
  | some x y h =>
    simp only [rep, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one] at e0 e1 e2
    refine ⟨.some x y h, P 3 / u, u, hu, ?_⟩
    funext i
    fin_cases i <;> simp [repB, ptAff, e0, e1, e2, mul_div_cancel₀ _ hu]
    rw [e0, e1, e2] at hG
    have h' : P 4 = 2 * y * P 3 - 2 * u * x ^ 2 := by
      have : u * (P 4 - (2 * y * P 3 - 2 * u * x ^ 2)) = 0 := by linear_combination hG
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hu)
    rw [h']; field_simp

end Rep

/-! ### The points of `E^♮` over `ℂ` and the group law -/

noncomputable section

variable (L : PeriodPair)

/-- **The points of `E^♮`** for the lattice `L`: a point of `E` and a fibre coordinate (the
affine coordinate `t = w − ζ(z)` over affine points, `w' = T₃/V` over `O`). -/
@[ext] structure EVL where
  /-- the base point in `E` -/
  base : (curve L.g₂ L.g₃).toAffine.Point
  /-- the fibre coordinate -/
  fib : ℂ

variable {L}

/-- The cone representative of a point of `E^♮`. -/
def repV (p : EVL L) : Fin 5 → ℂ := repB p.base p.fib

theorem Pe_repV (p : EVL L) : Pe (repV p) = rep p.base := Pe_repB _ _

theorem Fn_repV (p : EVL L) : Fn L.g₂ L.g₃ (repV p) = 0 := Fn_repB two_ne_zero _ _

theorem Gn_repV (p : EVL L) : Gn (repV p) = 0 := Gn_repB _ _

theorem repV_ne_zero (p : EVL L) : repV p ≠ 0 := repB_ne_zero _ _

variable (L)

/-- A preimage of a point of `E` under `expE`. -/
noncomputable def pick (P : (curve L.g₂ L.g₃).toAffine.Point) : ℂ :=
  (LSG.ME.expE_surjective L P).choose

theorem expE_pick (P : (curve L.g₂ L.g₃).toAffine.Point) : expE L (pick L P) = P :=
  (LSG.ME.expE_surjective L P).choose_spec

/-- The cocycle `c(P, Q) = ζ(u + v) − ζ(u) − ζ(v)` for `expE u = P`, `expE v = Q`. -/
noncomputable def cc (P Q : (curve L.g₂ L.g₃).toAffine.Point) : ℂ :=
  zeta L (pick L P + pick L Q) - zeta L (pick L P) - zeta L (pick L Q)

variable {L}

theorem expE_ne_zero {u : ℂ} (hu : u ∉ L.lattice) : expE L u ≠ 0 := by
  rw [expE_of_notMem L hu]; exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem sub_mem_of_expE_eq {u v : ℂ} (h : expE L u = expE L v) : u - v ∈ L.lattice := by
  by_cases hu : u ∈ L.lattice
  · have hv : v ∈ L.lattice := by
      by_contra hv
      exact expE_ne_zero hv (by rw [← h, expE_of_mem L hu])
    exact sub_mem hu hv
  · have hv : v ∉ L.lattice := fun hv => expE_ne_zero hu (by rw [h, expE_of_mem L hv])
    rw [expE_of_notMem L hu, expE_of_notMem L hv] at h
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    rcases (weierstrassP_eq_iff L hv hu).mp hx with h' | h'
    · exact h'
    · have hd : ℘'[L] u = -℘'[L] v := by
        have := derivWeierstrassP_add_mem L (-v) h'
        rwa [show -v + (u + v) = u by ring, L.derivWeierstrassP_neg] at this
      have hy' : ℘'[L] u = ℘'[L] v := by linear_combination 2 * hy
      have h0 : ℘'[L] v = 0 := by linear_combination (hd - hy') / 2
      have h2v : 2 * v ∈ L.lattice := (derivWeierstrassP_eq_zero_iff L hv).mp h0
      have := sub_mem h' h2v
      rwa [show u + v - 2 * v = u - v by ring] at this

theorem zeta_of_sub_mem {u v : ℂ} (h : u - v ∈ L.lattice) :
    zeta L u = zeta L v + eta L (u - v) := by
  have := zeta_add L h v
  rwa [show v + (u - v) = u by ring] at this

/-- **The cocycle in terms of any preimages.** -/
theorem cc_expE (u v : ℂ) : cc L (expE L u) (expE L v) = zeta L (u + v) - zeta L u - zeta L v := by
  have hu := sub_mem_of_expE_eq (expE_pick L (expE L u))
  have hv := sub_mem_of_expE_eq (expE_pick L (expE L v))
  set u' := pick L (expE L u)
  set v' := pick L (expE L v)
  have huv : u' + v' - (u + v) ∈ L.lattice := by
    have := add_mem hu hv; rwa [show u' - u + (v' - v) = u' + v' - (u + v) by ring] at this
  rw [show cc L (expE L u) (expE L v) = zeta L (u' + v') - zeta L u' - zeta L v' from rfl,
    zeta_of_sub_mem hu, zeta_of_sub_mem hv, zeta_of_sub_mem huv,
    show u' + v' - (u + v) = (u' - u) + (v' - v) by ring, eta_add L hu hv]
  ring

instance : Add (EVL L) := ⟨fun a b => ⟨a.base + b.base, a.fib + b.fib - cc L a.base b.base⟩⟩
instance : Zero (EVL L) := ⟨⟨0, 0⟩⟩
instance : Neg (EVL L) := ⟨fun a => ⟨-a.base, -a.fib⟩⟩

@[simp] theorem add_base (a b : EVL L) : (a + b).base = a.base + b.base := rfl
@[simp] theorem add_fib (a b : EVL L) : (a + b).fib = a.fib + b.fib - cc L a.base b.base := rfl
@[simp] theorem zero_base : (0 : EVL L).base = 0 := rfl
@[simp] theorem zero_fib : (0 : EVL L).fib = 0 := rfl
@[simp] theorem neg_base (a : EVL L) : (-a).base = -a.base := rfl
@[simp] theorem neg_fib (a : EVL L) : (-a).fib = -a.fib := rfl

variable (L)

/-- **The exponential map of `E^♮`**: `(z, w) ↦ (expE z, w − ζ(z))`. -/
noncomputable def expV (p : ℂ × ℂ) : EVL L := ⟨expE L p.1, p.2 - zeta L p.1⟩

variable {L}

theorem expV_add (p q : ℂ × ℂ) : expV L (p + q) = expV L p + expV L q := by
  ext
  · exact expE_add L _ _
  · simp only [expV, Prod.fst_add, Prod.snd_add, add_fib, cc_expE]; ring

theorem expV_zero : expV L 0 = 0 := by
  ext
  · exact expE_zero L
  · simp [expV, zeta_zero' L]

theorem expV_neg (p : ℂ × ℂ) : expV L (-p) = -expV L p := by
  ext
  · exact expE_neg L _
  · simp only [expV, Prod.fst_neg, Prod.snd_neg, neg_fib, zeta_neg]; ring

theorem expV_surjective : Function.Surjective (expV L) := by
  intro a
  obtain ⟨u, hu⟩ := LSG.ME.expE_surjective L a.base
  exact ⟨(u, a.fib + zeta L u), EVL.ext hu (by simp [expV])⟩

/-- **The group `E^♮(ℂ)`.** -/
instance : AddCommGroup (EVL L) where
  add_assoc a b c := by
    obtain ⟨p, rfl⟩ := expV_surjective a
    obtain ⟨q, rfl⟩ := expV_surjective b
    obtain ⟨r, rfl⟩ := expV_surjective c
    simp only [← expV_add, add_assoc]
  zero_add a := by
    obtain ⟨p, rfl⟩ := expV_surjective a
    rw [← expV_zero, ← expV_add, zero_add]
  add_zero a := by
    obtain ⟨p, rfl⟩ := expV_surjective a
    rw [← expV_zero, ← expV_add, add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by
    obtain ⟨p, rfl⟩ := expV_surjective a
    rw [← expV_neg, ← expV_add, neg_add_cancel, expV_zero]
  add_comm a b := by
    obtain ⟨p, rfl⟩ := expV_surjective a
    obtain ⟨q, rfl⟩ := expV_surjective b
    rw [← expV_add, ← expV_add, add_comm]

/-- `expV` as an additive homomorphism. -/
noncomputable def expVHom : ℂ × ℂ →+ EVL L := AddMonoidHom.mk' (expV L) expV_add

theorem expV_base (p : ℂ × ℂ) : (expV L p).base = expE L p.1 := rfl

/-- The fibre direction: `(0, w)` acts by `t ↦ t + w`. -/
theorem add_expV_fib (a : EVL L) (w : ℂ) : a + expV L (0, w) = ⟨a.base, a.fib + w⟩ := by
  have hc : cc L a.base (expE L 0) = 0 := by
    rw [← expE_pick L a.base, cc_expE, add_zero, zeta_zero' L]; ring
  ext
  · simp only [add_base, expV_base, expE_zero L]; exact add_zero _
  · simp only [add_fib, expV, hc, zeta_zero' L]; ring

/-- **`repV ∘ expV` is the spike's `expN`.** -/
theorem repV_expV (z w : ℂ) : repV (expV L (z, w)) = expN L z w := by
  by_cases hz : z ∈ L.lattice
  · simp only [repV, expV, expN_of_mem L hz, expE_of_mem L hz]; rfl
  · simp only [repV, expV, expN_of_notMem L hz, expE_of_notMem L hz, repB]
    rw [mul_div_cancel₀ _ (two_ne_zero' ℂ)]

/-- **Law compatibility**: each of the eight laws maps `(repV a, repV b)` to a multiple of
`repV (a + b)`. -/
theorem NLaw_repV (a b : EVL L) (i j k : Fin 2) :
    ∃ c : ℂ, NLaw L.g₂ L.g₃ i j k (repV a) (repV b) = c • repV (a + b) := by
  obtain ⟨⟨z₁, w₁⟩, rfl⟩ := expV_surjective a
  obtain ⟨⟨z₂, w₂⟩, rfl⟩ := expV_surjective b
  rw [← expV_add, Prod.mk_add_mk, repV_expV, repV_expV, repV_expV]
  exact NLaw_expN_all L z₁ w₁ z₂ w₂ i j k

/-- **Completeness**: some law is nonzero at `(repV a, repV b)`. -/
theorem exists_NLaw_ne (a b : EVL L) :
    ∃ i j k : Fin 2, NLaw L.g₂ L.g₃ i j k (repV a) (repV b) ≠ 0 := by
  obtain ⟨i, j, k, -, -, -, h⟩ := NLaw_complete (two_ne_zero' ℂ) (discr_ne_zero L) (Fn_repV a)
    (Fn_repV b) (by rw [Pe_repV]; exact rep_ne_zero _) (by rw [Pe_repV]; exact rep_ne_zero _)
  exact ⟨i, j, k, h⟩

/-- A nonzero law is a **nonzero** multiple of `repV (a + b)`. -/
theorem NLaw_repV_ne (a b : EVL L) (i j k : Fin 2) (hne : NLaw L.g₂ L.g₃ i j k (repV a) (repV b) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ NLaw L.g₂ L.g₃ i j k (repV a) (repV b) = c • repV (a + b) := by
  obtain ⟨c, hc⟩ := NLaw_repV a b i j k
  refine ⟨c, fun h0 => hne ?_, hc⟩
  rw [hc, h0, zero_smul]

end

end LSG.MEV
