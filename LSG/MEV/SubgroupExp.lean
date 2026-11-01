import Mathlib
import LSG.MEV.SubgroupStab
import LSG.W88.StatementVec
import LSG.ME.ProductGraph

/-!
# The analytic exponential of `G̃` and the linear subgroup of a closed subgroup

Tangent space `T_G̃ = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^m ∋ (a, b, z, w)` (`TanG`, i.e. VECEXT's `TanV` with
`r = m`, `M = 1`): `z` base, `w` fibre coordinates of the `E_k^♮`.

* `expGV (a, b, z, w) = (a, e^b, expV(z_k, w_k))`: an additive homomorphism (`expGVHom`), onto
  (`expGV_surjective`), with kernel exactly `PerV Ls 1 = 0 × 2πiℤ^{d₁} × {(λ, η(λ))}`
  (**`expGV_eq_zero_iff`**).
* `Htil hH = exp⁻¹(H)` (an `AddSubgroup`) contains the periods (`per_le_Htil`);
  **`lieAlg hH`** `= {v | ℂ·v ⊆ H̃}` (a `ℂ`-subspace by definition; for `H` Zariski closed it equals
  the real linear part of `H̃` once the analytic `smul_mem_Htil` of `LSG.ME.SubgroupLie` is ported).
* **The linear subgroup.** `inLin : G_a^{d₀+m} × G_m^{d₁} → G̃`, `((a, w), y) ↦ (a, y, (O, w_k))`, is an
  injective homomorphism onto `G_a^{d₀} × G_m^{d₁} × (fibres over O)`. For a subgroup `H`,
  `HL H = inLin⁻¹(H)` is a StrongSix subgroup, Zariski closed if `H` is (`HL_eq_zeros`, substitution
  of the `O`-fibre chart `(0 : 1 : 0 : 0 : w)`), hence **`HL = V × T_Λ`** (`HL_eq_prodSet`, Roy's
  classification): a Zariski-closed subgroup of the vector group `G_a^{d₀} × (fibres)` is a
  `ℂ`-subspace — the algebraic input replacing the abelian "no `G_a` in `E`".
* `expGV_of_lattice`: at `z ∈ Λ^m`, `expGV (a, b, z, w) = inLin ((a, w − η(z)), e^b)`.
-/

open MvPolynomial LSG.Elliptic LSG.Weierstrass
open LSG.W88.Vec (TanV PerV etaV)

namespace LSG.MEV

noncomputable section

/-- The tangent space `ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^m` of `G̃`. -/
abbrev TanG (d₀ d₁ m : ℕ) := TanV d₀ d₁ m m

variable {d₀ d₁ m : ℕ} (Ls : Fin m → PeriodPair)

/-- **The exponential map of `G̃`.** -/
noncomputable def expGV (p : TanG d₀ d₁ m) : GPtV d₀ d₁ Ls :=
  (p.1, Additive.ofMul (fun j => LSG.ME.expU (p.2.1 j)),
    fun k => expV (Ls k) (p.2.2.1 k, p.2.2.2 k))

theorem expU_add (a b : ℂ) : LSG.ME.expU (a + b) = LSG.ME.expU a * LSG.ME.expU b :=
  Units.ext (by simp [LSG.ME.expU, Complex.exp_add])

theorem expGV_add (p q : TanG d₀ d₁ m) : expGV Ls (p + q) = expGV Ls p + expGV Ls q := by
  refine Prod.ext rfl (Prod.ext ?_ (funext fun k => ?_))
  · exact Additive.toMul.injective (funext fun j => expU_add (p.2.1 j) (q.2.1 j))
  · show expV (Ls k) ((p + q).2.2.1 k, (p + q).2.2.2 k) =
      expV (Ls k) (p.2.2.1 k, p.2.2.2 k) + expV (Ls k) (q.2.2.1 k, q.2.2.2 k)
    rw [← expV_add]; rfl

/-- `expGV` as an additive homomorphism. -/
noncomputable def expGVHom : TanG d₀ d₁ m →+ GPtV d₀ d₁ Ls :=
  AddMonoidHom.mk' (expGV Ls) (expGV_add Ls)

@[simp] theorem expGVHom_apply (p : TanG d₀ d₁ m) : expGVHom Ls p = expGV Ls p := rfl

theorem expGV_zero : expGV (d₀ := d₀) (d₁ := d₁) Ls 0 = 0 := (expGVHom Ls).map_zero

theorem expGV_surjective : Function.Surjective (expGV (d₀ := d₀) (d₁ := d₁) Ls) := by
  intro g
  choose p hp using fun k => expV_surjective (g.2.2 k)
  refine ⟨(g.1, fun j => Complex.log (g.ym j : ℂ), fun k => (p k).1, fun k => (p k).2), ?_⟩
  refine Prod.ext rfl (Prod.ext ?_ (funext fun k => hp k))
  show Additive.ofMul _ = g.2.1
  apply Additive.toMul.injective
  funext j
  exact Units.ext (Complex.exp_log (g.ym j).ne_zero)

theorem expV_fib (L : PeriodPair) (w : ℂ) : expV L (0, w) = ⟨0, w⟩ :=
  EVL.ext (expE_zero L) (by simp [expV, zeta_zero' L])

theorem expV_of_mem (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) (w : ℂ) :
    expV L (z, w) = ⟨0, w - eta L z⟩ :=
  EVL.ext (expE_of_mem L hz) (by simp [expV, LSG.W88.Vec.zeta_of_mem_lattice L hz])

/-- **The kernel of `expGV` is `PerV Ls 1`.** -/
theorem expGV_eq_zero_iff (p : TanG d₀ d₁ m) : expGV Ls p = 0 ↔ p ∈ PerV Ls 1 := by
  have hη : (1 : Matrix (Fin m) (Fin m) ℂ).mulVec (etaV Ls p.2.2.1) = etaV Ls p.2.2.1 :=
    Matrix.one_mulVec _
  constructor
  · intro h
    have h1 : p.1 = 0 := congrArg Prod.fst h
    have h2 : ∀ j, Complex.exp (p.2.1 j) = 1 := fun j => by
      have := congrArg (fun g : GPtV d₀ d₁ Ls => (g.ym j : ℂ)) h
      simpa [expGV, GPtV.ym, LSG.ME.expU] using this
    have h3 : ∀ k, expV (Ls k) (p.2.2.1 k, p.2.2.2 k) = 0 := fun k =>
      congrFun (congrArg (fun g : GPtV d₀ d₁ Ls => g.2.2) h) k
    have hz : ∀ k, p.2.2.1 k ∈ (Ls k).lattice := fun k => by
      by_contra hk
      exact expE_ne_zero hk (congrArg EVL.base (h3 k))
    refine ⟨h1, fun j => ?_, hz, ?_⟩
    · obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (h2 j)
      exact ⟨n, by rw [hn]; ring⟩
    · rw [hη]
      funext k
      have := congrArg EVL.fib (h3 k)
      rw [expV_of_mem _ (hz k)] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2, hz, hw⟩
    rw [hη] at hw
    refine Prod.ext h1 (Prod.ext ?_ (funext fun k => ?_))
    · apply Additive.toMul.injective
      funext j
      obtain ⟨n, hn⟩ := h2 j
      refine Units.ext ?_
      show Complex.exp (p.2.1 j) = 1
      rw [hn, Complex.exp_eq_one_iff]
      exact ⟨n, by ring⟩
    · show expV (Ls k) (p.2.2.1 k, p.2.2.2 k) = 0
      rw [expV_of_mem _ (hz k), hw]
      exact EVL.ext rfl (by simp [etaV])

/-! ### `H̃` and the Lie algebra -/

variable {Ls} {H : Set (GPtV d₀ d₁ Ls)}

/-- A subgroup as an `AddSubgroup`. -/
def IsSubgroupG.toAddSubgroupV (hH : IsSubgroupG H) : AddSubgroup (GPtV d₀ d₁ Ls) where
  carrier := H
  add_mem' {a b} ha hb := hH.add_mem a ha b hb
  zero_mem' := hH.zero_mem
  neg_mem' {a} ha := hH.neg_mem a ha

variable (Ls) in
/-- `H̃ = exp⁻¹(H)`. -/
def Htil (hH : IsSubgroupG H) : AddSubgroup (TanG d₀ d₁ m) :=
  hH.toAddSubgroupV.comap (expGVHom Ls)

theorem mem_Htil {hH : IsSubgroupG H} {p : TanG d₀ d₁ m} : p ∈ Htil Ls hH ↔ expGV Ls p ∈ H :=
  Iff.rfl

/-- **The periods lie in `H̃`.** -/
theorem per_le_Htil (hH : IsSubgroupG H) : PerV Ls 1 ≤ Htil Ls hH := fun p hp => by
  rw [mem_Htil, (expGV_eq_zero_iff Ls p).mpr hp]
  exact hH.zero_mem

variable (Ls) in
/-- **The Lie algebra** `{v | ℂ · v ⊆ H̃}`. -/
def lieAlg (hH : IsSubgroupG H) : Submodule ℂ (TanG d₀ d₁ m) where
  carrier := {v | ∀ c : ℂ, c • v ∈ Htil Ls hH}
  add_mem' {u v} hu hv c := by rw [smul_add]; exact (Htil Ls hH).add_mem (hu c) (hv c)
  zero_mem' c := by rw [smul_zero]; exact (Htil Ls hH).zero_mem
  smul_mem' a v hv c := by rw [smul_smul]; exact hv (c * a)

theorem mem_lieAlg {hH : IsSubgroupG H} {v : TanG d₀ d₁ m} :
    v ∈ lieAlg Ls hH ↔ ∀ c : ℂ, expGV Ls (c • v) ∈ H := Iff.rfl

theorem lieAlg_le_Htil {hH : IsSubgroupG H} {v : TanG d₀ d₁ m} (hv : v ∈ lieAlg Ls hH) :
    v ∈ Htil Ls hH := by simpa using hv 1

/-! ### The linear subgroup `G_a^{d₀} × G_m^{d₁} × (fibres over O)` -/

/-- The points of the linear group `G_a^{d₀+m} × G_m^{d₁}` (StrongSix). -/
abbrev LPt (d₀ d₁ m : ℕ) := StrongSix.Thm1.GPt ℂ (d₀ + m) d₁

variable (Ls) in
/-- `((a, w), y) ↦ (a, y, (O, w_k))`. -/
def inLin (g : LPt d₀ d₁ m) : GPtV d₀ d₁ Ls :=
  (fun i => g.1 (Fin.castAdd m i), Additive.ofMul g.2, fun k => ⟨0, g.1 (Fin.natAdd d₀ k)⟩)

theorem evl_fib_add (L : PeriodPair) (a b : ℂ) : (⟨0, a⟩ : EVL L) + ⟨0, b⟩ = ⟨0, a + b⟩ := by
  rw [← expV_fib, ← expV_fib, ← expV_add, Prod.mk_add_mk, add_zero, expV_fib]

theorem inLin_zero : inLin Ls (StrongSix.Thm1.GPt.zero : LPt d₀ d₁ m) = 0 :=
  Prod.ext rfl (Prod.ext rfl (funext fun _ => EVL.ext rfl rfl))

theorem inLin_gmul (g h : LPt d₀ d₁ m) :
    inLin Ls (StrongSix.M2.gmul g h) = inLin Ls g + inLin Ls h := by
  refine Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))
  show (⟨0, (g.1 + h.1) (Fin.natAdd d₀ k)⟩ : EVL (Ls k)) = ⟨0, _⟩ + ⟨0, _⟩
  rw [evl_fib_add]; rfl

theorem inLin_ginv (g : LPt d₀ d₁ m) : inLin Ls (StrongSix.M2.ginv g) = -inLin Ls g := by
  refine Prod.ext rfl (Prod.ext rfl (funext fun k => EVL.ext ?_ rfl))
  show (0 : (curve (Ls k).g₂ (Ls k).g₃).toAffine.Point) = -0
  rw [neg_zero]

variable (Ls) in
/-- `HL H = inLin⁻¹(H)`. -/
def HL (H : Set (GPtV d₀ d₁ Ls)) : Set (LPt d₀ d₁ m) := {g | inLin Ls g ∈ H}

theorem HL_isSubgroup (hH : IsSubgroupG H) : StrongSix.M2.IsSubgroupG (HL Ls H) where
  one_mem := by show inLin Ls _ ∈ H; rw [inLin_zero]; exact hH.zero_mem
  mul_mem g hg h hh := by
    show inLin Ls _ ∈ H; rw [inLin_gmul]; exact hH.add_mem _ hg _ hh
  inv_mem g hg := by show inLin Ls _ ∈ H; rw [inLin_ginv]; exact hH.neg_mem _ hg

/-- Substituting the (rescaled) `O`-fibre chart `(0 : 1 : 0 : 0 : w)` into the `E^♮` blocks. -/
noncomputable def substV (lam : Fin m → ℂˣ) :
    Var d₀ d₁ m → MvPolynomial (StrongSix.M2.V3 (d₀ + m) d₁) ℂ
  | .x i => X (.inl (Fin.castAdd m i))
  | .y j => X (.inr (.inl j))
  | .z j => X (.inr (.inr j))
  | .e k c => C ((lam k : ℂ)) * ptO (X (.inl (Fin.natAdd d₀ k))) c

theorem eval_substV (lam : Fin m → ℂˣ) (g : LPt d₀ d₁ m) (P : MvPolynomial (Var d₀ d₁ m) ℂ) :
    eval (StrongSix.M2.pt g) (aeval (substV lam) P) = eval (coords (inLin Ls g) lam) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, aeval_X, eval_X]
    congr 1
    cases v with
    | x i => simp [substV, StrongSix.M2.pt, coords, inLin]
    | y j => simp [substV, StrongSix.M2.pt, coords, inLin, GPtV.ym]
    | z j => simp [substV, StrongSix.M2.pt, coords, inLin, GPtV.ym]
    | e k c =>
      simp only [substV, coords, coordsZ_e, inLin, repV, repB_zero, map_mul, eval_C]
      congr 1
      fin_cases c <;> simp [ptO, StrongSix.M2.pt]

theorem HL_eq_zeros (hc : IsZClosed H) :
    HL Ls H = StrongSix.M2.zeros
      {Q | ∃ P ∈ vanish H, ∃ lam : Fin m → ℂˣ, Q = aeval (substV lam) P} := by
  have hz := zeros_vanish hc
  ext g
  constructor
  · rintro hg _ ⟨P, hP, lam, rfl⟩
    rw [eval_substV]
    exact mem_vanish.mp hP _ hg lam
  · intro h
    change inLin Ls g ∈ H
    rw [← hz]
    intro P hP lam
    rw [← eval_substV]
    exact h _ ⟨P, hP, lam, rfl⟩

/-- **`HL H = V × T_Λ`** (Roy's classification of algebraic subgroups of linear groups). -/
theorem HL_eq_prodSet (hH : IsSubgroupG H) (hc : IsZClosed H) :
    HL Ls H = StrongSix.M2.prodSet (StrongSix.M2.linV (HL Ls H)) (StrongSix.M2.latt (HL Ls H)) :=
  StrongSix.M2.classify (HL_isSubgroup hH) (HL_eq_zeros hc)

/-! ### `exp` at lattice points -/

/-- The linear point `((a, w), e^b)`. -/
noncomputable def linPtV (a : Fin d₀ → ℂ) (w : Fin m → ℂ) (b : Fin d₁ → ℂ) : LPt d₀ d₁ m :=
  (Fin.append a w, fun j => LSG.ME.expU (b j))

theorem chr_linPtV (a : Fin d₀ → ℂ) (w : Fin m → ℂ) (b : Fin d₁ → ℂ) (φ : Fin d₁ → ℤ) :
    StrongSix.M2.chr (linPtV a w b).2 φ = Complex.exp (∑ j, (φ j : ℂ) * b j) := by
  simp only [StrongSix.M2.chr, linPtV, LSG.ME.expU, Units.val_mk0, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => (Complex.exp_int_mul _ _).symm

/-- **`exp` at a lattice point of the base**: `expGV (a, b, z, w) = inLin ((a, w − η(z)), e^b)`. -/
theorem expGV_of_lattice {p : TanG d₀ d₁ m} (hz : ∀ k, p.2.2.1 k ∈ (Ls k).lattice) :
    expGV Ls p = inLin Ls (linPtV p.1 (p.2.2.2 - etaV Ls p.2.2.1) p.2.1) := by
  refine Prod.ext (funext fun i => ?_) (Prod.ext rfl (funext fun k => ?_))
  · simp [inLin, linPtV, expGV]
  · show expV (Ls k) (p.2.2.1 k, p.2.2.2 k) = ⟨0, Fin.append p.1 _ (Fin.natAdd d₀ k)⟩
    rw [expV_of_mem _ (hz k), Fin.append_right]; rfl

theorem expGV_lin (a : Fin d₀ → ℂ) (b : Fin d₁ → ℂ) (w : Fin m → ℂ) :
    expGV Ls ((a, b, 0, w) : TanG d₀ d₁ m) = inLin Ls (linPtV a w b) := by
  rw [expGV_of_lattice (fun k => (Ls k).lattice.zero_mem)]
  congr 2
  funext k
  simp [etaV, LSG.Weierstrass.eta_zero]

end

end LSG.MEV
