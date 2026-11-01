/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.Block
import LSG.MEB.Geom

/-!
# The multi-cone model of `G̃ = G_a^{d₀} × G_m^{d₁} × B₁^♮ × ⋯ × B_m^♮` (M2.md §M2.4a; frozen)

The analogue of `LSG.MEB.Geom` for a family `B : Fin m → VBlock` of vector-extension blocks. The blocks `Blk m`
(`x`, `yz`, `e k`) are MEB's (`LSG.MEB.Blk`): each `B_k^♮` is one block, its `X`- and `T`-coordinates together.

* `VBlock.Pt b = (ℂ^g × ℂ) ⧸ perV`: the points of `B^♮` (an additive group for free). `VBlock.rep b p = lift (out p)`;
  `VBlock.rep_mk`: `rep (mk u) = c • lift u` with `c ≠ 0`.
* `Var d₀ d₁ B`: the variables `x i` (`G_a`), `y j`, `z j` (`G_m`, `y z = 1`), `e k c` (`c : (B k).Idx`, i.e. `X_c`
  for `c = inl _` and `T_t` for `c = inr _`). `blk : Var d₀ d₁ B → LSG.MEB.Blk m`.
* `GPt d₀ d₁ B`: the points; **`Tan d₀ d₁ B = ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k} × ℂ^m`** (additive, toric, base and fibre
  coordinates; the fibre coordinate of block `k` is `u.2.2.2 k`); `expG : Tan →+ GPt`, onto (`expG_surjective`).
* `liftV u : Var → ℂ`: the entire lift `(u₀, e^{u₁}, e^{−u₁}, lift_k(z_k, w_k))`.
* `coords g λ`, `vanish E`, `zeros`, `IsZClosed`, `zcl`, `IsSubgroupG`, `gtransl`; `IGsem = vanish univ`.
* `coords_expG`: `liftV u = coords (expG u) λ` for some `λ`; **`notMem_IGsem_of_eval_ne`**.
* `dimG d₀ d₁ B = d₀ + d₁ + Σ_k (g_k + 1) = dim G̃`.
-/

open MvPolynomial

namespace LSG.MEBV

open LSG.MEB (Blk)

/-! ### Points of a block -/

namespace VBlock

variable (b : VBlock)

/-- The points `(ℂ^g × ℂ) ⧸ perV` of `B^♮`. -/
abbrev Pt : Type := ((Fin b.g → ℂ) × ℂ) ⧸ b.perV

/-- A cone representative of a point: the lift at a representative. -/
noncomputable def rep (p : b.Pt) : b.Idx → ℂ := b.lift (Quotient.out p)

theorem mk_out_sub (u : (Fin b.g → ℂ) × ℂ) :
    Quotient.out (QuotientAddGroup.mk u : b.Pt) - u ∈ b.perV := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk u : b.Pt)) : b.Pt) =
      QuotientAddGroup.mk u := Quotient.out_eq _
  have h' := QuotientAddGroup.eq.mp h
  have : Quotient.out (QuotientAddGroup.mk u : b.Pt) - u =
      -(-Quotient.out (QuotientAddGroup.mk u : b.Pt) + u) := by abel
  rw [this]
  exact b.perV.neg_mem h'

/-- `rep (mk u) = c • lift u` with `c ≠ 0`. -/
theorem rep_mk (u : (Fin b.g → ℂ) × ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ b.rep (QuotientAddGroup.mk u) = c • b.lift u := by
  obtain ⟨c, hc, h⟩ := b.lift_add_perV (b.mk_out_sub u) u
  refine ⟨c, hc, ?_⟩
  rw [rep, ← h]
  congr 1
  abel

theorem rep_ne_zero (p : b.Pt) : b.rep p ≠ 0 := b.lift_ne_zero _

end VBlock

variable {m : ℕ}

/-! ### Variables and points -/

/-- The variables: `x i` (`G_a`), `y j`, `z j` (`G_m`), and the cone coordinates `e k c` of the blocks
(`c = inl c'`: `X_{c'}`; `c = inr t`: `T_t`). -/
inductive Var (d₀ d₁ : ℕ) (B : Fin m → VBlock)
  | x (i : Fin d₀)
  | y (j : Fin d₁)
  | z (j : Fin d₁)
  | e (k : Fin m) (c : Fin (B k).base.N ⊕ Fin (B k).nT)
  deriving DecidableEq

variable {d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- `Var` as a sum type (for the `Fintype` instance). -/
def Var.equivSum : Var d₀ d₁ B ≃ Fin d₀ ⊕ Fin d₁ ⊕ Fin d₁ ⊕ (Σ k, (B k).Idx) where
  toFun
    | .x i => .inl i
    | .y j => .inr (.inl j)
    | .z j => .inr (.inr (.inl j))
    | .e k c => .inr (.inr (.inr ⟨k, c⟩))
  invFun
    | .inl i => .x i
    | .inr (.inl j) => .y j
    | .inr (.inr (.inl j)) => .z j
    | .inr (.inr (.inr ⟨k, c⟩)) => .e k c
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with i | j | j | ⟨k, c⟩ <;> rfl

instance : Fintype (Var d₀ d₁ B) := Fintype.ofEquiv _ Var.equivSum.symm

/-- The base coordinate `X_c` of block `k`. -/
abbrev Var.eX (k : Fin m) (c : Fin (B k).base.N) : Var d₀ d₁ B := .e k (Sum.inl c)

/-- The fibre coordinate `T_t` of block `k`. -/
abbrev Var.eT (k : Fin m) (t : Fin (B k).nT) : Var d₀ d₁ B := .e k (Sum.inr t)

/-- The block of a variable. -/
def blk : Var d₀ d₁ B → Blk m
  | .x _ => .x
  | .y _ => .yz
  | .z _ => .yz
  | .e k _ => .e k

variable (d₀ d₁ B) in
/-- The points of `G̃ = G_a^{d₀} × G_m^{d₁} × ∏_k B_k^♮` (the `G_m` part written additively). -/
abbrev GPt : Type := (Fin d₀ → ℂ) × Additive (Fin d₁ → ℂˣ) × (∀ k, (B k).Pt)

variable (d₀ d₁ B) in
/-- The Lie algebra `ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k} × ℂ^m` (additive, toric, base, fibre). -/
abbrev Tan : Type := (Fin d₀ → ℂ) × (Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ) × (Fin m → ℂ)

variable (d₀ d₁ B) in
/-- `dim G̃ = d₀ + d₁ + Σ_k (g_k + 1)`. -/
def dimG : ℕ := d₀ + d₁ + ∑ k, ((B k).g + 1)

/-- The block-`k` component `(z_k, w_k)` of a tangent vector. -/
def Tan.blkV (u : Tan d₀ d₁ B) (k : Fin m) : (Fin (B k).g → ℂ) × ℂ := (u.2.2.1 k, u.2.2.2 k)

@[simp] theorem Tan.blkV_add (u v : Tan d₀ d₁ B) (k : Fin m) : (u + v).blkV k = u.blkV k + v.blkV k := rfl

/-- The `G_m` coordinates of a point. -/
def GPt.ym (g : GPt d₀ d₁ B) (j : Fin d₁) : ℂˣ := Additive.toMul g.2.1 j

/-- `e^b` as a unit. -/
noncomputable def expU (b : ℂ) : ℂˣ := Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)

/-- The exponential map `Tan → GPt`, `(a, b, z, w) ↦ (a, e^b, (z_k, w_k) mod perV_k)`. -/
noncomputable def expGf (u : Tan d₀ d₁ B) : GPt d₀ d₁ B :=
  (u.1, Additive.ofMul fun j => expU (u.2.1 j), fun k => QuotientAddGroup.mk (u.blkV k))

theorem expGf_add (u v : Tan d₀ d₁ B) : expGf (u + v) = expGf u + expGf v := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change Additive.ofMul _ = Additive.ofMul ((fun j => expU (u.2.1 j)) * fun j => expU (v.2.1 j))
    congr 1
    funext j
    exact Units.ext (by simp [expU, Complex.exp_add])
  · funext k
    rfl

variable (d₀ d₁ B) in
/-- **The exponential map** as an additive homomorphism. -/
noncomputable def expG : Tan d₀ d₁ B →+ GPt d₀ d₁ B := AddMonoidHom.mk' expGf expGf_add

theorem expG_apply (u : Tan d₀ d₁ B) : expG d₀ d₁ B u = expGf u := rfl

/-- `expG` is onto. -/
theorem expG_surjective : Function.Surjective (expG d₀ d₁ B) := by
  rintro ⟨a, b, p⟩
  refine ⟨(a, fun j => Complex.log ((Additive.toMul b j : ℂˣ) : ℂ), fun k => (Quotient.out (p k)).1,
    fun k => (Quotient.out (p k)).2), ?_⟩
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change Additive.ofMul _ = b
    apply Additive.toMul.injective
    funext j
    exact Units.ext (by simp [expU, Complex.exp_log (Units.ne_zero _)])
  · funext k
    exact Quotient.out_eq _

/-- **The entire lift** `(u₀, e^{u₁}, e^{−u₁}, lift_k(z_k, w_k))` of `expG` to the multi-cone. -/
noncomputable def liftV (u : Tan d₀ d₁ B) : Var d₀ d₁ B → ℂ
  | .x i => u.1 i
  | .y j => Complex.exp (u.2.1 j)
  | .z j => Complex.exp (-u.2.1 j)
  | .e k c => (B k).lift (u.blkV k) c

/-! ### Cone representatives and vanishing ideals -/

/-- The cone coordinates of `g` with scalings `λ : Fin m → ℂˣ`. -/
noncomputable def coords (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) : Var d₀ d₁ B → ℂ
  | .x i => g.1 i
  | .y j => (g.ym j : ℂ)
  | .z j => ((g.ym j)⁻¹ : ℂˣ)
  | .e k c => (lam k : ℂ) * (B k).rep (g.2.2 k) c

/-- **The lift is a cone representative**: `liftV u = coords (expG u) λ` for some scalings. -/
theorem coords_expG (u : Tan d₀ d₁ B) :
    ∃ lam : Fin m → ℂˣ, coords (expG d₀ d₁ B u) lam = liftV u := by
  choose c hc h using fun k => (B k).rep_mk (u.blkV k)
  refine ⟨fun k => (Units.mk0 (c k) (hc k))⁻¹, ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => simp [coords, liftV, GPt.ym, expG_apply, expGf, expU]
  | z j => simp [coords, liftV, GPt.ym, expG_apply, expGf, expU, Complex.exp_neg]
  | e k c' =>
    simp only [coords, liftV, expG_apply, expGf]
    rw [h k]
    simp [hc k]

/-- The ideal of polynomials vanishing at every cone representative of every point of `E`. -/
noncomputable def vanish (E : Set (GPt d₀ d₁ B)) : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) :=
  StrongSix.M2.vanish' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2) (E ×ˢ Set.univ)

theorem mem_vanish {E : Set (GPt d₀ d₁ B)} {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanish E ↔ ∀ g ∈ E, ∀ lam, eval (coords g lam) P = 0 := by
  rw [vanish, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg lam; exact h (g, lam) ⟨hg, Set.mem_univ _⟩
  · rintro h ⟨g, lam⟩ ⟨hg, -⟩; exact h g hg lam

theorem vanish_antitone {E E' : Set (GPt d₀ d₁ B)} (h : E ⊆ E') : vanish E' ≤ vanish E :=
  fun _ hP => mem_vanish.mpr fun g hg lam => mem_vanish.mp hP g (h hg) lam

variable (d₀ d₁ B) in
/-- **The semantic ideal of `G̃`**: polynomials vanishing on every cone representative of every point. -/
noncomputable def IGsem : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) := vanish Set.univ

/-- **The auxiliary function is not in `IGsem`**: if `P ∘ liftV ≢ 0` then `P ∉ IGsem`. -/
theorem notMem_IGsem_of_eval_ne {P : MvPolynomial (Var d₀ d₁ B) ℂ} {u : Tan d₀ d₁ B}
    (hu : eval (liftV u) P ≠ 0) : P ∉ IGsem d₀ d₁ B := by
  intro hP
  obtain ⟨lam, hlam⟩ := coords_expG u
  exact hu (hlam ▸ mem_vanish.mp hP _ (Set.mem_univ _) lam)

/-- The points at all of whose cone representatives every polynomial of `Ps` vanishes. -/
def zeros (Ps : Set (MvPolynomial (Var d₀ d₁ B) ℂ)) : Set (GPt d₀ d₁ B) :=
  {g | ∀ P ∈ Ps, ∀ lam, eval (coords g lam) P = 0}

/-- `V` is **Zariski closed**: the (cone) zero set of a set of polynomials. -/
def IsZClosed (V : Set (GPt d₀ d₁ B)) : Prop :=
  ∃ S : Set (MvPolynomial (Var d₀ d₁ B) ℂ), V = zeros S

/-- The Zariski closure. -/
def zcl (S : Set (GPt d₀ d₁ B)) : Set (GPt d₀ d₁ B) :=
  zeros (vanish S : Set (MvPolynomial (Var d₀ d₁ B) ℂ))

theorem subset_zcl (S : Set (GPt d₀ d₁ B)) : S ⊆ zcl S :=
  fun _ hg _ hP lam => mem_vanish.mp hP _ hg lam

theorem isZClosed_zcl (S : Set (GPt d₀ d₁ B)) : IsZClosed (zcl S) := ⟨_, rfl⟩

/-- A subgroup of `G̃`. -/
structure IsSubgroupG (E : Set (GPt d₀ d₁ B)) : Prop where
  zero_mem : 0 ∈ E
  add_mem : ∀ g ∈ E, ∀ h ∈ E, g + h ∈ E
  neg_mem : ∀ g ∈ E, -g ∈ E

/-- The translate `E + g`. -/
def gtransl (g : GPt d₀ d₁ B) (E : Set (GPt d₀ d₁ B)) : Set (GPt d₀ d₁ B) := (· + g) '' E

theorem mem_gtransl {g h : GPt d₀ d₁ B} {E : Set (GPt d₀ d₁ B)} : h ∈ gtransl g E ↔ h - g ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩; simpa using he
  · intro h'; exact ⟨h - g, h', by simp⟩

end LSG.MEBV
