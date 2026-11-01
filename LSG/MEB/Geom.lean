/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEB.Block
import StrongSix.M2.SeparateGen

/-!
# The multi-cone model of `G = G_a^{d₀} × G_m^{d₁} × B₁ × ⋯ × B_m` (STAGE_A4 §1.2; frozen in A4.0)

The analogue of `LSG.ME.Geom` for a family `B : Fin m → AbBlock` of abelian blocks.

* `AbBlock.Pt b = ℂ^g ⧸ per`: the points of a block. This is an additive group for free; no group law on the model is
  needed. `AbBlock.rep b p = θ (out p)` is a cone representative (any lift; the cone scalings absorb the choice).
  `AbBlock.mk_out_sub`, `AbBlock.rep_mk`: `rep (mk u) = c • θ u` with `c ≠ 0`.
* `Var d₀ d₁ B`: the variables `x i` (`G_a`), `y j`, `z j` (`G_m`, `y z = 1`), `e k c` (`c : Fin (B k).N`).
  `Blk m`, `blk`: the blocks `x`, `yz`, `e k`.
* `GPt d₀ d₁ B`: the points; `Tan d₀ d₁ B = ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k}`; `expG : Tan →+ GPt`, which is onto
  (`expG_surjective`).
* `liftB u : Var → ℂ`: the entire lift `(u₀, e^{u₁}, e^{−u₁}, θ_k(u_{2,k}))`.
* `coords g λ`, `vanish E`, `zeros`, `IsZClosed`, `zcl`, `IsSubgroupG`, `gtransl`; `IGsem = vanish univ`.
* `coords_expG`: `liftB u = coords (expG u) λ` for some `λ`. Hence **`notMem_IGsem_of_eval_ne`**: if `P ∘ liftB ≢ 0`
  then `P ∉ IGsem`, which is the form in which the auxiliary function of W88 §6 enters.
-/

open MvPolynomial

namespace LSG.MEB

/-! ### Points of a block -/

namespace AbBlock

variable (b : AbBlock)

/-- The points `ℂ^g ⧸ per` of a block. -/
abbrev Pt : Type := (Fin b.g → ℂ) ⧸ b.per

/-- A cone representative of a point: `θ` at a lift. -/
noncomputable def rep (p : b.Pt) : Fin b.N → ℂ := b.θ (Quotient.out p)

theorem mk_out_sub (u : Fin b.g → ℂ) :
    Quotient.out (QuotientAddGroup.mk u : b.Pt) - u ∈ b.per := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk u : b.Pt)) : b.Pt) =
      QuotientAddGroup.mk u := Quotient.out_eq _
  have h' := QuotientAddGroup.eq.mp h
  have : Quotient.out (QuotientAddGroup.mk u : b.Pt) - u =
      -(-Quotient.out (QuotientAddGroup.mk u : b.Pt) + u) := by abel
  rw [this]
  exact b.per.neg_mem h'

/-- `rep (mk u) = c • θ u` with `c ≠ 0`. -/
theorem rep_mk (u : Fin b.g → ℂ) : ∃ c : ℂ, c ≠ 0 ∧ b.rep (QuotientAddGroup.mk u) = c • b.θ u := by
  obtain ⟨c, hc, h⟩ := b.θ_per _ (b.mk_out_sub u) u
  refine ⟨c, hc, ?_⟩
  rw [rep, ← h]
  congr 1
  abel

theorem rep_ne_zero (p : b.Pt) : b.rep p ≠ 0 := b.θ_ne _

end AbBlock

variable {m : ℕ}

/-! ### Variables, blocks, points -/

/-- The variables: `x i` (`G_a`), `y j`, `z j` (`G_m`), and the cone coordinates `e k c` of the
blocks. -/
inductive Var (d₀ d₁ : ℕ) (B : Fin m → AbBlock)
  | x (i : Fin d₀)
  | y (j : Fin d₁)
  | z (j : Fin d₁)
  | e (k : Fin m) (c : Fin (B k).N)
  deriving DecidableEq

/-- The blocks: `x`, `(y, z)`, and one block per abelian factor. -/
inductive Blk (m : ℕ)
  | x
  | yz
  | e (k : Fin m)
  deriving DecidableEq, Fintype

variable {d₀ d₁ : ℕ} {B : Fin m → AbBlock}

/-- `Var` as a sum type (for the `Fintype` instance). -/
def Var.equivSum : Var d₀ d₁ B ≃ Fin d₀ ⊕ Fin d₁ ⊕ Fin d₁ ⊕ (Σ k, Fin (B k).N) where
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

/-- The block of a variable. -/
def blk : Var d₀ d₁ B → Blk m
  | .x _ => .x
  | .y _ => .yz
  | .z _ => .yz
  | .e k _ => .e k

variable (d₀ d₁ B) in
/-- The points of `G = G_a^{d₀} × G_m^{d₁} × ∏_k B_k` (the `G_m` part written additively). -/
abbrev GPt : Type := (Fin d₀ → ℂ) × Additive (Fin d₁ → ℂˣ) × (∀ k, (B k).Pt)

variable (d₀ d₁ B) in
/-- The Lie algebra `ℂ^{d₀} × ℂ^{d₁} × ∏_k ℂ^{g_k}`. -/
abbrev Tan : Type := (Fin d₀ → ℂ) × (Fin d₁ → ℂ) × (∀ k, Fin (B k).g → ℂ)

/-- The `G_m` coordinates of a point. -/
def GPt.ym (g : GPt d₀ d₁ B) (j : Fin d₁) : ℂˣ := Additive.toMul g.2.1 j

/-- `e^b` as a unit. -/
noncomputable def expU (b : ℂ) : ℂˣ := Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b)

/-- The exponential map `Tan → GPt`, `(a, b, z) ↦ (a, e^b, z mod per)`. -/
noncomputable def expGf (u : Tan d₀ d₁ B) : GPt d₀ d₁ B :=
  (u.1, Additive.ofMul fun j => expU (u.2.1 j), fun k => QuotientAddGroup.mk (u.2.2 k))

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
  refine ⟨(a, fun j => Complex.log ((Additive.toMul b j : ℂˣ) : ℂ), fun k => Quotient.out (p k)),
    ?_⟩
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change Additive.ofMul _ = b
    apply Additive.toMul.injective
    funext j
    exact Units.ext (by simp [expU, Complex.exp_log (Units.ne_zero _)])
  · funext k
    exact Quotient.out_eq _

/-- **The entire lift** `(u₀, e^{u₁}, e^{−u₁}, θ_k(u_{2,k}))` of `expG` to the multi-cone. -/
noncomputable def liftB (u : Tan d₀ d₁ B) : Var d₀ d₁ B → ℂ
  | .x i => u.1 i
  | .y j => Complex.exp (u.2.1 j)
  | .z j => Complex.exp (-u.2.1 j)
  | .e k c => (B k).θ (u.2.2 k) c

/-! ### Cone representatives and vanishing ideals -/

/-- The cone coordinates of `g` with scalings `λ : Fin m → ℂˣ`. -/
noncomputable def coords (g : GPt d₀ d₁ B) (lam : Fin m → ℂˣ) : Var d₀ d₁ B → ℂ
  | .x i => g.1 i
  | .y j => (g.ym j : ℂ)
  | .z j => ((g.ym j)⁻¹ : ℂˣ)
  | .e k c => (lam k : ℂ) * (B k).rep (g.2.2 k) c

/-- **The lift is a cone representative**: `liftB u = coords (expG u) λ` for some scalings. -/
theorem coords_expG (u : Tan d₀ d₁ B) :
    ∃ lam : Fin m → ℂˣ, coords (expG d₀ d₁ B u) lam = liftB u := by
  choose c hc h using fun k => (B k).rep_mk (u.2.2 k)
  refine ⟨fun k => (Units.mk0 (c k) (hc k))⁻¹, ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => simp [coords, liftB, GPt.ym, expG_apply, expGf, expU]
  | z j => simp [coords, liftB, GPt.ym, expG_apply, expGf, expU, Complex.exp_neg]
  | e k c' =>
    simp only [coords, liftB, expG_apply, expGf]
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
/-- **The semantic ideal of `G`**: polynomials vanishing on every cone representative of every
point. -/
noncomputable def IGsem : Ideal (MvPolynomial (Var d₀ d₁ B) ℂ) := vanish Set.univ

/-- **The auxiliary function is not in `IGsem`**: if `P ∘ liftB ≢ 0` then `P ∉ IGsem`. -/
theorem notMem_IGsem_of_eval_ne {P : MvPolynomial (Var d₀ d₁ B) ℂ} {u : Tan d₀ d₁ B}
    (hu : eval (liftB u) P ≠ 0) : P ∉ IGsem d₀ d₁ B := by
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

/-- A subgroup of `G`. -/
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

end LSG.MEB
