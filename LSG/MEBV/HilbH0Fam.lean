/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.SubgroupHtil
import LSG.MEB.HilbH0Fam

/-!
# The independent family for `H(I(H⁰); t)` (M2.5 β′; template `LSG.MEB.HilbH0Fam`)

Pure algebra: the family, its block degrees, its evaluation, and its count. Compared with MEB, every block `k = ιF l`
in the image of a **fibre coordinate pivot** `ιF : Fin r → Fin m` gets one more factor `T_{k,t₀}^{e_l}` (the fibre
ratio `T_{t₀}/X_{i₀}` is affine in `w`).

On block `k`: `pivG = g_k` on the base pivot set `J` (else `0`), `fibG k = #{l | ιF l = k}`, `pvV = pivG + fibG`,
`pivMV T k = T/(pvV+1) + 1`.
* `HIdxV`: exponents `(a, b, c, d, e)`; **`hPolyV`** `= ∏ lp_l^{a_l} ∏ Y_{jj k}^{b_k} ∏_k (X_{k,i₀}^{c_k}
  ∏_j X_{k,is j}^{d_kj} ∏_{ιF l = k} T_{k,t₀}^{e_l})`;
* `HCrdV`, `hExpV`; **`eval_hPolyV`** (at any point whose coordinates are the target monomials),
  **`hExpV_injective`**, **`hPolyV_mem_FLE`**, **`card_HIdxV`**, **`count_leV`**;
* `linPolyV`, `eval_linPolyV`; **`card_le_hfun_vanishV`**.
-/

open MvPolynomial Module
open StrongSix.M2 (FLE hfun)

namespace LSG.MEBV

open LSG.MEB (Blk DfunB pivG pivG_le C_mem_FLE0 X_mem_FLE pow_mem_FLE prod_mem_FLE)

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-! ### Counting independent elements -/

/-- **A family of `FLE(tD)` independent modulo `I(E)` has at most `H(I(E); t)` members.** -/
theorem card_le_hfun_vanishV {ι : Type*} [Fintype ι] (D : Blk m → ℕ) (t : ℕ) (E : Set (GPt d₀ d₁ B))
    (P : ι → MvPolynomial (Var d₀ d₁ B) ℂ) (hP : ∀ i, P i ∈ FLE ℂ blk (t • D))
    (hind : ∀ c : ι → ℂ, ∑ i, c i • P i ∈ vanish E → ∀ i, c i = 0) :
    Fintype.card ι ≤ hfun blk D ℂ (vanish E) t := by
  classical
  have e : vanish E = StrongSix.M2.vanish' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2)
      (E ×ˢ Set.univ) := rfl
  rw [e, StrongSix.M2.hfun_vanish_eq' blk D (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2)
    (E ×ˢ Set.univ) t]
  set R := (FLE ℂ blk (t • D)).map
    (StrongSix.M2.restrE' (fun p : GPt d₀ d₁ B × (Fin m → ℂˣ) => coords p.1 p.2) (E ×ˢ Set.univ))
  let f : ι → R := fun i => ⟨_, ⟨P i, hP i, rfl⟩⟩
  have hf : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply hind c
    rw [e, StrongSix.M2.mem_vanish']
    rintro ⟨g, lam⟩ ⟨hg, -⟩
    have := congrArg (fun x : R => (x : GPt d₀ d₁ B × (Fin m → ℂˣ) → ℂ) (g, lam)) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply, f, StrongSix.M2.restrE'_apply] at this
    rw [map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (Set.mk_mem_prod hg (Set.mem_univ _)), smul_eval, smul_eq_mul, mul_comm]
  exact hf.fintype_card_le_finrank

/-! ### Linear forms on the additive part -/

/-- The polynomial `Σ_j L(e_j) x_j` of a linear form `L`. -/
noncomputable def linPolyV (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  ∑ j, C (L (Pi.single j 1)) * X (Var.x j)

theorem linPolyV_mem_FLE (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) :
    linPolyV (d₁ := d₁) (B := B) L ∈ FLE ℂ blk (Pi.single Blk.x 1) := by
  refine Submodule.sum_mem _ fun j _ => ?_
  have := StrongSix.M2.mul_mem_FLE ℂ (C_mem_FLE0 blk (L (Pi.single j 1)))
    (X_mem_FLE (blk (m := m)) (Var.x j : Var d₀ d₁ B))
  rwa [zero_add] at this

theorem eval_linPolyV (L : (Fin d₀ → ℂ) →ₗ[ℂ] ℂ) (u : Tan d₀ d₁ B) (μ : Fin m → ℂ) :
    eval (liftZ u μ) (linPolyV L) = L u.1 := by
  simp only [linPolyV, map_sum, map_mul, eval_C, eval_X, liftZ]
  rw [LinearMap.pi_apply_eq_sum_univ L u.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  funext i'
  simp [Pi.single_apply, eq_comm]

/-! ### The pivot sizes -/

/-- The number of fibre coordinates on block `k`. -/
def fibG {r : ℕ} (ιF : Fin r → Fin m) (k : Fin m) : ℕ := (Finset.univ.filter fun l => ιF l = k).card

theorem fibG_le_one {r : ℕ} {ιF : Fin r → Fin m} (hι : Function.Injective ιF) (k : Fin m) :
    fibG ιF k ≤ 1 :=
  Finset.card_le_one.mpr fun a ha b hb => hι ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

theorem sum_fibG {r : ℕ} (ιF : Fin r → Fin m) : ∑ k, fibG ιF k = r := by
  unfold fibG
  rw [← Finset.card_eq_sum_card_fiberwise (fun l _ => Finset.mem_univ (ιF l))]
  simp

variable (B) in
/-- `pivG + fibG`. -/
def pvV (J : Finset (Fin m)) {r : ℕ} (ιF : Fin r → Fin m) (k : Fin m) : ℕ :=
  pivG (fun k => (B k).base) J k + fibG ιF k

variable (B) in
/-- The exponent range `T/(pvV+1) + 1` on block `k`. -/
def pivMV (J : Finset (Fin m)) {r : ℕ} (ιF : Fin r → Fin m) (T : ℕ) (k : Fin m) : ℕ :=
  T / (pvV B J ιF k + 1) + 1

variable (B) in
/-- The exponents of the family. -/
abbrev HIdxV (t₀ M0 : ℕ) (κ : Type) (M1 : ℕ) (J : Finset (Fin m)) {r : ℕ} (ιF : Fin r → Fin m) (T : ℕ) :
    Type :=
  (Fin t₀ → Fin M0) × (κ → Fin M1) × (∀ k, Fin (pivMV B J ιF T k)) ×
    (∀ k, Fin (pivG (fun k => (B k).base) J k) → Fin (pivMV B J ιF T k)) × (∀ l, Fin (pivMV B J ιF T (ιF l)))

variable (B) in
/-- The target coordinates: `h₀`-coordinates, torus coordinates, per block `ν_k` and the ratios, fibre ratios. -/
abbrev HCrdV (t₀ : ℕ) (κ : Type) (J : Finset (Fin m)) (r : ℕ) : Type :=
  Fin t₀ ⊕ κ ⊕ (Σ k : Fin m, Option (Fin (pivG (fun k => (B k).base) J k))) ⊕ Fin r

variable {t₀ M0 M1 T r : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {J : Finset (Fin m)} {ιF : Fin r → Fin m}

/-- The block-`k` factor. -/
noncomputable def blkPoly (i : HIdxV B t₀ M0 κ M1 J ιF T) (k : Fin m) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  X (Var.eX k (B k).base.i₀) ^ (i.2.2.1 k : ℕ) *
    (∏ j, X (Var.eX k ((B k).base.is (Fin.castLE (pivG_le J k) j))) ^ (i.2.2.2.1 k j : ℕ)) *
    ∏ l ∈ Finset.univ.filter (fun l => ιF l = k), X (Var.eT (ιF l) (B (ιF l)).t₀) ^ (i.2.2.2.2 l : ℕ)

/-- **The family.** -/
noncomputable def hPolyV (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ) (jj : κ → Fin d₁)
    (i : HIdxV B t₀ M0 κ M1 J ιF T) : MvPolynomial (Var d₀ d₁ B) ℂ :=
  (∏ l, lp l ^ (i.1 l : ℕ)) * (∏ k, X (Var.y (jj k)) ^ (i.2.1 k : ℕ)) * ∏ k, blkPoly i k

/-- The exponent of `hPolyV i` as a monomial in the target coordinates. -/
def hExpV (i : HIdxV B t₀ M0 κ M1 J ιF T) : HCrdV B t₀ κ J r → ℕ
  | .inl l => i.1 l
  | .inr (.inl k) => i.2.1 k
  | .inr (.inr (.inl ⟨k, none⟩)) => i.2.2.1 k + ∑ j, (i.2.2.2.1 k j : ℕ) +
      ∑ l ∈ Finset.univ.filter (fun l => ιF l = k), (i.2.2.2.2 l : ℕ)
  | .inr (.inr (.inl ⟨k, some j⟩)) => i.2.2.2.1 k j
  | .inr (.inr (.inr l)) => i.2.2.2.2 l

/-- **The evaluation identity.** -/
theorem eval_hPolyV (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ) (jj : κ → Fin d₁) (x : Var d₀ d₁ B → ℂ)
    (w : HCrdV B t₀ κ J r → ℂ)
    (h1 : ∀ l, eval x (lp l) = w (.inl l))
    (h2 : ∀ k, x (Var.y (jj k)) = w (.inr (.inl k)))
    (h3 : ∀ k, x (Var.eX k (B k).base.i₀) = w (.inr (.inr (.inl ⟨k, none⟩))))
    (h4 : ∀ k j, x (Var.eX k ((B k).base.is (Fin.castLE (pivG_le J k) j))) =
      w (.inr (.inr (.inl ⟨k, none⟩))) * w (.inr (.inr (.inl ⟨k, some j⟩))))
    (h5 : ∀ l, x (Var.eT (ιF l) (B (ιF l)).t₀) = w (.inr (.inr (.inl ⟨ιF l, none⟩))) * w (.inr (.inr (.inr l))))
    (i : HIdxV B t₀ M0 κ M1 J ιF T) :
    eval x (hPolyV lp jj i) = ∏ s, w s ^ hExpV i s := by
  classical
  have hblk : ∀ k, eval x (blkPoly i k) =
      w (.inr (.inr (.inl ⟨k, none⟩))) ^ (i.2.2.1 k + ∑ j, (i.2.2.2.1 k j : ℕ) +
        ∑ l ∈ Finset.univ.filter (fun l => ιF l = k), (i.2.2.2.2 l : ℕ)) *
      (∏ j, w (.inr (.inr (.inl ⟨k, some j⟩))) ^ (i.2.2.2.1 k j : ℕ)) *
      ∏ l ∈ Finset.univ.filter (fun l => ιF l = k), w (.inr (.inr (.inr l))) ^ (i.2.2.2.2 l : ℕ) := by
    intro k
    simp only [blkPoly, map_mul, map_prod, map_pow, eval_X, h3, h4]
    have h5' : ∀ l ∈ Finset.univ.filter (fun l => ιF l = k),
        x (Var.eT (ιF l) (B (ιF l)).t₀) ^ (i.2.2.2.2 l : ℕ) =
          w (.inr (.inr (.inl ⟨k, none⟩))) ^ (i.2.2.2.2 l : ℕ) * w (.inr (.inr (.inr l))) ^ (i.2.2.2.2 l : ℕ) := by
      intro l hl
      rw [h5, ← (Finset.mem_filter.mp hl).2, mul_pow]
    rw [Finset.prod_congr rfl h5', Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
    ring
  simp only [hPolyV, map_mul, map_prod, map_pow, eval_X, h1, h2, hblk]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [Fintype.prod_option, hExpV]
  have hfib : ∏ l, w (.inr (.inr (.inr l))) ^ (i.2.2.2.2 l : ℕ) =
      ∏ k, ∏ l ∈ Finset.univ.filter (fun l => ιF l = k), w (.inr (.inr (.inr l))) ^ (i.2.2.2.2 l : ℕ) :=
    (Finset.prod_fiberwise Finset.univ ιF _).symm
  rw [hfib]
  simp only [Finset.prod_mul_distrib]
  ring

theorem hExpV_injective : Function.Injective (hExpV (B := B) (t₀ := t₀) (M0 := M0) (κ := κ) (M1 := M1)
    (J := J) (ιF := ιF) (T := T)) := by
  rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h
  have ha : a = a' := funext fun l => Fin.ext (congrFun h (.inl l))
  have hb : b = b' := funext fun k => Fin.ext (congrFun h (.inr (.inl k)))
  have hd : d = d' := funext fun k => funext fun j => Fin.ext (congrFun h (.inr (.inr (.inl ⟨k, some j⟩))))
  have he : e = e' := funext fun l => Fin.ext (congrFun h (.inr (.inr (.inr l))))
  subst ha hb hd he
  have hc : c = c' := funext fun k => Fin.ext (by
    have := congrFun h (.inr (.inr (.inl ⟨k, none⟩)))
    simp only [hExpV] at this
    omega)
  subst hc
  rfl

/-! ### Block degrees -/

theorem X_pow_mem_FLE_blk (v : Var d₀ d₁ B) {b : Blk m} (hv : blk v = b) (n : ℕ) :
    (X v : MvPolynomial (Var d₀ d₁ B) ℂ) ^ n ∈ FLE ℂ blk (n • Pi.single b 1) := by
  subst hv; exact pow_mem_FLE blk (X_mem_FLE blk v) n

theorem blkPoly_mem_FLE (i : HIdxV B t₀ M0 κ M1 J ιF T) (k : Fin m) :
    blkPoly (d₀ := d₀) (d₁ := d₁) i k ∈ FLE ℂ blk ((i.2.2.1 k + ∑ j, (i.2.2.2.1 k j : ℕ) +
      ∑ l ∈ Finset.univ.filter (fun l => ιF l = k), (i.2.2.2.2 l : ℕ)) • Pi.single (Blk.e k) 1) := by
  have h1 := X_pow_mem_FLE_blk (Var.eX k (B k).base.i₀ : Var d₀ d₁ B) (b := Blk.e k) rfl (i.2.2.1 k)
  have h2 := prod_mem_FLE blk Finset.univ
    (fun j => (X (Var.eX k ((B k).base.is (Fin.castLE (pivG_le J k) j))) : MvPolynomial (Var d₀ d₁ B) ℂ) ^
      (i.2.2.2.1 k j : ℕ)) (fun j => (i.2.2.2.1 k j : ℕ) • (Pi.single (Blk.e k) 1 : Blk m → ℕ))
    fun j _ => X_pow_mem_FLE_blk
      (Var.eX k ((B k).base.is (Fin.castLE (pivG_le J k) j)) : Var d₀ d₁ B) rfl _
  have h3 := prod_mem_FLE blk (Finset.univ.filter fun l => ιF l = k)
    (fun l => (X (Var.eT (ιF l) (B (ιF l)).t₀) : MvPolynomial (Var d₀ d₁ B) ℂ) ^ (i.2.2.2.2 l : ℕ))
    (fun l => (i.2.2.2.2 l : ℕ) • (Pi.single (Blk.e k) 1 : Blk m → ℕ))
    fun l hl => X_pow_mem_FLE_blk (Var.eT (ιF l) (B (ιF l)).t₀ : Var d₀ d₁ B)
      (by rw [← (Finset.mem_filter.mp hl).2]; rfl) _
  have h := StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ h1 h2) h3
  refine StrongSix.M2.FLE_mono ℂ blk (le_of_eq ?_) h
  simp only [← Finset.sum_smul, ← add_smul]

theorem sum_fin_le' {ι : Type*} [Fintype ι] {M : ℕ} (f : ι → Fin M) :
    ∑ i, (f i : ℕ) ≤ Fintype.card ι * (M - 1) := LSG.MEB.sum_fin_le f

/-- **Block degrees of the family.** -/
theorem hPolyV_mem_FLE (lp : Fin t₀ → MvPolynomial (Var d₀ d₁ B) ℂ)
    (hlp : ∀ l, lp l ∈ FLE ℂ blk (Pi.single Blk.x 1)) (jj : κ → Fin d₁) {D₀ D₁ D₂ t : ℕ}
    (hM0 : t₀ * (M0 - 1) ≤ t * D₀) (hM1 : Fintype.card κ * (M1 - 1) ≤ t * D₁) (hT : T = t * D₂)
    (i : HIdxV B t₀ M0 κ M1 J ιF T) :
    hPolyV lp jj i ∈ FLE ℂ blk (t • DfunB D₀ D₁ D₂) := by
  classical
  obtain ⟨a, b, c, d, e⟩ := i
  have hA := prod_mem_FLE blk Finset.univ (fun l => lp l ^ (a l : ℕ))
    (fun l => (a l : ℕ) • Pi.single Blk.x 1) fun l _ => pow_mem_FLE blk (hlp l) _
  have hB := prod_mem_FLE blk Finset.univ (fun k => (X (Var.y (jj k)) : MvPolynomial (Var d₀ d₁ B) ℂ) ^
    (b k : ℕ)) (fun k => (b k : ℕ) • Pi.single (Blk.yz : Blk m) 1)
    fun k _ => pow_mem_FLE blk (X_mem_FLE blk (Var.y (jj k) : Var d₀ d₁ B)) _
  have hC := prod_mem_FLE blk Finset.univ (fun k => blkPoly (d₀ := d₀) (d₁ := d₁) (a, b, c, d, e) k)
    _ fun k _ => blkPoly_mem_FLE (a, b, c, d, e) k
  refine StrongSix.M2.FLE_mono ℂ blk ?_ (StrongSix.M2.mul_mem_FLE ℂ (StrongSix.M2.mul_mem_FLE ℂ hA hB) hC)
  intro bl
  cases bl with
  | x =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, if_true, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero, DfunB]
    exact (sum_fin_le' a).trans (by simpa using hM0)
  | yz =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, if_true, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero, zero_add,
      DfunB]
    exact (sum_fin_le' b).trans (by simpa using hM1)
  | e k =>
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add, Blk.e.injEq,
      DfunB]
    rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true]
    set q := T / (pivG (fun k => (B k).base) J k + fibG ιF k + 1) with hq
    have hA : (c k : ℕ) ≤ q := Nat.lt_succ_iff.mp (c k).2
    have hB' : ∑ j, (d k j : ℕ) ≤ pivG (fun k => (B k).base) J k * q := by
      have := sum_fin_le' (d k)
      simp only [Fintype.card_fin] at this
      exact this.trans (le_of_eq (by simp [pivMV, pvV, hq]))
    have hC : ∑ l ∈ Finset.univ.filter (fun l => ιF l = k), (e l : ℕ) ≤ fibG ιF k * q := by
      rw [fibG, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have h1 : (e l : ℕ) < pivMV B J ιF T k :=
        calc (e l : ℕ) < pivMV B J ιF T (ιF l) := (e l).2
          _ = pivMV B J ιF T k := by rw [(Finset.mem_filter.mp hl).2]
      exact Nat.lt_succ_iff.mp h1
    have hD := LSG.MEB.div_bound T (pivG (fun k => (B k).base) J k + fibG ιF k)
    rw [← hT]
    nlinarith

theorem prod_comp_ιF (f : Fin m → ℕ) : ∏ l, f (ιF l) = ∏ k, f k ^ fibG ιF k := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ ιF (fun l => f (ιF l))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]), Finset.prod_const, fibG]

theorem card_HIdxV : Fintype.card (HIdxV B t₀ M0 κ M1 J ιF T) =
    M0 ^ t₀ * M1 ^ Fintype.card κ * ∏ k, pivMV B J ιF T k ^ (pvV B J ιF k + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_pi]
  rw [prod_comp_ιF (ιF := ιF) (fun k => pivMV B J ιF T k)]
  simp only [pvV, pow_succ, pow_add, Finset.prod_mul_distrib]
  ring

variable (B) in
/-- The constant `∏_k (g_k+2)^{g_k+2}`. -/
def cHV : ℕ := ∏ k, ((B k).base.g + 2) ^ ((B k).base.g + 2)

theorem one_le_cHV : 1 ≤ cHV B :=
  Finset.one_le_prod' fun k _ => Nat.one_le_pow _ _ (Nat.succ_pos _)

/-- **The count**: `(T+1)^{s+m} ≤ cHV B · ∏_k pivMV_k^{pvV_k+1}` for `s ≤ Σ_k pvV_k`. -/
theorem count_leV (hι : Function.Injective ιF) {s : ℕ} (hs : s ≤ ∑ k, pvV B J ιF k) :
    (T + 1) ^ (s + m) ≤ cHV B * ∏ k, pivMV B J ιF T k ^ (pvV B J ιF k + 1) := by
  calc (T + 1) ^ (s + m) ≤ (T + 1) ^ (∑ k, pvV B J ιF k + m) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    _ = ∏ k : Fin m, (T + 1) ^ (pvV B J ιF k + 1) := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
        simp
    _ ≤ ∏ k, (((B k).base.g + 2) ^ ((B k).base.g + 2) * pivMV B J ιF T k ^ (pvV B J ιF k + 1)) := by
        refine Finset.prod_le_prod' fun k _ => ?_
        have hk : pvV B J ιF k ≤ (B k).base.g + 1 := by
          have := pivG_le (B := fun k => (B k).base) J k
          have := fibG_le_one hι k
          simp only [pvV]; omega
        calc (T + 1) ^ (pvV B J ιF k + 1)
            ≤ ((pvV B J ιF k + 1) * pivMV B J ιF T k) ^ (pvV B J ιF k + 1) :=
              Nat.pow_le_pow_left (LSG.MEB.succ_le_div_bound T _) _
          _ = (pvV B J ιF k + 1) ^ (pvV B J ιF k + 1) * pivMV B J ιF T k ^ (pvV B J ιF k + 1) :=
              mul_pow _ _ _
          _ ≤ ((B k).base.g + 2) ^ ((B k).base.g + 2) * pivMV B J ιF T k ^ (pvV B J ιF k + 1) := by
              refine Nat.mul_le_mul_right _ ?_
              calc (pvV B J ιF k + 1) ^ (pvV B J ιF k + 1) ≤ ((B k).base.g + 2) ^ (pvV B J ιF k + 1) :=
                    Nat.pow_le_pow_left (by omega) _
                _ ≤ ((B k).base.g + 2) ^ ((B k).base.g + 2) :=
                    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    _ = cHV B * ∏ k, pivMV B J ιF T k ^ (pvV B J ιF k + 1) := by rw [Finset.prod_mul_distrib, cHV]

end LSG.MEBV
