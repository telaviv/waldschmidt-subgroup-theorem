import Mathlib
import LSG.ME.OrderTransl
import StrongSix.M2.BridgeLow

/-!
# Roy's chain of ideals on the multi-cone model (Roy §8.4.1, STAGE2 §6 S2.8)

Template: StrongSix `M2/Chain.lean` and the claim `hAVO` of `M2/MainB.lean`. Differences: the
derivations are the homogenized chart derivations `Dh ch w` (`LSG.ME.Order`), translations `τ σ c`
depend on a law choice `c` and double elliptic degrees, and `P` is homogeneous in each elliptic
block (`IsHomE P d`).

* `VO W n J = ⋂_ch VO1 ch W n J`: order `> n` along `W` modulo `J`, all charts; an ideal,
  `VO ≤ J`, monotone, `I_G ≤ VO W n (vanish E)`; `mem_VO_vanish`.
* `sig S r`, `gensR r = {τ σ c (D^{ch}_l P) : σ ∈ Σ[r], all c, all ch, l ⊆ W, |l| ≤ rT}`,
  `Lr r = I_G ⊔ (gensR r)`: monotone (`Lr_mono`), `Lr_le_vanish_zero`.
* Degrees: `gensR_mem_FLE`: `gensR r ⊆ FLE (dblE (D + (r T) • ellOnes))` (one translation, so one
  doubling; the translates `τ v c Q` used in `A` lie in `FLE (dblE (dblE (D + (r T) • ellOnes)))`,
  `transl_gensR_mem_FLE`). Homogeneity: `gensR_isHomE`.
* Dimensions: `hdim_IG`: `hdim I_G = d₀ + d₁ + 2m` (affine cone dimensions);
  `hdim_ge_of_le_vanish_zero`: every ideal `≤ vanish {0}` has `hdim ≥ m`;
  `hdim_L0_lt`: `hdim L₀ < d₀ + d₁ + 2m`.
* **`exists_flat`**: some `r < d₀ + d₁ + m` has `hdim L_{r+1} = hdim L_r`.
* **`hAVO`** (Roy's vanishing claim): for `p ⊇ L_{r+1}`, `V = Z(p)`, `GV` stabilizing `V`,
  `A = I_G ⊔ (τ v c Q : Q ∈ gensR r, v ∈ V, all c)` satisfies
  `A ≤ VO W T (vanish (⋃ s ∈ S, s + GV))`.
-/

universe u

open MvPolynomial LSG.Elliptic
open StrongSix.M2 (FLE DL DL_cons hdata hdata_le_of_le hdim_section_lt hdim_add_height_eq
  FLE_mono)

namespace LSG.ME

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

/-! ### Vanishing to order `> n`, all charts -/

variable (g₂ g₃) in
/-- `VO W n J`: elements whose derivatives along words of length `≤ n` in `W`, in all charts,
lie in `J`. -/
noncomputable def VO (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ)
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  ⨅ ch : Fin m → Fin 3, VO1 g₂ g₃ ch W n J

theorem mem_VO {W : Submodule K (LieE K d₀ d₁ m)} {n : ℕ}
    {J : Ideal (MvPolynomial (Var d₀ d₁ m) K)} {x : MvPolynomial (Var d₀ d₁ m) K} :
    x ∈ VO g₂ g₃ W n J ↔ ∀ ch, x ∈ VO1 g₂ g₃ ch W n J := Submodule.mem_iInf _

theorem VO_le (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ)
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : VO g₂ g₃ W n J ≤ J :=
  fun _ hx => VOg_le n (mem_VO.mp hx (fun _ => 0))

theorem VO_mono (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ)
    {J J' : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (h : J ≤ J') :
    VO g₂ g₃ W n J ≤ VO g₂ g₃ W n J' :=
  fun _ hx => mem_VO.mpr fun ch => VOg_mono h (mem_VO.mp hx ch)

theorem VO_anti (W : Submodule K (LieE K d₀ d₁ m)) {n n' : ℕ} (h : n ≤ n')
    (J : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : VO g₂ g₃ W n' J ≤ VO g₂ g₃ W n J :=
  fun _ hx => mem_VO.mpr fun ch => VOg_anti h (mem_VO.mp hx ch)

theorem IG_le_VO (h2 : (2 : K) ≠ 0) (W : Submodule K (LieE K d₀ d₁ m)) (n : ℕ)
    (E : Set (GPt K d₀ d₁ g₂ g₃)) : IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ VO g₂ g₃ W n (vanish E) :=
  fun _ hx => mem_VO.mpr fun ch => IG_le_VO1 h2 ch W n E hx

/-- Order `> n` modulo `I(E)` is order `> n` at every point of `E`. -/
theorem mem_VO_vanish {W : Submodule K (LieE K d₀ d₁ m)} {n : ℕ} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    {x : MvPolynomial (Var d₀ d₁ m) K} :
    x ∈ VO g₂ g₃ W n (vanish E) ↔ ∀ g ∈ E, VanAll g₂ g₃ W x n g := by
  constructor
  · intro h g hg ch l hlW hl
    exact mem_vanish_singleton.mpr fun lam => mem_vanish.mp (mem_VO.mp h ch l hlW hl) g hg lam
  · intro h
    exact mem_VO.mpr fun ch l hlW hl =>
      mem_vanish.mpr fun g hg lam => mem_vanish_singleton.mp (h g hg ch l hlW hl) lam

/-! ### The sets `Σ[r]` and the chain -/

section Chain

variable [DecidableEq K]

/-- `Σ[r] = {σ₁ + ⋯ + σ_r : σᵢ ∈ S}`. -/
def sig (S : Finset (GPt K d₀ d₁ g₂ g₃)) (r : ℕ) : Set (GPt K d₀ d₁ g₂ g₃) :=
  {g | ∃ σ : Fin r → GPt K d₀ d₁ g₂ g₃, (∀ i, σ i ∈ S) ∧ g = ∑ i, σ i}

theorem zero_mem_sig (S : Finset (GPt K d₀ d₁ g₂ g₃)) : (0 : GPt K d₀ d₁ g₂ g₃) ∈ sig S 0 :=
  ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_sig {S : Finset (GPt K d₀ d₁ g₂ g₃)} {r : ℕ} {g s : GPt K d₀ d₁ g₂ g₃}
    (hg : g ∈ sig S r) (hs : s ∈ S) : g + s ∈ sig S (r + 1) := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  refine ⟨Fin.snoc σ s, fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hs
    · simpa using hσ i
  · simp [Fin.sum_univ_castSucc]

theorem sig_mono {S : Finset (GPt K d₀ d₁ g₂ g₃)} (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (r : ℕ) :
    sig S r ⊆ sig S (r + 1) :=
  fun g hg => by simpa using add_mem_sig hg hS

variable (g₂ g₃) (W : Submodule K (LieE K d₀ d₁ m)) (S : Finset (GPt K d₀ d₁ g₂ g₃))
  (P : MvPolynomial (Var d₀ d₁ m) K) (T : ℕ)

/-- Generators of `L_r`: `τ σ c (D^{ch}_l P)` with `σ ∈ Σ[r]`, any law choice `c`, any charts `ch`,
`l ⊆ W`, `|l| ≤ r T`. -/
def gensR (r : ℕ) : Set (MvPolynomial (Var d₀ d₁ m) K) :=
  {Q | ∃ σ ∈ sig S r, ∃ (c : Fin m → Fin 2) (ch : Fin m → Fin 3) (l : List (LieE K d₀ d₁ m)),
    (∀ w ∈ l, w ∈ W) ∧ l.length ≤ r * T ∧ Q = τ g₂ g₃ σ c (DL (Dh g₂ g₃ ch) l P)}

/-- Roy's ideal `L_r = I_G + (gensR r)`. -/
noncomputable def Lr (r : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span (gensR g₂ g₃ W S P T r)

variable {g₂ g₃ W S P T}

theorem gensR_mono (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (r : ℕ) :
    gensR g₂ g₃ W S P T r ⊆ gensR g₂ g₃ W S P T (r + 1) := by
  rintro _ ⟨σ, hσ, c, ch, l, hlW, hl, rfl⟩
  exact ⟨σ, sig_mono hS r hσ, c, ch, l, hlW, by nlinarith, rfl⟩

theorem Lr_mono (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (r : ℕ) :
    Lr g₂ g₃ W S P T r ≤ Lr g₂ g₃ W S P T (r + 1) :=
  sup_le_sup_left (Ideal.span_mono (gensR_mono hS r)) _

theorem Lr_mono' (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) {r r' : ℕ} (h : r ≤ r') :
    Lr g₂ g₃ W S P T r ≤ Lr g₂ g₃ W S P T r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Lr_mono hS n)

theorem transl_mem_L0 (c : Fin m → Fin 2) : τ g₂ g₃ 0 c P ∈ Lr g₂ g₃ W S P T 0 :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, zero_mem_sig S, c, fun _ => 0, [], by simp, by simp,
    by simp⟩)

/-- **Block degrees of the generators**: one translation, hence one doubling. -/
theorem gensR_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE K blk D) (r : ℕ) :
    ∀ Q ∈ gensR g₂ g₃ W S P T r, Q ∈ FLE K blk (dblE (D + (r * T) • ellOnes)) := by
  rintro _ ⟨σ, _, c, ch, l, _, hl, rfl⟩
  refine fle_le (transl_mem_FLE σ c (DLh_mem_FLE ch l hPD)) fun b => ?_
  simp only [dblE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : l.length * ellOnes b ≤ r * T * ellOnes b := Nat.mul_le_mul_right _ hl
  exact Nat.mul_le_mul_left _ (by omega)

/-- Translates of generators (the generators of `A`): two doublings. -/
theorem transl_gensR_mem_FLE {D : Blk m → ℕ} (hPD : P ∈ FLE K blk D) (r : ℕ)
    {Q : MvPolynomial (Var d₀ d₁ m) K} (hQ : Q ∈ gensR g₂ g₃ W S P T r)
    (v : GPt K d₀ d₁ g₂ g₃) (c : Fin m → Fin 2) :
    τ g₂ g₃ v c Q ∈ FLE K blk (dblE (dblE (D + (r * T) • ellOnes))) :=
  transl_mem_FLE v c (gensR_mem_FLE hPD r Q hQ)

/-- Homogeneity of the generators. -/
theorem gensR_isHomE [CharZero K] {d : Fin m → ℕ} (hP : IsHomE P d) {r : ℕ}
    {Q : MvPolynomial (Var d₀ d₁ m) K} (hQ : Q ∈ gensR g₂ g₃ W S P T r) :
    ∃ d' : Fin m → ℕ, IsHomE Q d' := by
  obtain ⟨σ, _, c, ch, l, _, _, rfl⟩ := hQ
  exact ⟨_, isHomE_transl (isHomE_DL hP ch l) σ c⟩

variable (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **The last ideal vanishes at `0`** when `P` vanishes to order `> r T` along `W` on `Σ[r]`. -/
theorem Lr_le_vanish_zero [Infinite K] {r : ℕ}
    (hvan : ∀ g ∈ sig S r, P ∈ VO g₂ g₃ W (r * T) (vanish {g})) :
    Lr g₂ g₃ W S P T r ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) := by
  refine sup_le (IG_le_vanish h2 _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, c, ch, l, hlW, hl, rfl⟩
  refine mem_vanish_singleton.mpr fun lam => ?_
  obtain ⟨ν, hν⟩ := eval_transl h2 hΔ σ 0 c lam
  rw [hν, zero_add]
  refine eval_coordsZ_eq_zero (fun lam' => ?_) ν
  exact mem_vanish_singleton.mp (mem_VO.mp (hvan σ hσ) ch l hlW hl) lam'

/-- The same, from vanishing in the canonical charts (homogeneous `P`). -/
theorem Lr_le_vanish_zero_of_vanCan [Infinite K] [CharZero K] {d : Fin m → ℕ} (hP : IsHomE P d)
    {r : ℕ} (hvan : ∀ g ∈ sig S r, VanCan g₂ g₃ W P (r * T) g) :
    Lr g₂ g₃ W S P T r ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) :=
  Lr_le_vanish_zero h2 hΔ fun g hg =>
    mem_VO.mpr ((vanAll_iff_vanCan h2 W hP (r * T) g).mpr (hvan g hg))

end Chain

/-! ### Hilbert dimensions -/

section Dims

theorem card_Var : Fintype.card (Var d₀ d₁ m) = d₀ + 2 * d₁ + 3 * m := by
  rw [Fintype.card_congr (varEquiv d₀ d₁ m), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin]
  ring

variable (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include hD

/-- **`hdim I_G = d₀ + d₁ + 2m`** (affine cone dimensions: each elliptic cone has dimension `2`). -/
theorem hdim_IG (h2 : (2 : K) ≠ 0) :
    (hdata blk D K (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)).1 = d₀ + d₁ + 2 * m := by
  have hne := (IG_isPrime (d₀ := d₀) (d₁ := d₁) g₂ g₃ h2).ne_top
  have h := hdim_add_height_eq blk D hD hne
  rw [IG, height_IG g₂ g₃ h2, lG_length, card_Var] at h
  have h' : (((hdata blk D K (IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)).1 + (d₁ + m) : ℕ) : ℕ∞) =
      ((d₀ + 2 * d₁ + 3 * m : ℕ) : ℕ∞) := by
    push_cast; exact h
  have := ENat.natCast_inj.mp h'
  omega

/-- The point `0`: `X = 0`, `Y = Z = 1`, `U = W = 0` (the `V`-coordinates are free). -/
def pt0 : Var d₀ d₁ m → K
  | .x _ => 0
  | .y _ => 1
  | .z _ => 1
  | .e _ _ => 0

/-- `V`-coordinates. -/
def isV : Var d₀ d₁ m → Prop
  | .e _ c => c = 1
  | _ => False

instance : DecidablePred (isV : Var d₀ d₁ m → Prop) := fun v => by
  cases v <;> unfold isV <;> infer_instance

omit hD in
theorem card_isV : (Finset.univ.filter fun v : Var d₀ d₁ m => isV v).card = m := by
  have : (Finset.univ.filter fun v : Var d₀ d₁ m => isV v) =
      Finset.univ.image fun k : Fin m => (Var.e k 1 : Var d₀ d₁ m) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    cases v with
    | e k c =>
      simp only [isV, Var.e.injEq]
      exact ⟨fun h => ⟨k, by simp [h]⟩, fun ⟨_, _, h⟩ => h.symm⟩
    | _ => simp [isV]
  rw [this, Finset.card_image_of_injective _ (fun a b h => by cases h; rfl)]
  simp

variable (K) in
/-- The linear ideal of the closure of the cone over `0`. -/
noncomputable def q0 (d₀ d₁ m : ℕ) : Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  Ideal.span ((fun v => X v - C (pt0 v)) '' {v | ¬ isV v})

variable (K) in
/-- The projection onto the closure of the cone over `0`. -/
noncomputable def φ0 : MvPolynomial (Var d₀ d₁ m) K →ₐ[K] MvPolynomial (Var d₀ d₁ m) K :=
  aeval fun v => if isV v then X v else C (pt0 v)

omit hD in
theorem sub_φ0_mem (P : MvPolynomial (Var d₀ d₁ m) K) : P - φ0 K P ∈ q0 K d₀ d₁ m := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [φ0]
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    rwa [map_add, add_sub_add_comm]
  | mul_X p v hp =>
    have hv : X v - φ0 K (X v) ∈ q0 K d₀ d₁ m := by
      by_cases h : isV v
      · simp [φ0, h]
      · exact Ideal.subset_span ⟨v, h, by simp [φ0, h]⟩
    have : p * X v - φ0 K (p * X v) = (p - φ0 K p) * X v + φ0 K p * (X v - φ0 K (X v)) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hv)

omit hD in
theorem vanish_zero_le_q0 [Infinite K] :
    vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃)) ≤ q0 K d₀ d₁ m := by
  intro P hP
  have hφ : φ0 K P = 0 := by
    have hprod : φ0 K P * ∏ k, X (Var.e k 1 : Var d₀ d₁ m) = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_prod, map_zero, φ0, eval_aeval']
      by_cases hy : ∀ k, y (.e k 1) ≠ 0
      · let lam : Fin m → Kˣ := fun k => Units.mk0 _ (hy k)
        have : (fun v => eval y (if isV v then X v else C (pt0 v))) =
            coords (0 : GPt K d₀ d₁ g₂ g₃) lam := by
          funext v
          cases v with
          | x i => simp [isV, pt0, coords]
          | y j => simp [isV, pt0, coords]
          | z j => simp [isV, pt0, coords]
          | e k c => fin_cases c <;> simp [isV, pt0, coords, lam, rep, O]
        rw [this, mem_vanish_singleton.mp hP lam, zero_mul]
      · push Not at hy
        obtain ⟨k, hk⟩ := hy
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simpa using hk), mul_zero]
    have hne : (∏ k, X (Var.e k 1 : Var d₀ d₁ m) : MvPolynomial (Var d₀ d₁ m) K) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => X_ne_zero _
    exact (mul_eq_zero.mp hprod).resolve_right hne
  have := sub_φ0_mem P
  rwa [hφ, sub_zero] at this

omit hD in
theorem q0_ne_top : q0 K d₀ d₁ m ≠ ⊤ := by
  intro h
  have hle : q0 K d₀ d₁ m ≤ RingHom.ker (eval (pt0 (d₀ := d₀) (d₁ := d₁) (m := m))) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, -, rfl⟩
    simp
  have := hle (h ▸ Submodule.mem_top : (1 : MvPolynomial (Var d₀ d₁ m) K) ∈ q0 K d₀ d₁ m)
  simp at this

theorem hdim_q0 : m ≤ (hdata blk D K (q0 K d₀ d₁ m)).1 := by
  classical
  set s := (Finset.univ.filter fun v : Var d₀ d₁ m => ¬ isV v).image
    fun v => (X v - C (pt0 v) : MvPolynomial (Var d₀ d₁ m) K) with hs
  have hq : q0 K d₀ d₁ m = Ideal.span (s : Set _) := by
    rw [q0, hs, Finset.coe_image, Finset.coe_filter]
    simp
  have h := hdim_add_height_eq blk D hD (q0_ne_top (K := K) (d₀ := d₀) (d₁ := d₁) (m := m))
  have hht := Ideal.height_span_le_card_of_span_ne_top (s := s) (hq ▸ q0_ne_top)
  have hcard : s.card ≤ (Finset.univ.filter fun v : Var d₀ d₁ m => ¬ isV v).card :=
    Finset.card_image_le
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v : Var d₀ d₁ m => isV v)
  rw [card_isV, Finset.card_univ] at hsplit
  rw [← hq] at hht
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top (q0_ne_top (K := K)
    (d₀ := d₀) (d₁ := d₁) (m := m)))
  rw [← hn] at h hht
  have h' : (((hdata blk D K (q0 K d₀ d₁ m)).1 + n : ℕ) : ℕ∞) =
      ((Fintype.card (Var d₀ d₁ m) : ℕ) : ℕ∞) := by
    push_cast; exact h
  have h1 := ENat.natCast_inj.mp h'
  have h2 : n ≤ s.card := ENat.natCast_le_natCast.mp hht
  omega

/-- **Ideals vanishing at `0` have dimension `≥ m`.** -/
theorem hdim_ge_of_le_vanish_zero [Infinite K]
    {L : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (hL : L ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃))) :
    m ≤ (hdata blk D K L).1 := by
  have h := hdata_le_of_le blk D K (hL.trans vanish_zero_le_q0) q0_ne_top
  have := hdim_q0 (K := K) (d₀ := d₀) (d₁ := d₁) D hD
  rcases h with h | ⟨h, -⟩ <;> omega

end Dims

/-! ### The pigeonhole -/

section Flat

variable [DecidableEq K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
  {W : Submodule K (LieE K d₀ d₁ m)} {S : Finset (GPt K d₀ d₁ g₂ g₃)}
  {P : MvPolynomial (Var d₀ d₁ m) K} {T : ℕ} (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
include h2 hΔ hD

/-- `hdim L₀ < d₀ + d₁ + 2m` (`P ∉ I_G`, `I_G` prime). -/
theorem hdim_L0_lt (hP : P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃) (hL0 : Lr g₂ g₃ W S P T 0 ≠ ⊤) :
    (hdata blk D K (Lr g₂ g₃ W S P T 0)).1 < d₀ + d₁ + 2 * m := by
  have hprime := IG_isPrime (d₀ := d₀) (d₁ := d₁) g₂ g₃ h2
  -- a translate of `P` by `0` is still outside `I_G`
  rw [← vanish_univ hΔ h2] at hP
  obtain ⟨h, -, lam, hh⟩ : ∃ h ∈ (Set.univ : Set (GPt K d₀ d₁ g₂ g₃)), ∃ lam,
      eval (coords h lam) P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP (mem_vanish.mpr hcon)
  obtain ⟨c, hc⟩ := exists_good h2 hΔ h 0
  obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc
  obtain ⟨lam', hlam'⟩ := exists_sq_mul μ lam
  have hτ : τ g₂ g₃ 0 c P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ := by
    intro hm
    have := mem_vanish.mp (IG_le_vanish h2 Set.univ hm) h (Set.mem_univ _) lam'
    rw [hμ, hlam', add_zero] at this
    exact hh this
  have hlt := hdim_section_lt blk D K hD (J := IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
    (P := τ g₂ g₃ 0 c P) (fun Q hQ => (hprime.mem_or_mem hQ).resolve_left hτ)
    (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (transl_mem_L0 c)))) hL0
  rwa [hdim_IG D hD h2] at hlt

/-- **Pigeonhole**: two consecutive ideals of the chain have the same Hilbert dimension. -/
theorem exists_flat (hS : (0 : GPt K d₀ d₁ g₂ g₃) ∈ S) (hP : P ∉ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃)
    (hlast : Lr g₂ g₃ W S P T (d₀ + d₁ + m) ≤ vanish ({0} : Set (GPt K d₀ d₁ g₂ g₃))) :
    ∃ r < d₀ + d₁ + m,
      (hdata blk D K (Lr g₂ g₃ W S P T (r + 1))).1 = (hdata blk D K (Lr g₂ g₃ W S P T r)).1 := by
  have hlast' : Lr g₂ g₃ W S P T (d₀ + d₁ + m) ≠ ⊤ :=
    ne_top_of_le_ne_top (vanish_ne_top (Set.singleton_nonempty 0)) hlast
  have hne : ∀ r ≤ d₀ + d₁ + m, Lr g₂ g₃ W S P T r ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hlast' (Lr_mono' hS hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d₀ + d₁ + m, (hdata blk D K (Lr g₂ g₃ W S P T (r + 1))).1 <
      (hdata blk D K (Lr g₂ g₃ W S P T r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D K (Lr_mono hS r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d₀ + d₁ + m, (hdata blk D K (Lr g₂ g₃ W S P T r)).1 + r ≤
      (hdata blk D K (Lr g₂ g₃ W S P T 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have h0 := hdim_L0_lt h2 hΔ D hD hP (hne 0 (Nat.zero_le _))
  have h1 := hdec (d₀ + d₁ + m) le_rfl
  have h2' := hdim_ge_of_le_vanish_zero D hD hlast
  omega

end Flat

/-! ### Roy's vanishing claim -/

section AVO

variable [DecidableEq K] [CharZero K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
  (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Roy's vanishing claim** (`hAVO`): with `p ⊇ L_{r+1}`, `V = Z(p)` and `GV` stabilizing `V`,
the ideal `A = I_G + (τ v c Q : Q ∈ gensR r, v ∈ V, all c)` vanishes to order `> T` along `W` on
`S + GV`. -/
theorem hAVO (W : Submodule K (LieE K d₀ d₁ m)) (S : Finset (GPt K d₀ d₁ g₂ g₃))
    {P : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hP : IsHomE P d) (T r : ℕ)
    {p : Ideal (MvPolynomial (Var d₀ d₁ m) K)} (hLp : Lr g₂ g₃ W S P T (r + 1) ≤ p)
    (GV : Set (GPt K d₀ d₁ g₂ g₃))
    (hGV : ∀ u ∈ GV, ∀ v ∈ zeros (g₂ := g₂) (g₃ := g₃) (p : Set _), u + v ∈ zeros (p : Set _)) :
    IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ⊔ Ideal.span {Q' | ∃ Q ∈ gensR g₂ g₃ W S P T r,
        ∃ v ∈ zeros (g₂ := g₂) (g₃ := g₃) (p : Set _), ∃ c, Q' = τ g₂ g₃ v c Q} ≤
      VO g₂ g₃ W T (vanish (⋃ s ∈ S, gtransl s GV)) := by
  refine sup_le (IG_le_VO h2 W T _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨_, ⟨σ, hσ, c', ch₁, l₀, hl₀W, hl₀, rfl⟩, v, hv, c, rfl⟩
  refine mem_VO_vanish.mpr fun y hy => ?_
  simp only [Set.mem_iUnion] at hy
  obtain ⟨s, hs, hy⟩ := hy
  have hu : y - s ∈ GV := mem_gtransl.mp hy
  set z := y + v + σ with hz
  -- 1. `P` vanishes to order `> (r + 1) T` at `z`
  have h1 : P ∈ VO1 g₂ g₃ (chartAt z) W ((r + 1) * T) (vanish {z}) := by
    intro l hlW hl
    have hgen : ∀ c'', τ g₂ g₃ (σ + s) c'' (DL (Dh g₂ g₃ (chartAt z)) l P) ∈ p := fun c'' =>
      hLp (Ideal.mem_sup_right (Ideal.subset_span
        ⟨σ + s, add_mem_sig hσ hs, c'', chartAt z, l, hlW, hl, rfl⟩))
    have huv := hGV _ hu v hv
    obtain ⟨c'', hc''⟩ := exists_good h2 hΔ (y - s + v) (σ + s)
    obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hc''
    refine mem_vanish_singleton.mpr fun ν => ?_
    obtain ⟨lam, hlam⟩ := exists_sq_mul μ ν
    have := huv _ (hgen c'') lam
    rw [hμ, hlam] at this
    rwa [show y - s + v + (σ + s) = z by rw [hz]; abel] at this
  -- 2. a word of length `≤ r T` lowers the order to `> T`
  have h2' : DL (Dh g₂ g₃ ch₁) l₀ P ∈ VO1 g₂ g₃ (chartAt z) W T (vanish {z}) :=
    DL_mem_VO1_chartAt h2 W ch₁ l₀ hl₀W hP
      (VOg_anti (by rw [Nat.succ_mul]; omega) h1)
  -- 3, 4. two translations
  have h3 := transl_van h2 hΔ W (h := y + v) (g := σ) c' T (isHomE_DL hP ch₁ l₀) h2'
  have h4 := transl_van h2 hΔ W (h := y) (g := v) c T
    (isHomE_transl (isHomE_DL hP ch₁ l₀) σ c') h3
  exact (vanAll_iff_vanCan h2 W
    (isHomE_transl (isHomE_transl (isHomE_DL hP ch₁ l₀) σ c') v c) T y).mpr h4

end AVO

end LSG.ME
