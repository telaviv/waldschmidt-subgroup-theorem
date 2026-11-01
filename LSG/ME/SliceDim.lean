import Mathlib
import LSG.ME.SliceIG

/-!
# Partial slices: primality, the dimension drop, the slice Nullstellensatz (STAGE2 §11, S1)

For a Finset `s` of elliptic blocks, `vanishP s α E` is the ideal of polynomials vanishing at the
cone representatives of the points `g ∈ E` with `ℓ_k(rep g_k) ≠ 0` (`k ∈ s`) that are normalised
(`ℓ_k = 1`) in the blocks `k ∈ s` and arbitrary elsewhere. `vanishP ∅ α E = vanish E` and
`vanishP univ α E = vanishS α E`.

* `homP s α N P = Σ_e (∏_{k ∈ s} ℓ_k^{N − e_k}) · P_e` (components for the weights of the blocks in
  `s`), with **`eval_homP`**: at `coords g λ`, it is
  `∏_{k ∈ s} (λ_k ℓ_k(rep g_k))^N · P(normalised)`.
* **`vanishP_isPrime`**: `vanishP s α E` is prime if `vanish E` is prime, all `ℓ_k ∉ vanish E`
  (`k ∈ s`) and some point of `E` has all `ℓ_k(rep) ≠ 0`.
* `vanishP_mono`, `lsl_sub_one_mem_vanishP`, `lsl_sub_one_notMem_vanishP`.
* **`hdim_vanishP_add_le`**: `hdim (vanishP univ α E) + m ≤ hdim (vanish E)` (a chain of `m`
  sections by `ℓ_k − 1`, `hdim_section_lt`).
* `hom_mem_vanish_of_mem_vanishP`, so `hfun_le_of_hom` applies to `vanishP univ`.
* **`radical_sl`** (slice Nullstellensatz): for `I_G ≤ I`, `√(sl α I) = vanish' nrm (Zs α I)`,
  `Zs α I` the points with all `ℓ_k(rep) ≠ 0` at whose normalised representative `I` vanishes.
-/

open MvPolynomial LSG.Elliptic Module
open StrongSix.M2 (FLE hfun hdata)

namespace LSG.ME

variable {K : Type*} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

open Classical in
/-- Normalise the scalings in the blocks `k ∈ s` (where `ℓ_k(rep) ≠ 0`). -/
noncomputable def nscal (s : Finset (Fin m)) (α : Fin m → K) (g : GPt K d₀ d₁ g₂ g₃)
    (lam : Fin m → Kˣ) : Fin m → Kˣ :=
  fun k => if h : k ∈ s ∧ lval α g k ≠ 0 then Units.mk0 (lval α g k)⁻¹ (inv_ne_zero h.2) else lam k

/-- The partially sliced vanishing ideal. -/
noncomputable def vanishP (s : Finset (Fin m)) (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    Ideal (MvPolynomial (Var d₀ d₁ m) K) :=
  StrongSix.M2.vanish' (fun p : GPt K d₀ d₁ g₂ g₃ × (Fin m → Kˣ) => coords p.1 (nscal s α p.1 p.2))
    {p | p.1 ∈ E ∧ ∀ k ∈ s, lval α p.1 k ≠ 0}

theorem mem_vanishP {s : Finset (Fin m)} {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    {P : MvPolynomial (Var d₀ d₁ m) K} :
    P ∈ vanishP s α E ↔ ∀ g ∈ E, (∀ k ∈ s, lval α g k ≠ 0) → ∀ lam,
      eval (coords g (nscal s α g lam)) P = 0 := by
  rw [vanishP, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg hs lam; exact h (g, lam) ⟨hg, hs⟩
  · rintro h ⟨g, lam⟩ ⟨hg, hs⟩; exact h g hg hs lam

theorem nscal_mem {s : Finset (Fin m)} {α : Fin m → K} {g : GPt K d₀ d₁ g₂ g₃} {lam : Fin m → Kˣ}
    {k : Fin m} (hk : k ∈ s) (hl : lval α g k ≠ 0) :
    (nscal s α g lam k : K) = (lval α g k)⁻¹ := by
  simp [nscal, hk, hl]

theorem nscal_notMem {s : Finset (Fin m)} {α : Fin m → K} {g : GPt K d₀ d₁ g₂ g₃}
    {lam : Fin m → Kˣ} {k : Fin m} (hk : k ∉ s) : nscal s α g lam k = lam k := by
  simp [nscal, hk]

theorem vanishP_empty (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    vanishP ∅ α E = vanish E := by
  ext P
  rw [mem_vanishP, mem_vanish]
  have e : ∀ (g : GPt K d₀ d₁ g₂ g₃) lam, nscal ∅ α g lam = lam := fun g lam => by
    funext k; exact nscal_notMem (Finset.notMem_empty k)
  simp [e]

theorem vanish_le_vanishP (s : Finset (Fin m)) (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    vanish E ≤ vanishP s α E := fun _ hP =>
  mem_vanishP.mpr fun g hg _ _ => mem_vanish.mp hP g hg _

theorem vanishP_mono {s s' : Finset (Fin m)} (h : s ⊆ s') (α : Fin m → K)
    (E : Set (GPt K d₀ d₁ g₂ g₃)) : vanishP s α E ≤ vanishP s' α E := by
  intro P hP
  refine mem_vanishP.mpr fun g hg hs' lam => ?_
  have e : nscal s α g (nscal s' α g lam) = nscal s' α g lam := by
    funext k
    by_cases hk : k ∈ s
    · apply Units.ext
      rw [nscal_mem hk (hs' k (h hk)), nscal_mem (h hk) (hs' k (h hk))]
    · exact nscal_notMem hk
  rw [← e]
  exact mem_vanishP.mp hP g hg (fun k hk => hs' k (h hk)) _

theorem lsl_sub_one_mem_vanishP {s : Finset (Fin m)} {k : Fin m} (hk : k ∈ s) (α : Fin m → K)
    (E : Set (GPt K d₀ d₁ g₂ g₃)) : lsl α k - 1 ∈ vanishP s α E := by
  refine mem_vanishP.mpr fun g _ hs lam => ?_
  rw [map_sub, eval_coords_lsl, nscal_mem hk (hs k hk), map_one, inv_mul_cancel₀ (hs k hk),
    sub_self]

theorem lsl_sub_one_notMem_vanishP (h2 : (2 : K) ≠ 0) {s : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ s) (α : Fin m → K) {E : Set (GPt K d₀ d₁ g₂ g₃)} {g : GPt K d₀ d₁ g₂ g₃}
    (hg : g ∈ E) (hs : ∀ k ∈ s, lval α g k ≠ 0) : lsl α k - 1 ∉ vanishP s α E := by
  classical
  intro hmem
  have hev : ∀ lam : Fin m → Kˣ, (lam k : K) * lval α g k - 1 = 0 := fun lam => by
    have := mem_vanishP.mp hmem g hg hs lam
    rwa [map_sub, eval_coords_lsl, nscal_notMem hk, map_one] at this
  by_cases h1 : lval α g k = 1
  · have := hev fun _ => Units.mk0 2 h2
    rw [h1] at this
    norm_num at this
  · have := hev 1
    simp only [Pi.one_apply, Units.val_one, one_mul] at this
    exact h1 (sub_eq_zero.mp this)

/-! ### Homogenisation in the blocks of `s` -/

/-- The weights of the blocks in `s`. -/
def wS (s : Finset (Fin m)) : Var d₀ d₁ m → Fin m → ℕ := fun v k => if k ∈ s then wV v k else 0

/-- `homP s α N P = Σ_e (∏_{k ∈ s} ℓ_k^{N − e_k}) · P_e`. -/
noncomputable def homP (s : Finset (Fin m)) (α : Fin m → K) (N : ℕ)
    (P : MvPolynomial (Var d₀ d₁ m) K) : MvPolynomial (Var d₀ d₁ m) K :=
  ∑ e : Fin m → Fin (N + 1), (∏ k ∈ s, lsl α k ^ (N - (e k : ℕ))) *
    weightedHomogeneousComponent (wS s) (fun k => (e k : ℕ)) P

theorem weight_wS_le (s : Finset (Fin m)) (x : Var d₀ d₁ m →₀ ℕ) (k : Fin m) :
    Finsupp.weight (wS s) x k ≤ x.degree := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.degree]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, wS]
  split_ifs
  · cases v <;> simp [wV, Pi.single_apply]
    split_ifs <;> simp
  · simp

/-- `P` is the sum of its `wS`-components in the box `[0, N]^m`, `N ≥ totalDegree P`. -/
theorem sum_box_comp (s : Finset (Fin m)) {N : ℕ} {P : MvPolynomial (Var d₀ d₁ m) K}
    (hN : P.totalDegree ≤ N) :
    ∑ e : Fin m → Fin (N + 1), weightedHomogeneousComponent (wS s) (fun k => (e k : ℕ)) P = P := by
  classical
  ext x
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hx : P.coeff x = 0
  · simp [hx]
  have hb : ∀ k, Finsupp.weight (wS s) x k < N + 1 := fun k =>
    Nat.lt_succ_of_le ((weight_wS_le s x k).trans
      ((le_totalDegree (MvPolynomial.mem_support_iff.mpr hx)).trans hN))
  let e₀ : Fin m → Fin (N + 1) := fun k => ⟨Finsupp.weight (wS s) x k, hb k⟩
  rw [Finset.sum_eq_single e₀ (fun e _ he => ite_eq_right_iff.mpr fun hw =>
      absurd (funext fun k => Fin.ext (congrFun hw k).symm) he) (by simp)]
  simp only [↓reduceIte]

/-- The scale factors `ρ_k = λ_k ℓ_k(rep g_k)` (`k ∈ s`), `1` elsewhere. -/
noncomputable def rho (s : Finset (Fin m)) (α : Fin m → K) (g : GPt K d₀ d₁ g₂ g₃)
    (lam : Fin m → Kˣ) (k : Fin m) : K :=
  if k ∈ s then (lam k : K) * lval α g k else 1

theorem coords_eq_rho {s : Finset (Fin m)} {α : Fin m → K} {g : GPt K d₀ d₁ g₂ g₃}
    (hs : ∀ k ∈ s, lval α g k ≠ 0) (lam : Fin m → Kˣ) :
    coords g lam = fun v => (∏ k, rho s α g lam k ^ wS s v k) * coords g (nscal s α g lam) v := by
  classical
  funext v
  cases v with
  | x i => simp [coords, wS, wV]
  | y j => simp [coords, wS, wV]
  | z j => simp [coords, wS, wV]
  | e k c =>
    simp only [coords, coordsZ_e, wS, wV, Pi.single_apply]
    rw [Finset.prod_eq_single k (fun b _ hb => by simp; intro _ h; exact absurd h hb) (by simp)]
    by_cases hk : k ∈ s
    · simp only [hk, ite_true, rho, pow_one, nscal_mem hk (hs k hk)]
      field_simp [hs k hk]
    · simp [hk, rho, nscal_notMem hk]

theorem eval_homP {s : Finset (Fin m)} {α : Fin m → K} {N : ℕ} {P : MvPolynomial (Var d₀ d₁ m) K}
    (hN : P.totalDegree ≤ N) {g : GPt K d₀ d₁ g₂ g₃} (hs : ∀ k ∈ s, lval α g k ≠ 0)
    (lam : Fin m → Kˣ) :
    eval (coords g lam) (homP s α N P) =
      (∏ k ∈ s, ((lam k : K) * lval α g k) ^ N) * eval (coords g (nscal s α g lam)) P := by
  classical
  conv_rhs => rw [← sum_box_comp s hN]
  rw [homP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hh := weightedHomogeneousComponent_isWeightedHomogeneous (w := wS s)
    (fun k => (e k : ℕ)) P
  rw [map_mul, map_prod, coords_eq_rho hs lam, eval_scale (wS s) (rho s α g lam) _ hh,
    ← coords_eq_rho hs lam]
  have hl : ∀ k ∈ s, eval (coords g lam) (lsl α k) = rho s α g lam k := fun k hk => by
    rw [eval_coords_lsl]; simp [rho, hk]
  rw [Finset.prod_congr rfl fun k hk => by rw [map_pow, hl k hk]]
  have hsplit : (∏ k, rho s α g lam k ^ (e k : ℕ)) = ∏ k ∈ s, rho s α g lam k ^ (e k : ℕ) := by
    rw [← Finset.prod_subset (Finset.subset_univ s) (fun k _ hk => by simp [rho, hk])]
  rw [hsplit, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hle : (e k : ℕ) ≤ N := Nat.lt_succ_iff.mp (e k).isLt
  simp only [rho, hk, ite_true]
  rw [← pow_add, Nat.sub_add_cancel hle]

/-! ### Primality and the dimension drop -/

theorem prod_lsl_notMem {s : Finset (Fin m)} {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k ∈ s, lsl α k ∉ vanish E) :
    ∏ k ∈ s, lsl (d₀ := d₀) (d₁ := d₁) α k ∉ vanish E := by
  intro h
  obtain ⟨k, hk, hk'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp h
  exact hℓ k hk hk'

theorem homP_mem_vanish_iff {s : Finset (Fin m)} {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    {N : ℕ} {P : MvPolynomial (Var d₀ d₁ m) K} (hN : P.totalDegree ≤ N)
    (hhP : homP s α N P ∈ vanish E) :
    P ∈ vanishP s α E := by
  refine mem_vanishP.mpr fun g hg hs lam => ?_
  have h0 := mem_vanish.mp hhP g hg lam
  rw [eval_homP hN hs lam] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    pow_ne_zero _ (mul_ne_zero (Units.ne_zero _) (hs k hk))

/-- **Partial slices of irreducible sets are irreducible.** -/
theorem vanishP_isPrime {s : Finset (Fin m)} {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k ∈ s, lsl α k ∉ vanish E) {g₀ : GPt K d₀ d₁ g₂ g₃}
    (hg₀ : g₀ ∈ E) (hs₀ : ∀ k ∈ s, lval α g₀ k ≠ 0) : (vanishP s α E).IsPrime := by
  classical
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ m) K) ∈ vanishP s α E := htop ▸ Submodule.mem_top
    have := mem_vanishP.mp h1 g₀ hg₀ hs₀ 1
    simp at this
  set NP := P.totalDegree
  set NQ := Q.totalDegree
  have hmem : homP s α NP P * homP s α NQ Q * ∏ k ∈ s, lsl (d₀ := d₀) (d₁ := d₁) α k ∈
      vanish E := by
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [map_mul, map_mul, map_prod]
    by_cases hs : ∀ k ∈ s, lval α g k ≠ 0
    · rw [eval_homP le_rfl hs lam, eval_homP le_rfl hs lam]
      have := mem_vanishP.mp hPQ g hg hs lam
      rw [map_mul] at this
      rcases mul_eq_zero.mp this with h | h <;> simp [h]
    · push Not at hs
      obtain ⟨k, hk, hk0⟩ := hs
      rw [Finset.prod_eq_zero hk (by rw [eval_coords_lsl, hk0, mul_zero]), mul_zero]
  rcases hp.mem_or_mem hmem with h | h
  · rcases hp.mem_or_mem h with h' | h'
    · exact Or.inl (homP_mem_vanish_iff le_rfl h')
    · exact Or.inr (homP_mem_vanish_iff le_rfl h')
  · exact absurd h (prod_lsl_notMem hp hℓ)

/-- **The dimension drop**: `hdim (vanishP s α E) + #s ≤ hdim (vanish E)`. -/
theorem hdim_vanishP_add_le (h2 : (2 : K) ≠ 0) (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)} (hp : (vanish E).IsPrime)
    (hℓ : ∀ k, lsl α k ∉ vanish E) {g₀ : GPt K d₀ d₁ g₂ g₃} (hg₀ : g₀ ∈ E)
    (hs₀ : ∀ k, lval α g₀ k ≠ 0) (s : Finset (Fin m)) :
    (hdata blk D K (vanishP s α E)).1 + s.card ≤ (hdata blk D K (vanish E)).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vanishP_empty]
  | insert k s hk ih =>
    have hpr := vanishP_isPrime hp (fun k _ => hℓ k) hg₀ (s := s) (fun k _ => hs₀ k)
    have hpr' := vanishP_isPrime hp (fun k _ => hℓ k) hg₀ (s := insert k s) (fun k _ => hs₀ k)
    have hlt := StrongSix.M2.hdim_section_lt blk D K hD (J := vanishP s α E)
      (L := vanishP (insert k s) α E) (P := lsl α k - 1)
      (fun Q hQ => (hpr.mem_or_mem hQ).resolve_left
        (lsl_sub_one_notMem_vanishP h2 hk α hg₀ fun k _ => hs₀ k))
      (sup_le (vanishP_mono (Finset.subset_insert k s) α E)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (lsl_sub_one_mem_vanishP (Finset.mem_insert_self k s) α E))))
      hpr'.ne_top
    rw [Finset.card_insert_of_notMem hk]
    omega

/-- Multihomogeneous elements of `vanishP univ α E` lie in `vanish E`. -/
theorem hom_mem_vanish_of_mem_vanishP {α : Fin m → K} {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hp : (vanish E).IsPrime) (hℓ : ∀ k, lsl α k ∉ vanish E)
    {Q : MvPolynomial (Var d₀ d₁ m) K} {d : Fin m → ℕ} (hQ : IsWeightedHomogeneous wV Q d)
    (hQs : Q ∈ vanishP Finset.univ α E) : Q ∈ vanish E := by
  classical
  have hmul : Q * ∏ k, lsl (d₀ := d₀) (d₁ := d₁) α k ∈ vanish E := by
    refine mem_vanish.mpr fun g hg lam => ?_
    rw [map_mul, map_prod]
    by_cases h0 : ∃ k, lval α g k = 0
    · obtain ⟨k, hk⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_coords_lsl, hk, mul_zero]),
        mul_zero]
    push Not at h0
    have hn := mem_vanishP.mp hQs g hg (fun k _ => h0 k) lam
    rw [eval_coords_eq_zero_iff hQ g _ lam] at hn
    rw [hn, zero_mul]
  exact (hp.mem_or_mem hmul).resolve_right (prod_lsl_notMem hp fun k _ => hℓ k)

theorem sl_vanish_le_vanishP (α : Fin m → K) (E : Set (GPt K d₀ d₁ g₂ g₃)) :
    sl α (vanish E) ≤ vanishP Finset.univ α E :=
  sup_le (vanish_le_vanishP _ α E) (Ideal.span_le.mpr (by
    rintro _ ⟨k, rfl⟩; exact lsl_sub_one_mem_vanishP (Finset.mem_univ k) α E))

/-! ### The slice Nullstellensatz -/

/-- The points with all `ℓ_k(rep) ≠ 0` at whose normalised representative `I` vanishes. -/
def Zs (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) : Set (GPt K d₀ d₁ g₂ g₃) :=
  {g | (∀ k, lval α g k ≠ 0) ∧ ∀ P ∈ I, eval (nrm α g) P = 0}

/-- A zero of `I_G` with nonzero cone blocks is a cone representative. -/
theorem exists_coords_of_IG (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
    {a : Var d₀ d₁ m → K} (ha : ∀ P ∈ IG (d₀ := d₀) (d₁ := d₁) g₂ g₃, eval a P = 0)
    (hne : ∀ k, (fun c => a (.e k c)) ≠ 0) :
    ∃ (g : GPt K d₀ d₁ g₂ g₃) (ν : Fin m → Kˣ), a = coords g ν := by
  classical
  have hyz : ∀ j, a (.y j) * a (.z j) = 1 := fun j => by
    have := ha _ (YZ_mem_IG g₂ g₃ j)
    simpa [YZ, sub_eq_zero] using this
  set cv : Fin m → Fin 3 → K := fun k c => a (.e k c)
  have hF : ∀ k, Fv (g₂ k) (g₃ k) (cv k) = 0 := fun k => by
    have := ha _ (Fk_mem_IG g₂ g₃ k)
    simpa [Fk, LSG.Elliptic.F, Fv, cv] using this
  choose u hu0 hu using fun k => exists_smul_rep h2 (hΔ k) (hF k) (hne k)
  let g : GPt K d₀ d₁ g₂ g₃ := (fun i => a (.x i),
    Additive.ofMul fun j => Units.mkOfMulEqOne _ _ (hyz j),
    fun k => toPoint (g₂ k) (g₃ k) (cv k))
  refine ⟨g, fun k => Units.mk0 (u k) (hu0 k), ?_⟩
  funext v
  cases v with
  | x i => rfl
  | y j => rfl
  | z j =>
    change a (.z j) = (((Units.mkOfMulEqOne _ _ (hyz j))⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, Units.val_mkOfMulEqOne]
    exact eq_inv_of_mul_eq_one_right (hyz j)
  | e k c => exact congrFun (hu k) c

theorem sl_le_vanish_Zs (α : Fin m → K) (I : Ideal (MvPolynomial (Var d₀ d₁ m) K)) :
    sl α I ≤ StrongSix.M2.vanish' (nrm α) (Zs (g₂ := g₂) (g₃ := g₃) α I) := by
  refine sup_le (fun P hP => (StrongSix.M2.mem_vanish' _).mpr fun g hg => hg.2 P hP)
    (Ideal.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine (StrongSix.M2.mem_vanish' _).mpr fun g hg => ?_
  rw [map_sub, nrm, eval_coords_lsl]
  simp [hg.1 k]

/-- **The slice Nullstellensatz**: for `I_G ≤ I`, `√(sl α I) = I(Zs α I)` (normalised points). -/
theorem radical_sl [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
    (α : Fin m → K) {I : Ideal (MvPolynomial (Var d₀ d₁ m) K)}
    (hI : IG (d₀ := d₀) (d₁ := d₁) g₂ g₃ ≤ I) :
    (sl α I).radical = StrongSix.M2.vanish' (nrm α) (Zs (g₂ := g₂) (g₃ := g₃) α I) := by
  classical
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  ext P
  rw [mem_vanishingIdeal_iff, StrongSix.M2.mem_vanish']
  constructor
  · intro h g hg
    refine h (nrm α g) ?_
    rw [mem_zeroLocus_iff]
    intro p hp
    exact (StrongSix.M2.mem_vanish' _).mp (sl_le_vanish_Zs α I hp) g hg
  · intro h x hx
    rw [mem_zeroLocus_iff] at hx
    have hxI : ∀ p ∈ sl α I, eval x p = 0 := hx
    have hl : ∀ k, eval x (lsl α k) = 1 := fun k => by
      have := hxI _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
      rwa [map_sub, map_one, sub_eq_zero] at this
    have hne : ∀ k, (fun c => x (.e k c)) ≠ 0 := fun k h0 => by
      have := hl k
      simp only [lsl, map_add, map_mul, eval_X, eval_C] at this
      rw [show x (.e k 1) = 0 from congrFun h0 1, show x (.e k 2) = 0 from congrFun h0 2] at this
      simp at this
    obtain ⟨g, ν, rfl⟩ := exists_coords_of_IG h2 hΔ
      (fun p hp => hxI p (Ideal.mem_sup_left (hI hp))) hne
    have hlv : ∀ k, (ν k : K) * lval α g k = 1 := fun k => by
      rw [← eval_coords_lsl]; exact hl k
    have hlv0 : ∀ k, lval α g k ≠ 0 := fun k h0 => by
      have := hlv k; rw [h0, mul_zero] at this; exact zero_ne_one this
    have hν : coords g ν = nrm α g := by
      unfold nrm
      congr 1
      funext k
      apply Units.ext
      simp only [hlv0 k, ↓reduceDIte, Units.val_mk0]
      exact eq_inv_of_mul_eq_one_left (hlv k)
    have hg : g ∈ Zs (g₂ := g₂) (g₃ := g₃) α I :=
      ⟨hlv0, fun p hp => by rw [← hν]; exact hxI p (Ideal.mem_sup_left hp)⟩
    have := h g hg
    rw [← hν] at this
    exact this

end LSG.ME
