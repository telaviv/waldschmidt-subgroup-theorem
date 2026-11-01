import Mathlib
import LSG.ME.TranslHF
import LSG.ME.SubgroupComp

/-!
# Hilbert functions of finite unions of cosets, projective form (STAGE2 §6, S2.7)

StrongSix's `hfun_cosets_ge` uses separating polynomials equal to `1` on a coset (`hfun_union2'`).
On cones this is impossible for elliptic cosets (a polynomial equal to `1` at all cone
representatives of a coset has its elliptic-degree-`0` part equal to `1` there, and that part only
involves the linear variables). We replace "`B ≡ 1` on `E₂`" by "**`B` is a non-zero-divisor
modulo `I(E₂)`**", which is purely ideal-theoretic:

* **`hfun_inter_ge`** (any block structure): if `B ∈ J₁` has block degree `≤ c • D` and
  `B x ∈ J₂ → x ∈ J₂`, then `H(J₁; t₁) + H(J₂; t₂) ≤ H(J₁ ⊓ J₂; t)` for `t₁ ≤ t`, `t₂ + c ≤ t`
  (`F_{t₁} ⊕ B · F_{t₂}` injects into `F_t / (J₁ ⊓ J₂)`).
* `vanish_union`: `I(E₁ ∪ E₂) = I(E₁) ⊓ I(E₂)`.
* `exists_sep_proj`: for Zariski-closed `C₁ ⊄ C₂`, some `f ∈ I(C₂) \ I(C₁)`.
* **`hfun_sum_cosets_ge`**: for an irreducible Zariski-closed `V` and a finite set `R` of pairwise
  non-nested translates, `Σ_{a ∈ R} H(I(V + a); t) ≤ H(I(⋃ (V + a)); t + c)`.
* **`hfun_cosets_ge_proj`**: with `hfun_le_transl` (constant `2^m`, `t ↦ 2t`):
  `#R · H(I(V); t) ≤ 2^m · H(I(⋃_{a ∈ R} (V + a)); 2t + c)`.
* `hfun_cosets_ge_subgroup`: the same for cosets of a subgroup `V` (`a − b ∉ V` for `a ≠ b`).
-/

open MvPolynomial Module Submodule
open StrongSix.M2 (FLE hfun mul_mem_FLE FLE_mono mem_FLE_totalDegree)

namespace LSG.ME

/-! ### Two ideals and a non-zero-divisor -/

section Generic

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] {K : Type*}
  [Field K] (β : σ → ι) (D : ι → ℕ)

/-- A complement of `J ∩ F_t` in `F_t`, of dimension `H(J; t)`. -/
theorem exists_compl_hfun (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    ∃ E : Submodule K (MvPolynomial σ K), E ≤ FLE K β (t • D) ∧
      finrank K E = hfun β D K J t ∧ ∀ x ∈ E, x ∈ J → x = 0 := by
  set F := FLE K β (t • D)
  set p := J.restrictScalars K ⊓ F
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  have : FiniteDimensional K p := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional K ↥(q ⊓ F) := Submodule.finiteDimensional_of_le inf_le_right
  have hpE : p ⊓ (q ⊓ F) = ⊥ := eq_bot_iff.mpr fun x hx =>
    hq.disjoint.le_bot ⟨hx.1, hx.2.1⟩
  have hpE' : p ⊔ (q ⊓ F) = F := by
    rw [← sup_inf_assoc_of_le q (inf_le_right : p ≤ F), hq.sup_eq_top, top_inf_eq]
  refine ⟨q ⊓ F, inf_le_right, ?_, fun x hx hxJ => ?_⟩
  · have := Submodule.finrank_sup_add_finrank_inf_eq p (q ⊓ F)
    rw [hpE, hpE', finrank_bot] at this
    change _ = finrank K F - finrank K p
    omega
  · exact (Submodule.mem_bot K).mp (hpE ▸ ⟨⟨hxJ, hx.2⟩, hx⟩)

/-- **Two ideals and a non-zero-divisor.** -/
theorem hfun_inter_ge {J₁ J₂ : Ideal (MvPolynomial σ K)} {B : MvPolynomial σ K} {c : ℕ}
    (hB : B ∈ FLE K β (c • D)) (hBJ : B ∈ J₁) (hB₂ : ∀ x, B * x ∈ J₂ → x ∈ J₂)
    {t₁ t₂ t : ℕ} (h₁ : t₁ ≤ t) (h₂ : t₂ + c ≤ t) :
    hfun β D K J₁ t₁ + hfun β D K J₂ t₂ ≤ hfun β D K (J₁ ⊓ J₂) t := by
  classical
  obtain ⟨E₁, hE₁F, hE₁d, hE₁J⟩ := exists_compl_hfun β D J₁ t₁
  obtain ⟨E₂, hE₂F, hE₂d, hE₂J⟩ := exists_compl_hfun β D J₂ t₂
  set F := FLE K β (t • D)
  have : FiniteDimensional K E₁ := Submodule.finiteDimensional_of_le hE₁F
  have : FiniteDimensional K E₂ := Submodule.finiteDimensional_of_le hE₂F
  let Ψ : (E₁ × E₂) →ₗ[K] MvPolynomial σ K :=
    E₁.subtype ∘ₗ LinearMap.fst K E₁ E₂ + LinearMap.mulLeft K B ∘ₗ E₂.subtype ∘ₗ
      LinearMap.snd K E₁ E₂
  have hΨ : ∀ x, Ψ x = (x.1 : MvPolynomial σ K) + B * x.2 := fun x => rfl
  have hzero : ∀ x, Ψ x ∈ J₁ ⊓ J₂ → x = 0 := by
    intro x hx
    rw [hΨ] at hx
    have h1 : (x.1 : MvPolynomial σ K) = 0 := hE₁J _ x.1.2 (by
      have := J₁.sub_mem hx.1 (J₁.mul_mem_right (x.2 : MvPolynomial σ K) hBJ)
      rwa [add_sub_cancel_right] at this)
    rw [h1, zero_add] at hx
    have h2 : (x.2 : MvPolynomial σ K) = 0 := hE₂J _ x.2.2 (hB₂ _ hx.2)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot K).mpr (hzero x (by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _))
  set U := LinearMap.range Ψ
  have hUF : U ≤ F := by
    rintro _ ⟨x, rfl⟩
    rw [hΨ]
    refine Submodule.add_mem _ (FLE_mono K β (fun i => ?_) (hE₁F x.1.2)) ?_
    · simp only [Pi.smul_apply, smul_eq_mul]; exact Nat.mul_le_mul_right _ h₁
    · have := mul_mem_FLE K hB (hE₂F x.2.2)
      rw [← add_smul] at this
      exact FLE_mono K β (fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact Nat.mul_le_mul_right _ (by omega)) this
  set X := (J₁ ⊓ J₂).restrictScalars K ⊓ F
  have : FiniteDimensional K U := Submodule.finiteDimensional_of_le hUF
  have : FiniteDimensional K X := Submodule.finiteDimensional_of_le inf_le_right
  have hUX : U ⊓ X = ⊥ := eq_bot_iff.mpr fun y ⟨⟨x, hx⟩, hyJ, _⟩ => by
    subst hx; rw [hzero x hyJ, map_zero]; exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U X
  rw [hUX, finrank_bot, add_zero] at hsum
  have hle : finrank K ↥(U ⊔ X) ≤ finrank K F := Submodule.finrank_mono (sup_le hUF inf_le_right)
  have hU : finrank K U = hfun β D K J₁ t₁ + hfun β D K J₂ t₂ := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, hE₁d, hE₂d]
  have hX : hfun β D K (J₁ ⊓ J₂) t = finrank K F - finrank K X := rfl
  rw [hX, ← hU]
  omega

end Generic

/-! ### Cosets -/

universe u

variable {K : Type u} [Field K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}

theorem vanish_union (E₁ E₂ : Set (GPt K d₀ d₁ g₂ g₃)) :
    vanish (E₁ ∪ E₂) = vanish E₁ ⊓ vanish E₂ := by
  ext P
  simp only [Submodule.mem_inf, mem_vanish, Set.mem_union]
  exact ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun h g hg => hg.elim (h.1 g) (h.2 g)⟩

theorem mem_vanish_biUnion {ι : Type*} (s : Finset ι) (C : ι → Set (GPt K d₀ d₁ g₂ g₃))
    {P : MvPolynomial (Var d₀ d₁ m) K} : P ∈ vanish (⋃ a ∈ s, C a) ↔ ∀ a ∈ s, P ∈ vanish (C a) := by
  simp only [mem_vanish, Set.mem_iUnion]
  exact ⟨fun h a ha g hg => h g ⟨a, ha, hg⟩, fun h g ⟨a, ha, hg⟩ => h a ha g hg⟩

/-- A polynomial vanishing on a Zariski-closed `C₂` but not on `C₁ ⊄ C₂`. -/
theorem exists_sep_proj {C₁ C₂ : Set (GPt K d₀ d₁ g₂ g₃)} (hC₂ : IsZClosed C₂)
    (h : ¬ C₁ ⊆ C₂) : ∃ f ∈ vanish C₂, f ∉ vanish C₁ := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [← zeros_vanish hC₂]
  intro g hg P hP lam
  exact mem_vanish.mp (hcon P hP) g hg lam

section Cosets

variable [DecidableEq K]

/-- Distinct cosets of a subgroup are not nested. -/
theorem not_gtransl_subset {V : Set (GPt K d₀ d₁ g₂ g₃)} (hVs : IsSubgroupG V)
    {a b : GPt K d₀ d₁ g₂ g₃} (hab : a - b ∉ V) : ¬ gtransl a V ⊆ gtransl b V := by
  intro h
  have : a ∈ gtransl b V := h ⟨0, hVs.zero_mem, zero_add a⟩
  exact hab (mem_gtransl.mp this)

variable (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

/-- **Sums over cosets.** -/
theorem hfun_sum_cosets_ge [IsAlgClosed K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt K d₀ d₁ g₂ g₃))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun blk D K (vanish (gtransl a V)) t ≤
      hfun blk D K (vanish (⋃ a ∈ R, gtransl a V)) (t + c) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih fun x hx y hy hxy =>
      hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hpa : (vanish (gtransl a V)).IsPrime := vanish_gtransl_isPrime h2 hΔ hV hp a
    -- separators
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanish (gtransl a V) := fun b hb =>
      exists_sep_proj (isZClosed_gtransl h2 hΔ hV b)
        (hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
          (fun h => ha (h ▸ hb)))
    choose! f hfb hfa using hsep
    set B := ∏ b ∈ s, f b
    have hBs : B ∈ vanish (⋃ b ∈ s, gtransl b V) := by
      rw [mem_vanish_biUnion]
      intro b hb
      rw [show B = f b * ∏ x ∈ s.erase b, f x from (Finset.mul_prod_erase s f hb).symm]
      exact Ideal.mul_mem_right _ _ (hfb b hb)
    have hBa : B ∉ vanish (gtransl a V) := by
      intro h
      obtain ⟨b, hb, hfb'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpa)).mp h
      exact hfa b hb hfb'
    have hnzd : ∀ x, B * x ∈ vanish (gtransl a V) → x ∈ vanish (gtransl a V) := fun x hx =>
      (hpa.mem_or_mem hx).resolve_left hBa
    have hBdeg := mem_FLE_totalDegree blk D K hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : (⋃ x ∈ insert a s, gtransl x V) = (⋃ b ∈ s, gtransl b V) ∪ gtransl a V := by
      rw [Finset.set_biUnion_insert, Set.union_comm]
    have h1 := hfun_inter_ge blk D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, vanish_union, Finset.sum_insert ha]
    have := hc t
    omega

/-- **Projective `hfun_cosets_ge`**: `#R · H(I(V); t) ≤ 2^m · H(I(⋃_{a ∈ R} (V + a)); 2t + c)`. -/
theorem hfun_cosets_ge_proj [IsAlgClosed K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPt K d₀ d₁ g₂ g₃))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, R.card * hfun blk D K (vanish V) t ≤
      2 ^ m * hfun blk D K (vanish (⋃ a ∈ R, gtransl a V)) (2 * t + c) := by
  obtain ⟨c, hc⟩ := hfun_sum_cosets_ge h2 hΔ D hD hV hp R hdist
  refine ⟨c, fun t => ?_⟩
  calc R.card * hfun blk D K (vanish V) t = ∑ _a ∈ R, hfun blk D K (vanish V) t := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ R, 2 ^ m * hfun blk D K (vanish (gtransl a V)) (2 * t) :=
        Finset.sum_le_sum fun a _ => hfun_le_transl h2 hΔ D V a t
    _ = 2 ^ m * ∑ a ∈ R, hfun blk D K (vanish (gtransl a V)) (2 * t) := by
        rw [Finset.mul_sum]
    _ ≤ 2 ^ m * hfun blk D K (vanish (⋃ a ∈ R, gtransl a V)) (2 * t + c) :=
        Nat.mul_le_mul_left _ (hc (2 * t))

/-- **Cosets of a subgroup**: `#R · H(I(V); t) ≤ 2^m · H(I(⋃_{a ∈ R} (V + a)); 2t + c)` when the
cosets `V + a` (`a ∈ R`) are distinct. -/
theorem hfun_cosets_ge_subgroup [IsAlgClosed K] (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPt K d₀ d₁ g₂ g₃)} (hVs : IsSubgroupG V) (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (R : Finset (GPt K d₀ d₁ g₂ g₃))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ V) :
    ∃ c : ℕ, ∀ t, R.card * hfun blk D K (vanish V) t ≤
      2 ^ m * hfun blk D K (vanish (⋃ a ∈ R, gtransl a V)) (2 * t + c) :=
  hfun_cosets_ge_proj h2 hΔ D hD hV hp R fun a ha b hb hab =>
    not_gtransl_subset hVs (hdist a ha b hb hab)

end Cosets

end LSG.ME
