import Mathlib
import LSG.MEV.TranslHF
import LSG.MEV.SubgroupCompV
import LSG.ME.WustCoset

/-!
# Hilbert functions of finite unions of cosets in `G̃` (projective form)

Port of the coset part of `LSG.ME.WustCoset` to the vector-extension model. The generic
"two ideals and a non-zero-divisor" bound `LSG.ME.hfun_inter_ge` is reused by import; the
translation loss is `8^m` with `t ↦ 3t` (`hfun_le_transl`, eight laws of bidegree `(3, 3)`).

* `vanish_unionV`, `mem_vanish_biUnionV`, `exists_sep_projV`, `not_gtransl_subsetV`.
* **`hfun_sum_cosets_geV`**: for irreducible Zariski-closed `V` and pairwise non-nested translates
  `V + a` (`a ∈ R`): `Σ_{a ∈ R} H(I(V + a); t) ≤ H(I(⋃ (V + a)); t + c)`.
* **`hfun_cosets_ge_projV`**: `#R · H(I(V); t) ≤ 8^m · H(I(⋃_{a ∈ R} (V + a)); 3t + c)`.
* **`hfun_cosets_ge_subgroupV`**: the same for distinct cosets of a subgroup `V`.
-/

open MvPolynomial Module Submodule
open LSG.ME (Blk)
open StrongSix.M2 (FLE hfun mem_FLE_totalDegree)

namespace LSG.MEV

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem vanish_unionV (E₁ E₂ : Set (GPtV d₀ d₁ Ls)) :
    vanish (E₁ ∪ E₂) = vanish E₁ ⊓ vanish E₂ := by
  ext P
  simp only [Submodule.mem_inf, mem_vanish, Set.mem_union]
  exact ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun h g hg => hg.elim (h.1 g) (h.2 g)⟩

theorem mem_vanish_biUnionV {ι : Type*} (s : Finset ι) (C : ι → Set (GPtV d₀ d₁ Ls))
    {P : MvPolynomial (Var d₀ d₁ m) ℂ} : P ∈ vanish (⋃ a ∈ s, C a) ↔ ∀ a ∈ s, P ∈ vanish (C a) := by
  simp only [mem_vanish, Set.mem_iUnion]
  exact ⟨fun h a ha g hg => h g ⟨a, ha, hg⟩, fun h g ⟨a, ha, hg⟩ => h a ha g hg⟩

/-- A polynomial vanishing on a Zariski-closed `C₂` but not on `C₁ ⊄ C₂`. -/
theorem exists_sep_projV {C₁ C₂ : Set (GPtV d₀ d₁ Ls)} (hC₂ : IsZClosed C₂)
    (h : ¬ C₁ ⊆ C₂) : ∃ f ∈ vanish C₂, f ∉ vanish C₁ := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [← zeros_vanish hC₂]
  intro g hg P hP lam
  exact mem_vanish.mp (hcon P hP) g hg lam

/-- Distinct cosets of a subgroup are not nested. -/
theorem not_gtransl_subsetV {V : Set (GPtV d₀ d₁ Ls)} (hVs : IsSubgroupG V)
    {a b : GPtV d₀ d₁ Ls} (hab : a - b ∉ V) : ¬ gtransl a V ⊆ gtransl b V := by
  intro h
  have : a ∈ gtransl b V := h ⟨0, hVs.zero_mem, zero_add a⟩
  exact hab (mem_gtransl.mp this)

/-- **Sums over cosets.** -/
theorem hfun_sum_cosets_geV (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, ∑ a ∈ R, hfun blk D ℂ (vanish (gtransl a V)) t ≤
      hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a V)) (t + c) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih fun x hx y hy hxy =>
      hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hpa : (vanish (gtransl a V)).IsPrime := vanish_gtransl_isPrime hV hp a
    have hsep : ∀ b ∈ s, ∃ f ∈ vanish (gtransl b V), f ∉ vanish (gtransl a V) := fun b hb =>
      exists_sep_projV (isZClosed_gtransl hV b)
        (hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
          (fun h => ha (h ▸ hb)))
    choose! f hfb hfa using hsep
    set B := ∏ b ∈ s, f b
    have hBs : B ∈ vanish (⋃ b ∈ s, gtransl b V) := by
      rw [mem_vanish_biUnionV]
      intro b hb
      rw [show B = f b * ∏ x ∈ s.erase b, f x from (Finset.mul_prod_erase s f hb).symm]
      exact Ideal.mul_mem_right _ _ (hfb b hb)
    have hBa : B ∉ vanish (gtransl a V) := by
      intro h
      obtain ⟨b, hb, hfb'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hpa)).mp h
      exact hfa b hb hfb'
    have hnzd : ∀ x, B * x ∈ vanish (gtransl a V) → x ∈ vanish (gtransl a V) := fun x hx =>
      (hpa.mem_or_mem hx).resolve_left hBa
    have hBdeg := mem_FLE_totalDegree blk D ℂ hD B
    refine ⟨c + B.totalDegree, fun t => ?_⟩
    have hU : (⋃ x ∈ insert a s, gtransl x V) = (⋃ b ∈ s, gtransl b V) ∪ gtransl a V := by
      rw [Finset.set_biUnion_insert, Set.union_comm]
    have h1 := LSG.ME.hfun_inter_ge blk D hBdeg hBs hnzd (t₁ := t + c) (t₂ := t)
      (t := t + (c + B.totalDegree)) (by omega) (by omega)
    rw [hU, vanish_unionV, Finset.sum_insert ha]
    have := hc t
    omega

/-- **Projective coset bound**: `#R · H(I(V); t) ≤ 8^m · H(I(⋃_{a ∈ R} (V + a)); 3t + c)`. -/
theorem hfun_cosets_ge_projV (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPtV d₀ d₁ Ls)} (hV : IsZClosed V) (hp : (vanish V).IsPrime)
    (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ¬ gtransl a V ⊆ gtransl b V) :
    ∃ c : ℕ, ∀ t, R.card * hfun blk D ℂ (vanish V) t ≤
      8 ^ m * hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a V)) (3 * t + c) := by
  obtain ⟨c, hc⟩ := hfun_sum_cosets_geV D hD hV hp R hdist
  refine ⟨c, fun t => ?_⟩
  calc R.card * hfun blk D ℂ (vanish V) t = ∑ _a ∈ R, hfun blk D ℂ (vanish V) t := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ R, 8 ^ m * hfun blk D ℂ (vanish (gtransl a V)) (3 * t) :=
        Finset.sum_le_sum fun a _ => hfun_le_transl D V a t
    _ = 8 ^ m * ∑ a ∈ R, hfun blk D ℂ (vanish (gtransl a V)) (3 * t) := by
        rw [Finset.mul_sum]
    _ ≤ 8 ^ m * hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a V)) (3 * t + c) :=
        Nat.mul_le_mul_left _ (hc (3 * t))

/-- **Cosets of a subgroup**: `#R · H(I(V); t) ≤ 8^m · H(I(⋃_{a ∈ R} (V + a)); 3t + c)` when the
cosets `V + a` (`a ∈ R`) are distinct. -/
theorem hfun_cosets_ge_subgroupV (D : Blk m → ℕ) (hD : ∀ i, 1 ≤ D i)
    {V : Set (GPtV d₀ d₁ Ls)} (hVs : IsSubgroupG V) (hV : IsZClosed V)
    (hp : (vanish V).IsPrime) (R : Finset (GPtV d₀ d₁ Ls))
    (hdist : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → a - b ∉ V) :
    ∃ c : ℕ, ∀ t, R.card * hfun blk D ℂ (vanish V) t ≤
      8 ^ m * hfun blk D ℂ (vanish (⋃ a ∈ R, gtransl a V)) (3 * t + c) :=
  hfun_cosets_ge_projV D hD hV hp R fun a ha b hb hab =>
    not_gtransl_subsetV hVs (hdist a ha b hb hab)

end LSG.MEV
