import Mathlib
import LSG.MEV.Transl
import StrongSix.M2.DimsData

/-!
# Hilbert functions of translates on the `E^♮` model

Translations triple `E^♮` block degrees, so (as in `LSG.ME.TranslHF`, factor `2` there):

* **`hfun_le_transl`**: `hfun (vanish E) t ≤ 8^m · hfun (vanish (E + g)) (3t)`. Proof:
  `P ↦ (τ (−g) c P mod I(E + g))_c` (all `8^m` law choices) is injective modulo `I(E)` on
  `FLE(tD)` and lands in `FLE(3tD)`.
* `HasData.comp_mul`: if `f` has data `(b, d)`, then `t ↦ f (c t)` (`c ≥ 1`) has data `(b, cᵇ d)`
  (generalizing `LSG.ME.HasData.comp_two`).
* **`hdim_vanish_gtransl`**: `(hdata (vanish (E + g))).1 = (hdata (vanish E)).1` for `E ≠ ∅`.
-/

open MvPolynomial Module LSG.Elliptic
open LSG.ME (g2L g3L Blk)
open StrongSix.M2 (FLE hfun hdata HasData hdata_spec finrank_comap_subtype)

namespace LSG.MEV

/-! ### Data of `t ↦ f (c t)` -/

section Mul

open StrongSix.M2 (Δ)

/-- `T_c f (s) = f (s) + f (s + 1) + ⋯ + f (s + c − 1)`. -/
def Tc (c : ℕ) (f : ℕ → ℤ) : ℕ → ℤ := fun s => ∑ i ∈ Finset.range c, f (s + i)

theorem Δ_comp_mul (c : ℕ) (f : ℕ → ℤ) :
    Δ (fun t => f (c * t)) = fun t => Δ (Tc c f) (c * t) := by
  funext t
  simp only [fwdDiff, Tc]
  have h1 : ∑ i ∈ Finset.range c, f (c * t + 1 + i) = ∑ i ∈ Finset.range c, f (c * t + (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
  rw [h1]
  have e1 := Finset.sum_range_succ' (fun i => f (c * t + i)) c
  have e2 := Finset.sum_range_succ (fun i => f (c * t + i)) c
  simp only [add_zero] at e1 e2
  rw [show c * (t + 1) = c * t + c by ring]
  linear_combination e1 - e2

theorem Δ_Tc_comm (c : ℕ) : Function.Commute Δ (Tc c) := fun f => by
  funext s
  simp only [fwdDiff, Tc, Function.comp_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show s + 1 + i = s + i + 1 by ring]

theorem iter_Δ_comp_mul (c n : ℕ) : ∀ f : ℕ → ℤ,
    Δ^[n] (fun t => f (c * t)) = fun t => ((Δ ∘ Tc c)^[n] f) (c * t) := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [Function.iterate_succ_apply, Δ_comp_mul, ih, Function.iterate_succ_apply]
    rfl

theorem Tc_iter_eventually (c : ℕ) {u : ℕ → ℤ} {d : ℤ} (hu : ∀ᶠ k in Filter.atTop, u k = d)
    (n : ℕ) : ∀ᶠ k in Filter.atTop, ((Tc c)^[n] u) k = (c : ℤ) ^ n * d := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp ih
    refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
    rw [Function.iterate_succ_apply']
    simp only [Tc]
    rw [Finset.sum_congr rfl fun i _ => hk0 (k + i) (by omega), Finset.sum_const,
      Finset.card_range, pow_succ]
    simp only [nsmul_eq_mul]
    ring

/-- **Multiplying the variable by `c ≥ 1`** keeps the dimension. -/
theorem HasData.comp_mul {c : ℕ} (hc : 1 ≤ c) {f : ℕ → ℤ} {b : ℕ} {d : ℤ} (h : HasData f b d) :
    HasData (fun t => f (c * t)) b ((c : ℤ) ^ b * d) := by
  refine ⟨mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by omega : c ≠ 0))) h.1, ?_⟩
  rw [iter_Δ_comp_mul, (Δ_Tc_comm c).comp_iterate, Function.comp_apply]
  rw [show Δ^[b] ((Tc c)^[b] f) = (Tc c)^[b] (Δ^[b] f) from
    ((Δ_Tc_comm c).iterate_iterate b b) f]
  have h2 : Filter.Tendsto (fun t : ℕ => c * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun a => ⟨a, fun t ht => le_trans ht
      (Nat.le_mul_of_pos_left t hc)⟩
  exact h2.eventually (Tc_iter_eventually c h.2 b)

/-- If `0 ≤ f t ≤ C · g (c t)` eventually (`c ≥ 1`), then `dim f ≤ dim g`. -/
theorem HasData.le_of_le_comp_mul {c : ℕ} (hc : 1 ≤ c) {f g : ℕ → ℤ} {a b : ℕ} {e d C : ℤ}
    (hC : C ≠ 0) (hf : HasData f a e) (hg : HasData g b d)
    (hle : ∀ᶠ t in Filter.atTop, f t ≤ C * g (c * t)) (hnn : ∀ᶠ t in Filter.atTop, 0 ≤ f t) :
    a ≤ b := by
  have h := StrongSix.M2.HasData.smul (HasData.comp_mul hc hg) hC
  rcases StrongSix.M2.HasData.compare hf h hle hnn with h' | ⟨h', -⟩ <;> omega

end Mul

/-! ### The Hilbert-function comparison -/

variable {d₀ d₁ m : ℕ} {Ls : Fin m → PeriodPair}

theorem card_LC_fun : Fintype.card (Fin m → LC) = 8 ^ m := by
  simp [Fintype.card_fun, Fintype.card_prod]

set_option maxSynthPendingDepth 10 in
/-- **Hilbert functions of translates**, with constant loss `8^m` and `t ↦ 3t`. -/
theorem hfun_le_transl (D : Blk m → ℕ) (E : Set (GPtV d₀ d₁ Ls)) (g : GPtV d₀ d₁ Ls) (t : ℕ) :
    hfun blk D ℂ (vanish E) t ≤ 8 ^ m * hfun blk D ℂ (vanish (gtransl g E)) (3 * t) := by
  set F₁ := FLE ℂ blk (t • D)
  set F₂ := FLE ℂ blk ((3 * t) • D)
  set E' := gtransl g E
  set N : Submodule ℂ F₂ := ((vanish E').restrictScalars ℂ).comap F₂.subtype
  have hτ : ∀ c, ∀ P ∈ F₁, τ Ls (-g) c P ∈ F₂ := fun c P hP =>
    LSG.ME.fle_le (transl_mem_FLE (-g) c hP) (tplE_le D t)
  let φ : (Fin m → LC) → (F₁ →ₗ[ℂ] F₂ ⧸ N) := fun c =>
    N.mkQ ∘ₗ ((τ Ls (-g) c).toLinearMap.restrict (hτ c))
  let Ψ : F₁ →ₗ[ℂ] ((Fin m → LC) → F₂ ⧸ N) := LinearMap.pi φ
  have hker : LinearMap.ker Ψ ≤ ((vanish E).restrictScalars ℂ).comap F₁.subtype := by
    intro x hx
    have hc : ∀ c, τ Ls (-g) c (x : MvPolynomial (Var d₀ d₁ m) ℂ) ∈ vanish E' := by
      intro c
      have := congrFun (LinearMap.mem_ker.mp hx) c
      simp only [Ψ, φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    refine mem_vanish.mpr fun e he ν => ?_
    have hh : e + g ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨c, hgood⟩ := exists_good (e + g) (-g)
    obtain ⟨μ, hμ⟩ := eval_transl_good hgood
    obtain ⟨lam, hlam⟩ := exists_cube_mul μ ν
    have := mem_vanish.mp (hc c) (e + g) hh lam
    rw [hμ, hlam, add_neg_cancel_right] at this
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 : finrank ℂ (LinearMap.range Ψ) ≤ finrank ℂ ((Fin m → LC) → F₂ ⧸ N) :=
    Submodule.finrank_le _
  have e3 : finrank ℂ ((Fin m → LC) → F₂ ⧸ N) = 8 ^ m * finrank ℂ (F₂ ⧸ N) := by
    have hfr := Module.finrank_pi_fintype ℂ (ι := Fin m → LC) (M := fun _ => ↥F₂ ⧸ N)
    rw [hfr, Finset.sum_const, Finset.card_univ, card_LC_fun, smul_eq_mul]
  have e4 : finrank ℂ (F₂ ⧸ N) = hfun blk D ℂ (vanish E') (3 * t) := by
    have := Submodule.finrank_quotient_add_finrank N
    rw [finrank_comap_subtype, inf_comm] at this
    change finrank ℂ (F₂ ⧸ N) = finrank ℂ F₂ - finrank ℂ ↥((vanish E').restrictScalars ℂ ⊓ F₂)
    omega
  have e5 : finrank ℂ (LinearMap.ker Ψ) ≤ finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := by
    have := Submodule.finrank_mono hker
    rwa [finrank_comap_subtype, inf_comm] at this
  have e6 : hfun blk D ℂ (vanish E) t =
      finrank ℂ F₁ - finrank ℂ ↥((vanish E).restrictScalars ℂ ⊓ F₁) := rfl
  rw [e6, ← e4]
  omega

/-- **Translates have the same Hilbert dimension.** -/
theorem hdim_vanish_gtransl (D : Blk m → ℕ) {E : Set (GPtV d₀ d₁ Ls)} (hE : E.Nonempty)
    (g : GPtV d₀ d₁ Ls) :
    (hdata blk D ℂ (vanish (gtransl g E))).1 = (hdata blk D ℂ (vanish E)).1 := by
  have hE' : (gtransl g E).Nonempty := hE.image _
  have hf := hdata_spec blk D ℂ (vanish_ne_top hE)
  have hg := hdata_spec blk D ℂ (vanish_ne_top hE')
  have hC : ((8 : ℤ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have le1 := HasData.le_of_le_comp_mul (by norm_num : 1 ≤ 3) hC hf hg
    (Filter.Eventually.of_forall fun t => by exact_mod_cast hfun_le_transl D E g t)
    (Filter.Eventually.of_forall fun t => by positivity)
  have le2 := HasData.le_of_le_comp_mul (by norm_num : 1 ≤ 3) hC hg hf
    (Filter.Eventually.of_forall fun t => by
      have := hfun_le_transl D (gtransl g E) (-g) t
      rw [gtransl_gtransl_neg] at this
      exact_mod_cast this)
    (Filter.Eventually.of_forall fun t => by positivity)
  omega

end LSG.MEV
