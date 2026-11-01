import Mathlib
import LSG.ME.Transl
import StrongSix.M2.DimsData

/-!
# Hilbert functions of translates (STAGE2 §3)

Translations double elliptic block degrees, so `hfun (vanish (E + g))` and `hfun (vanish E)` are
not equal as in StrongSix's `hfun_vanish_transl`. What is true and suffices:

* **`hfun_le_transl`**: `hfun (vanish E) t ≤ 2^m · hfun (vanish (E + g)) (2t)` (`K` algebraically
  closed). Proof: `P ↦ (τ (−g) c P mod I(E + g))_c` (all `2^m` law choices) is injective modulo
  `I(E)` on `FLE(tD)` and lands in `FLE(2tD)`.
* `HasData.comp_two`: if `f` has data `(b, d)`, then `t ↦ f (2t)` has data `(b, 2^b d)`.
* **`hdim_vanish_gtransl`**: `(hdata (vanish (E + g))).1 = (hdata (vanish E)).1` for `E ≠ ∅`.
-/

universe u

open MvPolynomial Module LSG.Elliptic
open StrongSix.M2 (FLE hfun hdata HasData hdata_spec finrank_comap_subtype)

namespace LSG.ME

/-! ### Data of `t ↦ f (2t)` -/

section Doubling

open StrongSix.M2 (Δ)

/-- `T f (s) = f (s + 1) + f s` (so that `Δ (f ∘ 2·) = (Δ T f) ∘ 2·`). -/
def Tdbl (f : ℕ → ℤ) : ℕ → ℤ := fun s => f (s + 1) + f s

theorem Δ_comp_two (f : ℕ → ℤ) : Δ (fun t => f (2 * t)) = fun t => Δ (Tdbl f) (2 * t) := by
  funext t
  simp only [fwdDiff, Tdbl]
  rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]
  ring

theorem Δ_Tdbl_comm : Function.Commute Δ Tdbl := fun f => by
  funext s
  simp only [fwdDiff, Tdbl]
  ring

theorem iter_Δ_comp_two (n : ℕ) : ∀ f : ℕ → ℤ,
    Δ^[n] (fun t => f (2 * t)) = fun t => ((Δ ∘ Tdbl)^[n] f) (2 * t) := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    rw [Function.iterate_succ_apply, Δ_comp_two, ih, Function.iterate_succ_apply]
    rfl

theorem Tdbl_iter_eventually {u : ℕ → ℤ} {d : ℤ} (hu : ∀ᶠ k in Filter.atTop, u k = d) (n : ℕ) :
    ∀ᶠ k in Filter.atTop, (Tdbl^[n] u) k = 2 ^ n * d := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp ih
    refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
    rw [Function.iterate_succ_apply']
    simp only [Tdbl]
    rw [hk0 k hk, hk0 (k + 1) (by omega), pow_succ]
    ring

/-- **Doubling the variable** keeps the dimension. -/
theorem HasData.comp_two {f : ℕ → ℤ} {b : ℕ} {d : ℤ} (h : HasData f b d) :
    HasData (fun t => f (2 * t)) b (2 ^ b * d) := by
  refine ⟨mul_ne_zero (pow_ne_zero _ two_ne_zero) h.1, ?_⟩
  rw [iter_Δ_comp_two, Δ_Tdbl_comm.comp_iterate, Function.comp_apply]
  rw [show Δ^[b] (Tdbl^[b] f) = Tdbl^[b] (Δ^[b] f) from (Δ_Tdbl_comm.iterate_iterate b b) f]
  have h2 : Filter.Tendsto (fun t : ℕ => 2 * t) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun a => ⟨a, fun t ht => by omega⟩
  exact h2.eventually (Tdbl_iter_eventually h.2 b)

/-- If `0 ≤ f t ≤ C · g (2t)` eventually, then `dim f ≤ dim g`. -/
theorem HasData.le_of_le_comp_two {f g : ℕ → ℤ} {a b : ℕ} {c d C : ℤ} (hC : C ≠ 0)
    (hf : HasData f a c) (hg : HasData g b d) (hle : ∀ᶠ t in Filter.atTop, f t ≤ C * g (2 * t))
    (hnn : ∀ᶠ t in Filter.atTop, 0 ≤ f t) : a ≤ b := by
  have h := StrongSix.M2.HasData.smul (HasData.comp_two hg) hC
  rcases StrongSix.M2.HasData.compare hf h hle hnn with h' | ⟨h', -⟩ <;> omega

end Doubling

/-! ### The Hilbert-function comparison -/

variable {K : Type u} [Field K] [DecidableEq K] {d₀ d₁ m : ℕ} {g₂ g₃ : Fin m → K}
  (h2 : (2 : K) ≠ 0) (hΔ : ∀ k, g₂ k ^ 3 - 27 * g₃ k ^ 2 ≠ 0)
include h2 hΔ

set_option maxSynthPendingDepth 10 in
/-- **Hilbert functions of translates**, with constant loss `2^m` and `t ↦ 2t`. -/
theorem hfun_le_transl [IsAlgClosed K] (D : Blk m → ℕ) (E : Set (GPt K d₀ d₁ g₂ g₃))
    (g : GPt K d₀ d₁ g₂ g₃) (t : ℕ) :
    hfun blk D K (vanish E) t ≤ 2 ^ m * hfun blk D K (vanish (gtransl g E)) (2 * t) := by
  set F₁ := FLE K blk (t • D)
  set F₂ := FLE K blk ((2 * t) • D)
  set E' := gtransl g E
  set N : Submodule K F₂ := ((vanish E').restrictScalars K).comap F₂.subtype
  have hτ : ∀ c, ∀ P ∈ F₁, τ g₂ g₃ (-g) c P ∈ F₂ := fun c P hP =>
    fle_le (transl_mem_FLE (-g) c hP) (dblE_le D t)
  let φ : (Fin m → Fin 2) → (F₁ →ₗ[K] F₂ ⧸ N) := fun c =>
    N.mkQ ∘ₗ ((τ g₂ g₃ (-g) c).toLinearMap.restrict (hτ c))
  let Ψ : F₁ →ₗ[K] ((Fin m → Fin 2) → F₂ ⧸ N) := LinearMap.pi φ
  -- the kernel
  have hker : LinearMap.ker Ψ ≤ ((vanish E).restrictScalars K).comap F₁.subtype := by
    intro x hx
    have hc : ∀ c, τ g₂ g₃ (-g) c (x : MvPolynomial (Var d₀ d₁ m) K) ∈ vanish E' := by
      intro c
      have := congrFun (LinearMap.mem_ker.mp hx) c
      simp only [Ψ, φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    refine mem_vanish.mpr fun e he ν => ?_
    have hh : e + g ∈ E' := ⟨e, he, rfl⟩
    obtain ⟨c, hgood⟩ := exists_good h2 hΔ (e + g) (-g)
    obtain ⟨μ, hμ⟩ := eval_transl_good h2 hΔ hgood
    obtain ⟨lam, hlam⟩ := exists_sq_mul μ ν
    have := mem_vanish.mp (hc c) (e + g) hh lam
    rw [hμ, hlam, add_neg_cancel_right] at this
    exact this
  -- dimension count
  have e1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have e2 : finrank K (LinearMap.range Ψ) ≤ finrank K ((Fin m → Fin 2) → F₂ ⧸ N) :=
    Submodule.finrank_le _
  have e3 : finrank K ((Fin m → Fin 2) → F₂ ⧸ N) = 2 ^ m * finrank K (F₂ ⧸ N) := by
    have hfr := Module.finrank_pi_fintype K (ι := Fin m → Fin 2) (M := fun _ => ↥F₂ ⧸ N)
    rw [hfr, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
  have e4 : finrank K (F₂ ⧸ N) = hfun blk D K (vanish E') (2 * t) := by
    have := Submodule.finrank_quotient_add_finrank N
    rw [finrank_comap_subtype, inf_comm] at this
    change finrank K (F₂ ⧸ N) = finrank K F₂ - finrank K ↥((vanish E').restrictScalars K ⊓ F₂)
    omega
  have e5 : finrank K (LinearMap.ker Ψ) ≤ finrank K ↥((vanish E).restrictScalars K ⊓ F₁) := by
    have := Submodule.finrank_mono hker
    rwa [finrank_comap_subtype, inf_comm] at this
  have e6 : hfun blk D K (vanish E) t = finrank K F₁ - finrank K ↥((vanish E).restrictScalars K ⊓
      F₁) :=
    rfl
  rw [e6, ← e4]
  omega

/-- **Translates have the same Hilbert dimension.** -/
theorem hdim_vanish_gtransl [IsAlgClosed K] (D : Blk m → ℕ) {E : Set (GPt K d₀ d₁ g₂ g₃)}
    (hE : E.Nonempty) (g : GPt K d₀ d₁ g₂ g₃) :
    (hdata blk D K (vanish (gtransl g E))).1 = (hdata blk D K (vanish E)).1 := by
  have hE' : (gtransl g E).Nonempty := hE.image _
  have hf := hdata_spec blk D K (vanish_ne_top hE)
  have hg := hdata_spec blk D K (vanish_ne_top hE')
  have hC : ((2 : ℤ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
  have le1 := HasData.le_of_le_comp_two hC hf hg
    (Filter.Eventually.of_forall fun t => by exact_mod_cast hfun_le_transl h2 hΔ D E g t)
    (Filter.Eventually.of_forall fun t => by positivity)
  have le2 := HasData.le_of_le_comp_two hC hg hf
    (Filter.Eventually.of_forall fun t => by
      have := hfun_le_transl h2 hΔ D (gtransl g E) (-g) t
      rw [gtransl_gtransl_neg] at this
      exact_mod_cast this)
    (Filter.Eventually.of_forall fun t => by positivity)
  omega

end LSG.ME
