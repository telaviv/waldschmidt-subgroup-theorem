/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.MEBV.ModelIG
import LSG.MEBV.StmtG

/-!
# Irreducibility of `zcl (exp t)` (M2.5 α; template `LSG.MEB.MainGrp`)

For a complex subspace `t ⊆ Lie G`, the Zariski closure of `exp t` is irreducible: **`vanish_expG_isPrime`**,
by the identity theorem on the connected space `t × ℂ^m` (the argument of `IGsem_isPrime`, restricted to `t`).
Corollary **`vanish_grp_isPrime`**: for obstruction data `O`, `I(O.grp)` is prime. This is ME's
`vanish_H0_isPrime`, so the field `grp_prime` is no longer an input of the assembly.
-/

open MvPolynomial Filter Topology

namespace LSG.MEBV

variable {m d₀ d₁ : ℕ} {B : Fin m → VBlock}

/-- `I(exp t)` through the lift. -/
theorem mem_vanish_expG_iff (t : Submodule ℂ (Tan d₀ d₁ B)) {P : MvPolynomial (Var d₀ d₁ B) ℂ} :
    P ∈ vanish (expG d₀ d₁ B '' (t : Set (Tan d₀ d₁ B))) ↔
      ∀ u ∈ t, ∀ μ : Fin m → ℂ, eval (liftZ u μ) P = 0 := by
  constructor
  · intro hP u hu μ
    obtain ⟨lam₀, h⟩ := coords_expG u
    rw [liftZ_eq_coordsZ h]
    exact eval_coordsZ_eq_zero (fun lam => mem_vanish.mp hP _ ⟨u, hu, rfl⟩ lam) _
  · intro h
    refine mem_vanish.mpr ?_
    rintro _ ⟨u, hu, rfl⟩ lam
    obtain ⟨lam₀, h0⟩ := coords_expG u
    have : coords (expG d₀ d₁ B u) lam = liftZ u fun k => (lam k : ℂ) / lam₀ k := by
      rw [liftZ_eq_coordsZ h0, coords_eq_coordsZ]
      congr 1
      funext k
      field_simp
    rw [this]
    exact h u hu _

/-- **`zcl (exp t)` is irreducible.** -/
theorem vanish_expG_isPrime (t : Submodule ℂ (Tan d₀ d₁ B)) :
    (vanish (expG d₀ d₁ B '' (t : Set (Tan d₀ d₁ B)))).IsPrime := by
  have han : ∀ (Q : MvPolynomial (Var d₀ d₁ B) ℂ) (q : ↥t × (Fin m → ℂ)),
      AnalyticAt ℂ (fun q : ↥t × (Fin m → ℂ) => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) Q) q := by
    intro Q q
    have hL : AnalyticAt ℂ (fun q : ↥t × (Fin m → ℂ) => ((q.1 : Tan d₀ d₁ B), q.2)) q :=
      (t.subtypeL.prodMap (ContinuousLinearMap.id ℂ (Fin m → ℂ))).analyticAt q
    exact (analyticAt_eval_liftZ Q ((q.1 : Tan d₀ d₁ B), q.2)).comp
      (f := fun q : ↥t × (Fin m → ℂ) => (((q.1 : Tan d₀ d₁ B), q.2) : LZ d₀ d₁ B)) hL
  refine ⟨fun htop => ?_, fun {P Q} hPQ => ?_⟩
  · have h1 : (1 : MvPolynomial (Var d₀ d₁ B) ℂ) ∈ vanish (expG d₀ d₁ B '' (t : Set _)) :=
      htop ▸ Submodule.mem_top
    have := (mem_vanish_expG_iff t).mp h1 0 t.zero_mem 0
    rw [map_one] at this
    exact one_ne_zero this
  have hfh : ∀ q : ↥t × (Fin m → ℂ), eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) P *
      eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) Q = 0 := fun q => by
    have := (mem_vanish_expG_iff t).mp hPQ q.1 q.1.2 q.2
    rwa [map_mul] at this
  by_cases hP : P ∈ vanish (expG d₀ d₁ B '' (t : Set _))
  · exact Or.inl hP
  right
  have : ∃ q : ↥t × (Fin m → ℂ), eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) P ≠ 0 := by
    by_contra hcon
    exact hP ((mem_vanish_expG_iff t).mpr fun u hu μ =>
      not_not.mp fun h => hcon ⟨(⟨u, hu⟩, μ), h⟩)
  obtain ⟨q₀, hq₀⟩ := this
  have hev : (fun q : ↥t × (Fin m → ℂ) => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) Q) =ᶠ[𝓝 q₀] 0 := by
    filter_upwards [(han P q₀).continuousAt.eventually_ne hq₀] with q hq
    exact (mul_eq_zero.mp (hfh q)).resolve_left hq
  have hanQ : AnalyticOnNhd ℂ
      (fun q : ↥t × (Fin m → ℂ) => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) Q) Set.univ :=
    fun q _ => han Q q
  have hpc : IsPreconnected (Set.univ : Set (↥t × (Fin m → ℂ))) :=
    (convex_univ (𝕜 := ℝ)).isPreconnected
  have hzero : Set.EqOn (fun q : ↥t × (Fin m → ℂ) => eval (liftZ (q.1 : Tan d₀ d₁ B) q.2) Q) 0
      Set.univ :=
    hanQ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc (Set.mem_univ q₀) hev
  refine (mem_vanish_expG_iff t).mpr fun u hu μ => ?_
  have := hzero (Set.mem_univ (⟨u, hu⟩, μ))
  simpa using this

/-- **`I(H⁰)` is prime** for obstruction data (`H⁰ = O.grp = zcl (exp T_{H⁰})`). -/
theorem vanish_grp_isPrime (O : ObstrDataGV d₀ d₁ B) : (vanish O.grp).IsPrime := by
  rw [O.grp_eq, vanish_zcl]
  exact vanish_expG_isPrime _

end LSG.MEBV
