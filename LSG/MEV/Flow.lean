import Mathlib
import LSG.MEV.FibreDefs
import LSG.ME.FormalExp

/-!
# Normalized flows of the invariant vector fields of `E^♮` (one block)

For a chart `a ∈ Fin 2` (`0 = V`, `1 = W`) and a direction `(ζ, β) = (2s, β)` of `Lie E^♮`,
`dvalB a s β P` is the homogeneous (degree `+2`) chart derivation on the cone coordinates
`(U, V, W, T₁, T₃)`: the abelian chart derivation `s · c2_a` times the chart form `L_a` on the base,
`L_a (β L_a² + 2s ρ_a)` on the chart fibre coordinate `T_a`, and the other fibre coordinate from
`δG = 0`. It preserves `G` exactly (`dvalB_G`) and `F` (`dvalB_F`).

* `IsBFlow a s β Y`: `Y` is normalized in chart `a` (`L_a(Y) = 1`) and `Y' = dvalB a s β (Y)`.
* **`eq_of_isBFlow`**: two flows (same chart and direction) with the same initial value agree.
* `IsBFlow.base`, `IsBFlow.fib`: the base flow is the abelian chart flow `Y_j' = s c2_a(Y)_j`; the
  chart fibre coordinate moves by `T_a' = β + 2s ρ_a(Y)`.
-/

open LSG.Elliptic
open LSG.ME (c2)

namespace LSG.MEV

section Field

variable {T : Type*} [CommRing T]

/-- The index of the chart form in `Fin 5`. -/
def bi (a : Fin 2) : Fin 5 := ![1, 2] a

/-- The index of the chart fibre coordinate: `V ↦ T₃`, `W ↦ T₁`. -/
def ti (a : Fin 2) : Fin 5 := ![4, 3] a

theorem mult_Pe (a : Fin 2) (P : Fin 5 → T) : mult a (Pe P) = P (bi a) := by
  fin_cases a <;> rfl

theorem tcoord_eq (a : Fin 2) (P : Fin 5 → T) : tcoord a P = P (ti a) := by
  fin_cases a <;> rfl

/-- **The chart derivation** (degree `+2`) of `E^♮` in chart `a`, direction `(2s, β)`. -/
def dvalB (a : Fin 2) (g₂ g₃ s β : T) (P : Fin 5 → T) : Fin 5 → T :=
  ![![P 1 * (s * c2 1 g₂ g₃ (Pe P) 0), P 1 * (s * c2 1 g₂ g₃ (Pe P) 1),
      P 1 * (s * c2 1 g₂ g₃ (Pe P) 2),
      s * c2 1 g₂ g₃ (Pe P) 2 * P 4 + P 2 * (β * P 1 ^ 2 + 2 * s * rhoh 0 g₂ g₃ (Pe P)) +
        4 * P 0 * (s * c2 1 g₂ g₃ (Pe P) 0),
      P 1 * (β * P 1 ^ 2 + 2 * s * rhoh 0 g₂ g₃ (Pe P))],
    ![P 2 * (s * c2 2 g₂ g₃ (Pe P) 0), P 2 * (s * c2 2 g₂ g₃ (Pe P) 1),
      P 2 * (s * c2 2 g₂ g₃ (Pe P) 2), P 2 * (β * P 2 ^ 2 + 2 * s * rhoh 1 g₂ g₃ (Pe P)),
      s * c2 2 g₂ g₃ (Pe P) 1 * P 3 + P 1 * (β * P 2 ^ 2 + 2 * s * rhoh 1 g₂ g₃ (Pe P)) -
        4 * P 0 * (s * c2 2 g₂ g₃ (Pe P) 0)]] a

theorem dvalB_map {T' : Type*} [CommRing T'] (f : T →+* T') (a : Fin 2) (g₂ g₃ s β : T)
    (P : Fin 5 → T) (l : Fin 5) :
    f (dvalB a g₂ g₃ s β P l) = dvalB a (f g₂) (f g₃) (f s) (f β) (f ∘ P) l := by
  fin_cases a <;> fin_cases l <;> simp [dvalB, c2, rhoh, Pe, map_ofNat]

/-- The chart derivation is tangent to `G = 0` (exactly). -/
theorem dvalB_G (a : Fin 2) (g₂ g₃ s β : T) (P : Fin 5 → T) :
    dvalB a g₂ g₃ s β P 2 * P 4 + P 2 * dvalB a g₂ g₃ s β P 4 - dvalB a g₂ g₃ s β P 1 * P 3 -
      P 1 * dvalB a g₂ g₃ s β P 3 + 4 * P 0 * dvalB a g₂ g₃ s β P 0 = 0 := by
  fin_cases a <;> simp [dvalB, c2, rhoh, Pe] <;> ring

/-- The chart derivation is tangent to `F = 0` (exactly). -/
theorem dvalB_F (a : Fin 2) (g₂ g₃ s β : T) (P : Fin 5 → T) :
    (2 * P 1 * P 2) * dvalB a g₂ g₃ s β P 1 + (P 1 ^ 2 + 2 * g₂ * P 0 * P 2 + 3 * g₃ * P 2 ^ 2) *
      dvalB a g₂ g₃ s β P 2 + (-12 * P 0 ^ 2 + g₂ * P 2 ^ 2) * dvalB a g₂ g₃ s β P 0 = 0 := by
  fin_cases a <;> simp [dvalB, c2, rhoh, Pe] <;> ring

end Field

section Flow

variable {K : Type*} [Field K] [CharZero K] {R : Type*} [CommRing R] [Algebra K R]

local notation "dz" => (PowerSeries.derivative (R := R))
local notation "alg" => algebraMap K (PowerSeries R)

variable (g₂ g₃ : K)

/-- `Y` is a **flow** of the invariant field `(2s, β)`, **normalized in chart `a`**. -/
structure IsBFlow (a : Fin 2) (s β : K) (Y : Fin 5 → PowerSeries R) : Prop where
  norm : Y (bi a) = 1
  ode : ∀ l, dz (Y l) = dvalB a (alg g₂) (alg g₃) (alg s) (alg β) Y l

variable {g₂ g₃}

/-- The chart derivation as a polynomial vector field. -/
noncomputable def dvalPoly (a : Fin 2) (s β : K) : Fin 5 → MvPolynomial (Fin 5) K :=
  fun l => dvalB a (MvPolynomial.C g₂) (MvPolynomial.C g₃) (MvPolynomial.C s) (MvPolynomial.C β)
    MvPolynomial.X l

theorem aeval_dvalPoly (a : Fin 2) (s β : K) (Γ : Fin 5 → PowerSeries R) (l : Fin 5) :
    MvPolynomial.aeval Γ (dvalPoly (g₂ := g₂) (g₃ := g₃) a s β l) =
      dvalB a (alg g₂) (alg g₃) (alg s) (alg β) Γ l := by
  rw [dvalPoly, ← AlgHom.coe_toRingHom, dvalB_map]
  simp only [AlgHom.coe_toRingHom, MvPolynomial.aeval_C]
  congr 1
  funext i; simp

/-- **Uniqueness of flows.** -/
theorem eq_of_isBFlow {a : Fin 2} {s β : K} {Y Y' : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) (hY' : IsBFlow g₂ g₃ a s β Y')
    (h0 : ∀ l, PowerSeries.constantCoeff (Y l) = PowerSeries.constantCoeff (Y' l)) : Y = Y' := by
  have e1 := LSG.ME.eq_solve (K := K) (F := dvalPoly (g₂ := g₂) (g₃ := g₃) a s β)
    (x₀ := fun l => PowerSeries.constantCoeff (Y l)) (Γ := Y)
    (fun l => by rw [hY.ode, aeval_dvalPoly]) (fun l => rfl)
  have e2 := LSG.ME.eq_solve (K := K) (F := dvalPoly (g₂ := g₂) (g₃ := g₃) a s β)
    (x₀ := fun l => PowerSeries.constantCoeff (Y l)) (Γ := Y')
    (fun l => by rw [hY'.ode, aeval_dvalPoly]) (fun l => (h0 l).symm)
  rw [e1, e2]

theorem IsBFlow.norm' {a : Fin 2} {s β : K} {Y : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) : Y (bi a) = 1 := hY.norm

theorem IsBFlow.base {a : Fin 2} {s β : K} {Y : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) (j : Fin 3) :
    dz (Pe Y j) = alg s * c2 (biE a) (alg g₂) (alg g₃) (Pe Y) j := by
  have hn := hY.norm
  rw [Pe_apply, hY.ode]
  fin_cases a
  · have h1 : Y 1 = 1 := hn
    fin_cases j <;> simp [dvalB, h1]
  · have h2 : Y 2 = 1 := hn
    fin_cases j <;> simp [dvalB, h2]

theorem IsBFlow.fib {a : Fin 2} {s β : K} {Y : Fin 5 → PowerSeries R}
    (hY : IsBFlow g₂ g₃ a s β Y) :
    dz (tcoord a Y) = alg β + 2 * alg s * rhoh a (alg g₂) (alg g₃) (Pe Y) := by
  have hn := hY.norm
  rw [tcoord_eq, hY.ode]
  fin_cases a
  · have h1 : Y 1 = 1 := hn
    simp [dvalB, ti, h1]
  · have h2 : Y 2 = 1 := hn
    simp [dvalB, ti, h2]

end Flow

end LSG.MEV
