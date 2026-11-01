/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Sec7
import LSG.ME.MainAb
import LSG.W88.Thm11Kappa

/-!
# W88 Theorem 4.1 for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, unconditionally

* `theorem41Abelian : Theorem41Abelian` — Waldschmidt's subgroup theorem with period term
  (W88, Thm 4.1) under hypothesis (NR), statement in `LSG/W88/Statement.lean`. It is W88 §7
  (`theorem41Abelian_of`) applied to Philippon's multiplicity estimate (`LSG.ME.multEstAb`).
* `thm11Kappa : MStarCopy.Thm11Kappa L d₁` — W88 §5d (Thm 1.1 with the κ-refined hypothesis) for
  `G_m^{d₁} × E`, verbatim the hypothesis `hW` of `lean_mstar` (`CM4E.Waldschmidt.Thm11Kappa`).
-/

namespace LSG.W88

/-- **Waldschmidt's subgroup theorem with period term (W88, Thm 4.1), under (NR), for
`G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`.** -/
theorem theorem41Abelian : Theorem41Abelian :=
  theorem41Abelian_of LSG.ME.multEstAb

/-- **W88 §5d for `G_m^{d₁} × E`** (the hypothesis `hW` of `lean_mstar`). -/
theorem thm11Kappa (L : PeriodPair) (d₁ : ℕ) : MStarCopy.Thm11Kappa L d₁ :=
  thm11Kappa_of_theorem41 theorem41Abelian L d₁

end LSG.W88
