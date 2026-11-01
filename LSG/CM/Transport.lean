/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.Thm41Sub
import LSG.W88.Main
import LSG.CM.Coord

/-!
# Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B`, `B ⊂ E₁ × ⋯ × E_r` an abelian subvariety

`thm41Sub : Thm41Sub` (and the per-curve form `thm41SubAt_cm` for a power of one curve, e.g. a CM
curve), deduced from `LSG.W88.theorem41Abelian` by transport along the isogeny
`∏ₖ E_{ι k} → B` whose tangent map is the inverse `lift` of a coordinate projection
`π_ι : t → ℂ^{dim t}` (`LSG.CM.Chart`). No CM is needed: for any abelian subvariety `B` of a
product of elliptic curves, some coordinate projection `B → ∏ₖ E_{ι k}` is an isogeny.

On tangent spaces the transport is `Θ = id × id × lift : Tan k₀ k₁ s → tanB k₀ k₁ t` (a linear
isomorphism onto `T_G`), with left inverse `Φ = id × id × π_ι`. Pulling back `V, W, Y` along `Θ`:
* logarithms of algebraic points pull back to logarithms of algebraic points (`Φ` only forgets
  coordinates), `ℚ̄`-rationality is preserved;
* `Θ⁻¹(Ω(G)) ⊂ Ω(∏ E_{ι k})` with torsion quotient (`Chart.exists_nsmul_lift_mem`), so `κ` and `λ`
  are unchanged;
* subgroups `H₀ × T_U × B''` of `∏ E_{ι k}` push forward to `H₀ × T_U × lift(B'')` with
  `lift(t'')` an abelian tangent (`Chart.isAbelianTangent_map`), and `δ`, `τ` are unchanged.
-/

open Module Complex

namespace LSG.CM

open LSG.W88

variable {k0 k1 r : ℕ} {Ls : Fin r → PeriodPair} {t : Submodule ℂ (Fin r → ℂ)}

namespace Chart

variable (c : Chart t) (k0 k1)

/-- `Θ = id × id × lift`. -/
noncomputable def Θ : Tan k0 k1 (finrank ℂ t) →ₗ[ℂ] Tan k0 k1 r :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id c.lift)

/-- `Φ = id × id × π_ι`. -/
noncomputable def Φ : Tan k0 k1 r →ₗ[ℂ] Tan k0 k1 (finrank ℂ t) :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id (proj c.ι))

variable {k0 k1}

@[simp] lemma Θ_apply (u : Tan k0 k1 (finrank ℂ t)) :
    c.Θ k0 k1 u = (u.1, u.2.1, c.lift u.2.2) := rfl

@[simp] lemma Φ_apply (p : Tan k0 k1 r) : c.Φ k0 k1 p = (p.1, p.2.1, proj c.ι p.2.2) := rfl

lemma Φ_Θ (u : Tan k0 k1 (finrank ℂ t)) : c.Φ k0 k1 (c.Θ k0 k1 u) = u := by
  simp [c.proj_lift]

lemma Θ_Φ {p : Tan k0 k1 r} (hp : p ∈ tanB k0 k1 t) : c.Θ k0 k1 (c.Φ k0 k1 p) = p := by
  simp [c.lift_proj hp.2.2]

lemma Θ_injective : Function.Injective (c.Θ k0 k1) :=
  Function.LeftInverse.injective (g := c.Φ k0 k1) c.Φ_Θ

lemma range_Θ : LinearMap.range (c.Θ k0 k1) = tanB k0 k1 t := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact ⟨Submodule.mem_top, Submodule.mem_top, c.lift_mem _⟩
  · intro p hp; exact ⟨_, c.Θ_Φ hp⟩

lemma mem_Per_iff {m : ℕ} {Ls : Fin m → PeriodPair} {p : Tan k0 k1 m} :
    p ∈ Per Ls ↔ p.1 = 0 ∧ (∀ i, ∃ k : ℤ, p.2.1 i = 2 * Real.pi * I * k) ∧
      ∀ j, p.2.2 j ∈ (Ls j).lattice := Iff.rfl

lemma Φ_mem_Per {p : Tan k0 k1 r} (hp : p ∈ Per Ls) : c.Φ k0 k1 p ∈ Per (Ls ∘ c.ι) := by
  rw [mem_Per_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun k => hp.2.2 (c.ι k)⟩

lemma comap_Per_le : (Per Ls).comap (c.Θ k0 k1).toAddMonoidHom ≤ Per (Ls ∘ c.ι) := by
  intro u hu
  have := c.Φ_mem_Per hu
  rwa [LinearMap.toAddMonoidHom_coe, c.Φ_Θ] at this

lemma exists_nsmul_Θ_mem_Per (hab : IsAbelianTangent Ls t) {x : Tan k0 k1 (finrank ℂ t)}
    (hx : x ∈ Per (Ls ∘ c.ι)) : ∃ n : ℕ, n ≠ 0 ∧ c.Θ k0 k1 (n • x) ∈ Per Ls := by
  rw [mem_Per_iff] at hx
  obtain ⟨n, hn, hlat⟩ := c.exists_nsmul_lift_mem hab hx.2.2
  refine ⟨n, hn, ?_⟩
  rw [mem_Per_iff]
  refine ⟨by simp [hx.1], fun i => ?_, fun j => by simpa using hlat j⟩
  obtain ⟨k, hk⟩ := hx.2.1 i
  exact ⟨n * k, by simp [hk]; ring⟩

end Chart

/-- Transport of ranks along an injective map whose image contains `Y`. -/
lemma rk_inf_eq {E F : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup F] [Module ℚ F]
    (θ : E →+ F) (φ : F →+ E) (hθ : Function.Injective θ) {Y : AddSubgroup F}
    (hY : ∀ y ∈ Y, θ (φ y) = y) (X : AddSubgroup F) {X' : AddSubgroup E}
    (hle : X.comap θ ≤ X') (hn : ∀ x ∈ X', ∃ n : ℕ, n ≠ 0 ∧ θ (n • x) ∈ X) :
    rk (Y ⊓ X) = rk (Y.map φ ⊓ X') := by
  have hmemY : ∀ u, u ∈ Y.map φ ↔ θ u ∈ Y := fun u => by
    constructor
    · rintro ⟨y, hy, rfl⟩; rwa [hY y hy]
    · intro hu
      refine ⟨θ u, hu, hθ ?_⟩
      rw [hY _ hu]
  have hmap : (Y.map φ ⊓ X.comap θ).map θ = Y ⊓ X := by
    ext p
    constructor
    · rintro ⟨u, ⟨hu, hux⟩, rfl⟩
      exact ⟨(hmemY u).mp hu, hux⟩
    · rintro ⟨hpY, hpX⟩
      refine ⟨φ p, ⟨⟨p, hpY, rfl⟩, ?_⟩, hY p hpY⟩
      change θ (φ p) ∈ X
      rwa [hY p hpY]
  rw [← hmap, rk_map_of_injective θ hθ]
  refine rk_eq_of_le_of_nsmul (inf_le_inf_left _ hle) fun b hb => ?_
  obtain ⟨n, hn0, hnb⟩ := hn b hb.2
  refine ⟨n, hn0, ?_, hnb⟩
  exact (Y.map φ).nsmul_mem hb.1 n


/-- **W88 Theorem 4.1 for `G_a^{k₀} × G_m^{k₁} × B`**, any abelian subvariety `B` of
`E₁ × ⋯ × E_r`, from Theorem 4.1 for products of elliptic curves. -/
theorem thm41SubAt_of (h41 : Theorem41Abelian)
    (halg : ∀ j, IsAlgebraic ℚ (Ls j).g₂ ∧ IsAlgebraic ℚ (Ls j).g₃)
    (hab : IsAbelianTangent Ls t) : Thm41SubAt k0 k1 Ls t := by
  classical
  intro V W Y hVt hdim hWV hWrat hYfg hYV hNR
  obtain ⟨c⟩ := nonempty_chart t
  set Θ := c.Θ k0 k1 with hΘdef
  set Φ := c.Φ k0 k1 with hΦdef
  have hΘi : Function.Injective Θ := c.Θ_injective
  have hrange : LinearMap.range Θ = tanB k0 k1 t := c.range_Θ
  have hΘΦ : ∀ p ∈ tanB k0 k1 t, Θ (Φ p) = p := fun p hp => c.Θ_Φ hp
  have hΦΘ : ∀ u, Φ (Θ u) = u := c.Φ_Θ
  set V' := V.comap Θ
  set W' := W.comap Θ
  set Y' : AddSubgroup (Tan k0 k1 (finrank ℂ t)) := Y.map Φ.toAddMonoidHom
  have hVmap : V'.map Θ = V := Submodule.map_comap_eq_of_le (hrange ▸ hVt)
  have hWmap : W'.map Θ = W := Submodule.map_comap_eq_of_le (hrange ▸ hWV.trans hVt)
  have hVdim : finrank ℂ V' = finrank ℂ V := by
    rw [← hVmap, finrank_map_of_injective' hΘi]
  have hWdim : finrank ℂ W' = finrank ℂ W := by
    rw [← hWmap, finrank_map_of_injective' hΘi]
  have hYT : ∀ y ∈ Y, Θ (Φ y) = y := fun y hy => hΘΦ y (hVt (hYV y hy).1)
  have hmemY : ∀ u, u ∈ Y' ↔ Θ u ∈ Y := fun u => by
    constructor
    · rintro ⟨y, hy, rfl⟩; change Θ (Φ y) ∈ Y; rwa [hYT y hy]
    · intro hu; exact ⟨Θ u, hu, hΦΘ u⟩
  -- ranks
  have hrkY : rk Y = rk Y' := by
    have := rk_inf_eq Θ.toAddMonoidHom Φ.toAddMonoidHom hΘi hYT ⊤ (X' := ⊤) le_top
      (fun x _ => ⟨1, one_ne_zero, trivial⟩)
    simpa using this
  have hrkPer : rk (Y ⊓ Per Ls) = rk (Y' ⊓ Per (Ls ∘ c.ι)) :=
    rk_inf_eq Θ.toAddMonoidHom Φ.toAddMonoidHom hΘi hYT _ c.comap_Per_le
      (fun x hx => c.exists_nsmul_Θ_mem_Per hab hx)
  -- apply Theorem 4.1 to `G_a^{k₀} × G_m^{k₁} × ∏ₖ E_{ι k}`
  have hW'rat : RationalOverQbarTan W' := by
    apply le_antisymm
    · intro w hw
      have hΘw : Θ w ∈ W := hw
      rw [hWrat] at hΘw
      have hmap := Submodule.mem_map_of_mem (f := Φ) hΘw
      rw [hΦΘ, Submodule.map_span] at hmap
      refine (Submodule.span_mono ?_) hmap
      rintro _ ⟨p, ⟨hpW, h1, h2, h3⟩, rfl⟩
      refine ⟨?_, h1, h2, fun k => h3 (c.ι k)⟩
      change Θ (Φ p) ∈ W
      rwa [hΘΦ p (hVt (hWV hpW))]
    · rw [Submodule.span_le]; exact fun w hw => hw.1
  have hY'fg : Y'.FG := LSG.W88.K11.fg_map_addSubgroup hYfg _
  have hY'V : ∀ y ∈ Y', y ∈ V' ∧ y ∈ Lam (Ls ∘ c.ι) := by
    intro u hu
    have hΘu := (hmemY u).mp hu
    obtain ⟨hV, h1, h2, h3⟩ := hYV _ hΘu
    refine ⟨hV, h1, h2, fun k => ?_⟩
    have := h3 (c.ι k)
    simpa [hΘdef, c.lift_apply] using this
  obtain ⟨H', hprop, hτ, hineq⟩ := h41 k0 k1 (finrank ℂ t) (Ls ∘ c.ι) (fun j => halg (c.ι j))
    V' W' Y' (by rw [hVdim]; exact hdim) (Submodule.comap_mono hWV) hW'rat hY'fg hY'V
    (by rw [← hrkPer, hVdim]; exact hNR)
  -- push the subgroup forward
  let H : SubgroupData (d0 := k0) (d1 := k1) Ls :=
    ⟨H'.h0, H'.U, H'.t.map c.lift, H'.h0_rat, c.isAbelianTangent_map hab H'.t_ab⟩
  have hHt : finrank ℂ H.t = finrank ℂ H'.t := finrank_map_of_injective' c.lift_injective _
  have hδ : H.δB t = H'.δ := by
    simp only [SubgroupData.δB, SubgroupData.δ, SubgroupData.δ0, SubgroupData.δ1,
      SubgroupData.δ2, hHt, H]
  have hcomap : H.tan.comap Θ = H'.tan := by
    ext u
    simp only [Submodule.mem_comap, SubgroupData.tan, Submodule.mem_prod, hΘdef, Chart.Θ_apply, H]
    have key : c.lift u.2.2 ∈ H'.t.map c.lift ↔ u.2.2 ∈ H'.t :=
      ⟨fun ⟨y, hy, he⟩ => c.lift_injective he ▸ hy, fun h => ⟨_, h, rfl⟩⟩
    rw [key]
  have hτeq : finrank ℂ ↥(W ⊓ H.tan) = finrank ℂ ↥(W' ⊓ H'.tan) := by
    have : (W' ⊓ H'.tan).map Θ = W ⊓ H.tan := by
      rw [← hcomap, ← Submodule.comap_inf]
      exact Submodule.map_comap_eq_of_le (hrange ▸ inf_le_left.trans (hWV.trans hVt))
    rw [← this, finrank_map_of_injective' hΘi]
  have hrkLam : rk (Y ⊓ (H.tan.toAddSubgroup ⊔ Per Ls)) =
      rk (Y' ⊓ (H'.tan.toAddSubgroup ⊔ Per (Ls ∘ c.ι))) := by
    refine rk_inf_eq Θ.toAddMonoidHom Φ.toAddMonoidHom hΘi hYT _ ?_ ?_
    · intro u hu
      obtain ⟨a, ha, p, hp, hap⟩ := AddSubgroup.mem_sup.mp hu
      have hu' : u = Φ a + Φ p := by
        rw [← map_add, hap]; exact (hΦΘ u).symm
      rw [hu']
      refine AddSubgroup.add_mem_sup ?_ (c.Φ_mem_Per hp)
      obtain ⟨h0a, hUa, b, hb, hba⟩ := ha
      refine ⟨h0a, hUa, ?_⟩
      change proj c.ι a.2.2 ∈ H'.t
      rw [← hba, c.proj_lift]; exact hb
    · intro x hx
      obtain ⟨a, ha, p, hp, rfl⟩ := AddSubgroup.mem_sup.mp hx
      obtain ⟨n, hn, hnp⟩ := c.exists_nsmul_Θ_mem_Per hab hp
      refine ⟨n, hn, ?_⟩
      have ha' : Θ (n • a) ∈ H.tan := by
        have : n • a ∈ H.tan.comap Θ := hcomap ▸ H'.tan.toAddSubgroup.nsmul_mem ha n
        exact this
      rw [smul_add]
      simp only [LinearMap.toAddMonoidHom_coe, map_add]
      exact AddSubgroup.add_mem_sup ha' hnp
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩; exact c.lift_mem u
  · rw [hδ]; exact hprop
  · rw [hδ, hτeq, ← hWdim]; exact hτ
  · rw [hδ, hτeq, ← hWdim, hrkY, hrkLam, hrkPer, ← hVdim, hHt]
    exact hineq

/-- **`Thm41Sub`** (W88 Theorem 4.1 under (NR) for `G_a^{k₀} × G_m^{k₁} × B`, `B` any abelian
subvariety of a product of elliptic curves with algebraic invariants). -/
theorem thm41Sub : Thm41Sub := fun _ _ _ _ halg _ hab =>
  thm41SubAt_of theorem41Abelian halg hab

/-- The per-curve form for a power of one curve `E` (e.g. a CM curve: no CM hypothesis is
needed). -/
theorem thm41SubAt_cm (L : PeriodPair) (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {m : ℕ} (k0 k1 : ℕ) (t : Submodule ℂ (Fin m → ℂ)) (hab : IsAbelianTangent (fun _ => L) t) :
    Thm41SubAt k0 k1 (fun _ : Fin m => L) t :=
  thm41SubAt_of theorem41Abelian (fun _ => ⟨hg₂, hg₃⟩) hab

end LSG.CM
