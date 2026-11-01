/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.W88.AbVarV5dHyp
import LSG.W88.AbVar5dRank
import LSG.W88.AbVarVSec7
import LSG.W88.V5dMain
import LSG.W88.K5dMain

/-!
# M2.7a: period ranks and members for the §5d engine on the vector-extension class

`Ω = span_ℚ PerAVf` (full periods; equal to `span_ℚ PerAV` by `perAVf_nsmul`). The forgetful map
`piAL : (a, b, z, s) ↦ (a, b, z)` is injective on `Ω` (`η` is additive, so a multiple of an element of `Ω` with zero
base part is `0`), so the abelian bounds transfer:
* **`finrank_OmAV_le`**: `rk Ω ≤ d₁ + 2G` (`G = Σ g_k`; the fibre of a period is determined by its base);
* **`finrank_OmAV_inf_ge`**: `rk (Ω ∩ T_H) ≥ dim U^⊥ + 2 dim t`;
* **`kappa_le_of_torInjAV`**: under `TorInjAV`, `κ′ ≤ dim U^⊥` (REVIEW_TORINJ §3d).
Members: `d2H H = dim (T_H ∩ ker pr₀ ∩ ker pr_tor)` (W88's `d₂(H)`), `nPAV H = dim U^⊥ + 2 d2H H`; `d2H ≤ dim t + r`;
`topSubAV` (the whole group); under `PerTanFib`, `t ≠ 0 ⇒ T(B̃) = t × ℂ^r` (`perTanA_eq_prod`).
-/

open Complex Module Submodule LSG.AuxAV LSG.AuxA

noncomputable section

namespace LSG.W88

open LSG.W88.AVS

open LSG.MEB (IsRatSub tanOf)
open LSG.MEBV (VBlock perTanId perBase)
open LSG.W88.Vec (RatPair AlgPair AlgMat)

variable {m d₀ d₁ r : ℕ} {B : Fin m → VBlock} {M : Matrix (Fin r) (Fin m) ℂ}

/-! ### `ℚ`-spans of subgroups -/

lemma exists_nsmul_of_mem_span {E : Type*} [AddCommGroup E] [Module ℚ E] {P : AddSubgroup E} {x : E}
    (hx : x ∈ span ℚ (P : Set E)) : ∃ N : ℕ, 0 < N ∧ N • x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simpa using P.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨N', hN', hNy⟩ := hy
    refine ⟨N * N', Nat.mul_pos hN hN', ?_⟩
    rw [smul_add]
    refine P.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact P.nsmul_mem hNx N'
    · rw [mul_smul]; exact P.nsmul_mem hNy N
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    refine ⟨c.den * N, Nat.mul_pos c.den_pos hN, ?_⟩
    have e : (c.den * N) • (c • x) = c.num • (N • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ N, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        smul_smul]
      congr 1
      push_cast
      rw [mul_comm (c.den : ℚ), mul_assoc, Rat.den_mul_eq_num]; ring
    rw [e]; exact P.zsmul_mem hNx _

/-! ### `Ω` and the forgetful map -/

variable (d₀ d₁ B M) in
/-- `Ω = span_ℚ Ω(G)` (full periods). -/
abbrev OmAV : Submodule ℚ (TanAV d₀ d₁ r B) := span ℚ (PerAVf d₀ d₁ B M : Set (TanAV d₀ d₁ r B))

lemma piAL_apply' (u : TanAV d₀ d₁ r B) : piAL u = (u.1, u.2.1, u.2.2.1) := rfl

lemma etaB_zero' : etaB B (0 : ∀ k, Fin (B k).g → ℂ) = 0 := funext fun k => (B k).η_zero

lemma eq_zero_of_perAVf {p : TanAV d₀ d₁ r B} (hp : p ∈ PerAVf d₀ d₁ B M) (h0 : piAL p = 0) : p = 0 := by
  have h1 : p.2.1 = 0 := congrArg (fun q : LSG.MEB.Tan d₀ d₁ (Bb B) => q.2.1) h0
  have h2 : p.2.2.1 = 0 := congrArg (fun q : LSG.MEB.Tan d₀ d₁ (Bb B) => q.2.2) h0
  have h3 : p.2.2.2 = 0 := by rw [hp.2.2.2, h2, etaB_zero', Matrix.mulVec_zero]
  exact Prod.ext hp.1 (Prod.ext h1 (Prod.ext h2 h3))

lemma piAL_injOn_OmAV {x : TanAV d₀ d₁ r B} (hx : x ∈ OmAV d₀ d₁ B M) (h0 : piAL x = 0) : x = 0 := by
  obtain ⟨N, hN, hNx⟩ := exists_nsmul_of_mem_span hx
  have := eq_zero_of_perAVf hNx (by rw [map_nsmul, h0, smul_zero])
  exact (smul_eq_zero.mp this).resolve_left hN.ne'

lemma piAL_perAVf {p : TanAV d₀ d₁ r B} (hp : p ∈ PerAVf d₀ d₁ B M) : piAL p ∈ MEB.Per d₀ d₁ (Bb B) :=
  ⟨hp.1, hp.2.1, fun k => hp.2.2.1 k⟩

/-- `piAL` on `Ω`, landing in `span_ℚ MEB.Per`. -/
def piOm : OmAV d₀ d₁ B M →ₗ[ℚ] span ℚ (MEB.Per d₀ d₁ (Bb B) : Set (MEB.Tan d₀ d₁ (Bb B))) :=
  LinearMap.codRestrict _ ((piAL.restrictScalars ℚ).domRestrict _) fun x => by
    have h : (OmAV d₀ d₁ B M).map (piAL.restrictScalars ℚ) ≤ span ℚ (MEB.Per d₀ d₁ (Bb B) : Set _) := by
      rw [map_span, span_le]
      rintro _ ⟨p, hp, rfl⟩
      exact subset_span (piAL_perAVf hp)
    exact h ⟨x, x.2, rfl⟩

lemma piOm_injective : Function.Injective (piOm (d₀ := d₀) (d₁ := d₁) (B := B) (M := M)) := by
  intro x y h
  have h' : piAL ((x : TanAV d₀ d₁ r B) - (y : TanAV d₀ d₁ r B)) = 0 := by
    rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val h
  exact Subtype.ext (sub_eq_zero.mp (piAL_injOn_OmAV ((OmAV d₀ d₁ B M).sub_mem x.2 y.2) h'))

instance : FiniteDimensional ℚ (OmAV d₀ d₁ B M) :=
  Module.Finite.of_injective _ piOm_injective

/-- **`rk Ω(G) ≤ d₁ + 2G`.** -/
theorem finrank_OmAV_le : finrank ℚ (OmAV d₀ d₁ B M) ≤ d₁ + 2 * ∑ k, (B k).g :=
  (LinearMap.finrank_le_finrank_of_injective piOm_injective).trans
    (finrank_span_Per_le (d₀ := d₀) (d₁ := d₁) (B := Bb B)).2

/-! ### Members -/

lemma mem_tan_z {H : SubgroupDataAV d₀ d₁ B M} {x : TanAV d₀ d₁ r B} (hx : x ∈ H.tan) : x.2.2.1 ∈ H.t := by
  have hle : H.tan ≤ H.t.comap ((LinearMap.fst ℂ _ _).comp ((LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _))) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨γ, -, rfl⟩; exact H.t.zero_mem
    · rintro _ ⟨b, -, rfl⟩; exact H.t.zero_mem
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩; exact perTanId_le_fst H.t hp
  exact hle hx

lemma g2InclA_mem_tan (H : SubgroupDataAV d₀ d₁ B M) {z : ∀ k, Fin (B k).g → ℂ} (hz : z ∈ H.t)
    (hzp : ∀ k, z k ∈ (B k).base.per) :
    (g2InclA (z, M.mulVec (etaB B z)) : TanAV d₀ d₁ r B) ∈ H.tan := by
  refine mem_sup_right ⟨(z, M.mulVec (etaB B z)), ⟨(z, etaB B z), subset_span ⟨hz, fun k => ⟨hzp k, rfl⟩⟩,
    rfl⟩, rfl⟩

lemma torInclA_mem_tan (H : SubgroupDataAV d₀ d₁ B M) {b : Fin d₁ → ℂ} (hb : b ∈ torusLie H.U) :
    (torInclA b : TanAV d₀ d₁ r B) ∈ H.tan :=
  mem_sup_left (mem_sup_right ⟨b, hb, rfl⟩)

/-- **`rk (Ω ∩ T_H) ≥ dim U^⊥ + 2 dim t`.** -/
theorem finrank_OmAV_inf_ge (H : SubgroupDataAV d₀ d₁ B M) :
    finrank ℂ (torusLie H.U) + 2 * finrank ℂ H.t ≤
      finrank ℚ ↥(OmAV d₀ d₁ B M ⊓ H.tan.restrictScalars ℚ) := by
  have hab := finrank_Per_inf_tan_ge (d₀ := d₀) (B := Bb B) ⊥ H.U H.t H.t_rat
  have : FiniteDimensional ℚ ↥(OmAV d₀ d₁ B M ⊓ H.tan.restrictScalars ℚ) :=
    Submodule.finiteDimensional_of_le inf_le_left
  refine hab.trans ((Submodule.finrank_mono ?_).trans (Submodule.finrank_map_le (piAL.restrictScalars ℚ) _))
  rintro x ⟨hxP, hxT⟩
  obtain ⟨N, hN, hNx⟩ := exists_nsmul_of_mem_span hxP
  obtain ⟨hx1, hx2, hx3⟩ := (show x ∈ tanOf ⊥ H.U H.t from hxT)
  set y := N • x with hy
  have hy1 : y.1 = 0 := hNx.1
  have hyz : ∀ k, y.2.2 k ∈ (B k).base.per := hNx.2.2
  set p : TanAV d₀ d₁ r B := (0, y.2.1, y.2.2, M.mulVec (etaB B y.2.2)) with hp
  have hpP : p ∈ PerAVf d₀ d₁ B M := ⟨rfl, hNx.2.1, hyz, rfl⟩
  have hpT : p ∈ H.tan := by
    have e : p = torInclA y.2.1 + g2InclA (y.2.2, M.mulVec (etaB B y.2.2)) := by
      ext <;> simp [p, torInclA, g2InclA]
    rw [e]
    refine H.tan.add_mem (torInclA_mem_tan H ?_) (g2InclA_mem_tan H ?_ hyz)
    · exact (torusLie H.U).smul_of_tower_mem N hx2
    · exact H.t.smul_of_tower_mem N hx3
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(N : ℚ)⁻¹ • p, ⟨(OmAV d₀ d₁ B M).smul_mem _ (subset_span hpP),
    H.tan.restrictScalars ℚ |>.smul_mem _ hpT⟩, ?_⟩
  have hpy : piAL p = y := by
    change ((0 : Fin d₀ → ℂ), y.2.1, y.2.2) = y
    rw [← hy1]
  change piAL ((N : ℚ)⁻¹ • p) = x
  rw [show piAL ((N : ℚ)⁻¹ • p) = (N : ℚ)⁻¹ • piAL p from (piAL.restrictScalars ℚ).map_smul _ _, hpy, hy,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN', one_smul]

/-- W88's `d₂(H) = dim (T_H ∩ ker pr₀ ∩ ker pr_tor)`. -/
def d2H (H : SubgroupDataAV d₀ d₁ B M) : ℕ :=
  finrank ℂ ↥(H.tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA))

/-- `d₁(H) + 2d₂(H)`. -/
def nPAV (H : SubgroupDataAV d₀ d₁ B M) : ℕ := finrank ℂ (torusLie H.U) + 2 * d2H H

lemma finrank_tan_eq (H : SubgroupDataAV d₀ d₁ B M) :
    finrank ℂ H.tan = finrank ℂ (H.gam.map (LinearMap.fst ℂ _ _)) + finrank ℂ (torusLie H.U) + d2H H :=
  finrank_tanAV H.gam H.U H.t

lemma d2H_le (H : SubgroupDataAV d₀ d₁ B M) : d2H H ≤ finrank ℂ H.t + r := by
  let f : TanAV d₀ d₁ r B →ₗ[ℂ] (∀ k, Fin (B k).g → ℂ) × (Fin r → ℂ) :=
    (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)
  have hinj : ∀ x ∈ H.tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓
      LinearMap.ker prBA), f x = 0 → x = 0 := by
    rintro x ⟨-, h1, h2⟩ hf
    exact Prod.ext h1 (Prod.ext h2 hf)
  have hle : (H.tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓
      LinearMap.ker prBA)).map f ≤ H.t.prod ⊤ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_tan_z hx.1, mem_top⟩
  have h1 := Submodule.finrank_mono hle
  rw [K5d.finrank_prodSub, finrank_top, Module.finrank_fin_fun] at h1
  set S := H.tan ⊓ (LinearMap.ker (prAA (d₀ := d₀) (d₁ := d₁) (r := r) (B := B)) ⊓ LinearMap.ker prBA)
  have hinj' : Function.Injective (f.domRestrict S) := by
    intro x y h
    exact Subtype.ext (sub_eq_zero.mp (hinj ((x : TanAV d₀ d₁ r B) - (y : TanAV d₀ d₁ r B))
      (S.sub_mem x.2 y.2) (by rw [map_sub]; exact sub_eq_zero.mpr h)))
  have h2 : finrank ℂ ↥(S.map f) = d2H H := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj']; rfl
  omega

lemma nPAV_le (H : SubgroupDataAV d₀ d₁ B M) : nPAV H ≤ finrank ℂ (torusLie H.U) + 2 * (finrank ℂ H.t + r) := by
  have := d2H_le H; unfold nPAV; omega

/-! ### The whole group -/

variable (d₀ d₁ B M) in
/-- The whole group as a member. -/
def topSubAV : SubgroupDataAV d₀ d₁ B M where
  U := ⊥
  t := ⊤
  gam := ⊤
  gam_rat := V5d.ratPair_top
  t_rat := isRatSub_top (B := Bb B)

lemma topSubAV_tan : (topSubAV d₀ d₁ B M).tan = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b, z, s⟩ -
  obtain ⟨w, hw⟩ := exists_perTanId (isRatSub_top (B := Bb B)) (mem_top : z ∈ (⊤ : Submodule ℂ _))
  have e : ((a, b, z, s) : TanAV d₀ d₁ r B) =
      vecInclA (a, s - M.mulVec w) + torInclA b + g2InclA (z, M.mulVec w) := by
    ext <;> simp [vecInclA, torInclA, g2InclA]
  rw [e]
  refine add_mem (add_mem (mem_sup_left (mem_sup_left ⟨_, mem_top, rfl⟩)) ?_) ?_
  · refine torInclA_mem_tan _ ?_
    change b ∈ torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))
    rw [K5d.torusLie_bot]; trivial
  · exact mem_sup_right ⟨(z, M.mulVec w), ⟨(z, w), hw, rfl⟩, rfl⟩

lemma nPAV_top : nPAV (topSubAV d₀ d₁ B M) = d₁ + 2 * (∑ k, (B k).g + r) := by
  have h := finrank_tan_eq (topSubAV d₀ d₁ B M)
  rw [topSubAV_tan, finrank_top, finrank_TanAV] at h
  have h0 : finrank ℂ ((⊤ : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))).map (LinearMap.fst ℂ _ _)) = d₀ :=
    V5d.finrank_map_fst_top
  have h1 : finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))) = d₁ := by
    rw [K5d.torusLie_bot, finrank_top, Module.finrank_fin_fun]
  change finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))) + 2 * d2H (topSubAV d₀ d₁ B M) = _
  change _ = finrank ℂ ((⊤ : Submodule ℂ ((Fin d₀ → ℂ) × (Fin r → ℂ))).map (LinearMap.fst ℂ _ _)) +
    finrank ℂ (torusLie (⊥ : Submodule ℚ (Fin d₁ → ℚ))) + d2H (topSubAV d₀ d₁ B M) at h
  rw [h0, h1] at h
  rw [h1]; omega

/-! ### The fibre property -/

/-- **Under `PerTanFib`, `T(B̃) = t × ℂ^r` for rational `t ≠ 0`.** -/
theorem perTanA_eq_prod (hF : PerTanFib B M) {t : Submodule ℂ (∀ k, Fin (B k).g → ℂ)}
    (ht : IsRatSub (perBase B) t) (hne : t ≠ ⊥) : perTanA B M t = t.prod ⊤ := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨perTanId_le_fst t hp, mem_top⟩
  · rintro ⟨z, s⟩ ⟨hz, -⟩
    obtain ⟨w, hw⟩ := exists_perTanId ht hz
    have h1 : (z, M.mulVec w) ∈ perTanA B M t := ⟨(z, w), hw, rfl⟩
    have h2 := hF t ht hne (s - M.mulVec w)
    have := (perTanA B M t).add_mem h1 h2
    simpa using this

/-- **The tangent space of a member with `t ≠ 0`** (under `PerTanFib`): `pr₀ Γ × U^⊥ × t × ℂ^r`. -/
theorem mem_tan_iff_of_ne (hF : PerTanFib B M) (H : SubgroupDataAV d₀ d₁ B M) (hne : H.t ≠ ⊥)
    {x : TanAV d₀ d₁ r B} :
    x ∈ H.tan ↔ x.1 ∈ H.gam.map (LinearMap.fst ℂ _ _) ∧ x.2.1 ∈ torusLie H.U ∧ x.2.2.1 ∈ H.t := by
  have hP := perTanA_eq_prod hF H.t_rat hne
  constructor
  · intro hx
    refine ⟨?_, ?_, mem_tan_z hx⟩
    · have := (map_fst_tanAV (B := B) (M := M) (gam := H.gam) (U := H.U) (t := H.t)) ▸
        (show x.1 ∈ (tanAV B M H.gam H.U H.t).map (LinearMap.fst ℂ _ _) from ⟨x, hx, rfl⟩)
      exact this
    · have hle : H.tan ≤ (torusLie H.U).comap prBA := by
        refine sup_le (sup_le ?_ ?_) ?_
        · rintro _ ⟨γ, -, rfl⟩; exact (torusLie H.U).zero_mem
        · rintro _ ⟨b, hb, rfl⟩; exact hb
        · rintro _ ⟨_, -, rfl⟩; exact (torusLie H.U).zero_mem
      exact hle hx
  · rintro ⟨⟨γ, hγ, hγa⟩, hb, hz⟩
    have e : x = vecInclA γ + torInclA x.2.1 + g2InclA (x.2.2.1, x.2.2.2 - γ.2) := by
      obtain ⟨a, b, z, s⟩ := x
      obtain ⟨γa, γs⟩ := γ
      simp only at hγa
      subst hγa
      ext <;> simp [vecInclA, torInclA, g2InclA]
    rw [e]
    refine add_mem (add_mem (mem_sup_left (mem_sup_left ⟨γ, hγ, rfl⟩)) (torInclA_mem_tan H hb)) ?_
    refine mem_sup_right ⟨_, ?_, rfl⟩
    rw [hP]; exact ⟨hz, mem_top⟩

/-! ### Toric injectivity bounds `κ` -/

lemma exists_toric_ratAV {v : TanAV d₀ d₁ r B} (hv : v ∈ OmAV d₀ d₁ B M) :
    ∃ q : Fin d₁ → ℚ, v.2.1 = (2 * Real.pi * I : ℂ) • K11.castL d₁ q := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    choose n hn using hx.2.1
    refine ⟨fun i => (n i : ℚ), funext fun i => ?_⟩
    simp [hn i, K11.castL]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [Prod.snd_add, Prod.fst_add, ha, hb, map_add, smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c • a, ?_⟩
    rw [Prod.smul_snd, Prod.smul_fst, ha, map_smul, smul_comm]

/-- **Toric injectivity bounds the period rank by the toric dimension.** -/
theorem kappa_le_of_torInjAV {V : Submodule ℂ (TanAV d₀ d₁ r B)} (hV : TorInjAV M V)
    (U : Submodule ℚ (Fin d₁ → ℚ)) (S : Submodule ℚ (TanAV d₀ d₁ r B)) [FiniteDimensional ℚ S]
    (hSV : ∀ v ∈ S, v ∈ V) (hSP : S ≤ OmAV d₀ d₁ B M)
    (hST : ∀ v ∈ S, v.2.1 ∈ torusLie U) : finrank ℚ S ≤ finrank ℂ (torusLie U) := by
  classical
  let b := Module.finBasis ℚ S
  set k := finrank ℚ S
  choose q hq using fun i => exists_toric_ratAV (hSP (b i).2)
  have hqli : LinearIndependent ℚ q := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set v : TanAV d₀ d₁ r B := ∑ i, c i • (b i : TanAV d₀ d₁ r B)
    have hvS : v ∈ S := sum_mem fun i _ => smul_mem _ _ (b i).2
    have hv1 : v.2.1 = 0 := by
      have e : v.2.1 = ∑ i, c i • (b i : TanAV d₀ d₁ r B).2.1 := by
        simp only [v, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst]
      rw [e]
      simp only [hq, smul_comm (c _) (2 * Real.pi * I : ℂ), ← Finset.smul_sum, ← map_smul, ← map_sum, hc,
        map_zero, smul_zero]
    have hv0 := hV v (hSV v hvS) (hSP hvS) hv1
    have : (∑ i, c i • b i : S) = 0 := Subtype.ext (by simpa [v] using hv0)
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c this
  have hcC := K5d.linIndep_cast (F := ℂ) q hqli
  let f : Fin k → torusLie U := fun i => ⟨(b i : TanAV d₀ d₁ r B).2.1, hST _ (b i).2⟩
  have hf : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    refine Fintype.linearIndependent_iff.mp hcC a ?_
    have h1 : ∑ i, a i • (b i : TanAV d₀ d₁ r B).2.1 = 0 := by
      have := congrArg Subtype.val ha
      simpa [f] using this
    simp only [hq, K11.castL] at h1
    funext j
    have h2 := congrFun h1 j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.zero_apply] at h2
    have h3 : (2 * Real.pi * I : ℂ) * ∑ i, a i * ((q i j : ℚ) : ℂ) = 0 := by
      rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have := (mul_eq_zero.mp h3).resolve_left K11.two_pi_I_ne_zero
    simpa [Finset.sum_apply, smul_eq_mul] using this
  simpa using hf.fintype_card_le_finrank

/-- `span_ℚ PerAV = Ω`. -/
theorem span_perAV_eq (An : ∀ k, VBlockAn (B k)) :
    span ℚ (PerAV d₀ d₁ An M : Set (TanAV d₀ d₁ r B)) = OmAV d₀ d₁ B M :=
  span_rat_eq_of_nsmul (PerAV_le_PerAVf An M) fun _ hω => perAVf_nsmul An hω

end LSG.W88
