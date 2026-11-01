/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Jac.TableFacts
import LSG.Jac.RangeSound
import LSG.Jac.Cert.T5base
import LSG.Jac.Cert.T5_0
import LSG.Jac.Cert.T5_1
import LSG.Jac.Cert.T5_2
import LSG.Jac.Cert.T5_3
import LSG.Jac.Cert.T5_4
import LSG.Jac.Cert.T5_5
import LSG.Jac.Cert.T5_6
import LSG.Jac.Cert.T5_7
import LSG.Jac.Cert.T5_8
import LSG.Jac.Cert.T5_9
import LSG.Jac.Cert.T5_10
import LSG.Jac.Cert.T5_11
import LSG.Jac.Cert.T5_12
import LSG.Jac.Cert.T5_13
import LSG.Jac.Cert.T5_14
import LSG.Jac.Cert.T5_15
import LSG.Jac.Cert.T5_16
import LSG.Jac.Cert.T5_17
import LSG.Jac.Cert.T5_18
import LSG.Jac.Cert.T5_19
import LSG.Jac.Cert.T5_20
import LSG.Jac.Cert.T5_21
import LSG.Jac.Cert.T5_22
import LSG.Jac.Cert.T5_23
import LSG.Jac.Cert.T5_24
import LSG.Jac.Cert.T5_25
import LSG.Jac.Cert.T5_26
import LSG.Jac.Cert.T5_27
import LSG.Jac.Cert.T5_28
import LSG.Jac.Cert.T5_29
import LSG.Jac.Cert.T5_30
import LSG.Jac.Cert.T5_31
import LSG.Jac.Cert.T5_32
import LSG.Jac.Cert.T5_33
import LSG.Jac.Cert.T5_34

/-! GENERATED (by hand-run script, see STAGE_A1 §10) — the E1 tables are valid normal forms.

* `nfValid5`: the degree-5 table (`35` certificate chunks) is valid at every point of `V(Q)`.
* `nfValid4b`: the degree-4 table with packing width `kb4b` (same rows as `nfTree`).
* `nfValid_id2`, `nfValid_id3`: the identity tables, everywhere. -/

namespace LSG.Jac

open Data Cert

theorem Qd_vanish {R : Type*} [CommRing R] (x : Fin 9 → R) (hx : OnQ x) : ∀ q ∈ Qd, evalRow x q = 0 := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have := hx ⟨i, Qd_length ▸ hi⟩
  simpa [Qe, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem nfValid5 {R : Type*} [CommRing R] (x : Fin 9 → R) (hx : OnQ x) : NFValid nfTree5 stdc5 nfDelta5 x := by
  have hQ := Qd_vanish x hx
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hl
  have hi' : i < 1287 := leaves_len5 ▸ hi
  rcases (show (0 ≤ i ∧ i < 30) ∨ (30 ≤ i ∧ i < 62) ∨ (62 ≤ i ∧ i < 93) ∨ (93 ≤ i ∧ i < 127) ∨ (127 ≤ i ∧ i < 156) ∨ (156 ≤ i ∧ i < 188) ∨ (188 ≤ i ∧ i < 221) ∨ (221 ≤ i ∧ i < 259) ∨ (259 ≤ i ∧ i < 289) ∨ (289 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 391) ∨ (391 ≤ i ∧ i < 424) ∨ (424 ≤ i ∧ i < 471) ∨ (471 ≤ i ∧ i < 501) ∨ (501 ≤ i ∧ i < 535) ∨ (535 ≤ i ∧ i < 566) ∨ (566 ≤ i ∧ i < 602) ∨ (602 ≤ i ∧ i < 637) ∨ (637 ≤ i ∧ i < 680) ∨ (680 ≤ i ∧ i < 713) ∨ (713 ≤ i ∧ i < 758) ∨ (758 ≤ i ∧ i < 803) ∨ (803 ≤ i ∧ i < 837) ∨ (837 ≤ i ∧ i < 872) ∨ (872 ≤ i ∧ i < 909) ∨ (909 ≤ i ∧ i < 945) ∨ (945 ≤ i ∧ i < 989) ∨ (989 ≤ i ∧ i < 1030) ∨ (1030 ≤ i ∧ i < 1074) ∨ (1074 ≤ i ∧ i < 1128) ∨ (1128 ≤ i ∧ i < 1164) ∨ (1164 ≤ i ∧ i < 1211) ∨ (1211 ≤ i ∧ i < 1259) ∨ (1259 ≤ i ∧ i < 1287) by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 0 nfc5_0 nf5_ok_0 x hQ i hi h.1 (by rw [nfc5_len_0]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 30 nfc5_1 nf5_ok_1 x hQ i hi h.1 (by rw [nfc5_len_1]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 62 nfc5_2 nf5_ok_2 x hQ i hi h.1 (by rw [nfc5_len_2]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 93 nfc5_3 nf5_ok_3 x hQ i hi h.1 (by rw [nfc5_len_3]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 127 nfc5_4 nf5_ok_4 x hQ i hi h.1 (by rw [nfc5_len_4]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 156 nfc5_5 nf5_ok_5 x hQ i hi h.1 (by rw [nfc5_len_5]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 188 nfc5_6 nf5_ok_6 x hQ i hi h.1 (by rw [nfc5_len_6]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 221 nfc5_7 nf5_ok_7 x hQ i hi h.1 (by rw [nfc5_len_7]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 259 nfc5_8 nf5_ok_8 x hQ i hi h.1 (by rw [nfc5_len_8]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 289 nfc5_9 nf5_ok_9 x hQ i hi h.1 (by rw [nfc5_len_9]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 320 nfc5_10 nf5_ok_10 x hQ i hi h.1 (by rw [nfc5_len_10]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 352 nfc5_11 nf5_ok_11 x hQ i hi h.1 (by rw [nfc5_len_11]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 391 nfc5_12 nf5_ok_12 x hQ i hi h.1 (by rw [nfc5_len_12]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 424 nfc5_13 nf5_ok_13 x hQ i hi h.1 (by rw [nfc5_len_13]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 471 nfc5_14 nf5_ok_14 x hQ i hi h.1 (by rw [nfc5_len_14]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 501 nfc5_15 nf5_ok_15 x hQ i hi h.1 (by rw [nfc5_len_15]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 535 nfc5_16 nf5_ok_16 x hQ i hi h.1 (by rw [nfc5_len_16]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 566 nfc5_17 nf5_ok_17 x hQ i hi h.1 (by rw [nfc5_len_17]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 602 nfc5_18 nf5_ok_18 x hQ i hi h.1 (by rw [nfc5_len_18]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 637 nfc5_19 nf5_ok_19 x hQ i hi h.1 (by rw [nfc5_len_19]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 680 nfc5_20 nf5_ok_20 x hQ i hi h.1 (by rw [nfc5_len_20]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 713 nfc5_21 nf5_ok_21 x hQ i hi h.1 (by rw [nfc5_len_21]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 758 nfc5_22 nf5_ok_22 x hQ i hi h.1 (by rw [nfc5_len_22]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 803 nfc5_23 nf5_ok_23 x hQ i hi h.1 (by rw [nfc5_len_23]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 837 nfc5_24 nf5_ok_24 x hQ i hi h.1 (by rw [nfc5_len_24]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 872 nfc5_25 nf5_ok_25 x hQ i hi h.1 (by rw [nfc5_len_25]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 909 nfc5_26 nf5_ok_26 x hQ i hi h.1 (by rw [nfc5_len_26]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 945 nfc5_27 nf5_ok_27 x hQ i hi h.1 (by rw [nfc5_len_27]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 989 nfc5_28 nf5_ok_28 x hQ i hi h.1 (by rw [nfc5_len_28]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1030 nfc5_29 nf5_ok_29 x hQ i hi h.1 (by rw [nfc5_len_29]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1074 nfc5_30 nf5_ok_30 x hQ i hi h.1 (by rw [nfc5_len_30]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1128 nfc5_31 nf5_ok_31 x hQ i hi h.1 (by rw [nfc5_len_31]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1164 nfc5_32 nf5_ok_32 x hQ i hi h.1 (by rw [nfc5_len_32]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1211 nfc5_33 nf5_ok_33 x hQ i hi h.1 (by rw [nfc5_len_33]; exact h.2)
  · exact nfRange_sound nfTree5 39 1287 nfDelta5 stdc5 Qd keys5 keys_ok5 1259 nfc5_34 nf5_ok_34 x hQ i hi h.1 (by rw [nfc5_len_34]; exact h.2)

theorem nfValid4b {R : Type*} [CommRing R] (x : Fin 9 → R) (hx : OnQ x) : NFValid nfTree4b stdc nfDelta x :=
  nfValid_of_sameRows nfTree nfTree4b stdc nfDelta same4b x (nfValid x hx)

theorem nfValid_id2 {R : Type*} [CommRing R] (x : Fin 9 → R) : NFValid idTree2 stdcId2 1 x :=
  nfValid_of_idOK _ _ id2_ok x

theorem nfValid_id3 {R : Type*} [CommRing R] (x : Fin 9 → R) : NFValid idTree3 stdcId3 1 x :=
  nfValid_of_idOK _ _ id3_ok x

end LSG.Jac
