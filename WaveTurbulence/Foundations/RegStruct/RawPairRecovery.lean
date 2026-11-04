/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type2TerminalRecovery

/-! # The actual carrier recovers the oriented raw pair list up to permutation -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Every literal raw pair has its positive endpoint first. -/
theorem rawPair_signs (C : RegCpl) (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ C.raw.2) :
    nodeSign ![1,-1] p.1 = 1 ∧ nodeSign ![1,-1] p.2 = -1 :=
  couple_pairsAt_signs C ![1,-1] (0,[]) (1,[]) nodeSign_root_zero nodeSign_root_one p hp

/-- Equal decoded carriers determine the same positive/negative oriented raw pairs. -/
theorem rawPair_mem_iff_of_carrier_eq {C D : RegCpl} (he : decodedCouple C = decodedCouple D)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) : p ∈ C.raw.2 ↔ p ∈ D.raw.2 := by
  have hforward : ∀ (C D : RegCpl), decodedCouple C = decodedCouple D → p ∈ C.raw.2 → p ∈ D.raw.2 := by
    intro C D he hp
    have hu := (symmPairs_eq_of_carrier_eq he p).mp ((mem_symmPairs_iff _ _).mpr (Or.inl hp))
    rcases (mem_symmPairs_iff _ _).mp hu with hd | hd
    · exact hd
    · have hsC := (rawPair_signs C p hp).1
      have hsD := (rawPair_signs D p.swap hd).2
      change nodeSign ![1,-1] p.1 = -1 at hsD
      have hh : (1 : ℤˣ) = -1 := hsC.symm.trans hsD
      exact (by decide : (1 : ℤˣ) ≠ -1) hh |>.elim
  exact ⟨hforward C D he,hforward D C he.symm⟩

/-- Multiplicity and orientation are both recovered from the actual carrier. -/
theorem rawPairs_perm_of_carrier_eq {C D : RegCpl} (he : decodedCouple C = decodedCouple D) :
    C.raw.2.Perm D.raw.2 :=
  (List.perm_ext_iff_of_nodup (decodedPair_nodup C) (decodedPair_nodup D)).mpr
    (fun p => rawPair_mem_iff_of_carrier_eq he p)

end WaveTurbulence.Reg
