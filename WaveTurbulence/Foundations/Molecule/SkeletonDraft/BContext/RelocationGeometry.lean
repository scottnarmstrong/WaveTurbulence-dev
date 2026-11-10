/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality


/-! # Local geometry of the source operation-B relocation map

Relocation respects path extension below a descendant root or below a root
incomparable with the insertion node. It is not claimed to respect extension
at a strict ancestor of that node.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

theorem relocate_eq_of_not_below (a : Fin w × Path) (c l : Fin 3) (z : Fin w × Path)
    (h : ¬ Below a z) : WaveTurbulence.Reg.Skeleton.relocate a c l z = z := by
  dsimp only [Below] at h
  rw [WaveTurbulence.Reg.Skeleton.relocate,ite_eq_right h]

/-- Below a descendant root, relocation is a fixed prefix change. -/
theorem relocate_respects_desc (a b : Fin w × Path) (c l : Fin 3) (h : Below a b) :
    RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a c l) b := by
  intro p
  have he : Below a (addrExt b p) := below_trans h (below_extend b p)
  dsimp only [Below] at h he
  rw [WaveTurbulence.Reg.Skeleton.relocate,ite_eq_left he,WaveTurbulence.Reg.Skeleton.relocate,ite_eq_left h]
  obtain ⟨r,hr⟩ := h.2
  simp only [addrExt]
  rw [← hr]
  simp only [List.append_assoc,List.drop_left]

/-- Below an incomparable root, relocation is the identity on its full represented subtree. -/
theorem relocate_respects_incomparable (a b : Fin w × Path) (c l : Fin 3)
    (hab : ¬ Below a b) (hba : ¬ Below b a) : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a c l) b := by
  intro p
  rw [relocate_eq_of_not_below _ _ _ _ (not_below_extension hab hba p),
    relocate_eq_of_not_below _ _ _ _ hab]

/-- Relocation respects all extensions from a root which is not above the insertion. -/
theorem relocate_respectsAt_of_not_below (target root : Fin w × Path) (c l : Fin 3)
    (h : ¬ Below root target) : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate target c l) root := by
  by_cases ht : Below target root
  · exact relocate_respects_desc target root c l ht
  · exact relocate_respects_incomparable target root c l ht h

end WaveTurbulence.Reg.Skeleton.BContext
