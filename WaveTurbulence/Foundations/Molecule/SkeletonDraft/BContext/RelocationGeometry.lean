/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegStructWork
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RootAddressMaps


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

/-- Every moved address remains below the insertion node. -/
theorem relocate_below (a z : Fin w × Path) (c l : Fin 3) (h : Below a z) :
    Below a (WaveTurbulence.Reg.Skeleton.relocate a c l z) := by
  dsimp only [Below] at h
  rw [WaveTurbulence.Reg.Skeleton.relocate,ite_eq_left h]
  refine ⟨h.1,?_⟩
  change a.2 <+: (a.2 ++ [c,l]) ++ z.2.drop a.2.length
  rw [List.append_assoc]
  exact List.prefix_append _ _

/-- Inserting two path slots is injective on the entire raw address space. -/
theorem relocate_injective (a : Fin w × Path) (c l : Fin 3) :
    Function.Injective (WaveTurbulence.Reg.Skeleton.relocate a c l) := by
  intro x y hxy
  by_cases hx : Below a x
  · by_cases hy : Below a y
    · dsimp only [Below] at hx hy
      have hp := congrArg Prod.snd hxy
      rw [WaveTurbulence.Reg.Skeleton.relocate,ite_eq_left hx,WaveTurbulence.Reg.Skeleton.relocate,ite_eq_left hy] at hp
      obtain ⟨r,hr⟩ := hx.2
      obtain ⟨s,hs⟩ := hy.2
      change (a.2 ++ [c,l]) ++ x.2.drop a.2.length =
        (a.2 ++ [c,l]) ++ y.2.drop a.2.length at hp
      rw [← hr,← hs] at hp
      simp only [List.drop_left] at hp
      have hrs := List.append_cancel_left hp
      apply Prod.ext (hx.1.trans hy.1.symm)
      rw [← hr,← hs,hrs]
    · have hb := relocate_below a x c l hx
      rw [hxy,relocate_eq_of_not_below a c l y hy] at hb
      exact (hy hb).elim
  · by_cases hy : Below a y
    · have hb := relocate_below a y c l hy
      rw [← hxy,relocate_eq_of_not_below a c l x hx] at hb
      exact (hx hb).elim
    · rw [relocate_eq_of_not_below a c l x hx,relocate_eq_of_not_below a c l y hy] at hxy
      exact hxy

/-- Relocation respects all extensions from a root which is not above the insertion. -/
theorem relocate_respectsAt_of_not_below (target root : Fin w × Path) (c l : Fin 3)
    (h : ¬ Below root target) : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate target c l) root := by
  by_cases ht : Below target root
  · exact relocate_respects_desc target root c l ht
  · exact relocate_respects_incomparable target root c l ht h

end WaveTurbulence.Reg.Skeleton.BContext
