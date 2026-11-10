/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.ChainInsertionLower


/-! # Operation B at either root of a framed sub-couple

Both roots may lie in one original tree. Incomparability supplies the local
address frame; positive/negative roles refer to the decoded couple's own roots.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- Inserting B at a positive sub-couple root preserves all literal pair data. -/
theorem insertMiniCouple_left_pairs (Q : RegCpl) (a b : Fin w × Path) (m : MiniTreeCode)
    (hab : IncompAddr a b) :
    ((insertMiniCouple Q a b a m).pairsAt a b).Perm
      ((Q.pairsAt a b).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone p.2)) ++
        (miniChain m).pairsAt 1 a) := by
  rw [insertMiniCouple_at_left,type2_left_pairsAt,miniChain_lonePath]
  have ha : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) a :=
    relocate_respects_desc _ _ _ _ ⟨rfl,List.prefix_refl _⟩
  have hb : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) b :=
    relocate_respects_incomparable _ _ _ _ hab.1 hab.2
  have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate a m.c m.lone) a b ha hb
  rw [relocate_self,relocate_eq_of_not_below a m.c m.lone b hab.1] at hm
  rw [hm]
  exact List.perm_append_comm

/-- Inserting B at a negative sub-couple root has the corresponding negative mini-tree sign. -/
theorem insertMiniCouple_right_pairs (Q : RegCpl) (a b : Fin w × Path) (m : MiniTreeCode)
    (hab : IncompAddr a b) :
    ((insertMiniCouple Q a b b m).pairsAt a b).Perm
      ((Q.pairsAt a b).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate b m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate b m.c m.lone p.2)) ++
        (miniChain m).pairsAt (-1) b) := by
  have hne : b ≠ a := by
    intro he
    subst b
    exact hab.1 ⟨rfl,List.prefix_refl _⟩
  rw [insertMiniCouple_at_right Q a b hne,type2_right_pairsAt,miniChain_lonePath]
  have ha : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate b m.c m.lone) a :=
    relocate_respects_incomparable _ _ _ _ hab.2 hab.1
  have hb : RespectsAt (WaveTurbulence.Reg.Skeleton.relocate b m.c m.lone) b :=
    relocate_respects_desc _ _ _ _ ⟨rfl,List.prefix_refl _⟩
  have hm := couple_pairsAt_map_local Q (WaveTurbulence.Reg.Skeleton.relocate b m.c m.lone) a b ha hb
  rw [relocate_self,relocate_eq_of_not_below b m.c m.lone a hab.2] at hm
  rw [hm]
  exact List.perm_append_comm

end WaveTurbulence.Reg.Skeleton.BContext
