/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.Type1Stability
public import WaveTurbulence.Foundations.RegStruct.PermutationBlocks


/-! # Type-1 code contexts: exact B-step shapes and pair-list congruence

The permutation lemmas below are congruence statements for arbitrary replacement
code data and an arbitrary inserted list N. The source B theorem must supply
that local permutation by its actual recursive proof, not as a source premise.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- A red-component B-step changes only the red code. -/
theorem insertMiniCouple_type1_red (c : MiniCplCode) (r g d : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b)
    (ht : target ∈ coupleNodes r (redFrame c a b).1 (redFrame c a b).2) :
    insertMiniCouple (.type1 c r g d) a b target m =
      .type1 c (insertMiniCouple r (redFrame c a b).1 (redFrame c a b).2 target m) g d := by
  have hsep := red_node_separation c r a b target hab ht
  have hg := insertMiniCouple_of_incomparable g _ _ target m hsep.1.1 hsep.1.2
  have hd := insertMiniCouple_of_incomparable d _ _ target m hsep.2.1 hsep.2.2
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [hg,hd]

/-- A green-component B-step changes only the green code. -/
theorem insertMiniCouple_type1_green (c : MiniCplCode) (r g d : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b)
    (ht : target ∈ coupleNodes g (greenFrame a b).1 (greenFrame a b).2) :
    insertMiniCouple (.type1 c r g d) a b target m =
      .type1 c r (insertMiniCouple g (greenFrame a b).1 (greenFrame a b).2 target m) d := by
  have hsep := green_node_separation c g a b target hab ht
  have hr := insertMiniCouple_of_incomparable r _ _ target m hsep.1.1 hsep.1.2
  have hd := insertMiniCouple_of_incomparable d _ _ target m hsep.2.1 hsep.2.2
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [hr,hd]

/-- A blue-component B-step changes only the blue code. -/
theorem insertMiniCouple_type1_blue (c : MiniCplCode) (r g d : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b)
    (ht : target ∈ coupleNodes d (blueFrame c a b).1 (blueFrame c a b).2) :
    insertMiniCouple (.type1 c r g d) a b target m =
      .type1 c r g (insertMiniCouple d (blueFrame c a b).1 (blueFrame c a b).2 target m) := by
  have hsep := blue_node_separation c d a b target hab ht
  have hr := insertMiniCouple_of_incomparable r _ _ target m hsep.1.1 hsep.1.2
  have hg := insertMiniCouple_of_incomparable g _ _ target m hsep.2.1 hsep.2.2
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [hr,hg]

/-- Pair-list congruence for arbitrary replacement data in the red component. -/
theorem type1_red_constructor_perm (c : MiniCplCode) (r r' g d : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (N : List ((Fin w × Path) × (Fin w × Path)))
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes r (redFrame c a b).1 (redFrame c a b).2)
    (hlocal : (r'.pairsAt (redFrame c a b).1 (redFrame c a b).2).Perm
      ((r.pairsAt (redFrame c a b).1 (redFrame c a b).2).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegCpl.type1 c r' g d).pairsAt a b).Perm
      (((RegCpl.type1 c r g d).pairsAt a b).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N) := by
  have hsep := red_node_separation c r a b target hab ht
  have hg := relocate_couple_pairs_fixed g _ _ target m hsep.1.1 hsep.1.2
  have hd := relocate_couple_pairs_fixed d _ _ target m hsep.2.1 hsep.2.2
  simp only [RegCpl.pairsAt,List.map_append]
  rw [hg,hd]
  exact perm_lift_first _ _ _ _ _ hlocal

/-- Pair-list congruence for arbitrary replacement data in the green component. -/
theorem type1_green_constructor_perm (c : MiniCplCode) (r g g' d : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (N : List ((Fin w × Path) × (Fin w × Path)))
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes g (greenFrame a b).1 (greenFrame a b).2)
    (hlocal : (g'.pairsAt (greenFrame a b).1 (greenFrame a b).2).Perm
      ((g.pairsAt (greenFrame a b).1 (greenFrame a b).2).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegCpl.type1 c r g' d).pairsAt a b).Perm
      (((RegCpl.type1 c r g d).pairsAt a b).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N) := by
  have hsep := green_node_separation c g a b target hab ht
  have hr := relocate_couple_pairs_fixed r _ _ target m hsep.1.1 hsep.1.2
  have hd := relocate_couple_pairs_fixed d _ _ target m hsep.2.1 hsep.2.2
  simp only [RegCpl.pairsAt,List.map_append]
  rw [hr,hd]
  exact perm_lift_middle _ _ _ _ _ hlocal

/-- Pair-list congruence for arbitrary replacement data in the blue component. -/
theorem type1_blue_constructor_perm (c : MiniCplCode) (r g d d' : RegCpl)
    (a b target : Fin w × Path) (m : MiniTreeCode) (N : List ((Fin w × Path) × (Fin w × Path)))
    (hab : IncompAddr a b) (ht : target ∈ coupleNodes d (blueFrame c a b).1 (blueFrame c a b).2)
    (hlocal : (d'.pairsAt (blueFrame c a b).1 (blueFrame c a b).2).Perm
      ((d.pairsAt (blueFrame c a b).1 (blueFrame c a b).2).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N)) :
    ((RegCpl.type1 c r g d').pairsAt a b).Perm
      (((RegCpl.type1 c r g d).pairsAt a b).map (fun p =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone p.2)) ++ N) := by
  have hsep := blue_node_separation c d a b target hab ht
  have hr := relocate_couple_pairs_fixed r _ _ target m hsep.1.1 hsep.1.2
  have hg := relocate_couple_pairs_fixed g _ _ target m hsep.2.1 hsep.2.2
  simp only [RegCpl.pairsAt,List.map_append]
  rw [hr,hg]
  exact perm_lift_last _ _ _ _ _ hlocal

end WaveTurbulence.Reg.Skeleton.BContext
