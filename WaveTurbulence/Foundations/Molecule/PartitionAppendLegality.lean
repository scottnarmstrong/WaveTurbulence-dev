/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PartitionConstructors

/-! # Legality of actual concatenated index-block partitions -/

public section
namespace WaveTurbulence.Reg.PairPartition

/-- Noncrossing partitions concatenate on their actual successive label blocks. -/
theorem append_legal {n m : ℕ} (P : PairPartition n) (Q : PairPartition m) (hP : P.Legal) (hQ : Q.Legal) :
    (P.append Q).Legal := by
  intro a b c d
  refine Fin.addCases (fun A => ?_) (fun A => ?_) a <;>
    refine Fin.addCases (fun B => ?_) (fun B => ?_) b <;>
    refine Fin.addCases (fun C => ?_) (fun C => ?_) c <;>
    refine Fin.addCases (fun D => ?_) (fun D => ?_) d
  all_goals
    intro hAB hBC hCD hAC hBD
    simp only [append_pair_left,append_pair_right] at hAC hBD
  all_goals
    have hACv := congrArg Fin.val hAC
    have hBDv := congrArg Fin.val hBD
  all_goals
    simp only [Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd] at hAB hBC hCD hACv hBDv
  all_goals first
    | exact hP A B C D hAB hBC hCD (Fin.ext hACv) (Fin.ext hBDv)
    | exact hQ A B C D (by omega) (by omega) (by omega)
        (Fin.ext (Nat.add_left_cancel hACv)) (Fin.ext (Nat.add_left_cancel hBDv))
    | omega

end WaveTurbulence.Reg.PairPartition
