/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NestedReplacement

/-! # Ordered single-child replacement in the three-child tree constructor -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem replaceAt_node3_child (f : Fin 3 → TTree) (i : Fin 3) (p : Path) (t : TTree) :
    Comb.replaceAt (node3 f) ([i] ++ p) t =
      node3 (Function.update f i (Comb.replaceAt (f i) p t)) := by
  fin_cases i <;> simp [node3,Comb.replaceAt,Function.update]

end WaveTurbulence.Reg.Skeleton
