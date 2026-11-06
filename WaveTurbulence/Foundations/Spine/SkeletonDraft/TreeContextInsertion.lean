/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.NestedReplacement

/-! # Inserting a chain at a subtree inside an already replaced valid frame -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem insert_chain_under_frame {t t₀ : TTree} {p : Path} (h : Comb.subtree t p = some t₀)
    (u : TTree) (q : Path) (X : RegChain) (ζ : ℤˣ) :
    Comb.replaceAt (Comb.replaceAt t p u) (p ++ q)
      (X.plug ζ ((Comb.replaceAt t p u).subtreeAt (p ++ q))) =
        Comb.replaceAt t p (Comb.replaceAt u q (X.plug ζ (u.subtreeAt q))) := by
  rw [subtreeAt_replaceAt_descendant h,replaceAt_descendant h]

end WaveTurbulence.Reg.Skeleton
