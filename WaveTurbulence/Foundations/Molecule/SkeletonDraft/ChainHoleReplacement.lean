/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs
public import WaveTurbulence.Foundations.Molecule.DominantChains

/-! # Replacing exactly the lone subtree of a regular chain context -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem replaceAt_plug_lone_append (X : RegChain) (ζ : ℤˣ) (t u : TTree) (p : Path) :
    Comb.replaceAt (X.plug ζ t) (X.lonePath ++ p) u = X.plug ζ (Comb.replaceAt t p u) := by
  cases X with
  | nil => simp [RegChain.plug,RegChain.lonePath]
  | pair k r g i s =>
    obtain ⟨c,b⟩ := k
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug,RegChain.lonePath,node3,MiniTreeCode.lone,
        Comb.replaceAt,List.append_assoc,replaceAt_plug_lone_append i,replaceAt_plug_lone_append s]
termination_by structural X

theorem replaceAt_plug_lonePath (X : RegChain) (ζ : ℤˣ) (t u : TTree) :
    Comb.replaceAt (X.plug ζ t) X.lonePath u = X.plug ζ u := by
  have h := replaceAt_plug_lone_append X ζ t u []
  simpa only [List.append_nil,Comb.replaceAt] using h

end WaveTurbulence.Reg.Skeleton
