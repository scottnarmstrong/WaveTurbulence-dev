/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions

/-! # The first distinct ordered child separates two incomparable source paths -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem incomparable_paths_split (p q : Path) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    ∃ r : Path, ∃ i j : Fin 3, ∃ s t : Path,
      p = r ++ i :: s ∧ q = r ++ j :: t ∧ i ≠ j := by
  induction p generalizing q with
  | nil => exact (hpq List.nil_prefix).elim
  | cons i p ih =>
    cases q with
    | nil => exact (hqp List.nil_prefix).elim
    | cons j q =>
      by_cases hij : i = j
      · subst j
        have hp : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.mpr ⟨rfl,h⟩)
        have hq : ¬ q <+: p := fun h => hqp (List.cons_prefix_cons.mpr ⟨rfl,h⟩)
        obtain ⟨r,a,b,s,t,he,hf,hab⟩ := ih q hp hq
        exact ⟨i::r,a,b,s,t,congrArg (List.cons i) he,congrArg (List.cons i) hf,hab⟩
      · exact ⟨[],i,j,p,q,rfl,rfl,hij⟩

end WaveTurbulence.Reg.Skeleton
