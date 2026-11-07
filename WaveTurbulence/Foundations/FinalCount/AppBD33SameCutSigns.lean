/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD33CutData
import Mathlib.Tactic

/-! # Same-direction boundary signs in the 3D3-4G figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_cut_signs_same (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hsame : ¬AppbD33BoundaryOpposite M r) :
    appbCutSign M r.removedAtoms (r.edge ⟨2,by decide⟩).val =
      appbCutSign M r.removedAtoms (r.edge ⟨3,by decide⟩).val := by
  have h2 := r.edge_atom_mem_removed_iff_fst ⟨2,by decide⟩ (by decide) (by decide)
  have h3 := r.edge_atom_mem_removed_iff_fst ⟨3,by decide⟩ (by decide) (by decide)
  change (M.atom (r.edge ⟨2,by decide⟩).val ∈ r.removedAtoms ↔ M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1) at h2
  change (M.atom (r.edge ⟨3,by decide⟩).val ∈ r.removedAtoms ↔ M.atom (r.edge ⟨3,by decide⟩).val = r.vertex 2) at h3
  unfold AppbD33BoundaryOpposite AppbOppositeFrom at hsame
  by_cases ha : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1 <;>
    by_cases hb : M.atom (r.edge ⟨3,by decide⟩).val = r.vertex 2
  all_goals simp_all [appbCutSign]

end WaveTurbulence.Mole
