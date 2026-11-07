/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCombinedFrames
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # The original star triple in all combined 3R-2G coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbR3Frame {M : Molecule V D} (r : AppbRealization M AppbPatternKind.r3.pattern) :
    AppbTripleFrame r (r.vertex 1) where
  index := (Equiv.refl (Fin 3)).toEmbedding
  incidence := by
    intro j
    rw [r.edge_incidence _ 1 (by decide)]
    fin_cases j <;> decide
  other := by
    intro i hi
    exact False.elim (hi i rfl)

noncomputable def appbR32Frame {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (π : Equiv.Perm (Fin 3)) : AppbTripleFrame (r.combinedRemoval s v0) (r.vertex 1) :=
  ((appbR3Frame r).combinedLeft r s v0 (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.r3.pattern.removed by decide))).reindex π

theorem appb_r32_frame_index {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (π : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (appbR32Frame r s v0 π).index j = r.combinedLeftIndex s (π j) := rfl

theorem appb_r32_center_removed {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms) :
    r.vertex 1 ∈ (r.combinedRemoval s v0).removedAtoms := by
  rw [r.combinedRemoval_removed]
  exact mem_union_left _ (mem_image_of_mem _ (show 1 ∈ AppbPatternKind.r3.pattern.removed by decide))

theorem appb_r32_frame_labels {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (π : Equiv.Perm (Fin 3)) (κ : D → K) (j : Fin 3) :
    (appbR32Frame r s v0 π).project ((r.combinedRemoval s v0).localLabels κ) j =
      r.localLabels κ (π j) := r.combined_labels_left s v0 κ (π j)

theorem appb_r32_first_labels_eq_of_frame {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (π : Equiv.Perm (Fin 3)) (κ κ' : D → K)
    (he : (appbR32Frame r s v0 π).project ((r.combinedRemoval s v0).localLabels κ) =
      (appbR32Frame r s v0 π).project ((r.combinedRemoval s v0).localLabels κ')) :
    r.localLabels κ = r.localLabels κ' := by
  change (fun j : Fin 3 => r.localLabels κ j) = (fun j : Fin 3 => r.localLabels κ' j)
  funext j
  have hh := congrFun he (π.symm j)
  rw [appb_r32_frame_labels,appb_r32_frame_labels,π.apply_symm_apply] at hh
  exact hh

end WaveTurbulence.Mole
