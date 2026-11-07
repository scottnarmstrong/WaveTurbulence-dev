/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBS33LeftParameters
public import WaveTurbulence.Foundations.FinalCount.AppBFrameProjectionReindex
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFixedTuples
import Mathlib.Tactic

/-! # The new bond in the 35 component fixes the copied boundary coordinate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbS33LeftNewDart {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r) :
    AppbSideDart (r.directedPostWithBond 3 5 ⟨1,by decide⟩) (appbS33Side r) := by
  refine ⟨Sum.inr true,?_⟩
  have hs := appb_s33_side_labels_topology M r (appb_s33_splitTopology_of_geometry hg)
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · exact hs.2.2.1
  · exact hs.2.2.2.2.1

theorem appb_s33_left_copied_label {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    {d : ℕ} (κ : D → (Fin d → ℤ)) :
    appbS33LeftLabels r κ (appbS33LeftNewDart r hg) = r.localLabels κ ⟨1,by decide⟩ := rfl

/-- The internal pair consists of coordinates 0 and 2; coordinate 1 is
already carried by the new bond on the left component. -/
def appbS33ReinsertFrame {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) : AppbTripleFrame r (r.vertex 1) :=
  (appbS33Frame r).reindex (Equiv.swap 1 2)

theorem appb_s33_reinsert_frame_indices {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33.pattern) :
    (appbS33ReinsertFrame r).index 0 = ⟨0,by decide⟩ ∧
    (appbS33ReinsertFrame r).index 1 = ⟨2,by decide⟩ ∧
    (appbS33ReinsertFrame r).index 2 = ⟨1,by decide⟩ := by
  norm_num [appbS33ReinsertFrame,AppbTripleFrame.reindex,appbS33Frame,appbFirstThreeEmbedding,Equiv.swap_apply_def]

end WaveTurbulence.Mole
