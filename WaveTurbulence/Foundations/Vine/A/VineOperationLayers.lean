/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue1
/-! The actual inherited core layer commutes with each admissible LF
operation, retaining all choices of the actual reconstruction. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Every actual LF operation preserves the inherited regular-reconstruction core layer. -/
theorem operation_coreLayer {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i) (b : GBranch A.skeleton.tree) :
    RegRed.coreLayer op.output.layered op.output.data op.output.plain op.output.decodes ((operationMolIso op).e b) =
      RegRed.coreLayer A.layered A.data A.plain A.decodes b := by
  cases op with
  | mk hc he ht hq ε C =>
    have h := inducedPrelayer_output C b
    cases ε <;> exact h

/-- Actual core layers transport through every composed LF batch map. -/
theorem BatchIso.coreLayer {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (b : GBranch A.skeleton.tree) :
    RegRed.coreLayer B.layered B.data B.plain B.decodes (F.e b) =
      RegRed.coreLayer A.layered A.data A.plain A.decodes b := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih b
  | @apply L A B i op J h ih =>
    exact (ih ((operationMolIso op).e b)).trans (operation_coreLayer op b)

end WaveTurbulence.VineA
