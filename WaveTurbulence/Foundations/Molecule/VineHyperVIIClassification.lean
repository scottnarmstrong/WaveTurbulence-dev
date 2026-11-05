/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperVIICapData
public import WaveTurbulence.Foundations.Molecule.VineCapAdjointClassification
import Mathlib.Tactic

/-! # Source hyper-vine-like containment classification in type VII -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, HV/HVC inside one type-VII vine: the designated
adjoint is exactly two concatenated double bonds or a pinned type-V vine.
All cap rows, selected-prefix shape, labels and graph data are constructed
from source containment. This uses the current B2 family in the short-case
exclusion; see F69 and the handoff. No gap premise is necessary in this case. -/
theorem hyperLike_in_typeVII_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .VII S a b)
    (hAS : A ⊆ S) (h : IsHV M A x y ∨ IsHVC M A x y) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp h
  have hH : Mole.IsHyperBlock M A x y := ⟨e,he,hVC.1⟩
  obtain ⟨n,r,⟨C⟩⟩ := typeVII_hyper_cap_data M hM hV hAS hH
  exact C.hyperLike_adjoint_classification hM h

end WaveTurbulence.Vine
