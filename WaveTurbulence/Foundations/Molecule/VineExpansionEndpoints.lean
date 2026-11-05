/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEndpointBounds
public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
import Mathlib.Tactic

/-! # Every expanded template bond has allocated atom endpoints -/

public section
namespace WaveTurbulence.Vine

/-- Literal expansion never creates a bond outside its finite atom range. -/
theorem expand_endpoints (X : VineType) (k : List ℕ) :
    ∀ p ∈ (X.expand k).bonds,p.1<(X.expand k).n ∧ p.2<(X.expand k).n := by
  apply fold_insertRungs_endpoints _ _ (template_endpoints X)
  intro sk hsk
  have hs := (List.of_mem_zip hsk).1
  exact template_slot_endpoints X sk.1 hs

end WaveTurbulence.Vine
