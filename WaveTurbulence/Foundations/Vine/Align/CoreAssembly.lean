/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Assembly
/-! Choose valid chain labels that recognize every geometrically core vine.
The source core carrier is existential in the vine type. This normalization
retains every atom set and both ordered joints, and retains the original label
when no core label exists. It adds no assumption to the output-set bridge. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS2 VineEstS3 VineEstS4 VineA RedSplice Stage1 Twist RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {X : VineType}

noncomputable def coreLabel (X : VineType) (U : Finset (GBranch G.tree)) (a b : GBranch G.tree) : VineType := by
  classical
  exact if h : ∃ Y, IsCoreCLVine G Y U a b then h.choose else X

theorem coreLabel_vine (hV : G.molecule.IsVine X U a b) :
    G.molecule.IsVine (coreLabel X U a b) U a b := by
  classical
  unfold coreLabel
  split_ifs with h
  · exact h.choose_spec.1
  · exact hV

theorem coreLabel_core (h : ∃ Y, IsCoreCLVine G Y U a b) :
    IsCoreCLVine G (coreLabel X U a b) U a b := by
  classical
  simp only [coreLabel, dite_eq_left h]
  exact h.choose_spec

/-- Same chain and region, with a core label whenever its geometric vine is core. -/
noncomputable def coreAssembly {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) : CLChainAssembly G R n :=
  match B with
  | .single hV R => .single (coreLabel_vine hV) R
  | .append B hT hi hU R => .append (coreAssembly B) (coreLabel_vine hT) hi hU R

/-- Each normalized piece recognizes exactly the existential core carrier. -/
theorem coreAssembly_piece_core (B : CLChainAssembly G R n) (i : Fin n)
    (h : ∃ Y, IsCoreCLVine G Y (assemblyPieceAt (coreAssembly B) i).atoms
      (assemblyPieceAt (coreAssembly B) i).upper (assemblyPieceAt (coreAssembly B) i).lower) :
    IsCoreCLVine G (assemblyPieceAt (coreAssembly B) i).vineType (assemblyPieceAt (coreAssembly B) i).atoms
      (assemblyPieceAt (coreAssembly B) i).upper (assemblyPieceAt (coreAssembly B) i).lower := by
  induction B with
  | single hV R => exact coreLabel_core h
  | append B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact coreLabel_core h
    · exact ih k h

/-- Actual unit assemblies with core labels chosen by the source's existential criterion.  B1a: the Mk-general
family (the units are the runs of the marked groups); main's `alignedAssembly hM σ` is its value at `Mk = ∅`. -/
noncomputable def alignedAssemblyMk (hM : G.molecule.IsMolecule) (σ : Prescription G) (Mk : Set (CLVine G))
    (j : Fin (unitBlocks G σ Mk).length) := coreAssembly (Represents.unitAssembly hM σ j)

/-- Actual unit assemblies with core labels chosen by the source's existential criterion. -/
noncomputable abbrev alignedAssembly (hM : G.molecule.IsMolecule) (σ : Prescription G) :=
  alignedAssemblyMk hM σ ∅

end WaveTurbulence.VineAlign
