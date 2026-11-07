/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103StarEnumerations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.PositiveQuarticCutGeometry
public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # Actual geometrical outputs of the Proposition10.3 good selector

These constructors contain only actual graph data. The source selector
produces them from the literal source graph conditions and inspected R
step; no source endpoint assumes this output or a local counting estimate.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The internally produced stars, OLD cuts, and circuit loss for a good
configuration. Constructor shapes match the six actual local source counts. -/
inductive ActualGoodConfiguration (M : Molecule V D) (a : V) : Prop
  | sharedCubic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x : D)
      (A : Star3Remainder M a x) (B : Star3Remainder M b (M.mate x))
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3) :
      ActualGoodConfiguration M a
  | affineCubic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x p : D)
      (A : Star3Remainder M a x) (B : Star3Remainder M b p)
      (px : p ≠ x) (pmx : p ≠ M.mate x)
      (inside : Bool) (U : Finset V) (hU : U ⊆ M.atoms)
      (cut : boundaryDarts M U = {if inside then p else M.mate p,M.mate x})
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3) :
      ActualGoodConfiguration M a
  | affineQuartic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x p : D)
      (A : Star3Remainder M a x) (B : Star4Remainder M b (M.mate x) p)
      (py : p ≠ A.y) (U : Finset V) (hU : U ⊆ M.atoms)
      (cut : boundaryDarts M U = {M.mate p,M.mate A.y})
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3) :
      ActualGoodConfiguration M a
  | positiveQuartic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x p q : D)
      (A : Star3Remainder M a x) (B : Star4Remainder M b p q)
      (same : M.out B.s = M.out B.r)
      (cutp : FirstProfileCut M x A.y A.z p) (cutq : FirstProfileCut M x A.y A.z q)
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3) :
      ActualGoodConfiguration M a
  | threeCutQuartic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x p q : D)
      (A : Star3Remainder M a x) (B : Star4Remainder M b p q)
      (pmx : p ≠ M.mate x) (qmx : q ≠ M.mate x)
      (U₀ U₁ U₂ : Finset V) (hU₀ : U₀ ⊆ M.atoms) (hU₁ : U₁ ⊆ M.atoms) (hU₂ : U₂ ⊆ M.atoms)
      (cut₀ : boundaryDarts M U₀ = {p,q,M.mate x})
      (cut₁ : boundaryDarts M U₁ = {M.mate p,M.mate A.y})
      (cut₂ : boundaryDarts M U₂ = {M.mate q,M.mate A.z})
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 3) :
      ActualGoodConfiguration M a
  | sevenLabelQuartic (b : V) (hb : b ∈ M.atoms) (hab : a ≠ b) (x p q : D)
      (A : Star3Remainder M a x) (B : Star4Remainder M b p q)
      (xp : x ≠ p) (xq : x ≠ q)
      (po : M.out p = false) (qo : M.out q = true)
      (ro : M.out B.r = false) (so : M.out B.s = true)
      (U : Finset V) (hU : U ⊆ M.atoms)
      (cut : boundaryDarts M U = {M.mate x,M.mate p,M.mate q})
      (loss : M.circuitRank - (eraseAtoms M {a,b}).circuitRank = 4) :
      ActualGoodConfiguration M a

end WaveTurbulence.MoleProp
