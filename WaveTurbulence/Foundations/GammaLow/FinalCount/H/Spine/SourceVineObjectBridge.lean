/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceVineObjectBridge`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Definition-preserving transport of the spine's designated objects to the proved VINES API. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- In the low world main's two copies of the vine objects are one (`Src`): the bridge is the identity. -/
theorem Src.Chain.toVine {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : Src.Chain Src.γL M S a b n := h

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Chain.toVine := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Chain.toVine

theorem Src.IsVC.toVine {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsVC Src.γL M S a b) : Src.IsVC Src.γL M S a b := h

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.IsVC.toVine := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.IsVC.toVine

def Src.HyperLikeRealization.toVine {M : Molecule V D} {S : Finset V} {a b : V}
    (R : Src.HyperLikeRealization Src.γL M S a b) : Src.HyperLikeRealization Src.γL M S a b where
  added := R.added
  ends_eq := R.ends_eq
  adjoint := R.adjoint.toVine

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.HyperLikeRealization.toVine := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.HyperLikeRealization.toVine
def Src.VineLikeObject.toVine {M : Molecule V D} {S : Finset V} {a b : V} :
    Src.VineLikeObject Src.γL M S a b → Src.VineLikeObject Src.γL M S a b
  | .vc h => .vc h.toVine
  | .hyper R => .hyper R.toVine

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.toVine := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.toVine
theorem Src.VineLikeObject.toVine_isGap {M : Molecule V D} {S : Finset V} {a b : V}
    (P : Src.VineLikeObject Src.γL M S a b) {d : ℕ} (L : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ)) (r : Mom d) :
    P.toVine.IsGap L base κ r ↔ P.IsGap L base κ r := by
  cases P <;> rfl

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.toVine_isGap := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.toVine_isGap
theorem Src.VineLikeObject.toVine_isContained {M : Molecule V D} {S A : Finset V} {a b x y : V}
    (P : Src.VineLikeObject Src.γL M A x y) (Q : Src.VineLikeObject Src.γL M S a b) :
    P.toVine.IsContained Q.toVine ↔ P.IsContained Q := by
  cases P <;> cases Q <;> rfl

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.toVine_isContained := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.toVine_isContained
theorem Src.Object.contained_atoms_subset {M : Molecule V D} (P Q : Src.Object Src.γL M) (h : P.IsContained Q) :
    P.atoms ⊆ Q.atoms := by
  exact (P.shape.toVine.atoms_subset Q.shape.toVine)
    ((P.shape.toVine_isContained Q.shape).mpr h)

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.contained_atoms_subset := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.contained_atoms_subset
end WaveTurbulence.GammaLow.FinalCount.H
