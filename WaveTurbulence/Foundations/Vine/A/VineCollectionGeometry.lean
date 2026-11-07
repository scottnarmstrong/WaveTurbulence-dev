/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineObjectGeometry
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
/-! Actual C1 indexed geometry: supports determine the shape tag and unordered joints. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Mapping the chosen object never rechooses its ordinary/hyper constructor. -/
theorem mapObject_hyperTag {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {N : Molecule V' D'}
    (E : MolIso M N) (O : Object M) : objectHyperTag (mapObject E O) = objectHyperTag O := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape <;> rfl

/-- The actual independently chosen collection objects have corresponding unordered joints and shape tags. -/
theorem BatchIso.collectionIndexEquiv_geometry (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (i : Fin (collectionChoices A.skeleton σ).count) :
    (let E := h.spliceMolIso σ hA
     let P := (collectionChoices A.skeleton σ).collection i
     let Q := (collectionChoices B.skeleton (transportPrescription F σ)).collection (h.collectionIndexEquiv σ hA i)
     ({E.e P.upper, E.e P.lower} : Finset _) = {Q.upper, Q.lower} ∧ objectHyperTag P = objectHyperTag Q) := by
  let E := h.spliceMolIso σ hA
  let P := (collectionChoices A.skeleton σ).collection i
  let Q := (collectionChoices B.skeleton (transportPrescription F σ)).collection (h.collectionIndexEquiv σ hA i)
  have ha : (mapObject E P).atoms = Q.atoms := (h.collectionIndexEquiv_atoms σ hA i).symm
  have hg := object_geometry_eq_of_atoms (mapObject E P) Q ha
  exact ⟨hg.1, (mapObject_hyperTag E P).symm.trans hg.2⟩

end WaveTurbulence.VineA
