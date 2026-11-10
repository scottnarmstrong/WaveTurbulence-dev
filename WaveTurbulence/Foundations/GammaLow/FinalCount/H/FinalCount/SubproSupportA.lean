/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproSupportA
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproSupportA`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# SUBPRO (S4): the atom-set form of `SubproSupport` (R28) and the decoration data of `G_sb`

`SubproSupportA` is `SourceVine.SubproSupport` with `Outside` / `IsContained` replaced by atom-set containment
(TARGET L2040-L2051 says "subset"; R28 ruling 3).  `sbDec_of_gen`: a generic decoration of the plain garden `G_sb`
gives the decoration data `SbDec` used by the gap-kind transport.
-/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

/-- TARGET subpro(2)-(6) with atom-set containment (`C.Outside` becomes `∀ i, ¬ P.atoms ⊆ (C.collection i).atoms`). -/
structure SubproSupportA {w d : ℕ} (G : Garden w) (C : Src.SubproChoices Src.γL G) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) →
      G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Src.Object Src.γL G.molecule,
    P.HasGapKind L γ η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → Disjoint P.atoms C.hinges →
    (∃ S a b, Src.IsDV Src.γL G.molecule S a b ∧ P.atoms ⊆ S ∧
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Src.Object Src.γL G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  crossing : ∀ P : Src.Object Src.γL G.molecule,
    P.HasGapKind L γ η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

variable {R : ℕ} {G : Garden (2 * R)}

end WaveTurbulence.GammaLow.FinalCount.H
