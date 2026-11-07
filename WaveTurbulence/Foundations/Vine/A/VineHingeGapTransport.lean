/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineProperPairTransport
/-! The actual independent Cs.first/second choices have invariant gap kinds
under every selected LF batch on conserving source labels. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p d : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Actual first/second hinge gap semantics transport without any same-choice assumption. -/
theorem BatchIso.collectionChoices_hinge_gapKind (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (v : GBranch (stSt A.skeleton σ).G.tree) (hv : v ∈ (collectionChoices A.skeleton σ).hinges)
    (scale γ η : ℝ) (base : Mom d) (charge : GBranch B.skeleton.tree → Mom d)
    (κ : GardenDart B.skeleton → (Fin d → ℤ)) (hκ : B.skeleton.molecule.IsDecoration scale base charge κ)
    (hc0 : ∀ b ∈ B.skeleton.molecule.atoms, B.skeleton.molecule.deg b = 4 → charge b = 0)
    (κsb : GardenDart (stSt B.skeleton (transportPrescription F σ)).G → (Fin d → ℤ))
    (hlab : ∀ z, κsb z = κ ((stSt B.skeleton (transportPrescription F σ)).M.od z)) :
    ∃ x y u t,
      (collectionChoices A.skeleton σ).first v = some x ∧
      (collectionChoices A.skeleton σ).second v = some y ∧
      (collectionChoices B.skeleton (transportPrescription F σ)).first ((h.spliceMolIso σ hA).e v) = some u ∧
      (collectionChoices B.skeleton (transportPrescription F σ)).second ((h.spliceMolIso σ hA).e v) = some t ∧
      Molecule.gapKind scale γ η (Molecule.gapAt scale base (κsb ∘ (h.spliceMolIso σ hA).d) x y) =
        Molecule.gapKind scale γ η (Molecule.gapAt scale base κsb u t) := by
  obtain ⟨x, y, hxy, hP, _⟩ := hingePair_spec (Mole.garden_isMolecule A.skeleton) σ hv
  have hI := h.properPair_image σ hA hP
  have htv := properPair_mem_hinges hI
  obtain ⟨u, t, hut, hQ, _⟩ := hingePair_spec (Mole.garden_isMolecule B.skeleton) (transportPrescription F σ) htv
  refine ⟨x, y, u, t, collectionChoices_first_of_pair hxy, collectionChoices_second_of_pair hxy,
    collectionChoices_first_of_pair hut, collectionChoices_second_of_pair hut, ?_⟩
  exact (properPairs_gapKind_eq (transportPrescription F σ) hQ hI scale γ η base charge κ hκ hc0 κsb hlab).symm

end WaveTurbulence.VineA
