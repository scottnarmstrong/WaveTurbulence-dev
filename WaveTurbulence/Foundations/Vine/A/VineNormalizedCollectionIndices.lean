/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedCollectionTransport
public import Mathlib.Data.Fintype.EquivFin
/-! The independently ordered actual C1 choices have corresponding finite indices. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Pairwise disjoint nonempty actual collection supports identify their finite indices. -/
theorem collectionChoices_atoms_injective {G : Garden w} (σ : Prescription G) :
    Function.Injective (fun i => ((collectionChoices G σ).collection i).atoms) := by
  change Function.Injective (fun i : Fin (objects G σ).length => ((objects G σ).get i).atoms)
  intro i j he
  by_contra hn
  have hp := List.pairwise_iff_get.mp (objects_pairwise (Mole.garden_isMolecule G) σ)
  have hd : Disjoint ((objects G σ).get i).atoms ((objects G σ).get j).atoms := by
    rcases lt_or_gt_of_ne (fun h => hn (Fin.ext h)) with hij | hji
    · exact hp i j hij
    · exact (hp j i hji).symm
  change ((objects G σ).get i).atoms = ((objects G σ).get j).atoms at he
  have hi : ((objects G σ).get i).upper ∈ ((objects G σ).get i).atoms := RedSplice.Object.upper_mem ((objects G σ).get i)
  have hj : ((objects G σ).get i).upper ∈ ((objects G σ).get j).atoms := he ▸ hi
  exact (Finset.disjoint_left.mp hd hi) hj

/-- Every actual source collection index has an actual target index with its transported support. -/
theorem BatchIso.collection_support_index (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (i : Fin (collectionChoices A.skeleton σ).count) :
    ∃ j : Fin (collectionChoices B.skeleton (transportPrescription F σ)).count,
      ((collectionChoices B.skeleton (transportPrescription F σ)).collection j).atoms =
        (h.spliceMolIso σ hA).img (((collectionChoices A.skeleton σ).collection i).atoms) := by
  have hm := ((BatchIso.objects_atoms_perm h) σ hA).mem_iff.mp
    (List.mem_map.mpr ⟨(objects A.skeleton σ).get i, List.get_mem _ i, rfl⟩)
  obtain ⟨O, hO, he⟩ := List.mem_map.mp hm
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hO
  exact ⟨j, (congrArg Object.atoms hj).trans he⟩

/-- The actual collection indices correspond bijectively despite independent list ordering. -/
noncomputable def BatchIso.collectionIndexEquiv (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) :
    Fin (collectionChoices A.skeleton σ).count ≃
      Fin (collectionChoices B.skeleton (transportPrescription F σ)).count := by
  classical
  let f := fun i => ((BatchIso.collection_support_index h) σ hA i).choose
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨?_, ?_⟩
  · intro i j he
    apply collectionChoices_atoms_injective σ
    apply (h.spliceMolIso σ hA).img_injective
    exact ((BatchIso.collection_support_index h) σ hA i).choose_spec.symm.trans
      ((congrArg (fun k => ((collectionChoices B.skeleton (transportPrescription F σ)).collection k).atoms) he).trans
        ((BatchIso.collection_support_index h) σ hA j).choose_spec)
  · simpa only [Fintype.card_fin] using (BatchIso.collectionChoices_count h) σ hA

/-- The actual correspondence carries the actual chosen collection supports. -/
theorem BatchIso.collectionIndexEquiv_atoms (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (i : Fin (collectionChoices A.skeleton σ).count) :
    ((collectionChoices B.skeleton (transportPrescription F σ)).collection ((BatchIso.collectionIndexEquiv h) σ hA i)).atoms =
      (h.spliceMolIso σ hA).img (((collectionChoices A.skeleton σ).collection i).atoms) :=
  ((BatchIso.collection_support_index h) σ hA i).choose_spec

end WaveTurbulence.VineA.NormalizedSplice
