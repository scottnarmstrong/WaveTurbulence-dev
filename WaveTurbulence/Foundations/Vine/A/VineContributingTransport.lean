/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineContributingGroups
/-! The actual contributing-group predicate transports via actual unit lists. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w : ℕ} {G H : Garden w}

theorem vineLikeGroup_image_iff (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree)) :
    VineLikeGroup H (F.img S) ↔ VineLikeGroup G S := by
  constructor
  · rintro ⟨a, b, hv | hv | hv⟩
    · have hh := F.symm.isHV_img hv
      rw [F.img_img_symm] at hh
      exact ⟨F.e.symm a, F.e.symm b, Or.inl hh⟩
    · have hh := F.symm.isVC_img hv
      rw [F.img_img_symm] at hh
      exact ⟨F.e.symm a, F.e.symm b, Or.inr (Or.inl hh)⟩
    · have hh := F.symm.isHVC_img hv
      rw [F.img_img_symm] at hh
      exact ⟨F.e.symm a, F.e.symm b, Or.inr (Or.inr hh)⟩
  · rintro ⟨a, b, hv | hv | hv⟩
    · exact ⟨F.e a, F.e b, Or.inl (F.isHV_img hv)⟩
    · exact ⟨F.e a, F.e b, Or.inr (Or.inl (F.isVC_img hv))⟩
    · exact ⟨F.e a, F.e b, Or.inr (Or.inr (F.isHVC_img hv))⟩

/-- For an SG group, whole-group contraction is detected by the actual global unit list. -/
theorem group_whole_unit_iff (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) :
    (∃ u ∈ (groupUnitsOf G S).units, u.atoms = S) ↔ ∃ u ∈ unitBlocks G σ, u.atoms = S := by
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, mem_unitBlocks.mpr ⟨S, hS, hσ, hu⟩, he⟩
  · rintro ⟨u, hu, he⟩
    obtain ⟨T, hT, _, hut⟩ := mem_unitBlocks.mp hu
    have hTS : T = S := by
      by_contra hn
      exact (Finset.disjoint_left.mp (groups_disjoint (Mole.garden_isMolecule G) hT hS hn)
        ((groupUnitsOf G T).sub u hut u.isBlock.2.1)) (he ▸ u.isBlock.2.1)
    subst T
    exact ⟨u, hut, he⟩

/-- Natural whole-group detection uses only the proved actual atom-list permutation. -/
theorem whole_unit_image_iff (F : MolIso G.molecule H.molecule) (σ : Prescription G) (τ : Prescription H)
    (hp : ((unitBlocks G σ).map (fun u => F.img u.atoms)).Perm ((unitBlocks H τ).map CLBlock.atoms))
    (S : Finset (GBranch G.tree)) :
    (∃ v ∈ unitBlocks H τ, v.atoms = F.img S) ↔ ∃ u ∈ unitBlocks G σ, u.atoms = S := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hm := hp.mem_iff.mpr (List.mem_map.mpr ⟨v, hv, he⟩)
    obtain ⟨u, hu, he⟩ := List.mem_map.mp hm
    exact ⟨u, hu, F.img_injective he⟩
  · rintro ⟨u, hu, he⟩
    have hm := hp.mem_iff.mp (List.mem_map.mpr ⟨u, hu, congrArg F.img he⟩)
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
    exact ⟨v, hv, he⟩

/-- The actual choice of whether a group contributes to Cs is natural under actual unit transport. -/
theorem hasObj_image_of_units (F : MolIso G.molecule H.molecule) (σ : Prescription G) (τ : Prescription H)
    (hp : ((unitBlocks G σ).map (fun u => F.img u.atoms)).Perm ((unitBlocks H τ).map CLBlock.atoms))
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hτ : τ (F.img S) = Molecule.GapKind.SG) :
    HasObj H (F.img S) ↔ HasObj G S := by
  rw [hasObj_iff _ (F.maximalGroups_img hS), hasObj_iff _ hS,
    group_whole_unit_iff τ (F.maximalGroups_img hS) hτ, group_whole_unit_iff σ hS hσ,
    vineLikeGroup_image_iff F S, whole_unit_image_iff F σ τ hp S]

/-- Actual selected batches preserve the actual Cs-contributing groups. -/
theorem BatchIso.hasObj {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    {S : Finset (GBranch A.skeleton.tree)} (hS : S ∈ maximalGroups A.skeleton.molecule)
    (hσ : σ S = Molecule.GapKind.SG) : HasObj B.skeleton (F.img S) ↔ HasObj A.skeleton S :=
  hasObj_image_of_units F σ _ (h.units σ hA) hS hσ ((transportPrescription_apply F σ S).trans hσ)

end WaveTurbulence.VineA
