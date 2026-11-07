/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.CoreAssembly
/-! The assembled unit family is exactly VINE-A's selected core family. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS2 VineEstS3 VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents
variable {w : ℕ} {S : Garden w}

/-- All and only selected core vines occur in the unit assembly family. -/
theorem unitsFamily_isV0Fam (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    IsV0Fam (unitsFamily (alignedAssembly hM σ) (unitBlk_disj hM σ)) σ := by
  constructor
  · rintro ⟨j, k⟩
    have hmem := assemblyVine_mem (List.get_mem (unitBlocks S σ) j) (alignedAssembly hM σ j) k.1
    have he : assemblyVine (alignedAssembly hM σ j) k.1 =
        familyVine (unitsFamily (alignedAssembly hM σ) (unitBlk_disj hM σ)) ⟨j, k⟩ :=
      clVine_eq_of_atoms rfl
    exact he ▸ hmem
  · intro c hc hcore
    obtain ⟨_, u, hu, hcu⟩ := (vinesV0_iff_unit_cover S σ c).mp hc
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
    obtain ⟨i, hi⟩ := vine_subset_assemblyPiece (alignedAssembly hM σ j) c.isVine.choose_spec hcu
    have hm := assemblyVine_mem (List.get_mem (unitBlocks S σ) j) (alignedAssembly hM σ j) i
    have he : c = assemblyVine (alignedAssembly hM σ j) i := by
      by_contra hne
      have hh := vinesV_separated hc.1 hm.1 hne c.upper c.upper_mem (hi c.upper_mem)
        c.lower c.lower_mem (hi c.lower_mem)
      exact c.isVine.choose_spec.1.2.2.2.1 hh
    have hk : IsCoreCLVine S ((assemblySourceFamily (alignedAssembly hM σ j)).kind i)
        ((assemblySourceFamily (alignedAssembly hM σ j)).atoms i)
        ((assemblySourceFamily (alignedAssembly hM σ j)).upper i)
        ((assemblySourceFamily (alignedAssembly hM σ j)).lower i) := by
      apply coreAssembly_piece_core (Represents.unitAssembly hM σ j) i
      rw [he] at hcore
      exact hcore
    exact ⟨⟨j, ⟨i, hk⟩⟩, congrArg CLVine.atoms he.symm⟩

end WaveTurbulence.VineAlign
