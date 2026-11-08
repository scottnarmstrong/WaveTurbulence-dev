/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitEquiv
/-! The actual unit lists agree up to permutation after atom transport.
No order compatibility of independent finite-list choices is assumed. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b (Mk-general form of `unitBlocks_nodup`). -/
theorem unitBlocks_nodupMk (σ : Prescription G) {Mk : Set (Stage1.CLVine _)} : (unitBlocks (Mk := Mk) G σ).Nodup := by
  apply (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ).imp
  intro u v hd he
  subst v
  exact (disjoint_left.mp hd u.isBlock.2.1) u.isBlock.2.1

/-- Actual units occur without repetitions, since every unit is nonempty. -/
theorem unitBlocks_nodup (σ : Prescription G) : (unitBlocks G σ).Nodup := unitBlocks_nodupMk (Mk := ∅) σ

/-- B1b-2 (Mk-general form of `unitBlocks_image_perm`, two marked sets carried by the twist). -/
theorem unitBlocks_image_permMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    ((unitBlocks G σ Mk).map (fun u => Z.iso.img u.atoms)).Perm
      ((unitBlocks Z.target (transportPrescription Z.iso σ) Mk').map CLBlock.atoms) := by
  apply (List.perm_ext_iff_of_nodup
    ((unitBlocks_nodupMk σ (Mk := Mk)).map (fun _ _ h => clBlock_eq_of_atoms (Z.iso.img_injective h)))
    ((unitBlocks_nodupMk (transportPrescription Z.iso σ) (Mk := Mk')).map
      (fun _ _ h => clBlock_eq_of_atoms h))).mpr
  intro A
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨unitImage Z u (unitBlocks_goodMk Z σ hsel hu), unitImage_memMk Z σ hT hsel hu, rfl⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    obtain ⟨u, hu, he, _, _⟩ := unitBlocks_preimageMk Z σ hT hsel hv
    exact List.mem_map.mpr ⟨u, hu, he.symm⟩

/-- Actual atom lists correspond up to permutation under a selected LF unit twist. -/
theorem unitBlocks_image_perm (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ((unitBlocks G σ).map (fun u => Z.iso.img u.atoms)).Perm
      ((unitBlocks Z.target (transportPrescription Z.iso σ)).map CLBlock.atoms) :=
  unitBlocks_image_permMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

end WaveTurbulence.VineA
