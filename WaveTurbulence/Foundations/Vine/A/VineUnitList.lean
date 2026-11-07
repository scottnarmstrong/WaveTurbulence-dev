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

/-- Actual units occur without repetitions, since every unit is nonempty. -/
theorem unitBlocks_nodup (σ : Prescription G) : (unitBlocks G σ).Nodup := by
  apply (unitBlocks_pairwise (Mole.garden_isMolecule G) σ).imp
  intro u v hd he
  subst v
  exact (disjoint_left.mp hd u.isBlock.2.1) u.isBlock.2.1

/-- Actual atom lists correspond up to permutation under a selected LF unit twist. -/
theorem unitBlocks_image_perm (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ((unitBlocks G σ).map (fun u => Z.iso.img u.atoms)).Perm
      ((unitBlocks Z.target (transportPrescription Z.iso σ)).map CLBlock.atoms) := by
  apply (List.perm_ext_iff_of_nodup
    ((unitBlocks_nodup σ).map (fun _ _ h => clBlock_eq_of_atoms (Z.iso.img_injective h)))
    ((unitBlocks_nodup (transportPrescription Z.iso σ)).map (fun _ _ h => clBlock_eq_of_atoms h))).mpr
  intro A
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨unitImage Z u (unitBlocks_good Z σ hsel hu), unitImage_mem Z σ hsel hu, rfl⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    obtain ⟨u, hu, he, _, _⟩ := unitBlocks_preimage Z σ hsel hv
    exact List.mem_map.mpr ⟨u, hu, he.symm⟩

end WaveTurbulence.VineA
