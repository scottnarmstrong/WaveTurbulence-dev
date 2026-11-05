/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IsoVineTransport

/-! # Internal incidence positions through an actual garden isomorphism

This conditional infrastructure lemma is used only at atoms whose
position codes have independently been proved unchanged.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G H : Garden w) (f : GardenDirectedIso G H)

/-- Position-preserving actual darts transport the internal slot set at one specified atom. -/
theorem iso_internalPositions_at (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (hpos : ∀ x, G.molecule.atom x = v → Mole.dartPosition H (f.darts x) = Mole.dartPosition G x)
    (i : Fin 4) :
    i ∈ Mole.internalPositions H (isoAtoms G H f S) (f.branches v) ↔ i ∈ Mole.internalPositions G S v := by
  constructor
  · intro h
    obtain ⟨y,ha,hg,hp⟩ := (Mole.mem_internalPositions H).mp h
    obtain ⟨x,rfl⟩ := f.darts.surjective y
    have hx : G.molecule.atom x = v := f.branches.injective ((f.atom_comm x).symm.trans ha)
    exact (Mole.mem_internalPositions G).mpr ⟨x,hx,(inGroup_isoAtoms G H f S x).mp hg,
      (hpos x hx).symm.trans hp⟩
  · intro h
    obtain ⟨x,ha,hg,hp⟩ := (Mole.mem_internalPositions G).mp h
    exact (Mole.mem_internalPositions H).mpr ⟨f.darts x,(f.atom_comm x).trans (congrArg f.branches ha),
      (inGroup_isoAtoms G H f S x).mpr hg,(hpos x ha).trans hp⟩

end WaveTurbulence.Twist
