/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
public import WaveTurbulence.Foundations.Molecule.IsoGroupTransport

/-! # Current connected blocks are preserved by the actual unit twist -/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (G H : Garden w) (f : GardenDirectedIso G H)

/-- The degree-only auxiliary block predicate transports through the exact molecule isomorphism. -/
theorem iso_isBlockDeg {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlockDeg S a b) :
    H.molecule.IsBlockDeg (isoAtoms G H f S) (f.branches a) (f.branches b) := by
  refine ⟨fun _ _ => mem_univ _,(mem_isoAtoms G H f S a).mpr hB.2.1,
    (mem_isoAtoms G H f S b).mpr hB.2.2.1,f.branches.injective.ne hB.2.2.2.1,?_,?_,?_,?_,?_⟩
  · rw [iso_outIn]; exact hB.2.2.2.2.1
  · rw [iso_inIn]; exact hB.2.2.2.2.2.1
  · rw [iso_outIn]; exact hB.2.2.2.2.2.2.1
  · rw [iso_inIn]; exact hB.2.2.2.2.2.2.2.1
  · intro v hv hva hvb
    obtain ⟨v,rfl⟩ := f.branches.surjective v
    rw [iso_degIn]
    exact hB.2.2.2.2.2.2.2.2 v ((mem_isoAtoms G H f S v).mp hv)
      (fun he => hva (congrArg f.branches he))
      (fun he => hvb (congrArg f.branches he))

/-- The literal current B2 connectedness relation transports along the actual dart bijection. -/
theorem iso_groupConnected {S : Finset (GBranch G.tree)}
    (h : G.molecule.GroupConnected S) : H.molecule.GroupConnected (isoAtoms G H f S) := by
  intro u hu v hv
  obtain ⟨u,rfl⟩ := f.branches.surjective u
  obtain ⟨v,rfl⟩ := f.branches.surjective v
  have hp := h u ((mem_isoAtoms G H f S u).mp hu) v ((mem_isoAtoms G H f S v).mp hv)
  clear hu hv h
  induction hp with
  | rel a b hab =>
    obtain ⟨x,hx,ha,hb⟩ := hab
    apply Relation.EqvGen.rel
    refine ⟨f.darts x,(inGroup_isoAtoms G H f S x).mpr hx,?_,?_⟩
    · rw [f.atom_comm,ha]
    · rw [f.mate_comm,f.atom_comm,hb]
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc

/-- The exact current connected B2 block predicate is preserved. -/
theorem iso_isBlock {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    H.molecule.IsBlock (isoAtoms G H f S) (f.branches a) (f.branches b) := by
  apply (Molecpl.isBlock_iff_degree_connected _).mpr
  exact ⟨iso_isBlockDeg G H f (Molecpl.isBlock_degree G.molecule hB),
    iso_groupConnected G H f hB.2.2.2.2.2.2.2.2.2⟩

end WaveTurbulence.Twist
