/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIILocalCases

/-! # Identifying the actual parent incidence in the end-rung rows

TARGET molecpl: the lower parent bond is the rail incidence in its
parent's row, so the other three local bonds occupy actual child slots.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The lower parent dart is exactly the mate of the left rail dart. -/
theorem lower_parent_dart {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (R : EndRungData G.molecule S a b)
    (hn : b.1.2 ≠ []) (hp : GNode.parent b.toNode hn = R.left) :
    G.molecule.mate (R.left_row.dart 2) = (.inl (⟨b,hn⟩,false) : GardenDart G) := by
  let x : GardenDart G := .inl (⟨b,hn⟩,false)
  have hx : x ∈ (G.molecule.dartsAt b).filter (G.molecule.InGroup S) := by
    apply mem_filter.mpr
    refine ⟨(Mole.mem_dartsAt G.molecule b x).mpr rfl,?_⟩
    change b ∈ S ∧ GNode.parent b.toNode hn ∈ S
    rw [hp]
    exact ⟨hB.2.2.1,R.left_mem⟩
  rw [R.lower_darts hB] at hx
  rcases mem_insert.mp hx with he | he
  · exact he.symm
  · have he' := congrArg (fun y => G.molecule.atom (G.molecule.mate y)) (mem_singleton.mp he)
    change GNode.parent b.toNode hn = G.molecule.atom (G.molecule.mate (G.molecule.mate (R.right_row.dart 2))) at he'
    rw [G.molecule.mate_mate,R.right_row.atom_eq,hp] at he'
    exact (R.distinct he').elim

/-- The left rail dart has the actual lower branch as child endpoint. -/
theorem lower_parent_reverse_dart {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (R : EndRungData G.molecule S a b)
    (hn : b.1.2 ≠ []) (hp : GNode.parent b.toNode hn = R.left) :
    R.left_row.dart 2 = (.inl (⟨b,hn⟩,true) : GardenDart G) := by
  have hh := congrArg G.molecule.mate (lower_parent_dart G hB R hn hp)
  rw [G.molecule.mate_mate] at hh
  exact hh

end WaveTurbulence.Molecpl
