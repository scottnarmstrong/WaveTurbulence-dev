/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.RungBondTypes

/-! # Excluding PC shortcuts across two generations

TARGET molecpl (II-e): its two rung bonds must both be LP bonds.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- An actual parent relation increments path length by one. -/
theorem parent_height {a b : GBranch G.tree} (hn : b.1.2 ≠ [])
    (hp : GNode.parent b.toNode hn = a) : a.1.2.length+1 = b.1.2.length := by
  have hh := parent_length G b.toNode hn
  have he := congrArg (fun v : GBranch G.tree => v.1.2.length) hp
  dsimp [GBranch.toNode,GNode.parent] at hh he
  omega

/-- There is no PC bond from a grandparent to its grandchild. -/
theorem parent_chain_no_pc {p b q : GBranch G.tree}
    (hbn : b.1.2 ≠ []) (hbp : GNode.parent b.toNode hbn = p)
    (hqn : q.1.2 ≠ []) (hqp : GNode.parent q.toNode hqn = b)
    {x : GardenDart G} (hx : G.molecule.atom x = p)
    (hy : G.molecule.atom (G.molecule.mate x) = q) : ¬ IsPCDart G x := by
  intro hpc
  have hb := parent_height G hbn hbp
  have hq := parent_height G hqn hqp
  rcases pc_dart_parent G hpc hx hy with ⟨hn,hp⟩ | ⟨hn,hp⟩
  · have hh := parent_height G hn hp
    omega
  · have hh := parent_height G hn hp
    omega

end WaveTurbulence.Molecpl
