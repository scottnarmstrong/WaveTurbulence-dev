/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.EndRungLowerDarts
public import WaveTurbulence.Foundations.Molecule.TypeIIEndRung

/-! # The actual parent of a lower type-II joint

TARGET molecpl (2): its parent is one of the two neighboring rung atoms.
-/

public section
namespace WaveTurbulence.Molecpl
open Finset TTree

/-- Every internal incidence at the lower joint ends at one of the rung atoms. -/
theorem EndRungData.lower_neighbor {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    (R : EndRungData M S a b) {x : D} (hx : M.atom x = b) (hgroup : M.InGroup S x) :
    M.atom (M.mate x) = R.left ∨ M.atom (M.mate x) = R.right := by
  have hm : x ∈ (M.dartsAt b).filter (M.InGroup S) :=
    mem_filter.mpr ⟨(Mole.mem_dartsAt M b x).mpr hx,hgroup⟩
  rw [R.lower_darts hB] at hm
  rcases mem_insert.mp hm with he | he
  · rw [he,M.mate_mate]
    exact Or.inl (R.left_row.atom_eq 2)
  · rw [mem_singleton.mp he,M.mate_mate]
    exact Or.inr (R.right_row.atom_eq 2)

/-- The actual lower parent is a rung atom, with its nonroot witness retained. -/
theorem EndRungData.lower_parent {w : ℕ} (G : Garden w)
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : EndRungData G.molecule S a b) :
    ∃ hn : b.1.2 ≠ [], GNode.parent b.toNode hn = R.left ∨
      GNode.parent b.toNode hn = R.right := by
  obtain ⟨hn,hp⟩ := hCL.2
  let x : GardenDart G := .inl (⟨b,hn⟩,false)
  exact ⟨hn,R.lower_neighbor hB (x := x) rfl ⟨hB.2.2.1,hp⟩⟩

end WaveTurbulence.Molecpl
