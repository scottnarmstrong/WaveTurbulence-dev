/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! Actual maximal ladders admit source presentations; no combinatorial source assumption is added. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem sourceMaximalLadderData_nonempty {w : ℕ} (G : Garden w) : Nonempty (SourceMaximalLadderData G) := by
  classical
  have hw (S : {S // S ∈ G.molecule.maximalLadders}) :
      ∃ m : ℕ, ∃ u v : Fin (m + 1) → GBranch G.tree,
        G.molecule.IsLadder u v ∧ Molecule.ladderAtoms u v = S.1 := by
    have hs := S.2
    simp only [Molecule.maximalLadders, Finset.mem_filter] at hs
    have hm : G.molecule.IsLadderSet S.1 := hs.2.1
    exact hm
  choose m u v hL hS using hw
  exact ⟨⟨m, u, v, hL, hS⟩⟩

end WaveTurbulence.LGSpine
