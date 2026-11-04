/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type2SpineRecovery

/-! # The maximal chain roots determine the actual terminal-couple carrier -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Once the two maximal spines are recovered, their terminal couple's actual carrier is fixed. -/
theorem type2_terminal_carrier_unique (p n p' n' : RegChain) (q q' : RegCpl)
    (hq : q.isType2 = false) (hq' : q'.isType2 = false)
    (he : decodedCouple (.type2 p n q) = decodedCouple (.type2 p' n' q')) :
    decodedCouple q = decodedCouple q' := by
  have hlp := type2_lonePaths_unique p n p' n' q q' hq hq' he
  have ht : q.trees = q'.trees := by
    apply Prod.ext
    · have hh := congrArg (fun G : Garden 2 => Comb.subtree (G.tree 0) p.lonePath) he
      change Comb.subtree (p.plug 1 q.trees.1) p.lonePath =
        Comb.subtree (p'.plug 1 q'.trees.1) p.lonePath at hh
      rw [plug_subtree_lonePath p,hlp.1,plug_subtree_lonePath p'] at hh
      exact Option.some.inj hh
    · have hh := congrArg (fun G : Garden 2 => Comb.subtree (G.tree 1) n.lonePath) he
      change Comb.subtree (n.plug (-1) q.trees.2) n.lonePath =
        Comb.subtree (n'.plug (-1) q'.trees.2) n.lonePath at hh
      rw [plug_subtree_lonePath n,hlp.2,plug_subtree_lonePath n'] at hh
      exact Option.some.inj hh
  have hab : IncompAddr ((0 : Fin 2),p.lonePath) (1,n.lonePath) :=
    ⟨fun h => (by decide : (1 : Fin 2) ≠ 0) h.1,
      fun h => (by decide : (0 : Fin 2) ≠ 1) h.1⟩
  apply decodedCouple_eq_of_common_frame (.type2 p n q) q q' (0,p.lonePath) (1,n.lonePath) hab ht
  · apply symmPairs_subset_of_pairs_subset
    intro z hz
    exact List.mem_append_right _ hz
  · intro z hz
    have hz' : z ∈ symmPairs ((RegCpl.type2 p' n' q').raw.2) := by
      rw [hlp.1,hlp.2] at hz
      apply symmPairs_subset_of_pairs_subset (fun z hz => List.mem_append_right _ hz) z hz
    exact (symmPairs_eq_of_carrier_eq he z).mpr hz'

end WaveTurbulence.Reg
