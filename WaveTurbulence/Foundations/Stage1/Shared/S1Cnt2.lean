/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF7
import Mathlib.Tactic

/-!
# The new-side layer counts of an LF construction depend only on the template layers
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

/-- Layers of the output at the couple nodes equal those of the mid garden (the tree reinsertion only shifts). -/
theorem outC_shift (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
    (mid out : LayeredGarden w)
    (hT : OutAgreeT mid out (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) X.lonePath))
    (j : Fin 2) (r : Path) :
    layerAt out (addrExt (coupleRoot (s.finalData ε X Q hX hQ) (s.chosen_plain ε) (s.pairs ε s.exceptional) j) r) =
      layerAt mid (addrExt (coupleRoot (s.midData ε Q hQ) (s.chosen_plain ε) (s.pairs ε s.exceptional) j) r) := by
  have key : ∀ n : GNode (s.chosen ε).tree, ¬ Below n.1 (s.branches ε s.placement.lower).1 →
      layerAt out (addrExt (inflatedPosition (s.chosen ε) (s.finalData ε X Q hX hQ).tree n) r) =
        layerAt mid (addrExt (inflatedPosition (s.chosen ε) (s.midData ε Q hQ).tree n) r) := by
    intro n hn
    have hp := (s.finalData ε X Q hX hQ).eraseTree_pair_root_transport (s.branches ε s.placement.lower) n hn
    have hE : (s.finalData ε X Q hX hQ).eraseTree (s.branches ε s.placement.lower) = s.midData ε Q hQ :=
      eraseTree_final _ _ _ _
    simp only [hE] at hp
    have hpos := finalPos_eq (s := s) (ε := ε) X Q hX hQ
    have hlone : ((s.finalData ε X Q hX hQ).tree (s.branches ε s.placement.lower)).lonePath = X.lonePath := by
      rw [show (s.finalData ε X Q hX hQ).tree (s.branches ε s.placement.lower) = X from Function.update_self _ _ _]
    rw [hlone] at hp
    rw [hp.1, ← hp.2 r]
    have hh := hT.layer (addrExt (inflatedPosition (s.chosen ε) (s.midData ε Q hQ).tree n) r)
      (fun h => h.2 h.1)
    rw [hh, stretch_eq_shift]
    rfl
  have hn := fun (l : GLeaf (s.chosen ε).tree) => leaf_not_above_branch (s.chosen ε).tree l (s.branches ε s.placement.lower)
  fin_cases j
  · exact key _ (hn _)
  · exact key _ (hn _)

end WaveTurbulence.Stage1
