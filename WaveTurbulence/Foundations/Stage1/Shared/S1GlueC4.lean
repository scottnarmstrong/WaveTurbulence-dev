/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC3
import Mathlib.Tactic

/-!
# Glued layers: children are no larger than their parents
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

theorem child_le (c : GBranch G.tree) (i : Fin 3) :
    glueAt LN T a b aT bT (c.child i).1 ≤ glueAt LN T a b aT bT c.1 := by
  obtain ⟨⟨x1, x2⟩, hcb⟩ := c
  have hcn : (x2 ++ [i]) ∈ (G.tree x1).nodes := (GBranch.child ⟨(x1,x2),hcb⟩ i).2
  change glueAt LN T a b aT bT (x1, x2 ++ [i]) ≤ glueAt LN T a b aT bT (x1, x2)
  by_cases hA : Under a (x1, x2)
  · obtain ⟨q, hq⟩ := under_of_addrExt hA
    have ex1 : x1 = a.1 := congrArg Prod.fst hq
    have ex2 : x2 = a.2 ++ q := congrArg Prod.snd hq
    subst ex2 ex1
    have e1 : ((a.1, a.2 ++ q ++ [i]) : Fin w × Path) = addrExt a (q ++ [i]) := by
      simp [addrExt]
    have e0 : ((a.1, a.2 ++ q) : Fin w × Path) = addrExt a q := rfl
    rw [e1, e0, h.glue_a, h.glue_a]
    have hc : (q ++ [i]) ∈ Q.trees.1.nodes := by
      have : (addrExt a (q ++ [i])).2 ∈ (G.tree (addrExt a (q ++ [i])).1).nodes := by
        simpa [addrExt] using hcn
      exact (node_iff_of_subtree h.embM.nodeA h.embM.treeA (q ++ [i])).1.mp this
    exact h.region_child h.embT.nodeA h.embT.treeA q i hc
  by_cases hB : Under b (x1, x2)
  · obtain ⟨q, hq⟩ := under_of_addrExt hB
    have ex1 : x1 = b.1 := congrArg Prod.fst hq
    have ex2 : x2 = b.2 ++ q := congrArg Prod.snd hq
    subst ex2 ex1
    have e1 : ((b.1, b.2 ++ q ++ [i]) : Fin w × Path) = addrExt b (q ++ [i]) := by
      simp [addrExt]
    have e0 : ((b.1, b.2 ++ q) : Fin w × Path) = addrExt b q := rfl
    rw [e1, e0, h.glue_b, h.glue_b]
    have hc : (q ++ [i]) ∈ Q.trees.2.nodes := by
      have : (addrExt b (q ++ [i])).2 ∈ (G.tree (addrExt b (q ++ [i])).1).nodes := by
        simpa [addrExt] using hcn
      exact (node_iff_of_subtree h.embM.nodeB h.embM.treeB (q ++ [i])).1.mp this
    exact h.region_child h.embT.nodeB h.embT.treeB q i hc
  have hx : ¬ InRegion a b (x1, x2) := fun hh => hh.elim hA hB
  have hx2 : x2 ∈ (G.tree x1).nodes := by simpa using TTree.dropLast_mem_nodes _ hcn
  have hxN : x2 ∈ (LN.garden.tree x1).nodes := (h.node (x1, x2) hx).mp hx2
  by_cases hy : InRegion a b (x1, x2 ++ [i])
  · -- the child is one of the roots
    have key : ∀ r : Fin w × Path, Under r (x1, x2 ++ [i]) → ¬ Under r (x1, x2) →
        (x1, x2 ++ [i]) = r := by
      intro r hr hnr
      obtain ⟨h1, h2⟩ := hr
      rcases (List.prefix_concat_iff.mp h2) with h3 | h3
      · exact Prod.ext h1.symm h3.symm
      · exact (hnr ⟨h1, h3⟩).elim
    have hpar : layerAt LN (x1, x2) = parAt LN p (x1, x2 ++ [i]) := by
      have hh := parAt_child LN p (x := (x1, x2)) i (by
        have hmem : (x1, x2 ++ [i]) ∈ ({(x1, x2 ++ [i])} : Finset _) := Finset.mem_singleton_self _
        rcases hy with hy | hy
        · have e := key a hy hA
          have := h.embN.nodeA
          rw [← e] at this
          simpa [addrExt] using this
        · have e := key b hy hB
          have := h.embN.nodeB
          rw [← e] at this
          simpa [addrExt] using this)
      simpa [addrExt] using hh.symm
    rw [glueAt_out _ _ _ _ _ _ hx]
    rcases hy with hy | hy
    · have e := key a hy hA
      have e' : ((x1, x2 ++ [i]) : Fin w × Path) = addrExt a [] := e.trans (by simp [addrExt])
      rw [e', h.glue_a, hpar, e, ← h.hpa]
      have := layerAt_le_parAt T p h.hp h.embT.nodeA
      simpa [addrExt] using this
    · have e := key b hy hB
      have e' : ((x1, x2 ++ [i]) : Fin w × Path) = addrExt b [] := e.trans (by simp [addrExt])
      rw [e', h.glue_b, hpar, e, ← h.hpb]
      have := layerAt_le_parAt T p h.hp h.embT.nodeB
      simpa [addrExt] using this
  · rw [glueAt_out _ _ _ _ _ _ hy, glueAt_out _ _ _ _ _ _ hx]
    have hyN : x2 ++ [i] ∈ (LN.garden.tree x1).nodes := (h.node (x1, x2 ++ [i]) hy).mp hcn
    exact layerAt_le_of_under LN hxN hyN ⟨rfl, List.prefix_append _ _⟩

end GlueC
end WaveTurbulence.Stage1
