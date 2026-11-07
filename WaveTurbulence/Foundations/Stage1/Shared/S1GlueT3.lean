/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT2
import Mathlib.Tactic

/-!
# Glued tree layers: children are no larger than their parents
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem child_eq_of_under {r : Fin w × Path} {x1 : Fin w} {x2 : Path} {i : Fin 3}
    (hr : Under r (x1, x2 ++ [i])) (hnr : ¬ Under r (x1, x2)) :
    ((x1, x2 ++ [i]) : Fin w × Path) = r := by
  obtain ⟨h1, h2⟩ := hr
  rcases List.prefix_concat_iff.mp h2 with h3 | h3
  · exact Prod.ext h1.symm h3.symm
  · exact (hnr ⟨h1, h3⟩).elim

namespace GlueT
variable {LM T : LayeredGarden w} {G2 : Garden w} {X : RegChain} {ζ : ℤˣ} {a aT : Fin w × Path}
  {t t' : TTree} {p : ℕ} (h : GlueT LM T G2 X ζ a aT t t' p)
include h

theorem under_lone : Under a (addrExt a X.lonePath) := under_ext a _

/-- Moving the subtree back and forth is the identity outside the tree region. -/
theorem shift_back {z : Fin w × Path} (hz : ¬ InTree a (addrExt a X.lonePath) z) :
    shiftAddr a (addrExt a X.lonePath) (shiftAddr (addrExt a X.lonePath) a z) = z :=
  shift_shift (n := addrExt a X.lonePath) (n' := a) (a := a) (under_refl a) hz

theorem base_node_of {z : Fin w × Path} (hz : ¬ InTree a (addrExt a X.lonePath) z)
    (hn : z.2 ∈ (G2.tree z.1).nodes) :
    (shiftAddr (addrExt a X.lonePath) a z).2 ∈
      (LM.garden.tree (shiftAddr (addrExt a X.lonePath) a z).1).nodes := by
  rw [h.node]
  rw [h.shift_back hz]
  exact hn

theorem child_le (c : GBranch G2.tree) (i : Fin 3) :
    glueTAt LM T a aT (addrExt a X.lonePath) (c.child i).1 ≤
      glueTAt LM T a aT (addrExt a X.lonePath) c.1 := by
  obtain ⟨⟨x1, x2⟩, hcb⟩ := c
  have hcn : (x2 ++ [i]) ∈ (G2.tree x1).nodes := (GBranch.child ⟨(x1,x2),hcb⟩ i).2
  have hx2 : x2 ∈ (G2.tree x1).nodes := by simpa using TTree.dropLast_mem_nodes _ hcn
  change glueTAt LM T a aT (addrExt a X.lonePath) (x1, x2 ++ [i]) ≤
    glueTAt LM T a aT (addrExt a X.lonePath) (x1, x2)
  by_cases hx : InTree a (addrExt a X.lonePath) (x1, x2)
  · obtain ⟨q, hq⟩ := under_of_addrExt hx.1
    have hxq : ((x1, x2) : Fin w × Path) = addrExt a q := hq
    have hyq : ((x1, x2 ++ [i]) : Fin w × Path) = addrExt a (q ++ [i]) := by
      have e1 : x1 = a.1 := congrArg Prod.fst hxq
      have e2 : x2 = a.2 ++ q := congrArg Prod.snd hxq
      refine Prod.ext e1 ?_
      simp [addrExt, e2]
    have hxT := (h.port_node_iff hx).mp hx2
    rw [hxq] at hxT
    rw [treePort_ext] at hxT
    by_cases hy : Under (addrExt a X.lonePath) (x1, x2 ++ [i])
    · have hyn := child_eq_of_under hy hx.2
      have hyl : q ++ [i] = X.lonePath := by
        have := hyq.symm.trans hyn
        have := congrArg Prod.snd this
        simpa [addrExt] using this
      have hnot : ¬ InTree a (addrExt a X.lonePath) (x1, x2 ++ [i]) := fun hh => hh.2 hy
      rw [glueTAt_out _ _ _ _ _ hnot, hyn, shift_self, hxq,
        glueTAt_ext LM T a aT _ (h.under_lone) q (by rw [← hxq]; exact hx.2), ← h.hlone]
      have hlT : (addrExt aT X.lonePath).2 ∈ (T.garden.tree (addrExt aT X.lonePath).1).nodes :=
        (node_iff_of_subtree h.embT.node h.embT.tree X.lonePath).1.mpr (lonePath_mem_plug X ζ t')
      refine layerAt_le_of_under T hxT hlT ?_
      rw [← hyl]
      exact (under_ext_iff aT q (q ++ [i])).mpr (List.prefix_append _ _)
    · have hyin : InTree a (addrExt a X.lonePath) (x1, x2 ++ [i]) :=
        ⟨by rw [hyq]; exact under_ext _ _, hy⟩
      have hyT := (h.port_node_iff hyin).mp hcn
      rw [hyq, treePort_ext] at hyT
      rw [hyq, hxq, glueTAt_ext LM T a aT _ h.under_lone _ (by rw [← hyq]; exact hy),
        glueTAt_ext LM T a aT _ h.under_lone _ (by rw [← hxq]; exact hx.2)]
      exact layerAt_le_of_under T hxT hyT ((under_ext_iff aT q (q ++ [i])).mpr (List.prefix_append _ _))
  · -- the parent lies outside the tree region
    set n' := addrExt a X.lonePath with hn'
    have hnotUnderA : ¬ Under a (x1, x2) → ¬ Under n' (x1, x2) := fun h1 h2 =>
      h1 (under_trans h.under_lone h2)
    by_cases hy : InTree a n' (x1, x2 ++ [i])
    · -- the child is the root `a`
      have hxa : ¬ Under a (x1, x2) := by
        intro hu
        have : Under n' (x1, x2) := by
          by_contra hh; exact hx ⟨hu, hh⟩
        exact hy.2 (by obtain ⟨e1, e2⟩ := this; exact ⟨e1, e2.trans (List.prefix_append _ _)⟩)
      have hya := child_eq_of_under hy.1 hxa
      have hxn := hnotUnderA hxa
      rw [glueTAt_in _ _ _ _ _ hy, glueTAt_out _ _ _ _ _ hx, shift_of_not hxn, hya]
      have hpar : layerAt LM (x1, x2) = parAt LM p a := by
        have hh := parAt_child LM p (x := (x1, x2)) i (by
          rw [show addrExt (x1, x2) [i] = (x1, x2 ++ [i]) from rfl, hya]
          exact h.embM.node)
        rw [show addrExt (x1, x2) [i] = (x1, x2 ++ [i]) from rfl, hya] at hh
        exact hh.symm
      rw [hpar, ← h.hpa]
      have := layerAt_le_parAt T p h.hp h.embT.node
      simpa [treePort, addrExt] using this
    · by_cases hyn : ((x1, x2 ++ [i]) : Fin w × Path) = n'
      · -- the child is the lone position equal to the root
        have hxa : ¬ Under a (x1, x2) := by
          intro hu
          have hu2 : Under n' (x1, x2) := by
            by_contra hh; exact hx ⟨hu, hh⟩
          have h4 : n'.2.length ≤ x2.length := hu2.2.length_le
          have h3 : n'.2.length = x2.length + 1 := by rw [← hyn]; simp
          omega
        have hxn := hnotUnderA hxa
        have hya : ((x1, x2 ++ [i]) : Fin w × Path) = a :=
          child_eq_of_under (by rw [hyn]; exact h.under_lone) hxa
        rw [glueTAt_out _ _ _ _ _ hy, glueTAt_out _ _ _ _ _ hx, shift_of_not hxn, hyn, shift_self]
        have hxN : x2 ∈ (LM.garden.tree x1).nodes := by
          have := (h.node (x1, x2)).mpr (by rw [shift_of_not hxa]; exact hx2)
          exact this
        rw [← hya]
        exact layerAt_le_of_under LM (x := (x1, x2)) (z := (x1, x2 ++ [i])) hxN
          (by rw [hya]; exact h.embM.node) ⟨rfl, List.prefix_append _ _⟩
      · have hs := shift_parent (a := a) (n := n') (n' := a) h.under_lone hy hyn
          (x := (x1, x2)) (k := i) rfl
        rw [glueTAt_out _ _ _ _ _ hy, glueTAt_out _ _ _ _ _ hx, hs.2]
        have h1 := h.base_node_of hx hx2
        have h2 := h.base_node_of hy hcn
        rw [hs.2] at h2
        exact layerAt_le_of_under LM h1 h2 (under_ext _ _)

end GlueT
end WaveTurbulence.Stage1
