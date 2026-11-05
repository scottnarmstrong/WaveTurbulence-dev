/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PrunedParents
import Mathlib.Tactic

/-! # Extending a pruned region by an actual internal child slot
TARGET `block_clcn`: branch and LP-leaf realizations use the same
pruned descendant sets, including their boundary child slots.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem child_pair_injective : Function.Injective
    (fun p : GBranch G.tree × Fin 3 => p.1.child p.2) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ he
  have hidx : a.1.1 = b.1.1 := congrArg (fun n : GNode G.tree => n.1.1) he
  have hpath : a.1.2++[i] = b.1.2++[j] := congrArg (fun n : GNode G.tree => n.1.2) he
  have hp := congrArg List.dropLast hpath
  simp only [List.dropLast_append_cons,List.dropLast_singleton,List.append_nil] at hp
  have hab : a = b := Subtype.ext (Prod.ext hidx hp)
  subst b
  have hij := List.append_cancel_left hpath
  exact Prod.ext rfl (List.singleton_inj.mp hij)

theorem excluded_child_extension {S : Finset (GBranch G.tree)}
    {j p : GBranch G.tree} {k i : Fin 3}
    (hcut : k.succ ∉ internalPositions G S j)
    (hkeep : i.succ ∈ internalPositions G S p)
    (hn : ¬ (j.child k).IsDesc p.toNode) : ¬ (j.child k).IsDesc (p.child i) := by
  intro hd
  by_cases he : (j.child k).1.2 = (p.child i).1.2
  · have heq : j.child k = p.child i := Subtype.ext (Prod.ext hd.1 he)
    have hp := child_pair_injective G (a₁ := (j,k)) (a₂ := (p,i)) heq
    have hj : j = p := congrArg Prod.fst hp
    have hk : k = i := congrArg Prod.snd hp
    exact hcut (hj.symm ▸ hk.symm ▸ hkeep)
  · apply hn
    refine ⟨hd.1,?_⟩
    have hpre := proper_prefix_dropLast hd.2 he
    simpa only [GBranch.toNode,GBranch.child,List.dropLast_append_cons,List.dropLast_singleton,
      List.append_nil] using hpre

theorem cl_pruned_child_extension {S : Finset (GBranch G.tree)} {a b p : GBranch G.tree}
    (hp : InCLPrunedRegion G S a b p.toNode) (i : Fin 3)
    (hi : i.succ ∈ internalPositions G S p) : InCLPrunedRegion G S a b (p.child i) := by
  refine ⟨⟨hp.1.1,hp.1.2.trans (List.prefix_append _ _)⟩,?_⟩
  intro j hj k hk
  exact excluded_child_extension G hk hi (hp.2 j hj k hk)

end WaveTurbulence.Mole
