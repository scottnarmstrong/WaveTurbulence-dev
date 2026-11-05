/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceDipoles
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniPorts

/-! # Every actual source branch bond reverses its conservation sign -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- The source's ordered child sign rule, on actual branching nodes. -/
theorem branch_child_sign {w : ℕ} (G : Garden w) (b : GBranch G.tree) (i : Fin 3) :
    G.sign (b.child i) = slotSign (G.sign b.toNode) i := by
  change nodeSign G.sig (addrExt b.1 [i]) = slotSign (nodeSign G.sig b.1) i
  exact nodeSign_step G.sig b.1 i

/-- Both tree bonds and actual paired-leaf bonds have opposite incident-port signs. -/
theorem source_port_sign {w : ℕ} (G : Garden w) (hG : G.IsPlain) (b c : GBranch G.tree)
    (i j : Fin 4) (he : portMate G (.inr (b,i)) = .inr (c,j)) :
    portSign (G.sign b.toNode) i = -portSign (G.sign c.toNode) j := by
  revert he
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun z => ?_) j
    · intro he
      exact (portMate_parent_ne_parent G b c he).elim
    · intro he
      have hn := (portMate_parent_child_iff G b c z).mp he
      have hs := congrArg G.sign hn
      rw [branch_child_sign] at hs
      exact congrArg Neg.neg hs
  · refine Fin.cases ?_ (fun z => ?_) j
    · intro he
      have hn := (portMate_child_parent_iff G b c a).mp he
      have hs := congrArg G.sign hn
      rw [branch_child_sign] at hs
      simpa only [portSign,Fin.cases_zero,Fin.cases_succ,neg_neg] using hs
    · intro he
      obtain ⟨ℓ,q,hℓ,hq,hp⟩ := paired_leaves_of_child_bond G b c a z he
      have hs := G.pair_sign ℓ (Comb.pair_ne_of_plain hG ℓ)
      rw [hp] at hs
      change G.sign q.toNode = -G.sign ℓ.toNode at hs
      rw [hℓ,hq,branch_child_sign,branch_child_sign] at hs
      simpa only [portSign,Fin.cases_succ,neg_neg] using (congrArg Neg.neg hs).symm

/-- For a parent-free orientation, the three known mini bonds satisfy exactly
one of the pinned finite sign patterns. -/
theorem BranchDipole.internal_signs {w : ℕ} {G : Garden w} (D : BranchDipole G)
    (hG : G.IsPlain) (hf : D.free = 0) (i : Fin 3) :
    slotSign (G.sign D.u.toNode) i = -portSign (G.sign D.v.toNode) (D.perm i.succ) := by
  have hi : i.succ ≠ D.free := by rw [hf]; exact Fin.succ_ne_zero i
  exact source_port_sign G hG D.u D.v i.succ (D.perm i.succ) (D.internal i.succ hi)

end WaveTurbulence.Reg.Skeleton
