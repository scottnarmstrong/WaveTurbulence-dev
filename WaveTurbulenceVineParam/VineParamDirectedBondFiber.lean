/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondModel
public import WaveTurbulenceVineParam.VineParamSpliceSourceFiber
import Mathlib.Tactic

/-! # The actual molecule's entire internal source fiber in directed model coordinates -/

public section
namespace WaveTurbulence.Vine.Param.DirectedBondModel
open Finset VineParamContract
variable {V D A β E : Type*} [DecidableEq V] [Fintype D] [DecidableEq A] [Fintype β]
  [AddCommGroup E] {M : Molecule V D} {S : Finset V}
variable (Q : DirectedBondModel M S A β)

/-- Both source joint rows and every actual interior row are retained by
the directed model, uniformly over arbitrary additive groups. -/
@[expose] noncomputable def rootFiberEquiv (a b : A) (hab : a ≠ b) (r : E) :
    FlowFiber M S (Q.atom a).1 (Q.atom b).1 E r ≃ DirectedRootFiber Q.ends a b r := by
  classical
  refine {
    toFun := fun k => ⟨fun e => k.1 (Q.edge e),?_⟩
    invFun := fun k => ⟨fun e => k.1 (Q.edge.symm e),?_,?_,?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro v
    rw [← Q.flow_eq]
    by_cases hva : v=a
    · subst v
      simpa only [rootForcing,ite_true] using k.2.1
    · by_cases hvb : v=b
      · subst v
        simpa only [rootForcing,Ne.symm hab,ite_false,ite_true] using k.2.2.1
      · have ha : (Q.atom v).1 ≠ (Q.atom a).1 := fun h => hva ((Q.atom_val_eq_iff v a).mp h)
        have hb : (Q.atom v).1 ≠ (Q.atom b).1 := fun h => hvb ((Q.atom_val_eq_iff v b).mp h)
        simpa only [rootForcing,hva,hvb,ite_false] using k.2.2.2 (Q.atom v).1 (Q.atom v).2 ha hb
  · simpa only [Q.flow_eq,Equiv.symm_apply_apply,rootForcing,ite_true] using k.2 a
  · simpa only [Q.flow_eq,Equiv.symm_apply_apply,rootForcing,Ne.symm hab,ite_false,ite_true] using k.2 b
  · intro v hv hva hvb
    let w := Q.atom.symm ⟨v,hv⟩
    have hw : (Q.atom w).1=v := congrArg Subtype.val (Q.atom.apply_symm_apply ⟨v,hv⟩)
    have ha : w ≠ a := by
      intro h
      apply hva
      rw [← hw,h]
    have hb : w ≠ b := by
      intro h
      apply hvb
      rw [← hw,h]
    rw [← hw,Q.flow_eq]
    simpa only [Equiv.symm_apply_apply,rootForcing,ha,hb,ite_false] using k.2 w
  · intro k
    apply Subtype.ext
    funext e
    exact congrArg k.1 (Q.edge.apply_symm_apply e)
  · intro k
    apply Subtype.ext
    funext e
    exact congrArg k.1 (Q.edge.symm_apply_apply e)

end WaveTurbulence.Vine.Param.DirectedBondModel
