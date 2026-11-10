/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Comm1
import Mathlib.Tactic

/-!
# Generic casting lemmas for the diamond of two `true` operations
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- Branch cast along a garden equality (same address). -/
@[expose] def castBranch {S S' : Garden w} (hs : S = S') (b : GBranch S.tree) : GBranch S'.tree :=
  ⟨b.1, (congrArg (fun G : Garden w => b.1.2 ∈ (G.tree b.1.1).branching) hs).mp b.2⟩

@[expose] def castPair {S S' : Garden w} (hs : S = S') (q : SourcePair S) : SourcePair S' :=
  ⟨q.1, (congrArg (fun G : Garden w => q.1 ∈ sourcePairs G) hs).mp q.2⟩

theorem heq_recon {S S' : Garden w} (hs : S = S') (D : ReconstructionData S) (D' : ReconstructionData S')
    (ht : ∀ b : GBranch S.tree, D.tree b = D'.tree (castBranch hs b))
    (hc : ∀ q : SourcePair S, D.couple q = D'.couple (castPair hs q)) : HEq D D' := by
  subst hs
  apply heq_of_eq
  apply ReconstructionData.ext_tree_couple
  · funext b; exact ht b
  · funext q; exact hc q

theorem decodes_of_heq {S S' : Garden w} (hs : S = S') (D : ReconstructionData S) (D' : ReconstructionData S')
    (hD : HEq D D') (hS : S.IsPlain) (hS' : S'.IsPlain) {G : Garden w} (h' : D'.Decodes hS' G) :
    D.Decodes hS G := by
  subst hs
  cases hD
  exact h'

theorem infl_cast {S S' : Garden w} (hs : S = S') (D : ReconstructionData S) (D' : ReconstructionData S')
    (hD : HEq D D') (n : GNode S.tree) (n' : GNode S'.tree) (h : n.1 = n'.1) :
    inflatedPosition S D.tree n = inflatedPosition S' D'.tree n' := by
  subst hs
  cases hD
  have : n = n' := Subtype.ext h
  subst this
  rfl

theorem coupleRoot_cast {S S' : Garden w} (hs : S = S') (D : ReconstructionData S) (D' : ReconstructionData S')
    (hD : HEq D D') (hS : S.IsPlain) (hS' : S'.IsPlain) (q : SourcePair S) (q' : SourcePair S')
    (h : q.1 = q'.1) (j : Fin 2) : coupleRoot D hS q j = coupleRoot D' hS' q' j := by
  subst hs
  cases hD
  have : q = q' := Subtype.ext h
  subst this
  rfl

end WaveTurbulence.Stage1
