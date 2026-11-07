/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin6
public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueData4
public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC11
public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT7
import Mathlib.Tactic

/-!
# Glue specification: an LF construction built from a template pair of records
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem base_garden_eq (s : LFSource p kind LG) (ε : Bool) :
    (s.base ε).garden = (s.baseData ε).garden (s.chosen_plain ε) :=
  rawOfGarden_injective_plain (s.base_decodes ε).1 ((s.baseData ε).garden_plain _)
    ((s.base_decodes ε).2.symm.trans ((s.baseData ε).garden_raw _).symm)

/-- The template data for gluing new exceptional objects into the base of `s` at choice `ε`. -/
structure GlueSpec (s : LFSource p kind LG) (ε : Bool) where
  X : RegChain
  Q : RegCpl
  hX : X.wf = true
  hQ : Q.wf = true
  Tm : LayeredGarden w
  To : LayeredGarden w
  aT : Fin w × Path
  bT : Fin w × Path
  aT2 : Fin w × Path
  t' : TTree
  embQ : Embeds Tm.garden Q aT bT
  patQ : LayerPattern Tm p Q aT bT
  embX : ChainEmb To.garden X (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) aT2 t'
  patX : TreePattern To p X (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) aT2
  hpa : parAt Tm p aT = parAt (s.base ε) p
    (inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
  hpb : parAt Tm p bT = parAt (s.base ε) p
    (inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
  hpl : parAt To p aT2 = parAt (s.base ε) p
    (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
  hlone : layerAt To (addrExt aT2 X.lonePath) = layerAt (s.base ε)
    (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
  hpm : ∀ n, Tm.layer n ≤ p
  hpo : ∀ n, To.layer n ≤ p

namespace GlueSpec
variable {s : LFSource p kind LG} {ε : Bool} (g : GlueSpec s ε)

theorem hLN : (s.base ε).garden =
    ((s.midData ε g.Q g.hQ).eraseCouple (s.pairs ε s.exceptional)).garden (s.chosen_plain ε) := by
  rw [eraseCouple_mid]
  exact base_garden_eq s ε

theorem glueC : GlueC (s.base ε) g.Tm ((s.midData ε g.Q g.hQ).garden (s.chosen_plain ε))
    ((s.midData ε g.Q g.hQ).couple (s.pairs ε s.exceptional))
    (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
    (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
    g.aT g.bT p := by
  refine glueC_ofData (s.midData ε g.Q g.hQ) (s.chosen_plain ε) (s.pairs ε s.exceptional) (s.base ε) g.Tm
    g.hLN g.aT g.bT p ?_ g.hpa g.hpb g.hpm
  have e : (s.midData ε g.Q g.hQ).couple (s.pairs ε s.exceptional) = g.Q := Function.update_self _ _ _
  rw [e]
  exact g.embQ

end GlueSpec
end WaveTurbulence.Stage1
