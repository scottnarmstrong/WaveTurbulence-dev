/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons1
import Mathlib.Tactic

/-!
# Glue specification: the glued mid and out layered gardens and their insertion records
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem cci_congr {LG' LH : LayeredGarden w} {a b : Address w} {Q Q' : RegCpl} (e : Q = Q')
    (h : CoherentCoupleInsertion p LG' LH a b Q) : CoherentCoupleInsertion p LG' LH a b Q' := e ▸ h

theorem cti_congr {LG' LH : LayeredGarden w} {a a' : Address w} {ζ : ℤˣ} {t : TTree} {X X' : RegChain}
    (ea : a = a') (eX : X = X') (h : CoherentTreeInsertion p LG' LH a ζ t X) :
    CoherentTreeInsertion p LG' LH a' ζ t X' := by subst ea; subst eX; exact h

namespace GlueSpec
variable {s : LFSource p kind LG} {ε : Bool} (g : GlueSpec s ε)

/-- The glued layered garden after the couple reinsertion. -/
@[expose] noncomputable def glued1 : LayeredGarden w := g.glueC.glued

theorem coupleInsertion_aux :
    CoherentCoupleInsertion p (s.base ε) g.glued1
      (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0)
      (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) g.Q := by
  have e : (s.midData ε g.Q g.hQ).couple (s.pairs ε s.exceptional) = g.Q := Function.update_self _ _ _
  have hg := base_garden_eq s ε
  have h0 : coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0 =
      inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode := by
    simp [coupleRoot]; rfl
  have h1 : coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1 =
      inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode := by
    simp [coupleRoot]; rfl
  rw [h0, h1]
  refine cci_congr e (g.glueC.insertion (by rw [e]; exact g.patQ) (by rw [e]; exact g.hQ) ?_ ?_ ?_)
  · rw [hg]; rfl
  · change nodeSign (s.base ε).garden.sig (inflatedPosition (s.chosen ε) (s.baseData ε).tree _) = 1
    exact ((s.baseData ε).decodedNode_sign (s.chosen_plain ε) (s.base_decodes ε)
      ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode).trans
      (sourcePair_first_sign _ (s.chosen_plain ε) _)
  · change nodeSign (s.base ε).garden.sig (inflatedPosition (s.chosen ε) (s.baseData ε).tree _) = -1
    exact ((s.baseData ε).decodedNode_sign (s.chosen_plain ε) (s.base_decodes ε)
      ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode).trans
      (sourcePair_second_sign _ (s.chosen_plain ε) _)

end GlueSpec
end WaveTurbulence.Stage1
