/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.TreeSide
public import WaveTurbulence.Foundations.VineEst.ZpSurj.PatRoot
public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons5
public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin7

/-! # ZP-SURJ: the exceptional datum of an LF operation and the two graft layered gardens -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool)

/-- The address of the positive root of the exceptional couple in the base garden of choice `ε`. -/
@[expose] noncomputable def cA : Fin w × Path :=
  inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode

/-- The address of the negative root of the exceptional couple. -/
@[expose] noncomputable def cB : Fin w × Path :=
  inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode

/-- The address of the lower branch (the nil regular tree) in the base garden. -/
@[expose] noncomputable def tA : Fin w × Path :=
  inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode

/-- The sign of the exceptional regular tree. -/
@[expose] noncomputable def srcSign : ℤˣ := nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1

/-- **The exceptional datum**: a coherent replacement of the exceptional pair, with the layerreg1 patterns for the
parent layers read off the base garden of choice `ε`, the lone-leaf layer of the base, and the order and layer-`p`
count of the source. -/
structure ExcDatum (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1) : Prop where
  hQ : Q.wf = true
  hX : X.wf = true
  dQ : Q.Decodes LQ.garden
  dX : X.DecodesTree LX.garden
  sig : LX.garden.sig 0 = srcSign s ε
  patQ : LayerPatternN LQ (parAt (s.base ε) p (cA s ε)) (parAt (s.base ε) p (cB s ε)) Q
    ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
  patX : TreePatternN LX (parAt (s.base ε) p (tA s ε)) X (srcSign s ε) ((0 : Fin 1), ([] : Path))
  lone : layerAt LX ((0 : Fin 1), X.lonePath) = layerAt (s.base ε) (tA s ε)
  size : X.size + Q.size = (s.data.tree s.placement.lower).size + (s.data.couple s.exceptional).size

variable {s ε}

theorem exc_embM (Q : RegCpl) (hQ : Q.wf = true) :
    Embeds ((s.midData ε Q hQ).garden (s.chosen_plain ε)) Q (cA s ε) (cB s ε) := by
  have h := reconstruction_coupleEmb (s.midData ε Q hQ) (s.chosen_plain ε)
    ((s.midData ε Q hQ).garden_decodes (s.chosen_plain ε)) (s.pairs ε s.exceptional)
  have e : (s.midData ε Q hQ).couple (s.pairs ε s.exceptional) = Q := Function.update_self _ _ _
  rw [e] at h
  exact h

theorem exc_embB : Embeds (s.base ε).garden .triv (cA s ε) (cB s ε) := by
  have h := reconstruction_coupleEmb (s.baseData ε) (s.chosen_plain ε) (s.base_decodes ε) (s.pairs ε s.exceptional)
  rw [baseData_couple_exc s ε] at h
  exact h

theorem exc_gout (Q : RegCpl) (hQ : Q.wf = true) :
    GOut (s.base ε).garden ((s.midData ε Q hQ).garden (s.chosen_plain ε)) (cA s ε) (cB s ε) :=
  gout_couple (s.chosen_plain ε) (s.baseData ε) (s.base_decodes ε) (s.pairs ε s.exceptional)
    (baseData_couple_exc s ε) Q hQ

variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

theorem ExcDatum.rootA (hD : ExcDatum s ε Q X LQ LX) :
    layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ parAt (s.base ε) p (cA s ε) :=
  (layerPatternN_root_le hD.patQ).1

theorem ExcDatum.rootB (hD : ExcDatum s ε Q X LQ LX) :
    layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ parAt (s.base ε) p (cB s ε) :=
  (layerPatternN_root_le hD.patQ).2

/-- The layered garden after the couple reinsertion. -/
@[expose] noncomputable def midG (hD : ExcDatum s ε Q X LQ LX) : LayeredGarden w :=
  graftC (exc_embM (s := s) (ε := ε) Q hD.hQ).indep exc_embB (exc_embM Q hD.hQ) (exc_gout Q hD.hQ)
    hD.dQ hD.rootA hD.rootB

end WaveTurbulence.ZpSurj
