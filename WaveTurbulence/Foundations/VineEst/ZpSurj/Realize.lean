/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Coh3

/-! # ZP-SURJ: the realized construction of an exceptional datum -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

/-- The construction of a datum whose count matches the source. -/
@[expose] noncomputable def construction' (hD : ExcDatum s ε Q X LQ LX)
    (hc : rawTreeLayerCount LG s.data s.plain p s.placement.lower +
        rawCoupleLayerCount LG s.data s.plain p s.exceptional = topBranchCount LX p + topBranchCount LQ p) :
    LFConstruction s ε :=
  construction hD (hcnt_of_count hD hc)

theorem construction'_newTree (hD : ExcDatum s ε Q X LQ LX) (hc) : (construction' hD hc).newTree = X := rfl

theorem construction'_newCouple (hD : ExcDatum s ε Q X LQ LX) (hc) : (construction' hD hc).newCouple = Q := rfl

theorem conLQ_construction' (hD : ExcDatum s ε Q X LQ LX) (hc) : conLQ (construction' hD hc) = LQ :=
  native_couple_eq hD (Classical.choose (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX))
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).1
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.1
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.2

theorem conLX_construction' (hD : ExcDatum s ε Q X LQ LX) (hc) : conLX (construction' hD hc) = LX :=
  native_chain_eq hD (Classical.choose (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX))
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).1
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.1
    (Classical.choose_spec (exc_tree_side (s := s) (ε := ε) Q hD.hQ X hD.hX)).2.2

end WaveTurbulence.ZpSurj
