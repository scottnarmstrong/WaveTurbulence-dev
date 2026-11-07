/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.CountBridge

/-! # ZP-SURJ: existence of the LF construction, with the count in native form -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

/-- The layer-`p` count hypothesis of `construction`, from the count in native form. -/
theorem hcnt_of_count (hD : ExcDatum s ε Q X LQ LX)
    (hc : rawTreeLayerCount LG s.data s.plain p s.placement.lower +
        rawCoupleLayerCount LG s.data s.plain p s.exceptional = topBranchCount LX p + topBranchCount LQ p) :
    ∀ (t : TTree) (hEO : ChainEmb (midG hD).garden .nil (srcSign s ε) (tA s ε) t)
      (hEN : ChainEmb ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t)
      (hOutT : GOutT (midG hD).garden ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (tA s ε)
        (addrExt (tA s ε) X.lonePath)),
      rawTreeLayerCount LG s.data s.plain p s.placement.lower +
        rawCoupleLayerCount LG s.data s.plain p s.exceptional =
      rawTreeLayerCount (outG hD t hEO hEN hOutT) (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) p
        (s.branches ε s.placement.lower) +
      rawCoupleLayerCount (outG hD t hEO hEN hOutT) (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) p
        (s.pairs ε s.exceptional) := by
  intro t hEO hEN hOutT
  rw [hc]
  have h1 := raw_tree_bridge (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
    (outG hD t hEO hEN hOutT).isLayering p (s.branches ε s.placement.lower)
  have h2 := raw_couple_bridge (s.finalData ε X Q hD.hX hD.hQ) (s.chosen_plain ε) (outG hD t hEO hEN hOutT).layer
    (outG hD t hEO hEN hOutT).isLayering p (s.pairs ε s.exceptional)
  rw [native_chain_eq hD t hEO hEN hOutT] at h1
  rw [native_couple_eq hD t hEO hEN hOutT] at h2
  exact (congrArg₂ (· + ·) h1 h2).symm

end WaveTurbulence.ZpSurj
