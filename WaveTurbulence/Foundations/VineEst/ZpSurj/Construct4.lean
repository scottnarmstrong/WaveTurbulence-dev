/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct3

/-! # ZP-SURJ: existence of the LF construction (the main step) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

theorem coupleRoot_zero (s : LFSource p kind LG) (ε : Bool) :
    coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0 = cA s ε := by
  simp [coupleRoot, cA]

theorem coupleRoot_one (s : LFSource p kind LG) (ε : Bool) :
    coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1 = cB s ε := by
  simp [coupleRoot, cB]

/-- The graft layered garden after both reinsertions. -/
@[expose] noncomputable def outG (hD : ExcDatum s ε Q X LQ LX) (t : TTree)
    (hEO : ChainEmb (midG hD).garden .nil (srcSign s ε) (tA s ε) t)
    (hEN : ChainEmb ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t)
    (hOutT : GOutT (midG hD).garden ((s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) (tA s ε)
      (addrExt (tA s ε) X.lonePath)) : LayeredGarden w :=
  graftT (LM := midG hD) (M' := (s.finalData ε X Q hD.hX hD.hQ).garden (s.chosen_plain ε)) hEO hEN hD.hEX hOutT
    hD.lone' hD.root'

end WaveTurbulence.ZpSurj
