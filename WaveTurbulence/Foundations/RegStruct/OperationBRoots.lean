/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.RootAddressMaps
public import WaveTurbulence.Foundations.RegStruct.RawRepresentation

/-! # Full source fidelity of operation B at either original root (DH21 Proposition 4.8, case 3) -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Code operation B, followed by the proved terminal normalization. -/
def operationB (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode) : RegCpl :=
  normalizeCouple (insertMiniCouple Q (0,[]) (1,[]) target m)

/-- A missing negative chain contributes no pairs or path shift. -/
theorem type2_left_pairsAt {w : ℕ} (X : RegChain) (Q : RegCpl) (a b : Fin w × Path) :
    (RegCpl.type2 X .nil Q).pairsAt a b =
      X.pairsAt 1 a ++ Q.pairsAt (addrExt a X.lonePath) b := by
  simp [RegCpl.pairsAt,RegChain.pairsAt,RegChain.lonePath,addrExt]

/-- A missing positive chain contributes no pairs or path shift. -/
theorem type2_right_pairsAt {w : ℕ} (X : RegChain) (Q : RegCpl) (a b : Fin w × Path) :
    (RegCpl.type2 .nil X Q).pairsAt a b =
      X.pairsAt (-1) b ++ Q.pairsAt a (addrExt b X.lonePath) := by
  simp [RegCpl.pairsAt,RegChain.pairsAt,RegChain.lonePath,addrExt]

/-- Every raw B-step adds two pairs to the source list. -/
theorem raw_opB_pairs_length (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode) :
    (R.opB a m).2.length = R.2.length + 2 := by
  change (R.2.map _ ++ [_,_]).length = _
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]

/-- B always returns well-formed data after normalization. -/
theorem operationB_wf (Q : RegCpl) (a : Fin 2 × Path) (m : MiniTreeCode) :
    (operationB Q a m).wf = true := normalizeCouple_wf _

end WaveTurbulence.Reg
