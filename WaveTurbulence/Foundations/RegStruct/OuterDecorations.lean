/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainDecorations
public import WaveTurbulence.Foundations.RegStruct.SourceOuterTemplates

/-! # Literal complete decoration lists of both source outer template families -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- The three actual colour frames and their inserted couples. -/
def type1Decorations (c : MiniCplCode) (r g d : RegCpl) : List CoupleDecoration :=
  [(type1Frame c 0,r),(type1Frame c 1,g),(type1Frame c 2,d)]

/-- Type-1 decoration frames are exactly the chosen source mini-couple's leaf pairs. -/
theorem type1Decorations_frames (c : MiniCplCode) (r g d : RegCpl) :
    (type1Decorations c r g d).map Prod.fst = (miniCoupleCode c).raw.2 := by
  simp [type1Decorations,type1Frame,miniCoupleCode,RegCpl.raw,RegCpl.pairsAt,addrExt]

/-- Type-1 decoration blocks reproduce the desired actual oriented pair list. -/
theorem type1Decorations_pairs (c : MiniCplCode) (r g d : RegCpl) :
    (RegCpl.type1 c r g d).raw.2 = decorationPairs (type1Decorations c r g d) := by
  simp [type1Decorations,type1Frame,decorationPairs,RegCpl.raw,RegCpl.pairsAt,addrExt,List.append_assoc]

/-- Every red/green side couple, followed by the terminal couple. -/
def type2Decorations (p n : RegChain) (q : RegCpl) : List CoupleDecoration :=
  chainDecorations p 1 (0,[]) ++ chainDecorations n (-1) (1,[]) ++
    [((((0 : Fin 2),p.lonePath),(1,n.lonePath)),q)]

/-- Type-2 decoration frames are exactly the actual bare double-chain template's pairs. -/
theorem type2Decorations_frames (p n : RegChain) (q : RegCpl) :
    (type2Decorations p n q).map Prod.fst = (joinChains (eraseChainCouples p) (eraseChainCouples n) .triv).raw.2 := by
  simp only [type2Decorations,List.map_append,List.map_cons,List.map_nil,
    chainDecorations_frames,doubleChain_pairs,eraseChainCouples_lonePath]

/-- Type-2 decoration blocks reproduce the complete desired source pair list. -/
theorem type2Decorations_pairs (p n : RegChain) (q : RegCpl) :
    (RegCpl.type2 p n q).raw.2 = decorationPairs (type2Decorations p n q) := by
  rw [type2Decorations,decorationPairs_append,decorationPairs_append,
    chainDecorations_pairs,chainDecorations_pairs,decorationPairs_cons,decorationPairs_nil,List.append_nil]
  rfl

/-- All actual inserted type-2 couples are well formed under the pinned code's typing premises. -/
theorem type2Decorations_wf (p n : RegChain) (q : RegCpl) (hw : (RegCpl.type2 p n q).wf = true)
    (e : CoupleDecoration) (he : e ∈ type2Decorations p n q) : e.2.wf = true := by
  simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hw
  simp only [type2Decorations,List.mem_append,List.mem_singleton] at he
  rcases he with (hp | hn) | rfl
  · exact chainDecorations_wf p hw.1.1.1.1 _ _ e hp
  · exact chainDecorations_wf n hw.1.1.1.2 _ _ e hn
  · exact hw.1.1.2

/-- Every actual inserted couple is strictly smaller than the containing well-formed type-2 code. -/
theorem type2Decorations_size_lt (p n : RegChain) (q : RegCpl) (hw : (RegCpl.type2 p n q).wf = true)
    (e : CoupleDecoration) (he : e ∈ type2Decorations p n q) : e.2.size < (RegCpl.type2 p n q).size := by
  have hpos : 2 ≤ p.size+n.size := by
    simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hw
    rcases Bool.and_eq_false_iff.mp hw.2 with hp | hn
    · have hh := chain_size_pos_of_not_isNil hp; omega
    · have hh := chain_size_pos_of_not_isNil hn; omega
  simp only [type2Decorations,List.mem_append,List.mem_singleton] at he
  rcases he with (hp | hn) | rfl
  · have hh := chainDecorations_size_lt p 1 (0,[]) e hp
    simp only [RegCpl.size]; omega
  · have hh := chainDecorations_size_lt n (-1) (1,[]) e hn
    simp only [RegCpl.size]; omega
  · simp only [RegCpl.size]; omega

end WaveTurbulence.Reg
