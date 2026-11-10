/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceDecorationGrafts
public import WaveTurbulence.Foundations.RegStruct.ChainMiniFidelity

/-! # Bare outer chain templates and their literal source-ordered inserted couples -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Decoration blocks concatenate in their source list order. -/
theorem decorationPairs_append (E F : List CoupleDecoration) :
    decorationPairs (E ++ F) = decorationPairs E ++ decorationPairs F := by
  simp only [decorationPairs,List.flatMap_append]

@[simp] theorem decorationPairs_nil : decorationPairs [] = [] := rfl

theorem decorationPairs_cons (e : CoupleDecoration) (E : List CoupleDecoration) :
    decorationPairs (e :: E) = e.2.pairsAt e.1.1 e.1.2 ++ decorationPairs E := rfl

/-- Retain the actual legal spine and mini-tree codes, replacing its side couples by leaf pairs. -/
def eraseChainCouples : RegChain → RegChain
  | .nil => .nil
  | .pair k _ _ i s => .pair k .triv .triv (eraseChainCouples i) (eraseChainCouples s)

/-- The erased chain is an actual bare chain. -/
theorem eraseChainCouples_bare (X : RegChain) : BareChain (eraseChainCouples X) := by
  cases X with
  | nil => trivial
  | pair k r g i s => exact ⟨rfl,rfl,eraseChainCouples_bare i,eraseChainCouples_bare s⟩
termination_by structural X

/-- Erasing side couples retains the literal lone position. -/
theorem eraseChainCouples_lonePath (X : RegChain) : (eraseChainCouples X).lonePath = X.lonePath := by
  cases X with
  | nil => rfl
  | pair k r g i s => simp only [eraseChainCouples,RegChain.lonePath,eraseChainCouples_lonePath i,eraseChainCouples_lonePath s]
termination_by structural X

/-- Actual red/green frame and side-couple data, in the source's first-pair/inner/rest order. -/
def chainDecorations : RegChain → ℤˣ → (Fin 2 × Path) → List CoupleDecoration
  | .nil,_,_ => []
  | .pair k r g i s,ζ,a =>
    [(chainRedFrame k i ζ a,r),(chainGreenFrame k i ζ a,g)] ++
      chainDecorations i (slotSign ζ k.c) (addrExt a [k.c]) ++
      chainDecorations s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)

/-- The decoration frames are precisely the actual bare template's oriented leaf pairs. -/
theorem chainDecorations_frames (X : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path) :
    (chainDecorations X ζ a).map Prod.fst = (eraseChainCouples X).pairsAt ζ a := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    rw [eraseChainCouples,chain_pairsAt_frames]
    simp only [chainDecorations,List.map_append,List.map_cons,
      chainDecorations_frames i,chainDecorations_frames s,RegCpl.pairsAt,
      chainRedFrame,chainGreenFrame,backRoot,eraseChainCouples_lonePath,
      List.cons_append,List.nil_append,Prod.eta]
termination_by structural X

/-- Inserting each listed couple gives exactly the desired actual chain pair list. -/
theorem chainDecorations_pairs (X : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path) :
    decorationPairs (chainDecorations X ζ a) = X.pairsAt ζ a := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    rw [chainDecorations,decorationPairs_append,decorationPairs_append,
      decorationPairs_cons,decorationPairs_cons,decorationPairs_nil,List.append_nil,
      chainDecorations_pairs i,chainDecorations_pairs s,chain_pairsAt_frames]
termination_by structural X

/-- Every recorded inserted couple is well formed when the chain data are well formed. -/
theorem chainDecorations_wf (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) (a : Fin 2 × Path)
    (e : CoupleDecoration) (he : e ∈ chainDecorations X ζ a) : e.2.wf = true := by
  cases X with
  | nil => simp [chainDecorations] at he
  | pair k r g i s =>
    simp only [RegChain.wf,Bool.and_eq_true] at hX
    simp only [chainDecorations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with ((rfl | rfl) | hi) | hs
    · exact hX.1.1.1
    · exact hX.1.1.2
    · exact chainDecorations_wf i hX.1.2 _ _ e hi
    · exact chainDecorations_wf s hX.2 _ _ e hs
termination_by structural X

/-- Every recorded inserted couple has strictly smaller order than its containing nonempty chain. -/
theorem chainDecorations_size_lt (X : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path)
    (e : CoupleDecoration) (he : e ∈ chainDecorations X ζ a) : e.2.size < X.size := by
  cases X with
  | nil => simp [chainDecorations] at he
  | pair k r g i s =>
    simp only [chainDecorations,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with ((rfl | rfl) | hi) | hs
    · simp only [RegChain.size]; omega
    · simp only [RegChain.size]; omega
    · have hh := chainDecorations_size_lt i _ _ e hi
      simp only [RegChain.size]
      omega
    · have hh := chainDecorations_size_lt s _ _ e hs
      simp only [RegChain.size]
      omega
termination_by structural X

end WaveTurbulence.Reg
