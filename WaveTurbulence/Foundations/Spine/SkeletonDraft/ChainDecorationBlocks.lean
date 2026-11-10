/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs
public import WaveTurbulence.Foundations.Molecule.DominantChains

/-! # Source-ordered side-couple blocks of a chain context at arbitrary forest width -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

abbrev Decoration (w : ℕ) := ((Fin w × Path) × (Fin w × Path)) × RegCpl

def chainDecorationBlocks {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) → List (Decoration w)
  | .nil,_,_ => []
  | .pair m r g i s,ζ,a =>
    [((if slotSign ζ m.red.1 = 1 then
        (addrExt a [m.red.1],addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])) else
        (addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]),addrExt a [m.red.1])),r),
      ((if slotSign ζ m.green.1 = 1 then
        (addrExt a [m.green.1],addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])) else
        (addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]),addrExt a [m.green.1])),g)] ++
      chainDecorationBlocks i (slotSign ζ m.c) (addrExt a [m.c]) ++
      chainDecorationBlocks s (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))

theorem chainDecorationBlocks_frames {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (chainDecorationBlocks X ζ a).map Prod.fst = (eraseChainCouples X).pairsAt ζ a := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;> by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp [chainDecorationBlocks,eraseChainCouples,RegChain.pairsAt,RegCpl.pairsAt,
        RegChain.lonePath,eraseChainCouples_lonePath,chainDecorationBlocks_frames i,
        chainDecorationBlocks_frames s,hr,hg]
termination_by structural X

theorem chainDecorationBlocks_pairs {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (chainDecorationBlocks X ζ a).flatMap (fun e => e.2.pairsAt e.1.1 e.1.2) = X.pairsAt ζ a := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;> by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp [chainDecorationBlocks,RegChain.pairsAt,chainDecorationBlocks_pairs i,
        chainDecorationBlocks_pairs s,hr,hg]
termination_by structural X

theorem chainDecorationBlocks_wf {w : ℕ} (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ)
    (a : Fin w × Path) (e : Decoration w) (he : e ∈ chainDecorationBlocks X ζ a) : e.2.wf = true := by
  cases X with
  | nil => simp [chainDecorationBlocks] at he
  | pair m r g i s =>
    simp only [RegChain.wf,Bool.and_eq_true] at hX
    simp only [chainDecorationBlocks,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with ((rfl | rfl) | hi) | hs
    · exact hX.1.1.1
    · exact hX.1.1.2
    · exact chainDecorationBlocks_wf i hX.1.2 _ _ e hi
    · exact chainDecorationBlocks_wf s hX.2 _ _ e hs
termination_by structural X

end WaveTurbulence.Reg.Skeleton
