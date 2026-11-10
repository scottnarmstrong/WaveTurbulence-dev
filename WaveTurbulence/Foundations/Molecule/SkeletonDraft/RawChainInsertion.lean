/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Literal insertion of a regular chain context above a complete existing subtree -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Retain the full original subtree at the chain's lone slot, retain every original
pair through prefix transport, and add exactly the chain's internal pairs. -/
noncomputable def Raw.insertChain {w : ℕ} (R : Raw w) (a : Address w) (X : RegChain) : Raw w :=
  ⟨R.sig,Function.update R.tree a.1 ((R.tree a.1).setAt a.2
    (X.plug (nodeSign R.sig a) ((R.tree a.1).subtreeAt a.2))),
    R.pairs.image (fun p => (stretch a X.lonePath p.1,stretch a X.lonePath p.2)) ∪
      (X.pairsAt (nodeSign R.sig a) a).toFinset⟩

theorem miniChain_pairsAt_finset {w : ℕ} (m : MiniTreeCode) (σ : Fin w → ℤˣ) (a : Address w) :
    ((miniChain m).pairsAt (nodeSign σ a) a).toFinset = miniPairs σ a m := by
  classical
  by_cases hr : slotSign (nodeSign σ a) m.red.1 = 1 <;>
    by_cases hg : slotSign (nodeSign σ a) m.green.1 = 1 <;>
    simp [miniChain,RegChain.pairsAt,RegCpl.pairsAt,RegChain.lonePath,miniPairs,orient,hr,hg]

end WaveTurbulence.Reg.Skeleton
