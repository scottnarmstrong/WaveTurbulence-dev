/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSideCarrierRecovery

/-! # Exact predicates for the simultaneous structure-data uniqueness induction -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Couple-code uniqueness through a bounded actual code order. -/
def CoupleUniqueUpTo (N : ℕ) : Prop :=
  ∀ C D : RegCpl, C.size ≤ N → C.wf = true → D.wf = true →
    decodedCouple C = decodedCouple D → C = D

/-- Chain-code uniqueness in an actual ambient decoded carrier and fixed terminal slot. -/
def ChainUniqueUpTo (N : ℕ) : Prop :=
  ∀ X Y : RegChain, X.size ≤ N → X.wf = true → Y.wf = true →
    ∀ (Q : RegCpl) (G : Garden 2), Q.Decodes G → ∀ (a : Fin 2 × Path) (ζ : ℤˣ) (h h' : TTree),
    Comb.subtree (G.tree a.1) a.2 = some (X.plug ζ h) →
    Comb.subtree (G.tree a.1) a.2 = some (Y.plug ζ h') →
    (∀ p ∈ X.pairsAt ζ a, p ∈ Q.raw.2) →
    (∀ p ∈ Y.pairsAt ζ a, p ∈ Q.raw.2) → X.lonePath = Y.lonePath → X = Y

end WaveTurbulence.Reg
