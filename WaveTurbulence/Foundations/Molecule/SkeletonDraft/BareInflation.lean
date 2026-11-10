/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreEmbedding

/-! # Literal intermediate gardens: bare chains at branches and trivial couples at leaf pairs -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The exact first stage of DH21 Proposition 4.14 and DH21-2 Proposition 4.5. -/
def ReconstructionData.IsBareInflation {w : ℕ} {S : Garden w} (D : ReconstructionData S) : Prop :=
  (∀ b, BareChain (D.tree b)) ∧ ∀ p, D.couple p = .triv

end WaveTurbulence.Reg.Skeleton
