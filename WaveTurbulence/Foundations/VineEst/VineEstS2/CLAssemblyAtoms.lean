/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape

/-! # Actual source atom and clock correspondence for the full-chain chart -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Every free slot indexes its original interior branch. At concatenation
the shared joint belongs to the prefix, exactly as in the source. -/
noncomputable def assemblyAtomEquiv (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : chainInputIndex hM9 B ≃ ↥(U.erase a) := by
  induction B with
  | single hV R => exact (chosenVineChart hM9 _ hV).indexing.atom
  | @append S T a b c n RP B X hT hi hU R ih =>
    have hS := B.isBlock
    have hp := chainInterior_union S T a b hS.2.1 hS.2.2.1 hS.2.2.2.1 hi
    exact (Equiv.sumCongr (chosenVineChart hM9 X hT).indexing.atom ih).trans
      ((Equiv.sumComm _ _).trans ((Equiv.Finset.union _ _ (chainInterior_disjoint S T a b hi)).trans
        (Set.equivOfEq (congrArg (fun q : Finset (GBranch G.tree) => (q : Set (GBranch G.tree))) hp.symm))))

noncomputable def assemblyVectorAtomEquiv (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : (assemblyShape hM9 B).VIdx ≃ ↥(U.erase a) :=
  (assemblyVectorEquiv hM9 B).symm.trans (assemblyAtomEquiv hM9 B)

noncomputable def assemblyClockAtomEquiv (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : (assemblyShape hM9 B).TVar ≃ ↥(U.erase a) :=
  (assemblyTimeEquiv hM9 B).trans (assemblyAtomEquiv hM9 B)

end WaveTurbulence.VineEstS2
