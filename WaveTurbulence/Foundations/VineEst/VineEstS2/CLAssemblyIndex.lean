/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPrefixAnchor
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ChosenChart
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainInteriorPartition

/-! # Recursive actual chain chart indices and their exact source dimension -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

namespace CLChainAssembly
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

noncomputable def terminalRegion {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssembly G RP n)
    {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) : CLRegionData G T b c :=
  clRegionData G hT.1 (clBlockConcat_parentPatterns B.isBlock hT.1 hi hU R).2

noncomputable def terminalAnchor {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssembly G RP n)
    {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) : Bond G.molecule T :=
  clPrefixAnchorBond B.isBlock hT.1 RP (B.terminalRegion hT hi hU R) hi

end CLChainAssembly

/-- Bottom-to-top recursive block slots. Their Sigma/sumint transport is
separate, so the dependent triangular chart can be built on these indices. -/
noncomputable def chainInputIndex (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Type :=
  match B with
  | .single hV _ => Fin (chosenVineChart hM9 _ hV).indexing.shape.n
  | .append B hT _ _ _ => Fin (chosenVineChart hM9 _ hT).indexing.shape.n ⊕ chainInputIndex hM9 B

noncomputable instance chainInputFintype (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Fintype (chainInputIndex hM9 B) :=
  match B with
  | .single hV _ => Fin.fintype (chosenVineChart hM9 _ hV).indexing.shape.n
  | .append B hT _ _ _ => @instFintypeSum _ _
      (Fin.fintype (chosenVineChart hM9 _ hT).indexing.shape.n) (chainInputFintype hM9 B)

/-- The full input count is the actual n_(1) of the original regional tree. -/
theorem card_chainInputIndex (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : Fintype.card (chainInputIndex hM9 B) = clLocalOrder1 R := by
  induction B with
  | single hV R =>
    change Fintype.card (Fin (chosenVineChart hM9 _ hV).indexing.shape.n) = _
    rw [Fintype.card_fin]
    exact vineChart_dimension R (chosenVineChart hM9 _ hV)
  | @append S T a b c n RP B X hT hi hU R ih =>
    change Fintype.card (Fin (chosenVineChart hM9 X hT).indexing.shape.n ⊕ chainInputIndex hM9 B) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    have hTdim := vineChart_dimension (B.terminalRegion hT hi hU R) (chosenVineChart hM9 X hT)
    change (chosenVineChart hM9 X hT).indexing.shape.n = (T.erase b).card at hTdim
    have hS := B.isBlock
    have hpart := chainInterior_card S T a b hS.2.1 hS.2.2.1 hS.2.2.2.1 hi
    change _ = ((S ∪ T).erase a).card
    change Fintype.card (chainInputIndex hM9 B) = (S.erase a).card at ih
    change (chosenVineChart hM9 X hT).indexing.shape.n+(S.erase a).card = _
    omega

end WaveTurbulence.VineEstS2
