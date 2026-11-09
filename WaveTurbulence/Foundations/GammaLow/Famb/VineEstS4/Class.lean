/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Kernel
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.PieceFamily
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.Class` (sha256 55853ba27c531ff9…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The twist class of a vine chain and its sections (V5 Step 4a)

`ClassSectionK p kind A c Z`: `Z` is a finite set of (state, chain region) pairs, each reached from `(A, c)` by a
once-per-member LF batch over all core members (`Reach`), whose layered gardens are pairwise distinct and exactly the
class `A.allCoreOutputs` (M7; S1's `congruent_layered_iff`).  `exists_classSection` shows sections exist (so the
statement `VineEstFull` is not vacuous); with no available operation the only section is the start (`BaseCase`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The state of `(G, RD, layer)` with the core family of the pieces of the chain. -/
@[expose] noncomputable def startStateΓ (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    FamilyReconstruction w (assemblySourceFamilyΓ B).CoreIndex where
  skeleton := G
  family := (assemblySourceFamilyΓ B).coreFamily
  plain := hG
  data := RD
  layered := layeredReconstruction RD hG layer hLayer
  decodes := RD.garden_decodes hG

/-- The chain region of the assembly, as a region of the start state. -/
@[expose] noncomputable def chainStartΓ (B : CLChainAssemblyΓ γF G R n) : ChainAt G (assemblySourceFamilyΓ B).coreFamily where
  U := U
  a := a
  b := b
  block := B.isBlock
  cl := R.parentPattern
  atoms_sub := fun i => assemblyPiece_subsetΓ B i.1
  lower_ne := fun i => by
    have h1 := ((assemblySourceFamilyΓ B).corePlacement_at i).1
    change ((assemblySourceFamilyΓ B).corePlacement i).lower ≠ a
    rw [h1]
    exact (Finset.mem_erase.mp (lower_mem_interiorΓ B i.1)).1

section Finite
variable {ι : Type*} {p : ℕ} {kind : Bool}

end Finite

end WaveTurbulence.GammaLow.Famb.VineEstS4
