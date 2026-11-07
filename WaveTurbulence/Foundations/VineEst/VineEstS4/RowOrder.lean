/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement

/-! # The standing garden-order bound and the row sizes (V5 Step 4b, ruling on RowSizes)

TARGET's standing bound is on the total garden order `n ≤ N_{p+1}^4` (L806-L810).  Every regular object of a row is
a sub-object of the garden, so its order is at most the garden order: `rowSizes_of_order`.  The LF twists preserve the
total order (`FamilyBatch.order`), hence every member garden of the class satisfies the same bound and its rows
the same `RowSizes` (`Reach.rowSizes`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Every replacement of a reconstruction has order at most the total replacement order. -/
theorem rowSizes_of_dataSize (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) {Nb : ℕ} (h : RD.size ≤ Nb) : RowSizes hM9 B RD hG Nb := by
  intro v
  constructor
  · have : (rowCouple hM9 B RD hG v).size ≤ RD.size := by
      unfold ReconstructionData.size
      exact le_trans (Finset.single_le_sum (f := fun p => (RD.couple p).size) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)) (Nat.le_add_left _ _)
    omega
  · have : (rowTree hM9 B RD v).size ≤ RD.size := by
      unfold ReconstructionData.size
      exact le_trans (Finset.single_le_sum (f := fun b => (RD.tree b).size) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ _)) (Nat.le_add_right _ _)
    omega

/-- **Garden-order bound gives the row sizes.** -/
theorem rowSizes_of_order (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) {Nb : ℕ} (h : (RD.garden hG).order ≤ Nb) : RowSizes hM9 B RD hG Nb := by
  apply rowSizes_of_dataSize
  have := RD.decoded_order hG (RD.garden_decodes hG)
  omega

/-- Row sizes of any reconstruction state of bounded garden order, in particular of every member garden of the
twist class (its assembly `B1` from `Reach.exists_asm`). -/
theorem rowSizes_of_state {ι : Type*} (hM9 : VINEPARAM) (Bs : FamilyReconstruction w ι)
    {U' : Finset (GBranch Bs.skeleton.tree)} {a' b' : GBranch Bs.skeleton.tree}
    {R' : CLRegionData Bs.skeleton U' a' b'} (B' : CLChainAssembly Bs.skeleton R' n) {Nb : ℕ}
    (h : Bs.layered.garden.order ≤ Nb) :
    RowSizes hM9 B' Bs.data Bs.plain Nb := by
  apply rowSizes_of_dataSize
  have := Bs.data.decoded_order Bs.plain Bs.decodes
  omega

/-- The garden order of every state reached from the start is the start's garden order. -/
theorem Reach.order_eq {ι : Type*} {p : ℕ} {kind : Bool} {L : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind L A c B c') :
    B.layered.garden.order = A.layered.garden.order :=
  h.batch.order

end WaveTurbulence.VineEstS4
