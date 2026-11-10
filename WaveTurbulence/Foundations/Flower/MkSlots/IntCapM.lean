/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapT
public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember1

/-! # B3s MK-SLOTS (integration, R-cap): the pinned cap slot kernels are common to the run class

For a cap pair `q` of `G_sb` and a member `y` of the run class of the representative `a`, the pinned weighted cap slot
kernel of `y` at its slot `Φ_y.iota (.inl q)` is the representative's `capSlotKer` at `Φ_a.iota (.inl q)`
(`member_capSlot`). Both are `IntCapT.capT_kernel` of their native couple (`capT_slot_eq`), and
* the native couples coincide (the native-couple chain, `memShape_nativeCouple`);
* the root tree indices are those of the `G_sb` leaves (`SpliceShape.tree_eq`);
* the last address letters agree when the flower-side leaf has a non-hinge parent in `G_sb` (it is then the same
  child of the same `G_sb` atom); when the parent is a hinge, the couple is not trivial on the flower side
  (`rep_hinge_not_attLeaf`), so no root is a capped flower and the kernel does not read the last letters
  (`capT_kernel_rl_indep`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine

namespace WaveTurbulence.Flower.MkSlots.IntCapM

open WaveTurbulence.Flower.MkSlots.IntCapT WaveTurbulence.Flower.MkSlots.IntCore
  WaveTurbulence.Flower.MkSlots.IntMember

/-! ### Through a splice shape -/

section Shape
variable {w : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G) (D : ReconstructionData S) (hS : S.IsPlain) (hG : G.IsPlain)

/-- The root of the native couple of the image of a `G_sb` pair, on side `c`. -/
theorem coupleRoot_iota_val (q : SourcePair G) (c : Fin 2) :
    coupleRoot D hS (pairOfLeaf S hS (Φ.leaf (q.firstLeaf hG))) c =
      inflatedPosition S D.tree (Φ.leaf (if c = 0 then q.firstLeaf hG else q.secondLeaf hG)).toNode := by
  unfold coupleRoot
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue, if_true]
    rw [Φ.iota_first hS hG q]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    rw [Φ.iota_second hS hG q]

end Shape

/-! ### The run class -/

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

end Class

end WaveTurbulence.Flower.MkSlots.IntCapM
