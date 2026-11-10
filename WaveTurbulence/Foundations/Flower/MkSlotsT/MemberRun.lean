/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Member
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore2

/-! # B3s-HELPER5 (γ) T1 at every member of a run class

For a prescribed point `a` at a marking `mk` (B3's run assembly; at B4's class marking `mk a.prime = classMk mkF a`)
and a member `y` of its run class (`y ∈ sourceClass a p kind mk`, B3's member shape `memShape a mk y hy`):

* `stemRet_repMk`: `CleanPt J a` gives retention for the units at ANY marked set `Mk` (the proof of `stemRet_rep`);
* **`stemRet_member`**: retention for the member's own units `unitClBlock (y.2 j)` on its reconstruction
  (`stemRet_transport`, the hinge data being common, B3's `memShape_hmom`);
* **`kindMember_spec`**: hence T1's classification (`kindOf_spec`) holds at every member, with its own shape — the atoms
  are the same `G_sb` atoms `c` (images `(memShape a mk y hy).br c`), the units are the same `j`, and the slots are the
  member's retained slots. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt)
open WaveTurbulence.Flower.MkDefs (IsCapFlowerParent)

namespace WaveTurbulence.Flower.MkSlotsT

/-- **Retention at the representative for the units at any marked set.** -/
theorem stemRet_repMk {w : ℕ} {J : Finset (Fin w)} {a : PrescribedPrimeGarden w} (hc : CleanPt J a)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    StemRet a.prime.skeleton a.prime.data.tree (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
      a.layered J :=
  stemRet_of_clean a.prime.data.tree _ (vinesV0 a.prime.skeleton a.totalSigma Mk)
    (stemAvoid_of_cleanPt hc Mk) (fun j => Represents.unitN a.totalSigma j)
    (fun j => VineAlign.alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk j)
    (fun j i => MkSlots.alignedPiece_mem_vinesV0 a.totalSigma Mk j i)

/-- Retention only reads the layered garden through its capped flowers. -/
theorem stemRet_congr {w : ℕ} {S : Garden w} {X : GBranch S.tree → RegChain} {ι : Type} {blk : ι → CLBlock S}
    {LG LG' : LayeredGarden w} {J : Finset (Fin w)} (h : LG = LG') (hR : StemRet S X blk LG J) :
    StemRet S X blk LG' J :=
  h ▸ hR

/-- The old name of a `G_sb` branch lies in the same tree. -/
theorem shape_br_fst {w : ℕ} {S Gsb : Garden w} {ι : Type} {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb)
    (c : GBranch Gsb.tree) : (Φ.br c).1.1 = c.1.1 := by
  have h := Φ.tree_eq c.toNode
  rw [← Φ.br_node] at h
  exact h

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)

include hy hcapA hcapY in
/-- **T1 retention at every member of the run class.** -/
theorem stemRet_member (hc : CleanPt J a) :
    StemRet y.1.skeleton y.1.data.tree (fun j => unitClBlock (y.2 j))
      (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J := by
  have hR₁ := stemRet_congr (VineAlign.sourceLayer_reconstructs a).symm (stemRet_repMk hc (mk a.prime))
  exact stemRet_transport (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
    (memShape a mk y hy) (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
    (source_disjMk a mk y hy) (fun j i => congrFun (congrFun (memShape_hmom a mk y hy) j) i)
    a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) hcapA hcapY hR₁

include hcapA hcapY in
/-- **T1 at every member of the run class**: the classification `kindOf` of the member's reconstruction through its
shape `memShape a mk y hy` onto the representative's `G_sb`. -/
theorem kindMember_spec (hc : CleanPt J a) {z : GNode (y.1.data.forest y.1.plain)}
    (hz : OnStemAddr (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J z.1) :
    (∀ c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree,
      (kindOf y.1.data y.1.plain (memShape a mk y hy) z = StemKind.atom c) ↔
        (z = (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode ∧
          c ∉ (memShape a mk y hy).hinges (source_disjMk a mk y hy))) ∧
    (∀ j, (kindOf y.1.data y.1.plain (memShape a mk y hy) z = StemKind.top j) ↔
      z = (y.1.data.coreBranch y.1.plain (unitClBlock (y.2 j)).upper).toNode) ∧
    (∀ s : ReplacementSlot y.1.skeleton, (kindOf y.1.data y.1.plain (memShape a mk y hy) z = StemKind.slot s) ↔
      (MkSlots.slotOf y.1.data y.1.plain z = s ∧
        ∀ β : GBranch y.1.skeleton.tree, z ≠ (y.1.data.coreBranch y.1.plain β).toNode)) ∧
    SlotRet y.1.plain (blk := fun j => unitClBlock (y.2 j)) (MkSlots.slotOf y.1.data y.1.plain z) :=
  kindOf_spec y.1.data y.1.plain (memShape a mk y hy) (source_disjMk a mk y hy)
    (stemRet_member a mk y hy J hcapA hcapY hc) hz

variable (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hG hcapA hcapY hrepU in
/-- **The stem test at a `G_sb` atom is common to the run class.** -/
theorem stemB_member_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    StemB y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J
        (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) ((memShape a mk y hy).br c)) ↔
      StemB a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
        (coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) := by
  rw [stemB_core_iff, stemB_core_iff,
    onStem_core_iff (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) hcapY,
    onStem_core_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.data
      a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcapA]
  have hc := MkSlots.IntCore.member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c
  exact and_congr Iff.rfl (not_congr hc)

include hy hG hcapA hcapY hrepU in
/-- **The unit radius lists (T2) are common to the run class** (tree-indexed radii). -/
theorem SUStem_member_eq (radT : Fin (2 * R) → List ℝ)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    SUStem y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (fun b => radT b.1.1)
        (blk := fun j => unitClBlock (y.2 j)) j =
      SUStem a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (fun b => radT b.1.1)
        (blk := unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) j := by
  set Φ₁ := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set hd₁ := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set c := Φ₁.hinge hd₁ j
  have hh : (memShape a mk y hy).hinge (source_disjMk a mk y hy) j = c :=
    hinge_eq_of_hmom Φ₁ (memShape a mk y hy) hd₁ (source_disjMk a mk y hy)
      (fun j i => congrFun (congrFun (memShape_hmom a mk y hy) j) i) j
  have hu₂ : (unitClBlock (y.2 j)).upper = (memShape a mk y hy).br c := by
    rw [← hh, (memShape a mk y hy).br_hinge]
  have hu₁ : (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper = Φ₁.br c :=
    (Φ₁.br_hinge hd₁ j).symm
  have hs := stemB_member_iff a mk y hy J hcapA hcapY hG hrepU c
  have ht₁ : (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
      ((memShape a mk y hy).br c)).1.1 = c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst y.1.data y.1.plain _).trans (shape_br_fst (memShape a mk y hy) c)
  have ht₂ : (coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (Φ₁.br c)).1.1 =
      c.1.1 :=
    (MkSlots.IntRest.coreBranch_fst a.prime.data a.prime.prime.1 _).trans (shape_br_fst Φ₁ c)
  unfold SUStem
  rw [hu₂, hu₁]
  by_cases h1 : StemB y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J
      (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) ((memShape a mk y hy).br c))
  · rw [if_pos h1, if_pos (hs.mp h1)]
    simp only [ht₁, ht₂]
  · rw [if_neg h1, if_neg (fun h => h1 (hs.mpr h))]

end Class

end WaveTurbulence.Flower.MkSlotsT
