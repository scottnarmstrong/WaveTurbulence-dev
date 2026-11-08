/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.CoreW3
public import WaveTurbulence.Foundations.Flower.MkSlots.IntPiece

/-! # B3s-HELPER7 WP7 (part 4): the selection constants are class-common; the core weight of a member

For a member `y` of the run class of the representative `a` (hypotheses of γ's `MemberRun` / δ's `SelClass`):

* **`selCap_isSome_member_iff`**: the selected vertex of tree `j` exists at the member iff it exists at the
  representative (the capped flower of tree `j` sits in the native couple of the same `Gsb` pair, the couples are
  common, `MkSlots.memShape_nativeCouple`, and so is the depth of its attachment address: `attach_depth` and δ's
  `stemCore_length_member`);
* **item 4**: `selOK_member` (`selOK` is common) and `selConst_member` (the selection constant
  `∏ j, (selCap … j).elim 1 (fun _ => Rs j⁻¹)` is common);
* **`zatom_member'`** (item 2 without `hex`) and **`genCoreW_member'`** (the core multiplier of a member is
  `selConst(a) · zatomG (resDec κ) · topW`, given `selOK(a) = 1` and the fine marking's unit tops, `rep_tops_not_sel`);
* `sibIndOf_eq_sibIndAt`: the general piece's dagger sibling indicator is α's `sibIndAt` at the class marking. -/

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
open WaveTurbulence.Flower.Stage1MKGate (CleanPt classMk)
open WaveTurbulence.Flower.MkSlots (recLG)

namespace WaveTurbulence.Flower.MkSlotsI

/-- The general piece's dagger sibling indicator is α's `sibIndAt` at the class marking. -/
theorem sibIndOf_eq_sibIndAt {w d : ℕ} (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)
    (dag : Option (Fin w → Fin 3 → Mom d)) :
    MkSlots.sibIndOf J mkF a dag (MkSlotsG.flwGen J mkF a) =
      MkSlots.sibIndAt J a (classMk mkF a) dag (MkSlots.flwAt J a (classMk mkF a)) := rfl

/-- The representative's unit tops are not selected vertices (from the fine marking). -/
theorem rep_tops_not_sel {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = classMk mkF a)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    a.prime.data.coreBranch a.prime.prime.1
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper ∉
        selSetCap (recLG a) J kSel :=
  rep_units_not_sel J pat t s kSel mkF hsub a mk hset j _ (upper_mem _)

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (hc : CleanPt J a)
  (honeA : MkSlotsS.OneFlower (recLG a) J)
  (honeY : MkSlotsS.OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)

include hy hcapA hcapY hG hc in
/-- The root depths of the flower sides of the native couples are common to the run class. -/
theorem cwDp_member (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (c : Fin 2)
    (hJ : (cwSide hG q c).1.1 ∉ J)
    (hJ' : ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair (cwSide hG q c)).1.1 ∈ J) :
    cwDp (memShape a mk y hy) y.1.data y.1.plain hG q c =
      cwDp (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.data
        a.prime.prime.1 hG q c := by
  have hRy := MkSlotsT.stemRet_member a mk y hy J hcapA hcapY hc
  have hRa := MkSlotsT.stemRet_congr (sourceLayer_reconstructs a).symm (MkSlotsT.stemRet_repMk hc (mk a.prime))
  rw [cwDp_eq, cwDp_eq]
  by_cases h : (cwSide hG q c).1.2 = []
  · rw [attach_depth_root _ _ _ h, attach_depth_root _ _ _ h]
  · obtain ⟨-, hy'⟩ := attach_depth (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1) hcapY hRy (cwSide hG q c) hJ hJ' h
    obtain ⟨hstA, ha'⟩ := attach_depth (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcapA hRa (cwSide hG q c) hJ hJ' h
    rw [hy', ha', MkSlotsS.stemCore_length_member a mk y hy J hcapA hcapY hG hc _ hstA]

include hy hcapA hcapY hG hc honeA honeY in
/-- **The selected vertex of a tree exists at a member iff it exists at the representative.** -/
theorem selCap_isSome_member_iff (kSel : Fin (2 * R) → Option ℕ) (j : Fin (2 * R)) :
    (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j).isSome ↔
      (selCap (recLG a) J kSel j).isSome := by
  rw [selCap_isSome_iff honeY, selCap_isSome_iff honeA]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [exists_capFlower_iff (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) hG
      hcapY j k,
    exists_capFlower_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.data
      a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hG hcapA j k]
  refine exists_congr fun q => flowerAtDepth_congr (MkSlots.memShape_nativeCouple a mk y hy hG q) ?_ ?_ j k
  · funext c
    rw [cwTr_eq, cwTr_eq]
  · intro l hl
    obtain ⟨h1, h2⟩ := hl
    rw [cwTr_eq] at h1 h2
    have hne : l.1.1 ≠ ((cwN (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        hG q).garden.pair l).1.1 := fun he => h1 (he ▸ h2)
    rw [cwSide_pair hG q _ _ hne] at h2
    exact cwDp_member a mk y hy J hcapA hcapY hG hc q l.1.1 h1 h2

include hy hcapA hcapY hG hc honeA honeY in
/-- **Item 4: `selOK` is common to the run class.** -/
theorem selOK_member (kSel : Fin (2 * R) → Option ℕ) :
    selOK (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel =
      selOK (recLG a) J kSel :=
  selOK_congr J kSel (selCap_isSome_member_iff a mk y hy J hcapA hcapY hG hc honeA honeY kSel)

include hy hcapA hcapY hG hc honeA honeY in
/-- **Item 4: the selection constant is common to the run class.** -/
theorem selConst_member (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) :
    (∏ j, (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel
        j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) =
      ∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ)) :=
  selConst_congr J kSel Rs (selCap_isSome_member_iff a mk y hy J hcapA hcapY hG hc honeA honeY kSel)

variable (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- **Item 2: the member transfer of the atom part** (no extra hypothesis). -/
theorem zatom_member' (L : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) {d : ℕ}
    {roots : Fin (2 * R) → (Fin d → ℤ)} (κ : GenDecoration y.1.skeleton d roots 0) :
    ∏ c ∈ univ.filter (fun c => c ∉ (memShape a mk y hy).hinges (source_disjMk a mk y hy)),
        genNW (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J L σ kSel Rs
          (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode
          (omegaNode y.1.skeleton (cosetDecoration y.1.skeleton L 0 κ.1) ((memShape a mk y hy).br c)) =
      zatomG J L σ kSel Rs a (mk a.prime) ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) :=
  zatom_member a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel L σ Rs
    (selCap_isSome_member_iff a mk y hy J hcapA hcapY hG hc honeA honeY kSel) κ

include hy hcapA hcapY hG hrepU hc honeA honeY in
/-- **The core multiplier of a run-class member** (`genCoreW`, base `0`): if every requested selected vertex of the
representative exists (`selOK = 1`, the non-zero case) and no representative unit top is a selected vertex
(`rep_tops_not_sel`), it is the representative's selection constant times the atom weight `zatomG` of `G_sb` at the
restricted decoration times B3-2's top weight with the unit radius lists `SURep a mk J (radTGen L σ kSel Rs)`. -/
theorem genCoreW_member' (L : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (hselA : selOK (recLG a) J kSel = 1)
    (hrepS : ∀ j, a.prime.data.coreBranch a.prime.prime.1
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper ∉
        selSetCap (recLG a) J kSel)
    {d : ℕ} {roots : Fin (2 * R) → (Fin d → ℤ)} (κ : GenDecoration y.1.skeleton d roots 0) :
    genCoreW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
        (source_disjMk a mk y hy) J L σ kSel Rs 0 κ =
      (∏ j, (selCap (recLG a) J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
        (zatomG J L σ kSel Rs a (mk a.prime) ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) *
          ∏ j, VineSpaceK.nodeWeight (V5W2L.topFilterWeightL (MkSlotsT.SURep a mk J (radTGen L σ kSel Rs) j)) L 0
            (y.2 j).blk.a κ.1) := by
  have hex := selCap_isSome_member_iff a mk y hy J hcapA hcapY hG hc honeA honeY kSel
  have hselY : selOK (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      kSel = 1 := (selOK_member a mk y hy J hcapA hcapY hG hc honeA honeY kSel).trans hselA
  exact genCoreW_member a mk y hy J hcapA hcapY hG hrepU hc honeA honeY kSel L σ Rs hex
    ((selOK_eq_one_iff _ J kSel).1 hselY) hrepS κ

end Class

end WaveTurbulence.Flower.MkSlotsI
