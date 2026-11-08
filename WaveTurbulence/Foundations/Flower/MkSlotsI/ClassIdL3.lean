/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassIdL2
public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassForm

/-! # B3s-HELPER7 ClassId (lower bounds, part 3): the lower bounds of a member are the piece's `lbGenAt`

For a member `y` of the run class of `a` at the marking `mk` (shapes `Φ_y = memShape a mk y hy`,
`Φ_a = stShape … (mk a.prime)` onto `G_sb`), with the capped geometry of both reconstructions and the
representative's pattern `hU` (`hrepUP`):

* **`rep_lbS_br`**: `lbS_a (Φ_a.br c) = lbGenAt J pat t s a (mk a.prime) c` — a pinned child of the free core of
  `Φ_a.br c` that is the core of no `G_sb` atom is a pinned native couple root at a leaf child (`pinChild_iff`; the
  cores of non-retained branches are unit-atom cores, unpinned by `hrepUP`), and the `dParent` clause is
  β's `lbS_dParent`;
* **`member_lbS_br_rep`**: `lbS_y (Φ_y.br c) = lbS_a (Φ_a.br c)` — the free cores are common (β's
  `member_fixCap_pat`), and a pinned leaf child transfers (`leafPinBelow_transfer`: the clock of the image of a `G_sb`
  leaf is common by the common routes `memShape_route`, its leaf pin by `member_leafPin_iff`);
* **`member_lbS_br`** (the requested statement): `lbS_y (Φ_y.br c) = lbGenAt … c`;
* **`member_lbS_lower`**: the lower bounds at the unit lowers are common; **`member_lbS_clk`**: the lower bounds at
  the clock branches of the outer slots are common (route split: `Φ.br c'` or a unit lower). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsI

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hrepUP in
/-- The cores of the skeleton branches of `a` outside the image of `Φ_a` (unit atoms) are unpinned. -/
theorem rep_core_none_of_not_br (b' : GBranch a.prime.skeleton.tree)
    (hb : ∀ c', (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c' ≠ b') :
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b') = none := by
  rcases ret_or_interior (blk := unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      b'.toNode with h | ⟨j, hj, -⟩
  · obtain ⟨c', hc'⟩ := (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).exists_br h
    exact absurd hc' (hb c')
  · exact hrepUP j b' ((branch_real_iff _ _).mp hj)

/-- The piece pin `fixAt` is the representative's core pin. -/
theorem fixAt_eq_fixCore (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    fixAt J pat t s a (mk a.prime) c =
      MkSlots.fixCore a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) :=
  MkSlotsB.fixCap_decoded_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes J pat t s _

include hGeoA hrepUP in
/-- **The representative's lower bounds at the old names of the `G_sb` atoms are the piece's `lbGenAt`.** -/
theorem rep_lbS_br (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) =
      lbGenAt J pat t s a (mk a.prime) c := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hfix := fixAt_eq_fixCore a mk J pat t s c
  have hpin : (∃ u, PinTopBelowAt J pat t s a (mk a.prime) c u) ↔
      ∃ u : GBranch (a.prime.data.forest a.prime.prime.1),
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s u).isSome ∧
        u.IsChildOf (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) ∧
        ∀ c', a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c') ≠ u :=
    pinChild_decoded a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J pat t s a.layered
      (sourceLayer_reconstructs a) a.prime.decodes
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br _
  have hch := fun hfree => pinChild_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
    hcapA pat t s (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br
    (rep_core_none_of_not_br a mk J pat t s hrepUP)
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) hfree
  rw [lbS_eq_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA pat t s]
  unfold lbGenAt
  by_cases h : MkSlots.fixCore a.prime.data a.prime.prime.1
      (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
        t s) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) = none ∧
      LeafPinBelow a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J
          pat t s) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)
  · rw [ite_eq_left h, ite_eq_left]
    refine ⟨?_, hfix.trans h.1, hpin.mpr ((hch h.1).mpr h.2)⟩
    have hs : (MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).isSome := by
      rw [lbS_eq_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA pat t s,
        ite_eq_left h]
      rfl
    have hd := MkSlotsB.lbS_dParent a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA
      pat t s _ hs
    rwa [IntCore.br_fst] at hd
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨-, h1, h2⟩
    have hfree := hfix.symm.trans h1
    exact h ⟨hfree, (hch hfree).mp (hpin.mp h2)⟩

include hy hG hGeoA hGeoY hrepUP in
/-- **The lower bounds of a member at the old names of the `G_sb` atoms are the representative's.** -/
theorem member_lbS_br_rep (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
        ((memShape a mk y hy).br c) =
      MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hfc : MkSlots.fixCore y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
      ((memShape a mk y hy).br c) =
      MkSlots.fixCore a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c) :=
    (MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c).trans (fixAt_eq_fixCore a mk J pat t s c)
  have hroute := memShape_route a mk y hy hG
  rw [lbS_eq_leaf y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY pat t s,
    lbS_eq_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA pat t s]
  refine if_congr ⟨fun h => ⟨hfc.symm.trans h.1, ?_⟩, fun h => ⟨hfc.trans h.1, ?_⟩⟩ rfl rfl
  · exact leafPinBelow_transfer (memShape a mk y hy)
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) y.1.plain a.prime.prime.1 hcapY
      _ _ _ h.1 (fun m hm => clk_br_transfer _ _ y.1.plain a.prime.prime.1 hG hroute m c hm)
      (fun m hm => (member_leafPin_iff a mk y hy hG J hGeoA hGeoY pat t s hrepUP m).mp hm) h.2
  · exact leafPinBelow_transfer (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      (memShape a mk y hy) a.prime.prime.1 y.1.plain hcapA
      _ _ _ h.1 (fun m hm => clk_br_transfer _ _ a.prime.prime.1 y.1.plain hG hroute.symm m c hm)
      (fun m hm => (member_leafPin_iff a mk y hy hG J hGeoA hGeoY pat t s hrepUP m).mpr hm) h.2

include hy hG hGeoA hGeoY hrepUP in
/-- **The lower bounds of a member at the `G_sb` atoms are the piece's `lbGenAt`.** -/
theorem member_lbS_br (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
        ((memShape a mk y hy).br c) =
      lbGenAt J pat t s a (mk a.prime) c :=
  (member_lbS_br_rep a mk y hy hG J hGeoA hGeoY pat t s hrepUP c).trans (rep_lbS_br a mk J hGeoA pat t s hrepUP c)

include hy hG hGeoA hGeoY hrepUP in
/-- **The lower bounds at the unit lowers are common to the run class.** -/
theorem member_lbS_lower (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
        (unitClBlock (y.2 j)).lower =
      MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hfy : MkSlots.fixCore y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
      (unitClBlock (y.2 j)).lower = none :=
    MkSlotsB.member_fix_unit_pat a mk y hy hG J hcapA hcapY pat t s hrepUP j _ (lower_mem _)
  have hfa : MkSlots.fixCore a.prime.data a.prime.prime.1
      (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
        t s) (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower = none :=
    hrepUP j _ (lower_mem _)
  have hroute := memShape_route a mk y hy hG
  have hdy := source_disjMk a mk y hy
  have hda := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  rw [lbS_eq_leaf y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY pat t s,
    lbS_eq_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA pat t s]
  refine if_congr ⟨fun h => ⟨hfa, ?_⟩, fun h => ⟨hfy, ?_⟩⟩ rfl rfl
  · exact leafPinBelow_transfer (memShape a mk y hy)
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) y.1.plain a.prime.prime.1 hcapY
      _ _ _ hfy (fun m hm => clk_lower_transfer _ _ y.1.plain a.prime.prime.1 hG hdy hda hroute m j hm)
      (fun m hm => (member_leafPin_iff a mk y hy hG J hGeoA hGeoY pat t s hrepUP m).mp hm) h.2
  · exact leafPinBelow_transfer (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      (memShape a mk y hy) a.prime.prime.1 y.1.plain hcapA
      _ _ _ hfa (fun m hm => clk_lower_transfer _ _ a.prime.prime.1 y.1.plain hG hda hdy hroute.symm m j hm)
      (fun m hm => (member_leafPin_iff a mk y hy hG J hGeoA hGeoY pat t s hrepUP m).mpr hm) h.2

include hy hG hGeoA hGeoY hrepUP in
/-- **The lower bounds at the clock branches of the outer slots are common to the run class.** -/
theorem member_lbS_clk (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2)
    (by' : GBranch y.1.skeleton.tree) (ba : GBranch a.prime.skeleton.tree)
    (hby : argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inr by')
    (hba : argSrc a.prime.prime.1
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i =
        .inr ba) :
    MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
        by' =
      MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s ba := by
  have hroute := memShape_route a mk y hy hG
  rcases (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_natural a.prime.prime.1
      hG s' i with hr | ⟨j, hj⟩
  · have hr' : (memShape a mk y hy).route y.1.plain hG s' i = .inl (argSrc hG s' i) := by
      rw [hroute]; exact hr
    rw [SpliceShape.route_inl _ _ _ hr] at hba
    rw [SpliceShape.route_inl _ _ _ hr'] at hby
    rcases hx : argSrc hG s' i with r | c'
    · rw [hx] at hba
      exact absurd hba (by simp [SpliceShape.srcMap])
    · rw [hx] at hba hby
      obtain rfl : (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c' = ba :=
        Sum.inr_injective hba
      obtain rfl : (memShape a mk y hy).br c' = by' := Sum.inr_injective hby
      exact member_lbS_br_rep a mk y hy hG J hGeoA hGeoY pat t s hrepUP c'
  · have hj' : (memShape a mk y hy).route y.1.plain hG s' i = .inr j := by
      rw [hroute]; exact hj
    rw [SpliceShape.route_inr _ _ _ hj] at hba
    rw [SpliceShape.route_inr _ _ _ hj'] at hby
    obtain rfl := Sum.inr_injective hba
    obtain rfl := Sum.inr_injective hby
    exact member_lbS_lower a mk y hy hG J hGeoA hGeoY pat t s hrepUP j

end Class

end WaveTurbulence.Flower.MkSlotsI
