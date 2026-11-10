/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoClass
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoU

/-! # B3s-HELPER3 B4 (pattern R-core 4): the pattern pins of a member

**`member_fixCap_pat`**, **`member_fix_unit_pat`** (see `PatGeoClass` for the plan). Hypotheses: B3s's `hG`,
`hcapA`, `hcapY` and the representative's `hrepUP` (no unit atom of `a` pinned, `PatGeoU.hU_rep_pat_recon`). -/

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
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

theorem core_fst {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.coreBranch hS b).1.1 = b.1.1 :=
  inflatedPosition_index S D.tree b.toNode

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hrepUP in
/-- The representative's pattern `hU` implies B3s's `hrepU`. -/
theorem hrepU_of_pat : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b) :=
  fun j b hb => (preds_of_fixCap_none (hrepUP j b hb)).1

include hG hcapA hcapY hrepUP in
/-- **The top attached at the image of a `G_sb` node is a capped flower parent for a member iff for the
representative.** -/
theorem attCfp_member_iff (z : GNode (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    (∃ C : GBranch (y.1.data.forest y.1.plain),
        C.toNode = attachedNode y.1.data y.1.plain ((memShape a mk y hy).node z) ∧
        IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J C) ↔
      ∃ C : GBranch (a.prime.data.forest a.prime.prime.1),
        C.toNode = attachedNode a.prime.data a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).node z) ∧
        IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a)) J C := by
  rcases VineB.SpliceShape.node_cases z with ⟨c', rfl⟩ | ⟨ℓ, rfl⟩
  · rw [← (memShape a mk y hy).br_node,
      ← (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br_node,
      cfp_attached_branch_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY,
      cfp_attached_branch_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA,
      memShape_lonePath_nil_iff a mk y hy hG c',
      member_cfp_iff a mk y hy hG J hcapA hcapY (hrepU_of_pat a mk J pat t s hrepUP) c']
  · rw [← (memShape a mk y hy).leaf_node,
      ← (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf_node,
      cfp_attached_leaf_iff (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        J hG ℓ,
      cfp_attached_leaf_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
        a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hG ℓ]
    have hN := memShape_nativeCouple a mk y hy hG (pairOfLeaf _ hG ℓ)
    have hg := congrArg LayeredGarden.garden hN
    rw [nativeCoupleLayered_garden, nativeCoupleLayered_garden] at hg
    rw [hg]

include hG in
/-- Root: common at every `G_sb` atom. -/
theorem member_root_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).1.2 = [] ↔
      (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).1.2 = [] := by
  rw [core_root_iff, core_root_iff, br_root_iff, br_root_iff, memShape_lonePath_nil_iff a mk y hy hG c]

include hG hcapA hcapY hrepUP in
/-- `dParent`: common at every non-hinge `G_sb` atom. -/
theorem member_par_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hnh : ∀ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c ≠
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper) :
    (∃ C, IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J C ∧
        C.IsChildOf (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c))) ↔
      ∃ C, IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a)) J C ∧
        C.IsChildOf (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) := by
  have hnhy : ∀ j, (memShape a mk y hy).br c ≠ (unitClBlock (y.2 j)).upper := fun j h => by
    obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy c).mp ⟨j, h⟩
    exact hnh j' hj'
  rw [hasCfpChild_core_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J,
    hasCfpChild_core_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J]
  refine exists_congr fun i => ?_
  rw [← (memShape a mk y hy).child c i hnhy,
    ← (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).child c i hnh]
  exact attCfp_member_iff a mk y hy hG J hcapA hcapY pat t s hrepUP (c.child i)

include hG hcapA hcapY hrepUP in
/-- `dChild i`: common at every `G_sb` atom. -/
theorem member_ch_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) (i : Fin 3) :
    (∃ C, IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J C ∧
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).1.1 = C.1.1 ∧
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).1.2 = C.1.2 ++ [i]) ↔
      ∃ C, IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a)) J C ∧
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).1.1 = C.1.1 ∧
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).1.2 =
          C.1.2 ++ [i] := by
  have hU := hrepU_of_pat a mk J pat t s hrepUP
  rw [childOfCfp_core_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY,
    childOfCfp_core_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA,
    memShape_lonePath_nil_iff a mk y hy hG c]
  refine and_congr_right fun _ => ?_
  by_cases hc : c.1.2 = []
  · constructor
    · rintro ⟨hb, -⟩
      exact absurd ((br_root_iff _ c).mpr hc) hb
    · rintro ⟨hb, -⟩
      exact absurd ((br_root_iff _ c).mpr hc) hb
  · obtain ⟨hby, hy1, hy2⟩ := br_parent_cases (memShape a mk y hy) c hc
    obtain ⟨hba, ha1, ha2⟩ :=
      br_parent_cases (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) c hc
    by_cases h0 : ∃ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br
        (c.toNode.parent hc) = (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper
    · obtain ⟨j, hj⟩ := h0
      obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy _).mpr ⟨j, hj⟩
      constructor
      · rintro ⟨hb, -, hcf⟩
        exact (member_unit_not_cfp a mk y hy hG J hcapA hcapY hU j' _ (hy2 j' hj') hcf).elim
      · rintro ⟨hb, -, hcf⟩
        exact (hU j _ (ha2 j hj) hcf).elim
    · have h0a : ∀ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br
          (c.toNode.parent hc) ≠ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper :=
        fun j e => h0 ⟨j, e⟩
      have h0y : ∀ j, (memShape a mk y hy).br (c.toNode.parent hc) ≠ (unitClBlock (y.2 j)).upper := fun j e =>
        h0 ((member_hinge_iff a mk y hy _).mp ⟨j, e⟩)
      obtain ⟨py, ly⟩ := hy1 h0y
      obtain ⟨pa, la⟩ := ha1 h0a
      constructor
      · rintro ⟨hb, hl, hcf⟩
        refine ⟨hba, la.trans (ly.symm.trans hl), ?_⟩
        rw [pa]
        refine (member_cfp_iff a mk y hy hG J hcapA hcapY hU _).mp ?_
        rw [← py]
        exact hcf
      · rintro ⟨hb, hl, hcf⟩
        refine ⟨hby, ly.trans (la.symm.trans hl), ?_⟩
        rw [py]
        refine (member_cfp_iff a mk y hy hG J hcapA hcapY hU _).mpr ?_
        rw [← pa]
        exact hcf

include hy hG hcapA hcapY hrepUP in
/-- **No core of an atom of a unit of a member is pinned, for every pattern.** -/
theorem member_fix_unit_pat (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
    (b : GBranch y.1.skeleton.tree) (hb : b ∈ (unitClBlock (y.2 j)).atoms) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s
      (y.1.data.coreBranch y.1.plain b) = none := by
  have hU := hrepU_of_pat a mk J pat t s hrepUP
  have hdy := source_disjMk a mk y hy
  refine fixCap_none_of J pat t s _ (member_unit_not_cfp a mk y hy hG J hcapA hcapY hU j b hb) ?_ ?_ ?_
  · -- `dRoot`
    intro hp hr
    obtain ⟨hbr, hbl⟩ := (core_root_iff y.1.data y.1.plain b).mp hr
    have hbu : b = (unitClBlock (y.2 j)).upper := by
      by_contra hne
      obtain ⟨hn, -⟩ := real_parent (unitClBlock (y.2 j)) ((branch_mem_clRealizationNodes b).mpr hb)
        (fun h => hne (Mole.branch_toNode_injective h))
      exact hn hbr
    obtain ⟨h, rfl⟩ : ∃ h, b = (memShape a mk y hy).br h :=
      ⟨_, hbu.trans ((memShape a mk y hy).br_hinge hdy j).symm⟩
    have hroot : h.1.2 = [] := (br_root_iff _ h).mp hbr
    have hla := (memShape_lonePath_nil_iff a mk y hy hG h).mp hbl
    have hra : (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br h)).1.2 = [] :=
      (core_root_iff a.prime.data a.prime.prime.1 _).mpr ⟨(br_root_iff _ h).mpr hroot, hla⟩
    obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy h).mp ⟨j, hbu⟩
    have hpre := preds_of_fixCap_none (hrepUP j' _ (hj' ▸ upper_mem _))
    refine hpre.2.1 ?_ hra
    rw [core_fst, br_fst, ← br_fst (memShape a mk y hy) h, ← core_fst y.1.data y.1.plain]
    exact hp
  · -- `dParent`
    intro hp hpar
    obtain ⟨i, C, hC, hcf⟩ :=
      (hasCfpChild_core_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J b).mp hpar
    by_cases hr : b.child i ∈ clRealizationNodes y.1.skeleton (unitClBlock (y.2 j)).atoms
    · rcases (Comb.TreePath.mem_nodes_iff _ _).mp (b.child i).2 with hl | hbr
      · let σ : GLeaf y.1.skeleton.tree := ⟨(b.child i).1, hl⟩
        have hσ : σ.toNode = b.child i := rfl
        have hint := (leaf_mem_clRealizationNodes σ).mp (hσ ▸ hr)
        obtain ⟨-, -, hp2, -⟩ := hint
        have hC' : C.toNode = (nativeCoupleForest y.1.data y.1.plain (pairOfLeaf _ y.1.plain σ)).root
            (sideOf y.1.plain σ) := hC.trans (root_sideOf _ _ σ).symm
        obtain ⟨hni, ℓ', -, -, hpJ⟩ :=
          (cfp_nativeRoot_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J _ _ C hC').mp hcf
        rcases nativeRoot_cases y.1.data y.1.plain σ
            ((decodedCouple (y.1.data.couple (pairOfLeaf _ y.1.plain σ))).pair ℓ').1.1 with he | he
        · apply hni
          show ((nativeCoupleForest y.1.data y.1.plain (pairOfLeaf _ y.1.plain σ)).root (sideOf y.1.plain σ)).1.1 ∈ J
          rw [root_sideOf]
          rw [he] at hpJ
          exact hpJ
        · rw [he] at hpJ
          have hJ : (y.1.skeleton.pair σ).1.1 ∈ J := by
            have h3 := inflatedPosition_index y.1.skeleton y.1.data.tree (y.1.skeleton.pair σ).toNode
            exact h3 ▸ hpJ
          exact hp2 (skel_path_nil y.1.data y.1.plain (hcapY _ hJ) _ rfl)
      · let b'' : GBranch y.1.skeleton.tree := ⟨(b.child i).1, hbr⟩
        have hb'' : b'' ∈ (unitClBlock (y.2 j)).atoms := (branch_mem_clRealizationNodes b'').mp hr
        have h2 := (cfp_attached_branch_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY
          b'').mp ⟨C, hC, hcf⟩
        exact member_unit_not_cfp a mk y hy hG J hcapA hcapY hU j b'' hb'' h2.2
    · have hcr := ext_child_crown (unitClBlock (y.2 j)) hb i hr
      obtain ⟨k, hk⟩ := (memShape a mk y hy).crown_exists hdy j hcr
      obtain ⟨Ca, hCa, hcfa⟩ := (attCfp_member_iff a mk y hy hG J hcapA hcapY pat t s hrepUP
        (((memShape a mk y hy).hinge hdy j).child k)).mp ⟨C, by rw [hk]; exact hC, hcf⟩
      obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy ((memShape a mk y hy).hinge hdy j)).mp
        ⟨j, (memShape a mk y hy).br_hinge hdy j⟩
      have hcra := (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).crown _ j' hj' k
      obtain ⟨v, hv, i', hvi⟩ := crown_parent _ hcra
      have hpa := (hasCfpChild_core_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
        v).mpr ⟨i', Ca, by rw [hvi]; exact hCa, hcfa⟩
      have hpre := preds_of_fixCap_none (hrepUP j' v hv)
      refine hpre.2.2.1 ?_ hpa
      have e1 : (a.prime.data.coreBranch a.prime.prime.1 v).1.1 = ((memShape a mk y hy).hinge hdy j).1.1 := by
        rw [core_fst]
        have h3 := congrArg (fun x : GNode a.prime.skeleton.tree => x.1.1) hvi
        exact h3.trans ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).tree_eq _)
      have e2 : (y.1.data.coreBranch y.1.plain b).1.1 = ((memShape a mk y hy).hinge hdy j).1.1 := by
        rw [core_fst]
        have h3 := congrArg (fun x : GNode y.1.skeleton.tree => x.1.1) hk
        exact h3.symm.trans ((memShape a mk y hy).tree_eq _)
      rw [e1, ← e2]
      exact hp
  · -- `dChild i`
    intro i hp hch
    obtain ⟨hl0, hbn, hli, hcf⟩ :=
      (childOfCfp_core_iff y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY b i).mp hch
    by_cases hbu : b = (unitClBlock (y.2 j)).upper
    · obtain ⟨h, rfl⟩ : ∃ h, b = (memShape a mk y hy).br h :=
        ⟨_, hbu.trans ((memShape a mk y hy).br_hinge hdy j).symm⟩
      have hh : h.1.2 ≠ [] := fun h0 => hbn ((br_root_iff _ h).mpr h0)
      obtain ⟨hby, hy1, hy2⟩ := br_parent_cases (memShape a mk y hy) h hh
      by_cases h0 : ∃ j'', (memShape a mk y hy).br (h.toNode.parent hh) = (unitClBlock (y.2 j'')).upper
      · obtain ⟨j'', hj''⟩ := h0
        exact member_unit_not_cfp a mk y hy hG J hcapA hcapY hU j'' _ (hy2 j'' hj'') hcf
      · have h0y : ∀ j'', (memShape a mk y hy).br (h.toNode.parent hh) ≠ (unitClBlock (y.2 j'')).upper :=
          fun j'' e => h0 ⟨j'', e⟩
        obtain ⟨py, ly⟩ := hy1 h0y
        have h0a : ∀ j'', (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br
            (h.toNode.parent hh) ≠
              (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j'').upper :=
          fun j'' e => h0 ((member_hinge_iff a mk y hy _).mpr ⟨j'', e⟩)
        obtain ⟨hba, ha1, -⟩ :=
          br_parent_cases (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h hh
        obtain ⟨pa, la⟩ := ha1 h0a
        have hcfa := (member_cfp_iff a mk y hy hG J hcapA hcapY hU (h.toNode.parent hh)).mp
          (by rw [← py]; exact hcf)
        have hla := (memShape_lonePath_nil_iff a mk y hy hG h).mp hl0
        have hcha := (childOfCfp_core_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
          hcapA _ i).mpr ⟨hla, hba, la.trans (ly.symm.trans hli), by rw [pa]; exact hcfa⟩
        obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy h).mp ⟨j, hbu⟩
        have hpre := preds_of_fixCap_none (hrepUP j' _ (hj' ▸ upper_mem _))
        refine hpre.2.2.2 i ?_ hcha
        rw [core_fst, br_fst, ← br_fst (memShape a mk y hy) h, ← core_fst y.1.data y.1.plain]
        exact hp
    · obtain ⟨hn, hpar⟩ := real_parent (unitClBlock (y.2 j)) ((branch_mem_clRealizationNodes b).mpr hb)
        (fun e => hbu (Mole.branch_toNode_injective e))
      exact member_unit_not_cfp a mk y hy hG J hcapA hcapY hU j _ hpar hcf

include hG hcapA hcapY hrepUP in
/-- **The pattern pins of a member at the `G_sb` atoms are the pins of the piece** (`fixAt … pat`, every pattern). -/
theorem member_fixCap_pat (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)) =
      fixAt J pat t s a (mk a.prime) c := by
  have hU := hrepU_of_pat a mk J pat t s hrepUP
  have hfa : fixAt J pat t s a (mk a.prime) c =
      fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) :=
    fixCap_decoded_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes J pat t s _
  rw [hfa]
  by_cases hh : ∃ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c =
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper
  · obtain ⟨j, hj⟩ := hh
    obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy c).mpr ⟨j, hj⟩
    rw [hrepUP j _ (hj ▸ upper_mem _),
      member_fix_unit_pat a mk y hy hG J hcapA hcapY pat t s hrepUP j' _ (hj' ▸ upper_mem _)]
  · have hnh : ∀ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c ≠
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper :=
      fun j e => hh ⟨j, e⟩
    refine fixCap_congr J pat t s _ _ ?_ (member_cfp_iff a mk y hy hG J hcapA hcapY hU c)
      (member_root_iff a mk y hy hG c) (member_par_iff a mk y hy hG J hcapA hcapY pat t s hrepUP c hnh)
      (member_ch_iff a mk y hy hG J hcapA hcapY pat t s hrepUP c)
    rw [core_fst, core_fst, br_fst, br_fst]

include hy hG hcapA hcapY hrepUP in
/-- **`hU` of the member's pinned VINE-B♯** (`MkSlots.hasSum_skelValF_outerValMμ` on the member's skeleton, units
`unitClBlock (y.2 j)`, skeleton pins `fixCore` of the member's pattern pins), every pattern. -/
theorem hU_member_pat : ∀ j, ∀ x ∈ VineB.inter (fun j => unitClBlock (y.2 j)) j,
    fixCore y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) x =
      none :=
  fixU_of_atoms _ fun j x hx => member_fix_unit_pat a mk y hy hG J hcapA hcapY pat t s hrepUP j x hx

end Class

/-! ## The piece at an arbitrary marked set `Mk` (`fixAt`, B3s's `pieceAt` data) -/

section Piece
variable {w : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)
  (Mk : Set (Stage1.CLVine a.prime.skeleton))

end Piece

end WaveTurbulence.Flower.MkSlotsB
