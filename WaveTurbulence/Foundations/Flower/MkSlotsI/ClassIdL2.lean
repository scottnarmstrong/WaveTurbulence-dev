/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassIdL1
public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotCplM

/-! # B3s-HELPER7 ClassId (lower bounds, part 2): transporting pinned leaf children through two splice shapes

* `argSrc_leaf`: the clock source of side `sideOf m` of the image of the pair of a `G_sb` leaf `m` is the clock of the
  image of `m`;
* **`argSrc_br_iff`**, **`argSrc_lower_iff`**: for two shapes `Φ, Ψ` of the same `G_sb` with the same routes, a clock
  source `.inr (Φ.br c)` (resp. a lower joint `.inr (blk j).lower`) of an image slot is one for `Ψ`;
  `clk_br_transfer`, `clk_lower_transfer`: the same for the clock of the image of a `G_sb` leaf;
* **`leafPinBelow_transfer`**: a pinned leaf child of a free clock `B` of `Φ` transfers to `B'` of `Ψ`, given the
  clock and leaf-pin transfers (the pinned leaf is retained, `leafPin_ret`, hence the image of a `G_sb` leaf);
* the run class: **`member_cplPin`** (the pins of the native couple branches of an outer couple slot are common, the
  "pins" step of `member_genSlot_inl`) and **`member_leafPin_iff`** (`LeafPin` at the images of a `G_sb` leaf). -/

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
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore WaveTurbulence.Flower.MkSlots.IntCapT

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## Two shapes with the same routes -/

section Shape
variable {w : ℕ} {S S' G : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju]
  {blk : Ju → CLBlock S} {blk' : Ju → CLBlock S'} (Φ : SpliceShape blk G) (Ψ : SpliceShape blk' G)
  (hS : S.IsPlain) (hS' : S'.IsPlain) (hG : G.IsPlain)

/-- The clock source of side `sideOf m` of the image of the pair of a `G_sb` leaf `m` is the clock of `Φ.leaf m`. -/
theorem argSrc_leaf (m : GLeaf G.tree) :
    argSrc hS (Φ.iota hS hG (.inl (pairOfLeaf G hG m))) (sideOf hG m) = clkOfNode S (Φ.leaf m).toNode := by
  unfold sideOf
  split_ifs with h
  · simp only [SpliceShape.iota, argSrc, ↓reduceIte]
    rw [Φ.iota_first hS hG, h]
  · simp only [SpliceShape.iota, argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
    rw [Φ.iota_second hS hG]
    rcases IntRest.pairOfLeaf_sides hG m with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact absurd e1 h
    · rw [e2]

/-- The leaf of side `sideOf m` of the pair of a leaf `m` is `m`. -/
theorem sel_sideOf (m : GLeaf G.tree) :
    (if sideOf hG m = 0 then (pairOfLeaf G hG m).firstLeaf hG else (pairOfLeaf G hG m).secondLeaf hG) = m := by
  unfold sideOf
  by_cases h1 : (pairOfLeaf G hG m).firstLeaf hG = m
  · simp [h1]
  · rcases IntRest.pairOfLeaf_sides hG m with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact absurd e1 h1
    · simp [h1, e2]

/-- A lower joint is never the old name of a `G_sb` branch. -/
theorem lower_ne_br (c : GBranch G.tree) (j : Ju) : (blk j).lower ≠ Φ.br c := by
  intro hl
  rcases (ret_branch_iff _).mp (Φ.ret_br c) j with h1 | h1
  · rw [← hl] at h1
    exact h1 (lower_mem _)
  · rw [← hl] at h1
    exact (blk j).isBlock.2.2.2.1 h1.symm

/-- **A clock source `.inr (Φ.br c)` of an image slot is common to two shapes with the same routes.** -/
theorem argSrc_br_of_route (hroute : Φ.route hS hG = Ψ.route hS' hG) (sl : ReplacementSlot G) (i : Fin 2)
    (c : GBranch G.tree) (h : argSrc hS (Φ.iota hS hG sl) i = .inr (Φ.br c)) :
    argSrc hS' (Ψ.iota hS' hG sl) i = .inr (Ψ.br c) := by
  rcases Φ.route_natural hS hG sl i with hr | ⟨j, hj⟩
  · have hr' : Ψ.route hS' hG sl i = .inl (argSrc hG sl i) := by rw [← hroute]; exact hr
    rw [Φ.route_inl hS hG hr] at h
    rw [Ψ.route_inl hS' hG hr']
    rcases hx : argSrc hG sl i with r | c''
    · rw [hx] at h
      exact absurd h (by simp [SpliceShape.srcMap])
    · rw [hx] at h
      have : c'' = c := Φ.br_inj (Sum.inr_injective h)
      subst this
      rfl
  · rw [Φ.route_inr hS hG hj] at h
    exact absurd (Sum.inr_injective h) (lower_ne_br Φ c j)

/-- **A lower-joint clock source of an image slot is common to two shapes with the same routes.** -/
theorem argSrc_lower_iff (hd : Disj blk) (hd' : Disj blk') (hroute : Φ.route hS hG = Ψ.route hS' hG)
    (sl : ReplacementSlot G) (i : Fin 2) (j : Ju) :
    argSrc hS (Φ.iota hS hG sl) i = .inr (blk j).lower ↔ argSrc hS' (Ψ.iota hS' hG sl) i = .inr (blk' j).lower := by
  rw [← route_inr_iff Φ hd hS hG, ← route_inr_iff Ψ hd' hS' hG, hroute]

theorem clk_br_transfer (hroute : Φ.route hS hG = Ψ.route hS' hG) (m : GLeaf G.tree) (c : GBranch G.tree)
    (h : clkOfNode S (Φ.leaf m).toNode = .inr (Φ.br c)) : clkOfNode S' (Ψ.leaf m).toNode = .inr (Ψ.br c) := by
  rw [← argSrc_leaf Φ hS hG m] at h
  rw [← argSrc_leaf Ψ hS' hG m]
  exact argSrc_br_of_route Φ Ψ hS hS' hG hroute _ _ c h

theorem clk_lower_transfer (hd : Disj blk) (hd' : Disj blk') (hroute : Φ.route hS hG = Ψ.route hS' hG)
    (m : GLeaf G.tree) (j : Ju) (h : clkOfNode S (Φ.leaf m).toNode = .inr (blk j).lower) :
    clkOfNode S' (Ψ.leaf m).toNode = .inr (blk' j).lower := by
  rw [← argSrc_leaf Φ hS hG m] at h
  rw [← argSrc_leaf Ψ hS' hG m]
  exact (argSrc_lower_iff Φ Ψ hS hS' hG hd hd' hroute _ _ j).mp h

/-- The clock of a child `B.child i`. -/
theorem clkOfNode_child (B : GBranch S.tree) (i : Fin 3) : clkOfNode S (B.child i) = .inr B := by
  rw [VineB.clkOfNode_nonroot _ (VineB.child_nonroot B i), VineB.parent_child]

/-- A node whose clock is `.inr B'` is a child of `B'`. -/
theorem child_of_clkOfNode (x : GNode S'.tree) (B' : GBranch S'.tree) (h : clkOfNode S' x = .inr B') :
    ∃ i : Fin 3, x = B'.child i := by
  have hn : x.1.2 ≠ [] := by
    intro h0
    rw [SpliceShape.clkOfNode_root _ h0] at h
    exact Sum.inl_ne_inr h
  rw [VineB.clkOfNode_nonroot _ hn] at h
  obtain ⟨i, hi⟩ := VineB.child_parent _ hn
  refine ⟨i, ?_⟩
  rw [← hi, Sum.inr_injective h]

variable {D : ReconstructionData S} {D' : ReconstructionData S'}
  {layer : GNode (D.forest hS) → ℕ} {hLayer : IsLayering (D.garden hS) layer}
  {J : Finset (Fin w)} (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) {pat : Fin w → FixPat} {t s : ℝ}

include hcap in
/-- **A pinned leaf child of a free clock transfers between two shapes**, given the transfer of the clock of the
images of the `G_sb` leaves and of their leaf pins. -/
theorem leafPinBelow_transfer (fix' : GBranch (D'.forest hS') → Option ℝ) (B : GBranch S.tree) (B' : GBranch S'.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none)
    (hclk : ∀ m : GLeaf G.tree, clkOfNode S (Φ.leaf m).toNode = .inr B → clkOfNode S' (Ψ.leaf m).toNode = .inr B')
    (hpin : ∀ m : GLeaf G.tree, LeafPin D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (Φ.leaf m) →
      LeafPin D' hS' fix' (Ψ.leaf m))
    (h : LeafPinBelow D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B) :
    LeafPinBelow D' hS' fix' B' := by
  obtain ⟨σ, i, hσ, hp⟩ := h
  obtain ⟨m, rfl⟩ := Φ.exists_leaf (leafPin_ret D hS layer hLayer J hcap pat t s blk B hfree σ i hσ hp)
  have hc : clkOfNode S (Φ.leaf m).toNode = .inr B := by rw [hσ]; exact clkOfNode_child B i
  obtain ⟨i', hi'⟩ := child_of_clkOfNode _ B' (hclk m hc)
  exact ⟨Ψ.leaf m, i', hi', hpin m hp⟩

end Shape

/-! ## The run class: the leaf pins are common -/

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

include hy hG hGeoA hGeoY hrepUP in
/-- **The pins of the native couple branches of an outer couple slot are common to the run class** (the "pins" step
of `member_genSlot_inl`). -/
theorem member_cplPin (q : SourcePair (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (x : Fin 2 × Path)
    (h₁ : x.2 ∈ ((nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
      (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG)))).garden.tree x.1).branching)
    (h₂ : x.2 ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (pairOfLeaf a.prime.skeleton a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG)))).garden.tree
          x.1).branching) :
    fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s
        (capT_bemb (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
          (nativeCoupleForest y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG))))
          (nativeCoupleForest_closed y.1.data y.1.plain
            (pairOfLeaf y.1.skeleton y.1.plain ((memShape a mk y hy).leaf (q.firstLeaf hG)))) ⟨x, h₁⟩) =
      fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
        (capT_bemb (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
          (nativeCoupleForest a.prime.data a.prime.prime.1 (pairOfLeaf a.prime.skeleton a.prime.prime.1
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG))))
          (nativeCoupleForest_closed a.prime.data a.prime.prime.1 (pairOfLeaf a.prime.skeleton a.prime.prime.1
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf (q.firstLeaf hG))))
          ⟨x, h₂⟩) := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set qy := pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)) with hqy
  set qa := pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)) with hqa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  set LGa := layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    with hLGa
  have hN : nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) qy =
      nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) qa :=
    memShape_nativeCouple a mk y hy hG q
  have hroot : ∀ c, ((nativeCoupleForest y.1.data y.1.plain qy).root c =
      attachedNode y.1.data y.1.plain (Φy.node (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).toNode)) ∧
      ((nativeCoupleForest a.prime.data a.prime.prime.1 qa).root c =
        attachedNode a.prime.data a.prime.prime.1
          (Φa.node (if c = 0 then q.firstLeaf hG else q.secondLeaf hG).toNode)) :=
    fun c => ⟨cpl_root_attached Φy y.1.data y.1.plain hG q c, cpl_root_attached Φa a.prime.data a.prime.prime.1 hG q c⟩
  have hri : cplRI y.1.data y.1.plain qy = cplRI a.prime.data a.prime.prime.1 qa := by
    funext c
    unfold cplRI
    rw [(hroot c).1, (hroot c).2, attached_tree, attached_tree]
  have hrr : ∀ c, cplRR y.1.data y.1.plain qy c ↔ cplRR a.prime.data a.prime.prime.1 qa c := by
    intro c
    unfold cplRR
    rw [(hroot c).1, (hroot c).2, attached_root_iff, attached_root_iff]
  have hrc : cplRC y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J qy =
      cplRC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J qa := by
    funext c
    unfold cplRC
    rw [(hroot c).1, (hroot c).2]
    exact member_rcOf a mk y hy hG J hcapA hcapY hrepU _
  refine MkSlotsB.fixCap_congr J pat t s _ _ ?_ ?_ ?_ ?_ ?_
  · show cplRI y.1.data y.1.plain qy x.1 = cplRI a.prime.data a.prime.prime.1 qa x.1
    rw [hri]
  · exact (capT_cfp_iff LGy _ _ J _ (fun _ => rfl) ⟨x, h₁⟩).trans
      ((branch_fun_congr2 (fun N r b => capT_IsFP N r J b) hN hri x h₁ h₂).to_iff.trans
        (capT_cfp_iff LGa _ _ J _ (fun _ => rfl) ⟨x, h₂⟩).symm)
  · exact (root_bemb_iff LGy _ _ ⟨x, h₁⟩).trans
      ((and_congr Iff.rfl (hrr x.1)).trans (root_bemb_iff LGa _ _ ⟨x, h₂⟩).symm)
  · exact (par_bemb_iff LGy _ _ J ⟨x, h₁⟩).trans
      ((branch_fun_congr2 (fun N r b => ∃ c : GBranch N.garden.tree, capT_IsFP N r J c ∧ c.IsChildOf b) hN hri
        x h₁ h₂).to_iff.trans (par_bemb_iff LGa _ _ J ⟨x, h₂⟩).symm)
  · intro i
    refine (ch_bemb_iff LGy _ _ J ⟨x, h₁⟩ i).trans (Iff.trans ?_ (ch_bemb_iff LGa _ _ J ⟨x, h₂⟩ i).symm)
    refine or_congr (branch_fun_congr2 (fun N r b => ∃ c : GBranch N.garden.tree,
        capT_IsFP N r J c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i]) hN hri x h₁ h₂).to_iff (and_congr Iff.rfl ?_)
    have e := congrFun hrc x.1
    unfold cplRC at e
    rw [e]

include hy hG hGeoA hGeoY hrepUP in
/-- **The leaf pins at the images of a `G_sb` leaf are common to the run class.** -/
theorem member_leafPin_iff (m : GLeaf (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    LeafPin y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).leaf m) ↔
      LeafPin a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf m) := by
  have hry : (nativeCoupleForest y.1.data y.1.plain (pairOfLeaf y.1.skeleton y.1.plain
      ((memShape a mk y hy).leaf ((pairOfLeaf _ hG m).firstLeaf hG)))).root (sideOf hG m) =
        attachedNode y.1.data y.1.plain ((memShape a mk y hy).leaf m).toNode := by
    rw [cpl_root_attached (memShape a mk y hy) y.1.data y.1.plain hG _ _, sel_sideOf hG m,
      (memShape a mk y hy).leaf_node]
  have hra : (nativeCoupleForest a.prime.data a.prime.prime.1 (pairOfLeaf a.prime.skeleton a.prime.prime.1
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf
        ((pairOfLeaf _ hG m).firstLeaf hG)))).root (sideOf hG m) =
        attachedNode a.prime.data a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf m).toNode := by
    rw [cpl_root_attached (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))
      a.prime.data a.prime.prime.1 hG _ _, sel_sideOf hG m,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf_node]
  refine (leafPin_iff_cpl _ _ _ _ _ (sideOf hG m) hry).trans
    (Iff.trans ?_ (leafPin_iff_cpl _ _ _ _ _ (sideOf hG m) hra).symm)
  set q := pairOfLeaf _ hG m with hq
  set k : Fin 2 := sideOf hG m with hk
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  have hN := memShape_nativeCouple a mk y hy hG q
  have hbr : ∀ x : Fin 2 × Path,
      x.2 ∈ ((nativeCoupleLayered y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        (pairOfLeaf y.1.skeleton y.1.plain (Φy.leaf (q.firstLeaf hG)))).garden.tree x.1).branching ↔
      x.2 ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))).garden.tree x.1).branching := by
    intro x
    rw [hN]
  constructor
  · rintro ⟨h₁, hpin⟩
    have h₂ := (hbr (k, [])).mp h₁
    refine ⟨h₂, ?_⟩
    have e := member_cplPin a mk y hy hG J hGeoA hGeoY pat t s hrepUP q (k, []) h₁ h₂
    exact (congrArg Option.isSome e).symm.trans hpin
  · rintro ⟨h₂, hpin⟩
    have h₁ := (hbr (k, [])).mpr h₂
    refine ⟨h₁, ?_⟩
    have e := member_cplPin a mk y hy hG J hGeoA hGeoY pat t s hrepUP q (k, []) h₁ h₂
    exact (congrArg Option.isSome e).trans hpin

end Class

end WaveTurbulence.Flower.MkSlotsI
