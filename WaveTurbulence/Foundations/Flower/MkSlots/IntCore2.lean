/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore
public import WaveTurbulence.Foundations.Flower.MkSlots.IntChain

/-! # B3s MK-SLOTS (integration, R-core 2): the capped flower parents at the core are common to the run class

Through a splice shape `Φ : SpliceShape blk G` (`G = G_sb`), `cfp_core_iff` reads:
* at a `G_sb` atom `c` that is not a hinge, the core of `Φ.br c` is a capped flower parent iff a child of `c` is a
  `G_sb` leaf `ℓ` paired with a cap root whose skeleton image `Φ.leaf ℓ` has a leaf as attached node
  (`cfp_br_iff`);
* the core of an atom of a unit can only be a capped flower parent through a leaf child of the hinge of that unit
  (`cfp_unit_atom`, via the crown), and conversely (`cfp_of_hinge_leaf`).
The last condition (`AttLeaf`) is the shape of the native couple of the pair (`attLeaf_iff`), the same for every
member of the run class by the native-couple chain `memShape_nativeCouple` (`attLeaf_member_iff`); hinges are common
(`memShape_hinges`). With the representative's fact that no unit atom carries a pin (`Geo.fixCap_coreBranch_unit`,
here the hypothesis `hrepU`), this gives for every member `y` of the run class:
* `member_unit_not_cfp`: no core of an atom of a unit of `y` is a capped flower parent;
* **`member_cfp_iff`**: at every `G_sb` atom, the core of `y` is a capped flower parent iff the core of the
  representative is;
* `member_cfp_br`: every skeleton branch of `y` whose core is a capped flower parent is a `G_sb` atom. -/

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

namespace WaveTurbulence.Flower.MkSlots.IntCore

open WaveTurbulence.Flower.MkSlots.IntRest

/-! ### Through a splice shape -/

section Shape
variable {w : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G) (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)

/-- The tree of the skeleton partner of the image of a `G_sb` leaf. -/
theorem shape_leaf_pair_idx (ℓ : GLeaf G.tree) : (S.pair (Φ.leaf ℓ)).1.1 = (G.pair ℓ).1.1 := by
  rw [← Φ.pair]
  have h := Φ.tree_eq (G.pair ℓ).toNode
  rw [← Φ.leaf_node] at h
  exact h

include hcap in
/-- No skeleton branch lies in a cap tree. -/
theorem branch_tree_not_mem (b : GBranch S.tree) : b.1.1 ∉ J :=
  fun h => IntGeo.no_branch_of_leafTree (hcap _ h) b rfl

include hcap in
/-- **At a `G_sb` atom that is not a hinge.** -/
theorem cfp_br_iff (c : GBranch G.tree) (hh : ∀ j, Φ.br c ≠ (blk j).upper) :
    IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (Φ.br c)) ↔
      ∃ (i : Fin 3) (ℓ : GLeaf G.tree), ℓ.toNode = c.child i ∧ (G.pair ℓ).1.1 ∈ J ∧ AttLeaf D hS (Φ.leaf ℓ) := by
  rw [cfp_core_iff D hS layer hLayer J hcap]
  constructor
  · rintro ⟨i, σ, hσ, -, hpJ, hatt⟩
    have hn : Φ.node (c.child i) = σ.toNode := (Φ.child c i hh).trans hσ.symm
    rcases SpliceShape.node_cases (c.child i) with ⟨c', hc'⟩ | ⟨ℓ, hℓ⟩
    · exfalso
      rw [← hc', ← Φ.br_node] at hn
      exact SpliceShape.leaf_ne_branch hn.symm
    · have hσℓ : Φ.leaf ℓ = σ := Mole.leaf_toNode_injective (by rw [Φ.leaf_node, hℓ, hn])
      refine ⟨i, ℓ, hℓ, ?_, hσℓ ▸ hatt⟩
      rw [← shape_leaf_pair_idx Φ ℓ, hσℓ]
      exact hpJ
  · rintro ⟨i, ℓ, hℓ, hpJ, hatt⟩
    have hn : (Φ.leaf ℓ).toNode = (Φ.br c).child i := by rw [Φ.leaf_node, hℓ]; exact Φ.child c i hh
    refine ⟨i, Φ.leaf ℓ, hn, ?_, by rw [shape_leaf_pair_idx]; exact hpJ, hatt⟩
    have h1 : (Φ.leaf ℓ).1.1 = (Φ.br c).1.1 := congrArg (fun x : GNode S.tree => x.1.1) hn
    rw [h1]
    exact branch_tree_not_mem D hS J hcap _

include hcap in
/-- **At an atom of a unit**: only through a leaf child of the hinge. -/
theorem cfp_unit_atom (hd : Disj blk) (j : Ju) (b : GBranch S.tree) (hb : b ∈ (blk j).atoms)
    (hcfp : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) :
    ∃ (k : Fin 3) (ℓ : GLeaf G.tree), ℓ.toNode = (Φ.hinge hd j).child k ∧ (G.pair ℓ).1.1 ∈ J ∧
      AttLeaf D hS (Φ.leaf ℓ) := by
  obtain ⟨i, σ, hσ, -, hpJ, hatt⟩ := (cfp_core_iff D hS layer hLayer J hcap b).mp hcfp
  have hpnil : (S.pair σ).1.2 = [] := skel_path_nil D hS (hcap _ hpJ) (S.pair σ) rfl
  have hnr : b.child i ∉ clRealizationNodes S (blk j).atoms := by
    rw [← hσ, leaf_mem_clRealizationNodes]
    rintro ⟨-, -, hp, -⟩
    exact hp hpnil
  have hcr := ext_child_crown (blk j) hb i hnr
  obtain ⟨k, hk⟩ := Φ.crown_exists hd j hcr
  rcases SpliceShape.node_cases ((Φ.hinge hd j).child k) with ⟨c', hc'⟩ | ⟨ℓ, hℓ⟩
  · exfalso
    rw [← hc', ← Φ.br_node, ← hσ] at hk
    exact SpliceShape.leaf_ne_branch hk.symm
  · have hσℓ : Φ.leaf ℓ = σ := Mole.leaf_toNode_injective (by rw [Φ.leaf_node, hℓ, hk, hσ])
    refine ⟨k, ℓ, hℓ, ?_, hσℓ ▸ hatt⟩
    rw [← shape_leaf_pair_idx Φ ℓ, hσℓ]
    exact hpJ

include hcap in
/-- Conversely, a leaf child of a hinge paired with a cap root and attached at a leaf makes the core of an atom of
the unit a capped flower parent. -/
theorem cfp_of_hinge_leaf (hd : Disj blk) (j : Ju) (k : Fin 3) (ℓ : GLeaf G.tree)
    (hℓ : ℓ.toNode = (Φ.hinge hd j).child k) (hpJ : (G.pair ℓ).1.1 ∈ J) (hatt : AttLeaf D hS (Φ.leaf ℓ)) :
    ∃ v ∈ (blk j).atoms, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS v) := by
  have hcr : (Φ.leaf ℓ).toNode ∈ crownSet (blk j) := by
    rw [Φ.leaf_node, hℓ]
    exact Φ.crown _ j (Φ.br_hinge hd j) k
  obtain ⟨v, hv, i, hvi⟩ := crown_parent (blk j) hcr
  refine ⟨v, hv, cfp_core_backward D hS layer hLayer J hcap v i (Φ.leaf ℓ) hvi.symm ?_ ?_ hatt⟩
  · have h1 : (Φ.leaf ℓ).1.1 = v.1.1 := congrArg (fun x : GNode S.tree => x.1.1) hvi.symm
    rw [h1]
    exact branch_tree_not_mem D hS J hcap v
  · rw [shape_leaf_pair_idx]
    exact hpJ

/-- The skeleton pair of the image of a `G_sb` leaf is that of the image of the first leaf of its `G_sb` pair. -/
theorem pairOfLeaf_shape_leaf (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    pairOfLeaf S hS (Φ.leaf ℓ) = pairOfLeaf S hS (Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG)) := by
  rcases pairOfLeaf_sides hG ℓ with ⟨e1, -⟩ | ⟨e1, -⟩
  · rw [e1]
  · rw [e1, Φ.pair, pairOfLeaf_partner]

/-- The side of the image of a `G_sb` leaf. -/
theorem sideOf_shape_leaf (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    sideOf hS (Φ.leaf ℓ) = if (pairOfLeaf G hG ℓ).firstLeaf hG = ℓ then 0 else 1 := by
  unfold sideOf
  rw [pairOfLeaf_shape_leaf Φ hS hG ℓ]
  have h1 := Φ.iota_first hS hG (pairOfLeaf G hG ℓ)
  rw [h1]
  split_ifs with h2 h3 h3
  · rfl
  · exact absurd (Φ.leaf_inj h2) h3
  · exact absurd (by rw [h3]) h2
  · rfl

/-- `AttLeaf` of the image of a `G_sb` leaf, read on the native couple of the image of its `G_sb` pair. -/
theorem attLeaf_shape_iff (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    AttLeaf D hS (Φ.leaf ℓ) ↔
      (decodedCouple (D.couple (pairOfLeaf S hS (Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG))))).tree
        (if (pairOfLeaf G hG ℓ).firstLeaf hG = ℓ then 0 else 1) = TTree.leaf := by
  rw [attLeaf_iff, sideOf_shape_leaf Φ hS hG ℓ, pairOfLeaf_shape_leaf Φ hS hG ℓ]

end Shape

/-! ### The run class -/

section Class
variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))

include hG in
/-- **The attached-leaf condition is common to the run class.** -/
theorem attLeaf_member_iff (ℓ : GLeaf (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    AttLeaf y.1.data y.1.plain ((memShape a mk y hy).leaf ℓ) ↔
      AttLeaf a.prime.data a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf ℓ) := by
  rw [attLeaf_shape_iff (memShape a mk y hy) y.1.data y.1.plain hG ℓ,
    attLeaf_shape_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.data
      a.prime.prime.1 hG ℓ]
  have hN := memShape_nativeCouple a mk y hy hG (pairOfLeaf _ hG ℓ)
  have hg := congrArg LayeredGarden.garden hN
  rw [nativeCoupleLayered_garden, nativeCoupleLayered_garden] at hg
  rw [hg]

/-- Hinges are common to the run class. -/
theorem member_hinge_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    (∃ j, (memShape a mk y hy).br c = (unitClBlock (y.2 j)).upper) ↔
      ∃ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c =
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper := by
  rw [← (memShape a mk y hy).mem_hinges (source_disjMk a mk y hy),
    ← (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).mem_hinges
      (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)),
    memShape_hinges, stShape_hingesMk]

variable (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))

include hcapA hrepU in
/-- The representative: no leaf child of a hinge paired with a cap root is attached at a leaf. -/
theorem rep_hinge_not_attLeaf (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree)
    (hc : ∃ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c =
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper)
    (k : Fin 3) (ℓ : GLeaf (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) (hℓ : ℓ.toNode = c.child k)
    (hpJ : ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.pair ℓ).1.1 ∈ J) :
    ¬ AttLeaf a.prime.data a.prime.prime.1
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).leaf ℓ) := by
  intro hatt
  obtain ⟨j, hj⟩ := hc
  let Φ := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  have hd := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  have hcj : c = Φ.hinge hd j := Φ.br_inj (hj.trans (Φ.br_hinge hd j).symm)
  rw [hcj] at hℓ
  obtain ⟨v, hv, hcfp⟩ := cfp_of_hinge_leaf Φ a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) J hcapA hd j k ℓ hℓ hpJ hatt
  exact hrepU j v hv hcfp

include hy hG hcapA hcapY hrepU in
/-- **No core of an atom of a unit of a member is a capped flower parent.** -/
theorem member_unit_not_cfp (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
    (b : GBranch y.1.skeleton.tree) (hb : b ∈ (unitClBlock (y.2 j)).atoms) :
    ¬ IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (y.1.data.coreBranch y.1.plain b) := by
  intro hcfp
  let Φ := memShape a mk y hy
  have hd := source_disjMk a mk y hy
  obtain ⟨k, ℓ, hℓ, hpJ, hatt⟩ := cfp_unit_atom Φ y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
    J hcapY hd j b hb hcfp
  have hh : ∃ j', (memShape a mk y hy).br (Φ.hinge hd j) = (unitClBlock (y.2 j')).upper :=
    ⟨j, Φ.br_hinge hd j⟩
  exact rep_hinge_not_attLeaf a mk J hcapA hrepU (Φ.hinge hd j) ((member_hinge_iff a mk y hy _).mp hh) k ℓ hℓ hpJ
    ((attLeaf_member_iff a mk y hy hG ℓ).mp hatt)

include hG hcapA hcapY hrepU in
/-- **The capped flower parents at the `G_sb` atoms are common to the run class.** -/
theorem member_cfp_iff (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
        (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)) ↔
      IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J
        (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)) := by
  by_cases hc : ∃ j, (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c =
      (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper
  · obtain ⟨j, hj⟩ := hc
    obtain ⟨j', hj'⟩ := (member_hinge_iff a mk y hy c).mpr ⟨j, hj⟩
    constructor
    · intro h
      exact absurd h (member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j' _ (hj' ▸ upper_mem _))
    · intro h
      exact absurd h (hrepU j _ (hj ▸ upper_mem _))
  · have hcy : ¬ ∃ j, (memShape a mk y hy).br c = (unitClBlock (y.2 j)).upper :=
      fun h => hc ((member_hinge_iff a mk y hy c).mp h)
    push_neg at hc hcy
    rw [cfp_br_iff (memShape a mk y hy) y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY c
        hcy,
      cfp_br_iff (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.data
        a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA c hc]
    simp only [attLeaf_member_iff a mk y hy hG]

include hG hcapA hcapY hrepU in
/-- **Every skeleton branch of a member whose core is a capped flower parent is a `G_sb` atom.** -/
theorem member_cfp_br (b : GBranch y.1.skeleton.tree)
    (hb : IsCapFlowerParent (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (y.1.data.coreBranch y.1.plain b)) :
    ∃ c, (memShape a mk y hy).br c = b := by
  rcases ret_or_interior (blk := fun j => unitClBlock (y.2 j)) b.toNode with hr | ⟨j, hj, -⟩
  · exact (memShape a mk y hy).exists_br hr
  · exact absurd hb (member_unit_not_cfp a mk y hy hG J hcapA hcapY hrepU j b
      ((branch_mem_clRealizationNodes b).mp hj))

end Class

end WaveTurbulence.Flower.MkSlots.IntCore
