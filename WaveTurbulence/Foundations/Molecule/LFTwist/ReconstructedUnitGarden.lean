/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.AllPairTransport
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructedUnitForest
public import WaveTurbulence.Foundations.Molecule.LFTwist.PlainGardenExt

/-! # Literal reconstructed-garden naturality for erased LF attachments -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ}

theorem AddressPaired.symm {G : Garden w} {a b : Address w} (h : AddressPaired G a b) :
    AddressPaired G b a := by
  obtain ⟨l,ha,hb⟩ := h
  exact ⟨G.pair l,hb,(congrArg Subtype.val (G.pair_pair l)).trans ha⟩

theorem AddressPaired.partner {G : Garden w} {a b : Address w} (h : AddressPaired G a b)
    (l : GLeaf G.tree) (hl : l.1 = a) : (G.pair l).1 = b := by
  obtain ⟨m,hm,hp⟩ := h
  have he : l = m := Subtype.ext (hl.trans hm.symm)
  exact (congrArg (fun z => (G.pair z).1) he).trans hp

variable (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

/-- Literal partner transport for every actual old leaf. -/
theorem all_leaf_partners_twist (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (l : GLeaf (D.garden hS).tree) :
    AddressPaired ((twistReconstruction S P hS D).garden (unitTwistGarden_plain S P hS))
      (inflatedExchange S P D l.1) (inflatedExchange S P D ((D.garden hS).pair l).1) := by
  have hh := all_pairs_addressPaired_twist S P hS D hnil hq (sourcePairAt (D.garden hS) l)
    (sourcePairAt_mem _ (D.garden_decodes hS).1 l)
  unfold sourcePairAt at hh
  split_ifs at hh with hs
  · exact hh
  · exact hh.symm

/-- The physical map is exactly the actual expanded unit's leaf bijection. -/
theorem expanded_leaf_exchange (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (l : GLeaf (D.garden hS).tree) :
    (coreLeafEquiv (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq) l).1 =
      inflatedExchange S P D l.1 := by
  let Q := expandedPlacement D hS (D.garden_decodes hS) P hq
  have ha : Q.lower.1 = inflatedPosition S D.tree P.lower.toNode := by
    change addrExt (inflatedPosition S D.tree P.lower.toNode) (D.tree P.lower).lonePath = _
    simp only [hnil, RegChain.lonePath, addrExt_nil]
  have hb : ((D.garden hS).pair Q.retained).1 =
      inflatedPosition S D.tree (S.pair P.retained).toNode :=
    congrArg Subtype.val (decodedTrivLeaf_pair D hS (D.garden_decodes hS) P.retained hq)
  exact (coreLeafEquiv_address (D.garden hS) Q l).trans
    (by rw [ha,hb]; rfl)

/-- Reconstruction of the unit-twisted skeleton equals the actual unit twist
of the reconstruction, as an ordinary garden with its entire leaf involution. -/
theorem reconstructed_unit_garden (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (twistReconstruction S P hS D).garden (unitTwistGarden_plain S P hS) =
      unitTwistGarden (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq) := by
  let E := twistReconstruction S P hS D
  let hnew := unitTwistGarden_plain S P hS
  let G := D.garden hS
  let Q := expandedPlacement D hS (D.garden_decodes hS) P hq
  apply plainGarden_eq_of_pair_addresses (E.garden_decodes hnew).1
    (unitTwistGarden_plain G Q (D.garden_decodes hS).1) rfl
    (reconstructed_unit_forest S P hS D hnil hq)
  intro l m hlm
  obtain ⟨x,rfl⟩ := (coreLeafEquiv G Q).surjective m
  have hp := all_leaf_partners_twist S P hS D hnil hq x
  have hx := expanded_leaf_exchange S P hS D hnil hq x
  have hx' := expanded_leaf_exchange S P hS D hnil hq (G.pair x)
  exact (hp.partner l (hlm.trans hx)).trans
    (hx'.symm.trans (congrArg Subtype.val (unitTwistGarden_pair G Q x)).symm)

end WaveTurbulence.LFTwist
