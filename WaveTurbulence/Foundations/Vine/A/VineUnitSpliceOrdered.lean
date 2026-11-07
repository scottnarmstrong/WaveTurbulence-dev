/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceOuter
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDarts
public import WaveTurbulence.Foundations.RegStruct.TreeRecovery
/-! Literal ordered-garden normalization for the actual selected splice maps. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- The existing actual full node map fixes every literal ordered address. -/
theorem unitSpliceNodeEquiv_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1 = n.1 := by
  by_cases hr : n.1.2 = []
  · exact Prod.ext (unitSpliceNodeEquiv_index Z σ hsel n)
      (((unitSpliceNodeEquiv_root Z σ hsel n).mpr hr).trans hr.symm)
  · let p := GNode.parent n hr
    let i := n.1.2.getLast hr
    have hch : p.child i = n := parent_child_eq_node n hr
    have ih := unitSpliceNodeEquiv_address Z σ hsel p.toNode
    have hp : ((unitSpliceMolIso Z σ hsel).e p).1 = p.1 :=
      (congrArg Subtype.val (unitSpliceNodeEquiv_branch Z σ hsel p)).symm.trans ih
    have he := unitSpliceNodeEquiv_child Z σ hsel p i
    rw [unitSpliceChildSlot_eq, hch] at he
    apply (congrArg Subtype.val he).trans
    change (((unitSpliceMolIso Z σ hsel).e p).1.1,
      ((unitSpliceMolIso Z σ hsel).e p).1.2 ++ [i]) = n.1
    rw [hp]
    exact congrArg Subtype.val hch
termination_by n.1.2.length
decreasing_by
  change n.1.2.dropLast.length < n.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hr
  omega

/-- The actual branch correspondence fixes addresses. -/
theorem unitSpliceMolIso_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    ((unitSpliceMolIso Z σ hsel).e b).1 = b.1 :=
  (congrArg Subtype.val (unitSpliceNodeEquiv_branch Z σ hsel b)).symm.trans
    (unitSpliceNodeEquiv_address Z σ hsel b.toNode)

/-- The actual full leaf correspondence fixes addresses. -/
theorem unitSpliceLeafEquiv_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (unitSpliceLeafEquiv Z σ hsel q).1 = q.1 :=
  (congrArg Subtype.val (unitSpliceNodeEquiv_leaf Z σ hsel q)).symm.trans
    (unitSpliceNodeEquiv_address Z σ hsel q.toNode)

/-- The actual ordered forests agree literally. -/
theorem unitSplice_tree_eq (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.tree = (stSt G σ).G.tree := by
  funext j
  apply Reg.tree_eq_of_leaves_eq
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := (unitSpliceLeafEquiv Z σ hsel).surjective ⟨(j, p), hp⟩
    have hv : q.1 = (j, p) := (unitSpliceLeafEquiv_address Z σ hsel q).symm.trans
      (congrArg Subtype.val hq)
    have hm := q.2
    simpa only [hv] using hm
  · intro hp
    let q : GLeaf (stSt G σ).G.tree := ⟨(j, p), hp⟩
    have hm := (unitSpliceLeafEquiv Z σ hsel q).2
    simpa only [unitSpliceLeafEquiv_address] using hm

/-- Ordered normalization of the actual selected splice, including marks and pairing. -/
theorem unitSplice_garden_eq (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ)).G = (stSt G σ).G := by
  apply garden_eq_of_leaf_transport
    ((stSt Z.target (transportPrescription Z.iso σ)).sig_eq.trans (stSt G σ).sig_eq.symm)
    (unitSplice_tree_eq Z σ hsel) (unitSpliceLeafEquiv Z σ hsel)
    (unitSpliceLeafEquiv_address Z σ hsel)
    (fun q => (unitSpliceLeafEquiv_pair Z σ hsel q).symm)
    (unitSpliceLeafEquiv_mark Z σ hsel)

end WaveTurbulence.VineA
