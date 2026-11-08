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

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_address`). -/
theorem unitSpliceNodeEquiv_addressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (n : GNode (stSt G σ Mk).G.tree) :
    (unitSpliceNodeEquivMk Z σ hT hsel n).1 = n.1 := by
  by_cases hr : n.1.2 = []
  · exact Prod.ext (unitSpliceNodeEquiv_indexMk Z σ hT hsel n)
      (((unitSpliceNodeEquiv_rootMk Z σ hT hsel n).mpr hr).trans hr.symm)
  · let p := GNode.parent n hr
    let i := n.1.2.getLast hr
    have hch : p.child i = n := parent_child_eq_node n hr
    have ih := unitSpliceNodeEquiv_addressMk Z σ hT hsel p.toNode
    have hp : ((unitSpliceMolIsoMk Z σ hT hsel).e p).1 = p.1 :=
      (congrArg Subtype.val (unitSpliceNodeEquiv_branchMk Z σ hT hsel p)).symm.trans ih
    have he := unitSpliceNodeEquiv_childMk Z σ hT hsel p i
    rw [unitSpliceChildSlot_eqMk, hch] at he
    apply (congrArg Subtype.val he).trans
    change (((unitSpliceMolIsoMk Z σ hT hsel).e p).1.1,
      ((unitSpliceMolIsoMk Z σ hT hsel).e p).1.2 ++ [i]) = n.1
    rw [hp]
    exact congrArg Subtype.val hch
termination_by n.1.2.length
decreasing_by
  change n.1.2.dropLast.length < n.1.2.length
  rw [List.length_dropLast]
  have hpos := List.length_pos_of_ne_nil hr
  omega

/-- The existing actual full node map fixes every literal ordered address. -/
theorem unitSpliceNodeEquiv_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1 = n.1 :=
  unitSpliceNodeEquiv_addressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel n

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_address`). -/
theorem unitSpliceMolIso_addressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) :
    ((unitSpliceMolIsoMk Z σ hT hsel).e b).1 = b.1 :=
  (congrArg Subtype.val (unitSpliceNodeEquiv_branchMk Z σ hT hsel b)).symm.trans
    (unitSpliceNodeEquiv_addressMk Z σ hT hsel b.toNode)

/-- The actual branch correspondence fixes addresses. -/
theorem unitSpliceMolIso_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    ((unitSpliceMolIso Z σ hsel).e b).1 = b.1 :=
  unitSpliceMolIso_addressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel b

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_address`). -/
theorem unitSpliceLeafEquiv_addressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (unitSpliceLeafEquivMk Z σ hT hsel q).1 = q.1 :=
  (congrArg Subtype.val (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).symm.trans
    (unitSpliceNodeEquiv_addressMk Z σ hT hsel q.toNode)

/-- The actual full leaf correspondence fixes addresses. -/
theorem unitSpliceLeafEquiv_address (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (unitSpliceLeafEquiv Z σ hsel q).1 = q.1 :=
  unitSpliceLeafEquiv_addressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

/-- B1b-2 (Mk-general form of `unitSplice_tree_eq`). -/
theorem unitSplice_tree_eqMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree = (stSt G σ Mk).G.tree := by
  funext j
  apply Reg.tree_eq_of_leaves_eq
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := (unitSpliceLeafEquivMk Z σ hT hsel).surjective ⟨(j, p), hp⟩
    have hv : q.1 = (j, p) := (unitSpliceLeafEquiv_addressMk Z σ hT hsel q).symm.trans
      (congrArg Subtype.val hq)
    have hm := q.2
    simpa only [hv] using hm
  · intro hp
    let q : GLeaf (stSt G σ Mk).G.tree := ⟨(j, p), hp⟩
    have hm := (unitSpliceLeafEquivMk Z σ hT hsel q).2
    simpa only [unitSpliceLeafEquiv_addressMk] using hm

/-- The actual ordered forests agree literally. -/
theorem unitSplice_tree_eq (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.tree = (stSt G σ).G.tree :=
  unitSplice_tree_eqMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitSplice_garden_eq`). -/
theorem unitSplice_garden_eqMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G = (stSt G σ Mk).G := by
  apply garden_eq_of_leaf_transport
    ((stSt Z.target (transportPrescription Z.iso σ) Mk').sig_eq.trans (stSt G σ Mk).sig_eq.symm)
    (unitSplice_tree_eqMk Z σ hT hsel) (unitSpliceLeafEquivMk Z σ hT hsel)
    (unitSpliceLeafEquiv_addressMk Z σ hT hsel)
    (fun q => (unitSpliceLeafEquiv_pairMk Z σ hT hsel q).symm)
    (unitSpliceLeafEquiv_markMk Z σ hT hsel)

/-- Ordered normalization of the actual selected splice, including marks and pairing. -/
theorem unitSplice_garden_eq (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    (stSt Z.target (transportPrescription Z.iso σ)).G = (stSt G σ).G :=
  unitSplice_garden_eqMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

end WaveTurbulence.VineA
