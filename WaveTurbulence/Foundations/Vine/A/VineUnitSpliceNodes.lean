/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceTimeDomain
public import WaveTurbulence.Foundations.Molecule.TwistNodeLabels
/-! The complete actual node correspondence of selected simultaneous
splices, with signed rooted-forest and parent compatibility. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv`). -/
noncomputable def unitSpliceNodeEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    GNode (stSt G σ Mk).G.tree ≃ GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree :=
  (nodePieceEquiv (stSt G σ Mk).G.tree).symm.trans
    ((Equiv.sumCongr (unitSpliceMolIsoMk Z σ hT hsel).e (unitSpliceLeafEquivMk Z σ hT hsel)).trans
      (nodePieceEquiv (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree))

/-- The actual node map combines the proved branch and full-leaf maps. -/
noncomputable def unitSpliceNodeEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    GNode (stSt G σ).G.tree ≃ GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree :=
  unitSpliceNodeEquivMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_branch`). -/
theorem unitSpliceNodeEquiv_branchMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (b : GBranch (stSt G σ Mk).G.tree) :
    unitSpliceNodeEquivMk Z σ hT hsel b.toNode = ((unitSpliceMolIsoMk Z σ hT hsel).e b).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inl b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Actual branching nodes follow the actual molecular branch map. -/
theorem unitSpliceNodeEquiv_branch (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    unitSpliceNodeEquiv Z σ hsel b.toNode = ((unitSpliceMolIso Z σ hsel).e b).toNode :=
  unitSpliceNodeEquiv_branchMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel b

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_leaf`). -/
theorem unitSpliceNodeEquiv_leafMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    unitSpliceNodeEquivMk Z σ hT hsel q.toNode = (unitSpliceLeafEquivMk Z σ hT hsel q).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inr q)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Actual leaves follow the complete leaf map, including boundary leaves without LP darts. -/
theorem unitSpliceNodeEquiv_leaf (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    unitSpliceNodeEquiv Z σ hsel q.toNode = (unitSpliceLeafEquiv Z σ hsel q).toNode :=
  unitSpliceNodeEquiv_leafMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_sign`). -/
theorem unitSpliceNodeEquiv_signMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (n : GNode (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.sign (unitSpliceNodeEquivMk Z σ hT hsel n) =
      (stSt G σ Mk).G.sign n := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg _ (unitSpliceNodeEquiv_branchMk Z σ hT hsel b)).trans (unitSpliceMolIso_branch_signMk Z σ hT hsel b)
  | inr q => exact (congrArg _ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans (unitSpliceLeafEquiv_signMk Z σ hT hsel q)

/-- Every actual surviving node retains its sign. -/
theorem unitSpliceNodeEquiv_sign (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.sign (unitSpliceNodeEquiv Z σ hsel n) =
      (stSt G σ).G.sign n := unitSpliceNodeEquiv_signMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel n

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_index`). -/
theorem unitSpliceNodeEquiv_indexMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (n : GNode (stSt G σ Mk).G.tree) :
    (unitSpliceNodeEquivMk Z σ hT hsel n).1.1 = n.1.1 := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_branchMk Z σ hT hsel b)).trans (unitSpliceMolIso_branch_indexMk Z σ hT hsel b)
  | inr q => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans (unitSpliceLeafEquiv_indexMk Z σ hT hsel q)

/-- Every surviving node retains its root-tree index. -/
theorem unitSpliceNodeEquiv_index (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1.1 = n.1.1 :=
  unitSpliceNodeEquiv_indexMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel n

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_root`). -/
theorem unitSpliceNodeEquiv_rootMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (n : GNode (stSt G σ Mk).G.tree) :
    (unitSpliceNodeEquivMk Z σ hT hsel n).1.2 = [] ↔ n.1.2 = [] := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ Mk).G.tree).surjective n
  cases x with
  | inl b => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_branchMk Z σ hT hsel b))).trans (unitSpliceMolIso_branch_rootMk Z σ hT hsel b)
  | inr q => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q))).trans (unitSpliceLeafEquiv_rootMk Z σ hT hsel q)

/-- Every surviving root is detected by the full actual node map. -/
theorem unitSpliceNodeEquiv_root (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1.2 = [] ↔ n.1.2 = [] :=
  unitSpliceNodeEquiv_rootMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel n

/-- Equality of actual nodes transports their parent branching nodes. -/
theorem spliceNodeParent_congr {F : Fin w → TTree} {n m : GNode F}
    (hn : n.1.2 ≠ []) (hm : m.1.2 ≠ []) (he : n = m) : GNode.parent n hn = GNode.parent m hm := by
  apply Subtype.ext
  exact congrArg (fun q : GNode F => (q.1.1, q.1.2.dropLast)) he

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_parent`). -/
theorem unitSpliceNodeEquiv_parentMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (n : GNode (stSt G σ Mk).G.tree) (hn : n.1.2 ≠ []) :
    let e := unitSpliceNodeEquivMk Z σ hT hsel
    let hnew : (e n).1.2 ≠ [] := fun h => hn ((unitSpliceNodeEquiv_rootMk Z σ hT hsel n).mp h)
    (unitSpliceMolIsoMk Z σ hT hsel).e (GNode.parent n hn) = GNode.parent (e n) hnew := by
  dsimp only
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ Mk).G.tree).surjective n
  cases x with
  | inl b =>
    have hb : ((unitSpliceMolIsoMk Z σ hT hsel).e b).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_rootMk Z σ hT hsel b).mp h)
    exact (unitSpliceMolIso_parentMk Z σ hT hsel b hn).trans
      (spliceNodeParent_congr hb _ (unitSpliceNodeEquiv_branchMk Z σ hT hsel b).symm)
  | inr q =>
    have hq : (unitSpliceLeafEquivMk Z σ hT hsel q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_rootMk Z σ hT hsel q).mp h)
    exact (unitSpliceLeafEquiv_parentMk Z σ hT hsel q hn).trans
      (spliceNodeParent_congr hq _ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q).symm)

/-- The full actual node map preserves all surviving parent incidences. -/
theorem unitSpliceNodeEquiv_parent (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) (hn : n.1.2 ≠ []) :
    let e := unitSpliceNodeEquiv Z σ hsel
    let hnew : (e n).1.2 ≠ [] := fun h => hn ((unitSpliceNodeEquiv_root Z σ hsel n).mp h)
    (unitSpliceMolIso Z σ hsel).e (GNode.parent n hn) = GNode.parent (e n) hnew :=
  unitSpliceNodeEquiv_parentMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel n hn

end WaveTurbulence.VineA
