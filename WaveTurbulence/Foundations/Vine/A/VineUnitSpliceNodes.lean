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

/-- The actual node map combines the proved branch and full-leaf maps. -/
noncomputable def unitSpliceNodeEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    GNode (stSt G σ).G.tree ≃ GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree :=
  (nodePieceEquiv (stSt G σ).G.tree).symm.trans
    ((Equiv.sumCongr (unitSpliceMolIso Z σ hsel).e (unitSpliceLeafEquiv Z σ hsel)).trans
      (nodePieceEquiv (stSt Z.target (transportPrescription Z.iso σ)).G.tree))

/-- Actual branching nodes follow the actual molecular branch map. -/
theorem unitSpliceNodeEquiv_branch (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (b : GBranch (stSt G σ).G.tree) :
    unitSpliceNodeEquiv Z σ hsel b.toNode = ((unitSpliceMolIso Z σ hsel).e b).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inl b)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Actual leaves follow the complete leaf map, including boundary leaves without LP darts. -/
theorem unitSpliceNodeEquiv_leaf (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    unitSpliceNodeEquiv Z σ hsel q.toNode = (unitSpliceLeafEquiv Z σ hsel q).toNode := by
  change (nodePieceEquiv _) ((Equiv.sumCongr _ _)
    ((nodePieceEquiv _).symm ((nodePieceEquiv _) (.inr q)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every actual surviving node retains its sign. -/
theorem unitSpliceNodeEquiv_sign (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.sign (unitSpliceNodeEquiv Z σ hsel n) =
      (stSt G σ).G.sign n := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg _ (unitSpliceNodeEquiv_branch Z σ hsel b)).trans (unitSpliceMolIso_branch_sign Z σ hsel b)
  | inr q => exact (congrArg _ (unitSpliceNodeEquiv_leaf Z σ hsel q)).trans (unitSpliceLeafEquiv_sign Z σ hsel q)

/-- Every surviving node retains its root-tree index. -/
theorem unitSpliceNodeEquiv_index (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1.1 = n.1.1 := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ).G.tree).surjective n
  cases x with
  | inl b => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_branch Z σ hsel b)).trans (unitSpliceMolIso_branch_index Z σ hsel b)
  | inr q => exact (congrArg (fun n => n.1.1) (unitSpliceNodeEquiv_leaf Z σ hsel q)).trans (unitSpliceLeafEquiv_index Z σ hsel q)

/-- Every surviving root is detected by the full actual node map. -/
theorem unitSpliceNodeEquiv_root (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) :
    (unitSpliceNodeEquiv Z σ hsel n).1.2 = [] ↔ n.1.2 = [] := by
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ).G.tree).surjective n
  cases x with
  | inl b => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_branch Z σ hsel b))).trans (unitSpliceMolIso_branch_root Z σ hsel b)
  | inr q => exact (Iff.of_eq (congrArg (fun n => n.1.2 = []) (unitSpliceNodeEquiv_leaf Z σ hsel q))).trans (unitSpliceLeafEquiv_root Z σ hsel q)

/-- Equality of actual nodes transports their parent branching nodes. -/
theorem spliceNodeParent_congr {F : Fin w → TTree} {n m : GNode F}
    (hn : n.1.2 ≠ []) (hm : m.1.2 ≠ []) (he : n = m) : GNode.parent n hn = GNode.parent m hm := by
  apply Subtype.ext
  exact congrArg (fun q : GNode F => (q.1.1, q.1.2.dropLast)) he

/-- The full actual node map preserves all surviving parent incidences. -/
theorem unitSpliceNodeEquiv_parent (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (n : GNode (stSt G σ).G.tree) (hn : n.1.2 ≠ []) :
    let e := unitSpliceNodeEquiv Z σ hsel
    let hnew : (e n).1.2 ≠ [] := fun h => hn ((unitSpliceNodeEquiv_root Z σ hsel n).mp h)
    (unitSpliceMolIso Z σ hsel).e (GNode.parent n hn) = GNode.parent (e n) hnew := by
  dsimp only
  obtain ⟨x, rfl⟩ := (nodePieceEquiv (stSt G σ).G.tree).surjective n
  cases x with
  | inl b =>
    have hb : ((unitSpliceMolIso Z σ hsel).e b).1.2 ≠ [] := fun h => hn ((unitSpliceMolIso_branch_root Z σ hsel b).mp h)
    exact (unitSpliceMolIso_parent Z σ hsel b hn).trans
      (spliceNodeParent_congr hb _ (unitSpliceNodeEquiv_branch Z σ hsel b).symm)
  | inr q =>
    have hq : (unitSpliceLeafEquiv Z σ hsel q).1.2 ≠ [] := fun h => hn ((unitSpliceLeafEquiv_root Z σ hsel q).mp h)
    exact (unitSpliceLeafEquiv_parent Z σ hsel q hn).trans
      (spliceNodeParent_congr hq _ (unitSpliceNodeEquiv_leaf Z σ hsel q).symm)

end WaveTurbulence.VineA
