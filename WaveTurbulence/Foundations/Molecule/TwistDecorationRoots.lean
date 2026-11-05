/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorationEquiv

/-! # Prescribed roots in the actual decoration bijection

TARGET twistexplain (d): the correspondence preserves every prescribed
root vector, hence restricts to the literal integer n-decorations.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The common actual address formula applies to the full node bijection. -/
theorem naiveNodeEquiv_address (n : GNode G.tree) :
    (naiveNodeEquiv G P n).1 = exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep n.1 := by
  obtain ⟨q,rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change (naiveNodeEquiv G P b.toNode).1 = _
    rw [naiveNodeEquiv_branch]
    exact coreBranchEquiv_address G P b
  | inr l =>
    change (naiveNodeEquiv G P l.toNode).1 = _
    rw [naiveNodeEquiv_leaf]
    exact coreLeafEquiv_address G P l

/-- Every actual root keeps its root index and address. -/
theorem naiveNodeEquiv_root (j : Fin w) :
    naiveNodeEquiv G P (GNode.root G.tree j) = GNode.root (unitTwistGarden G P).tree j := by
  apply Subtype.ext
  rw [naiveNodeEquiv_address]
  have hpre : ¬ P.lower.1.2 <+: [] := fun hp => P.nonroot (List.eq_nil_of_prefix_nil hp)
  have hne : (j,([] : Path)) ≠ (G.pair P.retained).1 := by
    intro he
    exact P.paired_nonroot (congrArg Prod.snd he).symm
  change exchangeAddress P.lower.1 (G.pair P.retained).1 P.keep (j,[]) = (j,[])
  simp [exchangeAddress,hpre,hne]

/-- The three overwritten nodes are nonroot, so root labels are untouched. -/
theorem switchedOldLabels_root {E : Type*} (κ : GNode G.tree → E) (j : Fin w) :
    switchedOldLabels G P κ (GNode.root G.tree j) = κ (GNode.root G.tree j) := by
  have hb : GNode.root G.tree j ≠ P.lower.toNode := by
    intro he
    exact P.nonroot (congrArg (fun n : GNode G.tree => n.1.2) he).symm
  have hl : GNode.root G.tree j ≠ P.retained.toNode := by
    intro he
    exact retained_nonroot G P (congrArg (fun n : GNode G.tree => n.1.2) he).symm
  have hp : GNode.root G.tree j ≠ (G.pair P.retained).toNode := by
    intro he
    exact P.paired_nonroot (congrArg (fun n : GNode G.tree => n.1.2) he).symm
  simp [switchedOldLabels,hb,hl,hp]

/-- Forward label transport keeps each prescribed root value. -/
theorem twistNodeLabels_root {E : Type*} (κ : GNode G.tree → E) (j : Fin w) :
    twistNodeLabels G P κ (GNode.root (unitTwistGarden G P).tree j) = κ (GNode.root G.tree j) := by
  exact (congrArg (twistNodeLabels G P κ) (naiveNodeEquiv_root G P j)).symm.trans
    ((twistNodeLabels_naive G P κ _).trans (switchedOldLabels_root G P κ j))

/-- Inverse label transport keeps each prescribed root value. -/
theorem untwistNodeLabels_root {E : Type*} (η : GNode (unitTwistGarden G P).tree → E) (j : Fin w) :
    untwistNodeLabels G P η (GNode.root G.tree j) = η (GNode.root (unitTwistGarden G P).tree j) := by
  unfold untwistNodeLabels
  rw [switchedOldLabels_root,naiveNodeEquiv_root]

/-- Actual decoration bijection with arbitrary prescribed root vectors. -/
@[expose] noncomputable def unitTwistRootDecorationEquiv (E : Type*) [AddCommGroup E] (n : Fin w → E) :
    {κ : GNode G.tree → E // IsDecoration G κ ∧ ∀ j, κ (GNode.root G.tree j) = n j} ≃
    {η : GNode (unitTwistGarden G P).tree → E // IsDecoration (unitTwistGarden G P) η ∧
      ∀ j, η (GNode.root (unitTwistGarden G P).tree j) = n j} where
  toFun κ := ⟨twistNodeLabels G P κ.1,twistNodeLabels_isDecoration G P κ.1 κ.2.1,
    fun j => (twistNodeLabels_root G P κ.1 j).trans (κ.2.2 j)⟩
  invFun η := ⟨untwistNodeLabels G P η.1,untwistNodeLabels_isDecoration G P η.1 η.2.1,
    fun j => (untwistNodeLabels_root G P η.1 j).trans (η.2.2 j)⟩
  left_inv κ := Subtype.ext (untwist_twistNodeLabels G P κ.1 (κ.2.1.2 P.retained))
  right_inv η := Subtype.ext (twist_untwistNodeLabels G P η.1 η.2.1.2)

/-- The literal source integer-decoration carriers are bijective under the actual unit twist. -/
@[expose] noncomputable def unitTwistIntDecorationEquiv (d : ℕ) (n : Fin w → (Fin d → ℤ)) :
    IntDecoration G d n ≃ IntDecoration (unitTwistGarden G P) d n :=
  unitTwistRootDecorationEquiv G P (Fin d → ℤ) n

end WaveTurbulence.Twist
