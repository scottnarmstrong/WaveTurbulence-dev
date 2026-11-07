/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.SurvivingSlots
/-! The exact outer-slot diagram for a single selected LF operation. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {ι : Type*}
  {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}

noncomputable def operationSlotMap (op : FamilyOperation (p := p) (kind := kind) A i) :
    ReplacementSlot A.skeleton → ReplacementSlot op.output.skeleton :=
  Sum.map (chosenPairEquiv A.skeleton (A.family.placement i) A.plain op.choice)
    (chosenBranchEquiv A.skeleton (A.family.placement i) op.choice)

theorem shape_leaf_prescription_cast {S : Garden w} {τ σ : Prescription S} (he : τ = σ)
    (e : (stSt S σ).G = (stSt S τ).G) (l : GLeaf (stSt S σ).G.tree) :
    (stShape (Mole.garden_isMolecule S) τ).leaf (leafCast e l) =
      (stShape (Mole.garden_isMolecule S) σ).leaf l := by subst τ; rfl

theorem shape_branch_prescription_cast {S : Garden w} {τ σ : Prescription S} (he : τ = σ)
    (e : (stSt S σ).G = (stSt S τ).G) (b : GBranch (stSt S σ).G.tree) :
    (stSt S τ).M.ob (gardenBranchCast e b) = (stSt S σ).M.ob b := by subst τ; rfl

theorem operation_leaf_cast (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (l : GLeaf (stSt A.skeleton σ).G.tree) :
    (stShape (Mole.garden_isMolecule op.output.skeleton) (transportPrescription (operationMolIso op) σ)).leaf
      (leafCast (operation_splice_garden_eq hA op).symm l) =
    chosenLeafEquiv A.skeleton (A.family.placement i) op.choice
      ((stShape (Mole.garden_isMolecule A.skeleton) σ).leaf l) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change (stShape _ (transportPrescription (molIsoRefl _) σ)).leaf _ = _
      exact shape_leaf_prescription_cast (transportPrescription_refl σ) _ l
    · exact unit_leaf_cast (selectedMemberSite hA i) σ ⟨familyVine A.family i, hA.1 i, rfl⟩ l

theorem operation_branch_cast (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (b : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M.ob
      (gardenBranchCast (operation_splice_garden_eq hA op).symm b) =
    chosenBranchEquiv A.skeleton (A.family.placement i) op.choice ((stSt A.skeleton σ).M.ob b) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change (stSt _ (transportPrescription (molIsoRefl _) σ)).M.ob _ = _
      exact shape_branch_prescription_cast (transportPrescription_refl σ) _ b
    · exact unit_branch_cast (selectedMemberSite hA i) σ ⟨familyVine A.family i, hA.1 i, rfl⟩ b

variable {G H : Garden w}
def pairCast (e : G = H) (q : SourcePair G) : SourcePair H := e ▸ q

theorem slotCast_pair (e : G = H) (q : SourcePair G) :
    slotCast e (.inl q) = .inl (pairCast e q) := by subst H; rfl

theorem pairCast_first (e : G = H) (hG : G.IsPlain) (hH : H.IsPlain) (q : SourcePair G) :
    (pairCast e q).firstLeaf hH = leafCast e (q.firstLeaf hG) := by subst H; rfl

/-- The actual slot embeddings commute, with the literal garden equality cast. -/
theorem operation_iota (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (s : ReplacementSlot (stSt A.skeleton σ).G) :
    (stShape (Mole.garden_isMolecule op.output.skeleton) (transportPrescription (operationMolIso op) σ)).iota
      op.output.plain ((stSt _ _).plain op.output.plain)
      (slotCast (operation_splice_garden_eq hA op).symm s) =
    operationSlotMap op ((stShape (Mole.garden_isMolecule A.skeleton) σ).iota A.plain ((stSt _ _).plain A.plain) s) := by
  cases s with
  | inl q =>
    rw [slotCast_pair]
    simp only [SpliceShape.iota, operationSlotMap]
    rw [pairCast_first _ ((stSt _ _).plain A.plain), operation_leaf_cast hA op]
    exact congrArg Sum.inl (sourcePairEquiv_pairOfLeaf A.plain op.output.plain
      (chosenLeafEquiv A.skeleton (A.family.placement i) op.choice)
      (chosenLeafEquiv_pair _ _ _) _).symm
  | inr b =>
    rw [slotCast_inr]
    exact congrArg Sum.inr (operation_branch_cast hA op b)

end WaveTurbulence.VineAlign
