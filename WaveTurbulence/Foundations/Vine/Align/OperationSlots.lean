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

/-- B1b (Mk-general form of `shape_leaf_prescription_cast`). -/
theorem shape_leaf_prescription_castMk {S : Garden w} {τ σ : Prescription S} (he : τ = σ)
    {Mk : Set (Stage1.CLVine _)} (e : (stSt (Mk := Mk) S σ).G = (stSt (Mk := Mk) S τ).G) (l : GLeaf (stSt (Mk := Mk) S σ).G.tree) :
    (stShape (Mk := Mk) (Mole.garden_isMolecule S) τ).leaf (leafCast e l) =
      (stShape (Mk := Mk) (Mole.garden_isMolecule S) σ).leaf l := by subst τ; rfl

/-- B1b (Mk-general form of `shape_branch_prescription_cast`). -/
theorem shape_branch_prescription_castMk {S : Garden w} {τ σ : Prescription S} (he : τ = σ)
    {Mk : Set (Stage1.CLVine _)} (e : (stSt (Mk := Mk) S σ).G = (stSt (Mk := Mk) S τ).G) (b : GBranch (stSt (Mk := Mk) S σ).G.tree) :
    (stSt (Mk := Mk) S τ).M.ob (gardenBranchCast e b) = (stSt (Mk := Mk) S σ).M.ob b := by subst τ; rfl

/-- B1b-3 (Mk-general form of `operation_leaf_cast`). -/
theorem operation_leaf_castMk {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (l : GLeaf (stSt A.skeleton σ Mk).G.tree) :
    (stShape (Mole.garden_isMolecule op.output.skeleton) (transportPrescription (operationMolIso op) σ) Mk').leaf
      (leafCast (operation_splice_garden_eqMk hA op hT).symm l) =
    chosenLeafEquiv A.skeleton (A.family.placement i) op.choice
      ((stShape (Mole.garden_isMolecule A.skeleton) σ Mk).leaf l) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      change (stShape _ (transportPrescription (molIsoRefl _) σ) Mk).leaf _ = _
      exact shape_leaf_prescription_castMk (transportPrescription_refl σ) _ l
    · exact unit_leaf_castMk (selectedMemberSite hA i) σ hT ⟨familyVine A.family i, hA.1 i, rfl⟩ l

/-- B1b-3 (Mk-general form of `operation_branch_cast`). -/
theorem operation_branch_castMk {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (b : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').M.ob
      (gardenBranchCast (operation_splice_garden_eqMk hA op hT).symm b) =
    chosenBranchEquiv A.skeleton (A.family.placement i) op.choice ((stSt A.skeleton σ Mk).M.ob b) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      change (stSt _ (transportPrescription (molIsoRefl _) σ) Mk).M.ob _ = _
      exact shape_branch_prescription_castMk (transportPrescription_refl σ) _ b
    · exact unit_branch_castMk (selectedMemberSite hA i) σ hT ⟨familyVine A.family i, hA.1 i, rfl⟩ b

variable {G H : Garden w}
def pairCast (e : G = H) (q : SourcePair G) : SourcePair H := e ▸ q

theorem slotCast_pair (e : G = H) (q : SourcePair G) :
    slotCast e (.inl q) = .inl (pairCast e q) := by subst H; rfl

theorem pairCast_first (e : G = H) (hG : G.IsPlain) (hH : H.IsPlain) (q : SourcePair G) :
    (pairCast e q).firstLeaf hH = leafCast e (q.firstLeaf hG) := by subst H; rfl

/-- B1b-3 (Mk-general form of `operation_iota`). -/
theorem operation_iotaMk {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    (stShape (Mole.garden_isMolecule op.output.skeleton) (transportPrescription (operationMolIso op) σ) Mk').iota
      op.output.plain ((stSt _ _ Mk').plain op.output.plain)
      (slotCast (operation_splice_garden_eqMk hA op hT).symm s) =
    operationSlotMap op
      ((stShape (Mole.garden_isMolecule A.skeleton) σ Mk).iota A.plain ((stSt _ _ Mk).plain A.plain) s) := by
  cases s with
  | inl q =>
    rw [slotCast_pair]
    simp only [SpliceShape.iota, operationSlotMap]
    rw [pairCast_first _ ((stSt _ _ Mk).plain A.plain), operation_leaf_castMk hA op hT]
    exact congrArg Sum.inl (sourcePairEquiv_pairOfLeaf A.plain op.output.plain
      (chosenLeafEquiv A.skeleton (A.family.placement i) op.choice)
      (chosenLeafEquiv_pair _ _ _) _).symm
  | inr b =>
    rw [slotCast_inr]
    exact congrArg Sum.inr (operation_branch_castMk hA op hT b)

end WaveTurbulence.VineAlign
