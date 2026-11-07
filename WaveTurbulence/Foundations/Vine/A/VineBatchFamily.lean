/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
/-! VINE-A2: the trace's atom bijection transports the indexed core family.
These identities tie molecular sigma transport to the actual LF family data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.LFTwist

/-- An operation's actual atom isomorphism is the universe branch map. -/
theorem operationMolIso_e {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) :
    (operationMolIso op).e = chosenBranchEquiv A.skeleton (A.family.placement i) op.choice := by
  cases op with
  | mk hc he ht hq ε con => cases ε <;> rfl

/-- The operation carries each indexed member's atom set, including itself. -/
theorem operationMolIso_atoms {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) (j : ι) :
    (operationMolIso op).img (A.family.atoms j) = op.output.family.atoms j := by
  cases op with
  | mk hc he ht hq ε con =>
    cases ε
    · exact Finset.image_id
    · rfl

theorem operationMolIso_upper {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) (j : ι) :
    (operationMolIso op).e (A.family.upper j) = op.output.family.upper j := by
  cases op with
  | mk hc he ht hq ε con => cases ε <;> rfl

theorem operationMolIso_lower {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) (j : ι) :
    (operationMolIso op).e (A.family.placement j).lower = (op.output.family.placement j).lower := by
  cases op with
  | mk hc he ht hq ε con =>
    cases ε
    · rfl
    · exact (A.family.nextPlacement_lower i j).symm

/-- The source kind is carried with every member of the indexed family. -/
theorem operationMolIso_kind {w p : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i) (j : ι) :
    A.family.kind j = op.output.family.kind j := by
  cases op with
  | mk hc he ht hq ε con => cases ε <;> rfl

/-- Composition of the literal atom-set maps. -/
theorem molIsoTrans_img {w : ℕ} {G H K : Garden w} (F : MolIso G.molecule H.molecule)
    (J : MolIso H.molecule K.molecule) (S : Finset (GBranch G.tree)) :
    (molIsoTrans F J).img S = J.img (F.img S) := by
  change S.image (J.e ∘ F.e) = (S.image F.e).image J.e
  rw [Finset.image_image]

namespace BatchIso
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Every trace transports all its indexed atom sets literally. -/
theorem atoms (h : BatchIso p kind L A B F) (j : ι) : F.img (A.family.atoms j) = B.family.atoms j := by
  induction h with
  | nil A =>
    change (A.family.atoms j).image id = A.family.atoms j
    exact Finset.image_id
  | skip _ _ ih => exact ih
  | apply op h ih =>
    rw [molIsoTrans_img, operationMolIso_atoms]
    exact ih

/-- Ordered upper joints follow the trace's branch map. -/
theorem upper (h : BatchIso p kind L A B F) (j : ι) : F.e (A.family.upper j) = B.family.upper j := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    exact (congrArg J.e (operationMolIso_upper op j)).trans ih

/-- Lower joints follow the same trace map. -/
theorem lower (h : BatchIso p kind L A B F) (j : ι) :
    F.e (A.family.placement j).lower = (B.family.placement j).lower := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    exact (congrArg J.e (operationMolIso_lower op j)).trans ih

/-- Vine types are unchanged throughout the full LF batch. -/
theorem vineKind (h : BatchIso p kind L A B F) (j : ι) : A.family.kind j = B.family.kind j := by
  induction h with
  | nil => rfl
  | skip _ _ ih => exact ih
  | apply op _ ih => exact (operationMolIso_kind op j).trans ih

end BatchIso
end WaveTurbulence.VineA
