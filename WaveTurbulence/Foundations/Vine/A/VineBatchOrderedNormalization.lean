/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.Vine.A.VineCollectionTransport
/-! Literal ordered normalization along every actual selected LF batch. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}

/-- Every actual fine operation leaves the literal normalized garden unchanged. -/
theorem operation_splice_garden_eq {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).G = (stSt A.skeleton σ).G := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact congrArg (fun τ => (stSt A.skeleton τ).G) (transportPrescription_refl σ)
    · exact unitSplice_garden_eq (selectedMemberSite hA i) σ ⟨familyVine A.family i, hA.1 i, rfl⟩

/-- Every actual fine batch has exactly the same ordered spliced garden. -/
theorem BatchIso.splice_garden_eq {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    (stSt B.skeleton (transportPrescription F σ)).G = (stSt A.skeleton σ).G := by
  induction h with
  | nil => exact congrArg (fun τ => (stSt _ τ).G) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hA
  | apply op _ ih =>
    have hb := ih _ (isV0Fam_operation hA op)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_garden_eq hA op)

/-- Quotient atom addresses commute with one actual fine operation. -/
theorem operation_splice_pi_address {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (v : GBranch A.skeleton.tree) :
    ((stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M.pi
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).hcls ((operationMolIso op).e v)).1 =
      ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls v).1 := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact congrArg (fun τ => ((stSt A.skeleton τ).M.pi (stSt A.skeleton τ).hcls v).1)
        (transportPrescription_refl σ)
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      exact (congrArg Subtype.val (unitSplice_pi Z σ hs v)).trans (unitSpliceMolIso_address Z σ hs _)

/-- The forward quotient diagram in literal addresses for a full actual batch. -/
theorem BatchIso.splice_pi_address {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (v : GBranch A.skeleton.tree) :
    ((stSt B.skeleton (transportPrescription F σ)).M.pi
      (stSt B.skeleton (transportPrescription F σ)).hcls (F.e v)).1 =
      ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls v).1 := by
  induction h with
  | nil =>
    change ((stSt _ (transportPrescription (molIsoRefl _) σ)).M.pi _ v).1 = _
    rw [transportPrescription_refl]
  | skip _ _ ih => exact ih σ hA v
  | apply op _ ih =>
    have hb := ih _ (isV0Fam_operation hA op) ((operationMolIso op).e v)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_pi_address hA op v)

/-- The quotient reverses the old-name map on every surviving branch. -/
theorem splice_pi_ob {G : Garden w} (st : SpState G) (b : GBranch st.G.tree) : st.M.pi st.hcls (st.M.ob b) = b := by
  apply st.M.ob_inj
  exact (st.M.ob_pi st.hcls _).trans (splice_old_branch_fixed st b)

/-- The actual full-batch quotient map fixes every literal branch address. -/
theorem BatchIso.spliceMolIso_address {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (b : GBranch (stSt A.skeleton σ).G.tree) : ((h.spliceMolIso σ hA).e b).1 = b.1 := by
  have hp := h.splice_pi σ hA ((stSt A.skeleton σ).M.ob b)
  rw [splice_pi_ob] at hp
  exact (congrArg Subtype.val hp).trans
    ((h.splice_pi_address σ hA _).trans (congrArg Subtype.val (splice_pi_ob _ b)))

/-- The actual full-batch quotient map is the cast forced by garden equality. -/
theorem BatchIso.splice_branch_cast {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (b : GBranch (stSt A.skeleton σ).G.tree) :
    gardenBranchCast (h.splice_garden_eq σ hA) ((h.spliceMolIso σ hA).e b) = b :=
  Subtype.ext ((gardenBranchCast_val _ _).trans (h.spliceMolIso_address σ hA b))

end WaveTurbulence.VineA
