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

/-- B1b-2 (Mk-general form of `operation_splice_garden_eq`). -/
theorem operation_splice_garden_eqMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk') :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').G = (stSt A.skeleton σ Mk).G := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      exact congrArg (fun τ => (stSt A.skeleton τ Mk).G) (transportPrescription_refl σ)
    · exact unitSplice_garden_eqMk (selectedMemberSite hA i) σ hT ⟨familyVine A.family i, hA.1 i, rfl⟩

/-- Every actual fine operation leaves the literal normalized garden unchanged. -/
theorem operation_splice_garden_eq {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).G = (stSt A.skeleton σ).G :=
  operation_splice_garden_eqMk hA op (Stage1Mk.markTransported_empty _)

/-- B1b-2 (Mk-general form of `BatchIso.splice_garden_eq`). -/
theorem BatchIso.splice_garden_eqMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)}
    {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) :
    (stSt B.skeleton (transportPrescription F σ) Mk').G = (stSt A.skeleton σ Mk).G := by
  induction h with
  | nil =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact congrArg (fun τ => (stSt _ τ Mk).G) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hT hA
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih _ h2 (isV0Fam_operationMk hA op h1)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_garden_eqMk hA op h1)

/-- Every actual fine batch has exactly the same ordered spliced garden. -/
theorem BatchIso.splice_garden_eq {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    (stSt B.skeleton (transportPrescription F σ)).G = (stSt A.skeleton σ).G :=
  h.splice_garden_eqMk σ (Stage1Mk.markTransported_empty F) hA

/-- B1b-2 (Mk-general form of `operation_splice_pi_address`). -/
theorem operation_splice_pi_addressMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (v : GBranch A.skeleton.tree) :
    ((stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').M.pi
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').hcls ((operationMolIso op).e v)).1 =
      ((stSt A.skeleton σ Mk).M.pi (stSt A.skeleton σ Mk).hcls v).1 := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      exact congrArg (fun τ => ((stSt A.skeleton τ Mk).M.pi (stSt A.skeleton τ Mk).hcls v).1)
        (transportPrescription_refl σ)
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ Mk, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      exact (congrArg Subtype.val (unitSplice_piMk Z σ hT hs v)).trans (unitSpliceMolIso_addressMk Z σ hT hs _)

/-- Quotient atom addresses commute with one actual fine operation. -/
theorem operation_splice_pi_address {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (v : GBranch A.skeleton.tree) :
    ((stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M.pi
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).hcls ((operationMolIso op).e v)).1 =
      ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls v).1 :=
  operation_splice_pi_addressMk hA op (Stage1Mk.markTransported_empty _) v

/-- B1b-2 (Mk-general form of `BatchIso.splice_pi_address`). -/
theorem BatchIso.splice_pi_addressMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)}
    {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (v : GBranch A.skeleton.tree) :
    ((stSt B.skeleton (transportPrescription F σ) Mk').M.pi
      (stSt B.skeleton (transportPrescription F σ) Mk').hcls (F.e v)).1 =
      ((stSt A.skeleton σ Mk).M.pi (stSt A.skeleton σ Mk).hcls v).1 := by
  induction h with
  | nil =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    change ((stSt _ (transportPrescription (molIsoRefl _) σ) Mk).M.pi _ v).1 = _
    rw [transportPrescription_refl]
  | skip _ _ ih => exact ih σ hT hA v
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih _ h2 (isV0Fam_operationMk hA op h1) ((operationMolIso op).e v)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_splice_pi_addressMk hA op h1 v)

/-- The forward quotient diagram in literal addresses for a full actual batch. -/
theorem BatchIso.splice_pi_address {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (v : GBranch A.skeleton.tree) :
    ((stSt B.skeleton (transportPrescription F σ)).M.pi
      (stSt B.skeleton (transportPrescription F σ)).hcls (F.e v)).1 =
      ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls v).1 :=
  h.splice_pi_addressMk σ (Stage1Mk.markTransported_empty F) hA v

/-- The quotient reverses the old-name map on every surviving branch. -/
theorem splice_pi_ob {G : Garden w} (st : SpState G) (b : GBranch st.G.tree) : st.M.pi st.hcls (st.M.ob b) = b := by
  apply st.M.ob_inj
  exact (st.M.ob_pi st.hcls _).trans (splice_old_branch_fixed st b)

/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso_address`). -/
theorem BatchIso.spliceMolIso_addressMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)}
    {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (b : GBranch (stSt A.skeleton σ Mk).G.tree) : ((h.spliceMolIsoMk σ hT hA).e b).1 = b.1 := by
  have hp := h.splice_piMk σ hT hA ((stSt A.skeleton σ Mk).M.ob b)
  rw [splice_pi_ob] at hp
  exact (congrArg Subtype.val hp).trans
    ((h.splice_pi_addressMk σ hT hA _).trans (congrArg Subtype.val (splice_pi_ob _ b)))

/-- The actual full-batch quotient map fixes every literal branch address. -/
theorem BatchIso.spliceMolIso_address {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (b : GBranch (stSt A.skeleton σ).G.tree) : ((h.spliceMolIso σ hA).e b).1 = b.1 :=
  h.spliceMolIso_addressMk σ (Stage1Mk.markTransported_empty F) hA b

/-- B1b-2 (Mk-general form of `BatchIso.splice_branch_cast`). -/
theorem BatchIso.splice_branch_castMk {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)}
    {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (b : GBranch (stSt A.skeleton σ Mk).G.tree) :
    gardenBranchCast (h.splice_garden_eqMk σ hT hA) ((h.spliceMolIsoMk σ hT hA).e b) = b :=
  Subtype.ext ((gardenBranchCast_val _ _).trans (h.spliceMolIso_addressMk σ hT hA b))

/-- The actual full-batch quotient map is the cast forced by garden equality. -/
theorem BatchIso.splice_branch_cast {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (b : GBranch (stSt A.skeleton σ).G.tree) :
    gardenBranchCast (h.splice_garden_eq σ hA) ((h.spliceMolIso σ hA).e b) = b :=
  h.splice_branch_castMk σ (Stage1Mk.markTransported_empty F) hA b

end WaveTurbulence.VineA
