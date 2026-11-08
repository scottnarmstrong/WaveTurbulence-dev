/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberUnits
/-! The original upper external port of every actual unit is class-independent. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineA VineB RedSplice Twist Stage1 LFTwist
variable {w p : ℕ} {kind : Bool} {S : Garden w} {ι : Type*}

/-- B1b-2 (Mk-general form of `unit_upper_ne_active`). -/
theorem unit_upper_ne_activeMk (Z : TwistGroupSite S) (σ : Prescription S)
    {Mk : Set (CLVine S)}
    (hsel : ∃ c ∈ vinesV0 S σ Mk, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ Mk) : u.upper ≠ Z.P.lower := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
  intro he
  exact active_lower_not_survivingMk Z σ hsel
    ⟨(stShape (Mole.garden_isMolecule S) σ Mk).hinge (unitBlkMk_disj _ σ Mk) j,
      ((stShape (Mole.garden_isMolecule S) σ Mk).br_hinge (unitBlkMk_disj _ σ Mk) j).trans he⟩

/-- An actual unit upper joint is never the selected LF lower joint. -/
theorem unit_upper_ne_active (Z : TwistGroupSite S) (σ : Prescription S)
    (hsel : ∃ c ∈ vinesV0 S σ, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ) : u.upper ≠ Z.P.lower := unit_upper_ne_activeMk Z σ hsel hu

/-- B1b-2 (Mk-general form of `unitImage_excluded`). -/
theorem unitImage_excludedMk (Z : TwistGroupSite S) (σ : Prescription S)
    {Mk : Set (CLVine S)}
    (hsel : ∃ c ∈ vinesV0 S σ Mk, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ Mk) :
    (regionOf (unitImage Z u (unitBlocks_goodMk Z σ hsel hu))).excluded = (regionOf u).excluded := by
  let R := regionOf u
  let R' := regionOf (unitImage Z u (unitBlocks_goodMk Z σ hsel hu))
  have h1 : R'.excluded.succ ∉ Mole.internalPositions Z.target (Z.iso.img u.atoms) (Z.iso.e u.upper) :=
    fun h => ((R'.upper R'.excluded).mp h) rfl
  have h2 : R'.excluded.succ ∉ Mole.internalPositions S u.atoms u.upper := fun h =>
    h1 ((internalPositions_twist_other S Z.P u.atoms u.upper (unit_upper_ne_activeMk Z σ hsel hu) _).mpr h)
  by_contra hne
  exact h2 ((R.upper R'.excluded).mpr hne)

/-- The chosen region's excluded port is characterized by the unchanged internal positions. -/
theorem unitImage_excluded (Z : TwistGroupSite S) (σ : Prescription S)
    (hsel : ∃ c ∈ vinesV0 S σ, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ) :
    (regionOf (unitImage Z u (unitBlocks_good Z σ hsel hu))).excluded = (regionOf u).excluded :=
  unitImage_excludedMk Z σ hsel hu

/-- B1b-2 (Mk-general form of `operation_unit_excluded`). -/
theorem operation_unit_excludedMk {A : FamilyReconstruction w ι} {i : ι}
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ Mk)
    (v : CLBlock op.output.skeleton) (hv : v.atoms = (operationMolIso op).img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      have huv : v = u := clBlock_eq_of_atoms (hv.trans (Finset.image_id))
      exact congrArg (fun u => (regionOf u).excluded) huv
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ Mk, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      have huv : v = unitImage Z u (unitBlocks_goodMk Z σ hs hu) := clBlock_eq_of_atoms hv
      exact (congrArg (fun u => (regionOf u).excluded) huv).trans (unitImage_excludedMk Z σ hs hu)

/-- Each fine operation preserves the external upper port of every unit. -/
theorem operation_unit_excluded {A : FamilyReconstruction w ι} {i : ι}
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ)
    (v : CLBlock op.output.skeleton) (hv : v.atoms = (operationMolIso op).img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded :=
  operation_unit_excludedMk σ hA op (Stage1Mk.markTransported_empty _) hu v hv

/-- B1b-2 (Mk-general form of `batch_unit_excluded`). -/
theorem batch_unit_excludedMk {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ Mk)
    (v : CLBlock B.skeleton) (hv : v.atoms = F.img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    have huv : v = u := clBlock_eq_of_atoms (hv.trans Finset.image_id)
    exact congrArg (fun u => (regionOf u).excluded) huv
  | skip _ _ ih => exact ih σ hT hA hu v hv
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    obtain ⟨t, ht, hta, _, _⟩ := operation_units_jointsMk hA op h1 hu
    have hvt : v.atoms = J.img t.atoms := by
      rw [hta]
      exact hv.trans (molIsoTrans_img (operationMolIso op) J u.atoms)
    exact (ih (transportPrescription (operationMolIso op) σ) h2 (isV0Fam_operationMk hA op h1) ht v hvt).trans
      (operation_unit_excludedMk σ hA op h1 hu t hta)

/-- Every actual batch preserves the excluded port under the actual whole-unit identification. -/
theorem batch_unit_excluded {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ)
    (v : CLBlock B.skeleton) (hv : v.atoms = F.img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded :=
  batch_unit_excludedMk h σ (Stage1Mk.markTransported_empty F) hA hu v hv

end WaveTurbulence.VineAlign
