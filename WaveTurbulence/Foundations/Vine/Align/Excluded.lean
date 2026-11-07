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

/-- An actual unit upper joint is never the selected LF lower joint. -/
theorem unit_upper_ne_active (Z : TwistGroupSite S) (σ : Prescription S)
    (hsel : ∃ c ∈ vinesV0 S σ, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ) : u.upper ≠ Z.P.lower := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
  intro he
  exact active_lower_not_surviving Z σ hsel
    ⟨(stShape (Mole.garden_isMolecule S) σ).hinge (unitBlk_disj _ σ) j,
      ((stShape (Mole.garden_isMolecule S) σ).br_hinge (unitBlk_disj _ σ) j).trans he⟩

/-- The chosen region's excluded port is characterized by the unchanged internal positions. -/
theorem unitImage_excluded (Z : TwistGroupSite S) (σ : Prescription S)
    (hsel : ∃ c ∈ vinesV0 S σ, c.atoms = Z.S0)
    {u : CLBlock S} (hu : u ∈ unitBlocks S σ) :
    (regionOf (unitImage Z u (unitBlocks_good Z σ hsel hu))).excluded = (regionOf u).excluded := by
  let R := regionOf u
  let R' := regionOf (unitImage Z u (unitBlocks_good Z σ hsel hu))
  have h1 : R'.excluded.succ ∉ Mole.internalPositions Z.target (Z.iso.img u.atoms) (Z.iso.e u.upper) :=
    fun h => ((R'.upper R'.excluded).mp h) rfl
  have h2 : R'.excluded.succ ∉ Mole.internalPositions S u.atoms u.upper := fun h =>
    h1 ((internalPositions_twist_other S Z.P u.atoms u.upper (unit_upper_ne_active Z σ hsel hu) _).mpr h)
  by_contra hne
  exact h2 ((R.upper R'.excluded).mpr hne)

/-- Each fine operation preserves the external upper port of every unit. -/
theorem operation_unit_excluded {A : FamilyReconstruction w ι} {i : ι}
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ)
    (v : CLBlock op.output.skeleton) (hv : v.atoms = (operationMolIso op).img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · have huv : v = u := clBlock_eq_of_atoms (hv.trans (Finset.image_id))
      exact congrArg (fun u => (regionOf u).excluded) huv
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      have huv : v = unitImage Z u (unitBlocks_good Z σ hs hu) := clBlock_eq_of_atoms hv
      exact (congrArg (fun u => (regionOf u).excluded) huv).trans (unitImage_excluded Z σ hs hu)

/-- Every actual batch preserves the excluded port under the actual whole-unit identification. -/
theorem batch_unit_excluded {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ)
    (v : CLBlock B.skeleton) (hv : v.atoms = F.img u.atoms) :
    (regionOf v).excluded = (regionOf u).excluded := by
  induction h with
  | nil A =>
    have huv : v = u := clBlock_eq_of_atoms (hv.trans Finset.image_id)
    exact congrArg (fun u => (regionOf u).excluded) huv
  | skip _ _ ih => exact ih σ hA hu v hv
  | @apply L A B i op J h ih =>
    obtain ⟨t, ht, hta, _, _⟩ := operation_units_joints hA op hu
    have hvt : v.atoms = J.img t.atoms := by
      rw [hta]
      exact hv.trans (molIsoTrans_img (operationMolIso op) J u.atoms)
    exact (ih (transportPrescription (operationMolIso op) σ) (isV0Fam_operation hA op) ht v hvt).trans
      (operation_unit_excluded σ hA op hu t hta)

end WaveTurbulence.VineAlign
