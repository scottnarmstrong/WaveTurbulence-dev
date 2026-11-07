/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGroupKeyDiagrams
/-! Covariance of R83's unique normalized HV and DV choices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}
variable (Z : TwistGroupSite G) (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0)
include hsel

/-- The unique least HV candidate is carried by the actual triple bijection. -/
theorem hvGroupLeast_twist (hS : SingleHVGroup G S) :
    hvCandidateEquiv Z.iso S (hvGroupKey_existsUnique hS).choose =
      (hvGroupKey_existsUnique (hS.map Z.iso)).choose := by
  apply (hvGroupKey_existsUnique (hS.map Z.iso)).choose_spec.2
  intro u
  obtain ⟨t, rfl⟩ := (hvCandidateEquiv Z.iso S).surjective u
  rw [hvGroupKey_twist Z hsel, hvGroupKey_twist Z hsel]
  exact (hvGroupKey_existsUnique hS).choose_spec.1 t

/-- Single-HV selection commutes with actual LF, including its exact success domain. -/
theorem hvGroupPick_twist :
    hvGroupPick Z.target (Z.iso.img S) = (hvGroupPick G S).map (hvTripleEquiv Z.iso) := by
  classical
  by_cases hS : SingleHVGroup G S
  · have hT := hS.map Z.iso
    unfold hvGroupPick
    rw [dite_eq_left hS, dite_eq_left hT]
    exact congrArg (fun t => some t.1) (hvGroupLeast_twist Z hsel hS).symm
  · have hT : ¬ SingleHVGroup Z.target (Z.iso.img S) := by
      intro h
      have hh := h.map Z.iso.symm
      rw [Z.iso.img_img_symm] at hh
      exact hS hh
    unfold hvGroupPick
    rw [dite_eq_right hS, dite_eq_right hT]
    rfl

/-- The unique least DV candidate is carried with its entire selected support. -/
theorem dvGroupLeast_twist (hS : PureDVGroup G S) :
    dvCandidateEquiv Z.iso S (dvGroupKey_existsUnique hS).choose =
      (dvGroupKey_existsUnique (hS.map Z.iso)).choose := by
  apply (dvGroupKey_existsUnique (hS.map Z.iso)).choose_spec.2
  intro u
  obtain ⟨t, rfl⟩ := (dvCandidateEquiv Z.iso S).surjective u
  change dvGroupKey Z.target (dvTripleEquiv Z.iso _) ≤ dvGroupKey Z.target (dvTripleEquiv Z.iso t.1)
  rw [dvGroupKey_twist Z hsel, dvGroupKey_twist Z hsel]
  exact (dvGroupKey_existsUnique hS).choose_spec.1 t

/-- Pure-DV selection commutes with actual LF, including its exact success domain. -/
theorem dvGroupPick_twist :
    dvGroupPick Z.target (Z.iso.img S) = (dvGroupPick G S).map (dvTripleEquiv Z.iso) := by
  classical
  by_cases hS : PureDVGroup G S
  · have hT := hS.map Z.iso
    unfold dvGroupPick
    rw [dite_eq_left hS, dite_eq_left hT]
    exact congrArg (fun t => some t.1) (dvGroupLeast_twist Z hsel hS).symm
  · have hT : ¬ PureDVGroup Z.target (Z.iso.img S) := by
      intro h
      have hh := h.map Z.iso.symm
      rw [Z.iso.img_img_symm] at hh
      exact hS hh
    unfold dvGroupPick
    rw [dite_eq_right hS, dite_eq_right hT]
    rfl

end WaveTurbulence.VineA
