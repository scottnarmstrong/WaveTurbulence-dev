/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescription
/-! Canonical extension of the restricted group prescriptions required by R24 D2. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice Represents
variable {w : ℕ} {G H : Garden w}

/-- Extend only for the total S2a API; off-group values are the fixed kind LG. -/
noncomputable def extendGroupPrescription (σ : GroupPrescription G) : Prescription G := by
  classical
  exact fun S => if h : S ∈ maximalGroups G.molecule then σ ⟨S, h⟩ else .LG

/-- Restriction recovers the original finite group prescription exactly. -/
theorem of_extendGroupPrescription (σ : GroupPrescription G) :
    GroupPrescription.ofPrescription (extendGroupPrescription σ) = σ := by
  funext S
  exact dite_eq_left S.2

/-- Canonical extension commutes with actual molecular transport, also off the maximal groups. -/
theorem transport_extendGroupPrescription (F : MolIso G.molecule H.molecule) (σ : GroupPrescription G) :
    transportPrescription F (extendGroupPrescription σ) =
      extendGroupPrescription (transportGroupPrescription F σ) := by
  classical
  funext T
  have hm : F.symm.img T ∈ maximalGroups G.molecule ↔ T ∈ maximalGroups H.molecule :=
    F.symm.maximalGroups_img_iff
  change (if h : F.symm.img T ∈ maximalGroups G.molecule then σ ⟨F.symm.img T, h⟩ else .LG) =
    (if h : T ∈ maximalGroups H.molecule then σ ((groupEquiv F).symm ⟨T, h⟩) else .LG)
  by_cases h : T ∈ maximalGroups H.molecule
  · rw [dite_eq_left (hm.mpr h), dite_eq_left h]
    rfl
  · rw [dite_eq_right (fun hs => h (hm.mp hs)), dite_eq_right h]

end WaveTurbulence.VineA
