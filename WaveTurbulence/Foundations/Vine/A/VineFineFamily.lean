/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.Vine.A.VineSelectedTransport
/-! Exact selected-family states and their preservation under a skeleton
unit twist. The predicate uses the actual V0 carrier of the prescription. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w} {ι : Type*}

/-- The family enumerates exactly the core vines of the selected V0 carrier.  B1a: with the trailing marked vine set
`Mk` (default `∅`) the carrier is the unmarked `𝒱₀♮ = vinesV0 G σ Mk`. -/
def IsV0Fam (F : CoreFamily G ι) (σ : Prescription G) (Mk : Set (CLVine G) := ∅) : Prop :=
  (∀ i, familyVine F i ∈ vinesV0 G σ Mk) ∧
  (∀ c ∈ vinesV0 G σ Mk, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
    ∃ i, F.atoms i = c.atoms)

/-- B1b (Mk-general form of `fineState_isV0Fam`). -/
theorem fineState_isV0FamMk {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton) {Mk : Set (Stage1.CLVine _)} :
    IsV0Fam (Mk := Mk) (A.fineState (Mk := Mk) σ).family σ := by
  constructor
  · intro i
    have he : familyVine (A.fineState (Mk := Mk) σ).family i = i.1 := clVine_eq_of_atoms rfl
    exact he ▸ i.2.1
  · intro c hc hcore
    exact ⟨⟨c, hc, hcore⟩, rfl⟩

/-- The canonical fine state has the exact selected family. -/
theorem fineState_isV0Fam {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton) :
    IsV0Fam (A.fineState σ).family σ := fineState_isV0FamMk (Mk := ∅) A σ

/-- The actual twist site of a selected family member. -/
noncomputable def selectedMemberSite {F : CoreFamily G ι} {σ : Prescription G} {Mk : Set (CLVine G)}
    (hF : IsV0Fam F σ Mk) (i : ι) : TwistGroupSite G where
  P := F.placement i
  S0 := F.atoms i
  a0 := F.upper i
  hB := (F.core i).1.1
  hCL := (F.core i).2.1
  hP := F.designated i
  Sg := (hF.1 i).2.choose
  hSg := (hF.1 i).2.choose_spec.1
  hS0 := (hF.1 i).2.choose_spec.2.1

/-- A selected unit twist preserves completeness of the selected core family. -/
theorem isV0Fam_twist {F : CoreFamily G ι} {σ : Prescription G}
    (hF : IsV0Fam F σ) (i : ι) :
    IsV0Fam (F.twist i) (transportPrescription (selectedMemberSite hF i).iso σ) := by
  let Z := selectedMemberSite hF i
  constructor
  · intro j
    obtain ⟨c', hc', ha, _, _⟩ := vinesV0_image Z σ (hF.1 j)
    have he : c' = familyVine (F.twist i) j := clVine_eq_of_atoms ha
    exact he ▸ hc'
  · intro c' hc' ⟨X, hX⟩
    obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimage Z σ hc'
    by_cases hat : c.atoms = F.atoms i
    · refine ⟨i, ?_⟩
      rw [ha, hat]
      rfl
    · obtain ⟨S, hS, hi, _⟩ := hc.1
      have hsep := Z.sep_of_ing hS hi hat
      have hcore : IsCoreCLVine G X c.atoms c.upper c.lower :=
        Z.core_pull hsep (by rw [ha, hu, hl] at hX; exact hX)
      obtain ⟨j, hj⟩ := hF.2 c hc ⟨X, hcore⟩
      refine ⟨j, ?_⟩
      rw [ha, ← hj]
      rfl

/-- B1b (R11): a selected unit twist preserves completeness of the unmarked selected core family, for marked sets
carried by the twist. -/
theorem isV0Fam_twistMk {F : CoreFamily G ι} {σ : Prescription G} {Mk : Set (CLVine G)}
    (hF : IsV0Fam F σ Mk) (i : ι) {Mk' : Set (CLVine (selectedMemberSite hF i).target)}
    (hT : Stage1Mk.MarkTransported (selectedMemberSite hF i).iso Mk Mk') :
    IsV0Fam (F.twist i) (transportPrescription (selectedMemberSite hF i).iso σ) Mk' := by
  let Z := selectedMemberSite hF i
  constructor
  · intro j
    obtain ⟨c', hc', ha, _, _⟩ := vinesV0_imageMk Z σ hT (hF.1 j)
    have he : c' = familyVine (F.twist i) j := clVine_eq_of_atoms ha
    exact he ▸ hc'
  · intro c' hc' ⟨X, hX⟩
    obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimageMk Z σ hT hc'
    by_cases hat : c.atoms = F.atoms i
    · refine ⟨i, ?_⟩
      rw [ha, hat]
      rfl
    · obtain ⟨S, hS, hi, _⟩ := hc.1
      have hsep := Z.sep_of_ing hS hi hat
      have hcore : IsCoreCLVine G X c.atoms c.upper c.lower :=
        Z.core_pull hsep (by rw [ha, hu, hl] at hX; exact hX)
      obtain ⟨j, hj⟩ := hF.2 c hc ⟨X, hcore⟩
      refine ⟨j, ?_⟩
      rw [ha, ← hj]
      rfl

end WaveTurbulence.VineA
