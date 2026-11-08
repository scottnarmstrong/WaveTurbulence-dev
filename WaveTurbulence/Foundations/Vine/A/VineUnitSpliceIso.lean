/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineQuotientIso
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage
/-! Actual selected unit LF twists induce directed molecular isomorphisms
of the actual simultaneous splices, including internal vines of larger units. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitSpliceMolIso`). -/
noncomputable def unitSpliceMolIsoMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    MolIso (stSt G σ Mk).G.molecule
      (stSt Z.target (transportPrescription Z.iso σ) Mk').G.molecule :=
  quotientMolIso Z.iso (unitBlocks_cls_twistMk Z σ hT hsel)
    (stSt G σ Mk).M
    (stSt Z.target (transportPrescription Z.iso σ) Mk').M

/-- The actual molecular map between the two actual selected simultaneous splices. -/
noncomputable def unitSpliceMolIso (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    MolIso (stSt G σ).G.molecule
      (stSt Z.target (transportPrescription Z.iso σ)).G.molecule :=
  unitSpliceMolIsoMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_branch_names`). -/
theorem unitSpliceMolIso_branch_namesMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (c : GBranch (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob
      ((unitSpliceMolIsoMk Z σ hT hsel).e c) = Z.iso.e ((stSt G σ Mk).M.ob c) :=
  quotientBranchEquiv_comm Z.iso (unitBlocks_cls_twistMk Z σ hT hsel) _ _ c

/-- The induced actual splice atom map commutes with the original LF atom map. -/
theorem unitSpliceMolIso_branch_names (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (c : GBranch (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.ob
      ((unitSpliceMolIso Z σ hsel).e c) = Z.iso.e ((stSt G σ).M.ob c) :=
  unitSpliceMolIso_branch_namesMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_dart_names`). -/
theorem unitSpliceMolIso_dart_namesMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (x : GardenDart (stSt G σ Mk).G) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od
      ((unitSpliceMolIsoMk Z σ hT hsel).d x) = Z.iso.d ((stSt G σ Mk).M.od x) :=
  quotientDartEquiv_comm Z.iso (unitBlocks_cls_twistMk Z σ hT hsel) _ _ x

/-- The induced actual splice dart map commutes with the original LF dart map. -/
theorem unitSpliceMolIso_dart_names (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (x : GardenDart (stSt G σ).G) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.od
      ((unitSpliceMolIso Z σ hsel).d x) = Z.iso.d ((stSt G σ).M.od x) :=
  unitSpliceMolIso_dart_namesMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel x

/-- B1b-2 (Mk-general form of `active_lower_not_surviving`). -/
theorem active_lower_not_survivingMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    ¬ ∃ c, (stSt G σ Mk).M.ob c = Z.P.lower := by
  intro h
  obtain ⟨u, _, hu, hne⟩ := active_lower_mergedMk Z σ hsel
  have hr := ((stSt G σ Mk).M.ob_range Z.P.lower).mp h
  change (stSt G σ Mk).cls Z.P.lower = some u.upper at hu
  rw [hu] at hr
  rcases hr with h | h
  · cases h
  · exact hne (Option.some.inj h)

/-- The sign-changing active lower node is absent from the actual retained branch carrier. -/
theorem active_lower_not_surviving (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ¬ ∃ c, (stSt G σ).M.ob c = Z.P.lower := active_lower_not_survivingMk Z σ hsel

end WaveTurbulence.VineA
