/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineDartAddress
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGroupCode
/-! Forward quotient diagrams after the proved literal ordered normalization. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitSplice_pi`). -/
theorem unitSplice_piMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (v : GBranch G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').M.pi
      (stSt Z.target (transportPrescription Z.iso σ) Mk').hcls (Z.iso.e v) =
    (unitSpliceMolIsoMk Z σ hT hsel).e ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls v) := by
  apply (stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob_inj
  rw [SpMap.ob_pi, unitSpliceMolIso_branch_namesMk, SpMap.ob_pi]
  exact unitBlocks_repC_twistMk Z σ hT hsel v

/-- The forward atom quotient intertwines the actual LF map and actual quotient map. -/
theorem unitSplice_pi (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (v : GBranch G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.pi
      (stSt Z.target (transportPrescription Z.iso σ)).hcls (Z.iso.e v) =
    (unitSpliceMolIso Z σ hsel).e ((stSt G σ).M.pi (stSt G σ).hcls v) :=
  unitSplice_piMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel v

/-- B1b-2 (Mk-general form of `unitSplice_q_diagram`). -/
theorem unitSplice_q_diagramMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    gardenBranchCast (unitSplice_garden_eqMk Z σ hT hsel) ∘
      (stSt Z.target (transportPrescription Z.iso σ) Mk').M.pi
        (stSt Z.target (transportPrescription Z.iso σ) Mk').hcls ∘ Z.iso.e =
      (stSt G σ Mk).M.pi (stSt G σ Mk).hcls := by
  funext v
  exact (congrArg (gardenBranchCast (unitSplice_garden_eqMk Z σ hT hsel)) (unitSplice_piMk Z σ hT hsel v)).trans
    (unitSplice_branch_castMk Z σ hT hsel _)

/-- The requested forward atom diagram, with the literal garden equality cast explicit. -/
theorem unitSplice_q_diagram (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    gardenBranchCast (unitSplice_garden_eq Z σ hsel) ∘
      (stSt Z.target (transportPrescription Z.iso σ)).M.pi
        (stSt Z.target (transportPrescription Z.iso σ)).hcls ∘ Z.iso.e =
      (stSt G σ).M.pi (stSt G σ).hcls := unitSplice_q_diagramMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- The actual inverse old-name map, on exactly its surviving-dart domain. -/
noncomputable def spliceDartQuotient (st : SpState G)
    (x : {x : GardenDart G // ∃ y, st.M.od y = x}) : GardenDart st.G := x.2.choose

/-- The inverse returns the specified original dart. -/
theorem spliceDartQuotient_name (st : SpState G)
    (x : {x : GardenDart G // ∃ y, st.M.od y = x}) :
    st.M.od (spliceDartQuotient st x) = x.1 := x.2.choose_spec

/-- B1b-2 (Mk-general form of `unitSpliceRetainedDart`). -/
noncomputable def unitSpliceRetainedDartMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ Mk).M.od y = x}) :
    {x : GardenDart Z.target // ∃ y, (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od y = x} :=
  ⟨Z.iso.d x.1, (by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨(unitSpliceMolIsoMk Z σ hT hsel).d y,
      (unitSpliceMolIso_dart_namesMk Z σ hT hsel y).trans (congrArg Z.iso.d hy)⟩)⟩

/-- The actual LF dart map restricts to the exact surviving range. -/
noncomputable def unitSpliceRetainedDart (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ).M.od y = x}) :
    {x : GardenDart Z.target // ∃ y, (stSt Z.target (transportPrescription Z.iso σ)).M.od y = x} :=
  unitSpliceRetainedDartMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel x

/-- B1b-2 (Mk-general form of `unitSplice_dartQuotient`). -/
theorem unitSplice_dartQuotientMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ Mk).M.od y = x}) :
    spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ) Mk')
      (unitSpliceRetainedDartMk Z σ hT hsel x) =
      (unitSpliceMolIsoMk Z σ hT hsel).d (spliceDartQuotient (stSt G σ Mk) x) := by
  apply (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od_inj
  rw [spliceDartQuotient_name, unitSpliceMolIso_dart_namesMk, spliceDartQuotient_name]
  rfl

/-- The forward dart quotient intertwines the actual maps on surviving darts. -/
theorem unitSplice_dartQuotient (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ).M.od y = x}) :
    spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ))
      (unitSpliceRetainedDart Z σ hsel x) =
      (unitSpliceMolIso Z σ hsel).d (spliceDartQuotient (stSt G σ) x) :=
  unitSplice_dartQuotientMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel x

/-- B1b-2 (Mk-general form of `unitSplice_d_diagram`). -/
theorem unitSplice_d_diagramMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    gardenDartCast (unitSplice_garden_eqMk Z σ hT hsel) ∘
      spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ) Mk') ∘
        unitSpliceRetainedDartMk Z σ hT hsel = spliceDartQuotient (stSt G σ Mk) := by
  funext x
  exact (congrArg (gardenDartCast (unitSplice_garden_eqMk Z σ hT hsel))
    (unitSplice_dartQuotientMk Z σ hT hsel x)).trans (unitSplice_dart_castMk Z σ hT hsel _)

/-- The requested forward dart diagram, on the exact domain of surviving original darts. -/
theorem unitSplice_d_diagram (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    gardenDartCast (unitSplice_garden_eq Z σ hsel) ∘
      spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ)) ∘
        unitSpliceRetainedDart Z σ hsel = spliceDartQuotient (stSt G σ) :=
  unitSplice_d_diagramMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

end WaveTurbulence.VineA
