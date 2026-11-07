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

/-- The forward atom quotient intertwines the actual LF map and actual quotient map. -/
theorem unitSplice_pi (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (v : GBranch G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.pi
      (stSt Z.target (transportPrescription Z.iso σ)).hcls (Z.iso.e v) =
    (unitSpliceMolIso Z σ hsel).e ((stSt G σ).M.pi (stSt G σ).hcls v) := by
  apply (stSt Z.target (transportPrescription Z.iso σ)).M.ob_inj
  rw [SpMap.ob_pi, unitSpliceMolIso_branch_names, SpMap.ob_pi]
  exact unitBlocks_repC_twist Z σ hsel v

/-- The requested forward atom diagram, with the literal garden equality cast explicit. -/
theorem unitSplice_q_diagram (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    gardenBranchCast (unitSplice_garden_eq Z σ hsel) ∘
      (stSt Z.target (transportPrescription Z.iso σ)).M.pi
        (stSt Z.target (transportPrescription Z.iso σ)).hcls ∘ Z.iso.e =
      (stSt G σ).M.pi (stSt G σ).hcls := by
  funext v
  exact (congrArg (gardenBranchCast (unitSplice_garden_eq Z σ hsel)) (unitSplice_pi Z σ hsel v)).trans
    (unitSplice_branch_cast Z σ hsel _)

/-- The actual inverse old-name map, on exactly its surviving-dart domain. -/
noncomputable def spliceDartQuotient (st : SpState G)
    (x : {x : GardenDart G // ∃ y, st.M.od y = x}) : GardenDart st.G := x.2.choose

/-- The inverse returns the specified original dart. -/
theorem spliceDartQuotient_name (st : SpState G)
    (x : {x : GardenDart G // ∃ y, st.M.od y = x}) :
    st.M.od (spliceDartQuotient st x) = x.1 := x.2.choose_spec

/-- The actual LF dart map restricts to the exact surviving range. -/
noncomputable def unitSpliceRetainedDart (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ).M.od y = x}) :
    {x : GardenDart Z.target // ∃ y, (stSt Z.target (transportPrescription Z.iso σ)).M.od y = x} :=
  ⟨Z.iso.d x.1, (by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨(unitSpliceMolIso Z σ hsel).d y,
      (unitSpliceMolIso_dart_names Z σ hsel y).trans (congrArg Z.iso.d hy)⟩)⟩

/-- The forward dart quotient intertwines the actual maps on surviving darts. -/
theorem unitSplice_dartQuotient (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (x : {x : GardenDart G // ∃ y, (stSt G σ).M.od y = x}) :
    spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ))
      (unitSpliceRetainedDart Z σ hsel x) =
      (unitSpliceMolIso Z σ hsel).d (spliceDartQuotient (stSt G σ) x) := by
  apply (stSt Z.target (transportPrescription Z.iso σ)).M.od_inj
  rw [spliceDartQuotient_name, unitSpliceMolIso_dart_names, spliceDartQuotient_name]
  rfl

/-- The requested forward dart diagram, on the exact domain of surviving original darts. -/
theorem unitSplice_d_diagram (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    gardenDartCast (unitSplice_garden_eq Z σ hsel) ∘
      spliceDartQuotient (stSt Z.target (transportPrescription Z.iso σ)) ∘
        unitSpliceRetainedDart Z σ hsel = spliceDartQuotient (stSt G σ) := by
  funext x
  exact (congrArg (gardenDartCast (unitSplice_garden_eq Z σ hsel))
    (unitSplice_dartQuotient Z σ hsel x)).trans (unitSplice_dart_cast Z σ hsel _)

end WaveTurbulence.VineA
