/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSurvivingDarts
/-! The actual selected-splice dart map preserves PC/LP tags and agrees
with the full node map on the exact bond-momentum arguments of the kernel. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Mole WaveTurbulence.LGSpine
variable {w d : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitSpliceLP_profile_iff`). -/
theorem unitSpliceLP_profile_iffMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    ((stSt Z.target (transportPrescription Z.iso σ) Mk').G.mark (unitSpliceLeafEquivMk Z σ hT hsel q) = none ∧
      (unitSpliceLeafEquivMk Z σ hT hsel q).1.2 ≠ [] ∧
      ((stSt Z.target (transportPrescription Z.iso σ) Mk').G.pair (unitSpliceLeafEquivMk Z σ hT hsel q)).1.2 ≠ []) ↔
    ((stSt G σ Mk).G.mark q = none ∧ q.1.2 ≠ [] ∧ ((stSt G σ Mk).G.pair q).1.2 ≠ []) := by
  have hm := Iff.of_eq (congrArg (fun x : Option MarkTag => x = none) (unitSpliceLeafEquiv_markMk Z σ hT hsel q))
  have hr := not_congr (unitSpliceLeafEquiv_rootMk Z σ hT hsel q)
  have hp := (Iff.of_eq (congrArg (fun l : GLeaf (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree => l.1.2 ≠ [])
    (unitSpliceLeafEquiv_pairMk Z σ hT hsel q).symm)).trans
      (not_congr (unitSpliceLeafEquiv_rootMk Z σ hT hsel ((stSt G σ Mk).G.pair q)))
  exact and_congr hm (and_congr hr hp)

/-- The actual full leaf map preserves LP typing in both directions. -/
theorem unitSpliceLP_profile_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    ((stSt Z.target (transportPrescription Z.iso σ)).G.mark (unitSpliceLeafEquiv Z σ hsel q) = none ∧
      (unitSpliceLeafEquiv Z σ hsel q).1.2 ≠ [] ∧
      ((stSt Z.target (transportPrescription Z.iso σ)).G.pair (unitSpliceLeafEquiv Z σ hsel q)).1.2 ≠ []) ↔
    ((stSt G σ).G.mark q = none ∧ q.1.2 ≠ [] ∧ ((stSt G σ).G.pair q).1.2 ≠ []) :=
  unitSpliceLP_profile_iffMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

/-- B1b-2 (Mk-general form of `unitSpliceLPLeafEquiv`). -/
noncomputable def unitSpliceLPLeafEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    GardenLPLeaf (stSt G σ Mk).G ≃ GardenLPLeaf (stSt Z.target (transportPrescription Z.iso σ) Mk').G :=
  (unitSpliceLeafEquivMk Z σ hT hsel).subtypeEquiv (fun q => (unitSpliceLP_profile_iffMk Z σ hT hsel q).symm)

/-- The actual LP-leaf carrier correspondence. -/
noncomputable def unitSpliceLPLeafEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    GardenLPLeaf (stSt G σ).G ≃ GardenLPLeaf (stSt Z.target (transportPrescription Z.iso σ)).G :=
  unitSpliceLPLeafEquivMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitSplicePCEquiv`). -/
noncomputable def unitSplicePCEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    {c : GBranch (stSt G σ Mk).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree // c.1.2 ≠ []} :=
  (unitSpliceMolIsoMk Z σ hT hsel).e.subtypeEquiv
    (fun c => (not_congr (unitSpliceMolIso_branch_rootMk Z σ hT hsel c)).symm)

/-- The actual nonroot-branch carrier correspondence. -/
noncomputable def unitSplicePCEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    {c : GBranch (stSt G σ).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree // c.1.2 ≠ []} :=
  unitSplicePCEquivMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_pc`). -/
theorem unitSpliceMolIso_pcMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (c : {c : GBranch (stSt G σ Mk).G.tree // c.1.2 ≠ []}) (side : Bool) :
    (unitSpliceMolIsoMk Z σ hT hsel).d (.inl (c, side)) = .inl (unitSplicePCEquivMk Z σ hT hsel c, side) := by
  apply (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od_inj
  have he : naiveDartEquiv G Z.P (.inl (spliceOldPC (stSt G σ Mk) c, side)) =
      .inl (spliceOldPC (stSt Z.target (transportPrescription Z.iso σ) Mk') (unitSplicePCEquivMk Z σ hT hsel c), side) := by
    apply congrArg (fun b => Sum.inl (b, side))
    apply Subtype.ext
    exact (unitSpliceMolIso_branch_namesMk Z σ hT hsel c.1).symm
  exact (unitSpliceMolIso_surviving_dart_namesMk Z σ hT hsel (.inl (c, side))).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks G σ Mk)).pc c side)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).pc _ side).symm))

/-- Actual surviving PC darts retain their side and follow the actual branch map. -/
theorem unitSpliceMolIso_pc (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (c : {c : GBranch (stSt G σ).G.tree // c.1.2 ≠ []}) (side : Bool) :
    (unitSpliceMolIso Z σ hsel).d (.inl (c, side)) = .inl (unitSplicePCEquiv Z σ hsel c, side) :=
  unitSpliceMolIso_pcMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel c side

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_lp`). -/
theorem unitSpliceMolIso_lpMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GardenLPLeaf (stSt G σ Mk).G) :
    (unitSpliceMolIsoMk Z σ hT hsel).d (.inr q) = .inr (unitSpliceLPLeafEquivMk Z σ hT hsel q) := by
  apply (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od_inj
  have he : naiveDartEquiv G Z.P (.inr ((spliceFoldLeafTrace (unitBlocks G σ Mk)).lp q)) =
      .inr ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).lp
        (unitSpliceLPLeafEquivMk Z σ hT hsel q)) := by
    apply congrArg Sum.inr
    apply Subtype.ext
    exact (unitSpliceLeafEquiv_namesMk Z σ hT hsel q.1).symm
  exact (unitSpliceMolIso_surviving_dart_namesMk Z σ hT hsel (.inr q)).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks G σ Mk)).lp q)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).lp _).symm))

/-- Actual surviving LP darts follow the full actual leaf map. -/
theorem unitSpliceMolIso_lp (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GardenLPLeaf (stSt G σ).G) :
    (unitSpliceMolIso Z σ hsel).d (.inr q) = .inr (unitSpliceLPLeafEquiv Z σ hsel q) :=
  unitSpliceMolIso_lpMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

/-- B1b-2 (Mk-general form of `unitSplice_bondIndex`). -/
theorem unitSplice_bondIndexMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (z : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → (Fin d → ℤ))
    (x : GardenDart (stSt G σ Mk).G) :
    bondIndex (stSt G σ Mk).G (z ∘ unitSpliceNodeEquivMk Z σ hT hsel) x =
      bondIndex (stSt Z.target (transportPrescription Z.iso σ) Mk').G z ((unitSpliceMolIsoMk Z σ hT hsel).d x) := by
  cases x with
  | inl c =>
    obtain ⟨c, side⟩ := c
    rw [unitSpliceMolIso_pcMk]
    exact congrArg z (unitSpliceNodeEquiv_branchMk Z σ hT hsel c.1)
  | inr q =>
    rw [unitSpliceMolIso_lpMk]
    exact congrArg z (unitSpliceNodeEquiv_leafMk Z σ hT hsel q.1)

/-- Exact bond-momentum arguments commute with the actual full node and dart maps. -/
theorem unitSplice_bondIndex (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ))
    (x : GardenDart (stSt G σ).G) :
    bondIndex (stSt G σ).G (z ∘ unitSpliceNodeEquiv Z σ hsel) x =
      bondIndex (stSt Z.target (transportPrescription Z.iso σ)).G z ((unitSpliceMolIso Z σ hsel).d x) :=
  unitSplice_bondIndexMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel z x

end WaveTurbulence.VineA
