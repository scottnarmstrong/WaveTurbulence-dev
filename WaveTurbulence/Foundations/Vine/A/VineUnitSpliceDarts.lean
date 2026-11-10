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

/-- B1b-2 (Mk-general form of `unitSpliceLPLeafEquiv`). -/
noncomputable def unitSpliceLPLeafEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    GardenLPLeaf (stSt G σ Mk).G ≃ GardenLPLeaf (stSt Z.target (transportPrescription Z.iso σ) Mk').G :=
  (unitSpliceLeafEquivMk Z σ hT hsel).subtypeEquiv (fun q => (unitSpliceLP_profile_iffMk Z σ hT hsel q).symm)

/-- B1b-2 (Mk-general form of `unitSplicePCEquiv`). -/
noncomputable def unitSplicePCEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    {c : GBranch (stSt G σ Mk).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree // c.1.2 ≠ []} :=
  (unitSpliceMolIsoMk Z σ hT hsel).e.subtypeEquiv
    (fun c => (not_congr (unitSpliceMolIso_branch_rootMk Z σ hT hsel c)).symm)

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

end WaveTurbulence.VineA
