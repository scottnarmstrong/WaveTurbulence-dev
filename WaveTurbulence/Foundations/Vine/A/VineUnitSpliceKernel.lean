/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceKernelFactors
/-! Equality of the literal normalized spliced kernels under the actual
selected-splice correspondence and transported concrete kernel data. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w d : ℕ} {G H : Garden w}

/-- An actual garden molecular isomorphism preserves the number of branching nodes. -/
theorem molIso_garden_order (F : MolIso G.molecule H.molecule) : G.order = H.order :=
  (Comb.card_gbranch G.tree).symm.trans ((Fintype.card_congr F.e).trans (Comb.card_gbranch H.tree))

/-- The exact scalar summand in the literal normalized source kernel. -/
noncomputable def splicedKernelSummand (G : Garden w) (D : SplicedKernelData G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) : ℂ :=
  (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D L γ η base z.1 : ℂ) *
    (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
    D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
    splicedTimeIntegral G D L γ δ base z.1

/-- B1b-2 (Mk-general form of `unitSpliceGenDecorationEquiv_symm_val`). -/
theorem unitSpliceGenDecorationEquiv_symm_valMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0) :
    ((unitSpliceGenDecorationEquivMk Z σ hT hsel d roots 0).symm z).1 = z.1 ∘ unitSpliceNodeEquivMk Z σ hT hsel := rfl

/-- The inverse exact decoration map pulls back literal node values. -/
theorem unitSpliceGenDecorationEquiv_symm_val (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots 0) :
    ((unitSpliceGenDecorationEquiv Z σ hsel d roots 0).symm z).1 = z.1 ∘ unitSpliceNodeEquiv Z σ hsel :=
  unitSpliceGenDecorationEquiv_symm_valMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel roots z

/-- B1b-2 (Mk-general form of `unitSplice_kernelSummand`). -/
theorem unitSplice_kernelSummandMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ Mk).G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0) :
    splicedKernelSummand (stSt G σ Mk).G D L γ η δ base roots
      ((unitSpliceGenDecorationEquivMk Z σ hT hsel d roots 0).symm z) =
    splicedKernelSummand (stSt Z.target (transportPrescription Z.iso σ) Mk').G
      (mapSplicedKernelData (unitSpliceMolIsoMk Z σ hT hsel) D) L γ η δ base roots z := by
  have hh : (mapSplicedKernelData (unitSpliceMolIsoMk Z σ hT hsel) D).hinges =
      D.hinges.image (unitSpliceMolIsoMk Z σ hT hsel).e := rfl
  have heps := (unitSplice_splicedEpsilonMk Z σ hT hsel D.hinges z.1).trans
    (congrArg (fun hs => splicedEpsilon (stSt Z.target (transportPrescription Z.iso σ) Mk').G hs z.1) hh.symm)
  unfold splicedKernelSummand
  rw [unitSpliceGenDecorationEquiv_symm_valMk, heps, unitSplice_splicedGapIndicatorMk,
    unitSplice_edgeAmplitude_productMk, ← unitSplice_hingeAmplitudeMk, unitSplice_splicedTimeIntegralMk]

/-- Every exact decorated kernel summand is invariant under the actual correspondence. -/
theorem unitSplice_kernelSummand (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots 0) :
    splicedKernelSummand (stSt G σ).G D L γ η δ base roots
      ((unitSpliceGenDecorationEquiv Z σ hsel d roots 0).symm z) =
    splicedKernelSummand (stSt Z.target (transportPrescription Z.iso σ)).G
      (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D) L γ η δ base roots z :=
  unitSplice_kernelSummandMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel D L γ η δ base roots z

/-- B1b-2 (Mk-general form of `unitSplice_splicedKernel`). -/
theorem unitSplice_splicedKernelMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ Mk).G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel (stSt G σ Mk).G D L γ η δ base roots =
      splicedKernel (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (mapSplicedKernelData (unitSpliceMolIsoMk Z σ hT hsel) D) L γ η δ base roots := by
  let F := unitSpliceMolIsoMk Z σ hT hsel
  let E := unitSpliceGenDecorationEquivMk Z σ hT hsel d roots 0
  unfold splicedKernel
  change (coupling d L γ δ : ℂ) ^ (stSt G σ Mk).G.order *
      (∑' z, splicedKernelSummand (stSt G σ Mk).G D L γ η δ base roots z) =
    (coupling d L γ δ : ℂ) ^ (stSt Z.target (transportPrescription Z.iso σ) Mk').G.order *
      (∑' z, splicedKernelSummand (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (mapSplicedKernelData F D) L γ η δ base roots z)
  rw [molIso_garden_order F]
  apply congrArg (fun x : ℂ => (coupling d L γ δ : ℂ) ^ (stSt Z.target (transportPrescription Z.iso σ) Mk').G.order * x)
  trans ∑' z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0,
    splicedKernelSummand (stSt G σ Mk).G D L γ η δ base roots (E.symm z)
  · exact (E.symm.tsum_eq (fun z => splicedKernelSummand (stSt G σ Mk).G D L γ η δ base roots z)).symm
  · exact tsum_congr (fun z => unitSplice_kernelSummandMk Z σ hT hsel D L γ η δ base roots z)

/-- The literal normalized kernel is unchanged by a selected unit LF twist and actual data transport. -/
theorem unitSplice_splicedKernel (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel (stSt G σ).G D L γ η δ base roots =
      splicedKernel (stSt Z.target (transportPrescription Z.iso σ)).G
        (mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D) L γ η δ base roots :=
  unitSplice_splicedKernelMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel D L γ η δ base roots

end WaveTurbulence.VineA
