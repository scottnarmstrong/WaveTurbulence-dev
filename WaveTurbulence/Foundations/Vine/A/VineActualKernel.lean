/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGapIndicator
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceKernel
/-! R32 value fallback with the independently constructed successor gap specification. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Stage1 RedSplice LGSpine
variable {w d : ℕ} {G : Garden w}

/-- Replacing gap entries with the same complete indicator preserves the literal kernel. -/
theorem kernel_replace_gap (H : Garden w) (D : SplicedKernelData H d)
    (entries : (v : GBranch H.tree) → Option (LocalGapSpecification H v))
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (he : ∀ z : GenDecoration H d roots 0, splicedGapIndicator H D L γ η base z.1 =
      splicedGapIndicator H {D with gapSpecification := entries} L γ η base z.1) :
    splicedKernel H D L γ η δ base roots =
      splicedKernel H {D with gapSpecification := entries} L γ η δ base roots := by
  unfold splicedKernel
  apply congrArg (fun x : ℂ => (coupling d L γ δ : ℂ) ^ H.order * x)
  apply tsum_congr
  intro z
  rw [he z]
  rfl

/-- B1b-3 (Mk-general form of `actualTargetData`). -/
noncomputable def actualTargetDataMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ Mk).G d) :
    SplicedKernelData (stSt Z.target (transportPrescription Z.iso σ) Mk').G d :=
  {mapSplicedKernelData (unitSpliceMolIsoMk Z σ hT hsel) D with
    gapSpecification := gapSpecificationMk Z.target (transportPrescription Z.iso σ) Mk'}

/-- B1b-3 (Mk-general form of `unitSplice_actual_gapIndicator`), given B2c's dart-label gap identity at the source
and target (`GapValueSelDartsAt`). -/
theorem unitSplice_actual_gapIndicatorMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (hgS : GapValueSelDartsAt G σ Mk) (hgT : GapValueSelDartsAt Z.target (transportPrescription Z.iso σ) Mk')
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0) :
    splicedGapIndicator (stSt G σ Mk).G D L γ η base (z.1 ∘ unitSpliceNodeEquivMk Z σ hT hsel) =
      splicedGapIndicator (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (actualTargetDataMk Z σ hT hsel D) L γ η base z.1 :=
  (gapValue_eq_indicatorMk σ D hD L γ η base _).symm.trans
    ((unitSplice_actual_gapValueMk Z σ hT hsel hH hgS hgT hL γ η base roots z).trans
      (gapValue_eq_indicatorMk (transportPrescription Z.iso σ) (actualTargetDataMk Z σ hT hsel D) rfl
        L γ η base z.1))

/-- B1b-3 (Mk-general form of `unitSplice_actual_splicedKernel`). -/
theorem unitSplice_actual_splicedKernelMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (hgS : GapValueSelDartsAt G σ Mk) (hgT : GapValueSelDartsAt Z.target (transportPrescription Z.iso σ) Mk')
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    {L : ℝ} (hL : L ≠ 0) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel (stSt G σ Mk).G D L γ η δ base roots =
      splicedKernel (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (actualTargetDataMk Z σ hT hsel D) L γ η δ base roots := by
  refine (unitSplice_splicedKernelMk Z σ hT hsel D L γ η δ base roots).trans ?_
  apply kernel_replace_gap
  intro z
  exact (unitSplice_splicedGapIndicatorMk Z σ hT hsel D L γ η base z.1).symm.trans
    (unitSplice_actual_gapIndicatorMk Z σ hT hsel hH hgS hgT D hD hL γ η base roots z)

/-- Actual target gap entries, with the remaining arbitrary kernel inputs carried by the actual map. -/
noncomputable def actualTargetData (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (D : SplicedKernelData (stSt G σ).G d) :
    SplicedKernelData (stSt Z.target (transportPrescription Z.iso σ)).G d :=
  {mapSplicedKernelData (unitSpliceMolIso Z σ hsel) D with
    gapSpecification := gapSpecification Z.target (transportPrescription Z.iso σ)}

/-- The full actual gap indicator agrees; no naturality of the chosen pairs is assumed. -/
theorem unitSplice_actual_gapIndicator (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots 0) :
    splicedGapIndicator (stSt G σ).G D L γ η base (z.1 ∘ unitSpliceNodeEquiv Z σ hsel) =
      splicedGapIndicator (stSt Z.target (transportPrescription Z.iso σ)).G
        (actualTargetData Z σ hsel D) L γ η base z.1 :=
  unitSplice_actual_gapIndicatorMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel hH
    (gapValueSelDartsAt_empty G σ) (gapValueSelDartsAt_empty Z.target _) D hD hL γ η base roots z

/-- The literal normalized source kernel is invariant with the actual target gap specification. -/
theorem unitSplice_actual_splicedKernel (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    {L : ℝ} (hL : L ≠ 0) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel (stSt G σ).G D L γ η δ base roots =
      splicedKernel (stSt Z.target (transportPrescription Z.iso σ)).G
        (actualTargetData Z σ hsel D) L γ η δ base roots :=
  unitSplice_actual_splicedKernelMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel hH
    (gapValueSelDartsAt_empty G σ) (gapValueSelDartsAt_empty Z.target _) D hD hL γ η δ base roots

end WaveTurbulence.VineA.NormalizedSplice
