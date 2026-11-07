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
  (gapValue_eq_indicator σ D hD L γ η base _).symm.trans
    ((unitSplice_actual_gapValue Z σ hsel hH hL γ η base roots z).trans
      (gapValue_eq_indicator (transportPrescription Z.iso σ) (actualTargetData Z σ hsel D) rfl L γ η base z.1))

/-- The literal normalized source kernel is invariant with the actual target gap specification. -/
theorem unitSplice_actual_splicedKernel (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    {L : ℝ} (hL : L ≠ 0) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel (stSt G σ).G D L γ η δ base roots =
      splicedKernel (stSt Z.target (transportPrescription Z.iso σ)).G
        (actualTargetData Z σ hsel D) L γ η δ base roots := by
  refine (unitSplice_splicedKernel Z σ hsel D L γ η δ base roots).trans ?_
  apply kernel_replace_gap
  intro z
  exact (unitSplice_splicedGapIndicator Z σ hsel D L γ η base z.1).symm.trans
    (unitSplice_actual_gapIndicator Z σ hsel hH D hD hL γ η base roots z)

end WaveTurbulence.VineA.NormalizedSplice
