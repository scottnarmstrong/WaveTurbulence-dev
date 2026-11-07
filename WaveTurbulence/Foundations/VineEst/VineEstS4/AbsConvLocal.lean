/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsSummand

/-! # Absolute convergence of the CL-local kernel sum (V5 Step 4b)

`absConvLocal`: for a CL block region `R` and the source input summability `HF`, every summand `τ ↦ clLocalSummand κ τ` is
integrable and `κ ↦ ∫ ‖clLocalSummand κ τ‖` is summable over the local decorations.  The summand is bounded by
`localBound` on the unit time box (`norm_clLocalSummand_le`), `localBound` is a product of the couple majorants at the labels
of the regional pairs (summable in the labels, `summable_majSum`) and of label independent tree bounds, and the local decoration
is determined by the labels of the regional pairs (`clLocalDecoration_ext_of_pairs`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
open scoped Classical

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

theorem integrable_clLocalSummand (R : CLRegionData G U a b) (hF : HF D hG L F layer base)
    (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) :
    Integrable (fun τ : CLInternalTime R => clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ) := by
  set Bx : Set (CLInternalTime R) := Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
    Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ) ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1)
    with hBx
  have hBm : MeasurableSet Bx := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hv1 : (volume : Measure (CLInternalTime R)) Bx = 1 := volume_box R (fun v => layer (D.coreBranch hG v).toNode)
  have hvol : (volume : Measure (CLInternalTime R)) Bx ≠ ⊤ := by
    rw [hv1]; exact ENNReal.one_ne_top
  have hg : Integrable (Bx.indicator fun _ => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hvol)
  refine hg.mono' (measurable_clLocalSummand R hF boundary t κ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  refine (norm_clLocalSummand_le R hF boundary t κ τ).trans ?_
  exact Set.indicator_le_indicator_of_subset (localTimeDomain_subset_box R _ t)
    (fun _ => localBound_nonneg R _) τ

theorem integral_norm_clLocalSummand_le (R : CLRegionData G U a b) (hF : HF D hG L F layer base)
    (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) :
    ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ ≤
      localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) := by
  set Bx : Set (CLInternalTime R) := Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
    Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ) ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1)
    with hBx
  have hBm : MeasurableSet Bx := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hv1 : (volume : Measure (CLInternalTime R)) Bx = 1 := volume_box R (fun v => layer (D.coreBranch hG v).toNode)
  have hvol : (volume : Measure (CLInternalTime R)) Bx ≠ ⊤ := by
    rw [hv1]; exact ENNReal.one_ne_top
  have hg : Integrable (Bx.indicator fun _ => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hvol)
  calc ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖
      ≤ ∫ τ, Bx.indicator (fun _ => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) τ :=
        integral_mono (integrable_clLocalSummand R hF boundary t κ).norm hg fun τ =>
          (norm_clLocalSummand_le R hF boundary t κ τ).trans
            (Set.indicator_le_indicator_of_subset (localTimeDomain_subset_box R _ t)
              (fun _ => localBound_nonneg R _) τ)
    _ = localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) := by
        rw [integral_indicator hBm, setIntegral_const, Measure.real, hv1]
        simp

/-- **Absolute convergence of the local decoration sum.** -/
theorem summable_integral_norm_clLocalSummand (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (hL : L ≠ 0) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    Summable fun κ : CLLocalDecoration R L base boundary =>
      ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ := by
  let m : ↥(clRegionalPairs hG U) → (Fin d → ℤ) → ℝ := fun p x => pairBound D hG L γ δ F layer hLayer base p.1 x
  have hm0 : ∀ p x, 0 ≤ m p x := fun p x => by
    unfold m pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  have hms : ∀ p, Summable (m p) := fun p =>
    (summable_majSum L F (nativeCoupleLayered D hG layer hLayer p.1) base
      (native_couple_plain D hG layer hLayer p.1) 0 (couple_hF_base hF p.1)).mul_left _
  obtain ⟨hs, _⟩ := tsum_pi_prod_le m hm0 hms
  let X : CLLocalDecoration R L base boundary → (↥(clRegionalPairs hG U) → (Fin d → ℤ)) :=
    fun κ p => clExtendIndices R κ.1 (p.1.firstLeaf hG).toNode
  have hX : Function.Injective X := fun κ κ' h =>
    clLocalDecoration_ext_of_pairs hU R hG hL base boundary κ κ' fun p hp => congrFun h ⟨p, hp⟩
  have h2 := (hs.comp_injective hX).mul_right (∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v)
  have h3 : Summable fun κ : CLLocalDecoration R L base boundary =>
      localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) := by
    refine h2.congr fun κ => ?_
    unfold localBound
    simp only [Function.comp, X, m]
    rw [Finset.prod_coe_sort (clRegionalPairs hG U)
      (fun p => pairBound D hG L γ δ F layer hLayer base p (clExtendIndices R κ.1 (p.firstLeaf hG).toNode))]
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun κ => integral_norm_clLocalSummand_le R hF boundary t κ) h3

end WaveTurbulence.VineEstS4
