/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.VineEst.VineEstS3.DomainLayerOrder
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2TimeS1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.ConstraintsOK` (sha256 e1bb3c4fdfd6ce8f…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Constraints of the Step 3 datum: parent order plus layer order (R20 (2), R22)

`ConstraintsOK W`: the constraint set of `W` contains the parent pairs of the assembly and every further pair
is a layer-order pair `q v + 1 ≤ q w` (so, on the unit windows, automatically true off a null set).  The `sumint`
integral over `timeDom` of the datum therefore equals the integral over the source time domain
(`setIntegral_timeDom_eq_assembly`).  `layerOrderPairs q` collects all such pairs.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 VineParamContract TTree RegRed MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Parent pairs are constraints, every other constraint is a layer-order pair. -/
def ConstraintsOKΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) : Prop :=
  assemblyTimeConstraintsΓ hM9 B ⊆ W.constraints ∧
    ∀ c ∈ W.constraints, c ∉ assemblyTimeConstraintsΓ hM9 B → W.q c.1 + 1 ≤ W.q c.2

theorem constraintsOK_unionΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d)
    (hc : W.constraints = assemblyTimeConstraintsΓ hM9 B ∪ layerOrderPairs W.q) :
    ConstraintsOKΓ hM9 B W := by
  refine ⟨fun c h => hc ▸ Finset.mem_union_left _ h, fun c h h' => ?_⟩
  rw [hc] at h
  rcases Finset.mem_union.mp h with h1 | h1
  · exact absurd h1 h'
  · exact (mem_layerOrderPairs _ _).mp h1

/-- The source time domain and the `sumint` time domain differ by a null set. -/
theorem timeDom_ae_eq_assemblyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (layerB : GBranch G.tree → ℕ)
    (hq : W.q = assemblyTimeQΓ hM9 B layerB) (hok : ConstraintsOKΓ hM9 B W)
    (hI : 0 < (assemblyShapeΓ hM9 B).I) (t : Fin 3 → ℝ) :
    (sourceSumintDatumΓ hM9 B hG W).timeDom hI (t 0) (t 1) (t 2) =ᵐ[volume]
      assemblyTimeDomainΓ hM9 B layerB hI t := by
  have h := timeDom_ae_eq_of_layer_order (sourceSumintDatumΓ hM9 B hG W) (assemblyTimeConstraintsΓ hM9 B)
    hok.1 hok.2 hI (t 0) (t 1) (t 2)
  refine h.trans (Filter.EventuallyEq.of_eq ?_)
  ext τ
  simp only [SumintDatum.timeDom, assemblyTimeDomainΓ, sourceSumintDatumΓ, hq]
  rfl

theorem setIntegral_timeDom_eq_assemblyΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (layerB : GBranch G.tree → ℕ)
    (hq : W.q = assemblyTimeQΓ hM9 B layerB) (hok : ConstraintsOKΓ hM9 B W)
    (hI : 0 < (assemblyShapeΓ hM9 B).I) (t : Fin 3 → ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ((assemblyShapeΓ hM9 B).TVar → ℝ) → E) :
    ∫ τ in (sourceSumintDatumΓ hM9 B hG W).timeDom hI (t 0) (t 1) (t 2), f τ =
      ∫ τ in assemblyTimeDomainΓ hM9 B layerB hI t, f τ :=
  setIntegral_congr_set (timeDom_ae_eq_assemblyΓ hM9 B hG W layerB hq hok hI t)

end WaveTurbulence.GammaLow.Famb.VineEstS3
