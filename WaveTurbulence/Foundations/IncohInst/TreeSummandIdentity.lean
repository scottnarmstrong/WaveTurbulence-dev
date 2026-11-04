/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreePhaseIntegral
public import WaveTurbulence.Foundations.IncohInst.TemporalSourceIdentity
public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity

/-! # Exact original tree lattice summand in link/time coordinates -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- For each original integer decoration, the source summand equals its literal analytic
link-time integral. No localization, approximation or convergence premise enters this identity. -/
theorem tree_summand_eq_linkIntegral {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (k : Mom d) (ts : Fin 2 → ℝ)
    (p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    let κ := (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1
    (epsDec LG.garden κ : ℂ) *
      phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => ts 0) (ts 1)) (ts 1)
        (cosetDecoration LG.garden L k κ) *
      ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ ℓ.toNode) : ℂ) =
    ∫ t in ((actualTreeFibers (d := d) LG hX C).timeDomain ∩ C.rootCoordinates.causalRootCut ts),
      sourceTemporalPhase L γ δ (treeLayerLinks LG hX) p t *
        (treeCarrier hX).sourceLeafWeight (treeInputFunctions LG F) k
          (fun i j => latticePoint L (p (i, j))) := by
  dsimp only
  rw [tree_phaseIntegral_eq_linkIntegral hX C]
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [tree_temporalSource_eq hX L γ δ k p t]
  congr 1
  rw [tree_sourceLeafWeight_eq hX F k]
  have he := tree_decOfParams_eq_coset hX L k (fun j => (p (j, 0), p (j, 1)))
  apply Finset.prod_congr rfl
  intro ℓ _
  exact congrArg (fun v : Mom d => (F (LG.layer ℓ.toNode) v : ℂ)) (congrFun he ℓ.toNode).symm

end WaveTurbulence.IncohInst
