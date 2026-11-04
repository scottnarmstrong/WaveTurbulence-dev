/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeTimeBoundary
public import WaveTurbulence.Foundations.IncohInst.NoFlowerTimeIntegral
public import WaveTurbulence.Foundations.IncohInst.NoFlowers

/-! # Exact original tree phase integral in the actual causal clock fibers -/

public section
noncomputable section
open MeasureTheory Set
namespace WaveTurbulence.IncohInst
open Incoh

theorem TreeClockSelection.clock_root (LG : LayeredGarden 1) {X : RegChain}
    {hX : X.DecodesTree LG.garden} (C : TreeClockSelection hX)
    (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) :
    treeClockEquiv hX t C.rootBranch = (C.rootCoordinates.equiv t).1 0 := by
  rw [RootCoordinates.equiv_rootVertex, C.rootCoordinates_first]
  exact treeClockEquiv_link hX t _

theorem TreeClockSelection.clock_parent (LG : LayeredGarden 1) {X : RegChain}
    {hX : X.DecodesTree LG.garden} (C : TreeClockSelection hX)
    (t : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → ℝ) :
    treeClockEquiv hX t C.parentBranch = (C.rootCoordinates.equiv t).1 1 := by
  rw [RootCoordinates.equiv_rootVertex, C.rootCoordinates_last]
  exact treeClockEquiv_link hX t _

/-- The literal source domain has exactly the constructed fibers and causal root cuts a.e. -/
theorem tree_kDomain_ae_causalFibers {d : ℕ} (LG : LayeredGarden 1) {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX) (ts : Fin 2 → ℝ) :
    treeClockEquiv hX ⁻¹' kDomain LG (fun _ => ts 0) (ts 1) =ᵐ[volume]
      (actualTreeFibers (d := d) LG hX C).timeDomain ∩ C.rootCoordinates.causalRootCut ts := by
  have h₁ := (measurePreserving_treeClockEquiv hX).quasiMeasurePreserving.preimage_ae_eq
    (tree_kDomain_ae_extremeCut LG hX C ts)
  have h₂ := tree_internal_ae_actualFibers (d := d) LG hX C
  filter_upwards [h₁, h₂] with t ht hi
  change (t ∈ _) = (t ∈ _) at ht hi ⊢
  rw [ht]
  change ((treeClockEquiv hX t ∈ internalTimeDomain LG) ∧ _) = _
  change (treeClockEquiv hX t ∈ internalTimeDomain LG) =
    (t ∈ (actualTreeFibers (d := d) LG hX C).timeDomain) at hi
  rw [hi]
  apply propext
  simp only [mem_inter_iff, RootCoordinates.causalRootCut, mem_preimage, mem_prod,
    mem_univ, and_true, causalTriangle, mem_ofPred_eq, C.clock_root LG, C.clock_parent LG]

/-- Original strict source tree phase integrals equal the raw analytic causal integrals exactly. -/
theorem tree_phaseIntegral_eq_linkIntegral {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (C : TreeClockSelection hX)
    {d : ℕ} (L γ δ : ℝ) (ts : Fin 2 → ℝ) (κ : GNode LG.garden.tree → Mom d) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => ts 0) (ts 1)) (ts 1) κ =
      ∫ t in ((actualTreeFibers (d := d) LG hX C).timeDomain ∩ C.rootCoordinates.causalRootCut ts),
        phaseProd L γ δ LG.garden κ (treeClockEquiv hX t) := by
  rw [phaseIntegral_eq_of_noFlowers LG.garden (tree_noFlowers hX) L γ δ _
    (measurableSet_kDomain LG _ (ts 1))]
  rw [← (measurePreserving_treeClockEquiv hX).setIntegral_preimage_emb
    (treeClockEquiv hX).measurableEmbedding]
  exact setIntegral_congr_set (tree_kDomain_ae_causalFibers LG hX C ts)

end WaveTurbulence.IncohInst
