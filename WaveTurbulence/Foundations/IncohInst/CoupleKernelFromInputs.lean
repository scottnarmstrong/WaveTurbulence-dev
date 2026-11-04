/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleKernelIdentity
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization
public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence

/-! # Exact original couple kernel identity from the actual finite source input bounds -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- B2's literal two-root `KQstar` equals the analytic raw source at the exact source input
budget. All lattice summability and interchange conditions are discharged internally. -/
theorem KQstar_eq_raw {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (hd : 0 < d) (L γ δ : ℝ) (hL : 1 ≤ L) (F : ℕ → Mom d → ℝ)
    {p : ℕ} (hp : ∀ a, LG.layer a ≤ p) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ r ≤ p, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (F r k : ℂ)) ≤ ENNReal.ofReal B)
    (k : Mom d) (ts : Fin 2 → ℝ) :
    KQstar L γ δ F LG (ts 0) (ts 1) k =
      (coupleCarrier hQ).sourceCoupleKernel (gardenCircle LG.garden) (coupleRootCoordinates hQ hb)
        L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ) (coupleInputFunctions LG F) ts k := by
  obtain ⟨C, _, hloc⟩ := exists_uniform_couple_link_cell_localization d hd
  choose S hScard hcover using fun c => hloc Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2
    (coupleCarrier hQ) (coupleCarrier_all_leaves hQ) c
  apply KQstar_eq_raw_of_summable hQ hb L γ δ F k ts
  exact (coupleCarrier hQ).summable_norm_sourceLeafWeight_lattice (coupleInputFunctions LG F) S hcover hScard
    hL (by omega) (by omega) hB (fun a => coupleInputFunctions_spatialNorm_le LG F hp hF a) k

end WaveTurbulence.IncohInst
