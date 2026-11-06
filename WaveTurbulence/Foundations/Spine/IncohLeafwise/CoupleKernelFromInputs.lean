/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.CoupleKernelIdentity
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization
public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence

/-! # Exact original couple kernel identity from the actual finite source input bounds -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links
open WaveTurbulence.LGSpine

/-- B2's literal two-root `KQstar` equals the analytic raw source at the exact source input
budget. All lattice summability and interchange conditions are discharged internally. -/
theorem coupleLeaves_eq_rawL {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (hd : 0 < d) (L γ δ : ℝ) (hL : 1 ≤ L) (H : LeafProfiles 2 d)
    {p : ℕ} (_hp : ∀ a, LG.layer a ≤ p) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B)
    (k : Mom d) (ts : Fin 2 → ℝ) :
    coupleLeaves L γ δ LG H (ts 0) (ts 1) k =
      (coupleCarrier hQ).sourceCoupleKernel (gardenCircle LG.garden) (coupleRootCoordinates hQ hb)
        L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts k := by
  obtain ⟨C, _, hloc⟩ := exists_uniform_couple_link_cell_localization d hd
  choose S hScard hcover using fun c => hloc Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2
    (coupleCarrier hQ) (coupleCarrier_all_leaves hQ) c
  apply coupleLeaves_eq_raw_of_summableL hQ hb L γ δ H k ts
  exact (coupleCarrier hQ).summable_norm_sourceLeafWeight_lattice (coupleInputFunctionsL LG H) S hcover hScard
    hL (by omega) (by omega) hB (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a) k

end WaveTurbulence.IncohLeafwise
