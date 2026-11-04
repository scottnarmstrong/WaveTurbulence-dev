/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleSummandIdentity
public import WaveTurbulence.Foundations.IncohInst.GardenSign
public import WaveTurbulence.Foundations.IncohInst.SourceOrders
public import WaveTurbulence.Foundations.Incoh.RawSourceTimeFubini
public import WaveTurbulence.Foundations.Incoh.RawCoupleAgreement

/-! # The literal B1 couple kernel equals the analytic raw source kernel -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- The two notations for the original couple external upper times agree exactly. -/
theorem couple_upperTimes_eq {G : Garden 2} (ts : Fin 2 → ℝ) :
    (fun b : GBranch G.tree => if b.1.1 = 0 then ts 0 else ts 1) = fun b => ts b.1.1 := by
  funext b
  by_cases h : b.1.1 = 0
  · simp only [h, ite_true]
  · have h1 : b.1.1 = 1 := by omega
    simp [h1]

/-- Conditional exact original-kernel identity. Summability is discharged independently from
the source spatial input norms; it is used solely for the lattice/time Fubini step. -/
theorem KQstar_eq_raw_of_summable {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (k : Mom d) (ts : Fin 2 → ℝ)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctions LG F) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    KQstar L γ δ F LG (ts 0) (ts 1) k =
      (coupleCarrier hQ).sourceCoupleKernel (gardenCircle LG.garden) (coupleRootCoordinates hQ hb)
        L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ) (coupleInputFunctions LG F) ts k := by
  let I := coupleInternalLinkDomain LG hQ ∩ (coupleRootCoordinates hQ hb).rootCut ts
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (coupleLayerLinks (d := d) LG hQ j)) :=
    Set.inter_subset_left.trans (coupleInternalLinkDomain_subset_boxes d hQ)
  unfold KQstar kernelK
  rw [couple_upperTimes_eq ts, couple_order_eq_twice_links hQ]
  rw [← (coupleLatticeEquiv hQ d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * Q.links.length) * LG.garden.zeta *
    (∑' p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      (epsDec LG.garden (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode)
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ)) = _
  simp_rw [couple_summand_eq_linkIntegral hQ hb L γ δ F k ts]
  unfold MomentumTreeData.sourceCoupleKernel MomentumTreeData.sourceIntegral
  rw [(coupleCarrier hQ).integral_sourceTimeIntegrand_eq_tsum (gardenCircle LG.garden) L γ δ
    (coupleLayerLinks LG hQ) I hbox (coupleInputFunctions LG F) k hs]
  rw [Complex.ofReal_pow]
  unfold coupling
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [gardenCircle_coe]
  ring

end WaveTurbulence.IncohInst
