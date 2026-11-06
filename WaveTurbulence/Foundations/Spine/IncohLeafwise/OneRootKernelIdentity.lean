/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.OneRootSummandIdentity
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.CoupleKernelIdentity
public import WaveTurbulence.Foundations.IncohInst.GardenSign
public import WaveTurbulence.Foundations.IncohInst.SourceOrders
public import WaveTurbulence.Foundations.Incoh.RawSourceTimeFubini
public import WaveTurbulence.Foundations.Incoh.RawOneClockAgreement

/-! # The literal B1 couple kernel equals the analytic raw source kernel -/

public section
noncomputable section
open MeasureTheory
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links
open WaveTurbulence.LGSpine

/-- Conditional exact original-kernel identity. Summability is discharged independently from
the source spatial input norms; it is used solely for the lattice/time Fubini step. -/
theorem coupleLeaves_eq_oneRoot_raw_of_summableL {LG : LayeredGarden 2} {Q : RegCpl}
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
    (hwidth : ∀ b : GBranch LG.garden.tree, b.1.1 = a)
    {d : ℕ} (L γ δ : ℝ) (H : LeafProfiles 2 d) (k : Mom d) (ts : Fin 2 → ℝ)
    (hs : Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖)) :
    coupleLeaves L γ δ LG H (ts 0) (ts 1) k =
      (coupleCarrier hQ).sourceOneClockKernel (gardenCircle LG.garden) (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a) a
        L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts k := by
  let I := coupleInternalLinkDomain LG hQ ∩ (oneClockSelection Q.links.length hn ((coupleLinkEquiv hQ).symm ⟨(a, []), hb⟩) a).oneClockCut a (ts a)
  have hbox : I ⊆ Set.univ.pi (fun j => linkBox (coupleLayerLinks (d := d) LG hQ j)) :=
    Set.inter_subset_left.trans (coupleInternalLinkDomain_subset_boxes d hQ)
  unfold coupleLeaves kernelLeaves
  rw [couple_upperTimes_eqL ts, couple_order_eq_twice_links hQ]
  rw [← (coupleLatticeEquiv hQ d).symm.tsum_eq]
  change (coupling d L γ δ : ℂ) ^ (2 * Q.links.length) * LG.garden.zeta *
    (∑' p : Fin Q.links.length × Fin 2 → Fin d → ℤ,
      (epsDec LG.garden (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun b => ts b.1.1) 0) 0
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1
          (cosetDecoration LG.garden L k (decOfParams hQ (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1 ℓ.toNode) : ℂ)) = _
  simp_rw [couple_summand_eq_oneRootIntegralL hQ hn a hb hwidth L γ δ H k ts]
  unfold MomentumTreeData.sourceOneClockKernel MomentumTreeData.sourceIntegral
  rw [(coupleCarrier hQ).integral_sourceTimeIntegrand_eq_tsum (gardenCircle LG.garden) L γ δ
    (coupleLayerLinks LG hQ) I hbox (coupleInputFunctionsL LG H) k hs]
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

end WaveTurbulence.IncohLeafwise
