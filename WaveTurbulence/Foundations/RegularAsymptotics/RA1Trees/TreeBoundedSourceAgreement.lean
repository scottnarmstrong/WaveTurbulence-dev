/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedCellAgreement
public import WaveTurbulence.Foundations.RegAsymp.TreeLatticeCellExchange

/-! # Exact global original source recovery from the tree leaf Fourier mixture -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links

/-- The literal root-localized leaf Fourier mixture recovers its original lattice
series, with the temporary root input retained exactly. All countable exchanges follow
from original input norms and the actual bounded source coefficient. -/
theorem tree_root_bounded_mixture_eq_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hbH : ∀ g, ‖H g‖ ≤ D)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length)
    (q : Fin d → ℤ) (k : Mom d) :
    (∫ u, treeRootLeafAmplitude f S q k u * treeBoundedScalar hX L H S u
      ∂treeLeafCellMeasure S) =
      treeRootCutoff q k * treeRootPartition q k *
        ∑' g : (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
            (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ),
          H g * (treeCarrier hX).sourceLeafWeight f k
            (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
  have hm := stronglyMeasurable_treeBoundedScalar hX (zero_lt_one.trans_le hL) H S
  have hb := treeBoundedScalar_norm_le hX hL H hD hbH S
  have hi := integrable_treeRootLeafAmplitude_mul_scalar f hK hM hB hf S hS
    (treeBoundedScalar hX L H S) hm hb q k
  obtain ⟨Bq,hBq,hfq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  have hlocal (u : SourceCellIndex S) :
      (∫ α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ,
        treeRootLeafAmplitude f S q k (u,α)*treeBoundedScalar hX L H S (u,α)) =
      treeRootCutoff q k *
        ∑' g : (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
            (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ),
          H g * (treeCarrier hX).withRootInput.sourceCellWeight
            (appendRootInput f (treeRootPartition q)) S k
              (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) u := by
    rw [integral_treeRootLeafAmplitude_mul_boundedScalar_eq hX
      (zero_lt_one.trans_le hL) H f (by omega) hf S q k u,mul_assoc,
      tree_sourceRootMask_mul_cell_series (treeCarrier hX).withRootInputCoordinates]
    apply congrArg (fun v : ℂ => treeRootCutoff q k*v)
    apply tsum_congr
    intro g
    exact mul_comm _ _
  rw [integral_treeLeafCellMeasure_eq_tsum S _ hi]
  simp_rw [hlocal]
  rw [tsum_mul_left,← tree_lattice_pair_eq_tsum_cells (treeCarrier hX).withRootInput
    (appendRootInput f (treeRootPartition q)) S k (fun c x => hcover c k x)
    hS hL (by omega) hM hBq.le hfq H hbH]
  simp_rw [MomentumTreeData.sourceLeafWeight_withRootInput,← mul_assoc]
  rw [tsum_mul_right]
  ring

/-- Summing the actual locally finite moving-root models removes the temporary root
input and recovers the entire original tree lattice series pointwise. -/
theorem tree_bounded_mixture_eq_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hbH : ∀ g, ‖H g‖ ≤ D)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length)
    (k : Mom d) :
    (∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u * treeBoundedScalar hX L H S u
      ∂treeLeafCellMeasure S) =
        ∑' g : (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
            (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ),
          H g * (treeCarrier hX).sourceLeafWeight f k
            (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
  have he := (rootAmplitudeSum_eventuallyEq_model (treeRootLeafAmplitude f S)
    (treeRootLeafAmplitude_eq_zero f S) k).self_of_nhds
  have hz (q : Fin d → ℤ) (hq : q ∉ rootLocalCover k) : treeRootPartition q k = 0 := by
    rw [← treeRootCutoff_mul_partition q k,treeRootCutoff_eq_zero_on_ball_of_notMem k q hq (by simp),zero_mul]
  have hs : (∑ q ∈ rootLocalCover k, treeRootPartition q k) = 1 :=
    (hasSum_sum_of_ne_finset_zero hz).unique (hasSum_treeRootPartition k)
  simp_rw [he,rootAmplitudeModel,Finset.sum_mul]
  rw [integral_finsetSum _ (fun q _ => integrable_treeRootLeafAmplitude_mul_scalar f hK hM hB hf S hS
    (treeBoundedScalar hX L H S) (stronglyMeasurable_treeBoundedScalar hX (zero_lt_one.trans_le hL) H S)
      (treeBoundedScalar_norm_le hX hL H hD hbH S) q k)]
  simp_rw [tree_root_bounded_mixture_eq_source hX hL H hD hbH f hK hM hB hf S hcover hS,
    treeRootCutoff_mul_partition]
  rw [← Finset.sum_mul,hs,one_mul]

end WaveTurbulence.RegAsymp
