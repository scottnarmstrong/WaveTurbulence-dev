/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePointCellAgreement
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootScalarIntegrability

/-! # Exact continuum source leaf product from the moving-root half-cell Fourier mixture -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst

/-- Each actual root-localized point mixture equals its original continuum leaf product
with the temporary root input. Counted Fubini follows from the actual source norms. -/
theorem tree_root_point_mixture_eq_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length)
    (q : Fin d → ℤ) (k : Mom d) :
    (∫ u, treeRootLeafAmplitude f S q k u*treePointScalar hX x y S u ∂treeLeafCellMeasure S) =
      treeRootCutoff q k*treeRootPartition q k*(treeCarrier hX).sourceLeafWeight f k
        (fun j i => if i=0 then x j else y j) := by
  have hi := integrable_treeRootLeafAmplitude_mul_scalar (D := 1) f hK hM hB hf S hS
    (treePointScalar hX x y S) (stronglyMeasurable_treePointScalar hX x y S)
      (treePointScalar_norm_le_one hX x y S) q k
  rw [integral_treeLeafCellMeasure_eq_tsum S _ hi]
  simp_rw [integral_treeRootLeafAmplitude_mul_pointScalar_eq hX x y f (by omega) hf S q k]
  rw [tsum_mul_left,((treeCarrier hX).withRootInput.hasSum_sourceCellWeight
    (appendRootInput f (treeRootPartition q)) S hcover k (fun j i => if i=0 then x j else y j)).tsum_eq,
    MomentumTreeData.sourceLeafWeight_withRootInput]
  ring

/-- The actual locally finite root models recover the whole original continuum source
leaf product, with the lone root input removed by its original partition of unity. -/
theorem tree_point_mixture_eq_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d) :
    (∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u*treePointScalar hX x y S u
      ∂treeLeafCellMeasure S) =
      (treeCarrier hX).sourceLeafWeight f k (fun j i => if i=0 then x j else y j) := by
  have he := (rootAmplitudeSum_eventuallyEq_model (treeRootLeafAmplitude f S)
    (treeRootLeafAmplitude_eq_zero f S) k).self_of_nhds
  have hz (q : Fin d → ℤ) (hq : q ∉ rootLocalCover k) : treeRootPartition q k = 0 := by
    rw [← treeRootCutoff_mul_partition q k,treeRootCutoff_eq_zero_on_ball_of_notMem k q hq (by simp),zero_mul]
  have hs : (∑ q ∈ rootLocalCover k, treeRootPartition q k) = 1 :=
    (hasSum_sum_of_ne_finset_zero hz).unique (hasSum_treeRootPartition k)
  simp_rw [he,rootAmplitudeModel,Finset.sum_mul]
  rw [integral_finsetSum _ (fun q _ => integrable_treeRootLeafAmplitude_mul_scalar (D := 1) f hK hM hB hf S hS
    (treePointScalar hX x y S) (stronglyMeasurable_treePointScalar hX x y S)
      (treePointScalar_norm_le_one hX x y S) q k)]
  simp_rw [tree_root_point_mixture_eq_source hX x y f hK hM hB hf S hcover hS,
    treeRootCutoff_mul_partition]
  rw [← Finset.sum_mul,hs,one_mul]

end WaveTurbulence.RegAsymp
