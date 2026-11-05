/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePointSourceAgreement
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeRootSingularCountedMass

/-! # The original continuum tree leaf product is the actual counted half-cell mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst

/-- The actual unintegrated counted mixture with the original retained half cells. -/
def treeUnintegratedSingularKernel {d : ℕ} {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d) : ℂ :=
  ∑' c : SourceCellIndex S, ∫ α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ,
    treeRootSingularCoefficient hX f S k c α *
      halfCellAmplitude c.2.val (treeLeafModulations hX α).1 (treeLeafModulations hX α).2 x y

/-- The actual original continuum source product is recovered pointwise, before every
singular operation; root masks, Fourier coefficients and the omitted lone input are exact. -/
theorem treeUnintegratedSingularKernel_eq_source {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B C : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (treeCarrier hX).withRootInput.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p => x p.1 p.2) ≠ 0 → z ∈ S c)
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^(X.treeLinks (G.sig 0)).length) (k : Mom d)
    (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d) :
    treeUnintegratedSingularKernel hX f S k x y =
      (treeCarrier hX).sourceLeafWeight f k (fun j i => if i=0 then x j else y j) := by
  have hi := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar (D := 1) f hK hM hB hf S hS
    (treePointScalar hX x y S) (stronglyMeasurable_treePointScalar hX x y S)
      (treePointScalar_norm_le_one hX x y S) k
  rw [← tree_point_mixture_eq_source hX x y f hK hM hB hf S hcover hS k,
    integral_treeLeafCellMeasure_eq_tsum S _ hi]
  unfold treeUnintegratedSingularKernel
  apply tsum_congr
  intro c
  apply integral_congr_ae
  apply ae_of_all
  intro α
  unfold treeRootSingularCoefficient treePointScalar treeNormalizedScalar
  ring

end WaveTurbulence.RegAsymp
