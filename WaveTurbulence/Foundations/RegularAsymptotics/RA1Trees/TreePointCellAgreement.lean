/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePointScalar
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellProfiles
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement

/-! # Exact continuum recovery of one original tree leaf/link cell -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst WithLp

/-- The actual root mask cancels against the original physical source cell. -/
theorem tree_sourceRootMask_mul_sourceCellWeight {d n m w : ℕ} {P : MomentumTreeData n m w}
    (Croot : RootInputCoordinates P) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) (u : SourceCellIndex S) :
    sourceRootMask u.1 k*P.sourceCellWeight f S k x u = P.sourceCellWeight f S k x u := by
  change sourceRootMask u.1 k*(P.localizedLeafWeight f u.1 k x*
    halfCellArrayWeight u.2.val (fun p => x p.1 p.2)) = _
  rw [← mul_assoc,Croot.sourceRootMask_mul_localizedLeafWeight]
  rfl

/-- The actual added leaf moment cancels in the original unintegrated half-cell scalar. -/
theorem treeRootLeafAmplitude_mul_pointScalar {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    treeRootLeafAmplitude f S q k u*treePointScalar hX x y S u =
      (treeRootCutoff q k*sourceRootMask u.1.1 k)*
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (u.2 a)) k):ℂ)*
          treeLeafSpectrum (appendRootInput f (treeRootPartition q)) u.1.1 u.2*
            halfCellAmplitude u.1.2.val (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 x y) := by
  have hw : (treeLeafModulationWeight u.2:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (treeLeafModulationWeight_pos u.2).ne'
  unfold treeRootLeafAmplitude treeRootLeafModulation maskedModulation treePointScalar treeNormalizedScalar
  change (treeRootCutoff q k*(sourceRootMask u.1.1 k*
    (((treeLeafModulationWeight u.2:ℂ)*treeLeafSpectrum (appendRootInput f (treeRootPartition q))
      u.1.1 u.2)*(Real.fourierChar (inner ℝ (∑ a, toLp 2 (u.2 a)) k):ℂ)))) *
      (halfCellAmplitude u.1.2.val (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 x y /
        (treeLeafModulationWeight u.2:ℂ)) = _
  field_simp [hw]

/-- Original input Fourier inversion recovers the literal continuum source cell. -/
theorem integral_treeRootLeafAmplitude_mul_pointScalar_eq {d K M : ℕ}
    {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (x y : Fin (X.treeLinks (G.sig 0)).length → Mom d)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B : ℝ}
    (hK : d+1 ≤ K) (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S) :
    (∫ α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ,
      treeRootLeafAmplitude f S q k (u,α)*treePointScalar hX x y S (u,α)) =
      treeRootCutoff q k*(treeCarrier hX).withRootInput.sourceCellWeight
        (appendRootInput f (treeRootPartition q)) S k (fun j i => if i=0 then x j else y j) u := by
  obtain ⟨Bq,hBq,hfq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  simp_rw [treeRootLeafAmplitude_mul_pointScalar hX x y f S q k]
  rw [integral_const_mul]
  have he := tree_leafCellProduct_halfCell_eq_frequencyIntegral (treeCarrier hX).withRootInput
    hK hBq.le hfq u.1 k x y u.2.val
  change (treeRootCutoff q k*sourceRootMask u.1 k)*_ = _
  dsimp only [treeLeafModulations]
  rw [← he]
  change treeRootCutoff q k*sourceRootMask u.1 k*
    (treeCarrier hX).withRootInput.sourceCellWeight (appendRootInput f (treeRootPartition q)) S k
      (fun j i => if i=0 then x j else y j) u = _
  rw [mul_assoc,tree_sourceRootMask_mul_sourceCellWeight
    (treeCarrier hX).withRootInputCoordinates]

end WaveTurbulence.RegAsymp
