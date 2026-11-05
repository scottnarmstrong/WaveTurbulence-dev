/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellLatticeExchange
public import WaveTurbulence.Foundations.Incoh.SourceRootMaskAgreement

/-! # Exact original source recovery for one moving-root Fourier cell -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links WithLp

/-- The single extra moment in the actual amplitude cancels its literal scalar divisor. -/
theorem treeRootLeafAmplitude_mul_boundedScalar {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (L : ℝ)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    treeRootLeafAmplitude f S q k u * treeBoundedScalar hX L H S u =
      (treeRootCutoff q k * sourceRootMask u.1.1 k) *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (u.2 a)) k):ℂ) *
          treeLeafSpectrum (appendRootInput f (treeRootPartition q)) u.1.1 u.2 *
            treeHalfCellLatticeScalar L H u.1.2.val
              (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2) := by
  have hw : (treeLeafModulationWeight u.2:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (treeLeafModulationWeight_pos u.2).ne'
  unfold treeRootLeafAmplitude treeRootLeafModulation maskedModulation treeBoundedScalar
    treeNormalizedScalar
  change (treeRootCutoff q k * (sourceRootMask u.1.1 k *
    (((treeLeafModulationWeight u.2:ℂ)*treeLeafSpectrum (appendRootInput f (treeRootPartition q))
      u.1.1 u.2) * (Real.fourierChar (inner ℝ (∑ a, toLp 2 (u.2 a)) k):ℂ)))) *
      (treeHalfCellLatticeScalar L H u.1.2.val (treeLeafModulations hX u.2).1
        (treeLeafModulations hX u.2).2 / (treeLeafModulationWeight u.2:ℂ)) = _
  field_simp [hw]

/-- Original spatial input norms turn each actual counted Fourier cell into its original
finite lattice series, with the retained physical half-cell weight and root mask. -/
theorem integral_treeRootLeafAmplitude_mul_boundedScalar_eq {d K M : ℕ}
    {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {L : ℝ} (hL : 0 < L)
    (H : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B : ℝ}
    (hK : d+1 ≤ K) (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (q : Fin d → ℤ) (k : Mom d) (u : SourceCellIndex S) :
    (∫ α : Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ,
      treeRootLeafAmplitude f S q k (u,α) * treeBoundedScalar hX L H S (u,α)) =
      (treeRootCutoff q k * sourceRootMask u.1 k) *
        ∑' g : (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
            (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ),
          (treeCarrier hX).withRootInput.sourceCellWeight
            (appendRootInput f (treeRootPartition q)) S k
              (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) u * H g := by
  obtain ⟨Bq,hBq,hfq⟩ := exists_spatialNorm_bound_appendRootPartition f hf q
  simp_rw [treeRootLeafAmplitude_mul_boundedScalar hX L H f S q k]
  rw [integral_const_mul]
  congr 1
  exact (tree_leaf_halfCell_tsum_eq_frequencyIntegral (treeCarrier hX).withRootInput
    hK hBq.le hfq hL u.1 k u.2.val H).symm

/-- The literal root mask cancels against every original localized leaf product,
so it also cancels in any lattice-weighted cell series. -/
theorem tree_sourceRootMask_mul_cell_series {d n m w : ℕ} {P : MomentumTreeData n m w}
    (Croot : RootInputCoordinates P) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (u : SourceCellIndex S) {ι : Type*}
    (x : ι → Fin n → Fin 2 → Mom d) (H : ι → ℂ) :
    sourceRootMask u.1 k * (∑' g, P.sourceCellWeight f S k (x g) u * H g) =
      ∑' g, P.sourceCellWeight f S k (x g) u * H g := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro g
  change sourceRootMask u.1 k *
    ((P.localizedLeafWeight f u.1 k (x g) * halfCellArrayWeight u.2.val
      (fun p => x g p.1 p.2)) * H g) = _
  calc
    _ = (sourceRootMask u.1 k * P.localizedLeafWeight f u.1 k (x g)) *
        halfCellArrayWeight u.2.val (fun p => x g p.1 p.2) * H g := by ring
    _ = _ := by rw [Croot.sourceRootMask_mul_localizedLeafWeight]; rfl

end WaveTurbulence.RegAsymp
