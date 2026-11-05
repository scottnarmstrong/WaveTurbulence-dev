/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalCellLocalization
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafHalfCellLatticeExchange
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.RootMaskedInput

/-! # Exact masked leaf spectrum of each original physical source cell -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- The two literal lattice arrays of x/y coordinates, with no change of variables. -/
def latticeArrayProductEquiv (n : ℕ) (V : Type*) :
    ((Fin n × Fin 2) → V) ≃ (Fin n → V) × (Fin n → V) :=
  (linkPairArrayEquiv n V).symm.trans
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => V) (fun _ => V))

/-- Its inverse reads the corresponding original entry of the two arrays. -/
theorem latticeArrayProductEquiv_symm_apply {n : ℕ} {V : Type*}
    (g : (Fin n → V) × (Fin n → V)) (p : Fin n × Fin 2) :
    (latticeArrayProductEquiv n V).symm g p = if p.2=0 then g.1 p.1 else g.2 p.1 := rfl

/-- Original source-cell lattice sums have their literal masked leaf-only
Fourier integral. The lattice coefficient is arbitrary: the retained
half-cell support is finite before the interchange. -/
theorem sourceCell_lattice_eq_masked_leafSpectrum {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    {L : ℝ} (hL : 0 < L)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S) (k : Mom d)
    (H : ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ) :
    (∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
      H p*(coupleMomentumData hQ hG).sourceCellWeight (fun _ => F) S k
        (fun i j => latticePoint L (p (i,j))) u) =
    ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      sourceRootMask u.1 k *
        ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F u.1 α *
          ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
            halfCellAmplitude u.2.val
              (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
              (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1)))
              (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*
              H ((latticeArrayProductEquiv Q.links.length (Fin d → ℤ)).symm g)) := by
  let E := latticeArrayProductEquiv Q.links.length (Fin d → ℤ)
  let A := fun g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ) =>
    ((∏ a, leafCell F (u.1 a) ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) a))*
      halfCellArrayWeight u.2.val
        (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1)))*H (E.symm g)
  have hr : (∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
      H p*(coupleMomentumData hQ hG).sourceCellWeight (fun _ => F) S k
        (fun i j => latticePoint L (p (i,j))) u) = ∑' g, A g := by
    rw [← E.symm.tsum_eq]
    apply tsum_congr
    intro g
    have he : (fun i j => latticePoint L (E.symm g (i,j))) =
        (fun i j => if j=0 then latticePoint L (g.1 i) else latticePoint L (g.2 i)) := by
      funext i j
      rw [latticeArrayProductEquiv_symm_apply]
      split_ifs <;> rfl
    rw [he]
    unfold MomentumTreeData.sourceCellWeight MomentumTreeData.localizedLeafWeight A
    ring
  have hm : (∑' g, A g) = sourceRootMask u.1 k*(∑' g, A g) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro g
    have hh := sourceRootMask_mul_coupleLeafCellProduct hQ hG F u.1 k
      (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j))
    change (coupleLeafCellProduct hQ hG F u.1 k _ * _)*_ =
      sourceRootMask u.1 k*((coupleLeafCellProduct hQ hG F u.1 k _ * _)*_)
    rw [← mul_assoc,← mul_assoc,hh]
  rw [hr,hm]
  have hf := leaf_halfCell_tsum_eq_frequencyIntegral hQ hG hK hB hF hL u.1 k u.2.val
    (fun g => H (E.symm g))
  change (∑' g, A g) = _ at hf
  rw [hf,← integral_const_mul]

end WaveTurbulence.RegAsymp
