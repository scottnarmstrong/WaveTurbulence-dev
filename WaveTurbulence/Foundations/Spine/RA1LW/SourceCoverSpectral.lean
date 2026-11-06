/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeadingSpatialIdentification
public import WaveTurbulence.Foundations.Incoh.SourcePointwiseLocalization

/-! # Original leaf spectrum and singular recombination for the same actual source cover -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ApproxNT

/-- Every actual source cover gives the original leaf-only Fourier
expansion. The SAME cover can therefore be used for the physical lattice
localization and the leading singular recombination. -/
theorem source_leaf_spectral_cells_of_cover {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c k x, (coupleMomentumData hQ hG).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    (k : Mom d) (x y : Fin Q.links.length → Mom d) :
    (∏ a, F a ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) =
    ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
      ∑ z : S c, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        sourceRootMask c k *
          ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α *
            halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 x y) := by
  classical
  have hs := (coupleMomentumData hQ hG).hasSum_sourceCellWeight_of_cover_at F S k
    (fun j i => if i=0 then x j else y j) (fun c => hcover c k _)
  apply hs.tsum_eq.symm.trans
  rw [hs.summable.tsum_sigma]
  apply tsum_congr
  intro c
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  unfold MomentumTreeData.sourceCellWeight MomentumTreeData.localizedLeafWeight
  change coupleLeafCellProduct hQ hG F c k (fun j i => if i=0 then x j else y j)*
      halfCellArrayWeight z.val (fun p => if p.2=0 then x p.1 else y p.1) = _
  rw [← sourceRootMask_mul_coupleLeafCellProduct hQ hG F c k
    (fun j i => if i=0 then x j else y j),mul_assoc]
  unfold coupleLeafCellProduct
  rw [leafCellProduct_halfCell_eq_frequencyIntegral hQ hG hK hB hF c k x y z.val]
  rw [← integral_const_mul]
  rfl

/-- The actual ordinary-cell kernel recovers the original source product
for every geometric source cover, rather than a separately selected witness. -/
theorem leafSingularCellKernel_eq_source_of_cover {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length)
    (hcover : ∀ c k x, (coupleMomentumData hQ hG).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    (k : Mom d) (x y : Fin Q.links.length → Mom d) :
    (∏ a, F a ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k x y := by
  have hs := summable_leafSingularCellKernel_terms hQ hG hn hK hM hB hF S hS k x y
  rw [leafSingularCellKernel,tsum_leafSingularCellIndex S hs]
  apply (source_leaf_spectral_cells_of_cover hQ hG (by omega) hB hF S hcover k x y).trans
  apply tsum_congr
  intro c
  apply Finset.sum_congr rfl
  intro z _
  exact leaf_spectrum_eq_ordinary_cell_integrals hQ hG hn hK hM hB hF S k c z x y

/-- The SAME source cover used by the physical kernel recombines to the
original singular leaf integral in the leading term. Original norms give
all integrability; no recombination identity is a premise. -/
theorem leafLeadingSpatialProfile_eq_source_of_cover {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hd : 3 ≤ d) (hn : 0 < Q.links.length)
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B C : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^Q.links.length)
    (hcover : ∀ c k x, (coupleMomentumData hQ hG).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    (J : Finset (Fin Q.links.length)) (k : Mom d) :
    leafLeadingSpatialProfile hQ hG J F S k =
      singInt J (fun x y => ∏ a, F a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) := by
  obtain ⟨_,_,hsp⟩ := leafLeadingSpatialProfile_integrable_spatialNorm hd
  obtain ⟨hi,_⟩ := hsp G Q hQ hG hn J 0 0 K M (by omega) (by omega) B C hB F hF S hS
  rw [leafLeadingSpatialProfile_eq_singInt_cellKernel hQ hG hd hn hK hM hB hF S hS J k (hi k)]
  have he : (fun (x y : Fin Q.links.length → Mom d) =>
      ∏ a, F a ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k := by
    funext x y
    exact leafSingularCellKernel_eq_source_of_cover hQ hG hn hK hM hB hF S hS hcover k x y
  rw [he]

end WaveTurbulence.RA1Leafwise
