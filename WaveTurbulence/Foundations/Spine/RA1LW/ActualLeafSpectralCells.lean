/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafHalfCellSpectrum
public import WaveTurbulence.Foundations.Spine.RA1LW.RootMaskedInput
public import WaveTurbulence.Foundations.Incoh.LeafArrayLocalization

/-! # Exact countable spectral expansion of the original source leaf product -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp Finset

/-- The actual source input product has a countable leaf-cell expansion
with its literal root mask and finite half-link cover. The cover precedes
every input, root momentum and modulation choice. -/
theorem actual_source_leaf_spectral_cells (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      ∃ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
          Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) ∧
        ∀ K M : ℕ, ∀ B : ℝ, d+1 ≤ K → 0 ≤ B →
        ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B) →
        ∀ k : Mom d, ∀ x y : Fin Q.links.length → Mom d,
          (∏ a, F a ((coupleMomentumData hQ hG).inputMomentum k
            (fun j i => if i=0 then x j else y j) a)) =
          ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
            ∑ z ∈ S c, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
              sourceRootMask c k *
                ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) *
                  (∏ a, Fourier.timeFourier (fun v : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 v)) (α a)) *
                  halfCellAmplitude z
                    (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
                    (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y) := by
  classical
  obtain ⟨C,hC,hcover⟩ := actual_leafOnly_spectral_decomposition d hd
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG
  choose S hcard hdec using hcover G Q hQ hG
  refine ⟨S,hcard,?_⟩
  intro K M B hK hB F hF k x y
  calc
    _ = ∑' c : Fin (2*Q.links.length+1) → Fin d → ℤ,
        coupleLeafCellProduct hQ hG F c k (fun j i => if i=0 then x j else y j) :=
      (hasSum_leafCell_product F
        ((coupleMomentumData hQ hG).inputMomentum k (fun j i => if i=0 then x j else y j))).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro c
      rw [← sourceRootMask_mul_coupleLeafCellProduct hQ hG F c k
        (fun j i => if i=0 then x j else y j),hdec c K M B hK hB F hF k x y,mul_sum]
      apply sum_congr rfl
      intro z _hz
      rw [integral_const_mul]

end WaveTurbulence.RA1Leafwise
