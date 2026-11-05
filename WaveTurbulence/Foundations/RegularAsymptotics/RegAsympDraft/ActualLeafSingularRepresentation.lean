/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSingularCellExpansion

/-! # Actual singular representation of the original source leaf kernel

The original leaf product, rather than a surrogate amplitude, is identified
with the absolutely summable Fourier-cell kernel before applying singInt.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Incoh WithLp Finset

/-- The original source leaf kernel has the exact countable cell singular
representation with only finite input norms and one modulation moment.
Its geometric covers are chosen before all input functions and root momenta. -/
theorem actual_source_leaf_singular_representation (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length →
      ∃ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
          Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
        (∀ c, ((S c).card:ℝ) ≤ C^Q.links.length) ∧
        ∀ K M : ℕ, ∀ B : ℝ, d+2 ≤ K → 2*d ≤ M → 0 ≤ B →
        ∀ F : Mom d → ℂ, Fourier.spatialNorm K M F ≤ ENNReal.ofReal B →
        (∀ k : Mom d, ∀ x y : Fin Q.links.length → Mom d,
          (∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
            (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k x y) ∧
        ∀ (J : Finset (Fin Q.links.length)) (k : Mom d),
          singInt J (fun x y => ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
            (fun j i => if i=0 then x j else y j) a)) =
          ∑' i : LeafSingularCellIndex S, ∫ uv : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
              ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)),
            leafMaskedSingularCoefficient hQ hG F S k i uv * leafSingularCellOp J S i uv.2 := by
  classical
  obtain ⟨C,hC,hcover⟩ := actual_source_leaf_spectral_cells d (by omega)
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG hn
  obtain ⟨S,hcard,hdec⟩ := hcover G Q hQ hG
  refine ⟨S,hcard,?_⟩
  intro K M B hK hM hB F hF
  have hpoint (k : Mom d) (x y : Fin Q.links.length → Mom d) :
      (∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k x y := by
    have hs := summable_leafSingularCellKernel_terms hQ hG hn hK hM hB hF S hcard k x y
    rw [leafSingularCellKernel,tsum_leafSingularCellIndex S hs]
    apply (hdec K M B (by omega) hB F hF k x y).trans
    apply tsum_congr
    intro c
    calc
      _ = ∑ z : S c, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
          sourceRootMask c k *
            ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α *
              halfCellAmplitude z.val (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 x y) := by
        simpa only [leafSpectrumCoefficient,leafModulations] using
          (sum_coe_sort (S c) (fun z => ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
            sourceRootMask c k *
              ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α *
                halfCellAmplitude z (leafModulations hQ hG α).1 (leafModulations hQ hG α).2 x y))).symm
      _ = _ := by
        apply sum_congr rfl
        intro z _
        exact leaf_spectrum_eq_ordinary_cell_integrals hQ hG hn hK hM hB hF S k c z x y
  refine ⟨hpoint,?_⟩
  intro J k
  have hfun : (fun (x y : Fin Q.links.length → Mom d) =>
      ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then x j else y j) a)) = leafSingularCellKernel hQ hG F S k := by
    funext x y
    exact hpoint k x y
  rw [hfun]
  exact singInt_leafSingularCellKernel_eq hQ hG hd hn hK hM hB hF S hcard J k

end WaveTurbulence.RegAsymp
