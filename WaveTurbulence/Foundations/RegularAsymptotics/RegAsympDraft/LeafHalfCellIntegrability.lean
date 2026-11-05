/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafHalfCellSpectrum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafSpectralCoefficient
public import WaveTurbulence.Foundations.Incoh.FiniteCellProductFourier

/-! # Actual leaf-frequency integrability before finite lattice interchange -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp

/-- The literal independent-leaf Fourier density with original half cells. -/
def leafHalfCellFourierDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (x y : Fin Q.links.length → Mom d)
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) : ℂ :=
  (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α*
    halfCellAmplitude z
      (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
      (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y

/-- The retained half-cell density is exactly the independent input
Fourier density times its unmodified physical cutoff. -/
theorem leafHalfCellFourierDensity_eq {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d : ℕ} (F : Mom d → ℂ)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (x y : Fin Q.links.length → Mom d)
    (α : Fin (2*Q.links.length+1) → Fin d → ℝ) :
    leafHalfCellFourierDensity hQ hG F c k z x y α =
      cellProductFourierIntegrand (fun a v => leafCell F (c a) (toLp 2 v))
        (fun a => ofLp ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a)) α *
        halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
  have hh := leaf_character_halfCell_eq hQ hG α k x y z
  unfold leafHalfCellFourierDensity leafSpectrumCoefficient cellProductFourierIntegrand
  simp only [Circle.smul_def,smul_eq_mul,Finset.prod_mul_distrib]
  calc
    _ = ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*
        halfCellAmplitude z
          (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
          (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))) x y)*
        (∏ a, Fourier.timeFourier (fun v => leafCell F (c a) (toLp 2 v)) (α a)) := by ring
    _ = _ := by rw [← hh]; ring

/-- Original finite input norms give actual integrability of this
leaf-frequency density before any lattice or temporal interchange. -/
theorem integrable_leafHalfCellFourierDensity {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (x y : Fin Q.links.length → Mom d) :
    Integrable (leafHalfCellFourierDensity hQ hG F c k z x y) := by
  have hi := integrable_cellProductFourierIntegrand
    (fun a v => leafCell F (c a) (toLp 2 v))
    (fun a => (timeFourierNorm_leafCell_le hK hB hF (c a)).trans_lt ENNReal.ofReal_lt_top)
    (fun a => ofLp ((coupleMomentumData hQ hG).inputMomentum k
      (fun j i => if i=0 then x j else y j) a))
  have he : leafHalfCellFourierDensity hQ hG F c k z x y = fun α =>
      cellProductFourierIntegrand (fun a v => leafCell F (c a) (toLp 2 v))
        (fun a => ofLp ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a)) α *
          halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
    funext α
    exact leafHalfCellFourierDensity_eq hQ hG F c k z x y α
  rw [he]
  exact hi.mul_const _

end WaveTurbulence.RegAsymp
