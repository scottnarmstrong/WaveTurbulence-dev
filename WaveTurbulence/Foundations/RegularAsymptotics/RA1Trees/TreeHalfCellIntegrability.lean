/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellProfiles
public import WaveTurbulence.Foundations.Incoh.FiniteCellProductFourier

/-! # Actual leaf-only Fourier integrability before tree lattice interchange -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp

/-- The literal half-cell Fourier integrand, with the actual input-row modulation. -/
def treeHalfCellFourierDensity {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (x y : Fin n → Mom d)
    (α : Fin m → Fin d → ℝ) : ℂ :=
  (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) * treeLeafSpectrum f c α *
    halfCellAmplitude z
      (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
      (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1))) x y

/-- Exact pointwise equality to the independent leaf Fourier integrand times the
unmodified physical link cutoffs. -/
theorem treeHalfCellFourierDensity_eq {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (x y : Fin n → Mom d)
    (α : Fin m → Fin d → ℝ) :
    treeHalfCellFourierDensity P f c k z x y α =
      cellProductFourierIntegrand
        (fun a v => leafCell (f a) (c a) (toLp 2 v))
        (fun a => ofLp (P.inputMomentum k (fun j i => if i=0 then x j else y j) a)) α *
          halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
  have hh := tree_leaf_character_halfCell_eq P α k x y z
  unfold treeHalfCellFourierDensity treeLeafSpectrum cellProductFourierIntegrand
  simp only [Circle.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  calc
    _ = ((Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) *
        halfCellAmplitude z
          (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
          (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1))) x y) *
      (∏ a, Fourier.timeFourier (fun v => leafCell (f a) (c a) (toLp 2 v)) (α a)) := by ring
    _ = _ := by rw [← hh]; ring

/-- Source spatial norms justify the actual leaf-frequency integration for every
fixed physical link tuple, before a lattice sum or singular integral is exchanged. -/
theorem integrable_treeHalfCellFourierDensity {d n m w K M : ℕ} (P : MomentumTreeData n m w)
    {f : Fin m → Mom d → ℂ} {B : ℝ} (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (c : Fin m → Fin d → ℤ) (k : Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (x y : Fin n → Mom d) :
    Integrable (treeHalfCellFourierDensity P f c k z x y) := by
  have hi := integrable_cellProductFourierIntegrand
    (fun a v => leafCell (f a) (c a) (toLp 2 v))
    (fun a => (timeFourierNorm_leafCell_le hK hB (hf a) (c a)).trans_lt ENNReal.ofReal_lt_top)
    (fun a => ofLp (P.inputMomentum k (fun j i => if i=0 then x j else y j) a))
  have he : treeHalfCellFourierDensity P f c k z x y = fun α =>
      cellProductFourierIntegrand (fun a v => leafCell (f a) (c a) (toLp 2 v))
        (fun a => ofLp (P.inputMomentum k (fun j i => if i=0 then x j else y j) a)) α *
          halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
    funext α
    exact treeHalfCellFourierDensity_eq P f c k z x y α
  rw [he]
  exact hi.mul_const _

end WaveTurbulence.RegAsymp
