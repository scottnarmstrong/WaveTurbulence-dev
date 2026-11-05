/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeafProfiles
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitude
public import WaveTurbulence.Foundations.Incoh.SpectralPhaseFactorization

/-! # Leaf-only Fourier representation with the original physical tree link cutoffs -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp

/-- The exact root/link factorization of the source leaf characters with the actual half-cells. -/
theorem tree_leaf_character_halfCell_eq {d n m w : ℕ} (P : MomentumTreeData n m w)
    (α : Fin m → Fin d → ℝ) (k : Mom d) (x y : Fin n → Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    (∏ a, (Real.fourierChar (Fourier.timePairing d (α a)
      (ofLp (P.inputMomentum k (fun j i => if i=0 then x j else y j) a))) : ℂ)) *
        halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) =
    (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) *
      halfCellAmplitude z
        (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
        (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1))) x y := by
  classical
  simp_rw [timePairing_eq_inner]
  rw [← coe_fourierChar_sum, sum_inner_treeInputMomentum_root_links]
  simp only [show (1:Fin 2) ≠ 0 by decide, ite_true, ite_false,
    AddChar.map_add_eq_mul, Circle.coe_mul, coe_fourierChar_sum,
    halfCellArrayWeight, Fintype.prod_prod_type, Fin.prod_univ_two,
    halfCellAmplitude, Circle.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  ring

/-- The source spatial input, with all link cells retained in physical space, is exactly the
leaf Fourier mixture with the transposed original momentum rows. -/
theorem tree_leafCellProduct_halfCell_eq_frequencyIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {f : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (c : Fin m → Fin d → ℤ) (k : Mom d) (x y : Fin n → Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    (∏ a, leafCell (f a) (c a) (P.inputMomentum k (fun j i => if i=0 then x j else y j) a)) *
        halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) =
      ∫ α : Fin m → Fin d → ℝ,
        (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k) : ℂ) * treeLeafSpectrum f c α *
          halfCellAmplitude z
            (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
            (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1))) x y := by
  rw [tree_leafCellProduct_eq_frequencyIntegral P hK hB hf c k, ← integral_mul_const]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  simp only [Circle.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
  have hh := tree_leaf_character_halfCell_eq P α k x y z
  dsimp only [treeLeafSpectrum]
  calc
    _ = ((∏ a, (Real.fourierChar (Fourier.timePairing d (α a)
        (ofLp (P.inputMomentum k (fun j i => if i=0 then x j else y j) a))) : ℂ)) *
          halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1)) *
        (∏ a, Fourier.timeFourier (fun v => leafCell (f a) (c a) (toLp 2 v)) (α a)) := by ring
    _ = _ := by rw [hh]; ring

end WaveTurbulence.RegAsymp
