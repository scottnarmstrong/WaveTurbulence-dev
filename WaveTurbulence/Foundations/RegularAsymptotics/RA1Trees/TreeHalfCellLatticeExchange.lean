/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellIntegrability
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFiniteLattice

/-! # Exact leaf Fourier/lattice interchange with the actual finite half-cell support -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp

/-- At zero modulation the NT half-cell amplitude is the original physical cutoff product. -/
theorem halfCellAmplitude_zero_eq {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ)
    (x y : Fin n → Mom d) : halfCellAmplitude z 0 0 x y =
      halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
  simp only [halfCellAmplitude, Pi.zero_apply, inner_zero_left, AddChar.map_zero_eq_one,
    one_smul, halfCellArrayWeight, Fintype.prod_prod_type, Fin.prod_univ_two,
    ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false]
  exact (Finset.prod_mul_distrib).symm

/-- Original input norms justify Fourier/lattice interchange for any original lattice
weight, including the squared Wick factor and the full source time integral. The only
lattice truncation is the actual finite support of the retained physical half cells. -/
theorem tree_leaf_halfCell_tsum_eq_frequencyIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {f : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {L : ℝ} (hL : 0 < L) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      ((∏ a, leafCell (f a) (c a) (P.inputMomentum k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) a)) *
        halfCellArrayWeight z (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1))) * H g) =
      ∫ α : Fin m → Fin d → ℝ,
        (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) * treeLeafSpectrum f c α *
          ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
            halfCellAmplitude z
              (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
              (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1)))
              (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) * H g := by
  let T := halfCellArrayLatticeBox L z
  have hz (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) (hg : g ∉ T) :
      halfCellArrayWeight z (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1)) = 0 := by
    by_contra hn
    apply hg
    exact mem_halfCellArrayLatticeBox hL z 0 0 g (by simpa only [halfCellAmplitude_zero_eq] using hn)
  rw [tsum_eq_sum (s := T) (fun g hg => by rw [hz g hg,mul_zero,zero_mul])]
  calc
    _ = ∑ g ∈ T, ∫ α : Fin m → Fin d → ℝ,
        treeHalfCellFourierDensity P f c k z
          (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) α * H g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [tree_leafCellProduct_halfCell_eq_frequencyIntegral P hK hB hf c k,
        ← integral_mul_const]
      rfl
    _ = ∫ α : Fin m → Fin d → ℝ, ∑ g ∈ T,
        treeHalfCellFourierDensity P f c k z
          (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) α * H g := by
      exact (integral_finsetSum T (fun g _ =>
        (integrable_treeHalfCellFourierDensity P hK hB hf c k z _ _).mul_const (H g))).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro α
      dsimp only
      rw [tsum_eq_sum (s := T) (fun g hg => by
        have ha : halfCellAmplitude z
            (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
            (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1)))
            (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) = 0 := by
          by_contra hn
          exact hg (mem_halfCellArrayLatticeBox hL z _ _ g hn)
        rw [ha,zero_mul])]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      unfold treeHalfCellFourierDensity
      ring

end WaveTurbulence.RegAsymp
