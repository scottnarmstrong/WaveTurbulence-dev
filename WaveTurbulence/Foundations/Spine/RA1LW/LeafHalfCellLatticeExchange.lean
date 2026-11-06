/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafHalfCellIntegrability
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFiniteLattice

/-! # Exact independent-leaf Fourier exchange on each actual finite lattice cell -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links WithLp

private theorem halfCellAmplitude_zero_eq_weight {d n : ℕ}
    (z : (Fin n × Fin 2) → Fin d → ℤ) (x y : Fin n → Mom d) :
    halfCellAmplitude z 0 0 x y = halfCellArrayWeight z (fun p => if p.2=0 then x p.1 else y p.1) := by
  simp only [halfCellAmplitude,Pi.zero_apply,inner_zero_left,AddChar.map_zero_eq_one,
    one_smul,halfCellArrayWeight,Fintype.prod_prod_type,Fin.prod_univ_two,
    ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
  exact (Finset.prod_mul_distrib).symm

/-- The original finite input norm justifies the actual leaf Fourier
exchange with any lattice coefficient. Only the physical half-cell
support is truncated; no assumed spectral remainder identity is used. -/
theorem leaf_halfCell_tsum_eq_frequencyIntegral {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    {L : ℝ} (hL : 0 < L) (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    (H : ((Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ)) → ℂ) :
    (∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
      ((∏ a, leafCell (F a) (c a) ((coupleMomentumData hQ hG).inputMomentum k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) a)) *
        halfCellArrayWeight z (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1))) * H g) =
    ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ)*leafSpectrumCoefficient F c α *
        ∑' g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ),
          halfCellAmplitude z
            (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
            (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1)))
            (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) * H g := by
  let T := halfCellArrayLatticeBox L z
  have hz (g : (Fin Q.links.length → Fin d → ℤ) × (Fin Q.links.length → Fin d → ℤ)) (hg : g ∉ T) :
      halfCellArrayWeight z (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1)) = 0 := by
    by_contra hn
    apply hg
    exact mem_halfCellArrayLatticeBox hL z 0 0 g (by simpa only [halfCellAmplitude_zero_eq_weight] using hn)
  rw [tsum_eq_sum (s := T) (fun g hg => by rw [hz g hg,mul_zero,zero_mul])]
  calc
    _ = ∑ g ∈ T, ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        leafHalfCellFourierDensity hQ hG F c k z
          (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) α * H g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [leafCellProduct_halfCell_eq_frequencyIntegral hQ hG hK hB hF c k,
        ← integral_mul_const]
      rfl
    _ = ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ, ∑ g ∈ T,
        leafHalfCellFourierDensity hQ hG F c k z
          (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) α * H g := by
      exact (integral_finsetSum T (fun g _ =>
        (integrable_leafHalfCellFourierDensity hQ hG hK hB hF c k z _ _).mul_const (H g))).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro α
      dsimp only
      rw [tsum_eq_sum (s := T) (fun g hg => by
        have ha : halfCellAmplitude z
            (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0)))
            (fun j => sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1)))
            (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) = 0 := by
          by_contra hn
          exact hg (mem_halfCellArrayLatticeBox hL z _ _ g hn)
        rw [ha,zero_mul])]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      unfold leafHalfCellFourierDensity
      ring

end WaveTurbulence.RA1Leafwise
