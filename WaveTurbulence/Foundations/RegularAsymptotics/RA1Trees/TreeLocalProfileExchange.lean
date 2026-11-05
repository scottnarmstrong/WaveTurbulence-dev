/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellLatticeExchange

/-! # Exact original local tree lattice profiles as leaf and time Fourier mixtures -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh ClassJR ApproxNT WithLp

/-- An arbitrary original Wick weight preserves finite-support temporal Fubini. -/
theorem halfCell_weighted_temporal_interchange {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (μ t s : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      (halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j))*H g)*
        ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s) =
      ∫ lam, (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
        (halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
          (fun j => latticePoint L (g.2 j))*H g)*
          resProfile J (fun Ω => C (ofLp Ω) lam)
            (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j))))*e2 lam t s := by
  apply tsum_integral_resProfile_e2 (halfCellArrayLatticeBox L z)
  · intro g hg
    have hz : halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j)) = 0 := by
      by_contra hn
      exact hg (mem_halfCellArrayLatticeBox hL z β γ g hn)
    rw [hz, zero_mul]
  · exact hC

/-- Actual finite input norms justify both local exchanges for the literal source
resonant profile. The arbitrary lattice weight can be the exact squared Wick factor. -/
theorem tree_local_profile_eq_double_frequencyIntegral {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {f : Fin m → Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {L : ℝ} (hL : 0 < L) (μ t s : ℝ) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (z : (Fin n × Fin 2) → Fin d → ℤ)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (J : Finset (Fin n)) {C : ({j // j ∉ J} → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      ((∏ a, leafCell (f a) (c a) (P.inputMomentum k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) a)) *
        halfCellArrayWeight z (fun p => if p.2=0 then latticePoint L (g.1 p.1) else latticePoint L (g.2 p.1))) *
        (H g * ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
          (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s)) =
      ∫ α : Fin m → Fin d → ℝ,
        (Real.fourierChar (inner ℝ (∑ a, toLp 2 (α a)) k):ℂ) * treeLeafSpectrum f c α *
          ∫ lam, (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
            (halfCellAmplitude z
              (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
              (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1)))
              (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*H g)*
                resProfile J (fun Ω => C (ofLp Ω) lam)
                  (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j))))*e2 lam t s := by
  rw [tree_leaf_halfCell_tsum_eq_frequencyIntegral P hK hB hf hL]
  apply integral_congr_ae
  apply ae_of_all
  intro α
  dsimp only
  congr 1
  calc
    _ = ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
        (halfCellAmplitude z
          (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,0)))
          (fun j => treeLeafFrequency P (fun a => toLp 2 (α a)) (some (j,1)))
          (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*H g)*
            ∫ lam, resProfile J (fun Ω => C (ofLp Ω) lam)
              (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam t s :=
      tsum_congr (fun g => (mul_assoc _ _ _).symm)
    _ = _ := halfCell_weighted_temporal_interchange hL μ t s z _ _ H J hC

end WaveTurbulence.RegAsymp
