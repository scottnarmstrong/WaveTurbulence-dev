/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedLatticeScalar
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLocalProfileExchange
public import WaveTurbulence.Foundations.RegAsymp.TreeProfileQualitativeMass
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction

/-! # Exact finite profile decomposition of the actual local tree lattice scalar -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp Incoh

/-- The literal lattice scalar of one time-frequency profile, with its original Wick weight. -/
def treeProfileArrayScalar {d n : ℕ} (L μ : ℝ)
    (W : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) : ℂ :=
  treeHalfCellLatticeScalar L (fun g => W g * resProfile J (fun Ω => C (ofLp Ω) lam)
    (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))) z β γ

/-- Finitely many actual source profiles commute with their genuinely finite localized
lattice sum and temporal Fourier integral. The exact source masks and Wick weight remain. -/
theorem treeHalfCellLatticeScalar_finite_profiles {d n : ℕ} {ι : Type*} [Fintype ι]
    {L : ℝ} (hL : 0 < L) (μ : ℝ)
    (W : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (a : ι → ℂ) (J : ι → Finset (Fin n))
    (C : (i : ι) → ({j : Fin n // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) (t : Fin 2 → ℝ) :
    treeHalfCellLatticeScalar L (fun g => W g *
      ∑ i, a i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam (t 0) (t 1)) z β γ =
      ∑ i, a i * pairedInverseProfile (treeProfileArrayScalar L μ W z β γ (J i) (C i)) t := by
  classical
  let T := halfCellArrayLatticeBox L z
  have hz (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) (hg : g ∉ T) :
      halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j)) = 0 := by
    by_contra hn
    exact hg (mem_halfCellArrayLatticeBox hL z β γ g hn)
  unfold treeHalfCellLatticeScalar
  rw [tsum_eq_sum (s := T) (fun g hg => by rw [hz g hg,zero_mul])]
  calc
    _ = ∑ i, a i * ∑ g ∈ T,
        (halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
          (fun j => latticePoint L (g.2 j))*W g)*
            ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
              (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam (t 0) (t 1) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun v : ℂ => a i*v)
      have he := halfCell_weighted_temporal_interchange hL μ (t 0) (t 1) z β γ W (J i) (hC i)
      rw [tsum_eq_sum (s := T) (fun g hg => by rw [hz g hg,zero_mul,zero_mul])] at he
      exact he.trans (by
        unfold pairedInverseProfile treeProfileArrayScalar treeHalfCellLatticeScalar
        apply integral_congr_ae
        apply ae_of_all
        intro lam
        dsimp only
        congr 1
        apply tsum_congr
        intro g
        ring)

end WaveTurbulence.RegAsymp
