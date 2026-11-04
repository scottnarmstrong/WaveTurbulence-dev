/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpectralArraySummand

/-!
# Identification of the actual spectral lattice/time integral

TARGET (incohproof9). The finite lattice support is common to every
source time and every Fourier shift; finite Fubini gives the literal
product of analytic link time factors on the original source domain.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- The actual temporal phase integral with the computed Fourier shifts is precisely the
analytic link-product integral. No kernel identity is assumed as a carrier field. -/
theorem MomentumTreeData.spectral_link_integral_eq {d n m w : ℕ} (P : MomentumTreeData n m w)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (hL : 0 < L)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : I ⊆ Set.univ.pi (fun i => linkBox (Q i))) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      ((∫ t in I, sourceTemporalPhase L γ δ Q p t) *
        linkArrayCutoff z (latticeMomentumArray L p)) *
        ∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
          (latticePoint L (p q))) : ℂ)) =
      ∫ t in I, ∏ i, linkTimeFactor L γ δ (P.spectralLinks Q z ξ i) (t i) := by
  classical
  let S := (finite_linkCellLatticeSet hL z).toFinset
  let b := fun p : (Fin n × Fin 2) → Fin d → ℤ =>
    linkArrayCutoff z (latticeMomentumArray L p) *
      ∏ q : Fin n × Fin 2, (Real.fourierChar (inner ℝ (P.spectralShift ξ (some q))
        (latticePoint L (p q))) : ℂ)
  have hb (p : (Fin n × Fin 2) → Fin d → ℤ) (hp : p ∉ S) : b p = 0 := by
    dsimp only [b]
    rw [linkArrayCutoff_eq_zero_of_not_mem L z p
      (by simpa only [S, Set.Finite.mem_toFinset] using hp), zero_mul]
  have hs (t : Fin n → Fin 2 → ℝ) :
      (∑' p, sourceTemporalPhase L γ δ Q p t * b p) =
        ∑ p ∈ S, sourceTemporalPhase L γ δ Q p t * b p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hb p hp, mul_zero])
  have hts : (∑' p, (∫ t in I, sourceTemporalPhase L γ δ Q p t) * b p) =
      ∑ p ∈ S, (∫ t in I, sourceTemporalPhase L γ δ Q p t) * b p :=
    tsum_eq_sum (s := S) (fun p hp => by rw [hb p hp, mul_zero])
  calc
    _ = ∑' p, (∫ t in I, sourceTemporalPhase L γ δ Q p t) * b p := by
      apply tsum_congr
      intro p
      exact mul_assoc _ _ _
    _ = ∫ t in I, ∑' p, sourceTemporalPhase L γ δ Q p t * b p := by
      rw [hts]
      simp_rw [hs]
      rw [integral_finsetSum S (fun p _ =>
        (integrableOn_sourceTemporalPhase L γ δ Q p hI).mul_const (b p))]
      simp only [integral_mul_const]
    _ = ∫ t in I, ∑' p, linkArraySummand L γ δ (P.spectralLinks Q z ξ) t p := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      apply tsum_congr
      intro p
      exact (mul_assoc _ _ _).symm.trans
        (P.sourceTemporalPhase_mul_cutoff_mul_character L γ δ Q z ξ p t)
    _ = _ := by simp_rw [tsum_linkArraySummand hL]

end WaveTurbulence.Incoh
