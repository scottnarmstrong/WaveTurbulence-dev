/- Copy of INDUCT ../induct/SolutionPhase.lean (sha256 4679bd99915b5eac8e7dd8dac12cfabcb364cf0ad89efe4855ceb4392f3c05d7); only the namespace and imports changed. -/
/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.API
/-! Phase covariance of the literal classed a-system. -/
public section
namespace WaveTurbulence.Fixedpt
open Set

/-- A unit phase compatible with momentum addition commutes with the cubic nonlinearity. -/
theorem aNonlin_mul_phase {d : ℕ} (L γ δ t : ℝ) (phase : (Fin d → ℤ) → ℂ)
    (hphase : ∀ n q₁ q₂, phase q₁ * (starRingEnd ℂ) (phase q₂) * phase (n - q₁ + q₂) = phase n)
    (f : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    aNonlin L γ δ 1 t (fun m => phase m * f m)
      (fun m => (starRingEnd ℂ) (phase m * f m)) (fun m => phase m * f m) n =
      phase n * aNonlin L γ δ 1 t f (fun m => (starRingEnd ℂ) (f m)) f n := by
  rw [SysAPI.aNonlin_eq_tsum_pairs, SysAPI.aNonlin_eq_tsum_pairs]
  have he (q : (Fin d → ℤ) × (Fin d → ℤ)) (E : ℂ) :
      E * (phase q.1 * f q.1) * (starRingEnd ℂ) (phase q.2 * f q.2) *
        (phase (n - q.1 + q.2) * f (n - q.1 + q.2)) =
      phase n * (E * f q.1 * (starRingEnd ℂ) (f q.2) * f (n - q.1 + q.2)) := by
    rw [map_mul]
    calc
      _ = (phase q.1 * (starRingEnd ℂ) (phase q.2) * phase (n - q.1 + q.2)) *
          (E * f q.1 * (starRingEnd ℂ) (f q.2) * f (n - q.1 + q.2)) := by ring
      _ = _ := by rw [hphase]
  simp_rw [he]
  rw [tsum_mul_left]
  ring

/-- Phase covariance preserves the full class, its initial value, and the differential equation. -/
theorem isASolution_mul_phase {d : ℕ} {L γ δ T : ℝ} {c : (Fin d → ℤ) → ℂ}
    {a : ℝ → (Fin d → ℤ) → ℂ} (ha : IsASolution L γ δ T c a)
    (phase : (Fin d → ℤ) → ℂ) (hnorm : ∀ n, ‖phase n‖ = 1)
    (hphase : ∀ n q₁ q₂, phase q₁ * (starRingEnd ℂ) (phase q₂) * phase (n - q₁ + q₂) = phase n) :
    IsASolution L γ δ T (fun n => phase n * c n) (fun t n => phase n * a t n) := by
  refine ⟨?_, ?_, ?_⟩
  · funext n
    change phase n * a 0 n = phase n * c n
    rw [ha.1]
  · obtain ⟨C, hC⟩ := ha.2.1
    refine ⟨C, fun t ht n => ?_⟩
    rw [norm_mul, hnorm n, one_mul]
    exact hC t ht n
  · intro t ht n
    rw [aNonlin_mul_phase L γ δ t phase hphase]
    exact (ha.2.2 t ht n).const_mul (phase n)

end WaveTurbulence.Fixedpt
