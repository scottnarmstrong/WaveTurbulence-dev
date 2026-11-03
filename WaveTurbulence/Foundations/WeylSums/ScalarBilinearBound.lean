/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearTensor
public import WaveTurbulence.Foundations.WeylSums.DiagonalBilinearSum
public import WaveTurbulence.Foundations.WeylSums.ParitySeries

/-! # A translation-uniform bilinear Weyl bound -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- Exact scalar diagonalization, with the parity lattice retained. -/
theorem scalarBilinearSum_eq_diagonal_parity {L : ℝ} (hL : 0 < L)
    (s a b ξ ζ : ℝ) :
    scalarBilinearSum L s a b ξ ζ =
      ∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, scalarDiagonalAmplitude L a b pq.val *
        e ((s/(4*L^2))*(pq.val.1 : ℝ)^2+(-s/(4*L^2))*(pq.val.2 : ℝ)^2+
          ((ξ+ζ)/(2*L))*pq.val.1+((ξ-ζ)/(2*L))*pq.val.2) := by
  let F (p q : ℤ) := scalarDiagonalAmplitude L a b (p,q) *
    e ((s/(4*L^2))*(p : ℝ)^2+(-s/(4*L^2))*(q : ℝ)^2+
      ((ξ+ζ)/(2*L))*p+((ξ-ζ)/(2*L))*q)
  have heq : scalarBilinearSum L s a b ξ ζ =
      ∑' xy : ℤ × ℤ, F (xy.1+xy.2) (xy.1-xy.2) := by
    apply tsum_congr
    intro xy
    have harg₁ : (((xy.1+xy.2 : ℤ) : ℝ)+((xy.1-xy.2 : ℤ) : ℝ))/(2*L)-a = (xy.1 : ℝ)/L-a := by
      push_cast
      field_simp [hL.ne']
      ring
    have harg₂ : (((xy.1+xy.2 : ℤ) : ℝ)-((xy.1-xy.2 : ℤ) : ℝ))/(2*L)-b = (xy.2 : ℝ)/L-b := by
      push_cast
      field_simp [hL.ne']
      ring
    dsimp [F, scalarDiagonalAmplitude, scalarBilinearTerm]
    rw [harg₁,harg₂]
    congr 2
    push_cast
    field_simp [hL.ne']
    ring
  exact heq.trans (tsum_bilinear_lattice F)

/-- The scalar bilinear cutoff sum is uniformly bounded by the square of
one supremum Weyl sum. The fixed enlargement is `12L`. -/
theorem exists_scalarBilinearSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ s a b ξ ζ : ℝ,
      ‖scalarBilinearSum L s a b ξ ζ‖ ≤ C * weylSupremum (12*L) (s/(4*L^2))^2 := by
  obtain ⟨C,hC,hb⟩ := exists_scalarDiagonalSum_bound
  refine ⟨C,hC,?_⟩
  intro L hL s a b ξ ζ
  have hLp : 0 < L := by linarith only [hL]
  have hMp : 0 < 12*L := by positivity
  let u := s/(4*L^2)
  let r₁ := (ξ+ζ)/(2*L)
  let r₂ := (ξ-ζ)/(2*L)
  let φ (pq : ℤ × ℤ) := u*(pq.1 : ℝ)^2+(-u)*(pq.2 : ℝ)^2+r₁*pq.1+r₂*pq.2
  have hbound (v w : ℝ) : ‖scalarDiagonalSum L a b u (-u) v w‖ ≤
      C * weylSupremum (12*L) u^2 := by
    have hh := hb L hL a b u (-u) v w
    rw [weylSupremum_neg hMp] at hh
    simpa only [pow_two, mul_assoc] using hh
  have hshift : (∑' pq : ℤ × ℤ, scalarDiagonalAmplitude L a b pq *
      e (φ pq + ((pq.1-pq.2 : ℤ) : ℝ)/2)) =
      scalarDiagonalSum L a b u (-u) (r₁+1/2) (r₂-1/2) := by
    apply tsum_congr
    intro pq
    congr 2
    dsimp [φ]
    push_cast
    ring
  rw [scalarBilinearSum_eq_diagonal_parity hLp, neg_div]
  change ‖∑' pq : {pq : ℤ × ℤ // Even (pq.1-pq.2)}, scalarDiagonalAmplitude L a b pq.val * e (φ pq.val)‖ ≤ _
  have hh := norm_tsum_parity_le (scalarDiagonalAmplitude L a b)
    (finite_scalarDiagonalAmplitude hLp a b) φ
  rw [hshift] at hh
  have hh₀ := hbound r₁ r₂
  have hh₁ := hbound (r₁+1/2) (r₂-1/2)
  change ‖∑' pq, scalarDiagonalAmplitude L a b pq * e (φ pq)‖ ≤ _ at hh₀
  exact hh.trans (by linarith only [hh₀,hh₁])

end WaveTurbulence.WeylSums
