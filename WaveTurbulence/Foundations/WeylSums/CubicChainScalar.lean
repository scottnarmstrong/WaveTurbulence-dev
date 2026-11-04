/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicTensor
public import WaveTurbulence.Foundations.WeylSums.CubicDiagonalSum
public import WaveTurbulence.Foundations.WeylSums.DoubleParitySeries
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetry

/-! # Scalar cubic-chain diagonalization with both parity constraints -/

public section
namespace WaveTurbulence.WeylSums

/-- Exact cubic diagonalization of the scalar source sum. -/
theorem scalarCubicSum_false_eq_diagonal_parity {L : ℝ} (hL : 0 < L)
    (t s a b c ξ ζ ω : ℝ) :
    scalarCubicSum L t s false a b c ξ ζ ω =
      ∑' q : {q : ℤ × ℤ × ℤ // Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)},
        scalarCubicDiagonalAmplitude L a b c q.val *
        e (((t+s)/(4*L^2))*(q.val.1 : ℝ)^2-(t/(4*L^2))*(q.val.2.1 : ℝ)^2-
          (s/(4*L^2))*(q.val.2.2 : ℝ)^2+((ξ+ζ+ω)/(2*L))*q.val.1+
          ((ξ-ζ)/(2*L))*q.val.2.1-(ω/(2*L))*q.val.2.2) := by
  let F (u v w : ℤ) := scalarCubicDiagonalAmplitude L a b c (u,v,w)*
    e (((t+s)/(4*L^2))*(u : ℝ)^2-(t/(4*L^2))*(v : ℝ)^2-
      (s/(4*L^2))*(w : ℝ)^2+((ξ+ζ+ω)/(2*L))*u+((ξ-ζ)/(2*L))*v-(ω/(2*L))*w)
  have heq : scalarCubicSum L t s false a b c ξ ζ ω =
      ∑' q : ℤ × ℤ × ℤ, F (q.1+q.2.1) (q.1-q.2.1) (q.1+q.2.1-2*q.2.2) := by
    apply tsum_congr
    intro q
    have h₁ : ((((q.1+q.2.1 : ℤ) : ℝ)+((q.1-q.2.1 : ℤ) : ℝ))/(2*L))-a = (q.1 : ℝ)/L-a := by
      push_cast
      field_simp [hL.ne']
      ring
    have h₂ : ((((q.1+q.2.1 : ℤ) : ℝ)-((q.1-q.2.1 : ℤ) : ℝ))/(2*L))-b = (q.2.1 : ℝ)/L-b := by
      push_cast
      field_simp [hL.ne']
      ring
    have h₃ : ((((q.1+q.2.1 : ℤ) : ℝ)-((q.1+q.2.1-2*q.2.2 : ℤ) : ℝ))/(2*L))-c = (q.2.2 : ℝ)/L-c := by
      push_cast
      field_simp [hL.ne']
      ring
    dsimp [F,scalarCubicTerm,scalarCubicDiagonalAmplitude]
    rw [h₁,h₂,h₃]
    congr 2
    push_cast
    field_simp [hL.ne']
    ring
  exact heq.trans (tsum_cubic_lattice F)

/-- The scalar chain sum is bounded by three Weyl suprema. Both parity
constraints are removed by exact character averaging. -/
theorem exists_scalarCubicChain_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ t s a b c ξ ζ ω : ℝ,
      ‖scalarCubicSum L t s false a b c ξ ζ ω‖ ≤
        C*weylSupremum (20*L) ((t+s)/(4*L^2))*
          weylSupremum (20*L) (t/(4*L^2))*weylSupremum (20*L) (s/(4*L^2)) := by
  obtain ⟨C,hC,hb⟩ := exists_scalarCubicDiagonalSum_bound
  refine ⟨C,hC,?_⟩
  intro L hL t s a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  have hMp : 0 < 20*L := by positivity
  let A := scalarCubicDiagonalAmplitude L a b c
  let φ (q : ℤ × ℤ × ℤ) := ((t+s)/(4*L^2))*(q.1 : ℝ)^2-(t/(4*L^2))*(q.2.1 : ℝ)^2-
    (s/(4*L^2))*(q.2.2 : ℝ)^2+((ξ+ζ+ω)/(2*L))*q.1+((ξ-ζ)/(2*L))*q.2.1-(ω/(2*L))*q.2.2
  let B := C*weylSupremum (20*L) ((t+s)/(4*L^2))*
    weylSupremum (20*L) (t/(4*L^2))*weylSupremum (20*L) (s/(4*L^2))
  have hfull (ρ τ : ℝ) :
      ‖∑' q : ℤ × ℤ × ℤ, A q*e (φ q+ρ*((q.1-q.2.1 : ℤ) : ℝ)/2+τ*((q.1-q.2.2 : ℤ) : ℝ)/2)‖ ≤ B := by
    have hh := hb L hL a b c
      ![(t+s)/(4*L^2),-(t/(4*L^2)),-(s/(4*L^2))]
      ![(ξ+ζ+ω)/(2*L)+(ρ+τ)/2,(ξ-ζ)/(2*L)-ρ/2,-(ω/(2*L))-τ/2]
    have heq : (∑' q : ℤ × ℤ × ℤ, A q*e (φ q+ρ*((q.1-q.2.1 : ℤ) : ℝ)/2+τ*((q.1-q.2.2 : ℤ) : ℝ)/2)) =
        scalarCubicDiagonalSum L a b c
          ![(t+s)/(4*L^2),-(t/(4*L^2)),-(s/(4*L^2))]
          ![(ξ+ζ+ω)/(2*L)+(ρ+τ)/2,(ξ-ζ)/(2*L)-ρ/2,-(ω/(2*L))-τ/2] := by
      apply tsum_congr
      intro q
      congr 2
      dsimp [φ]
      push_cast
      ring
    rw [heq]
    simpa [Fin.prod_univ_three, Matrix.vecHead, Matrix.vecTail, weylSupremum_neg hMp, mul_assoc, B] using hh
  rw [scalarCubicSum_false_eq_diagonal_parity hLp]
  have hsub : (∑' q : {q : ℤ × ℤ × ℤ // Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)}, A q.val*e (φ q.val)) =
      ∑' q : ℤ × ℤ × ℤ, {q | Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)}.indicator (fun q => A q*e (φ q)) q :=
    _root_.tsum_subtype {q : ℤ × ℤ × ℤ | Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)} (fun q => A q*e (φ q))
  change ‖∑' q : {q : ℤ × ℤ × ℤ // Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)}, A q.val*e (φ q.val)‖ ≤ B
  rw [hsub]
  have heq : (fun q : ℤ × ℤ × ℤ => {q | Even (q.1-q.2.1) ∧ Even (q.1-q.2.2)}.indicator (fun q => A q*e (φ q)) q) =
      (fun q : ℤ × ℤ × ℤ => (if Even (q.1-q.2.1) ∧ Even (q.1-q.2.2) then A q else 0)*e (φ q)) := by
    funext q
    by_cases hq : Even (q.1-q.2.1) ∧ Even (q.1-q.2.2) <;> simp [Set.indicator,hq]
  rw [heq]
  exact norm_tsum_double_parity_le A (finite_scalarCubicDiagonalAmplitude hLp a b c)
    (fun q => q.1-q.2.1) (fun q => q.1-q.2.2) φ B hfull

end WaveTurbulence.WeylSums
