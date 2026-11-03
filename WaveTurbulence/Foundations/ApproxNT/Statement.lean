/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The objects of DH23 Prop 6.4 (packet NT6)

DH23 `/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex` L984–L1010.

* `Shift`, `Shift.eval`, `Shift.Below`: the triangular structure of (propertyw2): each
  `x̃_j - x_j` is `0`, `±x_{j'}` or `±y_{j'}` with `j' ≺ j` (likewise `ỹ_j`);
* `supportSet`: the set `E` of (propertyw2);
* `resProfile J Ψ₁`: `Ψ(Ω) = ∏_{j∈J} χ_∞(Ω_j)/Ω_j · Ψ₁(Ω[J^c])` of (propertypsi1), with the
  source's `χ_∞ = 1 - χ₀` (`Fourier.chiInfinity`);
* `approxSum`: the sum `I` of (defi) over `(x,y) ∈ (ℤ_L^d)^{2n}`, `ℤ_L = L⁻¹ℤ`;
* `approxInt`: the integral `∫_{(ℝ^d)^{2n}} W Ψ(μ⟨x_j,y_j⟩) dx dy` of (conclusion1);
* `fourierW`: the Fourier transform of `W` on `(ℝ^d)^{2n}`, `Ŵ(ξ,η) = ∫ e(-(ξ·x+η·y)) W`;
* `freqNorm`: the Euclidean norm of `(ξ,η) ∈ (ℝ^d)^{2n}`; for `W ∈ C¹_c`,
  `‖(∂W)^‖_{L¹} = ∫ 2π |(ξ,η)| |Ŵ(ξ,η)|`.
-/

public section

noncomputable section

open MeasureTheory WithLp
open scoped FourierTransform

namespace WaveTurbulence.ApproxNT

/-- A shift in DH23 (propertyw2): `x̃_j - x_j` is `0`, `±x_{j'}` or `±y_{j'}`. -/
inductive Shift (n : ℕ) where
  /-- `x̃_j = x_j`. -/
  | zero : Shift n
  /-- `x̃_j = x_j ± x_{j'}` (`+` for `true`). -/
  | x (j : Fin n) (sgn : Bool) : Shift n
  /-- `x̃_j = x_j ± y_{j'}` (`+` for `true`). -/
  | y (j : Fin n) (sgn : Bool) : Shift n

variable {d n : ℕ}

/-- The value of a shift. -/
@[expose] def Shift.eval : Shift n → (Fin n → Mom d) → (Fin n → Mom d) → Mom d
  | .zero, _, _ => 0
  | .x j s, X, _ => if s then X j else -X j
  | .y j s, _, Y => if s then Y j else -Y j

/-- The shift of index `k` only involves indices `j' ≺ k`. -/
@[expose] def Shift.Below (lt : Fin n → Fin n → Prop) (k : Fin n) : Shift n → Prop
  | .zero => True
  | .x j _ => lt j k
  | .y j _ => lt j k

/-- The support set `E` of DH23 (propertyw2). -/
@[expose] def supportSet (xs ys : Fin n → Shift n) (a b : Fin n → Mom d) (lam : Fin n → ℝ) :
    Set ((Fin n → Mom d) × (Fin n → Mom d)) :=
  {z | ∀ j, ‖z.1 j + (xs j).eval z.1 z.2 - a j‖ ≤ lam j ∧
    ‖z.2 j + (ys j).eval z.1 z.2 - b j‖ ≤ lam j}

/-- The profile `Ψ` of DH23 (propertypsi1). -/
@[expose] def resProfile (J : Finset (Fin n)) (Ψ₁ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (Ω : Fin n → ℝ) : ℂ :=
  (∏ j ∈ J, ((Fourier.chiInfinity (Ω j) / Ω j : ℝ) : ℂ)) *
    Ψ₁ (toLp 2 (fun i : {j // j ∉ J} => Ω i))

/-- The sum `I` of DH23 (defi), with `μ = L^{2γ} δ`. -/
@[expose] def approxSum (L μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (Ψ : (Fin n → ℝ) → ℂ) : ℂ :=
  ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
    W (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j)) *
      Ψ (fun j => μ * inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))

/-- The integral in DH23 (conclusion1), without the factor `L^{2dn}`. -/
@[expose] def approxInt (μ : ℝ) (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (Ψ : (Fin n → ℝ) → ℂ) : ℂ :=
  ∫ z : (Fin n → Mom d) × (Fin n → Mom d), W z.1 z.2 * Ψ (fun j => μ * inner ℝ (z.1 j) (z.2 j))

/-- The Fourier transform of `W` on `(ℝ^d)^{2n}`. -/
@[expose] def fourierW (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (ξ η : Fin n → Mom d) : ℂ :=
  ∫ z : (Fin n → Mom d) × (Fin n → Mom d),
    𝐞 (-(∑ j, (inner ℝ (z.1 j) (ξ j) + inner ℝ (z.2 j) (η j)))) • W z.1 z.2

/-- The Euclidean norm of a frequency `(ξ, η) ∈ (ℝ^d)^{2n}`. -/
@[expose] def freqNorm (ξ η : Fin n → Mom d) : ℝ := Real.sqrt (∑ j, (‖ξ j‖ ^ 2 + ‖η j‖ ^ 2))

/-- `γ₁ = min(2γ, 1, 2(d-1)(1-γ))` of DH23 (othergamma). -/
@[expose] def gamma1 (d : ℕ) (γ : ℝ) : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

end WaveTurbulence.ApproxNT
