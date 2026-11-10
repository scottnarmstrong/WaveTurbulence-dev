/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
/-! Auxiliary-constant compatibility for aligning the three WTPrefix gates. -/
public section
namespace WaveTurbulence.Induct
universe u

theorem Rdown_update_aux (P : WTParams) (C₁ C₂ : ℝ) (n : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).Rdown n = P.Rdown n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [WTParams.Rdown, ih]

theorem R_update_aux (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).R p = P.R p := by
  unfold WTParams.R
  exact Rdown_update_aux P C₁ C₂ _

theorem N_update_aux (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).N p = P.N p := by
  unfold WTParams.N
  rw [R_update_aux]

theorem inputsF_update_aux (P : WTParams) (C₁ C₂ : ℝ) (R : ℕ → Mom P.d → ℝ) :
    inputsF {P with C₁ := C₁, C₂ := C₂} R = inputsF P R := rfl

theorem coupleRemainder_update_aux (P : WTParams) (C₁ C₂ : ℝ)
    (R : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) :
    coupleRemainder {P with C₁ := C₁, C₂ := C₂} R p N t = coupleRemainder P R p N t := by
  funext k
  simp only [coupleRemainder, truncSumC, inputsF_update_aux, N_update_aux]

/-- Layergarden's actual assertion does not use either auxiliary constant. -/
theorem layergardenBody_update_aux (P : WTParams) (C₁ C₂ : ℝ) :
    LayergardenBody {P with C₁ := C₁, C₂ := C₂} = LayergardenBody P := by
  simp only [LayergardenBody, RemainderBound, coupleRemainder_update_aux, truncSum,
    inputsF_update_aux, WTParams.theta, WTParams.Lambda, N_update_aux, R_update_aux]


/-- Fixedpoint's actual assertion does not use either auxiliary constant. -/
theorem fixedpointBody_update_aux (P : WTParams) (C₁ C₂ : ℝ) :
    FixedpointBody.{u} {P with C₁ := C₁, C₂ := C₂} = FixedpointBody.{u} P := by
  simp only [FixedpointBody, AnsatzAt, truncSum, inputsF_update_aux, WTParams.theta, WTParams.Lambda,
    N_update_aux, R_update_aux]


end WaveTurbulence.Induct
