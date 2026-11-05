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


/-- WKE Taylor's two bounds increase monotonically with the auxiliary constants;
its convergence and exact-sum clauses retain the identical carriers and integrands. -/
theorem wkeTaylorBody_update_aux (P : WTParams) (hW : WkeTaylorBody P)
    (hδ : 0 ≤ P.δ) (hC₁ : 0 ≤ P.C₁) (hC₂ : 0 ≤ P.C₂)
    {C₁ C₂ : ℝ} (h₁ : P.C₁ ≤ C₁) (h₂ : P.C₂ ≤ C₂) :
    WkeTaylorBody {P with C₁ := C₁, C₂ := C₂} := by
  intro p hp
  obtain ⟨h0, h1, h2⟩ := hW p hp
  refine ⟨h0, h1, ?_⟩
  intro N t ht
  apply (h2 N t ht).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul h₂ (pow_le_pow_left₀ (mul_nonneg hC₁ hδ)
    (mul_le_mul_of_nonneg_right h₁ hδ) N)
    (pow_nonneg (mul_nonneg hC₁ hδ) _) (hC₂.trans h₂)

end WaveTurbulence.Induct
