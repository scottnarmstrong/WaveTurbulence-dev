/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceTimeFactors

/-!
# Literal third-time normal modulations

All three spatial modulations depend only on the third normal time.
The exact physical quadratic-time convention is exposed for the normal
endpoint-strip estimates, uniformly in both source quadratic forms.
-/

@[expose] public section
set_option autoImplicit false

open WithLp

namespace WaveTurbulence.SumintPar

/-- One of the three actual normal modulations as a function of the third time. -/
@[expose] noncomputable def normalOuterFrequency {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 3) (s : ℝ) : Mom d :=
  (4:ℝ) • (ν (D.S.uSlot i.1 i.2 j)+(sourceHalfScale L γ δ*(s-t)*
    (D.ξc i.1 (Fin.castLE (by omega) j):ℝ)) • r)

/-- Each normal modulation is continuous in the third input time. -/
theorem continuous_normalOuterFrequency {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 3) :
    Continuous (normalOuterFrequency D L γ δ ν r t i j) := by
  unfold normalOuterFrequency
  fun_prop

/-- Exact identification of the source normal factor in the physical two-time convention. -/
theorem normalTimeSum_eq_physical_cubic {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (z : Fin 3 → ℝ) :
    normalTimeSum D L γ δ p ν r t i z =
      WeylSums.cubicLatticeSum (4*L) (coreTimeSign D i.1 0*((16*sourceHalfScale L γ δ)*(z 0-z 2)))
        (coreTimeSign D i.1 1*((16*sourceHalfScale L γ δ)*(z 1-z 2))) (D.Λsel i.1)
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 0)))
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 1)))
        ((1/4:ℝ) • toLp 2 (p (D.S.uSlot i.1 i.2 2)))
        (normalOuterFrequency D L γ δ ν r t i 0 (z 2))
        (normalOuterFrequency D L γ δ ν r t i 1 (z 2))
        (normalOuterFrequency D L γ δ ν r t i 2 (z 2)) := by
  have h0 : (Fin.castLE (by omega) (0 : Fin 3) : Fin 4) = 0 := rfl
  have h1 : (Fin.castLE (by omega) (1 : Fin 3) : Fin 4) = 1 := rfl
  have h2 : (Fin.castLE (by omega) (2 : Fin 3) : Fin 4) = 2 := rfl
  have he (ε s s' : ℝ) : 16*(ε*(sourceHalfScale L γ δ*(s-s'))) = ε*((16*sourceHalfScale L γ δ)*(s-s')) := by ring
  unfold normalTimeSum normalOuterFrequency
  simp only [h0,h1,h2]
  rw [he,he]

end WaveTurbulence.SumintPar
