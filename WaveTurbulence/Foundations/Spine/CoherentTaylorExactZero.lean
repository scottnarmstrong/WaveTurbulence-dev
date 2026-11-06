/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineAt
public import WaveTurbulence.Foundations.Spine.StageOrderLimit
public import WaveTurbulence.Foundations.Spine.ZeroRemainderNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! The fixed explicit approximation in Prop 6.2 gives the exact zero-remainder Taylor identity. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set
open scoped Topology

/-- TARGET Prop 6.2 has an L-independent left side at zero remainder. Applying it
along the same-parameter large-L family proves the exact identity, without adding
a Taylor-identity gate or a free approximation function. -/
theorem coherentTaylor_eq_zero_remainder (P : WTParams)
    (hsource : ∀ L ≥ P.L, SourceCoherentTaylorAt {P with L := L})
    (hd : 1 ≤ P.d) (hη : 0 < P.η) {p : ℕ} (hp : p < P.D) (n : ℕ)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d) :
    (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
      Q.app P.δ p (P.φ (P.δ * p)) t t k) =
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ) := by
  let z : ℂ := (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
    Q.app P.δ p (P.φ (P.δ * p)) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)
  let a : ℝ := (P.theta (p + 1) + 4 * P.theta p) / 5
  let C : ℝ := P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ))
  have hθ (r : ℕ) : 0 < P.theta r := by unfold WTParams.theta; positivity
  have ha : 0 < a := by dsimp only [a]; linarith [hθ p, hθ (p + 1)]
  have hlim : Tendsto (fun L : ℝ => C * L ^ (-a)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop ha).const_mul C
  have hbound : ∀ᶠ L : ℝ in atTop, ‖z‖ ≤ C * L ^ (-a) := by
    filter_upwards [eventually_ge_atTop P.L, eventually_order_le_stage P hd (p + 1) n] with L hL hn
    have hh := hsource L hL p hp (fun _ _ => 0)
      (fun r _ => inputRemainder_zero ({P with L := L} : WTParams) r) n hn t ht k
    have hinputs : inputsF ({P with L := L} : WTParams) (fun _ _ => 0) p =
        fun x => P.φ (P.δ * p) x := by
      funext x
      simp only [inputsF, add_zero]
    rw [hinputs] at hh
    change ‖z‖ ≤ C * L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5) at hh
    simpa only [a, neg_div] using hh
  have hz : z = 0 := norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hbound) (norm_nonneg z))
  exact sub_eq_zero.mp hz

end WaveTurbulence.LGSpine
