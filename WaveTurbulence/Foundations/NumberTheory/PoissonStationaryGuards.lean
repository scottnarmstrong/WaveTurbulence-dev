/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.IntegralSecondDerivative
public import WaveTurbulence.Foundations.VdCB.TruncatedPoisson
public import WaveTurbulence.Foundations.VdCB.StationarySum
import Mathlib.Tactic

/-!
# Finite Poisson stationary transfer with endpoint guard frequencies

Near-boundary frequencies are estimated by the uniform curvature integral
test, while separated frequencies use integration by parts and interior
critical points use the shared sharp stationary formula. Every hypothesis
is actual phase calculus or finite-frequency geometry.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.NumberTheory

/-- A finite B-process estimate retaining a separate endpoint guard set.
The guard modes may include exact endpoint critical frequencies. -/
theorem norm_sum_sub_stationary_dual_le_with_guards {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {a b : ℕ} (hab : a ≤ b) (N : ℕ)
    (S G : Finset ℤ) (c r : ℤ → ℝ) {mu M rho : ℝ}
    (hmu : 0 < mu) (hM0 : 0 ≤ M) (hrho : 0 < rho)
    (hrange : ∀ x ∈ Icc (a:ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hcurv : ∀ x ∈ Icc (a:ℝ) b, mu ≤ deriv (deriv f) x)
    (hS : S ⊆ Finset.Icc 0 (N:ℤ)) (hG : G ⊆ Finset.Icc 0 (N:ℤ))
    (hdisj : Disjoint S G)
    (hr : ∀ nu ∈ S, 0 < r nu)
    (ha : ∀ nu ∈ S, (a:ℝ) ≤ c nu-r nu) (hb : ∀ nu ∈ S, c nu+r nu ≤ b)
    (hc : ∀ nu ∈ S, deriv f (c nu) = nu)
    (hM : ∀ nu ∈ S, ∀ x ∈ Icc (c nu-r nu) (c nu+r nu), |iteratedDeriv 3 f x| ≤ M)
    (hfar : ∀ nu ∈ (Finset.Icc 0 (N:ℤ) \ S) \ G,
      (∀ x ∈ Icc (a:ℝ) b, deriv f x ≤ (nu:ℝ)-rho) ∨
      (∀ x ∈ Icc (a:ℝ) b, (nu:ℝ)+rho ≤ deriv f x)) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1))) -
      ∑ nu ∈ S, expPhase (f (c nu)-(nu:ℝ)*c nu+1/8) /
        (Real.sqrt (deriv (deriv f) (c nu)) : ℂ)‖ ≤
      ((2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1)+
      (G.card:ℝ)*(4/Real.sqrt mu)+
      (((Finset.Icc 0 (N:ℤ) \ S) \ G).card:ℝ)/(Real.pi*rho)+
      ∑ nu ∈ S, (2*Real.pi/3*M*r nu^4+
        2/(Real.pi*(deriv (deriv f) (c nu)*r nu))+2/(Real.pi*(mu*r nu))) := by
  classical
  let I : ℤ → ℂ := fun nu => ∫ x in (a:ℝ)..b, expPhase (f x-(nu:ℝ)*x)
  let D : ℤ → ℂ := fun nu => expPhase (f (c nu)-(nu:ℝ)*c nu+1/8) /
    (Real.sqrt (deriv (deriv f) (c nu)) : ℂ)
  let T : Finset ℤ := Finset.Icc 0 (N:ℤ)
  let F : Finset ℤ := (T \ S) \ G
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hsec (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) : 0 ≤ deriv (deriv f) x :=
    hmu.le.trans (hcurv x hx)
  have hP := VdCB.norm_sum_sub_truncated_poisson_le hf2 hab N hrange hsec
  have hstation := VdCB.norm_sum_integral_sub_stationary_dual_le hf S c r hmu hM0 hcurv hr ha hb hc hM
  have hguard : ‖∑ nu ∈ G, I nu‖ ≤ (G.card:ℝ)*(4/Real.sqrt mu) := by
    calc
      _ ≤ ∑ nu ∈ G, ‖I nu‖ := norm_sum_le _ _
      _ ≤ ∑ _nu ∈ G, 4/Real.sqrt mu := by
        apply Finset.sum_le_sum
        intro nu _hnu
        exact norm_integral_expPhase_sub_frequency_le_of_second_pos hf2 habR hmu hcurv nu
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hnonstat : ‖∑ nu ∈ F, I nu‖ ≤ (F.card:ℝ)/(Real.pi*rho) := by
    calc
      _ ≤ ∑ nu ∈ F, ‖I nu‖ := norm_sum_le _ _
      _ ≤ ∑ _nu ∈ F, 1/(Real.pi*rho) := by
        apply Finset.sum_le_sum
        intro nu hnu
        have hfreq : ContDiff ℝ 2 (fun x => f x-(nu:ℝ)*x) :=
          hf2.sub (contDiff_const.mul contDiff_id)
        have hfreqsec (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) :
            0 ≤ deriv (deriv (fun x => f x-(nu:ℝ)*x)) x := by
          rw [VdCB.deriv_deriv_sub_frequency hf2]
          exact hsec x hx
        rcases hfar nu hnu with hneg | hpos
        · apply VdCB.norm_integral_expPhase_le_of_deriv_neg hfreq habR hrho _ hfreqsec
          intro x hx
          rw [VdCB.deriv_sub_frequency (hf2.differentiable (by norm_num))]
          linarith only [hneg x hx]
        · apply VdCB.norm_integral_expPhase_le_of_deriv_pos hfreq habR hrho _ hfreqsec
          intro x hx
          rw [VdCB.deriv_sub_frequency (hf2.differentiable (by norm_num))]
          linarith only [hpos x hx]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hGdiff : G ⊆ T \ S := by
    intro nu hnu
    exact Finset.mem_sdiff.mpr ⟨hG hnu,fun hs => Finset.disjoint_left.mp hdisj hs hnu⟩
  have hsum1 := Finset.sum_sdiff hS (f := I)
  have hsum2 := Finset.sum_sdiff hGdiff (f := I)
  have heq : (∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1)))-(∑ nu ∈ S,D nu) =
      ((∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1)))-(∑ nu ∈ T,I nu))+
      (∑ nu ∈ G,I nu)+(∑ nu ∈ F,I nu)+((∑ nu ∈ S,I nu)-(∑ nu ∈ S,D nu)) := by
    dsimp only [F] at *
    rw [← hsum1,← hsum2]
    abel
  change ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1)))-(∑ nu ∈ S,D nu)‖ ≤ _
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hP hguard)) hnonstat)) hstation))

end WaveTurbulence.NumberTheory
