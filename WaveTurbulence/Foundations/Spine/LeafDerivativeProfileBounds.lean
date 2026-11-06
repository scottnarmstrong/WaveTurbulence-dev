/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafDerivativeAssignments
public import WaveTurbulence.Foundations.Spine.LeafRealDerivativeWords
/-! Every assigned derivative profile is the derivative word assigned to that original leaf. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem leafDerivativeProfiles_input {w d : ℕ} (G : Garden w) (H : LeafProfiles w d)
    (word : List (Fin d)) (c : LeafDerivativeChoices G word.length) (l : ActualInputLeaves G) :
    leafDerivativeProfiles G H word c l.1.1 =
      realWordD (assignedDerivativeWord G word c l) (H l.1.1) := by
  classical
  induction word generalizing l with
  | nil => rfl
  | cons j word ih =>
    change singleLeafDerivative G (leafDerivativeProfiles G H word c.2) c.1 j l.1.1 = _
    rw [singleLeafDerivative_input]
    by_cases hl : l = c.1
    · subst l
      simp only [ite_true, assignedDerivativeWord]
      rw [ih c.2 c.1]
      rfl
    · simp only [hl, ite_false, assignedDerivativeWord]
      exact ih c.2 l

theorem contDiff_leafDerivativeProfiles {w d A : ℕ} (G : Garden w) (H : LeafProfiles w d)
    (word : List (Fin d)) (c : LeafDerivativeChoices G word.length)
    (hc : ∀ l ∈ inputLeaves G, ContDiff ℝ (A + word.length : ℕ) (H l.1)) :
    ∀ l ∈ inputLeaves G, ContDiff ℝ A (leafDerivativeProfiles G H word c l.1) := by
  intro l hl
  let a : ActualInputLeaves G := ⟨l, hl⟩
  change ContDiff ℝ A (leafDerivativeProfiles G H word c a.1.1)
  rw [leafDerivativeProfiles_input]
  apply contDiff_realWordD
  have hsub : A + (assignedDerivativeWord G word c a).length ≤ A + word.length :=
    Nat.add_le_add_left (assignedDerivativeWord_length G word c a) A
  exact (hc l hl).of_le (by exact_mod_cast hsub)

theorem SNormR_leafDerivativeProfiles_bound {w d A B : ℕ} (hd : 1 ≤ d)
    (G : Garden w) (H : LeafProfiles w d) (word : List (Fin d))
    (c : LeafDerivativeChoices G word.length) (l : ActualInputLeaves G)
    (hc : ContDiff ℝ (A + word.length : ℕ) (H l.1.1))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : SNormR (A + word.length) B (H l.1.1) ≤ ENNReal.ofReal C) :
    SNormR A B (leafDerivativeProfiles G H word c l.1.1) ≤
      ENNReal.ofReal ((d : ℝ) ^ (A + word.length) * C) := by
  have hlen := assignedDerivativeWord_length G word c l
  have hsub : A + (assignedDerivativeWord G word c l).length ≤ A + word.length :=
    Nat.add_le_add_left hlen A
  have hc' : ContDiff ℝ (A + (assignedDerivativeWord G word c l).length : ℕ) (H l.1.1) :=
    hc.of_le (by exact_mod_cast hsub)
  have hb' := SNorm_mono_bound hsub le_rfl (fun x => (H l.1.1 x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hc) C hC hb
  rw [leafDerivativeProfiles_input]
  apply (SNormR_realWordD_bound hd _ (H l.1.1) hc' C hC hb').trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hd) hsub) hC

end WaveTurbulence.LGSpine
