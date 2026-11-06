/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivativeNorm
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
/-! High-order source input norms supply the literal leafwise gate typing premises. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

 theorem leafwiseControlled_of_high {w d A B : ℕ} (LG : LayeredGarden w)
    (H : LeafProfiles w d) (C : (Fin w × TTree.Path) → NNReal)
    (hA : 40 * d ≤ A) (hB : 40 * d ≤ B)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR A B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ)) :
    LeafwiseControlled LG H C := by
  intro l hl
  exact SNorm_mono_bound hA hB _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
    _ (NNReal.coe_nonneg _) (hb l hl)

 theorem singleLeafDerivative_high {w d A B : ℕ} (hd : 1 ≤ d) (G : Garden w)
    (H : LeafProfiles w d) (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves G, ContDiff ℝ (A + 1 : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves G, SNormR (A + 1) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (a : ActualInputLeaves G) (j : Fin d) :
    (∀ l ∈ inputLeaves G, ContDiff ℝ A (singleLeafDerivative G H a j l.1)) ∧
    (∀ l ∈ inputLeaves G, SNormR A B (singleLeafDerivative G H a j l.1) ≤
      ENNReal.ofReal (((d : NNReal) ^ (A + 1) * C l.1 : NNReal) : ℝ)) := by
  classical
  constructor
  · intro l hl
    let b : ActualInputLeaves G := ⟨l, hl⟩
    change ContDiff ℝ A (singleLeafDerivative G H a j b.1.1)
    rw [singleLeafDerivative_input]
    split_ifs
    · exact contDiff_realPartialMom j _ (hc a.1 a.2)
    · exact (hc l hl).of_le (by exact_mod_cast Nat.le_succ A)
  · intro l hl
    let b : ActualInputLeaves G := ⟨l, hl⟩
    change SNormR A B (singleLeafDerivative G H a j b.1.1) ≤ _
    rw [singleLeafDerivative_input]
    by_cases he : b = a
    · rw [if_pos he]
      have hh := SNormR_realPartialMom_bound hd j (H a.1.1) (hc a.1 a.2)
        (C a.1.1 : ℝ) (NNReal.coe_nonneg _) (hb a.1 a.2)
      have he' : l.1 = a.1.1 := congrArg (fun x : ActualInputLeaves G => x.1.1) he
      simpa only [he', NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hh
    · rw [if_neg he]
      apply (SNorm_mono_bound (Nat.le_succ A) le_rfl _
        (Complex.ofRealCLM.contDiff.comp (hc l hl)) _ (NNReal.coe_nonneg _) (hb l hl)).trans
      apply ENNReal.ofReal_le_ofReal
      simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]
      exact le_mul_of_one_le_left (NNReal.coe_nonneg _)
        (one_le_pow₀ (by exact_mod_cast hd))

end WaveTurbulence.LGSpine
