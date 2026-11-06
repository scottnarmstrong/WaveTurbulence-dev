/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafKernelSingleDerivative
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeNorm
public import WaveTurbulence.Foundations.XChain.SNormRealPart
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
/-! The convergence conditions in the exact one-leaf derivative identity follow from the
original finite input norms. They are not additional source-gate assumptions. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch

theorem SNormR_realPartialMom_bound {d A B : ℕ} (hd : 1 ≤ d) (j : Fin d)
    (H : Mom d → ℝ) (hc : ContDiff ℝ (A + 1 : ℕ) H) (C : ℝ) (hC : 0 ≤ C)
    (hH : SNormR (A + 1) B H ≤ ENNReal.ofReal C) :
    SNormR A B (realPartialMom j H) ≤ ENNReal.ofReal ((d : ℝ) ^ (A + 1) * C) := by
  have hc' : ContDiff ℝ (A + 1 : ℕ) (fun x => (H x : ℂ)) := Complex.ofRealCLM.contDiff.comp hc
  have hb := SNorm_wordD_bound hd [j] (fun x => (H x : ℂ)) hc' C hC hH
  have hdiff : Differentiable ℝ H := hc.differentiable (by simp)
  have hcont := wordD_contDiff [j] A hc'
  have hr := SNormR_realPart_bound _ hcont _ (by positivity) hb
  have he : (fun x => (wordD [j] (fun y => (H y : ℂ)) x).re) = realPartialMom j H :=
    (realPartialMom_eq_re j H hdiff).symm
  rw [he] at hr
  exact hr

theorem singleLeafDerivative_summable_coset {w d B : ℕ} (hd : 1 ≤ d)
    {L : ℝ} (hL : 1 ≤ L) (hB : d + 1 ≤ B) (G : Garden w) (H : LeafProfiles w d)
    (hc : ∀ l ∈ inputLeaves G, ContDiff ℝ (1 : ℕ) (H l.1))
    (C : (Fin w × TTree.Path) → NNReal)
    (hb : ∀ l ∈ inputLeaves G, SNormR 1 B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (l : ActualInputLeaves G) (j : Fin d) (k : Mom d) :
    ∀ a ∈ inputLeaves G, Summable fun n : Fin d → ℤ =>
      |singleLeafDerivative G H l j a.1 (k + latticePoint L n)| := by
  classical
  intro a ha
  let b : ActualInputLeaves G := ⟨a, ha⟩
  change Summable (fun n : Fin d → ℤ =>
    |singleLeafDerivative G H l j b.1.1 (k + latticePoint L n)|)
  have he := singleLeafDerivative_input G H l b j
  by_cases hab : b = l
  · rw [if_pos hab] at he
    rw [he]
    have hnorm := SNormR_realPartialMom_bound (A := 0) hd j (H l.1.1)
      (hc l.1 l.2) (C l.1.1 : ℝ) (NNReal.coe_nonneg _) (hb l.1 l.2)
    exact summable_abs_coset_of_SNormR hL hB (by positivity) _ hnorm k
  · rw [if_neg hab] at he
    rw [he]
    exact summable_abs_coset_of_SNormR hL hB (NNReal.coe_nonneg _) _ (hb a ha) k

/-- Exact one-leaf derivative formula from the original order-one input norm bounds. -/
theorem partialMom_kernelLeaves_eq_sum {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR 1 B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (j : Fin d) (k : Mom d) :
    partialMom j (fun x => kernelLeaves L γ δ LG H up s x nroot nfl) k =
      ∑ l : ActualInputLeaves LG.garden,
        kernelLeaves L γ δ LG (singleLeafDerivative LG.garden H l j) up s k nroot nfl :=
  partialMom_kernelLeaves_single_leaf hd hL hB γ δ LG H C hc hb up s nroot nfl hlone j k
    (fun l => singleLeafDerivative_summable_coset hd hL hB LG.garden H hc C hb l j k)

end WaveTurbulence.LGSpine
