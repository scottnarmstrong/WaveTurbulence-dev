/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SingleLeafDerivativeNorm
public import WaveTurbulence.Foundations.Spine.LeafDerivativeFamilyNorm
/-! Repeated coordinate derivatives of the actual kernel are an explicit finite sum of
individually differentiated-input kernels, preserving the full phase and decoration sum. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch

theorem partialMom_finsetSum {I : Type*} {d : ℕ} (s : Finset I)
    (f : I → Mom d → ℂ) (j : Fin d) (k : Mom d)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) k) :
    partialMom j (fun x => ∑ i ∈ s, f i x) k = ∑ i ∈ s, partialMom j (f i) k := by
  unfold partialMom
  rw [fderiv_fun_sum hf]
  simp only [_root_.sum_apply]

theorem wordD_kernelLeaves_eq_sum {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (word : List (Fin d)) (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (1 + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (k : Mom d) :
    wordD word (fun x => kernelLeaves L γ δ LG H up s x nroot nfl) k =
      ∑ c : LeafDerivativeChoices LG.garden word.length,
        kernelLeaves L γ δ LG (leafDerivativeProfiles LG.garden H word c) up s k nroot nfl := by
  classical
  induction word generalizing k with
  | nil =>
    change kernelLeaves L γ δ LG H up s k nroot nfl =
      ∑ _c : PUnit, kernelLeaves L γ δ LG H up s k nroot nfl
    simp only [Fintype.sum_unique]
  | cons j word ih =>
    have hn : 1 + word.length ≤ 1 + (j :: word).length := by simp only [List.length_cons]; omega
    have hcTail : ∀ l ∈ inputLeaves LG.garden,
        ContDiff ℝ (1 + word.length : ℕ) (H l.1) := by
      intro l hl
      exact (hc l hl).of_le (by exact_mod_cast hn)
    have hbTail : ∀ l ∈ inputLeaves LG.garden,
        SNormR (1 + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) := by
      intro l hl
      exact SNorm_mono_bound hn le_rfl (fun x => (H l.1 x : ℂ))
        (Complex.ofRealCLM.contDiff.comp (hc l hl)) _ (NNReal.coe_nonneg _) (hb l hl)
    have he : wordD word (fun x => kernelLeaves L γ δ LG H up s x nroot nfl) =
        fun x => ∑ c : LeafDerivativeChoices LG.garden word.length,
          kernelLeaves L γ δ LG (leafDerivativeProfiles LG.garden H word c) up s x nroot nfl :=
      funext (fun x => ih hcTail hbTail x)
    change partialMom j (wordD word (fun x => kernelLeaves L γ δ LG H up s x nroot nfl)) k = _
    rw [he]
    have hdiff (c : LeafDerivativeChoices LG.garden word.length)
        (_ : c ∈ (univ : Finset (LeafDerivativeChoices LG.garden word.length))) :=
      (ContDiff.differentiable
        (contDiff_leafDerivative_kernel hd hL hB γ δ LG H word c C hcTail hbTail
          up s nroot nfl hlone) (by norm_num)) k
    rw [partialMom_finsetSum univ _ j k hdiff]
    have hfirst (c : LeafDerivativeChoices LG.garden word.length) :=
      partialMom_kernelLeaves_eq_sum hd hL hB γ δ LG
        (leafDerivativeProfiles LG.garden H word c) (leafDerivativeCosts C 1 word)
        (contDiff_leafDerivativeProfiles LG.garden H word c hcTail)
        (leafDerivativeProfiles_norm hd LG.garden H word c C hcTail hbTail)
        up s nroot nfl hlone j k
    simp_rw [hfirst]
    change (∑ c : LeafDerivativeChoices LG.garden word.length,
        ∑ l : ActualInputLeaves LG.garden,
          kernelLeaves L γ δ LG (singleLeafDerivative LG.garden
            (leafDerivativeProfiles LG.garden H word c) l j) up s k nroot nfl) =
      ∑ c : ActualInputLeaves LG.garden × LeafDerivativeChoices LG.garden word.length,
        kernelLeaves L γ δ LG (singleLeafDerivative LG.garden
          (leafDerivativeProfiles LG.garden H word c.2) c.1 j) up s k nroot nfl
    rw [Fintype.sum_prod_type, sum_comm]

end WaveTurbulence.LGSpine
