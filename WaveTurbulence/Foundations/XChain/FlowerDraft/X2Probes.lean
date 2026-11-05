/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes

/-!
# X2 probes

* `layergardenFlowerGate_eq`: the hypothesis `LayergardenFlowerGate` is the statement of `Flower-Gate.lean`'s
  `layergardenFlower`, verbatim (definitional equality). This probe uses the anchor, so it depends on `sorryAx`.
  The results of X2 never do.
* `flowerKernelGen_plain`: with the plain pattern, no `†` and no cutoffs, the general kernel of one flower tree is
  TARGET's `𝒥̃_𝒯` (jtflower), the `flowerKernel` of `Flower-Kernel.lean`, for `p < s < t ≤ p+1`. This checks the
  X2 kernel definitions against the kernel that O-FK represents.
-/

@[expose] public section

open MeasureTheory Finset Set

namespace WaveTurbulence.X2Probes


open SysAPI FTree

variable (L γ δ : ℝ) {d : ℕ}

theorem isChildOf_ne {T : TTree} {b b' : GBranch (single T)} (h : b'.IsChildOf b) : b' ≠ b := by
  rintro rfl
  obtain ⟨-, i, hi⟩ := h
  have := congrArg List.length hi
  simp at this

open Classical in
theorem flowerKernelGen_plain (p : ℕ) (F : FTree) (aP : (Fin d → ℤ) → ℂ) {t s : ℝ} (hps : (p : ℝ) < s)
    (hst : s < t) (ht : t ≤ p + 1) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F aP .plain none none none t s k k' = flowerKernel L γ δ p F aP t s k k' := by
  unfold flowerKernelGen flowerKernel
  by_cases hF : F = flower
  · simp only [hF, ↓reduceDIte]
  simp only [hF, ↓reduceDIte]
  congr 1
  refine tsum_congr fun κ => ?_
  have hw : treeWeight L F hF none none none κ.1.1 = 1 := by simp [treeWeight]
  rw [hw, Complex.ofReal_one, mul_one]
  congr 2
  have hfix : ∀ b, treeFixPat F hF .plain t s b = none ↔ b ≠ F.flowerParent hF := by
    intro b
    unfold treeFixPat
    by_cases h : b = F.flowerParent hF <;> simp [h]
  rw [← WaveTurbulence.FlowerProbes.integral_subtype_congr hfix
    (fun σ => (treeTimeDomain F.toTree p t).indicator (phaseFn L γ δ F.toTree κ.1.1)
      (fun c => if h : c = F.flowerParent hF then s else σ ⟨c, h⟩))]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  dsimp only
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  set x := fun c => if h : c = F.flowerParent hF then s else τ ⟨c, (hfix c).2 h⟩ with hx
  have hext : extendFixT (treeFixPat F hF .plain t s) τ = x := by
    funext b
    unfold extendFixT
    split
    · next v hv =>
      by_cases hb : b = F.flowerParent hF
      · subst hb
        unfold treeFixPat at hv
        simp only [↓reduceIte, Option.some.injEq] at hv
        simp only [hx, ↓reduceDIte, hv]
      · exfalso
        unfold treeFixPat at hv
        simp [hb] at hv
    · next hv =>
      have hb : b ≠ F.flowerParent hF := (hfix b).1 hv
      simp only [hx, hb, ↓reduceDIte]
  have hphase : phaseOffT L γ δ F.toTree ∅ κ.1.1 = phaseFn L γ δ F.toTree κ.1.1 := by
    funext τ
    simp [phaseOffT, phaseFn, omegaT]
  have hdom : x ∈ treeDomFix p F.toTree t (treeFixPat F hF .plain t s) ↔ x ∈ treeTimeDomain F.toTree p t := by
    have hxf : x (F.flowerParent hF) = s := by simp [hx]
    have hxo : ∀ b (hb : b ≠ F.flowerParent hF), x b = τ ⟨b, (hfix b).2 hb⟩ := fun b hb => by simp [hx, hb]
    constructor
    · intro h b
      refine ⟨?_, ?_, fun b' hb' => ?_⟩
      · by_cases hb : b = F.flowerParent hF
        · rw [hb, hxf]; exact hps
        · exact ((h b).1 ((hfix b).2 hb)).1
      · by_cases hb : b = F.flowerParent hF
        · rw [hb, hxf]; exact hst
        · exact ((h b).1 ((hfix b).2 hb)).2.2.2
      · refine (h b).2 b' hb' ?_
        by_cases hb1 : b' = F.flowerParent hF
        · right
          exact (hfix b).2 fun e => isChildOf_ne hb' (hb1.trans e.symm)
        · left
          exact (hfix b').2 hb1
    · intro h b
      refine ⟨fun hb => ?_, fun b' hb' _ => (h b).2.2 b' hb'⟩
      obtain ⟨h1, h2, -⟩ := h b
      exact ⟨h1, by linarith, by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith, h2⟩
  simp only [hext, hphase]
  by_cases hm : x ∈ treeTimeDomain F.toTree p t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.2 hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.1 h))]

end WaveTurbulence.X2Probes
