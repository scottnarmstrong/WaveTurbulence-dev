/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub

/-! # B3s MK-SLOTS: the pinned slice of the unpinned time domain

When every pinned value satisfies the unpinned constraints of its branch (strictly inside its layer window, positive,
below its upper time) and no two pinned branches are parent and child (`AdmissiblePins`), the frozen pinned domain
`kDomainFix` and the unpinned domain `kDomain` agree on the pinned slice. Then main's pinned leaf kernel term
`FlowerP1.kernelLeavesFixTerm` is the unpinned-domain integral against `fixMeasure`
(`kernelLeavesFixTerm_eq_fixMeasure`), the form consumed by the pinned reduction.

Milestone α: the intrinsic pins of plain patterns (capped flower parents at `s ∈ (p, t)`) are admissible
(`admissiblePins_plain`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

theorem extendFix_eq_extendFixI (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : G.extendFix fix τ = extendFixI fix τ := by
  funext b
  unfold Garden.extendFix extendFixI
  rfl

/-- Admissible pins: pinned values satisfy the unpinned constraints of their branch, and no parent–child pair is
pinned. -/
structure AdmissiblePins (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : Prop where
  val : ∀ b v, fix b = some v →
    (LG.layer b.toNode : ℝ) < v ∧ v < LG.layer b.toNode + 1 ∧ 0 < v ∧ v < up b
  adj : ∀ b b' : GBranch LG.garden.tree, b'.IsChildOf b → fix b = none ∨ fix b' = none

/-- On the pinned slice, the pinned and the unpinned domains agree. -/
theorem mem_kDomainFix_iff (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (hA : AdmissiblePins LG up fix)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) :
    LG.garden.extendFix fix τ ∈ kDomainFix LG up fix ↔ LG.garden.extendFix fix τ ∈ kDomain LG up 0 := by
  set T := LG.garden.extendFix fix τ
  have hpin : ∀ b, (LG.layer b.toNode : ℝ) < T b ∧ T b < LG.layer b.toNode + 1 ∧ 0 < T b ∧ T b < up b →
      True := fun _ _ => trivial
  clear hpin
  constructor
  · intro h b
    obtain ⟨hown, hord⟩ := h b
    have hb : (LG.layer b.toNode : ℝ) < T b ∧ T b < LG.layer b.toNode + 1 ∧ 0 < T b ∧ T b < up b := by
      cases hfb : fix b with
      | none => exact hown hfb
      | some v =>
        have := hA.val b v hfb
        rw [show T b = v from by
          show LG.garden.extendFix fix τ b = v
          rw [extendFix_eq_extendFixI]; exact extendFixI_some fix τ hfb]
        exact this
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, fun b' hb' => hord b' hb' ?_, fun _ => hb.2.2.1⟩
    rcases hA.adj b b' hb' with h0 | h0
    · exact Or.inr h0
    · exact Or.inl h0
  · intro h b
    obtain ⟨h1, h2, h3, h4, hord, -⟩ := h b
    exact ⟨fun _ => ⟨h1, h2, h3, h4⟩, fun b' hb' _ => hord b' hb'⟩

/-- **The pinned leaf kernel term as a `fixMeasure` integral over the unpinned domain.** -/
theorem kernelLeavesFixTerm_eq_fixMeasure (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (hA : AdmissiblePins LG up fix)
    (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    FlowerP1.kernelLeavesFixTerm L γ δ LG H up fix k₀ κ =
      (epsDec LG.garden κ.1 : ℂ) *
        (∫ τ, (kDomain LG up 0).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
          ∂(fixMeasure fix)) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
  unfold FlowerP1.kernelLeavesFixTerm
  congr 2
  rw [integral_fixMeasure]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [Set.indicator]
  rw [← extendFix_eq_extendFixI]
  by_cases h : LG.garden.extendFix fix τ ∈ kDomain LG up 0
  · rw [if_pos h, if_pos ((mem_kDomainFix_iff LG up fix hA τ).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((mem_kDomainFix_iff LG up fix hA τ).1 h'))]

/-- **α: the pins of plain patterns are admissible** (capped flower parents in layer `p`, pinned at `s ∈ (p, t)`,
upper time `t`; at most one capped flower per tree, so no parent–child pair is pinned). -/
theorem admissiblePins_plain (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (hG : CapGeo LG J p)
    (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (ht : t ≤ p + 1) :
    AdmissiblePins LG (fun _ => t) (fixCap LG J (fun _ => FixPat.plain) t s) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  refine ⟨fun b v hb => ?_, fun b b' hb' => ?_⟩
  · unfold fixCap at hb
    split_ifs at hb with hc
    · obtain rfl := Option.some.inj hb
      rw [layer_capFlowerParent hG hc]
      exact ⟨hs.1, by linarith [hs.2], by linarith [hs.1], hs.2⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hc1 : IsCapFlowerParent LG J b := by
      by_contra hn; exact h1 (by simp [fixCap, hn])
    have hc2 : IsCapFlowerParent LG J b' := by
      by_contra hn; exact h2 (by simp [fixCap, hn])
    obtain ⟨ℓ, hℓ, hpℓ⟩ := hc1
    obtain ⟨ℓ', hℓ', hpℓ'⟩ := hc2
    have htree : ℓ.1.1 = ℓ'.1.1 := by
      rw [hpℓ.1, hpℓ'.1]
      exact hb'.1.symm
    have heq := hG.one_flower ℓ ℓ' hℓ hℓ' htree
    subst heq
    obtain ⟨_, i, hi⟩ := hpℓ
    obtain ⟨_, i', hi'⟩ := hpℓ'
    obtain ⟨_, j, hj⟩ := hb'
    rw [hj] at hi'
    have hl := congrArg List.length (hi.symm.trans hi')
    simp at hl

end WaveTurbulence.Flower.MkSlots
