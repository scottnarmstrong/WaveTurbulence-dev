/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode

/-! # B3s MK-SLOTS: a pinned root factors out of the upper clock (ruling R184, F-B3s-7)

On a plain layered garden with per-root upper clocks `top`, the clock `top j` enters the time domain only through the
constraint on the root branch of tree `j` (`parentClockWith` reads `top` only at roots). If that root `r` is pinned at
`sv`, then on the pinned slice
`τ ∈ kDomain (top) ↔ sv < top j0 ∧ τ ∈ kDomain (top with any value u₀ > sv at j0)`
(`mem_coreTimeDomainW_rootPinned`), and the pinned weighted kernel factors:
`kernelNodeWF … (top) … = [sv < top j0] · kernelNodeWF … (top[j0 ↦ u₀]) …` (`kernelNodeWF_rootPinned`).
For a cap couple whose top node is the pinned capped flower parent this splits the slot kernel into the indicator
`[s < ts 0]` (moved to a lower bound of the parent atom) and a kernel independent of its upper clock. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- `fixMeasure`-almost every time vector takes the pinned value at a pinned coordinate. -/
theorem ae_fixMeasure_pinned {ι : Type*} [Fintype ι] (fix : ι → Option ℝ) {i : ι} {v : ℝ} (h : fix i = some v) :
    ∀ᵐ τ ∂(fixMeasure fix), τ i = v := by
  rw [ae_iff]
  have : {τ : ι → ℝ | ¬ τ i = v} = Function.eval i ⁻¹' ({v}ᶜ : Set ℝ) := by ext τ; simp
  rw [this]
  refine Measure.pi_eval_preimage_null _ ?_
  simp only [fixFactor, h, Option.elim]
  rw [Measure.dirac_apply' _ (measurableSet_singleton v).compl]
  simp

/-- **Membership with a pinned root.** -/
theorem mem_coreTimeDomainW_rootPinned {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (top : Fin w → ℝ)
    (j0 : Fin w) (u₀ : ℝ) (r : GBranch tree) (hr : r.1 = (j0, [])) (τ : GBranch tree → ℝ) (sv : ℝ)
    (hτ : τ r = sv) (hsv : sv < u₀) :
    τ ∈ coreTimeDomainW layer top ↔ sv < top j0 ∧ τ ∈ coreTimeDomainW layer (Function.update top j0 u₀) := by
  have hpcw : ∀ (top' : Fin w → ℝ) (b : GBranch tree),
      parentClockWith top' τ b.toNode = if b.1.2 = [] then top' b.1.1 else parentClockWith top τ b.toNode := by
    intro top' b
    by_cases hb : b.1.2 = []
    · have hroot : b.toNode = GNode.root tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
      rw [if_pos hb, hroot, parentClockWith_root]
    · rw [if_neg hb, parentClockWith_nonroot top' τ b.toNode hb, parentClockWith_nonroot top τ b.toNode hb]
  have hr_iff : ∀ b : GBranch tree, b.1.2 = [] → b.1.1 = j0 → b = r := fun b h1 h2 =>
    Subtype.ext (Prod.ext (h2.trans (congrArg Prod.fst hr).symm) (h1.trans (congrArg Prod.snd hr).symm))
  constructor
  · intro h
    have hrr := (h r).2.2.2
    rw [hpcw top r, if_pos (by rw [hr]), hτ] at hrr
    rw [show r.1.1 = j0 from congrArg Prod.fst hr] at hrr
    refine ⟨hrr, fun b => ⟨(h b).1, (h b).2.1, (h b).2.2.1, ?_⟩⟩
    rw [hpcw]
    by_cases hb : b.1.2 = []
    · rw [if_pos hb]
      by_cases hj : b.1.1 = j0
      · have := hr_iff b hb hj; subst this
        rw [hj, Function.update_self, hτ]; exact hsv
      · rw [Function.update_of_ne hj]
        have := (h b).2.2.2
        rwa [hpcw top b, if_pos hb] at this
    · rw [if_neg hb]; exact (h b).2.2.2
  · rintro ⟨hlt, h⟩ b
    refine ⟨(h b).1, (h b).2.1, (h b).2.2.1, ?_⟩
    have hb' := (h b).2.2.2
    rw [hpcw] at hb' ⊢
    by_cases hb : b.1.2 = []
    · rw [if_pos hb] at hb' ⊢
      by_cases hj : b.1.1 = j0
      · have := hr_iff b hb hj; subst this
        rw [hj, hτ]; exact hlt
      · rwa [Function.update_of_ne hj] at hb'
    · rw [if_neg hb] at hb' ⊢; exact hb'

/-- **The pinned weighted kernel with a pinned root.** -/
theorem kernelNodeWF_rootPinned (L γ δ : ℝ) (LG : LayeredGarden w) (hG : LG.garden.IsPlain)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ) (top : Fin w → ℝ)
    (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (fix : GBranch LG.garden.tree → Option ℝ) (j0 : Fin w) (r : GBranch LG.garden.tree) (hr : r.1 = (j0, []))
    (sv : ℝ) (hfix : fix r = some sv) (u₀ : ℝ) (hsv : sv < u₀) :
    kernelNodeWF L γ δ LG A m (fun b => top b.1.1) s k₀ nroot nfl fix =
      (if sv < top j0 then 1 else 0) *
        kernelNodeWF L γ δ LG A m (fun b => Function.update top j0 u₀ b.1.1) s k₀ nroot nfl fix := by
  have hint : ∀ κ : GenDecoration LG.garden d nroot nfl,
      ∫ τ, (kDomain LG (fun b => top b.1.1) s).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix) =
      (if sv < top j0 then 1 else 0) * ∫ τ, (kDomain LG (fun b => Function.update top j0 u₀ b.1.1) s).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix) := by
    intro κ
    rw [← integral_const_mul]
    refine integral_congr_ae ((ae_fixMeasure_pinned fix hfix).mono fun τ hτ => ?_)
    rw [kDomain_eq_coreTimeDomainW LG hG top s, kDomain_eq_coreTimeDomainW LG hG _ s]
    have key := mem_coreTimeDomainW_rootPinned (fun b => LG.layer b.toNode) top j0 u₀ r hr τ sv hτ hsv
    simp only [Set.indicator]
    by_cases h1 : τ ∈ coreTimeDomainW (fun b => LG.layer b.toNode) top
    · obtain ⟨hlt, h2⟩ := key.1 h1
      rw [if_pos h1, if_pos h2, if_pos hlt, one_mul]
    · rw [if_neg h1]
      by_cases hlt : sv < top j0
      · rw [if_pos hlt, one_mul, if_neg (fun h2 => h1 (key.2 ⟨hlt, h2⟩))]
      · rw [if_neg hlt, zero_mul]
  unfold kernelNodeWF
  have hκ : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) * ((epsDec LG.garden κ.1 : ℂ) *
        (∫ τ, (kDomain LG (fun b => top b.1.1) s).indicator
          (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) *
        ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
      (if sv < top j0 then 1 else 0) * (m (cosetDecoration LG.garden L k₀ κ.1) * ((epsDec LG.garden κ.1 : ℂ) *
        (∫ τ, (kDomain LG (fun b => Function.update top j0 u₀ b.1.1) s).indicator
          (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) *
        ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))) := by
    intro κ; rw [hint κ]; ring
  rw [tsum_congr hκ, tsum_mul_left]
  ring

end WaveTurbulence.Flower.MkSlots
