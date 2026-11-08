/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Analytic
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.Bs2Vanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar1

/-! # V5W-0, row 0a (part 2): time structure of the incoherent rows

Weighted copies of main's `VineEstS4c.KQstar_eq_zero_of_le_plus/_minus`, `KTstar_eq_zero_of_le` (vanishing below a
branching layer: empty time domain) and `W2.KQstar_const_above`, `KTstar_const_above` (constancy above the top layer
plus one), for `coupleLeavesTop`/`treeLeavesTop`; measurability in the clocks from row 0a's continuity.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1W MeasureTheory

section Vanish
variable {w d : ℕ}

theorem kernelLeavesW_eq_zero_of_kDomain_empty (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (hD : kDomain LG up s = ∅) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = 0 := by
  unfold kernelLeavesW
  have hz : ∀ k' : GNode LG.garden.tree → Mom d,
      phaseIntegral (d := d) L γ δ LG.garden (kDomain LG up s) s k' = 0 := by
    intro k'
    simp [phaseIntegral, hD]
  simp [hz]

/-- The incoherent couple row vanishes if the `+` tree has a branching node of layer `≥ t`. -/
theorem coupleLeavesTop_eq_zero_of_le_plus (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) (b : GBranch LG.garden.tree) (hb : b.1.1 = 0)
    (h : t ≤ (LG.layer b.toNode : ℝ)) : coupleLeavesTop L γ δ p g q q' LG H t s k = 0 := by
  unfold coupleLeavesTop
  refine kernelLeavesW_eq_zero_of_kDomain_empty L γ δ LG H _ 0 k _ _ _
    (VineEstS4c.kDomain_eq_empty_of_up_le LG _ 0 b ?_)
  simpa [hb] using h

/-- The incoherent couple row vanishes if the `−` tree has a branching node of layer `≥ s`. -/
theorem coupleLeavesTop_eq_zero_of_le_minus (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) (b : GBranch LG.garden.tree) (hb : b.1.1 ≠ 0)
    (h : s ≤ (LG.layer b.toNode : ℝ)) : coupleLeavesTop L γ δ p g q q' LG H t s k = 0 := by
  unfold coupleLeavesTop
  refine kernelLeavesW_eq_zero_of_kDomain_empty L γ δ LG H _ 0 k _ _ _
    (VineEstS4c.kDomain_eq_empty_of_up_le LG _ 0 b ?_)
  simpa [hb] using h

/-- The incoherent tree row vanishes if a branching node has layer `≥ t`. -/
theorem treeLeavesTop_eq_zero_of_le (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) (b : GBranch LG.garden.tree) (h : t ≤ (LG.layer b.toNode : ℝ)) :
    treeLeavesTop L γ δ p g q LG H t s k = 0 := by
  unfold treeLeavesTop
  exact kernelLeavesW_eq_zero_of_kDomain_empty L γ δ LG H _ s k _ _ _
    (VineEstS4c.kDomain_eq_empty_of_up_le LG _ s b h)

end Vanish

section Const
variable {w d : ℕ}

theorem kernelLeavesW_up_congr (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up up' : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (h : ∀ b, ((LG.layer b.toNode : ℝ) + 1 ≤ up b ∧ (LG.layer b.toNode : ℝ) + 1 ≤ up' b) ∨ up b = up' b) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeavesW L γ δ LG H up' s k₀ nroot nfl m := by
  unfold kernelLeavesW
  rw [VineEstS5C.P4.W2.kDomain_congr_up LG up up' s h]

/-- The incoherent couple row is constant in `t` beyond the top layer of the `+` tree plus one. -/
theorem coupleLeavesTop_const_above (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q₁ q₂ : ℕ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) {q : ℕ} (hlay : ∀ b : GBranch LG.garden.tree, b.1.1 = 0 → LG.layer b.toNode ≤ q)
    {t t' : ℝ} (ht : (q : ℝ) + 1 ≤ t) (ht' : (q : ℝ) + 1 ≤ t') (s : ℝ) (k : Mom d) :
    coupleLeavesTop L γ δ p g q₁ q₂ LG H t s k = coupleLeavesTop L γ δ p g q₁ q₂ LG H t' s k := by
  unfold coupleLeavesTop
  refine kernelLeavesW_up_congr L γ δ LG H _ _ 0 k _ 0 _ fun b => ?_
  by_cases hb : b.1.1 = 0
  · left
    have := hlay b hb
    simp only [hb, ite_true]
    constructor <;> linarith [(show ((LG.layer b.toNode : ℕ) : ℝ) ≤ q from by exact_mod_cast this)]
  · right; simp [hb]

/-- The incoherent tree row is constant in `t` beyond the top layer plus one. -/
theorem treeLeavesTop_const_above (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q₁ : ℕ) (LG : LayeredGarden 1)
    (H : LeafProfiles 1 d) {q : ℕ} (hlay : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode ≤ q)
    {t t' : ℝ} (ht : (q : ℝ) + 1 ≤ t) (ht' : (q : ℝ) + 1 ≤ t') (s : ℝ) (k : Mom d) :
    treeLeavesTop L γ δ p g q₁ LG H t s k = treeLeavesTop L γ δ p g q₁ LG H t' s k := by
  unfold treeLeavesTop
  refine kernelLeavesW_up_congr L γ δ LG H _ _ s k _ 0 _ fun b => ?_
  left
  have := hlay b
  constructor <;> linarith [(show ((LG.layer b.toNode : ℕ) : ℝ) ≤ q from by exact_mod_cast this)]

end Const

section Measurable
variable {d : ℕ}

/-- The incoherent couple row is measurable in its two clocks (from its continuity). -/
theorem measurable_coupleLeavesTop_time (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q q' : ℕ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain) (k : Mom d) (cψ : ℝ) (hc : 1 ≤ cψ)
    (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Measurable (fun ts : Fin 2 → ℝ => coupleLeavesTop L γ δ p g q q' LG (layerProfiles LG F) (ts 0) (ts 1) k) :=
  (continuous_coupleLeavesTop_time L γ δ p g q q' F LG hplain k cψ hc hg hF).measurable

/-- The incoherent tree row is measurable in its two clocks (from its continuity). -/
theorem measurable_treeLeavesTop_time (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden) (k : Mom d) (cψ : ℝ) (hc : 1 ≤ cψ)
    (hg : ∀ x, ‖g x‖ ≤ cψ)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Measurable (fun ts : Fin 2 → ℝ => treeLeavesTop L γ δ p g q LG (layerProfiles LG F) (ts 0) (ts 1) k) :=
  (continuous_treeLeavesTop_time L γ δ p g q F LG hT k cψ hc hg hF).measurable

end Measurable

end WaveTurbulence.Flower.V5W
