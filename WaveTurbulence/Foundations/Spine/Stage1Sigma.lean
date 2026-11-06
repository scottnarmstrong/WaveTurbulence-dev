/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Interface
/-! The sigma-indicator partition lemma (RULINGS R19 (1), TARGET L1950): if the restrictions `sel i`
(`i` in a finite index set) partition the decorations of a garden, and the decoration sum of the kernel
converges, then the restricted decoration sums add up to the full one. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped Classical

theorem kernelLeavesTerm_sum_sel {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) {ι : Type*} (t : Finset ι)
    (sel : ι → GenDecoration LG.garden d nroot nfl → Prop)
    (hpart : ∀ κ, ∃! i, i ∈ t ∧ sel i κ)
    (hsum : Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      kernelLeavesTerm L γ δ LG H up s k₀ κ) :
    ∑ i ∈ t, kernelLeavesSel L γ δ LG H up s k₀ nroot nfl (sel i) =
      kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  have hsel : ∀ i, Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      if sel i κ then kernelLeavesTerm L γ δ LG H up s k₀ κ else 0 := by
    intro i
    have := hsum.indicator {κ | sel i κ}
    refine this.congr fun κ => ?_
    by_cases h : sel i κ <;> simp [Set.indicator, h]
  unfold kernelLeavesSel kernelLeaves
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hsel i)]
  congr 1
  refine tsum_congr fun κ => ?_
  obtain ⟨i0, ⟨hi0, hs0⟩, huniq⟩ := hpart κ
  rw [Finset.sum_eq_single i0]
  · simp [hs0, kernelLeavesTerm]
  · intro j hj hne
    have : ¬ sel j κ := fun h => hne (huniq j ⟨hj, h⟩)
    simp [this]
  · intro h; exact absurd hi0 h

/-- The sigma-indicator partition lemma for a leaf-modified family: the restricted family values over a
partition of the decorations add up to the family value. -/
theorem LeafFamily.sum_valueSel {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) {ι : Type*}
    (t : Finset ι) (sel : ι → GenDecoration LG.garden P.d roots 0 → Prop)
    (hpart : ∀ κ, ∃! i, i ∈ t ∧ sel i κ)
    (hsum : ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ) :
    ∑ i ∈ t, F.valueSel tt base roots LG (sel i) = F.value tt base roots LG := by
  unfold LeafFamily.valueSel LeafFamily.value
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact kernelLeavesTerm_sum_sel P.L P.γ P.δ LG (F.H LG j) _ 0 base roots 0 t sel hpart (hsum j)

end WaveTurbulence.LGSpine
