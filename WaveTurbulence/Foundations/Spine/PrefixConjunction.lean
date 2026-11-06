/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.PrefixMap
/-! Combining source parameter prefixes without changing the order of constant dependencies. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set

/-- Monotonicity in the two large constants, on their actual source ranges. -/
def LargeConstantMonotone (A : WTParams → Prop) : Prop :=
  ∀ P c₁ c₂, 1 ≤ P.C₁ → 1 ≤ P.C₂ → 0 < P.δ → 2 ≤ P.L → P.C₁ ≤ c₁ → P.C₂ ≤ c₂ →
    A P → A {P with C₁ := c₁, C₂ := c₂}

theorem LargeConstantMonotone.and {A B : WTParams → Prop}
    (hA : LargeConstantMonotone A) (hB : LargeConstantMonotone B) :
    LargeConstantMonotone (fun P => A P ∧ B P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  exact ⟨hA P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h.1, hB P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h.2⟩

theorem prefix_and {A B : WTParams → Prop} (hA : WTPrefix A) (hB : WTPrefix B)
    (hmA : LargeConstantMonotone A) (hmB : LargeConstantMonotone B) :
    WTPrefix (fun P => A P ∧ B P) := by
  intro d hd γ hγ
  obtain ⟨ηA, hηA, hA⟩ := hA d hd γ hγ
  obtain ⟨ηB, hηB, hB⟩ := hB d hd γ hγ
  refine ⟨min ηA ηB, lt_min hηA hηB, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨CA, hCA, νA, hνA, hA⟩ := hA η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  obtain ⟨CB, hCB, νB, hνB, hB⟩ := hB η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨max CA CB, hCA.trans (le_max_left _ _), min νA νB, lt_min hνA hνB, ?_⟩
  intro ν hν
  obtain ⟨δA, hδA, hA⟩ := hA ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δB, hδB, hB⟩ := hB ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δA δB, lt_min hδA hδB, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂A, hC₂A, LA, hLA, hA⟩ := hA δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨C₂B, hC₂B, LB, hLB, hB⟩ := hB δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD htime
  refine ⟨max C₂A C₂B, hC₂A.trans (le_max_left _ _), max LA LB, hLA.trans (le_max_left _ _), ?_⟩
  intro L hL
  constructor
  · exact hmA _ _ _ hCA hC₂A hδ.1 (hLA.trans ((le_max_left _ _).trans hL)) (le_max_left _ _) (le_max_left _ _)
      (hA L ((le_max_left _ _).trans hL))
  · exact hmB _ _ _ hCB hC₂B hδ.1 (hLB.trans ((le_max_right _ _).trans hL)) (le_max_right _ _) (le_max_right _ _)
      (hB L ((le_max_right _ _).trans hL))

end WaveTurbulence.LGSpine
