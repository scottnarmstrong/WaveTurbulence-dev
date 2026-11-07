/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineIngredientCarrier
public import WaveTurbulence.Foundations.Vine.A.VineFineFamily
/-! The canonical fine family consists exactly of the core ingredients of
the actual chosen splice units, including the converse carrier direction. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
variable {w : ℕ} {LG : LayeredGarden w}

/-- Exact A1 identification with S2a's actual ChainIngredient carrier. -/
theorem fineState_exact_unitIngredients (A : PrimeData LG) (σ : Prescription A.skeleton)
    (c : CLVine A.skeleton) :
    (∃ i, FamilyRealizes (A.fineState σ) i c) ↔
      c.atoms ∈ unitIngredients A.skeleton σ ∧
        ∃ X, IsCoreCLVine A.skeleton X c.atoms c.upper c.lower := by
  have hh := coreFamilyOf_exact (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ) c
  change (∃ i, c.atoms = (coreFamilyOf (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ)).atoms i ∧
    c.upper = (coreFamilyOf (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ)).upper i ∧
    c.lower = ((coreFamilyOf (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ)).placement i).lower) ↔ _
  rw [hh]
  constructor
  · rintro ⟨hc, hcore⟩
    exact ⟨mem_unitIngredients_iff.mpr ⟨c, hc, rfl⟩, hcore⟩
  · rintro ⟨hc, hcore⟩
    obtain ⟨d, hd, he⟩ := mem_unitIngredients_iff.mp hc
    have hdc : d = c := clVine_eq_of_atoms he
    exact ⟨hdc ▸ hd, hcore⟩

end WaveTurbulence.VineA
