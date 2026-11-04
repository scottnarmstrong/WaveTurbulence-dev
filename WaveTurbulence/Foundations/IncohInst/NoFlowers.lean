/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.DecorationEquivalences

/-! # Decoded regular couples and paired trees have no flowers -/

public section
namespace WaveTurbulence.IncohInst

/-- No flower occurs in the plain source couple. -/
theorem couple_noFlowers {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    ∀ ℓ, ¬ G.IsFlower ℓ := by
  intro ℓ
  simp only [Garden.IsFlower, hQ.1.1 ℓ]
  decide

/-- A decoded paired tree has only its lower-marked lone leaf, never an equal-marked flower. -/
theorem tree_noFlowers {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    ∀ ℓ, ¬ G.IsFlower ℓ := by
  intro ℓ
  rw [Garden.IsFlower, hX.2.1 ℓ]
  split_ifs <;> decide

end WaveTurbulence.IncohInst
