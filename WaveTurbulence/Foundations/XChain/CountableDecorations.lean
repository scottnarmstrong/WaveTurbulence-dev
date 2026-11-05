/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBoundaryDecorations
/-! Countable carriers of integer decorations, used by the independent product-sum identity. -/
public section
namespace WaveTurbulence.Induct

instance instCountableGenDecoration {d w : ℕ} (G : Garden w)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : Countable (GenDecoration G d n nfl) := by
  unfold GenDecoration
  infer_instance

instance instCountableForestDecoration {d w : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) : Countable (ForestDecoration top d n) := by
  unfold ForestDecoration
  infer_instance

end WaveTurbulence.Induct
