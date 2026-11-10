/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TypeFamily
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub
/-! AMEND-ST (R61 X4): ANCHORED pair types with profile 1, exempt from `Bounded` and `size`.

The anchors of a garden (design C) are trivial trees `J ⊆ Fin w` with fixed labels; every pair `(ℓ, ℓ')` whose
partner leaf `ℓ'` lies in an anchor tree has profile `1` (`FlowerP1.AnchorOne`), carries no bound (`BoundedAnch`)
and contributes the factor `1` to the leaf size (`toLeafFamilyAnch`, `size_anch_eq`). With no anchors
(`J = ∅`) everything is the current `TypeFamily` data (`toLeafFamilyAnch_empty`, `boundedAnch_empty_iff`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

theorem pairTrees_leaf {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    pairTrees G ℓ.1 = (ℓ.1.1, (G.pair ℓ).1.1) := by
  have he : ∃ ℓ' : GLeaf G.tree, ℓ'.1 = ℓ.1 := ⟨ℓ, rfl⟩
  have hc : he.choose = ℓ := Subtype.ext he.choose_spec
  unfold pairTrees
  rw [dif_pos he, hc]

end WaveTurbulence.LGSpine
