/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SplitTree

/-!
# Transport of slices and leaf profiles along the layer splitting

The spine's explicit approximation (`LeafApp.coherentCouple`, `LeafApp.coherentTree`) reads the slices
`SourceApp.chainSlice` and the profile transport `LeafApp.sliceAddress` on the original carrier. Along
the one-step splittings:

* `chainSlice_congr_layers`, `sliceAddress_congr_layers`: both depend on the carrier only through the layers
  at the chain addresses;
* `sliceAddress_append_skip`: removed blocks in other layers are skipped;
* `sliceAddress_botAddr`: relabelling along a bottom address map;
* `kernelLeaves_congr_profiles`: a leafwise kernel reads its profiles only at its input leaves;
* `LeafApp.tree_nil`: the empty slice has leading term `1`.
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {w v : ℕ}

theorem sliceAddress_pair (LG : LayeredGarden w) (a : Fin w × Path) (r : ℕ) (m : MiniTreeCode)
    (Qr Qg : RegCpl) (inner rest : RegChain) (path : Path) :
    LeafApp.sliceAddress LG a r (.pair m Qr Qg inner rest) path =
      if layerAt LG a = r then
        if ([m.c] ++ inner.lonePath ++ [m.lone]).IsPrefix path then
          LeafApp.sliceAddress LG (nextAddr a m inner) r rest
            (path.drop ([m.c] ++ inner.lonePath ++ [m.lone]).length)
        else addrExt a path
      else LeafApp.sliceAddress LG (nextAddr a m inner) r rest path := rfl

/-- All top-level pairs of the chain are in layers other than `r`. -/
def TopNe (LG : LayeredGarden w) (r : ℕ) : (Fin w × Path) → RegChain → Prop
  | _, .nil => True
  | a, .pair m _ _ inner rest => layerAt LG a ≠ r ∧ TopNe LG r (nextAddr a m inner) rest

/-- **Removed blocks in other layers are skipped by the profile transport.** -/
theorem sliceAddress_append_skip (LG : LayeredGarden w) (r : ℕ) :
    ∀ (R X : RegChain) (a : Fin w × Path) (path : Path), TopNe LG r a R →
      LeafApp.sliceAddress LG a r (appendChain R X) path =
        LeafApp.sliceAddress LG (addrExt a R.lonePath) r X path
  | .nil, X, a, path, _ => by simp [appendChain, RegChain.lonePath, addrExt]
  | .pair m Qr Qg inner rest, X, a, path, ⟨hne, hR⟩ => by
    show LeafApp.sliceAddress LG a r (.pair m Qr Qg inner (appendChain rest X)) path = _
    rw [sliceAddress_pair, ite_eq_right hne, sliceAddress_append_skip LG r rest X _ path hR]
    simp only [nextAddr, addrExt_append, RegChain.lonePath, List.append_assoc]

theorem chainSlice_append_skip (LG : LayeredGarden w) (r : ℕ) :
    ∀ (R X : RegChain) (a : Fin w × Path), TopNe LG r a R →
      SourceApp.chainSlice LG a r (appendChain R X) =
        SourceApp.chainSlice LG (addrExt a R.lonePath) r X
  | .nil, X, a, _ => by simp [appendChain, RegChain.lonePath, addrExt]
  | .pair m Qr Qg inner rest, X, a, ⟨hne, hR⟩ => by
    show SourceApp.chainSlice LG a r (.pair m Qr Qg inner (appendChain rest X)) = _
    rw [chainSlice_pair, ite_eq_right hne, chainSlice_append_skip LG r rest X _ hR]
    simp only [nextAddr, addrExt_append, RegChain.lonePath, List.append_assoc]

/-- A leafwise kernel reads its profiles only at its input leaves. -/
theorem kernelLeaves_congr_profiles {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H H' : LeafProfiles w d) (hH : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = H' ℓ.1)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl = kernelLeaves L γ δ LG H' up s k₀ nroot nfl := by
  unfold kernelLeaves
  congr 1
  refine tsum_congr fun κ => ?_
  congr 1
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  rw [hH ℓ hℓ]

/-- **The empty slice has leading term `1`.** -/
theorem LeafApp.tree_nil {d : ℕ} (δ r : ℝ) (H : LeafProfiles 1 d) (ζ : ℤˣ) (t s : ℝ) (k : Mom d) :
    LeafApp.tree δ r H .nil ζ t s k = 1 := by
  have hs : specialSets (RegChain.nil.treeLinks ζ) = {∅} := by
    simp [specialSets, chosenSet, RegChain.treeLinks, RegChain.linksAt, IsSpecialSet]
  simp [LeafApp.tree, RegChain.dominant, RegChain.size, hs, zetaOfTrees, RegChain.plug,
    TTree.branching, specialWeight, RegChain.JBtree, RegChain.JBchain, LeafApp.chainNstar]

end WaveTurbulence.PL234
