/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.GluedDecorations

/-! # Centering an actual decoration with a common prescribed root label -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

/-- A typing helper for ordinary gardens and paired trees: subtract the actual
common attachment label at every node. Flower absence is a source carrier fact. -/
def centerGenDecoration {w d : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ))
    (hκ : IsDecoration G κ) (v : Fin d → ℤ) (hr : ∀ j, κ (GNode.root G.tree j) = v)
    (hf : ∀ ℓ, ¬ G.IsFlower ℓ) : GenDecoration G d (fun _ => 0) 0 :=
  ⟨fun a => κ a - v,by
    constructor
    · constructor
      · intro b
        change κ b.toNode-v = (κ (b.child 0)-v)-(κ (b.child 1)-v)+(κ (b.child 2)-v)
        rw [hκ.1 b]
        abel
      · intro ℓ
        exact congrArg (fun k => k-v) (hκ.2 ℓ)
    · constructor
      · intro j
        exact (congrArg (fun k => k-v) (hr j)).trans (sub_self _)
      · intro ℓ hℓ
        exact (hf ℓ hℓ).elim⟩

theorem nativeCouple_noFlower {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) (ℓ : GLeaf (nativeCoupleGarden D hS p).tree) :
    ¬ (nativeCoupleGarden D hS p).IsFlower ℓ := by
  intro h
  have hm := Comb.RootedSubforest.inducedGarden_plain (G := D.garden hS) (nativeCoupleForest D hS p)
    (nativeCoupleForest_closed D hS p) ℓ
  change (nativeCoupleGarden D hS p).mark ℓ = none at hm
  change (nativeCoupleGarden D hS p).mark ℓ = some .equal at h
  rw [h] at hm
  contradiction

theorem decodedTree_noFlower (X : RegChain) (ζ : ℤˣ) (ℓ : GLeaf (decodedTree X ζ).tree) :
    ¬ (decodedTree X ζ).IsFlower ℓ := by
  intro h
  change (decodedTree X ζ).mark ℓ = some .equal at h
  rw [(decodedTree_decodes X ζ).2.1 ℓ] at h
  split_ifs at h
  cases h

end WaveTurbulence.RegRed
