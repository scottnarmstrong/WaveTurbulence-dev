/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Carrier

/-! # Exact oriented-pair transport under signed leaf embeddings

The hypotheses are the literal sign, address and involution compatibility data
of a leaf embedding. No regularity, skeleton or reconstruction theorem is used.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Canonical oriented pairs map exactly onto the ambient pairs in the embedded leaf family. -/
theorem sourcePairs_image_of_embedding {v w : ℕ} (S : Garden v) (G : Garden w)
    (f : GLeaf S.tree ↪ GLeaf G.tree) (g : Address v → Address w)
    (hs : ∀ ℓ, nodeSign S.sig ℓ.1 = nodeSign G.sig (f ℓ).1)
    (hv : ∀ ℓ, (f ℓ).1 = g ℓ.1)
    (hp : ∀ ℓ, f (S.pair ℓ) = G.pair (f ℓ)) :
    (sourcePairs S).image (fun p => (g p.1,g p.2)) =
      (sourcePairs G).filter (fun p => ∃ ℓ : GLeaf S.tree, (f ℓ).1 = p.1) := by
  classical
  ext p
  constructor
  · intro hmem
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hq
    have hpos := (Finset.mem_filter.mp hℓ).2
    have hposG : nodeSign G.sig (f ℓ).1 = 1 := (hs ℓ).symm.trans hpos
    have h0 : g ℓ.1 = (f ℓ).1 := (hv ℓ).symm
    have h1 : g (S.pair ℓ).1 = (G.pair (f ℓ)).1 :=
      (hv (S.pair ℓ)).symm.trans (congrArg (fun x : GLeaf G.tree => x.1) (hp ℓ))
    change (g ℓ.1,g (S.pair ℓ).1) ∈ _
    rw [h0,h1]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨f ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hposG⟩,rfl⟩,?_⟩
    exact ⟨ℓ,rfl⟩
  · intro hmem
    obtain ⟨hq,hrange⟩ := Finset.mem_filter.mp hmem
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ℓ,hval⟩ := hrange
    have hf : f ℓ = y := Subtype.ext hval
    have hpos := (Finset.mem_filter.mp hy).2
    have hspos : nodeSign S.sig ℓ.1 = 1 :=
      (hs ℓ).trans ((congrArg (fun z : GLeaf G.tree => nodeSign G.sig z.1) hf).trans hpos)
    apply Finset.mem_image.mpr
    refine ⟨(ℓ.1,(S.pair ℓ).1),Finset.mem_image.mpr
      ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hspos⟩,rfl⟩,?_⟩
    apply Prod.ext
    · exact (hv ℓ).symm.trans (congrArg (fun z : GLeaf G.tree => z.1) hf)
    · exact (hv (S.pair ℓ)).symm.trans
        (congrArg (fun z : GLeaf G.tree => z.1) ((hp ℓ).trans (congrArg G.pair hf)))

end WaveTurbulence.Reg.Skeleton
