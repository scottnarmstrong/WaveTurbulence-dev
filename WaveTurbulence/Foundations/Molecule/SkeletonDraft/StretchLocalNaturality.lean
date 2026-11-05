/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchDescendantExtension
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainEndpointGeometry
public import WaveTurbulence.Foundations.RegStruct.LocalPairNaturality

/-! # Local pair transport below and away from a prefix insertion -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_respectsAt_below {w : ℕ} (a d : Address w) (p : Path) (hd : Below a d) :
    RespectsAt (stretch a p) d := fun q => stretch_addrExt_of_below a d p q hd

theorem stretch_respectsAt_incomp {w : ℕ} (a d : Address w) (p : Path) (hd : IncompAddr a d) :
    RespectsAt (stretch a p) d := by
  intro q
  have hq : ¬ Below a (addrExt d q) :=
    (hd.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)).1
  rw [stretch_outside a p _ hq,stretch_outside a p d hd.1]

theorem chain_pairs_image_fixed_below_lone {w : ℕ} (X : RegChain) (ζ : ℤˣ)
    (root a : Address w) (p : Path) (ha : Below (addrExt root X.lonePath) a) :
    ((X.pairsAt ζ root).toFinset.image (fun z => (stretch a p z.1,stretch a p z.2))) =
      (X.pairsAt ζ root).toFinset := by
  classical
  calc
    _ = (X.pairsAt ζ root).toFinset.image id := by
      apply Finset.image_congr
      intro z hz
      have hm := List.mem_toFinset.mp hz
      have h1 : ¬ Below a z.1 := fun h =>
        chain_endpoint_not_below_lone X ζ root z.1 ((mem_pairEndpoints_iff _ _).mpr ⟨z,hm,Or.inl rfl⟩)
          (below_trans ha h)
      have h2 : ¬ Below a z.2 := fun h =>
        chain_endpoint_not_below_lone X ζ root z.2 ((mem_pairEndpoints_iff _ _).mpr ⟨z,hm,Or.inr rfl⟩)
          (below_trans ha h)
      exact Prod.ext (stretch_outside _ _ _ h1) (stretch_outside _ _ _ h2)
    _ = _ := Finset.image_id

end WaveTurbulence.Reg.Skeleton
