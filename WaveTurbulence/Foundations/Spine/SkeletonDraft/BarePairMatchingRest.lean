/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainEndpointGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Literal matching split between a bare pair's initial context and remaining chain -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem bare_pair_pairsAt_rest {w : ℕ} (m : MiniTreeCode) (X Y : RegChain) (ζ : ℤˣ) (a : Address w) :
    ((RegChain.pair m .triv .triv X Y).pairsAt ζ a).toFinset =
      ((RegChain.pair m .triv .triv X .nil).pairsAt ζ a).toFinset ∪
        (Y.pairsAt ζ (addrExt a ([m.c] ++ X.lonePath ++ [m.lone]))).toFinset := by
  have hζ := slotSign_lone m ζ
  simp only [RegChain.pairsAt,hζ,List.toFinset_append,List.append_nil]

theorem bare_pair_initial_pairs_fixed_by_rest {w : ℕ} (m : MiniTreeCode) (X : RegChain)
    (ζ : ℤˣ) (a : Address w) (p : Pair w)
    (hp : p ∈ (RegChain.pair m .triv .triv X .nil).pairsAt ζ a) (q : Path) :
    (stretch (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])) q p.1,
      stretch (addrExt a ([m.c] ++ X.lonePath ++ [m.lone])) q p.2) = p := by
  have hpath : (RegChain.pair m .triv .triv X .nil).lonePath = [m.c] ++ X.lonePath ++ [m.lone] := by
    simp [RegChain.lonePath]
  have h1 := chain_endpoint_not_below_lone (RegChain.pair m .triv .triv X .nil) ζ a p.1
    ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩)
  have h2 := chain_endpoint_not_below_lone (RegChain.pair m .triv .triv X .nil) ζ a p.2
    ((mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩)
  rw [hpath] at h1 h2
  exact Prod.ext (stretch_outside _ q _ h1) (stretch_outside _ q _ h2)

end WaveTurbulence.Reg.Skeleton
