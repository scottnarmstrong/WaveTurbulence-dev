/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainEndpointGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairFunction

/-! # Recovering exact local chain pairs from the actual ambient partner -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem chain_pair_mem_of_ambient {w : ℕ} (X : RegChain) (ζ : ℤˣ) (G : Garden w)
    (a : Address w) (x y : Address 1) (ℓ q : GLeaf G.tree)
    (hx : x.2 ∈ (X.plug ζ .leaf).leaves) (hn : x.2 ≠ X.lonePath)
    (hℓ : ℓ.1 = addrExt a x.2) (hq : q.1 = addrExt a y.2) (hpair : G.pair ℓ = q)
    (hP : ∀ p ∈ X.pairsAt ζ a, p ∈ sourcePairs G) :
    (x,y) ∈ symmPairs (X.pairsAt ζ (0,[])) := by
  have hxP : x ∈ pairEndpoints (X.pairsAt ζ (0,[])) := by
    have hm := (leafAddresses_one_root (X.plug ζ .leaf) x).mpr hx
    rw [chain_leafAddresses,leafAddresses_leaf,Finset.mem_union,Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact (hn (congrArg (fun z : Address 1 => z.2) hm)).elim
  obtain ⟨p,hp,he⟩ := (mem_pairEndpoints_iff _ _).mp hxP
  let f : Address 1 → Address w := fun z => addrExt a z.2
  have hmap : X.pairsAt ζ a = (X.pairsAt ζ ((0 : Fin 1),[])).map (fun z => (f z.1,f z.2)) := by
    have hh := chain_pairsAt_map X f (by intro z r; simp [f,addrExt,List.append_assoc]) ζ (0,[])
    simpa only [f,addrExt,List.nil_append,List.append_nil] using hh
  have hm : (f p.1,f p.2) ∈ sourcePairs G := hP _ (by rw [hmap]; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  obtain ⟨u,v,hu,hv,huv⟩ := sourcePairs_actual_endpoints G _ hm
  rcases he with he | he
  · have hlu : ℓ = u := Subtype.ext (hℓ.trans ((congrArg f he).trans hu.symm))
    have hqv : q = v := hpair.symm.trans ((congrArg G.pair hlu).trans huv)
    have hy : y = p.2 := Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left (by
      have hh := hq.symm.trans ((congrArg Subtype.val hqv).trans hv)
      exact congrArg (fun z : Address w => z.2) hh))
    rw [he,hy]
    exact (mem_symmPairs_iff _ _).mpr (Or.inl hp)
  · have hlv : ℓ = v := Subtype.ext (hℓ.trans ((congrArg f he).trans hv.symm))
    have hqu : q = u := by rw [← hpair,hlv,← huv,G.pair_pair]
    have hy : y = p.1 := Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left (by
      have hh := hq.symm.trans ((congrArg Subtype.val hqu).trans hu)
      exact congrArg (fun z : Address w => z.2) hh))
    rw [he,hy]
    exact (mem_symmPairs_iff _ _).mpr (Or.inr hp)

end WaveTurbulence.Reg.Skeleton
