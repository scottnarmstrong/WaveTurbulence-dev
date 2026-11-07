/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Par1
public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC11
public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT7
import Mathlib.Tactic

/-!
# Coherence of a slot is transported along native layer pins
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- Coherence of a regular tree's links transports along layer equalities at its nodes. -/
theorem cohOn_chain_transport {LG LG' : LayeredGarden w} (X : RegChain) (ζ : ℤˣ) (a a' : Address w)
    (hpin : ∀ r ∈ (X.plug ζ .leaf).nodes, layerAt LG' (addrExt a' r) = layerAt LG (addrExt a r)) :
    CohOn LG (X.linksAt ζ a) → CohOn LG' (X.linksAt ζ a') := by
  intro hc
  have hl : X.linksAt ζ a' = (X.linksAt ζ a).map (fun p => (treePort a a' p.1, treePort a a' p.2)) := by
    have := chain_linksAt_map_local X (treePort a a') a (treePort_respects a a') ζ
    rwa [treePort_self] at this
  have hall : pairEndpoints (X.linksAt ζ a) = branchAddresses (X.plug ζ .leaf) a := by
    rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty]
  have hend : ∀ z ∈ pairEndpoints (X.linksAt ζ a), layerAt LG' (treePort a a' z) = layerAt LG z := by
    intro z hz
    rw [hall] at hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    rw [treePort_ext]
    exact hpin r (TTree.branching_subset_nodes _ hr)
  rw [hl]
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have e1 := hend q0.1 ((mem_pairEndpoints_iff _ _).mpr ⟨q0, hq0, Or.inl rfl⟩)
  have e2 := hend q0.2 ((mem_pairEndpoints_iff _ _).mpr ⟨q0, hq0, Or.inr rfl⟩)
  exact e1.trans ((hc q0 hq0).trans e2.symm)

/-- Coherence of a regular couple's links transports along layer equalities at its nodes. -/
theorem cohOn_couple_transport {LG LG' : LayeredGarden w} (Q : RegCpl) (a b a' b' : Address w)
    (hab : Indep a b)
    (hpa : ∀ r ∈ Q.trees.1.nodes, layerAt LG' (addrExt a' r) = layerAt LG (addrExt a r))
    (hpb : ∀ r ∈ Q.trees.2.nodes, layerAt LG' (addrExt b' r) = layerAt LG (addrExt b r)) :
    CohOn LG (Q.linksAt a b) → CohOn LG' (Q.linksAt a' b') := by
  intro hc
  have ha : couplePort a b a' b' a = a' := by simpa [addrExt] using couplePort_a a b a' b' hab []
  have hb : couplePort a b a' b' b = b' := by simpa [addrExt] using couplePort_b a b a' b' hab []
  have hra : RespectsAt (couplePort a b a' b') a := by
    intro q; rw [couplePort_a a b a' b' hab, ha]
  have hrb : RespectsAt (couplePort a b a' b') b := by
    intro q; rw [couplePort_b a b a' b' hab, hb]
  have hl : Q.linksAt a' b' = (Q.linksAt a b).map
      (fun p => (couplePort a b a' b' p.1, couplePort a b a' b' p.2)) := by
    have := couple_linksAt_map_local Q (couplePort a b a' b') a b hra hrb
    rwa [ha, hb] at this
  have hall := couple_branchAddresses Q a b
  have hend : ∀ z ∈ pairEndpoints (Q.linksAt a b), layerAt LG' (couplePort a b a' b' z) = layerAt LG z := by
    intro z hz
    rw [← hall] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
      rw [couplePort_a a b a' b' hab]
      exact hpa r (TTree.branching_subset_nodes _ hr)
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
      rw [couplePort_b a b a' b' hab]
      exact hpb r (TTree.branching_subset_nodes _ hr)
  rw [hl]
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  have e1 := hend q0.1 ((mem_pairEndpoints_iff _ _).mpr ⟨q0, hq0, Or.inl rfl⟩)
  have e2 := hend q0.2 ((mem_pairEndpoints_iff _ _).mpr ⟨q0, hq0, Or.inr rfl⟩)
  exact e1.trans ((hc q0 hq0).trans e2.symm)

end WaveTurbulence.Stage1
