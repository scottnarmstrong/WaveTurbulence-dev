/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT7
import Mathlib.Tactic

/-!
# Garden-level outside agreement for a couple update of reconstruction data

For reconstruction data `F` with a non-trivial couple at `q`, the gardens of `F` and of `F.eraseCouple q`
agree (nodes, leaves, leaf partners) outside the two regions at the roots of the couple.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- A garden carries the layering that is identically zero. -/
@[expose] def zeroLayered (G : Garden w) : LayeredGarden w :=
  ⟨G, fun _ => 0, ⟨fun _ _ => le_rfl, fun _ => rfl⟩⟩

theorem couple_outside_facts (G : Garden w) {a b : GNode G.tree} (h : Comb.IsSubCouple G a b)
    (N : Garden w) (hN : N = collapseCoupleGarden h) :
    (∀ z : Fin w × Path, ¬ InRegion a.1 b.1 z →
      (z.2 ∈ (G.tree z.1).nodes ↔ z.2 ∈ (N.tree z.1).nodes)) ∧
    (∀ z : Fin w × Path, ¬ InRegion a.1 b.1 z →
      (z.2 ∈ (G.tree z.1).leaves ↔ z.2 ∈ (N.tree z.1).leaves)) ∧
    (∀ (ℓ : GLeaf G.tree) (ℓ' : GLeaf N.tree), ¬ InRegion a.1 b.1 ℓ.1 → ℓ.1 = ℓ'.1 →
      (G.pair ℓ).1 = (N.pair ℓ').1) := by
  subst hN
  have ho : ∀ z : Fin w × Path, ¬ InRegion a.1 b.1 z → ¬ Below a.1 z ∧ ¬ Below b.1 z := fun z hz =>
    ⟨fun ht => hz (Or.inl ((under_iff_below a.1 z).mpr ht)),
      fun ht => hz (Or.inr ((under_iff_below b.1 z).mpr ht))⟩
  refine ⟨fun z hz => (coupleCollapse_node_outside (zeroLayered G) h z (ho z hz).1 (ho z hz).2).symm,
    fun z hz => (coupleCollapse_leaf_outside (zeroLayered G) h z (ho z hz).1 (ho z hz).2).symm,
    fun ℓ ℓ' hz he => coupleCollapse_pair_outside (zeroLayered G) h ℓ ℓ' (ho ℓ.1 hz).1 (ho ℓ.1 hz).2 he⟩

end WaveTurbulence.Stage1
