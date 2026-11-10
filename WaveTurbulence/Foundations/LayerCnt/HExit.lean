/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Deg4
public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering
import Mathlib.Tactic

/-! # A set of atoms with two exit darts (TARGET layervine, L1531: the group `H` of vines (V)–(VIII))

`ExitData G K d1 d2`: `K` is a set of degree-four atoms whose only darts leading out of `K` are `d1` and `d2`.
This file proves the structural consequences used in the exit lemma: every atom of `K` descends from the top of a
parent-exit, and descendants of a top lie in `K` unless a child exit is used.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- The atoms `K` have degree four and the only darts leaving `K` are `d1` and `d2`. -/
structure ExitData (G : Garden w) (K : Finset (GBranch G.tree)) (d1 d2 : GardenDart G) : Prop where
  deg4 : ∀ x ∈ K, G.molecule.deg x = 4
  ex : ∀ d, G.molecule.atom d ∈ K → G.molecule.atom (G.molecule.mate d) ∉ K → d = d1 ∨ d = d2

/-- The parent dart of a non-root branching node. -/
@[expose] def upDart (G : Garden w) (c : GBranch G.tree) (hc : c.1.2 ≠ []) : GardenDart G :=
  Sum.inl (⟨c, hc⟩, false)

/-- The child dart at the parent of a non-root branching node. -/
@[expose] def downDart (G : Garden w) (c : GBranch G.tree) (hc : c.1.2 ≠ []) : GardenDart G :=
  Sum.inl (⟨c, hc⟩, true)

namespace ExitData
variable {G : Garden w} {K : Finset (GBranch G.tree)} {d1 d2 : GardenDart G}

/-- Every atom of `K` descends from the top of a parent exit. -/
theorem exit_tops (h : ExitData G K d1 d2) :
    ∀ x ∈ K, ∃ (c : GBranch G.tree) (hc : c.1.2 ≠ []),
      (upDart G c hc = d1 ∨ upDart G c hc = d2) ∧ c.toNode.IsDesc x.toNode := by
  have key : ∀ n, ∀ x : GBranch G.tree, x.1.2.length = n → x ∈ K →
      ∃ (c : GBranch G.tree) (hc : c.1.2 ≠ []),
        (upDart G c hc = d1 ∨ upDart G c hc = d2) ∧ c.toNode.IsDesc x.toNode := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn hx
      have hxr := deg4_nonroot G x (h.deg4 x hx)
      by_cases hp : GNode.parent x.toNode hxr ∈ K
      · have hlen : (GNode.parent x.toNode hxr).1.2.length < n := by
          rw [← hn]
          show x.1.2.dropLast.length < x.1.2.length
          rw [List.length_dropLast]
          have := List.length_pos_of_ne_nil hxr; omega
        obtain ⟨c, hc, hcd, hdesc⟩ := ih _ hlen _ rfl hp
        exact ⟨c, hc, hcd, hdesc.trans (parent_isDesc x.toNode hxr)⟩
      · refine ⟨x, hxr, h.ex _ hx hp, GNode.isDesc_refl _⟩
  intro x hx
  exact key _ x rfl hx

/-- A branching child of an atom of `K` lies in `K`, unless the child dart is an exit. -/
theorem child_mem (h : ExitData G K d1 d2) {c : GBranch G.tree} (hc : c.1.2 ≠ [])
    (hp : GNode.parent c.toNode hc ∈ K) : c ∈ K ∨ downDart G c hc = d1 ∨ downDart G c hc = d2 := by
  by_cases hcK : c ∈ K
  · exact Or.inl hcK
  · exact Or.inr (h.ex _ hp hcK)

end ExitData

end WaveTurbulence.LayerCnt
