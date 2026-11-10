/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HExit
import Mathlib.Tactic

/-! # Leaves and complete pairing inside a set with two exits (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- The LP dart at the parent of a paired leaf. -/
@[expose] def lpDart (G : Garden w) (ℓ : GLeaf G.tree) (hm : G.mark ℓ = none) (hr : ℓ.1.2 ≠ [])
    (hp : (G.pair ℓ).1.2 ≠ []) : GardenDart G :=
  Sum.inr ⟨ℓ, hm, hr, hp⟩

theorem leaf_not_isDesc_branch {G : Garden w} (ℓ : GLeaf G.tree) :
    ∀ n, ∀ b : GBranch G.tree, b.1.2.length = n → ¬ ℓ.toNode.IsDesc b.toNode := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hd
    by_cases he : ℓ.1.2 = b.1.2
    · exact branch_ne_leaf b ℓ (Prod.ext hd.1.symm he.symm)
    · have hb : b.1.2 ≠ [] := by
        intro h0
        obtain ⟨hj, q, hq⟩ : ℓ.1.1 = b.1.1 ∧ ∃ q, ℓ.1.2 ++ q = b.1.2 := hd
        rw [h0] at hq
        exact he (by simpa using (List.append_eq_nil_iff.mp hq).1.trans h0.symm)
      have hd' := isDesc_parent_of_ne (a := ℓ.toNode) (x := b.toNode) hb hd he
      have hlen : (GNode.parent b.toNode hb).1.2.length < n := by
        rw [← hn]
        show b.1.2.dropLast.length < b.1.2.length
        rw [List.length_dropLast]
        have := List.length_pos_of_ne_nil hb; omega
      exact ih _ hlen _ rfl hd'

theorem leaf_valid_of_deg4 {G : Garden w} (ℓ : GLeaf G.tree) (hr : ℓ.1.2 ≠ [])
    (hx : G.molecule.deg (GNode.parent ℓ.toNode hr) = 4) :
    G.mark ℓ = none ∧ (G.pair ℓ).1.2 ≠ [] := by
  have hc := deg4_child G _ hx (ℓ.1.2.getLast hr)
  have key : (GNode.parent ℓ.toNode hr).child (ℓ.1.2.getLast hr) = ℓ.toNode :=
    Mole.parent_child_eq_node ℓ.toNode hr
  rw [key] at hc
  rcases hc with ⟨c, hc⟩ | ⟨ℓ', hℓ', hm, hp⟩
  · exact absurd (congrArg Subtype.val hc) (branch_ne_leaf c ℓ)
  · have : ℓ' = ℓ := Mole.leaf_toNode_injective hℓ'
    subst this
    exact ⟨hm, hp⟩

theorem pv_nonroot {G : Garden w} (f : GBranch G.tree → ℕ) (p : ℕ) {n : GNode G.tree} (hn : n.1.2 ≠ []) :
    LFTwist.branchParentValue G f p n = f (GNode.parent n hn) := by
  unfold LFTwist.branchParentValue
  rw [dif_neg hn]

end WaveTurbulence.LayerCnt
