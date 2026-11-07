/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeIdentity
/-! FLOWER-P7: a couple of kind `L0` with all layers `≤ p` has both roots branching in layer `p`
(the top order of each tree is positive and layers decrease from the root). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

theorem layer_le_root {w : ℕ} (LG : LayeredGarden w) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), b.1.2.length = n →
      ∃ r : GBranch LG.garden.tree, r.1.1 = b.1.1 ∧ r.1.2 = [] ∧ LG.layer b.toNode ≤ LG.layer r.toNode := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb
    by_cases hne : b.1.2 = []
    · exact ⟨b, rfl, hne, le_rfl⟩
    · obtain ⟨b0, hb0⟩ := exists_parent_branch b hne
      obtain ⟨hj, i, hi⟩ := hb0
      have hlen : b0.1.2.length < n := by rw [← hb, hi]; simp
      have hnode : b.toNode = b0.child i := Subtype.ext (Prod.ext hj hi)
      have h1 : LG.layer b.toNode ≤ LG.layer b0.toNode := by
        rw [hnode]; exact LG.isLayering.1 b0 i
      obtain ⟨r, hr1, hr2, hr3⟩ := ih _ hlen b0 rfl
      exact ⟨r, hr1.trans hj.symm, hr2, h1.trans hr3⟩

theorem roots_layer_of_L0 (Q : LayeredGarden 2) (p Ntr : ℕ) (hl : ∀ x, Q.layer x ≤ p)
    (hk : Q.TreeKindOK p Ntr .L0) :
    ∀ j : Fin 2, ∃ b : GBranch Q.garden.tree, b.1 = (j, []) ∧ Q.layer b.toNode = p := by
  intro j
  have hj := (hk j).1
  have hcard : 0 < (Finset.univ.filter fun b : GBranch Q.garden.tree => b.1.1 = j ∧ Q.layer b.toNode = p).card := by
    have : Ntr < Q.topOrder p j := hj
    unfold LayeredGarden.topOrder at this
    omega
  obtain ⟨b0, hb0⟩ := Finset.card_pos.1 hcard
  obtain ⟨hj0, hl0⟩ := (Finset.mem_filter.1 hb0).2
  obtain ⟨r, hr1, hr2, hr3⟩ := layer_le_root Q _ b0 rfl
  refine ⟨r, Prod.ext (hr1.trans hj0) hr2, le_antisymm (hl _) ?_⟩
  rw [← hl0]; exact hr3

end WaveTurbulence.FlowerP7
