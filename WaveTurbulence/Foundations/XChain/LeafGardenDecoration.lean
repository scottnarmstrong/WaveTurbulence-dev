/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafForest
/-! Decorations of a plain zero-order garden are uniquely its root labels, when paired labels match. -/
@[expose] public section
namespace WaveTurbulence.Induct

def LeafRootMatched {w d : ℕ} (G : Garden w) (n : Fin w → (Fin d → ℤ)) : Prop :=
  ∀ l : GLeaf G.tree, n l.1.1 = n (G.pair l).1.1

theorem leafGenDecoration_val {w d : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (κ : GenDecoration G d n nfl)
    (a : GNode G.tree) : κ.1 a = n a.1.1 :=
  (congrArg κ.1 (leafForest_node_eq_root G.tree ht a)).trans (κ.2.2.1 a.1.1)

theorem leafRootMatched_of_decoration {w d : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (κ : GenDecoration G d n nfl) : LeafRootMatched G n := by
  intro l
  exact (leafGenDecoration_val G ht n nfl κ l.toNode).symm.trans
    ((κ.2.1.2 l).trans (leafGenDecoration_val G ht n nfl κ (G.pair l).toNode))

noncomputable def leafGenDecoration {w d : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf)
    (hplain : G.IsPlain) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hm : LeafRootMatched G n) : GenDecoration G d n nfl := by
  haveI := leafForest_no_branch G.tree ht
  refine ⟨fun a => n a.1.1, ⟨fun b => isEmptyElim b, hm⟩, fun _ => rfl, ?_⟩
  intro l hl
  have he := (hplain l).symm.trans hl
  cases he

theorem leafGenDecoration_subsingleton {w d : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : Subsingleton (GenDecoration G d n nfl) := by
  refine ⟨fun a b => Subtype.ext (funext (fun u => ?_))⟩
  exact (leafGenDecoration_val G ht n nfl a u).trans (leafGenDecoration_val G ht n nfl b u).symm

end WaveTurbulence.Induct
