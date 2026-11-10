/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.CollapseData
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.PartnerPullback

/-! # Constructing the embedded paired tree (TARGET L846)

The lower subtree is collapsed to one lone leaf. Every other leaf is mapped
back to the ambient upper-minus-lower set, whose pairing is then pulled back.
-/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} {G : Garden w} {a b : GNode G.tree}

/-- The non-lone leaf map preserves root-relative signs. -/
theorem CollapseData.leafEmbedding_sign (D : CollapseData a b) (x : D.OtherLeaf) :
    nodeSign (fun _ : Fin 1 => G.sign a) x.1.1 =
      nodeSign G.sig (CollapseData.leafEmbedding D x).1 := by
  change pathSign (pathSign (G.sig a.1.1) a.1.2) x.1.1.2 =
    pathSign (G.sig a.1.1) (a.1.2 ++ (collapsedOtherEquiv D.lower_eq x).1)
  have he : (collapsedOtherEquiv D.lower_eq x).1 = x.1.1.2 := rfl
  rw [he]
  exact (pathSign_append _ _ _).symm

/-- The source's complete-pairing condition gives a partner for every non-lone leaf. -/
theorem CollapseData.closed_partner (D : CollapseData a b) (h : IsSubPairedTree G a b) :
    ∀ x : D.OtherLeaf, ∃ y, CollapseData.leafEmbedding D y = G.pair (CollapseData.leafEmbedding D x) := by
  intro x
  exact CollapseData.leafEmbedding_surj D _ (h.2 _ (CollapseData.leafEmbedding_mem D x)).2

/-- The source pairing has no fixed point on the retained non-lone leaves. -/
theorem CollapseData.pair_ne (D : CollapseData a b) (h : IsSubPairedTree G a b) :
    ∀ x : D.OtherLeaf, G.pair (CollapseData.leafEmbedding D x) ≠ CollapseData.leafEmbedding D x :=
  fun x => (h.2 _ (CollapseData.leafEmbedding_mem D x)).1

/-- The actual paired tree embedded between the two source nodes. -/
@[expose] noncomputable def embeddedPairedTree (h : IsSubPairedTree G a b) : Garden 1 :=
  let D := collapseDataOfDesc h.1
  pairedTreeFromLeafEmbedding (collapseAt D.upper D.path) (G.sign a) (collapsedLone D.lower_eq)
    (CollapseData.leafEmbedding D) (CollapseData.closed_partner D h) (CollapseData.pair_ne D h)
    (CollapseData.leafEmbedding_sign D)

end WaveTurbulence.Comb
