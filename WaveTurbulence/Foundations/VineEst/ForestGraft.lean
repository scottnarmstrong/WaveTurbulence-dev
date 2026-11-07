/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.GraftLeaves
/-! The concrete forest leaf reindexing and its sign identity for the garden grafting map. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open TTree

def graftForest {w : ℕ} (top : Fin w → TTree) (f : Fin w → TTree.Path → TTree) : Fin w → TTree :=
  fun j => graftTree (top j) (f j)

abbrev AttachedLeaf {w : ℕ} (top : Fin w → TTree) (f : Fin w → TTree.Path → TTree) :=
  Σ a : GLeaf top, {b // b ∈ (f a.1.1 a.1.2).leaves}

/-- No quotient or multiplicity appears when the top leaves are grafted. -/
noncomputable def graftForestLeafEquiv {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) : AttachedLeaf top f ≃ GLeaf (graftForest top f) :=
  Equiv.ofBijective (fun x => ⟨(x.1.1.1, x.1.1.2 ++ x.2.1),
    (mem_leaves_graftTree _ _ _).mpr ⟨x.1.1.2, x.1.2, x.2.1, x.2.2, rfl⟩⟩) (by
    constructor
    · rintro ⟨⟨⟨j, a⟩, ha⟩, ⟨b, hb⟩⟩ ⟨⟨⟨j', a'⟩, ha'⟩, ⟨b', hb'⟩⟩ h
      have hj : j = j' := congrArg (fun x => x.1.1) h
      subst j'
      have he : a ++ b = a' ++ b' := congrArg (fun x => x.1.2) h
      have h1 : a <+: a ++ b := List.prefix_append _ _
      have h2 : a' <+: a ++ b := he ▸ List.prefix_append _ _
      have haa : a = a' := by
        rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
        · exact leaf_eq_of_prefix (top j) ha ha' h
        · exact (leaf_eq_of_prefix (top j) ha' ha h).symm
      subst a'
      have hbb : b = b' := List.append_cancel_left he
      subst b'
      rfl
    · rintro ⟨⟨j, q⟩, hq⟩
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_leaves_graftTree (top j) (f j) q).mp hq
      exact ⟨⟨⟨(j, a), ha⟩, ⟨b, hb⟩⟩, Subtype.ext (Prod.ext rfl hab)⟩)

/-- The final sign is exactly the inherited top-leaf sign times the lower-tree path sign. -/
theorem nodeSign_graftForestLeafEquiv {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (sig : Fin w → ℤˣ) (x : AttachedLeaf top f) :
    nodeSign sig ((graftForestLeafEquiv top f x).1) =
      TTree.pathSign (nodeSign sig x.1.1) x.2.1 :=
  pathSign_append _ _ _

end WaveTurbulence.LGSpine
