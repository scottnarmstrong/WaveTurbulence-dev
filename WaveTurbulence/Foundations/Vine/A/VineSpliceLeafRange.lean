/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceBoundaryLeaves
/-! The exact surviving-leaf carrier of the actual spliceFold garden is
determined by the merge classes, including leaves absent from the molecule. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- An original LP leaf whose two bond endpoints are merged into one class. -/
def MergedLeaf (cls : GBranch G.tree → Option (GBranch G.tree)) (q : GLeaf G.tree) : Prop :=
  ∃ lp : GardenLPLeaf G, lp.1 = q ∧ ∃ a,
    cls (G.molecule.atom (.inr lp)) = some a ∧ cls (G.molecule.atom (G.molecule.mate (.inr lp))) = some a

/-- The full actual original-leaf range is the complement of the merged LP leaves. -/
theorem spliceFold_leaf_range (l : List (CLBlock G)) (q : GLeaf G.tree) :
    (∃ q', (spliceFoldLeafTrace l).leaf q' = q) ↔ ¬ MergedLeaf (spliceFold G l).cls q := by
  classical
  let T := spliceFoldLeafTrace l
  have H : SpliceDartTrace T := spliceFoldDartTrace l
  constructor
  · rintro ⟨q', hq⟩ ⟨lp, hlp, a, h1, h2⟩
    have hp : G.mark (T.leaf q') = none ∧ (T.leaf q').1.2 ≠ [] ∧ (G.pair (T.leaf q')).1.2 ≠ [] := by
      rw [hq, ← hlp]
      exact lp.2
    let lp' : GardenLPLeaf (spliceFold G l).G := ⟨q', (T.lp_profile q').mpr hp⟩
    have he : T.lp lp' = lp := Subtype.ext (hq.trans hlp.symm)
    have hd : (spliceFold G l).M.od (.inr lp') = .inr lp := (H.lp lp').trans (congrArg Sum.inr he)
    exact ((spliceFold G l).M.od_range (.inr lp)).mp ⟨.inr lp', hd⟩ ⟨a, h1, h2⟩
  · intro hn
    by_cases hp : G.mark q = none ∧ q.1.2 ≠ [] ∧ (G.pair q).1.2 ≠ []
    · let lp : GardenLPLeaf G := ⟨q, hp⟩
      have hnd : ¬ ∃ a, (spliceFold G l).cls (G.molecule.atom (.inr lp)) = some a ∧
          (spliceFold G l).cls (G.molecule.atom (G.molecule.mate (.inr lp))) = some a :=
        fun h => hn ⟨lp, rfl, h⟩
      obtain ⟨d, hd⟩ := ((spliceFold G l).M.od_range (.inr lp)).mpr hnd
      cases d with
      | inl pc => rw [H.pc] at hd; cases hd
      | inr lp' =>
        rw [H.lp] at hd
        have he : T.lp lp' = lp := Sum.inr.inj hd
        exact ⟨lp'.1, congrArg Subtype.val he⟩
    · exact spliceFold_nonLP_range l q hp

/-- Two actual splice sequences with the same merge classes retain the same full leaf carrier. -/
theorem spliceFold_leaf_same_range (l m : List (CLBlock G))
    (hc : (spliceFold G l).cls = (spliceFold G m).cls) (q : GLeaf G.tree) :
    (∃ q', (spliceFoldLeafTrace l).leaf q' = q) ↔ ∃ q', (spliceFoldLeafTrace m).leaf q' = q := by
  rw [spliceFold_leaf_range, spliceFold_leaf_range, hc]

end WaveTurbulence.VineA
