/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionInjective

/-! # Reflection of ancestry and root status by actual reconstruction positions -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- Inflation reflects source ancestry, as well as preserving it. -/
theorem inflatedPosition_below_iff {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a b : GNode S.tree) :
    Below (inflatedPosition S X a) (inflatedPosition S X b) ↔ Below a.1 b.1 := by
  constructor
  · intro h
    by_cases hab : Below a.1 b.1
    · exact hab
    by_cases hba : Below b.1 a.1
    · have hb := inflatedPosition_below S X b a hba
      have he : inflatedPosition S X a = inflatedPosition S X b :=
        Prod.ext h.1.symm (List.IsPrefix.eq_of_length h.2 (Nat.le_antisymm h.2.length_le hb.2.length_le))
      have he' := inflatedPosition_injective S X he
      subst b
      exact ⟨rfl,List.prefix_refl _⟩
    · exact ((inflatedPosition_incomp S X a b ⟨hab,hba⟩).1 h).elim
  · exact inflatedPosition_below S X a b

/-- A nonroot source node cannot become a root after inserting regular contexts. -/
theorem inflatedPosition_nonroot {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a : GNode S.tree) (ha : a.1.2 ≠ []) : (inflatedPosition S X a).2 ≠ [] := by
  intro h
  have he : inflatedPosition S X a = inflatedPosition S X (GNode.root S.tree a.1.1) := by
    rw [inflatedPosition_root]
    exact Prod.ext (inflatedPosition_index S X a) h
  have he' := congrArg (fun n : GNode S.tree => n.1.2) (inflatedPosition_injective S X he)
  exact ha he'

end WaveTurbulence.LFTwist
