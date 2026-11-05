/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFSource
public import WaveTurbulence.Foundations.Molecule.LFTwist.CoherentInsertion

/-! # Actual updated reconstruction data for both coherent reinsertions -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

@[expose] noncomputable def midData (ε : Bool) (Q : RegCpl) (hQ : Q.wf = true) :
    ReconstructionData (s.chosen ε) := (s.baseData ε).withCouple (s.pairs ε s.exceptional) Q hQ

@[expose] noncomputable def finalData (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) : ReconstructionData (s.chosen ε) :=
  (s.midData ε Q hQ).withTree (s.branches ε s.placement.lower) X hX

theorem base_tree_other (ε : Bool) (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    (s.baseData ε).tree (s.branches ε b) = s.data.tree b :=
  (transportReconstruction_tree s.plain (s.chosen_plain ε) (s.branches ε)
    (chosenLeafEquiv s.skeleton s.placement ε) (chosenLeafEquiv_pair s.skeleton s.placement ε)
    (normalizedData s.data s.placement.lower s.exceptional) b).trans (s.data.eraseTree_other _ _ hb)

theorem base_couple_other (ε : Bool) (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    (s.baseData ε).couple (s.pairs ε q) = s.data.couple q :=
  (transportReconstruction_couple s.plain (s.chosen_plain ε) (s.branches ε)
    (chosenLeafEquiv s.skeleton s.placement ε) (chosenLeafEquiv_pair s.skeleton s.placement ε)
    (normalizedData s.data s.placement.lower s.exceptional) q).trans
      ((s.data.eraseTree s.placement.lower).eraseCouple_other _ _ hq)

/-- The two literal reinsertions are exactly the source reconstruction with
only its designated tree and couple changed. -/
theorem finalData_eq_choice (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) :
    s.finalData ε X Q hX hQ =
      lfReconstructionChoice s.skeleton s.placement s.plain s.data ε X Q hX hQ := by
  apply ReconstructionData.ext_tree_couple
  · funext c
    obtain ⟨b,rfl⟩ := (s.branches ε).surjective c
    by_cases hb : b = s.placement.lower
    · subst b
      exact (Function.update_self _ _ _).trans
        (lfReconstructionChoice_tree_at _ _ _ _ _ _ _ _ _).symm
    · have hne : s.branches ε b ≠ s.branches ε s.placement.lower := fun he => hb ((s.branches ε).injective he)
      exact (Function.update_of_ne hne _ _).trans ((s.base_tree_other ε b hb).trans
        (lfReconstructionChoice_tree_other _ _ _ _ _ _ _ _ _ b hb).symm)
  · funext r
    obtain ⟨q,rfl⟩ := (s.pairs ε).surjective r
    by_cases hq : q = s.exceptional
    · subst q
      exact (Function.update_self _ _ _).trans
        (lfReconstructionChoice_couple_at _ _ _ _ _ _ _ _ _).symm
    · have hne : s.pairs ε q ≠ s.pairs ε s.exceptional := fun he => hq ((s.pairs ε).injective he)
      exact (Function.update_of_ne hne _ _).trans ((s.base_couple_other ε q hq).trans
        (lfReconstructionChoice_couple_other _ _ _ _ _ _ _ _ _ q hq).symm)

/-- The source combined-order constraint gives exact final garden order. -/
theorem finalData_order (ε : Bool) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true)
    (hn : X.size + Q.size = (s.data.tree s.placement.lower).size + (s.data.couple s.exceptional).size) :
    ((s.finalData ε X Q hX hQ).garden (s.chosen_plain ε)).order = LG.garden.order := by
  have he : s.data.garden s.plain = LG.garden := rawOfGarden_injective_plain (s.data.garden_plain s.plain)
    s.decodes.1 ((s.data.garden_raw s.plain).trans s.decodes.2)
  rw [s.finalData_eq_choice ε X Q hX hQ]
  exact (lfReconstructionChoice_order _ _ _ _ _ _ _ _ _ hn).trans (congrArg Garden.order he)

end LFSource
end WaveTurbulence.LFTwist
