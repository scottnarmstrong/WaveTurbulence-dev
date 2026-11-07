/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineQuotientClasses
/-! Actual molecular isomorphisms descend through compatible splice merge
classes, using only the proved old-name branch and dart ranges. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G H K J : Garden w}
variable {cls : GBranch G.tree → Option (GBranch G.tree)}
variable {clh : GBranch H.tree → Option (GBranch H.tree)}

/-- The canonical branch correspondence through compatible quotient carriers. -/
noncomputable def quotientBranchEquiv (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (M : SpMap G K cls) (N : SpMap H J clh) :
    GBranch K.tree ≃ GBranch J.tree :=
  equivOfSameRange (fun c => F.e (M.ob c)) N.ob (F.e.injective.comp M.ob_inj) N.ob_inj
    (splice_branch_ranges F hc M N)

/-- Its actual original branch names commute with the given old atom map. -/
theorem quotientBranchEquiv_comm (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (M : SpMap G K cls) (N : SpMap H J clh) (c : GBranch K.tree) :
    N.ob (quotientBranchEquiv F hc M N c) = F.e (M.ob c) :=
  equivOfSameRange_comm (fun c => F.e (M.ob c)) N.ob (F.e.injective.comp M.ob_inj) N.ob_inj
    (splice_branch_ranges F hc M N) c

/-- The canonical dart correspondence through compatible quotient carriers. -/
noncomputable def quotientDartEquiv (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (M : SpMap G K cls) (N : SpMap H J clh) :
    GardenDart K ≃ GardenDart J :=
  equivOfSameRange (fun x => F.d (M.od x)) N.od (F.d.injective.comp M.od_inj) N.od_inj
    (splice_dart_ranges F hc M N)

/-- Its actual original dart names commute with the given old dart map. -/
theorem quotientDartEquiv_comm (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (M : SpMap G K cls) (N : SpMap H J clh) (x : GardenDart K) :
    N.od (quotientDartEquiv F hc M N x) = F.d (M.od x) :=
  equivOfSameRange_comm (fun x => F.d (M.od x)) N.od (F.d.injective.comp M.od_inj) N.od_inj
    (splice_dart_ranges F hc M N) x

/-- The actual directed molecule map on compatible splice quotients. -/
noncomputable def quotientMolIso (F : MolIso G.molecule H.molecule)
    (hc : ∀ v, clh (F.e v) = (cls v).map F.e) (M : SpMap G K cls) (N : SpMap H J clh) :
    MolIso K.molecule J.molecule where
  e := quotientBranchEquiv F hc M N
  d := quotientDartEquiv F hc M N
  atoms_iff := fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  atom_comm x := by
    apply N.ob_inj
    rw [N.ob_atom, quotientDartEquiv_comm, F.atom_comm, repC_intertwines F hc,
      quotientBranchEquiv_comm, M.ob_atom]
  mate_comm x := by
    apply N.od_inj
    rw [N.od_mate, quotientDartEquiv_comm, F.mate_comm, quotientDartEquiv_comm, M.od_mate]
  out_comm x := by
    rw [← N.od_out, quotientDartEquiv_comm, F.out_comm, M.od_out]

end WaveTurbulence.VineA
