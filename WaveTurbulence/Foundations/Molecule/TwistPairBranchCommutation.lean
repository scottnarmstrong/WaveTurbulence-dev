/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPairData
public import WaveTurbulence.Foundations.Molecule.TwistDecorationRoots
public import WaveTurbulence.Foundations.Molecule.GardenRootEncoding

/-! # Branch and forest commutation for two separated source unit twists

The actual double surgeries have identical incidence codes: their port
permutations act at distinct lower atoms. Ordered-root reconstruction
then proves equality of their trees and of every transported branch.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w} {P Q : CorePlacement G}

/-- Branching roots keep their actual ordered root address under any unit twist. -/
theorem coreBranchEquiv_root_val {H : Garden w} (R : CorePlacement H) (b : GBranch H.tree)
    (hb : b.1.2 = []) : (coreBranchEquiv H R b).1 = b.1 := by
  apply coreBranchEquiv_fixed_val
  intro hd
  exact R.nonroot (List.eq_nil_of_prefix_nil (hb ▸ hd.2))

/-- Two actual unit twists preserve each ordered branching-root address. -/
theorem CorePairData.branch_root (D : CorePairData G P Q) (b : GBranch G.tree) (hb : b.1.2 = []) :
    (D.branches b).1 = b.1 := by
  have hp := coreBranchEquiv_root_val P b hb
  have hn : (coreBranchEquiv G P b).1.2 = [] := (congrArg Prod.snd hp).trans hb
  exact (coreBranchEquiv_root_val D.next _ hn).trans hp

/-- The local position after two actual twists is the composition of two disjoint port permutations. -/
theorem CorePairData.position (D : CorePairData G P Q) (x : GardenDart G) :
    Mole.dartPosition D.garden (D.darts x) =
      (if G.molecule.atom x = Q.lower then (switchPort Q.keep : Fin 4 → Fin 4) else id)
        ((if G.molecule.atom x = P.lower then (switchPort P.keep : Fin 4 → Fin 4) else id) (Mole.dartPosition G x)) := by
  classical
  have hq := twistDartEquiv_position (unitTwistGarden G P) D.next (twistDartEquiv G P x)
  have hp := twistDartEquiv_position G P x
  have ha := twistDartEquiv_atom G P x
  have he : (unitTwistGarden G P).molecule.atom (twistDartEquiv G P x) = D.next.lower ↔
      G.molecule.atom x = Q.lower := by
    constructor
    · intro h
      exact (coreBranchEquiv G P).injective (ha.symm.trans h)
    · intro h
      exact ha.trans (congrArg (coreBranchEquiv G P) h)
  have hq' : Mole.dartPosition D.garden (D.darts x) =
    if G.molecule.atom x = Q.lower then
      switchPort Q.keep (Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P x))
    else Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P x) := by
    by_cases h : G.molecule.atom x = Q.lower
    · exact hq.trans ((if_pos (he.mpr h)).trans (if_pos h).symm)
    · exact hq.trans ((if_neg (fun hh => h (he.mp hh))).trans (if_neg h).symm)
  simpa only [ite_apply,hp,id_eq] using hq'


/-- The actual positions agree in both orders. -/
theorem CorePairData.position_commute (D : CorePairData G P Q) (x : GardenDart G) :
    Mole.dartPosition D.garden (D.darts x) = Mole.dartPosition D.swap.garden (D.swap.darts x) := by
  classical
  rw [D.position,D.swap.position]
  by_cases hp : G.molecule.atom x = P.lower
  · have hq : G.molecule.atom x ≠ Q.lower := fun he => D.lower_ne (hp.symm.trans he)
    simp only [hp,D.lower_ne,ite_true,ite_false,id_eq]
  · simp only [hp,ite_false,id_eq]

/-- An actual encoded isomorphism between the two orders, with proved equal position codes. -/
@[expose] noncomputable def CorePairData.orderIso (D : CorePairData G P Q) : Mole.GardenEncodedIso D.garden D.swap.garden where
  branches := D.branches.symm.trans D.swap.branches
  darts := D.darts.symm.trans D.swap.darts
  atom_comm := by
    intro y
    obtain ⟨x,rfl⟩ := D.darts.surjective y
    change D.swap.garden.molecule.atom (D.swap.darts (D.darts.symm (D.darts x))) = _
    rw [D.darts.symm_apply_apply,D.swap.atom,D.atom]
    exact congrArg D.swap.branches (D.branches.symm_apply_apply _).symm
  mate_comm := by
    intro y
    obtain ⟨x,rfl⟩ := D.darts.surjective y
    change D.swap.garden.molecule.mate (D.swap.darts (D.darts.symm (D.darts x))) = _
    rw [D.darts.symm_apply_apply,D.swap.mate,D.mate]
    exact congrArg D.swap.darts (D.darts.symm_apply_apply _).symm
  position_comm := by
    intro y
    obtain ⟨x,rfl⟩ := D.darts.surjective y
    change Mole.dartPosition D.swap.garden (D.swap.darts (D.darts.symm (D.darts x))) = _
    exact (congrArg (fun x => Mole.dartPosition D.swap.garden (D.swap.darts x))
      (D.darts.symm_apply_apply x)).trans (D.position_commute x).symm

/-- Root-order preservation for the reconstructed isomorphism. -/
theorem CorePairData.orderIso_root (D : CorePairData G P Q) (b : GBranch D.garden.tree) (hb : b.1.2 = []) :
    (D.orderIso.branches b).1.1 = b.1.1 := by
  obtain ⟨v,rfl⟩ := D.branches.surjective b
  have hn : v.1.2 = [] := by
    by_contra hnv
    have hn₁ := (coreBranchEquiv_nonroot G P v).mpr hnv
    have hn₂ := (coreBranchEquiv_nonroot (unitTwistGarden G P) D.next (coreBranchEquiv G P v)).mpr hn₁
    exact hn₂ hb
  have he : D.orderIso.branches (D.branches v) = D.swap.branches v :=
    congrArg D.swap.branches (D.branches.symm_apply_apply v)
  exact (congrArg (fun b : GBranch D.swap.garden.tree => b.1.1) he).trans
    ((congrArg Prod.fst (D.swap.branch_root v hn)).trans (congrArg Prod.fst (D.branch_root v hn)).symm)

/-- The actual branch addresses are identical in both orders. -/
theorem CorePairData.branch_commute (D : CorePairData G P Q) (b : GBranch G.tree) :
    (D.swap.branches b).1 = (D.branches b).1 := by
  have h := D.orderIso.branch_addresses D.orderIso_root (D.branches b)
  have he : D.orderIso.branches (D.branches b) = D.swap.branches b :=
    congrArg D.swap.branches (D.branches.symm_apply_apply b)
  exact (congrArg Subtype.val he).symm.trans h

/-- The two orders produce exactly the same ordered forests. -/
theorem CorePairData.forest_commute (D : CorePairData G P Q) : D.garden.tree = D.swap.garden.tree :=
  D.orderIso.trees_eq D.orderIso_root

end WaveTurbulence.Twist
