/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDoubleRemovalAttachments
public import WaveTurbulence.Foundations.Molecule.VineBackboneCenter
import Mathlib.Tactic

/-! # Simultaneous double-bond removals preserve every nontrivial vine -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, the simultaneous ordinary type-I removal clause in
a nontrivial vine ingredient. Every single-bond backbone edge survives;
disjointness leaves at least one attachment of each normal center. Rung
counts are arbitrary, including the four-atom type-II Q-block (F72). -/
theorem nontrivial_vine_typeI_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} (hX : X ≠ .I) {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=Finset.univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ S,∀ v ∈ S,(removeBlocks M S ps).SameComponent u v := by
  obtain ⟨_hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  let N := removeBlocks M S ps
  let root := (R.coreAtom ⟨0,by cases X <;> decide⟩).1
  have reach (z : V) (hz : z ∈ S) : N.SameComponent root z := by
    by_cases hg : OnSingleBackbone X (R.f z)
    · exact typeI_removal_single_path M S ps hI hD (R.single_backbone_to_atom hM z hz hg)
    · have hzold := nonbackbone_label_lt X hX (R.f z) hg
      let i : Fin X.template.n := ⟨R.f z,hzold⟩
      have hei : (R.coreAtom i).1=z := by
        apply R.injOn (R.coreAtom i).2 hz
        exact R.label_coreAtom i
      obtain ⟨j,k,hj,hk,hij,hik,hjk,hej,hek⟩ := template_center_neighbors X i hX hg
      have hadj := typeI_removal_one_attachment M S ps hI hD hdis
        (R.coreAtom i).2 (R.coreAtom j).2 (R.coreAtom k).2
        (fun h => hij (R.coreAtom_injective h))
        (fun h => hik (R.coreAtom_injective h))
        (fun h => hjk (R.coreAtom_injective h))
        (R.center_core_adj i j hX hg hej) (R.center_core_adj i k hX hg hek)
      have hjpath := R.typeI_removals_core_backbone hM ps hI hD j hj
      have hkpath := R.typeI_removals_core_backbone hM ps hI hD k hk
      have hp : N.SameComponent root (R.coreAtom i).1 := by
        rcases hadj with hadj | hadj
        · exact Relation.EqvGen.trans _ _ _ hjpath
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hadj))
        · exact Relation.EqvGen.trans _ _ _ hkpath
            (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hadj))
      simpa only [hei] using hp
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

end WaveTurbulence.Vine
