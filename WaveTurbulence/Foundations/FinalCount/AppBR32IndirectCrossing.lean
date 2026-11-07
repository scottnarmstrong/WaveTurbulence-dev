/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBR32Incidence
public import WaveTurbulence.Foundations.FinalCount.AppBR32FiveIndices
public import WaveTurbulence.Foundations.FinalCount.AppBCombinedFrames
public import WaveTurbulence.Foundations.FinalCount.AppBDropInsideAtom
public import WaveTurbulence.Foundations.FinalCount.AppBCutTripleOfCrossing
import Mathlib.Tactic

/-! # The actual three-bond cut for indirect entry in 3R-2G -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_r32_indirect_crossing {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool)
    (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val})
    (ha : s.specialAtom which ∈ S) (hc : s.specialCompanion which ∈ S) (ho : s.specialAtom (!which) ∉ S)
    (hstar : appbIncidence M (s.specialAtom which) (r.edge j).val = 0) :
    appbCrossingBonds M (S \ {s.specialAtom which}) =
      {(r.edge j).val,(s.edge (s.specialFirst which)).val.val,(s.edge (s.specialSecond which)).val.val} := by
  let b := r.combinedRemoval s v0
  have hleft := appb_r32_all_star_incidence_zero r s S hS j hcross (s.specialAtom which) ha hstar
  let t := (s.specialFrame which).combinedRight r s v0 hleft
  have hrem : s.specialAtom which ∈ b.removedAtoms := by
    rw [r.combinedRemoval_removed]
    exact mem_union_right _ (s.special_atom_removed which)
  have ht0 : t.index 0 = r.combinedRightIndex s ⟨0,by decide⟩ := by
    change r.combinedRightIndex s ((s.specialFrame which).index 0) = _
    rw [(s.specialFrame_indices which).1]
  have ht1 : t.index 1 = r.combinedRightIndex s (s.specialFirst which) := by
    change r.combinedRightIndex s ((s.specialFrame which).index 1) = _
    rw [(s.specialFrame_indices which).2.1]
  have ht2 : t.index 2 = r.combinedRightIndex s (s.specialSecond which) := by
    change r.combinedRightIndex s ((s.specialFrame which).index 2) = _
    rw [(s.specialFrame_indices which).2.2]
  have he0 : (b.edge (t.index 0)).val = (s.edge ⟨0,by decide⟩).val.val := by
    rw [ht0]
    exact r.combined_edge_right s v0 _
  have he1 : (b.edge (t.index 1)).val = (s.edge (s.specialFirst which)).val.val := by
    rw [ht1]
    exact r.combined_edge_right s v0 _
  have he2 : (b.edge (t.index 2)).val = (s.edge (s.specialSecond which)).val.val := by
    rw [ht2]
    exact r.combined_edge_right s v0 _
  have hi := t.incident_bonds hrem
  rw [he0,he1,he2] at hi
  have hbEnds : M.ends (s.edge ⟨0,by decide⟩).val.val = s(s.specialAtom which,s.specialAtom (!which)) :=
    s.special_bridge_ends which
  have hd1 : M.ends (s.edge (s.specialFirst which)).val.val = s(s.specialAtom which,s.specialCompanion which) :=
    s.special_first_ends which
  have hd2 : M.ends (s.edge (s.specialSecond which)).val.val = s(s.specialAtom which,s.specialCompanion which) :=
    s.special_second_ends which
  exact appb_drop_inside_atom_crossing M S _ _ _ _ _ _ _ ha hc ho
    (s.special_atom_ne_companion which).symm hcross hi hbEnds hd1 hd2 hstar

noncomputable def appbR32IndirectCut {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) (v0 : M.atoms)
    (S : Finset V) (hS : S ⊆ r.post.atoms) (j : Fin 3) (which : Bool)
    (hcross : appbCrossingBonds M S = {(r.edge j).val,(s.edge ⟨0,by decide⟩).val.val})
    (ha : s.specialAtom which ∈ S) (hc : s.specialCompanion which ∈ S) (ho : s.specialAtom (!which) ∉ S)
    (hstar : appbIncidence M (s.specialAtom which) (r.edge j).val = 0) :
    AppbCutTriple (r.combinedRemoval s v0) (S \ {s.specialAtom which}) :=
  appbCutTripleOfCrossing (r.combinedRemoval s v0) _
    (fun v hv => (mem_sdiff.mp (hS (mem_sdiff.mp hv).1)).1) (appbR32TripleIndices r s j which) (by
      rw [appb_image_fin_three]
      have hi := appb_r32_triple_indices r s j which
      rw [hi.1,hi.2.1,hi.2.2]
      have hL : ((r.combinedRemoval s v0).edge (r.combinedLeftIndex s j)).val = (r.edge j).val :=
        r.combined_edge_left s v0 j
      have hR1 : ((r.combinedRemoval s v0).edge (r.combinedRightIndex s (s.specialFirst which))).val =
          (s.edge (s.specialFirst which)).val.val := r.combined_edge_right s v0 _
      have hR2 : ((r.combinedRemoval s v0).edge (r.combinedRightIndex s (s.specialSecond which))).val =
          (s.edge (s.specialSecond which)).val.val := r.combined_edge_right s v0 _
      rw [hL,hR1,hR2]
      exact appb_r32_indirect_crossing r s v0 S hS j which hcross ha hc ho hstar)

end WaveTurbulence.Mole
