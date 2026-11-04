/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationAFidelity

/-! # Exact representation of source construction histories

Trees are equal and oriented pair lists agree up to permutation. This relation
retains multiplicity and supports the A/B induction; it does not assert source
regularity or uniqueness of codes by definition.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- A raw source object and a structure code have identical trees and pairs. -/
def RawRep (Q : RegCpl) (R : RawCpl) : Prop := R.1 = Q.trees ∧ R.2.Perm Q.raw.2

/-- The source's initial trivial couple has the trivial code. -/
theorem rawRep_triv : RawRep .triv ((.leaf,.leaf),[((0,[]),(1,[]))]) := ⟨rfl,List.Perm.refl _⟩

/-- Exact raw representation implies equality of the actual indexed forests. -/
theorem RawRep.forest {Q : RegCpl} {R : RawCpl} (h : RawRep Q R) : R.tree = coupleForest Q := by
  rw [← raw_tree_eq_coupleForest]
  funext j
  simp only [RawCpl.tree,RegCpl.raw]
  rw [h.1]

/-- Representation transfers the actual source garden matching predicate. -/
theorem RawRep.decodes_iff {Q : RegCpl} {R : RawCpl} (h : RawRep Q R) (G : Garden 2) :
    Q.Decodes G ↔ G.MatchesCouple R.1 R.2 :=
  (matchesCouple_congr G h.1 (fun _ => h.2.mem_iff)).symm

/-- Source operation A preserves exact representation by a well-formed new code. -/
theorem rawRep_opA {Q : RegCpl} {R : RawCpl} (h : RawRep Q R)
    (x y : Fin 2 × Path) (c : MiniCplCode) (hxy : (x,y) ∈ R.2) :
    RawRep (operationA Q x y c) (R.opA x y c) := by
  have hQxy : (x,y) ∈ Q.raw.2 := h.2.mem_iff.mp hxy
  have hf : (R.opA x y c).tree = coupleForest (operationA Q x y c) := by
    rw [raw_opA_updates,h.forest]
    rw [operationA_forest Q x y c hQxy,raw_opA_updates,raw_tree_eq_coupleForest]
  constructor
  · have h0 := congrFun hf (0 : Fin 2)
    have h1 := congrFun hf (1 : Fin 2)
    change (R.opA x y c).1.1 = (operationA Q x y c).trees.1 at h0
    change (R.opA x y c).1.2 = (operationA Q x y c).trees.2 at h1
    exact Prod.ext h0 h1
  · have hp := (h.2.erase (x,y)).append_right ((miniCoupleCode c).pairsAt x y)
    rw [← raw_opA_pair_list R,← raw_opA_pair_list Q.raw] at hp
    exact hp.trans (operationA_pairs_perm Q x y c hQxy).symm

/-- An actual represented source history supplies source regularity of its decoded carrier.
The history itself must be produced by source A/B steps; this helper does not assume a
characterization theorem. -/
theorem isRegularCouple_of_rawRep {Q : RegCpl} {R : RawCpl}
    (h : RawRep Q R) (hR : RawRegular R) : IsRegularCouple (decodedCouple Q) :=
  ⟨R,hR,(h.decodes_iff _).mp (decodedCouple_decodes Q)⟩

end WaveTurbulence.Reg
