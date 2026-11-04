/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceTreeDecoding

/-! # Actual source regularity under the checked code operations -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Permuting the complete literal pair list preserves the actual decoded carrier. -/
theorem decodedCouple_eq_of_rawPairs_perm (C D : RegCpl) (h : C.raw.2.Perm D.raw.2) :
    decodedCouple C = decodedCouple D := by
  have ht : coupleForest C = coupleForest D := by
    apply forest_eq_of_leaf_set_eq
    rw [coupleForest_leaf_set,coupleForest_leaf_set,pairEndpoints_perm h]
  apply carrier_eq_of_embedded_pairing D _ _ (decodedCouple_decodes C).1 (decodedCouple_decodes D).1 ht id Function.injective_id
  · intro ℓ
    have hp := (decodedCouple_decodes C).2.2.2 ℓ
    rw [mem_symmPairs_iff] at hp ⊢
    exact hp.imp (fun hp => h.mem_iff.mp hp) (fun hp => h.mem_iff.mp hp)
  · exact (decodedCouple_decodes D).2.2.2

/-- Recoding by actual carrier equality retains an exact represented source history. -/
theorem RawRep.recoded {C D : RegCpl} {R : RawCpl} (h : RawRep C R)
    (he : decodedCouple C = decodedCouple D) : RawRep D R := by
  have hforest := congrArg Garden.tree he
  have ht : C.trees = D.trees := Prod.ext (congrFun hforest 0) (congrFun hforest 1)
  exact ⟨h.1.trans ht,h.2.trans (rawPairs_perm_of_carrier_eq he)⟩

/-- An actual source-regular decoded carrier has an actual represented A/B history. -/
theorem exists_rawRep_of_isRegularCouple (C : RegCpl) (hC : IsRegularCouple (decodedCouple C)) :
    ∃ R : RawCpl, RawRegular R ∧ RawRep C R := by
  obtain ⟨R,hR,hM⟩ := hC
  obtain ⟨D,_,hD⟩ := RawRegular.exists_wf_rawRep hR
  have hd : D.Decodes (decodedCouple C) := (hD.decodes_iff _).mpr hM
  have he : decodedCouple D = decodedCouple C := (decodedCouple_unique D _ hd).symm
  exact ⟨R,hR,hD.recoded he⟩

/-- The checked A operation retains actual source regularity. -/
theorem isRegularCouple_operationA (C : RegCpl) (hC : IsRegularCouple (decodedCouple C))
    (x y : Fin 2 × Path) (m : MiniCplCode) (hxy : (x,y) ∈ C.raw.2) :
    IsRegularCouple (decodedCouple (operationA C x y m)) := by
  obtain ⟨R,hR,hrep⟩ := exists_rawRep_of_isRegularCouple C hC
  have hxyR := hrep.2.mem_iff.mpr hxy
  exact isRegularCouple_of_rawRep (rawRep_opA hrep x y m hxyR) (.opA m hR hxyR)

/-- The checked B operation retains actual source regularity at every represented node. -/
theorem isRegularCouple_operationB (C : RegCpl) (hC : IsRegularCouple (decodedCouple C))
    (a : Fin 2 × Path) (m : MiniTreeCode) (ha : a ∈ coupleNodes C (0,[]) (1,[])) :
    IsRegularCouple (decodedCouple (operationB C a m)) := by
  obtain ⟨R,hR,hrep⟩ := exists_rawRep_of_isRegularCouple C hC
  have haR : a.2 ∈ (R.tree a.1).nodes := by
    rw [hrep.forest]
    exact (coupleForest_node_iff C a).mpr ha
  exact isRegularCouple_of_rawRep (rawRep_opB hrep a m haR) (.opB m hR haR)

/-- The constructed trivial carrier is the actual source base case. -/
theorem decodedTriv_isRegular : IsRegularCouple (decodedCouple .triv) :=
  isRegularCouple_of_rawRep rawRep_triv RawRegular.triv

end WaveTurbulence.Reg
