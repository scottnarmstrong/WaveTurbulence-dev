/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Final3

/-! # ZP-SURJ: a carrier element is the native datum of a II-b operation -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

theorem root_tree_le {p q q' : ℕ} {X : RegChain} {LX : LayeredGarden 1} (h : IsCoherentTreeAt p q q' X LX)
    (hq : q' ≤ q) : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ q := by
  cases X with
  | nil =>
    have := coherentTree_lone h
    simp only [RegChain.lonePath] at this
    rw [this]; exact hq
  | pair m Qr Qg inner rest =>
    exact treePatternN_root_le (pattern_of_coherentTree h) (by simp [RegChain.isNil])

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι}
variable (A : FamilyReconstruction w ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

include hcan hel htc hcc

theorem carrier_datum (ε : Bool) (hε : srcSign (A.source pstar hcan hel htc hcc) ε = -1)
    {Qc : RegCpl} {Xc : RegChain} {LQc : LayeredGarden 2} {LXc : LayeredGarden 1}
    (hcar : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Qc Xc LQc LXc) :
    ExcDatum (A.source pstar hcan hel htc hcc) ε Qc (conjChain Xc) LQc (conjLayered LXc (Equiv.refl (Fin 1))) ∧
    srcRaw (p := p) (pstar := pstar) A =
      topBranchCount (conjLayered LXc (Equiv.refl (Fin 1))) p + topBranchCount LQc p := by
  obtain ⟨cQ, cT, csig, cord, ccnt⟩ := hcar
  have hL := L2_le_m A hcan hel htc hcc
  obtain ⟨bL, bm1, bm2, bL1⟩ := base_facts A hcan hel htc hcc ε
  have hB := base_pair_parents (p := p) A hcan hel htc hcc ε
  have hB2 := base_branch_parents (p := p) A hcan hel htc hcc ε
  have hνB := nuOf_base A hcan hel htc hcc ε
  generalize baseState A hcan hel htc hcc ε = B at bL bm1 bm2 bL1 hB hB2 hνB
  have hv : nuOf B pstar = -1 := hνB.trans hε
  have pq := pairQ_neg B pstar hv
  have hBa := congrArg Prod.fst hB
  have hBb := congrArg Prod.snd hB
  simp only at hBa hBb
  rw [pq] at hBa hBb
  simp only at hBa hBb
  obtain ⟨R0, R1⟩ := layerPatternN_root_le (pattern_of_coherentCouple cQ)
  have RT := root_tree_le cT hL
  have hT := isCoherentTreeAt_conj (conjLayered_isConjugateBy LXc (Equiv.refl (Fin 1))) cT
  have hcT : layerAt (conjLayered LXc (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path)) =
      layerAt LXc ((0 : Fin 1), ([] : Path)) := layerAt_conj (conjLayered_isConjugateBy LXc (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path))
  have e1 : LQc.garden.order = Qc.size := by
    rw [decodedCouple_unique _ _ cQ.2.1, decodedCouple_order]
  have e2 : LXc.garden.order = Xc.size := by
    rw [decodedTree_unique _ _ _ cT.2.1 rfl, decodedTree_order]
  have hsz : Xc.size + Qc.size = (A.data.tree (A.family.placement pstar).lower).size +
      (A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).size := by
    have := two_zpN A (pstar := pstar)
    omega
  refine ⟨?_, ?_⟩
  · refine datum_of_coherent cQ (q' := (zpBranchQ A pstar).2) hT ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hBa, hBb, bL]
      show min _ _ = min (zpQ4 A pstar) (zpBranchQ A pstar).2
      rw [min_eq_right bL1, min_eq_right hL]
    · rw [hBa]; exact R0.trans bm1
    · rw [hBb, bL]; exact R1
    · have e : parAt ((A.source pstar hcan hel htc hcc).base ε) p (tA (A.source pstar hcan hel htc hcc) ε) =
          (zpBranchQ B pstar).1 := congrArg Prod.fst hB2
      rw [hcT, e]; exact RT.trans bm2
    · show -LXc.garden.sig 0 = _
      rw [csig, hε]
    · have e : layerAt ((A.source pstar hcan hel htc hcc).base ε) (tA (A.source pstar hcan hel htc hcc) ε) =
          (zpBranchQ B pstar).2 := congrArg Prod.snd hB2
      rw [e, bL]
    · rw [size_conjChain]; exact hsz
  · have h2 := srcRaw_eq_start (p := p) (pstar := pstar) A
    rw [topBranchCount_conj (conjLayered_isConjugateBy LXc (Equiv.refl (Fin 1)))]
    have : topBranchCount LQc p + topBranchCount LXc p = topBranchCount (sigStar A pstar).2.1 p +
        topBranchCount (sigStar A pstar).2.2 p := ccnt
    omega

end WaveTurbulence.ZpSurj
