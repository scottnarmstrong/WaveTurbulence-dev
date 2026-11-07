/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Final4

/-! # ZP-SURJ: the carrier bijection and the export -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5B WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} [DecidableEq ι] [Fintype ι]
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

theorem exists_eps_neg : ∃ ε : Bool, srcSign (A.source pstar hcan hel htc hcc) ε = -1 := by
  rcases nuOf_cases A pstar with h | h
  · exact ⟨true, by rw [srcSign_true, h]⟩
  · exact ⟨false, by rw [srcSign_false, h]⟩

/-- **`ZpSurj.carrier`**. -/
theorem zp_carrier (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J) :
    Set.BijOn (fun G : ST w ι pstar J => zpCarrierOf G.1 pstar) (zpSet p kind pstar J A sp0 hA (-1))
      {c | ZpCarrier p A pstar c} := by
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    obtain ⟨hGm, hσ, hR⟩ := hG
    obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hGm).batch
    rw [he] at hR hσ
    show ZpCarrier p A pstar (zpCarrierOf G.1 pstar)
    rw [he]
    exact carrier_of_IIb A hcan hel htc hcc con hσ ((zpRootsLE_iff A hcan hel htc hcc con).1 hR)
  · intro G1 hG1 G2 hG2 he
    obtain ⟨ε1, con1, e1⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hG1.1).batch
    obtain ⟨ε2, con2, e2⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hG2.1).batch
    have n1 : nuOf G1.1 pstar = -1 := hG1.2.1
    have n2 : nuOf G2.1 pstar = -1 := hG2.2.1
    have hc : zpCarrierOf G1.1 pstar = zpCarrierOf G2.1 pstar := he
    rw [e1] at n1 hc
    rw [e2] at n2 hc
    rw [carrierOf_IIb A hcan hel htc hcc con1 n1, carrierOf_IIb A hcan hel htc hcc con2 n2] at hc
    simp only [Prod.mk.injEq] at hc
    obtain ⟨-, hX, hLQ, hL⟩ := hc
    have hL' : conLX con1 = conLX con2 := by
      have := congrArg (fun L => conjLayered L (Equiv.refl (Fin 1))) hL
      simp only [conjLayered_refl_refl] at this
      exact this
    have hs : sigStar G1.1 pstar = sigStar G2.1 pstar := by
      rw [e1, e2]
      refine Prod.ext (n1.trans n2.symm) (Prod.ext ?_ ?_)
      · rw [sigStar_op A pstar hcan hel htc hcc con1, sigStar_op A pstar hcan hel htc hcc con2]; exact hLQ
      · rw [sigStar_op A pstar hcan hel htc hcc con1, sigStar_op A pstar hcan hel htc hcc con2]; exact hL'
    exact st_ext A sp0 ((mem_zpFinset hA).1 hG1.1) ((mem_zpFinset hA).1 hG2.1)
      (zp_eq_of_sigStar hA ((mem_zpFinset hA).1 hG1.1).batch ((mem_zpFinset hA).1 hG2.1).batch hs)
  · rintro ⟨Qc, Xc, LQc, LXc⟩ hc
    have hc' : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Qc Xc LQc LXc := hc
    obtain ⟨ε, hε⟩ := exists_eps_neg A hcan hel htc hcc
    obtain ⟨hD, hcnt⟩ := carrier_datum A hcan hel htc hcc ε hε hc'
    obtain ⟨con, h1, h2, h3, h4⟩ := state_of_datum A hcan hel htc hcc hD hcnt
    have hL := L2_le_m A hcan hel htc hcc
    obtain ⟨cQ, cT, -, -, -⟩ := hc'
    obtain ⟨R0, R1⟩ := layerPatternN_root_le (pattern_of_coherentCouple cQ)
    have RT := root_tree_le cT hL
    have hcT : layerAt (conjLayered LXc (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path)) =
        layerAt LXc ((0 : Fin 1), ([] : Path)) :=
      layerAt_conj (conjLayered_isConjugateBy LXc (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path))
    have hv : nuOf (opOut A pstar hcan hel htc hcc con) pstar = -1 := by
      rw [nuOf_op A hcan hel htc hcc con]; exact hε
    have hNR : NR A hcan hel htc hcc con := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h3]; exact R0
      · rw [h3]; exact R1.trans hL
      · rw [h4, hcT]; exact RT
    refine ⟨opState A sp0 hcan hel htc hcc con, ⟨?_, hv, (zpRootsLE_iff A hcan hel htc hcc con).2 hNR⟩, ?_⟩
    · exact (mem_zpFinset hA).2 (reach_opState A sp0 hcan hel htc hcc con)
    · show zpCarrierOf (opOut A pstar hcan hel htc hcc con) pstar = _
      rw [carrierOf_IIb A hcan hel htc hcc con hv, h1, h2, h3, h4, conjChain_conjChain, conjLayered_refl_refl]

end WaveTurbulence.ZpSurj
