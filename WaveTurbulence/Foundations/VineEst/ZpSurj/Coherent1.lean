/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.ConjTree1

/-! # ZP-SURJ: the carrier-side objects of the states of `Zp(A)` are coherent -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5B WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι}

open Classical in
/-- From the native coherence of the exceptional objects to that of the carrier-side objects. -/
theorem coherent_of_native (G : FamilyReconstruction w ι) (i : ι)
    (hnat : IsCoherentCoupleAt p (zpPairQ G i).1 (zpPairQ G i).2 (zpData G i).1 (sigStar G i).2.1 ∧
      IsCoherentTreeAt p (zpBranchQ G i).1 (zpBranchQ G i).2 (zpData G i).2.1 (sigStar G i).2.2) :
    IsCoherentCoupleAt p (zpQQ G i).1 (zpQQ G i).2 (zpCodeC G i) (zpObjC G i) ∧
      IsCoherentTreeAt p (zpBranchQ G i).1 (zpBranchQ G i).2 (zpCodeT G i) (zpObjT G i) := by
  obtain ⟨hC, hT⟩ := hnat
  by_cases hv : nuOf G i = -1
  · refine ⟨?_, ?_⟩
    · unfold zpQQ zpCodeC zpObjC
      rw [if_pos hv, if_pos hv, if_pos hv]; exact hC
    · unfold zpCodeT zpObjT
      rw [if_pos hv, if_pos hv]
      exact isCoherentTreeAt_conj (conjLayered_isConjugateBy (sigStar G i).2.2 (Equiv.refl (Fin 1))) hT
  · refine ⟨?_, ?_⟩
    · unfold zpQQ zpCodeC zpObjC
      rw [if_neg hv, if_neg hv, if_neg hv]
      exact isCoherentCoupleAt_conj (conjLayered_isConjugateCouple (sigStar G i).2.1) hC
    · unfold zpCodeT zpObjT
      rw [if_neg hv, if_neg hv]; exact hT

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

/-- **`ZpSurj.coherent`**. -/
theorem zp_coherent [DecidableEq ι] [Fintype ι] (hA : IsPrimeGarden A.skeleton)
    (sp0 : SplitAt A.skeleton A.family pstar J) :
    ∀ G ∈ zpFinset p kind pstar J A sp0 hA,
      IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQQ G.1 pstar).2 (zpCodeC G.1 pstar) (zpObjC G.1 pstar) ∧
      IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpBranchQ G.1 pstar).2 (zpCodeT G.1 pstar) (zpObjT G.1 pstar) := by
  intro G hG
  have hb := (mem_zpFinset hA).1 hG
  obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA hb.batch
  rw [he]
  exact coherent_of_native _ _ (nativeCoh_op A pstar hcan hel htc hcc con)

end WaveTurbulence.ZpSurj
