/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Inv2

/-! # ZP-SURJ: native root bounds and the twin at the level of states -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

theorem cplRootLayer_eq (L : LayeredGarden 2) : cplRootLayer L = layerAt L ((0 : Fin 2), ([] : Path)) :=
  (layerAt_node L (GNode.root L.garden.tree 0)).symm

theorem treeRootLayer_eq (L : LayeredGarden 1) : treeRootLayer L = layerAt L ((0 : Fin 1), ([] : Path)) :=
  (layerAt_node L (GNode.root L.garden.tree 0)).symm

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

/-- `L₂ ≤ L₄`. -/
theorem L2_le_m : (zpBranchQ A pstar).2 ≤ zpQ4 A pstar := by
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have h2 := L2_le_q2 A pstar hcan hel htc hcc
  rw [zpQ4_eq A (pstar := pstar)]
  exact le_min (le_max_right _ _) h2

/-- The native roots of a construction lie below `L₄`. -/
@[expose] def NR {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) : Prop :=
  layerAt (conLQ con) ((0 : Fin 2), ([] : Path)) ≤ zpQ4 A pstar ∧
  layerAt (conLQ con) ((1 : Fin 2), ([] : Path)) ≤ zpQ4 A pstar ∧
  layerAt (conLX con) ((0 : Fin 1), ([] : Path)) ≤ zpQ4 A pstar

theorem zpRootsLE_iff {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    ZpRootsLE A (opOut A pstar hcan hel htc hcc con) pstar ↔ NR A hcan hel htc hcc con := by
  have hnat := nativeCoh_op A pstar hcan hel htc hcc con
  rw [zpData_op A hcan hel htc hcc con, sigStar_op A pstar hcan hel htc hcc con] at hnat
  have hpat := pattern_of_coherentCouple hnat.1
  obtain ⟨R0, R1⟩ := layerPatternN_root_le hpat
  have hL := L2_le_m A hcan hel htc hcc
  obtain ⟨hGL, -⟩ := op_numbers A hcan hel htc hcc con
  have hconjQ := conjLayered_isConjugateCouple (conLQ con)
  have hconjT := conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1))
  have hc0 : layerAt (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) ((0 : Fin 2), ([] : Path)) =
      layerAt (conLQ con) ((1 : Fin 2), ([] : Path)) := by
    have := layerAt_conj hconjQ ((1 : Fin 2), ([] : Path))
    rw [phi_swap_one] at this; exact this
  have hcT : layerAt (conjLayered (conLX con) (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path)) =
      layerAt (conLX con) ((0 : Fin 1), ([] : Path)) := layerAt_conj hconjT ((0 : Fin 1), ([] : Path))
  unfold ZpRootsLE NR zpObjC zpObjT
  rw [sigStar_op A pstar hcan hel htc hcc con]
  have hv := nuOf_cases (opOut A pstar hcan hel htc hcc con) pstar
  by_cases hv1 : nuOf (opOut A pstar hcan hel htc hcc con) pstar = -1
  · have hq := pairQ_neg (opOut A pstar hcan hel htc hcc con) pstar hv1
    rw [hq, hGL] at R1
    simp only [if_pos hv1, cplRootLayer_eq, treeRootLayer_eq, hcT]
    constructor
    · rintro ⟨a, b⟩; exact ⟨a, R1.trans hL, b⟩
    · rintro ⟨a, -, b⟩; exact ⟨a, b⟩
  · have hv1' : nuOf (opOut A pstar hcan hel htc hcc con) pstar = 1 := hv.resolve_right hv1
    have hq := pairQ_pos (opOut A pstar hcan hel htc hcc con) pstar hv1'
    rw [hq, hGL] at R0
    simp only [if_neg hv1, cplRootLayer_eq, treeRootLayer_eq, hc0]
    constructor
    · rintro ⟨a, b⟩; exact ⟨R0.trans hL, a, b⟩
    · rintro ⟨-, a, b⟩; exact ⟨a, b⟩

variable {J : Set ι} [DecidableEq ι] [Fintype ι]

/-- The exact conjugacy relation between the exceptional data of two states. -/
def Rel (G G' : FamilyReconstruction w ι) (i : ι) : Prop :=
  (sigStar G' i).2.1 = conjLayered (sigStar G i).2.1 (Equiv.swap (0 : Fin 2) 1) ∧
  (sigStar G' i).2.2 = conjLayered (sigStar G i).2.2 (Equiv.refl (Fin 1)) ∧
  (zpData G' i).1 = conjCpl (zpData G i).1 ∧ (zpData G' i).2.1 = conjChain (zpData G i).2.1

theorem NR_conj {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (con' : LFConstruction (A.source pstar hcan hel htc hcc) (!ε)) (hn : NR A hcan hel htc hcc con)
    (h1 : conLQ con' = conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1))
    (h2 : conLX con' = conjLayered (conLX con) (Equiv.refl (Fin 1))) : NR A hcan hel htc hcc con' := by
  have hconjQ := conjLayered_isConjugateCouple (conLQ con)
  have hconjT := conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1))
  have hc0 : layerAt (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) ((0 : Fin 2), ([] : Path)) =
      layerAt (conLQ con) ((1 : Fin 2), ([] : Path)) := by
    have := layerAt_conj hconjQ ((1 : Fin 2), ([] : Path))
    rw [phi_swap_one] at this; exact this
  have hc1 : layerAt (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) ((1 : Fin 2), ([] : Path)) =
      layerAt (conLQ con) ((0 : Fin 2), ([] : Path)) := by
    have := layerAt_conj hconjQ ((0 : Fin 2), ([] : Path))
    rw [phi_swap_zero] at this; exact this
  have hcT : layerAt (conjLayered (conLX con) (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path)) =
      layerAt (conLX con) ((0 : Fin 1), ([] : Path)) := layerAt_conj hconjT ((0 : Fin 1), ([] : Path))
  obtain ⟨a, b, c⟩ := hn
  unfold NR
  rw [h1, h2, hc0, hc1, hcT]
  exact ⟨b, a, c⟩

/-- **Twin existence**: every state of `Zp(A)` with roots `≤ L₄` has a state of the opposite sign with conjugate data. -/
theorem twin_state (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J) (σ : ℤˣ)
    {G : ST w ι pstar J} (hG : G ∈ zpSet p kind pstar J A sp0 hA σ) :
    ∃ G' ∈ zpSet p kind pstar J A sp0 hA (-σ), Rel G.1 G'.1 pstar := by
  obtain ⟨hGm, hσ, hR⟩ := hG
  have hb := (mem_zpFinset hA).1 hGm
  obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA hb.batch
  rw [he] at hR hσ
  have hn := (zpRootsLE_iff A hcan hel htc hcc con).1 hR
  obtain ⟨con', h1, h2, h3, h4⟩ := twin_con A hcan hel htc hcc con hn.1 hn.2.1 hn.2.2
  refine ⟨opState A sp0 hcan hel htc hcc con', ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (mem_zpFinset hA).2 (reach_opState A sp0 hcan hel htc hcc con')
  · show nuOf (opOut A pstar hcan hel htc hcc con') pstar = -σ
    rw [nuOf_op A hcan hel htc hcc con', srcSign_not A hcan hel htc hcc ε, ← hσ, nuOf_op A hcan hel htc hcc con]
  · exact (zpRootsLE_iff A hcan hel htc hcc con').2 (NR_conj A hcan hel htc hcc con con' hn h3 h4)
  · rw [he]
    show Rel (opOut A pstar hcan hel htc hcc con) (opOut A pstar hcan hel htc hcc con') pstar
    unfold Rel
    rw [sigStar_op A pstar hcan hel htc hcc con, sigStar_op A pstar hcan hel htc hcc con',
      zpData_op A hcan hel htc hcc con, zpData_op A hcan hel htc hcc con']
    exact ⟨h3, h4, h1, h2⟩

omit hcan hel htc hcc in
theorem rel_rel {G G'' G3 : FamilyReconstruction w ι} (h1 : Rel G G'' pstar) (h2 : Rel G'' G3 pstar)
    (hν : nuOf G pstar = nuOf G3 pstar) : sigStar G pstar = sigStar G3 pstar ∧ zpData G pstar = zpData G3 pstar := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  have e1 : (sigStar G3 pstar).2.1 = (sigStar G pstar).2.1 := by
    rw [b1, a1]; exact conjLayered_invol _ (fun x => Equiv.swap_apply_self _ _ x) _
  have e2 : (sigStar G3 pstar).2.2 = (sigStar G pstar).2.2 := by
    rw [b2, a2]; exact conjLayered_refl_refl _
  have e3 : (zpData G3 pstar).1 = (zpData G pstar).1 := by rw [b3, a3, conjCpl_conjCpl]
  have e4 : (zpData G3 pstar).2.1 = (zpData G pstar).2.1 := by rw [b4, a4, conjChain_conjChain]
  refine ⟨Prod.ext hν (Prod.ext e1.symm e2.symm), ?_⟩
  unfold zpData
  exact Prod.ext e3.symm (Prod.ext e4.symm (Prod.ext e1.symm e2.symm))

/-- **`ZpSurj.twin`**. -/
theorem zp_twin (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J) :
    ∃ τ : ST w ι pstar J → ST w ι pstar J,
      Set.BijOn τ (zpSet p kind pstar J A sp0 hA (-1)) (zpSet p kind pstar J A sp0 hA 1) ∧
      ∀ G ∈ zpSet p kind pstar J A sp0 hA (-1),
        IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
        IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2 ∧
        (zpData (τ G).1 pstar).1 = conjCpl (zpData G.1 pstar).1 ∧
        (zpData (τ G).1 pstar).2.1 = conjChain (zpData G.1 pstar).2.1 := by
  classical
  let τ : ST w ι pstar J → ST w ι pstar J := fun G =>
    if h : ∃ G' ∈ zpSet p kind pstar J A sp0 hA 1, Rel G.1 G'.1 pstar then Classical.choose h else G
  have hτ : ∀ G ∈ zpSet p kind pstar J A sp0 hA (-1), τ G ∈ zpSet p kind pstar J A sp0 hA 1 ∧ Rel G.1 (τ G).1 pstar := by
    intro G hG
    have h : ∃ G' ∈ zpSet p kind pstar J A sp0 hA 1, Rel G.1 G'.1 pstar := by
      obtain ⟨G', hG', hr⟩ := twin_state A hcan hel htc hcc hA sp0 (-1) hG
      exact ⟨G', by simpa using hG', hr⟩
    have : τ G = Classical.choose h := dif_pos h
    rw [this]
    exact Classical.choose_spec h
  refine ⟨τ, ⟨fun G hG => (hτ G hG).1, ?_, ?_⟩, fun G hG => ?_⟩
  · intro G1 hG1 G2 hG2 he
    have r1 := (hτ G1 hG1).2
    have r2 := (hτ G2 hG2).2
    rw [← he] at r2
    obtain ⟨a1, a2, a3, a4⟩ := r1
    obtain ⟨b1, b2, b3, b4⟩ := r2
    have e1 : (sigStar G1.1 pstar).2.1 = (sigStar G2.1 pstar).2.1 := by
      have := congrArg (fun L => conjLayered L (Equiv.swap (0 : Fin 2) 1)) (a1.symm.trans b1)
      simp only [conjLayered_invol _ (fun x => Equiv.swap_apply_self _ _ x)] at this
      exact this
    have e2 : (sigStar G1.1 pstar).2.2 = (sigStar G2.1 pstar).2.2 := by
      have := congrArg (fun L => conjLayered L (Equiv.refl (Fin 1))) (a2.symm.trans b2)
      simp only [conjLayered_refl_refl] at this
      exact this
    have hs : sigStar G1.1 pstar = sigStar G2.1 pstar := by
      have n1 : nuOf G1.1 pstar = -1 := hG1.2.1
      have n2 : nuOf G2.1 pstar = -1 := hG2.2.1
      exact Prod.ext (n1.trans n2.symm) (Prod.ext e1 e2)
    have hb1 := ((mem_zpFinset hA).1 hG1.1).batch
    have hb2 := ((mem_zpFinset hA).1 hG2.1).batch
    exact st_ext A sp0 ((mem_zpFinset hA).1 hG1.1) ((mem_zpFinset hA).1 hG2.1)
      (zp_eq_of_sigStar hA hb1 hb2 hs)
  · intro G' hG'
    obtain ⟨G'', hG'', hr⟩ := twin_state A hcan hel htc hcc hA sp0 1 hG'
    have hG''' : G'' ∈ zpSet p kind pstar J A sp0 hA (-1) := by simpa using hG''
    obtain ⟨hmem, hr2⟩ := hτ G'' hG'''
    refine ⟨G'', hG''', ?_⟩
    have hν : nuOf G'.1 pstar = nuOf (τ G'').1 pstar := hG'.2.1.trans hmem.2.1.symm
    obtain ⟨hs, -⟩ := rel_rel hr hr2 hν
    have hb1 := ((mem_zpFinset hA).1 hG'.1).batch
    have hb2 := ((mem_zpFinset hA).1 hmem.1).batch
    exact (st_ext A sp0 ((mem_zpFinset hA).1 hmem.1) ((mem_zpFinset hA).1 hG'.1)
      (zp_eq_of_sigStar hA hb2 hb1 hs.symm))
  · obtain ⟨-, a1, a2, a3, a4⟩ := hτ G hG
    refine ⟨?_, ?_, a3, a4⟩
    · rw [a1]; exact conjLayered_isConjugateCouple _
    · rw [a2]; exact conjLayered_isConjugateBy _ _

end WaveTurbulence.ZpSurj
