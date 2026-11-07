/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Idx

/-! # BOT-DECOMP: `BotSurj`, `BotLayers` for the bottom class (mirror of ZP-SURJ's `zpSurj_of_state`, `zpLayers_of_state`)

ZP-SURJ's construction (`exists_construction`, soundness, `state_of_datum`, `classify`, `twin_con`, `carrier_of_IIb`, `carrierOf_IIb`, `carrier_datum`,
`zpRootsLE_iff`, `op_numbers`, ...) is state-level; only its last layer (`twin_state`, `zp_twin`, `zp_carrier`, `zp_coherent`, `zpLayers_of_start`)
refers to the index type `ST` and `ReachSp`.  Here the same last layer is redone for `BT` and `Reach` (`mem_canonFinset_iff_bottom`):
the class of the bottom vine is `{states reached by one operation at `pstar` or the skip}` with their chain regions (`Reach.region_unique` replaces `st_ext`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.ConjCoh
  WaveTurbulence.ZpSurj

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [DecidableEq ι] [Fintype ι]
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
  (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton)
  (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))

/-- The exact conjugacy relation between the exceptional data of two states (mirror of ZP-SURJ's `Rel`, which is not exposed). -/
@[expose] def BRel (G G' : FamilyReconstruction w ι) (i : ι) : Prop :=
  (sigStar G' i).2.1 = conjLayered (sigStar G i).2.1 (Equiv.swap (0 : Fin 2) 1) ∧
  (sigStar G' i).2.2 = conjLayered (sigStar G i).2.2 (Equiv.refl (Fin 1)) ∧
  (zpData G' i).1 = conjCpl (zpData G i).1 ∧ (zpData G' i).2.1 = conjChain (zpData G i).2.1

theorem bRel_rel {G G'' G3 : FamilyReconstruction w ι} (h1 : BRel G G'' pstar) (h2 : BRel G'' G3 pstar)
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

/-- The pair (state, chain region) reached by the operation with a given construction. -/
@[expose] noncomputable def opBT {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) : BT w ι :=
  ⟨opOut A pstar hcan hel htc hcc con, ChainAt.nextA A c0 pstar ε⟩

include hA hup in
theorem opBT_mem {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    opBT A hcan hel htc hcc c0 con ∈ canonFinsetK p kind A c0 :=
  (mem_canonFinset_iff_bottom hA hup).2
    (Reach.apply (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar) (Reach.nil _ _))

include hA hup

theorem bt_ext {G G' : BT w ι} (h : G ∈ canonFinsetK p kind A c0) (h' : G' ∈ canonFinsetK p kind A c0) (e : G.1 = G'.1) : G = G' := by
  obtain ⟨X, s1⟩ := G
  obtain ⟨X', s2⟩ := G'
  change X = X' at e
  subst e
  have : s1 = s2 := Reach.region_unique (List.nodup_singleton pstar) (List.nodup_singleton pstar)
    ((mem_canonFinset_iff_bottom hA hup).1 h) ((mem_canonFinset_iff_bottom hA hup).1 h')
  subst this
  rfl

/-- **Classification**: every pair of the bottom class has as state the output of an operation (the skip is the identity operation). -/
theorem bot_classify {G : BT w ι} (hG : G ∈ canonFinsetK p kind A c0) :
    ∃ (ε : Bool) (con : LFConstruction (A.source pstar hcan hel htc hcc) ε), G.1 = opOut A pstar hcan hel htc hcc con :=
  classify A hcan hel htc hcc hA ((mem_canonFinset_iff_bottom hA hup).1 hG).batch

include hcan hel htc hcc

/-- **`BotSurj.coherent`**. -/
theorem bot_coherent :
    ∀ G ∈ canonFinsetK p kind A c0,
      IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQQ G.1 pstar).2 (zpCodeC G.1 pstar) (zpObjC G.1 pstar) ∧
      IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpBranchQ G.1 pstar).2 (zpCodeT G.1 pstar) (zpObjT G.1 pstar) := by
  intro G hG
  obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG
  rw [he]
  exact coherent_of_native _ _ (nativeCoh_op A pstar hcan hel htc hcc con)

/-- **Twin existence** at the level of pairs. -/
theorem bot_twin_state (σ : ℤˣ) {G : BT w ι} (hG : G ∈ botSet p kind pstar A c0 σ) :
    ∃ G' ∈ botSet p kind pstar A c0 (-σ), BRel G.1 G'.1 pstar := by
  obtain ⟨hGm, hσ, hR⟩ := hG
  obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hGm
  rw [he] at hR hσ
  have hn := (zpRootsLE_iff A hcan hel htc hcc con).1 hR
  obtain ⟨con', h1, h2, h3, h4⟩ := twin_con A hcan hel htc hcc con hn.1 hn.2.1 hn.2.2
  refine ⟨opBT A hcan hel htc hcc c0 con', ⟨?_, ?_, ?_⟩, ?_⟩
  · exact opBT_mem A hcan hel htc hcc c0 hA hup con'
  · show nuOf (opOut A pstar hcan hel htc hcc con') pstar = -σ
    rw [nuOf_op A hcan hel htc hcc con', srcSign_not A hcan hel htc hcc ε, ← hσ, nuOf_op A hcan hel htc hcc con]
  · exact (zpRootsLE_iff A hcan hel htc hcc con').2 (NR_conj A hcan hel htc hcc con con' hn h3 h4)
  · rw [he]
    show BRel (opOut A pstar hcan hel htc hcc con) (opOut A pstar hcan hel htc hcc con') pstar
    unfold BRel
    rw [sigStar_op A pstar hcan hel htc hcc con, sigStar_op A pstar hcan hel htc hcc con',
      zpData_op A hcan hel htc hcc con, zpData_op A hcan hel htc hcc con']
    exact ⟨h3, h4, h1, h2⟩

/-- **`BotSurj.twin`**. -/
theorem bot_twin :
    ∃ τ : BT w ι → BT w ι,
      Set.BijOn τ (botSet p kind pstar A c0 (-1)) (botSet p kind pstar A c0 1) ∧
      ∀ G ∈ botSet p kind pstar A c0 (-1),
        IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
        IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2 ∧
        (zpData (τ G).1 pstar).1 = conjCpl (zpData G.1 pstar).1 ∧
        (zpData (τ G).1 pstar).2.1 = conjChain (zpData G.1 pstar).2.1 := by
  classical
  let τ : BT w ι → BT w ι := fun G =>
    if h : ∃ G' ∈ botSet p kind pstar A c0 1, BRel G.1 G'.1 pstar then Classical.choose h else G
  have hτ : ∀ G ∈ botSet p kind pstar A c0 (-1), τ G ∈ botSet p kind pstar A c0 1 ∧ BRel G.1 (τ G).1 pstar := by
    intro G hG
    have h : ∃ G' ∈ botSet p kind pstar A c0 1, BRel G.1 G'.1 pstar := by
      obtain ⟨G', hG', hr⟩ := bot_twin_state A hcan hel htc hcc c0 hA hup (-1) hG
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
    have hb1 := ((mem_canonFinset_iff_bottom hA hup).1 hG1.1).batch
    have hb2 := ((mem_canonFinset_iff_bottom hA hup).1 hG2.1).batch
    exact bt_ext A c0 hA hup hG1.1 hG2.1 (zp_eq_of_sigStar hA hb1 hb2 hs)
  · intro G' hG'
    obtain ⟨G'', hG'', hr⟩ := bot_twin_state A hcan hel htc hcc c0 hA hup 1 hG'
    have hG''' : G'' ∈ botSet p kind pstar A c0 (-1) := by simpa using hG''
    obtain ⟨hmem, hr2⟩ := hτ G'' hG'''
    refine ⟨G'', hG''', ?_⟩
    have hν : nuOf G'.1 pstar = nuOf (τ G'').1 pstar := hG'.2.1.trans hmem.2.1.symm
    obtain ⟨hs, -⟩ := bRel_rel hr hr2 hν
    have hb1 := ((mem_canonFinset_iff_bottom hA hup).1 hG'.1).batch
    have hb2 := ((mem_canonFinset_iff_bottom hA hup).1 hmem.1).batch
    exact (bt_ext A c0 hA hup hmem.1 hG'.1 (zp_eq_of_sigStar hA hb2 hb1 hs.symm))
  · obtain ⟨-, a1, a2, a3, a4⟩ := hτ G hG
    refine ⟨?_, ?_, a3, a4⟩
    · rw [a1]; exact conjLayered_isConjugateCouple _
    · rw [a2]; exact conjLayered_isConjugateBy _ _

/-- **`BotSurj.carrier`**. -/
theorem bot_carrier :
    Set.BijOn (fun G : BT w ι => zpCarrierOf G.1 pstar) (botSet p kind pstar A c0 (-1)) {c | ZpCarrier p A pstar c} := by
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    obtain ⟨hGm, hσ, hR⟩ := hG
    obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hGm
    rw [he] at hR hσ
    show ZpCarrier p A pstar (zpCarrierOf G.1 pstar)
    rw [he]
    exact carrier_of_IIb A hcan hel htc hcc con hσ ((zpRootsLE_iff A hcan hel htc hcc con).1 hR)
  · intro G1 hG1 G2 hG2 he
    obtain ⟨ε1, con1, e1⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG1.1
    obtain ⟨ε2, con2, e2⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG2.1
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
    exact bt_ext A c0 hA hup hG1.1 hG2.1
      (zp_eq_of_sigStar hA ((mem_canonFinset_iff_bottom hA hup).1 hG1.1).batch
        ((mem_canonFinset_iff_bottom hA hup).1 hG2.1).batch hs)
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
    refine ⟨opBT A hcan hel htc hcc c0 con, ⟨?_, hv, (zpRootsLE_iff A hcan hel htc hcc con).2 hNR⟩, ?_⟩
    · exact opBT_mem A hcan hel htc hcc c0 hA hup con
    · show zpCarrierOf (opOut A pstar hcan hel htc hcc con) pstar = _
      rw [carrierOf_IIb A hcan hel htc hcc con hv, h1, h2, h3, h4, conjChain_conjChain, conjLayered_refl_refl]

/-- **`BotSurj`**: the class of the bottom vine realizes the whole coherent pair carrier (R51, R60). -/
theorem botSurj_of_state : BotSurj p kind pstar A c0 :=
  ⟨bot_coherent A hcan hel htc hcc c0 hA hup, bot_twin A hcan hel htc hcc c0 hA hup, bot_carrier A hcan hel htc hcc c0 hA hup⟩

/-- **`BotLayers`**: the layer numerals of the bottom vine. -/
theorem botLayers_of_state : BotLayers p kind pstar A c0 := by
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have h2 := L2_le_q2 A pstar hcan hel htc hcc
  have h3 := q1_le_p A pstar hcan hel htc hcc
  have h4 := q2_le_p A pstar hcan hel htc hcc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [WaveTurbulence.ZpSurj.zpQ2_eq, WaveTurbulence.ZpSurj.zpQ4_eq]
    exact le_min (le_max_right _ _) h2
  · rw [WaveTurbulence.ZpSurj.zpQ4_eq]
    exact (min_le_right _ _).trans h4
  · intro G hG
    obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG
    rw [he, zpQQ_eq]
    obtain ⟨hL, hn⟩ := op_numbers A hcan hel htc hcc con
    rw [WaveTurbulence.ZpSurj.zpQ2_eq]
    rcases hn with ⟨-, hr⟩ | ⟨-, hr⟩
    · rw [hr, hL]; exact ⟨rfl, h1, h3⟩
    · rw [hr, hL]; exact ⟨rfl, h2, h4⟩
  · intro G hG
    obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG
    rw [he]
    obtain ⟨hL, hn⟩ := op_numbers A hcan hel htc hcc con
    rw [WaveTurbulence.ZpSurj.zpQ2_eq]
    rcases hn with ⟨hr, -⟩ | ⟨hr, -⟩
    · rw [hr, hL]; exact ⟨rfl, h2⟩
    · rw [hr, hL]; exact ⟨rfl, h1⟩

end WaveTurbulence.VineEstS5C.P4.Bot
