/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CohTrunk.Arm
public import WaveTurbulence.Foundations.Spine.PL234Draft.CohTransport
public import WaveTurbulence.Foundations.Spine.KernelCosetDecoration
public import WaveTurbulence.Foundations.Spine.CoherentObjects

/-!
# COH-TRUNK: Lemma 5.1 for coherent couples

The crossing nodes of a coherent couple (type 1/trivial: a root; type 2: a spine node of the arm whose root
parent layer is `p`), and the momentum there is `k`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

/-- The conclusion of Lemma 5.1 for a couple: at most one crossing node, at momentum `k`. -/
def CoupleCrossConcl {d : ℕ} (LG : LayeredGarden 2) (p q q' : ℕ) (k : Mom d)
    (K : GNode LG.garden.tree → Mom d) : Prop :=
  ((q' < p ∧ q = p) → ∃ z0 : GNode LG.garden.tree, z0.1.1 = 0 ∧ K z0 = k ∧
      ∀ z, NodeCr LG p ![q, q'] z ↔ z = z0) ∧
  ((q < p ∧ q' = p) → ∃ z0 : GNode LG.garden.tree, z0.1.1 = 1 ∧ K z0 = k ∧
      ∀ z, NodeCr LG p ![q, q'] z ↔ z = z0) ∧
  (¬ (q' < p ∧ q = p) → ¬ (q < p ∧ q' = p) → ∀ z, ¬ NodeCr LG p ![q, q'] z)

theorem hpH_of_canon {w p : ℕ} {H : LayeredGarden w} (hcan : IsCanonGC (p + 1) H) (x : Fin w × Path) :
    layerAt H x ≤ p := by
  by_cases hx : x.2 ∈ (H.garden.tree x.1).nodes
  · rw [layerAt_of_mem H hx]
    exact hcan.2.2.1 _
  · unfold layerAt
    rw [dif_neg hx]
    exact Nat.zero_le _

theorem coupleLayers_basic {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q' Q LG) :
    (∀ z : GNode LG.garden.tree, LG.layer z ≤ p) ∧ layerAt LG ((0 : Fin 2), []) ≤ q ∧
      layerAt LG ((1 : Fin 2), []) ≤ q' := by
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  have hlf := layerAt_rootEmb hQ hE hlay
  refine ⟨fun z => ?_, ?_, ?_⟩
  · rw [hlay z]
    exact hpH_of_canon hcan _
  · rw [hlf, rootEmb_zero, ← hpa]
    exact layerAt_le_parAt H p hcan.2.2.1 hE.nodeA
  · rw [hlf, rootEmb_one, ← hpb]
    exact layerAt_le_parAt H p hcan.2.2.1 hE.nodeB

theorem coupleCross_nt {d p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2} {k : Mom d}
    (hcoh : IsCoherentCoupleAt p q q' Q LG) (hqp : q ≤ p) (hq'p : q' ≤ p) (ht : Q.isType2 = false)
    (K : GNode LG.garden.tree → Mom d) (hKr : ∀ j, K (GNode.root LG.garden.tree j) = k) :
    CoupleCrossConcl LG p q q' k K := by
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hE, -, -, hcoh', hpa, hpb, hlay⟩ := hcoh
  have hlf := layerAt_rootEmb hQ hE hlay
  have hm : ∀ z ∈ cplNodes Q ((0 : Fin 2), []) ((1 : Fin 2), []), layerAt LG z = min q q' := by
    intro z hz
    rw [hlf z]
    have := layerreg1_type1 hcan.2.2 hcan.1 hwf hE hcoh' ht
    rw [hpa, hpb] at this
    apply this
    have hmap := cplNodes_map Q (rootEmb a b) (rootEmb_hom a b) ((0 : Fin 2), []) ((1 : Fin 2), [])
    rw [rootEmb_zero, rootEmb_one] at hmap
    rw [hmap]
    exact Finset.mem_image_of_mem _ hz
  have hlay_node : ∀ z : GNode LG.garden.tree, layerAt LG z.1 = min q q' :=
    fun z => hm _ (cplNodes_covers_node hQ z)
  have hNC : ∀ z : GNode LG.garden.tree, NodeCr LG p ![q, q'] z ↔
      z.1.2 = [] ∧ min q q' < p ∧ (![q, q'] : Fin 2 → ℕ) z.1.1 = p := by
    intro z
    by_cases hr : z.1.2 = []
    · have e : z.1 = (z.1.1, []) := Prod.ext rfl hr
      rw [nodeCr_iff]
      unfold Cr
      rw [if_pos e, hlay_node z]
      simp [hr]
    · refine iff_of_false ?_ (fun hh => hr hh.1)
      apply not_nodeCr_of_under (p := p) ![q, q'] z (x := (z.1.1, []))
      · exact TTree.nil_mem_nodes _
      · exact ⟨rfl, List.nil_prefix⟩
      · intro e
        exact hr (congrArg Prod.snd e)
      · rw [hlay_node z]
        exact (hlay_node (GNode.root LG.garden.tree z.1.1)).symm
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 h2 z => ?_⟩
  · refine ⟨GNode.root LG.garden.tree 0, rfl, hKr 0, fun z => ?_⟩
    rw [hNC]
    constructor
    · rintro ⟨hr, hmin, hq⟩
      rcases z with ⟨⟨j, path⟩, hz⟩
      fin_cases j
      · exact Subtype.ext (Prod.ext rfl hr)
      · simp at hq
        omega
    · rintro rfl
      refine ⟨rfl, ?_, ?_⟩
      · omega
      · show q = p
        exact h1.2
  · refine ⟨GNode.root LG.garden.tree 1, rfl, hKr 1, fun z => ?_⟩
    rw [hNC]
    constructor
    · rintro ⟨hr, hmin, hq⟩
      rcases z with ⟨⟨j, path⟩, hz⟩
      fin_cases j
      · simp at hq
        omega
      · exact Subtype.ext (Prod.ext rfl hr)
    · rintro rfl
      refine ⟨rfl, ?_, ?_⟩
      · omega
      · show q' = p
        exact h1.2
  · rw [hNC]
    rintro ⟨hr, hmin, hq⟩
    rcases z with ⟨⟨j, path⟩, hz⟩
    fin_cases j
    · simp at hq
      omega
    · simp at hq
      omega

theorem coupleCross_t2 {d p q q' : ℕ} {Xp Xm : RegChain} {Qlp : RegCpl} {LG : LayeredGarden 2} {k : Mom d}
    (hcoh : IsCoherentCoupleAt p q q' (.type2 Xp Xm Qlp) LG) (hqp : q ≤ p) (hq'p : q' ≤ p)
    (K : GNode LG.garden.tree → Mom d) (hK : IsDecoration LG.garden K)
    (hKr : ∀ j, K (GNode.root LG.garden.tree j) = k) :
    CoupleCrossConcl LG p q q' k K := by
  obtain ⟨hp, hu0, hu1⟩ := coupleLayers_basic hcoh
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hE, -, -, hcoh', hpa, hpb, hlay⟩ := hcoh
  obtain ⟨hL, hPLp, hPLm, -, -⟩ := layerreg1_type2 hcan.2.2 hcan.1 hwf hE hcoh'
  rw [hpa, hpb] at hL
  have hf := rootEmb_hom a b
  have hlf := layerAt_rootEmb hQ hE hlay
  have PLp : ChainPairLayers LG Xp 1 ((0 : Fin 2), []) :=
    chainPairLayers_map H LG (rootEmb a b) hf hlf Xp 1 _ (by rw [rootEmb_zero]; exact hPLp)
  have PLm : ChainPairLayers LG Xm (-1) ((1 : Fin 2), []) :=
    chainPairLayers_map H LG (rootEmb a b) hf hlf Xm (-1) _ (by rw [rootEmb_one]; exact hPLm)
  have hlp : ∀ z ∈ cplNodes Qlp ((0 : Fin 2), Xp.lonePath) ((1 : Fin 2), Xm.lonePath),
      layerAt LG z = min q q' := by
    intro z hz
    rw [hlf]
    apply hL
    have e1 : rootEmb a b ((0 : Fin 2), Xp.lonePath) = addrExt a Xp.lonePath := by simp [rootEmb]
    have e2 : rootEmb a b ((1 : Fin 2), Xm.lonePath) = addrExt b Xm.lonePath := by simp [rootEmb]
    have hmapL := cplNodes_map Qlp (rootEmb a b) hf ((0 : Fin 2), Xp.lonePath)
      ((1 : Fin 2), Xm.lonePath)
    rw [e1, e2] at hmapL
    rw [hmapL]
    exact Finset.mem_image_of_mem _ hz
  obtain ⟨Cp, Cm, -⟩ := (Embeds.of_decodes hQ).type2
  have ea : addrExt ((0 : Fin 2), ([] : Path)) Xp.lonePath = ((0 : Fin 2), Xp.lonePath) := by
    simp [addrExt]
  have eb : addrExt ((1 : Fin 2), ([] : Path)) Xm.lonePath = ((1 : Fin 2), Xm.lonePath) := by
    simp [addrExt]
  have hlone0 : layerAt LG (addrExt ((0 : Fin 2), ([] : Path)) Xp.lonePath) = min q q' := by
    rw [ea]
    exact hlp _ (left_mem_cplNodes Qlp _ _)
  have hlone1 : layerAt LG (addrExt ((1 : Fin 2), ([] : Path)) Xm.lonePath) = min q q' := by
    rw [eb]
    exact hlp _ (right_mem_cplNodes Qlp _ _)
  have hq0 := arm_cross hp Xp 1 (0 : Fin 2) Cp PLp ![q, q'] (by simpa using hu0) (by simpa using hqp)
  have hq1 := arm_cross hp Xm (-1) (1 : Fin 2) Cm PLm ![q, q'] (by simpa using hu1)
    (by simpa using hq'p)
  have nLa := nodeOfChainEmb Cp
  have nLb := nodeOfChainEmb Cm
  -- the Qlp region carries no further crossing
  have hqlp : ∀ z : GNode LG.garden.tree,
      z.1 ∈ cplNodes Qlp (addrExt ((0 : Fin 2), ([] : Path)) Xp.lonePath)
        (addrExt ((1 : Fin 2), ([] : Path)) Xm.lonePath) → NodeCr LG p ![q, q'] z →
      z.1 = addrExt ((0 : Fin 2), ([] : Path)) Xp.lonePath ∨
        z.1 = addrExt ((1 : Fin 2), ([] : Path)) Xm.lonePath := by
    intro z hz hc
    by_contra hne
    push_neg at hne
    have hzm : layerAt LG z.1 = min q q' := by
      rw [ea, eb] at hz
      exact hlp _ hz
    rcases cplNodes_region hz with hu | hu
    · exact not_nodeCr_of_under (p := p) ![q, q'] z nLa hu hne.1 (hzm.trans hlone0.symm) hc
    · exact not_nodeCr_of_under (p := p) ![q, q'] z nLb hu hne.2 (hzm.trans hlone1.symm) hc
  have hD : ∀ z : GNode LG.garden.tree, NodeCr LG p ![q, q'] z →
      z.1 ∈ spinePos Xp ((0 : Fin 2), []) ∨ z.1 ∈ spinePos Xm ((1 : Fin 2), []) := by
    intro z hc
    have hz := cplNodes_covers_node hQ z
    rcases mem_cplNodes_type2.1 hz with h1 | h1 | h1
    · exact Or.inl (hq0.1 z h1 hc)
    · exact Or.inr (hq1.1 z h1 hc)
    · rcases hqlp z h1 hc with h2 | h2
      · exact Or.inl (h2 ▸ lone_mem_spinePos Xp _)
      · exact Or.inr (h2 ▸ lone_mem_spinePos Xm _)
  -- momentum along the spines
  have hdec := cplDec_of_decoration hQ hK
  obtain ⟨hdp, hdm, -⟩ := hdec
  have hf0 : extend K ((0 : Fin 2), ([] : Path)) = k :=
    (extend_node K (GNode.root LG.garden.tree 0)).trans (hKr 0)
  have hf1 : extend K ((1 : Fin 2), ([] : Path)) = k :=
    (extend_node K (GNode.root LG.garden.tree 1)).trans (hKr 1)
  have mom0 : ∀ z : GNode LG.garden.tree, z.1 ∈ spinePos Xp ((0 : Fin 2), []) → K z = k := by
    intro z hz
    rw [← extend_node K z, spine_dec (extend K) Xp 1 _ hdp z.1 hz, hf0]
  have mom1 : ∀ z : GNode LG.garden.tree, z.1 ∈ spinePos Xm ((1 : Fin 2), []) → K z = k := by
    intro z hz
    rw [← extend_node K z, spine_dec (extend K) Xm (-1) _ hdm z.1 hz, hf1]
  have c0 := hq0.2.2
  have c1 := hq1.2.2
  rw [hlone0] at c0
  rw [hlone1] at c1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at c0 c1
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 h2 z hc => ?_⟩
  · obtain ⟨z0, hz0, hc0⟩ := c0.2 ⟨h1.2, by omega⟩
    refine ⟨z0, (spinePos_under _ _ z0.1 hz0).1.1.symm, mom0 z0 hz0, fun z => ⟨fun hc => ?_, ?_⟩⟩
    · rcases hD z hc with hz | hz
      · exact hq0.2.1 z z0 hz hz0 hc hc0
      · have := (c1.1 ⟨z, hz, hc⟩).1
        omega
    · rintro rfl
      exact hc0
  · obtain ⟨z0, hz0, hc0⟩ := c1.2 ⟨h1.2, by omega⟩
    refine ⟨z0, (spinePos_under _ _ z0.1 hz0).1.1.symm, mom1 z0 hz0, fun z => ⟨fun hc => ?_, ?_⟩⟩
    · rcases hD z hc with hz | hz
      · have := (c0.1 ⟨z, hz, hc⟩).1
        omega
      · exact hq1.2.1 z z0 hz hz0 hc hc0
    · rintro rfl
      exact hc0
  · rcases hD z hc with hz | hz
    · have := c0.1 ⟨z, hz, hc⟩
      omega
    · have := c1.1 ⟨z, hz, hc⟩
      omega

end WaveTurbulence.Flower.CohTrunk
