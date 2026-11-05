/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.LayerReg.Spine

/-!
# Coherent layered regular couples in canonical gardens (TARGET Prop `layerreg1`, part (1))

Setting (TARGET L898–L907): a layered garden `LG` satisfying the canonicity criterion
`CanonCriterion p` (T Prop `canonequiv`; this is `𝒢_{p+1}` / `𝒞_{p+1}` without properness and
irreducibility, which are not used), plain (all leaves paired); a regular couple `𝒬` with code `Q`
embedded at `(a, b)` (`Embeds`), coherent (`CohOn`, T Def `defcoh`); `q = parAt a`, `q' = parAt b` the
parent layers of its roots (`p` for a root of the garden).

`cpl_coherent` (by induction on the structure, as in TARGET's proof):
* (T1) if `𝒬` is trivial or of type 1, all its nodes are in layer `min(q, q')`;
* (T3) if `q = q'`, all its nodes are in layer `q` (any type);
`chain_coherent`: along an embedded coherent chain, each pair `{a, b}` has `𝔏_{𝔫_a} = 𝔏_{𝔫_b}` and all
nodes of its couples `𝒬_{j,ι}` are in this layer (`ChainPairLayers`).

The type-2 step is TARGET's argument: the roots of `𝒬_lp` are in a common layer `q_*`; if
`q_* < min(q, q')`, the first spine positions of the two chains in layer `q_*` (`spine_cut`) have
parents above `q_*`, and the union of their subtrees is closed under the leaf pairs
(`type2_pairedUnder`); this contradicts the criterion. Hence `q_* = min(q, q')`.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **Coherence** on a list of links (T Def `defcoh`): both nodes of every link are in the same
layer. -/
def CohOn (LG : LayeredGarden w) (L : List ((Fin w × Path) × (Fin w × Path))) : Prop :=
  ∀ l ∈ L, layerAt LG l.1 = layerAt LG l.2

/-- **The layers along a chain** (TARGET `layerreg1`): for every pair `{a, b}` of the chain (at any
nesting level), `𝔏_{𝔫_a} = 𝔏_{𝔫_b}` and all nodes of the couples `𝒬_{j,ι}` are in this layer. -/
def ChainPairLayers (LG : LayeredGarden w) : RegChain → ℤˣ → (Fin w × Path) → Prop
  | .nil, _, _ => True
  | .pair m Qr Qg inner rest, ζ, a =>
    layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) = layerAt LG a ∧
    (∀ z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])), layerAt LG z = layerAt LG a) ∧
    (∀ z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])), layerAt LG z = layerAt LG a) ∧
    ChainPairLayers LG inner (slotSign ζ m.c) (addrExt a [m.c]) ∧
    ChainPairLayers LG rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

variable {LG : LayeredGarden w} {p : ℕ}

theorem min_eq_of_crit {la lb pa pb : ℕ} (hab : la = lb) (ha : la ≤ pa) (hb : lb ≤ pb)
    (hc : min pa pb ≤ max la lb) : la = min pa pb := by
  subst hab
  rw [max_self] at hc
  exact le_antisymm (le_min ha hb) hc

theorem parAt_bottom {a : Fin w × Path} (L : Path) (k : Fin 3)
    (h : (addrExt a (L ++ [k])).2 ∈ (LG.garden.tree (addrExt a (L ++ [k])).1).nodes) :
    parAt LG p (addrExt a (L ++ [k])) = layerAt LG (addrExt a L) := by
  have e : addrExt a (L ++ [k]) = addrExt (addrExt a L) [k] := (addrExt_append a L [k]).symm
  rw [e] at h ⊢
  exact parAt_child LG p k h

/-- Every node of an embedded chain with `ChainPairLayers` is at least as high as the lone position. -/
theorem chain_lower : (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) → (h : TTree) →
    ChainEmb LG.garden X ζ a h → ChainPairLayers LG X ζ a →
    ∀ z ∈ chainNodesSet X ζ a, layerAt LG (addrExt a X.lonePath) ≤ layerAt LG z
  | .nil, _, _, _, _, _, z, hz => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, h, hC, hL, z, hz => by
    obtain ⟨ER, EG, EI, ES⟩ := hC.parts
    obtain ⟨hnb, hR, hG, hI, hS⟩ := hL
    have hlone := nodeOfChainEmb hC
    have nb_node := nodeOfChainEmb EI
    rw [addrExt_append] at nb_node
    have lone_eq : addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt a ([m.c] ++ inner.lonePath)) ([m.lone] ++ rest.lonePath) := by
      simp [RegChain.lonePath, addrExt_append]
    have l_nb : layerAt LG (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) ≤
        layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) := by
      apply layerAt_le_of_under LG nb_node hlone
      rw [lone_eq]; exact under_ext _ _
    have l_a : layerAt LG (addrExt a (RegChain.pair m Qr Qg inner rest).lonePath) ≤ layerAt LG a :=
      layerAt_le_of_under LG hC.node hlone (under_ext _ _)
    rcases mem_chainNodesSet_pair hz with rfl | rfl | h' | h' | h' | h'
    · exact l_a
    · exact l_nb
    · rw [hR z h']; exact l_a
    · rw [hG z h']; exact l_a
    · have := chain_lower inner _ _ _ EI hI z h'
      rw [addrExt_append] at this
      exact l_nb.trans this
    · have := chain_lower rest _ _ _ ES hS z h'
      rw [← chain_lonePath_eq] at this
      exact this

mutual
/-- **TARGET Prop `layerreg1` (1), couples**: (T1) a trivial or type-1 coherent embedded regular couple
lies in layer `min(q, q')`; (T3) if `q = q'`, every coherent embedded regular couple lies in layer `q`. -/
theorem cpl_coherent (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain) :
    (Q : RegCpl) → (a b : Fin w × Path) → Q.wf = true → Embeds LG.garden Q a b →
    CohOn LG (Q.linksAt a b) →
    (Q.isType2 = false →
      ∀ z ∈ cplNodes Q a b, layerAt LG z = min (parAt LG p a) (parAt LG p b)) ∧
    (parAt LG p a = parAt LG p b → ∀ z ∈ cplNodes Q a b, layerAt LG z = parAt LG p a)
  | .triv, a, b, _, hE, _ => by
    have hpair : layerAt LG a = layerAt LG b := hE.pair_layer LG (q := (a, b)) (by simp [RegCpl.pairsAt])
    have hpu : PairedUnder (RegCpl.triv.pairsAt a b) a b := by
      intro q hq
      simp only [RegCpl.pairsAt, List.mem_singleton] at hq
      subst hq
      exact ⟨fun _ => Or.inr (under_refl _), fun _ => Or.inl (under_refl _)⟩
    have hc := crit_apply hcan hplain hE hE.nodeA hE.nodeB (Or.inl (under_refl a))
      (Or.inr (under_refl b)) hE.indep hpu
    have key := min_eq_of_crit hpair (layerAt_le_parAt LG p hcan.1 hE.nodeA)
      (layerAt_le_parAt LG p hcan.1 hE.nodeB) hc
    have all : ∀ z ∈ cplNodes RegCpl.triv a b, layerAt LG z = min (parAt LG p a) (parAt LG p b) := by
      intro z hz
      rcases mem_cplNodes_triv.1 hz with rfl | rfl
      · exact key
      · rw [← hpair]; exact key
    exact ⟨fun _ => all, fun he z hz => (all z hz).trans (by rw [he, min_self])⟩
  | .type1 c Q₁ Q₂ Q₃, a, b, hwf, hE, hcoh => by
    simp only [RegCpl.wf, Bool.and_eq_true] at hwf
    obtain ⟨E1, E2, E3⟩ := hE.type1
    have hab : layerAt LG a = layerAt LG b := hcoh (a, b) List.mem_cons_self
    have c1 : CohOn LG (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])) := fun l hl =>
      hcoh l (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hl)))
    have c2 : CohOn LG (Q₂.linksAt (addrExt b [1]) (addrExt a [1])) := fun l hl =>
      hcoh l (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hl)))
    have c3 : CohOn LG (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])) := fun l hl =>
      hcoh l (List.mem_cons_of_mem _ (List.mem_append_right _ hl))
    have hpu : PairedUnder ((RegCpl.type1 c Q₁ Q₂ Q₃).pairsAt a b) a b := by
      intro q hq
      have r1 := cpl_endpoints_under (RegCpl.type1 c Q₁ Q₂ Q₃) a b q.1 (Finset.mem_union_right _
        ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩))
      have r2 := cpl_endpoints_under (RegCpl.type1 c Q₁ Q₂ Q₃) a b q.2 (Finset.mem_union_right _
        ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩))
      exact ⟨fun _ => r2, fun _ => r1⟩
    have hc := crit_apply hcan hplain hE hE.nodeA hE.nodeB (Or.inl (under_refl a))
      (Or.inr (under_refl b)) hE.indep hpu
    have key := min_eq_of_crit hab (layerAt_le_parAt LG p hcan.1 hE.nodeA)
      (layerAt_le_parAt LG p hcan.1 hE.nodeB) hc
    have pa0 : parAt LG p (addrExt a [0]) = layerAt LG a := parAt_child LG p 0 E1.nodeA
    have pb0 : parAt LG p (addrExt b [c.partner 0]) = layerAt LG a :=
      (parAt_child LG p _ E1.nodeB).trans hab.symm
    have pb1 : parAt LG p (addrExt b [1]) = layerAt LG a := (parAt_child LG p 1 E2.nodeA).trans hab.symm
    have pa1 : parAt LG p (addrExt a [1]) = layerAt LG a := parAt_child LG p 1 E2.nodeB
    have pa2 : parAt LG p (addrExt a [2]) = layerAt LG a := parAt_child LG p 2 E3.nodeA
    have pb2 : parAt LG p (addrExt b [c.partner 2]) = layerAt LG a :=
      (parAt_child LG p _ E3.nodeB).trans hab.symm
    have I1 := (cpl_coherent hcan hplain Q₁ _ _ hwf.1.1 E1 c1).2 (pa0.trans pb0.symm)
    have I2 := (cpl_coherent hcan hplain Q₂ _ _ hwf.1.2 E2 c2).2 (pb1.trans pa1.symm)
    have I3 := (cpl_coherent hcan hplain Q₃ _ _ hwf.2 E3 c3).2 (pa2.trans pb2.symm)
    have all : ∀ z ∈ cplNodes (RegCpl.type1 c Q₁ Q₂ Q₃) a b, layerAt LG z = layerAt LG a := by
      intro z hz
      rcases mem_cplNodes_type1.1 hz with rfl | rfl | h | h | h
      · rfl
      · exact hab.symm
      · rw [I1 z h, pa0]
      · rw [I2 z h, pb1]
      · rw [I3 z h, pa2]
    exact ⟨fun _ z hz => (all z hz).trans key,
      fun he z hz => (all z hz).trans (key.trans (by rw [he, min_self]))⟩
  | .type2 Xp Xm Qlp, a, b, hwf, hE, hcoh => by
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf
    obtain ⟨⟨⟨⟨wp, wm⟩, wl⟩, wlt⟩, -⟩ := hwf
    obtain ⟨Cp, Cm, El⟩ := hE.type2
    have cohP : CohOn LG (Xp.linksAt 1 a) := fun l hl =>
      hcoh l (List.mem_append_left _ (List.mem_append_left _ hl))
    have cohM : CohOn LG (Xm.linksAt (-1) b) := fun l hl =>
      hcoh l (List.mem_append_left _ (List.mem_append_right _ hl))
    have cohL : CohOn LG (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) := fun l hl =>
      hcoh l (List.mem_append_right _ hl)
    have LP := chain_coherent hcan hplain Xp 1 a _ wp Cp cohP
    have LM := chain_coherent hcan hplain Xm (-1) b _ wm Cm cohM
    have IL := (cpl_coherent hcan hplain Qlp _ _ wl El cohL).1 wlt
    have hu := IL _ (left_mem_cplNodes _ _ _)
    have hv := IL _ (right_mem_cplNodes _ _ _)
    have upA : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) ≤
        parAt LG p a := by
      rw [← hu]
      exact (layerAt_le_of_under LG hE.nodeA El.nodeA (under_ext a _)).trans
        (layerAt_le_parAt LG p hcan.1 hE.nodeA)
    have upB : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) ≤
        parAt LG p b := by
      rw [← hv]
      exact (layerAt_le_of_under LG hE.nodeB El.nodeB (under_ext b _)).trans
        (layerAt_le_parAt LG p hcan.1 hE.nodeB)
    have heq : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) =
        min (parAt LG p a) (parAt LG p b) := by
      by_contra hne
      have hlt := lt_of_le_of_ne (le_min upA upB) hne
      obtain ⟨sP, hsP, hsP1, hsP2⟩ := spine_cut Xp 1 a _ Cp (fun l hl => cohP l (spineLinks_sub _ _ _ l hl)) _ hu
        (lt_of_lt_of_le hlt (min_le_left _ _))
      obtain ⟨sM, hsM, hsM1, hsM2⟩ := spine_cut Xm (-1) b _ Cm (fun l hl => cohM l (spineLinks_sub _ _ _ l hl)) _ hv
        (lt_of_lt_of_le hlt (min_le_right _ _))
      have uP := spinePos_under Xp a sP hsP
      have uM := spinePos_under Xm b sM hsM
      have hc := crit_apply hcan hplain hE (spinePos_node Cp hsP) (spinePos_node Cm hsM)
        (Or.inl uP.1) (Or.inr uM.1) (indep_of_under hE.indep uP.1 uM.1)
        (type2_pairedUnder Xp Xm Qlp hE.indep hsP hsM)
      rw [hsP1, hsM1, max_self] at hc
      exact absurd hc (not_le.2 (lt_min hsP2 hsM2))
    refine ⟨fun h => by simp [RegCpl.isType2] at h, fun he z hz => ?_⟩
    have nz := hE.mem_nodes hz
    have lower : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) ≤
        layerAt LG z := by
      rcases mem_cplNodes_type2.1 hz with h | h | h
      · rw [← hu]; exact chain_lower Xp 1 a _ Cp LP z h
      · rw [← hv]; exact chain_lower Xm (-1) b _ Cm LM z h
      · rw [IL z h]
    have upper : layerAt LG z ≤ parAt LG p a := by
      rcases cpl_endpoints_under _ a b z hz with h | h
      · exact (layerAt_le_of_under LG hE.nodeA nz h).trans (layerAt_le_parAt LG p hcan.1 hE.nodeA)
      · rw [he]
        exact (layerAt_le_of_under LG hE.nodeB nz h).trans (layerAt_le_parAt LG p hcan.1 hE.nodeB)
    rw [heq, ← he, min_self] at lower
    exact le_antisymm upper lower

/-- **Along a coherent embedded chain** each pair is in one layer together with its couples. -/
theorem chain_coherent (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) → (h : TTree) → X.wf = true →
    ChainEmb LG.garden X ζ a h → CohOn LG (X.linksAt ζ a) → ChainPairLayers LG X ζ a
  | .nil, _, _, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, h, hwf, hC, hcoh => by
    simp only [RegChain.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨wr, wg⟩, wi⟩, ws⟩ := hwf
    obtain ⟨ER, EG, EI, ES⟩ := hC.parts
    have hab : layerAt LG a = layerAt LG (addrExt a ([m.c] ++ inner.lonePath)) :=
      hcoh _ List.mem_cons_self
    have hsub : ∀ l, (l ∈ (if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∨
        l ∈ (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∨
        l ∈ inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]) ∨
        l ∈ rest.linksAt (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) →
        layerAt LG l.1 = layerAt LG l.2 := by
      intro l hl
      apply hcoh l
      simp only [RegChain.linksAt, List.mem_cons, List.mem_append]
      tauto
    have pTop : ∀ i, (addrExt a [i]).2 ∈ (LG.garden.tree (addrExt a [i]).1).nodes →
        parAt LG p (addrExt a [i]) = layerAt LG a := fun i hi => parAt_child LG p i hi
    have pBot : ∀ k, (addrExt a ([m.c] ++ inner.lonePath ++ [k])).2 ∈
        (LG.garden.tree (addrExt a ([m.c] ++ inner.lonePath ++ [k])).1).nodes →
        parAt LG p (addrExt a ([m.c] ++ inner.lonePath ++ [k])) = layerAt LG a :=
      fun k hk => (parAt_bottom _ k hk).trans hab.symm
    refine ⟨hab.symm, ?_, ?_, chain_coherent hcan hplain inner _ _ _ wi EI
      (fun l hl => hsub l (Or.inr (Or.inr (Or.inl hl)))),
      chain_coherent hcan hplain rest _ _ _ ws ES (fun l hl => hsub l (Or.inr (Or.inr (Or.inr hl))))⟩
    · intro z hz
      have cR := fun l hl => hsub l (Or.inl hl)
      unfold orientedNodes at hz
      split_ifs at hz ER cR with hs
      · have := (cpl_coherent hcan hplain Qr _ _ wr ER cR).2
          ((pTop _ ER.nodeA).trans (pBot _ ER.nodeB).symm) z hz
        rw [this, pTop _ ER.nodeA]
      · have := (cpl_coherent hcan hplain Qr _ _ wr ER cR).2
          ((pBot _ ER.nodeA).trans (pTop _ ER.nodeB).symm) z hz
        rw [this, pBot _ ER.nodeA]
    · intro z hz
      have cG := fun l hl => hsub l (Or.inr (Or.inl hl))
      unfold orientedNodes at hz
      split_ifs at hz EG cG with hs
      · have := (cpl_coherent hcan hplain Qg _ _ wg EG cG).2
          ((pTop _ EG.nodeA).trans (pBot _ EG.nodeB).symm) z hz
        rw [this, pTop _ EG.nodeA]
      · have := (cpl_coherent hcan hplain Qg _ _ wg EG cG).2
          ((pBot _ EG.nodeA).trans (pTop _ EG.nodeB).symm) z hz
        rw [this, pBot _ EG.nodeA]

end

end WaveTurbulence.Links
