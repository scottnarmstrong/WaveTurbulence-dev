/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeCoverage
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DecodedCoreEmbedding
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2Tree
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2
public import WaveTurbulence.Foundations.IncohInst.Links.Partition
public import WaveTurbulence.Foundations.Spine.InducedLayeringFinite
import Mathlib.Tactic

/-!
# CLASSCOUNT: layered gardens over a fixed skeleton and replacement datum (injection into slot traces)

For `LG` decoded by `D` over the skeleton `S`, the layering of `LG` is determined by the core layer
`coreLayer` (a function of the skeleton branches) and the *slot traces*: the restriction to the nodes of each
regular couple/tree replacement (`ReplacementSlot S`), extended by `0`.  Each trace lies in the carrier of
`Links.layerreg2` / `layerreg2_tree`, so the number of `LG` with given core layer and slot incoherencies is bounded
by the product of the `layerreg2` bounds (TARGET L2248-L2252).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LFTwist RegRed

variable {w : ℕ} {S : Garden w}

/-- The parent value of a node of the skeleton read from a core layering `f` (`p` at a root). -/
noncomputable def pv (p : ℕ) (f : GBranch S.tree → ℕ) (n : GNode S.tree) : ℕ :=
  if h : n.1.2 = [] then p else f (n.parent h)

/-- The parent layer at the inflated position of a node is the parent value of the core layering. -/
theorem parAt_inflated (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden w)
    (hd : D.Decodes hS LG.garden) (p : ℕ) (n : GNode S.tree) :
    parAt LG p (inflatedPosition S D.tree n) = pv p (coreLayer LG D hS hd) n := by
  by_cases h : n.1.2 = []
  · have e : inflatedPosition S D.tree n = (n.1.1, []) := by
      rw [inflatedPosition, dif_pos h]; exact Prod.ext rfl h
    rw [e, parAt_root, pv, dif_pos h]
  · have hz := (D.decodedNode hS hd n).2
    have e : inflatedPosition S D.tree n =
        addrExt (D.corePosition (n.parent h)) [n.1.2.getLast h] := by
      rw [inflatedPosition, dif_neg h, ReconstructionData.corePosition, addrExt_append]
    rw [pv, dif_neg h]
    have hz' : (inflatedPosition S D.tree n).2 ∈ (LG.garden.tree (inflatedPosition S D.tree n).1).nodes := hz
    rw [parAt_of_mem LG p hz']
    unfold LayeredGarden.parentLayer coreLayer
    have hne : ¬ (⟨inflatedPosition S D.tree n, hz'⟩ : GNode LG.garden.tree).1.2 = [] := by
      change ¬ (inflatedPosition S D.tree n).2 = []
      rw [e]; simp [addrExt]
    rw [if_neg hne]
    congr 1
    apply Subtype.ext
    change ((inflatedPosition S D.tree n).1, (inflatedPosition S D.tree n).2.dropLast) = D.corePosition (n.parent h)
    rw [e]
    simp [addrExt]

variable (D : ReconstructionData S) (hS : S.IsPlain)

/-- The `+` root of the couple slot `p`. -/
noncomputable def cplA (p : SourcePair S) : Address w := inflatedPosition S D.tree (p.firstLeaf hS).toNode
/-- The `-` root of the couple slot `p`. -/
noncomputable def cplB (p : SourcePair S) : Address w := inflatedPosition S D.tree (p.secondLeaf hS).toNode
/-- The root of the tree slot `b`. -/
noncomputable def treeA (b : GBranch S.tree) : Address w := inflatedPosition S D.tree b.toNode

/-- The trace of `LG` on a slot: the layers on the nodes of the replacement, `0` elsewhere. -/
noncomputable def slotTrace (LG : LayeredGarden w) : ReplacementSlot S → (Fin w × Path → ℕ)
  | .inl p => fun z => if z ∈ cplNodes (D.couple p) (cplA D hS p) (cplB D hS p) then layerAt LG z else 0
  | .inr b => fun z => if z ∈ chainNodesSet (D.tree b) (nodeSign S.sig b.1) (treeA D b) then layerAt LG z else 0

/-- The incoherency index of the slot (the summands of `gregOf`, counted as a link list). -/
noncomputable def slotInc (LG : LayeredGarden w) : ReplacementSlot S → ℕ
  | .inl p => incohCount LG ((D.couple p).linksAt (cplA D hS p) (cplB D hS p))
  | .inr b => incohCount LG ((D.tree b).linksAt (nodeSign S.sig b.1) (treeA D b))

/-- The carrier of `layerreg2` / `layerreg2_tree` for a slot, with parent layers read from the core layering `f`. -/
def slotCarrier (p : ℕ) (f : GBranch S.tree → ℕ) (g : ℕ) : ReplacementSlot S → Set (Fin w × Path → ℕ)
  | .inl pr => inducedLayerings p (D.couple pr) (cplA D hS pr) (cplB D hS pr)
      (pv p f (pr.firstLeaf hS).toNode) (pv p f (pr.secondLeaf hS).toNode) g
  | .inr b => inducedTreeLayerings p (D.tree b) (nodeSign S.sig b.1) (treeA D b) (pv p f b.toNode) (f b) g

/-- The exponent of the `2^{|q-q'|}` factor of the slot. -/
noncomputable def slotDist (p : ℕ) (f : GBranch S.tree → ℕ) : ReplacementSlot S → ℕ
  | .inl pr => ldist (pv p f (pr.firstLeaf hS).toNode) (pv p f (pr.secondLeaf hS).toNode)
  | .inr b => pv p f b.toNode - f b

/-- The `layerreg2` bound of a slot. -/
noncomputable def slotBound (p : ℕ) (f : GBranch S.tree → ℕ) (g : ℕ) : ReplacementSlot S → ℕ
  | .inl pr => (2 ^ (9 * p)) ^ g * 2 ^ (D.couple pr).size * 2 ^ slotDist hS p f (.inl pr)
  | .inr b => (2 ^ (9 * p)) ^ g * 2 ^ (D.tree b).size * 2 ^ slotDist hS p f (.inr b)

theorem layerAt_core (LG : LayeredGarden w) (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) :
    layerAt LG (D.corePosition b) = coreLayer LG D hS hd b := by
  have := layerAt_node LG (D.decodedCoreBranch hS hd b).toNode
  exact this

/-- **The trace of a canonical layered garden on a slot lies in the `layerreg2` carrier.** -/
theorem slotTrace_mem {p : ℕ} {LG : LayeredGarden w} (hcan : LG.CanonCriterion p) (hpl : LG.garden.IsPlain)
    (hd : D.Decodes hS LG.garden) (s : ReplacementSlot S) :
    slotTrace D hS LG s ∈ slotCarrier D hS p (coreLayer LG D hS hd) (slotInc D hS LG s) s := by
  cases s with
  | inl pr =>
    refine ⟨LG, hcan, hpl, reconstruction_coupleEmb D hS hd pr, ?_, ?_, rfl, fun z => rfl⟩
    · exact parAt_inflated D hS LG hd p _
    · exact parAt_inflated D hS LG hd p _
  | inr b =>
    refine ⟨LG, node3 (fun i => D.inflateNode hS (b.child i)), hcan, hpl, reconstruction_chainEmb D hS hd b,
      parAt_inflated D hS LG hd p _, ?_, rfl, fun z => rfl⟩
    exact layerAt_core D hS LG hd b

theorem nodeAddresses_sub {w : ℕ} (t : TTree) (a : Fin w × Path) :
    nodeAddresses t a ⊆ branchAddresses t a ∪ leafAddresses t a := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
  rcases (Comb.TreePath.mem_nodes_iff t q).1 hq with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)

theorem coupleNodes_sub_cplNodes {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    coupleNodes Q a b ⊆ cplNodes Q a b := by
  intro z hz
  rw [← couple_nodeAddresses] at hz
  unfold cplNodes
  rw [← couple_branchAddresses Q a b, ← couple_leafAddresses Q a b]
  rcases Finset.mem_union.1 hz with h | h
  · rcases Finset.mem_union.1 (nodeAddresses_sub _ _ h) with h' | h'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
  · rcases Finset.mem_union.1 (nodeAddresses_sub _ _ h) with h' | h'
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')

theorem chainNodes_sub {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    chainNodes X ζ a ⊆ insert (addrExt a X.lonePath) (chainNodesSet X ζ a) := by
  intro z hz
  have h1 : z ∈ nodeAddresses (X.plug ζ .leaf) a := by
    rw [chain_nodeAddresses]; exact Finset.mem_union_left _ hz
  rcases Finset.mem_union.1 (nodeAddresses_sub _ _ h1) with h | h
  · rw [chain_branchAddresses] at h
    rcases Finset.mem_union.1 h with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
    · simp at h
  · rw [chain_leafAddresses] at h
    rcases Finset.mem_union.1 h with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
    · simp at h; exact Finset.mem_insert.2 (Or.inl h)

/-- Every node of a decoded garden is a node of a slot or the core position of a branch. -/
theorem node_slot_cover {G : Garden w} (hd : D.Decodes hS G) (z : GNode G.tree) :
    (∃ pr : SourcePair S, z.1 ∈ cplNodes (D.couple pr) (cplA D hS pr) (cplB D hS pr)) ∨
    (∃ b : GBranch S.tree, z.1 ∈ chainNodesSet (D.tree b) (nodeSign S.sig b.1) (treeA D b)) ∨
    (∃ b : GBranch S.tree, z.1 = D.corePosition b) := by
  have ht : D.forest hS = G.tree := congrArg Raw.tree hd.2
  have hz : z.1.2 ∈ (D.forest hS z.1.1).nodes := by rw [ht]; exact z.2
  obtain ⟨slot, hslot⟩ := D.node_covered hS ⟨z.1, hz⟩
  cases slot with
  | inl pr => exact Or.inl ⟨pr, coupleNodes_sub_cplNodes _ _ _ hslot⟩
  | inr b =>
    have h : z.1 ∈ chainNodes (D.tree b) (nodeSign S.sig b.1) (treeA D b) ∪ {D.corePosition b} := hslot
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_insert.1 (chainNodes_sub _ _ _ h) with h | h
      · exact Or.inr (Or.inr ⟨b, h⟩)
      · exact Or.inr (Or.inl ⟨b, h⟩)
    · exact Or.inr (Or.inr ⟨b, Finset.mem_singleton.1 h⟩)

/-- **A layered garden decoded by `D` is determined by its core layering and its slot traces.** -/
theorem layered_eq_of_traces {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : D.Decodes hS LG'.garden) (hcore : coreLayer LG D hS hd = coreLayer LG' D hS hd')
    (htr : ∀ s, slotTrace D hS LG s = slotTrace D hS LG' s) : LG = LG' := by
  have hG : LG.garden = LG'.garden := (D.existsUnique_decodes hS).unique hd hd'
  rcases LG with ⟨G, l, hl⟩
  rcases LG' with ⟨G', l', hl'⟩
  dsimp only at hG hd hd' hcore htr
  subst G'
  have hlayers : l = l' := by
    funext z
    have key : layerAt ⟨G, l, hl⟩ z.1 = layerAt ⟨G, l', hl'⟩ z.1 := by
      rcases node_slot_cover D hS hd z with ⟨pr, h⟩ | ⟨b, h⟩ | ⟨b, h⟩
      · have := congrFun (htr (.inl pr)) z.1
        simpa only [slotTrace, if_pos h] using this
      · have := congrFun (htr (.inr b)) z.1
        simpa only [slotTrace, if_pos h] using this
      · rw [h, layerAt_core D hS _ hd, layerAt_core D hS _ hd', hcore]
    simpa only [layerAt_node] using key
  subst l'
  rfl

theorem finite_inducedTreeLayerings (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) (a : Fin w × Path)
    (p q q' g : ℕ) : (inducedTreeLayerings p X ζ a q q' g).Finite := by
  set B := pairEndpoints (X.linksAt ζ a)
  set T := (q - q') + 9 * p * g
  have hmap : ∀ f ∈ inducedTreeLayerings p X ζ a q q' g, dropT B a q f ∈ boundedVecs B T := by
    rintro f ⟨LG, h, hcan, hplain, hC, ha, hl, hg, hfz⟩
    obtain ⟨W1, W2⟩ := tree_witness_facts hC ha hfz
    refine ⟨fun z hz => by unfold dropT; rw [ite_neg_of hz], ?_⟩
    have hbud : budget LG p B ≤ _ := chain_budget hcan hplain X ζ a h hwf hC
    have hlone : q' ≤ parAt LG p (addrExt a X.lonePath) := by
      rw [← hl]; exact layerAt_le_parAt LG p hcan.1 (nodeOfChainEmb hC)
    have hinc := incohCount_chain (LG := LG) X ζ a
    rw [ha] at hbud
    have hT : budget LG p B ≤ (q - q') + 9 * p * g := by
      rw [← hg, hinc]
      simp only [Nat.mul_assoc, Nat.mul_add] at hbud ⊢
      omega
    calc ∑ z ∈ B, dropT B a q f z = budget LG p B :=
          Finset.sum_congr rfl fun z hz => by
            unfold dropT dropAt
            rw [ite_pos_of hz, W2 z (chain_links_sub_nodes hz), W1 z (chain_links_sub_nodes hz)]
      _ ≤ T := hT
  have hinj : Set.InjOn (dropT B a q ·) (inducedTreeLayerings p X ζ a q q' g) :=
    fun f hf f' hf' hd => tree_layering_determined hf hf' hd
  exact Set.Finite.of_injOn hmap hinj (boundedVecs_spec B T).1

theorem slotCarrier_finite (p : ℕ) (f : GBranch S.tree → ℕ) (g : ℕ) (s : ReplacementSlot S) :
    (slotCarrier D hS p f g s).Finite := by
  cases s with
  | inl pr => exact LGSpine.finite_inducedLayerings _ (D.couple_wf pr) _ _ _ _ _ _
  | inr b => exact finite_inducedTreeLayerings _ (D.tree_wf b) _ _ _ _ _ _

theorem slotCarrier_ncard_le (p : ℕ) (f : GBranch S.tree → ℕ) (g : ℕ) (s : ReplacementSlot S) :
    (slotCarrier D hS p f g s).ncard ≤ slotBound D hS p f g s := by
  cases s with
  | inl pr => exact layerreg2 _ (D.couple_wf pr) _ _ _ _ _ _
  | inr b => exact layerreg2_tree _ (D.tree_wf b) _ _ _ _ _ _

/-- **The number of layered gardens with a given core layering and slot incoherencies** is at most the product of
the `layerreg2` bounds (TARGET L2248-L2252). -/
theorem card_slot_bound (p : ℕ) (f : GBranch S.tree → ℕ) (gs : ReplacementSlot S → ℕ)
    (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ ∃ hd : D.Decodes hS LG.garden,
      coreLayer LG D hS hd = f ∧ ∀ s, slotInc D hS LG s = gs s) :
    A.card ≤ ∏ s, slotBound D hS p f (gs s) s := by
  classical
  let F : ∀ s : ReplacementSlot S, Finset (Fin w × Path → ℕ) := fun s =>
    (slotCarrier_finite D hS p f (gs s) s).toFinset
  have hmem : ∀ LG ∈ A, (fun s => slotTrace D hS LG s) ∈ Fintype.piFinset F := by
    intro LG hLG
    obtain ⟨hc, hp, hd, hcore, hinc⟩ := hA LG hLG
    rw [Fintype.mem_piFinset]
    intro s
    rw [Set.Finite.mem_toFinset]
    have := slotTrace_mem D hS hc hp hd s
    rw [hcore, hinc s] at this
    exact this
  have hinj : Set.InjOn (fun LG => fun s => slotTrace D hS LG s) (A : Set (LayeredGarden w)) := by
    intro LG hLG LG' hLG' he
    obtain ⟨-, -, hd, hcore, -⟩ := hA LG hLG
    obtain ⟨-, -, hd', hcore', -⟩ := hA LG' hLG'
    exact layered_eq_of_traces D hS hd hd' (hcore.trans hcore'.symm) (fun s => congrFun he s)
  calc A.card ≤ (Fintype.piFinset F).card := Finset.card_le_card_of_injOn _ hmem hinj
    _ = ∏ s, (F s).card := Fintype.card_piFinset F
    _ ≤ ∏ s, slotBound D hS p f (gs s) s := by
        refine Finset.prod_le_prod' fun s _ => ?_
        simp only [F]
        rw [← Set.ncard_eq_toFinset_card _ (slotCarrier_finite D hS p f (gs s) s)]
        exact slotCarrier_ncard_le D hS p f (gs s) s

end WaveTurbulence.ClassCount
