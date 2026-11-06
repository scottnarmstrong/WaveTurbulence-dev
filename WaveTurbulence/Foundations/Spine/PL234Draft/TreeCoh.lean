/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.ChainFactsOn

/-!
# Prop 6.1, `q > q'`, trees: the coherence facts on the decoded carrier

* `TreeCohFacts`: the coherence facts of a coherent tree code whose lone leaf lies in layer `q'` and whose chain
  lies in layers `≤ q`;
* `treeCohFacts_of_coherent`: from `IsCoherentTreeAt` (TARGET L901), by LAYERREG's `layerreg1_tree` in the ambient
  canonical garden, transported along `z ↦ a · z.2`. The decoded carrier has a leaf at the lone position where the
  ambient garden carries the inserted subtree, so the layers agree on the chain region only (`ChainFactsOn`);
* the suffix lemmas, and the address and slice algebra of the tree blocks: `chainSlice_of_topNe`,
  `botAddr_comp_tree`, `layerAt_botLayered_tree`, `TopAll.of_chainNodes`.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The embedding of a decoded tree carrier into the ambient garden at `a`. -/
def treeEmb {w : ℕ} (a : Fin w × Path) (z : Fin 1 × Path) : Fin w × Path := addrExt a z.2

theorem treeEmb_hom {w : ℕ} (a : Fin w × Path) (z : Fin 1 × Path) (p : Path) :
    treeEmb a (addrExt z p) = addrExt (treeEmb a z) p := by
  simp [treeEmb, addrExt, List.append_assoc]

theorem treeEmb_zero {w : ℕ} (a : Fin w × Path) : treeEmb a ((0 : Fin 1), []) = a := by
  simp [treeEmb, addrExt]

/-- **Coherence facts** of a coherent tree code with lone leaf in layer `q'` and chain in layers `≤ q`. -/
structure TreeCohFacts (LG : LayeredGarden 1) (X : RegChain) (q' q : ℕ) : Prop where
  wf : X.wf = true
  dec : X.DecodesTree LG.garden
  pl : ChainPairLayers LG X (LG.garden.sig 0) ((0 : Fin 1), [])
  sm : SpineMono LG ((0 : Fin 1), []) X
  low : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []), q' ≤ layerAt LG z
  high : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []), layerAt LG z ≤ q
  lone : layerAt LG ((0 : Fin 1), X.lonePath) = q'

/-- **The coherence facts** of a coherent embedded tree with parent layer `q` and lone layer `q'`. -/
theorem treeCohFacts_of_coherent {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q' X LG) : TreeCohFacts LG X q' q := by
  obtain ⟨hwf, hX, w, HH, a, hh, hcan, hC, -, hcoh, hpa, hlone, hlay⟩ := h
  obtain ⟨hPL, hlh, -⟩ := layerreg1_tree hcan.2.2 hcan.1 hwf hC hcoh
  rw [hlone, hpa] at hlh
  have hCd := ChainEmb.of_decodesTree hX
  have hagree : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []),
      layerAt LG z = layerAt HH (treeEmb a z) := fun z hz =>
    (layerAt_node LG ⟨z, hCd.mem_nodes hz⟩).trans (hlay ⟨z, hCd.mem_nodes hz⟩)
  have hmapX : chainNodesSet X (LG.garden.sig 0) a =
      (chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), [])).image (treeEmb a) := by
    have := chainNodesSet_map X (treeEmb a) (treeEmb_hom a) (LG.garden.sig 0) ((0 : Fin 1), [])
    rwa [treeEmb_zero] at this
  have hmem : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []),
      treeEmb a z ∈ chainNodesSet X (LG.garden.sig 0) a := fun z hz => by
    rw [hmapX]
    exact Finset.mem_image_of_mem _ hz
  refine ⟨hwf, hX, ?_, ?_, ?_, ?_, ?_⟩
  · refine chainPairLayers_map_on HH LG (treeEmb a) (treeEmb_hom a) X _ _ hagree ?_
    rw [treeEmb_zero]
    exact hPL
  · refine spineMono_map_on HH LG (treeEmb a) (treeEmb_hom a) X (LG.garden.sig 0) _ hagree ?_
    rw [treeEmb_zero]
    exact spineMono_of_chainEmb hC
  · intro z hz
    rw [hagree z hz]
    exact (hlh _ (hmem z hz)).1
  · intro z hz
    rw [hagree z hz]
    exact (hlh _ (hmem z hz)).2
  · have hn : X.lonePath ∈ (LG.garden.tree 0).nodes := by
      rw [hX.1]
      exact lonePath_mem_plug X _ _
    exact (layerAt_node LG ⟨((0 : Fin 1), X.lonePath), hn⟩).trans ((hlay _).trans hlone)

section Suffix

variable {LG : LayeredGarden 1} {X : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X q' q) {R Y : RegChain}
  (hXp : X = appendChain R Y)
include F hXp

theorem TreeCohFacts.emb_suffix : ChainEmb LG.garden Y (LG.garden.sig 0) ((0 : Fin 1), R.lonePath) .leaf := by
  have h := ChainEmb.of_decodesTree F.dec
  rw [hXp] at h
  exact chainEmb_append_right h

theorem TreeCohFacts.pl_suffix : ChainPairLayers LG Y (LG.garden.sig 0) ((0 : Fin 1), R.lonePath) := by
  have h := F.pl
  rw [hXp] at h
  exact chainPairLayers_append_right LG R Y _ _ h

theorem TreeCohFacts.sm_suffix : SpineMono LG ((0 : Fin 1), R.lonePath) Y := by
  have h := F.sm
  rw [hXp] at h
  exact spineMono_append_right LG R Y _ h

omit F in
theorem TreeCohFacts.sub_suffix {z : Fin 1 × Path}
    (hz : z ∈ chainNodesSet Y (LG.garden.sig 0) ((0 : Fin 1), R.lonePath)) :
    z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []) := by
  rw [hXp]
  exact chainNodesSet_append_right R Y _ _ hz

theorem TreeCohFacts.lone_suffix : layerAt LG (addrExt ((0 : Fin 1), R.lonePath) Y.lonePath) = q' := by
  have he : addrExt ((0 : Fin 1), R.lonePath) Y.lonePath = ((0 : Fin 1), X.lonePath) := by
    rw [hXp, appendChain_lonePath]
    rfl
  rw [he]
  exact F.lone

theorem TreeCohFacts.wf_suffix : Y.wf = true := by
  have h := F.wf
  rw [hXp, appendChain_wf, Bool.and_eq_true] at h
  exact h.2

end Suffix

/-! ### The slice and address algebra of tree blocks -/

theorem chainSlice_of_topNe {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (a : Fin w × Path), TopNe LG r a X → SourceApp.chainSlice LG a r X = .nil
  | .nil, _, _ => rfl
  | .pair m Qr Qg inner rest, a, ⟨hne, hT⟩ => by
    rw [chainSlice_pair, ite_eq_right hne]
    exact chainSlice_of_topNe LG r rest _ hT

theorem TopAll.of_chainNodes {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path), (∀ z ∈ chainNodesSet X ζ a, layerAt LG z = r) →
      TopAll LG r a X
  | .nil, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, h => by
    refine ⟨h a (root_mem_chainNodesSet _ _ _ _ _ _ _), TopAll.of_chainNodes LG r rest _ _
      fun z hz => h z (mem_chainNodesSet_rest hz)⟩

theorem botAddr_comp_tree (π π' : Path) (z : Fin 1 × Path) :
    botAddr π (botAddr π' z) = botAddr (π ++ π') z := by
  obtain ⟨j, p⟩ := z
  fin_cases j
  simp [botAddr, List.append_assoc]

theorem botAddr_nil_tree (z : Fin 1 × Path) : botAddr [] z = z := by
  obtain ⟨j, p⟩ := z
  fin_cases j
  simp [botAddr]

/-- **The layers of the bottom tree** are those of the glued tree, at every address. -/
theorem layerAt_botLayered_tree {LG : LayeredGarden 1} {B D : RegChain} {G₁ G₂ : Garden 1}
    (hG : (appendChain B D).DecodesTree LG.garden) (h₁ : B.DecodesTree G₁) (hs₁ : G₁.sig 0 = LG.garden.sig 0)
    (h₂ : D.DecodesTree G₂) (hs₂ : G₂.sig 0 = LG.garden.sig 0) (z : Fin 1 × Path) :
    layerAt (botLayered_tree hG h₁ hs₁ h₂ hs₂) z = layerAt LG (botAddr B.lonePath z) := by
  set h := glueData_tree hG h₁ hs₁ h₂ hs₂
  unfold layerAt
  by_cases hz : z.2 ∈ (G₂.tree z.1).nodes
  · have hz' := (h.bot_iff z).1.mpr hz
    have hz0 : z.2 ∈ ((botLayered_tree hG h₁ hs₁ h₂ hs₂).garden.tree z.1).nodes := hz
    simp only [hz0, hz', ↓reduceDIte]
    rfl
  · have hz' : ¬ (botAddr B.lonePath z).2 ∈ (LG.garden.tree (botAddr B.lonePath z).1).nodes :=
      fun hh => hz ((h.bot_iff z).1.mp hh)
    have hz0 : ¬ z.2 ∈ ((botLayered_tree hG h₁ hs₁ h₂ hs₂).garden.tree z.1).nodes := hz
    simp only [hz0, hz', ↓reduceDIte]

end WaveTurbulence.PL234
