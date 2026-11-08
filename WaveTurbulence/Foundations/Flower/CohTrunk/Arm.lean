/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CohTrunk.Cross
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs

/-!
# COH-TRUNK: one arm, and the top weight as a single factor

* `NodeCr`: the crossing predicate on garden nodes (`topPsi`'s condition, with the root parent layers `qr`);
* `arm_cross`: for a layered chain placed at the root `(j, [])`, the crossing nodes are a single spine node,
  present iff `qr j = p` and the lone position lies below `p`;
* `rowTopWeightR_single`, `rowTopWeightR_one`: the top weight is `g j (k z₀)` at the unique crossing node, or `1`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

variable {w : ℕ} {LG : LayeredGarden w} {p : ℕ}

/-- `topPsi`'s condition at a node: layer `< p`, parent layer (root: `qr`) `= p`. -/
def NodeCr (LG : LayeredGarden w) (p : ℕ) (qr : Fin w → ℕ) (z : GNode LG.garden.tree) : Prop :=
  LG.layer z < p ∧ Stage1W.rowParentLayer LG qr z = p

theorem nodeCr_iff (qr : Fin w → ℕ) (z : GNode LG.garden.tree) :
    NodeCr LG p qr z ↔ Cr LG p (z.1.1, []) (qr z.1.1) z.1 := by
  unfold NodeCr Cr Stage1W.rowParentLayer
  rw [layerAt_node LG z]
  by_cases h : z.1.2 = []
  · have e : z.1 = (z.1.1, []) := Prod.ext rfl h
    rw [if_pos h, if_pos e]
  · have e : z.1 ≠ (z.1.1, []) := fun e => h (congrArg Prod.snd e)
    rw [if_neg h, if_neg e, parAt_of_mem LG p z.2]
    unfold LayeredGarden.parentLayer
    rw [if_neg h, if_neg h]

theorem arm_cross (hp : ∀ z : GNode LG.garden.tree, LG.layer z ≤ p) (X : RegChain) (ζ : ℤˣ) (j : Fin w)
    {h : TTree} (hC : ChainEmb LG.garden X ζ (j, []) h) (hPL : ChainPairLayers LG X ζ (j, []))
    (qr : Fin w → ℕ) (hu : layerAt LG (j, []) ≤ qr j) (hq : qr j ≤ p) :
    (∀ z : GNode LG.garden.tree, z.1 ∈ chainNodesSet X ζ (j, []) → NodeCr LG p qr z →
        z.1 ∈ spinePos X (j, [])) ∧
    (∀ z z' : GNode LG.garden.tree, z.1 ∈ spinePos X (j, []) → z'.1 ∈ spinePos X (j, []) →
        NodeCr LG p qr z → NodeCr LG p qr z' → z = z') ∧
    ((∃ z : GNode LG.garden.tree, z.1 ∈ spinePos X (j, []) ∧ NodeCr LG p qr z) ↔
        (qr j = p ∧ layerAt LG (addrExt (j, []) X.lonePath) < p)) := by
  obtain ⟨hA, hB, hC'⟩ := chain_cross hp X ζ (j, []) h hC hPL (qr j) hu hq
  have hj : ∀ z : GNode LG.garden.tree, Under (j, []) z.1 →
      (NodeCr LG p qr z ↔ Cr LG p (j, []) (qr j) z.1) := by
    intro z hz
    rw [nodeCr_iff]
    have e : z.1.1 = j := hz.1.symm
    rw [e]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hc
    exact hA z.1 hz ((hj z (chainNodes_region _ _ _ z.1 hz).1).1 hc)
  · intro z z' hz hz' hc hc'
    exact Subtype.ext (hB z.1 hz z'.1 hz' ((hj z (spinePos_under _ _ z.1 hz).1).1 hc)
      ((hj z' (spinePos_under _ _ z'.1 hz').1).1 hc'))
  · constructor
    · rintro ⟨z, hz, hc⟩
      exact hC'.1 ⟨z.1, hz, (hj z (spinePos_under _ _ z.1 hz).1).1 hc⟩
    · intro hh
      obtain ⟨y, hy, hcy⟩ := hC'.2 hh
      exact ⟨⟨y, spinePos_node hC hy⟩, hy, (hj ⟨y, spinePos_node hC hy⟩ (spinePos_under _ _ y hy).1).2 hcy⟩

theorem rowTopWeightR_single {d : ℕ} (g : Fin w → Mom d → ℂ) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) (z0 : GNode LG.garden.tree)
    (h : ∀ z, NodeCr LG p qr z ↔ z = z0) :
    Stage1W.rowTopWeightR p g LG qr k = g z0.1.1 (k z0) := by
  unfold Stage1W.rowTopWeightR
  rw [Finset.prod_eq_single z0]
  · unfold Stage1W.topPsi
    exact if_pos ((h z0).2 rfl)
  · intro z _ hz
    unfold Stage1W.topPsi
    exact if_neg (fun hc => hz ((h z).1 hc))
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem rowTopWeightR_one {d : ℕ} (g : Fin w → Mom d → ℂ) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) (h : ∀ z, ¬ NodeCr LG p qr z) :
    Stage1W.rowTopWeightR p g LG qr k = 1 := by
  unfold Stage1W.rowTopWeightR
  apply Finset.prod_eq_one
  intro z _
  unfold Stage1W.topPsi
  exact if_neg (h z)

theorem not_nodeCr_of_under (qr : Fin w → ℕ) {x : Fin w × Path} (z : GNode LG.garden.tree)
    (hx : x.2 ∈ (LG.garden.tree x.1).nodes) (hu : Under x z.1) (hne : z.1 ≠ x)
    (hl : layerAt LG z.1 = layerAt LG x) : ¬ NodeCr LG p qr z := by
  rw [nodeCr_iff]
  intro hc
  obtain ⟨h1, h2⟩ := hc
  have hza : z.1 ≠ (z.1.1, []) := by
    intro e
    have h2' : z.1.2 = [] := congrArg Prod.snd e
    apply hne
    have hx2 : x.2 = [] := List.prefix_nil.mp (h2' ▸ hu.2)
    exact Prod.ext hu.1.symm (by rw [h2', hx2])
  rw [if_neg hza] at h2
  have := parAt_le_layer_of_under (p := p) hx z.2 hu hne
  omega

end WaveTurbulence.Flower.CohTrunk
