/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CohTrunk.Couple
public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeCoh
public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayer

/-!
# COH-TRUNK: Lemma 5.1 for coherent regular trees

The crossing node of a coherent regular tree is a spine node, present iff `q = p` and the lone leaf (layer `q'`)
lies below `p`; the momentum there is `k`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

/-- The conclusion of Lemma 5.1 for a tree. -/
def TreeCrossConcl {d : ℕ} (LG : LayeredGarden 1) (p q q' : ℕ) (k : Mom d)
    (K : GNode LG.garden.tree → Mom d) : Prop :=
  ((q' < p ∧ q = p) → ∃ z0 : GNode LG.garden.tree, K z0 = k ∧ ∀ z, NodeCr LG p ![q] z ↔ z = z0) ∧
  (¬ (q' < p ∧ q = p) → ∀ z, ¬ NodeCr LG p ![q] z)

theorem treeCross {d p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} {k : Mom d}
    (hcoh : IsCoherentTreeAt p q q' X LG) (hq'q : q' ≤ q) (hqp : q ≤ p)
    (K : GNode LG.garden.tree → Mom d) (hK : IsDecoration LG.garden K)
    (hKr : ∀ j, K (GNode.root LG.garden.tree j) = k) : TreeCrossConcl LG p q q' k K := by
  have tf := treeCohFacts_of_coherent hcoh
  obtain ⟨hwf, hX, w, H, a, hh, hcan, hC, -, hcoh', hpa, hlone, hlay⟩ := hcoh
  have hp : ∀ z : GNode LG.garden.tree, LG.layer z ≤ p := fun z => by
    rw [hlay z]
    exact hpH_of_canon hcan _
  have hu : layerAt LG ((0 : Fin 1), []) ≤ q := by
    have h1 := hlay (GNode.root LG.garden.tree 0)
    have h2 := layerAt_node LG (GNode.root LG.garden.tree 0)
    have h3 : layerAt LG ((0 : Fin 1), []) = layerAt H a := by
      refine h2.trans (h1.trans ?_)
      show layerAt H (addrExt a []) = layerAt H a
      rw [addrExt_nil]
    rw [h3, ← hpa]
    exact layerAt_le_parAt H p hcan.2.2.1 hC.node
  have Cd := ChainEmb.of_decodesTree hX
  have hq := arm_cross hp X (LG.garden.sig 0) (0 : Fin 1) Cd tf.pl ![q] (by simpa using hu)
    (by simpa using hqp)
  have ea : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = ((0 : Fin 1), X.lonePath) := by
    simp [addrExt]
  have hD : ∀ z : GNode LG.garden.tree, NodeCr LG p ![q] z → z.1 ∈ spinePos X ((0 : Fin 1), []) := by
    intro z hc
    have ez : addrExt ((0 : Fin 1), ([] : Path)) z.1.2 = z.1 :=
      Prod.ext (Subsingleton.elim _ _) (by simp [addrExt])
    rcases addrExt_mem_chainNodes hX ((0 : Fin 1), ([] : Path)) z with h1 | h1
    · rw [ez] at h1
      exact hq.1 z h1 hc
    · have : z.1 = addrExt ((0 : Fin 1), ([] : Path)) X.lonePath := by
        rw [ea, ← h1]
        exact Prod.ext (Subsingleton.elim _ _) rfl
      rw [this]
      exact lone_mem_spinePos X _
  have hdec := chainDec_of_decoration hX hK
  have hf0 : extend K ((0 : Fin 1), ([] : Path)) = k :=
    (extend_node K (GNode.root LG.garden.tree 0)).trans (hKr 0)
  have mom : ∀ z : GNode LG.garden.tree, z.1 ∈ spinePos X ((0 : Fin 1), []) → K z = k := by
    intro z hz
    rw [← extend_node K z, spine_dec (extend K) X _ _ hdec z.1 hz, hf0]
  have c0 := hq.2.2
  rw [ea, tf.lone] at c0
  simp only [Matrix.cons_val_zero] at c0
  refine ⟨fun h1 => ?_, fun h1 z hc => ?_⟩
  · obtain ⟨z0, hz0, hc0⟩ := c0.2 ⟨h1.2, h1.1⟩
    refine ⟨z0, mom z0 hz0, fun z => ⟨fun hc => ?_, ?_⟩⟩
    · exact hq.2.1 z z0 (hD z hc) hz0 hc hc0
    · rintro rfl
      exact hc0
  · have := c0.1 ⟨z, hD z hc, hc⟩
    exact h1 ⟨this.2, this.1⟩

end WaveTurbulence.Flower.CohTrunk
