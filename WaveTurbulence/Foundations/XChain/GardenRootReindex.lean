/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RootReindex
/-! Exact relabelling of garden roots, pairings, marks and layers. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def reindexGarden {v w : ℕ} (G : Garden w) (e : Fin v ≃ Fin w) : Garden v where
  sig := fun j => G.sig (e j)
  tree := fun j => G.tree (e j)
  pair := fun ℓ => (reindexLeafEquiv G.tree e).symm (G.pair (reindexLeafEquiv G.tree e ℓ))
  mark := fun ℓ => G.mark (reindexLeafEquiv G.tree e ℓ)
  pair_pair ℓ := by
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (reindexLeafEquiv G.tree e).symm (G.pair_pair _)).trans
      ((reindexLeafEquiv G.tree e).symm_apply_apply ℓ)
  pair_eq_iff ℓ := by
    constructor
    · intro he
      have hp := congrArg (reindexLeafEquiv G.tree e) he
      have hpair : G.pair (reindexLeafEquiv G.tree e ℓ) = reindexLeafEquiv G.tree e ℓ :=
        ((reindexLeafEquiv G.tree e).apply_symm_apply _).symm.trans hp
      exact (G.pair_eq_iff _).mp hpair
    · intro hm
      have hp := (G.pair_eq_iff _).mpr hm
      exact (congrArg (reindexLeafEquiv G.tree e).symm hp).trans
        ((reindexLeafEquiv G.tree e).symm_apply_apply ℓ)
  pair_sign ℓ hne := by
    have hp : G.pair (reindexLeafEquiv G.tree e ℓ) ≠ reindexLeafEquiv G.tree e ℓ := by
      intro he
      exact hne ((congrArg (reindexLeafEquiv G.tree e).symm he).trans
        ((reindexLeafEquiv G.tree e).symm_apply_apply ℓ))
    have hs := G.pair_sign _ hp
    have he := congrArg (fun l : GLeaf G.tree => nodeSign G.sig l.1)
      ((reindexLeafEquiv G.tree e).apply_symm_apply (G.pair (reindexLeafEquiv G.tree e ℓ)))
    exact he.trans hs

theorem reindexGarden_pair_image {v w : ℕ} (G : Garden w) (e : Fin v ≃ Fin w)
    (ℓ : GLeaf (fun j => G.tree (e j))) :
    reindexLeafEquiv G.tree e ((reindexGarden G e).pair ℓ) = G.pair (reindexLeafEquiv G.tree e ℓ) :=
  (reindexLeafEquiv G.tree e).apply_symm_apply _

noncomputable def reindexLayeredGarden {v w : ℕ} (LG : LayeredGarden w) (e : Fin v ≃ Fin w) :
    LayeredGarden v where
  garden := reindexGarden LG.garden e
  layer := fun a => LG.layer (reindexNodeEquiv LG.garden.tree e a)
  isLayering := by
    constructor
    · intro b i
      exact LG.isLayering.1 (reindexBranchEquiv LG.garden.tree e b) i
    · intro ℓ
      have he := congrArg (fun l : GLeaf LG.garden.tree => LG.layer l.toNode)
        (reindexGarden_pair_image LG.garden e ℓ)
      exact (LG.isLayering.2 (reindexLeafEquiv LG.garden.tree e ℓ)).trans he.symm

theorem reindexLayeredGarden_parentLayer {v w : ℕ} (LG : LayeredGarden w) (e : Fin v ≃ Fin w)
    (q : ℕ) (a : GNode (fun j => LG.garden.tree (e j))) :
    (reindexLayeredGarden LG e).parentLayer q a =
      LG.parentLayer q (reindexNodeEquiv LG.garden.tree e a) := by
  by_cases ha : a.1.2 = []
  · have hb : (reindexNodeEquiv LG.garden.tree e a).1.2 = [] := ha
    simp only [LayeredGarden.parentLayer, ha, hb, ite_true]
  · have hb : (reindexNodeEquiv LG.garden.tree e a).1.2 ≠ [] := ha
    simp only [LayeredGarden.parentLayer, ha, hb, ite_false]
    rfl

end WaveTurbulence.Induct
