/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.IncohInst.InputProductIdentity

/-! # Leaf-indexed profile families of a paired tree (RA1-LEAFWISE)

The leafwise analogue of `IncohInst.treeInputFunctions` and `IncohInst.tree_sourceLeafWeight_eq`: the profile at the
input leaf `ℓ` of the tree garden is `H ℓ.1` (the individually modified leaf inputs of TARGET L2065–2067). -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp IncohInst Links Incoh

/-- The complex input family of the paired tree garden: the profile `H` at the address of the `a`-th input leaf. -/
@[expose] def treeInputFam {d : ℕ} (G : Garden 1) (H : LGSpine.LeafProfiles 1 d) :
    Fin (Fintype.card (TPlus G)) → Mom d → ℂ :=
  fun a k => (H ((treeInputEquiv G).symm a).1.1 k : ℂ)

/-- Same for a layered garden. -/
@[expose, reducible] def treeInputFunctionsL {d : ℕ} (LG : LayeredGarden 1) (H : LGSpine.LeafProfiles 1 d) :
    Fin (Fintype.card (TPlus LG.garden)) → Mom d → ℂ := treeInputFam LG.garden H

/-- Exact input-product agreement for the paired tree with leafwise inputs; the lone leaf remains absent. -/
theorem tree_sourceLeafWeight_eqL {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    {d : ℕ} (H : LGSpine.LeafProfiles 1 d) (k : Mom d)
    (x : Fin (X.treeLinks (LG.garden.sig 0)).length → Fin 2 → Mom d) :
    (treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k x =
      ∏ ℓ ∈ inputLeaves LG.garden,
        (H ℓ.1 ((treeDecOfParams hX k (fun j => (x j 0, x j 1))).1 ℓ.toNode) : ℂ) := by
  let κ : GNode LG.garden.tree → Mom d := (treeDecOfParams hX k (fun j => (x j 0, x j 1))).1
  let h : GLeaf LG.garden.tree → ℂ := fun ℓ => (H ℓ.1 (κ ℓ.toNode) : ℂ)
  unfold MomentumTreeData.sourceLeafWeight
  simp_rw [tree_inputMomentum_eq]
  change (∏ a, h ((treeInputEquiv LG.garden).symm a).1) = ∏ ℓ ∈ inputLeaves LG.garden, h ℓ
  calc
    _ = ∏ ℓ : TPlus LG.garden, h ℓ.1 := Equiv.prod_comp (treeInputEquiv LG.garden).symm _
    _ = _ := by
      rw [tree_inputLeaves hX]
      exact (Finset.prod_subtype (plusPaired LG.garden) (fun ℓ => by simp [plusPaired]) h).symm

end WaveTurbulence.RA1Leafwise
