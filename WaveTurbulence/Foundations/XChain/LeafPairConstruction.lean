/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerKernelSum
public import WaveTurbulence.Foundations.XChain.LeafPairKernel
/-! The actual zero-order pair component for either balanced root-sign orientation. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def leafPairGarden (sig : Fin 2 → ℤˣ) (hs : sig 1 = -sig 0) : Garden 2 := by
  have hn : ∀ j : Fin 2, Fin.rev j ≠ j := by intro j; fin_cases j <;> decide
  have hsign : ∀ j : Fin 2, sig (Fin.rev j) = -sig j := by
    intro j
    fin_cases j
    · exact hs
    · change sig 0 = -sig 1
      rw [hs, neg_neg]
  refine {
    sig := sig
    tree := fun _ => TTree.leaf
    pair := fun l => ⟨(Fin.rev l.1.1, []), mem_singleton_self []⟩
    mark := fun _ => none
    pair_pair := ?_
    pair_eq_iff := ?_
    pair_sign := ?_ }
  · intro l
    apply Subtype.ext
    exact Prod.ext (Fin.rev_rev l.1.1) (mem_singleton.mp l.2).symm
  · intro l
    constructor
    · intro he
      have hr := congrArg (fun a : GLeaf (fun _ : Fin 2 => TTree.leaf) => a.1.1) he
      exact False.elim (hn l.1.1 hr)
    · intro he
      exact False.elim (he rfl)
  · intro l _
    have hp : l.1.2 = [] := mem_singleton.mp l.2
    change nodeSign sig (Fin.rev l.1.1, []) = -nodeSign sig l.1
    have he : l.1 = (l.1.1, []) := Prod.ext rfl hp
    rw [he]
    simpa only [nodeSign, TTree.pathSign, List.count_nil, pow_zero, mul_one] using hsign l.1.1

noncomputable def leafPairLayeredGarden (sig : Fin 2 → ℤˣ) (hs : sig 1 = -sig 0) (p : ℕ) :
    LayeredGarden 2 where
  garden := leafPairGarden sig hs
  layer := fun _ => p
  isLayering := ⟨fun _ _ => le_rfl, fun _ => rfl⟩

noncomputable def leafPairLowerData (sig : Fin 2 → ℤˣ) (hs : sig 1 = -sig 0) (p N : ℕ) :
    LowerGraftData sig p N where
  low := leafPairLayeredGarden sig hs p
  sign := rfl
  plain := fun _ => rfl
  component := Or.inr ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  order_le := (leafForest_garden_order _ (fun _ => rfl)).trans_le (Nat.zero_le _)

end WaveTurbulence.Induct
