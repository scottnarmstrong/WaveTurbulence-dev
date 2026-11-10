/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDataPartitionUniqueness
public import WaveTurbulence.Foundations.XChain.GraftLowerInjectivity
public import WaveTurbulence.Foundations.XChain.InverseCanonicalGraftData
/-! Exact structural bijection between canonical gardens and top-tree graft data. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem canonicalGraftData_graft_injective {w p : ℕ} {sig : Fin w → ℤˣ} :
    Function.Injective (CanonicalGraftData.graft (sig := sig) (p := p)) := by
  intro C D he
  have ht := canonicalGraftData_top_eq C D he
  have hp := canonicalGraftData_partition_heq C D ht (congrArg LayeredGarden.garden he)
  cases C with
  | mk ct cp cl cpl cs ci cc =>
    cases D with
    | mk dt dp dl dpl ds di dc =>
      change ct = dt at ht
      cases ht
      have hp' : cp = dp := eq_of_heq hp
      cases hp'
      have hl : cl = dl := funext (fun B =>
        layeredGardenGraft_lower_injective sig ct cp cl dl p cpl dpl cs ds _ _ he B)
      cases hl
      rfl

end WaveTurbulence.Induct
