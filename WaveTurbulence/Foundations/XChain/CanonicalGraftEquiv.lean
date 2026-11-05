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

noncomputable def canonicalGraftEquiv {w p : ℕ} (sig : Fin w → ℤˣ) (hw : 4 ≤ w) :
    CanonicalGraftData sig p ≃ {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig} :=
  Equiv.ofBijective (fun C => ⟨C.graft, C.graft_isCanonG hw, rfl⟩) (by
    constructor
    · intro C D h
      exact canonicalGraftData_graft_injective (congrArg Subtype.val h)
    · rintro ⟨LG, hG, hs⟩
      obtain ⟨C, he⟩ := exists_canonicalGraftData LG hG
      have hr : ∃ D : CanonicalGraftData sig p, D.graft = LG := by
        cases hs
        exact ⟨C, he⟩
      obtain ⟨D, hD⟩ := hr
      exact ⟨D, Subtype.ext hD⟩)

theorem canonicalGraftEquiv_apply {w p : ℕ} (sig : Fin w → ℤˣ) (hw : 4 ≤ w)
    (C : CanonicalGraftData sig p) : (canonicalGraftEquiv sig hw C).1 = C.graft := rfl

end WaveTurbulence.Induct
