/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
/-! # Connectivity of `𝒱_γ` chains (packet L5c)

Main's `Molecule/VineChainConnected.lean`, `VineChainEraseEndpoints.lean`, `VineChainInteriorConnected.lean` and
`chain_joints_ne` (`VineChainBlock.lean`), sha256 in `COPIED-SHA256SUMS`, ported from the drawn chains `Vine.Chain` to
L6's `Src.Chain γ`. The per-ingredient facts are: a member of `𝒱_γ` is a block (hence connected), and the facts
`FamFacts.erase_connected`, `FamFacts.interior_connected`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.Vine (GroupConnected induced_path_mono groupConnected_union)

variable {γv : ℝ} {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A member of `𝒱_γ` is connected. -/
theorem isSomeVine_connected {M : Molecule V D} {S : Finset V} {a b : V} (h : IsSomeVine γv M S a b) :
    GroupConnected M S :=
  vineGroupConnected_of_groupConnected (isBlock_of_isSomeVine h).2.2.2.2.2.2.2.2.2

/-- Both declared chain joints belong to its atom set. -/
theorem chain_joints_mem {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : a ∈ S ∧ b ∈ S := by
  induction h with
  | single h => exact ⟨(isBlock_of_isSomeVine h).2.1, (isBlock_of_isSomeVine h).2.2.1⟩
  | append _ hT _ _ ih =>
    exact ⟨mem_union_left _ ih.1, mem_union_right _ (isBlock_of_isSomeVine hT).2.2.1⟩

theorem chain_joints_ne {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : a ≠ b := by
  cases h with
  | single h => exact (isBlock_of_isSomeVine h).2.2.2.1
  | append _ _ _ hne => exact hne

/-- Actual ordered concatenation preserves connectivity. -/
theorem chain_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : GroupConnected M S := by
  induction h with
  | single h => exact isSomeVine_connected h
  | append hS hT _ _ ih =>
    exact groupConnected_union M ih (isSomeVine_connected hT) (chain_joints_mem hS).2
      (isBlock_of_isSomeVine hT).2.1

/-- TARGET defvine: every VC is connected. -/
theorem isVC_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsVC γv M S a b) : GroupConnected M S := by
  obtain ⟨_hB, n, hn⟩ := h
  exact chain_connected hn

/-- Deleting a single atom from a chain leaves every remaining atom connected to at least one surviving outer
endpoint. -/
theorem chain_erase_endpoint_reach (hF : FamFacts γv) {M : Molecule V D} {S : Finset V} {a b z : V} {n : ℕ}
    (h : Chain γv M S a b n) : ∀ u ∈ S.erase z,
      (a ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent a u) ∨
      (b ≠ z ∧ (Mole.induced M (S.erase z)).SameComponent b u) := by
  induction h with
  | @single S a b h =>
    have hXB := isBlock_of_isSomeVine h
    intro u hu
    by_cases haz : a = z
    · have hbz : b ≠ z := by intro he; exact hXB.2.2.2.1 (haz.trans he.symm)
      exact Or.inr ⟨hbz, hF.erase_connected _ h z b (mem_erase.mpr ⟨hbz, hXB.2.2.1⟩) u hu⟩
    · exact Or.inl ⟨haz, hF.erase_connected _ h z a (mem_erase.mpr ⟨haz, hXB.2.1⟩) u hu⟩
  | @append S T a b c n hS hT hi _hne ih =>
    have hs := chain_joints_mem hS
    have ht := isBlock_of_isSomeVine hT
    have liftS : S.erase z ⊆ (S ∪ T).erase z := by
      intro v hv
      obtain ⟨hvz, hvS⟩ := mem_erase.mp hv
      exact mem_erase.mpr ⟨hvz, mem_union_left _ hvS⟩
    have liftT : T.erase z ⊆ (S ∪ T).erase z := by
      intro v hv
      obtain ⟨hvz, hvT⟩ := mem_erase.mp hv
      exact mem_erase.mpr ⟨hvz, mem_union_right _ hvT⟩
    intro u hu
    obtain ⟨huz, huU⟩ := mem_erase.mp hu
    by_cases hcz : c = z
    · have hcS : c ∉ S := by
        intro hcS
        have he : c = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS, ht.2.2.1⟩)
        exact ht.2.2.2.1 he.symm
      have hSz : ∀ v ∈ S, v ≠ z := by
        intro v hv he
        exact hcS (hcz.symm ▸ he ▸ hv)
      have hbz := hSz b hs.2
      have haz := hSz a hs.1
      have liftS' : S ⊆ (S ∪ T).erase z := fun v hv => mem_erase.mpr ⟨hSz v hv, mem_union_left _ hv⟩
      refine Or.inl ⟨haz, ?_⟩
      rcases mem_union.mp huU with huS | huT
      · exact induced_path_mono M liftS' (chain_connected hS a hs.1 u huS)
      · exact Relation.EqvGen.trans _ _ _
          (induced_path_mono M liftS' (chain_connected hS a hs.1 b hs.2))
          (induced_path_mono M liftT (hF.erase_connected _ hT z b (mem_erase.mpr ⟨hbz, ht.2.1⟩) u
            (mem_erase.mpr ⟨huz, huT⟩)))
    · rcases mem_union.mp huU with huS | huT
      · rcases ih u (mem_erase.mpr ⟨huz, huS⟩) with ⟨haz, hp⟩ | ⟨hbz, hp⟩
        · exact Or.inl ⟨haz, induced_path_mono M liftS hp⟩
        · refine Or.inr ⟨hcz, Relation.EqvGen.trans _ _ _ ?_ (induced_path_mono M liftS hp)⟩
          exact induced_path_mono M liftT
            (hF.erase_connected _ hT z c (mem_erase.mpr ⟨hcz, ht.2.2.1⟩) b (mem_erase.mpr ⟨hbz, ht.2.1⟩))
      · exact Or.inr ⟨hcz, induced_path_mono M liftT
          (hF.erase_connected _ hT z c (mem_erase.mpr ⟨hcz, ht.2.2.1⟩) u (mem_erase.mpr ⟨huz, huT⟩))⟩

/-- Removing the first endpoint of a chain leaves every atom connected to the surviving other endpoint. -/
theorem chain_erase_first_connected (hF : FamFacts γv) {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : GroupConnected M (S.erase a) := by
  have reach (u : V) (hu : u ∈ S.erase a) : (Mole.induced M (S.erase a)).SameComponent b u := by
    rcases chain_erase_endpoint_reach hF (z := a) h u hu with ⟨hne, _hp⟩ | ⟨_hne, hp⟩
    · exact False.elim (hne rfl)
    · exact hp
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

/-- TARGET defvine/subsetvc: all nonjoint atoms of a `𝒱_γ` chain form a connected region. -/
theorem chain_interior_connected (hF : FamFacts γv) {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : GroupConnected M (S \ {a, b}) := by
  cases h with
  | single h => exact hF.interior_connected _ h
  | @append S T a b c n hS hT hi _hne =>
    rename_i c
    have hX := isBlock_of_isSomeVine hT
    have hs := chain_joints_mem hS
    have hab := chain_joints_ne hS
    have hbc := hX.2.2.2.1
    have hcS : c ∉ S := by
      intro hcS
      have he : c = b := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hcS, hX.2.2.1⟩)
      exact hbc he.symm
    have haT : a ∉ T := by
      intro haT
      exact hab (mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hs.1, haT⟩))
    have liftS : S.erase a ⊆ (S ∪ T) \ {a, c} := by
      intro v hv
      obtain ⟨hva, hvS⟩ := mem_erase.mp hv
      refine mem_sdiff.mpr ⟨mem_union_left _ hvS, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hva, fun he => hcS (he ▸ hvS)⟩
    have liftT : T.erase c ⊆ (S ∪ T) \ {a, c} := by
      intro v hv
      obtain ⟨hvc, hvT⟩ := mem_erase.mp hv
      refine mem_sdiff.mpr ⟨mem_union_right _ hvT, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun he => haT (he ▸ hvT), hvc⟩
    have reach (u : V) (hu : u ∈ (S ∪ T) \ {a, c}) :
        (Mole.induced M ((S ∪ T) \ {a, c})).SameComponent b u := by
      obtain ⟨huU, huj⟩ := mem_sdiff.mp hu
      have hune : u ≠ a ∧ u ≠ c := by simpa only [mem_insert, mem_singleton, not_or] using huj
      rcases mem_union.mp huU with huS | huT
      · exact induced_path_mono M liftS
          (chain_erase_first_connected hF hS b (mem_erase.mpr ⟨hab.symm, hs.2⟩) u (mem_erase.mpr ⟨hune.1, huS⟩))
      · exact induced_path_mono M liftT
          (hF.erase_connected _ hT c b (mem_erase.mpr ⟨hbc, hX.2.1⟩) u (mem_erase.mpr ⟨hune.2, huT⟩))
    intro u hu v hv
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

end WaveTurbulence.GammaLow.Famc
