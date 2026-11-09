/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceGapTableSelection
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! # H-MS2: the gap-table selection lemmas over the low family (L6-HMS2, hand port)

Main's `Spine/SourceGapTableObjects` (H-MAP order 362, V-FAM) and `Spine/SourceGapTableSelection` (order 363, V-NORMAL)
were not emitted by the porter (they name the carrier only as `SourceVine.Object`). Their three carrier-dependent
lemmas, over `Src … Src.γL`, with main's proofs (sha256 of both sources in `H/MS2/COPIED-SHA256SUMS`); the family-free
ones (`block_gap_kind_congr`, `sourceGapTable_atomGapKind_eq`, `source_gapKind_eq_zero_iff`) are main's, by import.
Names as main's, in namespace `H` (they shadow main's in the ported modules, which open `WaveTurbulence.LGSpine`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Set Finset

/-- Main's `sourceGapTable_object_kind_iff` over `Src.Object Src.γL`. -/
theorem sourceGapTable_object_kind_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (P : Src.Object Src.γL G.molecule) (kind : Molecule.GapKind) :
    P.HasGapKind L γ η base κ kind ↔ P.HasGapKind L γ η base κ' kind := by
  have hloc := sourceGapTable_eq_apply G L γ η base κ κ' h
  unfold Src.Object.HasGapKind Src.VineLikeObject.IsGap
  cases P.shape with
  | vc hvc => exact block_gap_kind_congr G.molecule L γ η base κ κ' hloc P.atoms P.upper kind
  | hyper Q =>
    unfold Src.HyperLikeRealization.IsGap
    apply block_gap_kind_congr (Molecule.eraseBond G.molecule Q.added) L γ η base _ _
    intro x y hxy
    have hh : G.molecule.atom x.1 = G.molecule.atom y.1 := hxy
    exact hloc x.1 y.1 hh

/-- Main's `sourceGapTable_eligibleSecond_iff` over `Src.eligibleSecondObject Src.γL`. -/
theorem sourceGapTable_eligibleSecond_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (F : Set (GBranch G.tree)) (P : Src.Object Src.γL G.molecule) :
    Src.eligibleSecondObject Src.γL G L γ η base κ F P ↔
      Src.eligibleSecondObject Src.γL G L γ η base κ' F P := by
  unfold Src.eligibleSecondObject
  simp only [sourceGapTable_object_kind_iff G L γ η base κ κ' h]

/-- Main's `sourceGapTable_secondCollection_iff` over `Src.IsSourceSecondCollection Src.γL`. -/
theorem sourceGapTable_secondCollection_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (Src.Object Src.γL G.molecule)) :
    Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection ↔
      Src.IsSourceSecondCollection Src.γL G L γ η base κ' F omitted collection := by
  unfold Src.IsSourceSecondCollection
  simp only [sourceGapTable_object_kind_iff G L γ η base κ κ' h,
    sourceGapTable_eligibleSecond_iff G L γ η base κ κ' h]

end WaveTurbulence.GammaLow.FinalCount.H
