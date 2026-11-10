/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapSubpro
public import WaveTurbulence.Foundations.Spine.SourceFinalCountInputs
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 6: the garden molecule, `SubproSupport` -> `SubproOblG`, `numCriticalSG`

For a garden `G` and an injective renaming `ι : GBranch G.tree ↪ W` (e.g. `Sum.inl`):
* `collDataOf` and `subproOblG_of_support` / `degenSGT_of_support`: the decorated fields of the (atom-set)
  `SubproSupport` give G3's `SubproOblG` and `DegenSGT` for `G.molecule`; composing with `collMap` gives them
  for `mapAtoms G.molecule ι`;
* `critMap`, `numCriticalSG_eq`: the critical-SG count of the choices equals the count of the transported critical
  atoms of `mapAtoms G.molecule ι`;
* `ladderGaps_iff_sourceLadderGaps`: requirement (c) of `Admissible` is `SourceLadderGaps`, which transports with
  the ladder scale `scaleMap ι C.ladderScale`.
The admissibility predicate `splicedCountingAdmissible … κ` is a predicate on `κ : GardenDart G → …`; darts are
shared, so it needs no pull-back (`mapAtoms_countA`). -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {w d : ℕ} {G : Garden w}

/-- The collection data of `subpro` as G3's generic collection data of `G.molecule`. -/
def collDataOf (C : SubproChoices G) : CollData G.molecule :=
  ⟨C.count, C.collection, C.hinges, C.first, C.second⟩

theorem subproOblG_of_support {C : SubproChoices G} {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} (h : SubproSupport G C L γ η base kFix κ) :
    SubproOblG (collDataOf C) L γ η base κ :=
  ⟨h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩

theorem gapKind_neg {L γ η : ℝ} (r : Mom d) : Molecule.gapKind L γ η (-r) = Molecule.gapKind L γ η r := by
  unfold Molecule.gapKind
  simp only [neg_eq_zero, norm_neg]

theorem gapAt_swap {L : ℝ} {base : Mom d} {D : Type*} (κ : D → (Fin d → ℤ)) (x y : D) :
    Molecule.gapAt L base κ y x = -Molecule.gapAt L base κ x y := by
  unfold Molecule.gapAt
  rw [neg_sub]

/-- TARGET `subpro` (3): every atom of `M_sub` with a zero-gap triple is SG (a hinge) or tame. -/
theorem degenSGT_of_support {C : SubproChoices G} {L γ η : ℝ} {base : Mom d} {kFix : Finset (Mom d)}
    {κ : GardenDart G → (Fin d → ℤ)} (h : SubproSupport G C L γ η base kFix κ) :
    DegenSGT G.molecule L γ η base κ (fun v => G.molecule.IsTame L base kFix κ v) := by
  intro a ha x y hx hy hxo hyo hne hz
  by_cases hh : a ∈ C.hinges
  · left
    obtain ⟨x', y', -, -, hT, hk⟩ := h.hingeSG a hh
    obtain ⟨ha1, ha2, hne', hne2⟩ := hT
    by_cases ho : G.molecule.out x' = false
    · have hy' : G.molecule.out y' = true := by
        cases h1 : G.molecule.out y' <;> simp_all
      exact ⟨x', y', ha1, ha2, ho, hy', hne', hk⟩
    · have hx'' : G.molecule.out x' = true := by simpa using ho
      have hy' : G.molecule.out y' = false := by
        cases h1 : G.molecule.out y' <;> simp_all
      refine ⟨y', x', ha2, ha1, hy', hx'', ?_, ?_⟩
      · intro e
        apply hne'
        rw [e, G.molecule.mate_mate]
      · rw [gapAt_swap, gapKind_neg]; exact hk
  · right
    refine h.zeroTame a hh ⟨x, y, ⟨hx, hy, hne, ?_⟩, ?_⟩
    · rw [hxo, hyo]; simp
    · have : Molecule.gapAt L base κ x y = 0 := by
        unfold Molecule.gapKind at hz
        split_ifs at hz with h0
        exact h0
      exact this

/-! ### Critical SG atoms and the ladder-gap clause -/

variable {W : Type*} [DecidableEq W]

/-- The critical-SG predicate of the choices `C` transported along `ι`: the label is read at the preimage and the
interiors of the transported objects (`objMap`) are the images of the interiors. -/
def critMap (ι : GBranch G.tree ↪ W) (C : CountingChoices G d) (v' : W) : Prop :=
  (∃ a, ι a = v' ∧ C.atomLabel a = .SG) ∧
    (∀ i, ¬ (objMap (ι := ι) (C.subpro.collection i)).IsInterior v') ∧
    ∀ P' ∈ objMap (ι := ι) '' C.secondCollection, ¬ P'.IsInterior v'

theorem critMap_iff (ι : GBranch G.tree ↪ W) (C : CountingChoices G d) (a : GBranch G.tree) :
    critMap ι C (ι a) ↔ C.CriticalSG a := by
  unfold critMap CountingChoices.CriticalSG
  refine and_congr ⟨fun ⟨b, hb, h⟩ => ι.injective hb ▸ h, fun h => ⟨a, rfl, h⟩⟩ (and_congr ?_ ?_)
  · exact forall_congr' fun i => not_congr (objMap_isInterior_iff _ a)
  · constructor
    · intro h P hP
      exact fun hi => h _ ⟨P, hP, rfl⟩ ((objMap_isInterior_iff P a).mpr hi)
    · rintro h _ ⟨P, hP, rfl⟩ hi
      exact h P hP ((objMap_isInterior_iff P a).mp hi)

/-- **`numCriticalSG` is the number of critical atoms of the renamed molecule.** -/
theorem numCriticalSG_eq (ι : GBranch G.tree ↪ W) (C : CountingChoices G d) :
    C.numCriticalSG = ((mapAtoms G.molecule ι).atoms.filter (critMap ι C)).card := by
  unfold CountingChoices.numCriticalSG
  rw [show (mapAtoms G.molecule ι).atoms = (Finset.univ : Finset (GBranch G.tree)).map ι from rfl,
    Finset.filter_map, Finset.card_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, critMap_iff]

/-- ... and so holds for the renamed molecule with the ladder scale `scaleMap ι C.ladderScale`. -/
theorem ladderGaps_mapAtoms (ι : GBranch G.tree ↪ W) (C : CountingChoices G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) :
    SourceLadderGaps (mapAtoms G.molecule ι) L base (scaleMap ι C.ladderScale) κ ↔
      C.LadderGaps L γ η base κ :=
  mapAtoms_sourceLadderGaps_scaleMap ι C.ladderScale

end WaveTurbulence.AtomTransport
