/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceGapTable
/-! A partial choice of two incident darts per atom has at most 17^n possibilities.
None is retained for atoms where the source selects no pair, including isolated atoms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

abbrev SourcePairTable {w : ℕ} (G : Garden w) :=
  (v : GBranch G.tree) → Option
    ({x : GardenDart G // x ∈ G.molecule.dartsAt v} × {y : GardenDart G // y ∈ G.molecule.dartsAt v})

 theorem card_sourcePairTables_le {w : ℕ} (G : Garden w) :
    Fintype.card (SourcePairTable G) ≤ 17 ^ G.order := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_coe]
  calc
    _ ≤ ∏ _v : GBranch G.tree, 17 := by
      apply prod_le_prod' (fun v _ => ?_)
      have hh := WaveTurbulence.Mole.garden_molecule_deg_le_four G v
      change (G.molecule.dartsAt v).card ≤ 4 at hh
      nlinarith
    _ = _ := by simp only [prod_const, card_univ, card_gbranch]; rfl

noncomputable def sourcePairFirst {w : ℕ} (G : Garden w) (T : SourcePairTable G) :
    GBranch G.tree → Option (GardenDart G) := fun v => (T v).map (fun p => p.1.1)

noncomputable def sourcePairSecond {w : ℕ} (G : Garden w) (T : SourcePairTable G) :
    GBranch G.tree → Option (GardenDart G) := fun v => (T v).map (fun p => p.2.1)

 theorem sourcePairTable_hasChosenPair_iff {w : ℕ} (G : Garden w) (T : SourcePairTable G)
    (v : GBranch G.tree) (P : GardenDart G → GardenDart G → Prop) :
    SourceVine.HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) P ↔
      ∃ p, T v = some p ∧ P p.1.1 p.2.1 := by
  cases h : T v with
  | none => simp only [SourceVine.HasChosenPair, sourcePairFirst, sourcePairSecond, h, Option.map_none]
            simp
  | some p =>
    simp [SourceVine.HasChosenPair, sourcePairFirst, sourcePairSecond, h]

end WaveTurbulence.LGSpine
