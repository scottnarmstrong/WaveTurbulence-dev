/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.OneRootClocks
public import WaveTurbulence.Foundations.WaveB.FrozenB2
public import WaveTurbulence.Foundations.Incoh.OneClockUpperBox

/-! # Exact source passive external boxes for one-root couples -/

public section
noncomputable section
open Set
namespace WaveTurbulence.IncohInst
open Incoh

/-- The lower end of the passive external unit interval. -/
@[expose] def passiveClockBase (q q' : ℕ) (a : Fin 2) : ℝ := if a = 0 then q' else q

/-- The source box supplies both passive bounds without choosing an auxiliary source root. -/
theorem timeBox_passive_bounds (q q' : ℕ) (a : Fin 2) {t : Fin 2 → ℝ} (ht : t ∈ timeBox q q') :
    ∀ j, j ≠ a → passiveClockBase q q' a ≤ t j ∧ t j ≤ passiveClockBase q q' a + 1 := by
  intro j hj
  fin_cases a <;> fin_cases j <;> simp_all [passiveClockBase, timeBox]

/-- B2's external root bound implies the active lower bound of the actual one-clock split. -/
theorem timeBox_above_oneRoot {LG : LayeredGarden 2} {Q : RegCpl} (d : ℕ)
    (hQ : Q.Decodes LG.garden) (hn : 1 ≤ Q.links.length) (a : Fin 2)
    (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching) (q q' : ℕ)
    (hq : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hq' : LG.layer (GNode.root LG.garden.tree 1) ≤ q') {t : Fin 2 → ℝ}
    (ht : t ∈ timeBox q q') :
    (oneRootCoordinates hQ hn a hb).baseRootTimes (coupleLayerLinks (d := d) LG hQ) a ≤ t a := by
  rw [oneRootCoordinates_base]
  fin_cases a
  · exact (show (LG.layer (GNode.root LG.garden.tree 0) : ℝ) ≤ q by exact_mod_cast hq).trans ht.1.1
  · exact (show (LG.layer (GNode.root LG.garden.tree 1) : ℝ) ≤ q' by exact_mod_cast hq').trans ht.2.1

/-- The active upper clock remains in the finite source layer range. -/
theorem timeBox_clock_upper (D q q' : ℕ) (hq : q ≤ D) (hq' : q' ≤ D)
    {t : Fin 2 → ℝ} (ht : t ∈ timeBox q q') (a : Fin 2) : t a ≤ (D : ℝ) + 1 := by
  fin_cases a
  · exact ht.1.2.trans (by exact_mod_cast Nat.add_le_add_right hq 1)
  · exact ht.2.2.trans (by exact_mod_cast Nat.add_le_add_right hq' 1)

end WaveTurbulence.IncohInst
