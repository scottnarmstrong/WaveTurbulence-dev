/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.RungBondTypes

/-! # PC/LP labels are shared by the two actual bond incidences -/

public section
namespace WaveTurbulence.Molecpl
variable {w : ℕ} (G : Garden w)

/-- Reversing an actual PC incidence remains a PC incidence. -/
theorem pc_mate {x : GardenDart G} (h : IsPCDart G x) :
    IsPCDart G (G.molecule.mate x) := by
  obtain ⟨c,s,rfl⟩ := h
  exact ⟨c,!s,rfl⟩

/-- Both incidences of an LP bond are LP incidences. -/
theorem not_pc_mate {x : GardenDart G} (h : ¬ IsPCDart G x) :
    ¬ IsPCDart G (G.molecule.mate x) := by
  intro hm
  have hh := pc_mate G hm
  rw [G.molecule.mate_mate] at hh
  exact h hh

end WaveTurbulence.Molecpl
